(*
  File:         PAC_Checker_Synthesis.thy
  Author:       Mathias Fleury, Daniela Kaufmann, JKU
  Maintainer:   Mathias Fleury, JKU
*)
theory PAC_Checker_Synthesis
  imports PAC_Checker WB_Sort PAC_Checker_Relation
    PAC_Checker_Init More_Loops PAC_Version
begin

section \<open>Code Synthesis of the Complete Checker\<close>

text \<open>We here combine refine the full checker, using the initialisation provided in another file and
adding more efficient data structures (mostly replacing the set of variables by a more efficient
hash map).\<close>

hide_const (open) Autoref_Fix_Rel.CONSTRAINT

section \<open>Status Codes\<close>

text \<open>Erasure of error messages for the LLVM backend: the abstract checker keeps
  building \<open>string code_status\<close> values (nothing upstream changes), but the refinement
  forgets the message text. A status is implemented by a tag word
  (0 = \<open>CSUCCESS\<close>, 1 = \<open>CFOUND\<close>, 2 = \<open>CFAILED\<close>) plus a 64-bit payload word that the
  implementation may use freely for diagnostics. We store the line number of a
  failure; the assertion constrains only the tag, so the payload never has to be
  related to the dropped message. Error-message \<^emph>\<open>strings\<close> are erased to a dummy
  \<open>1 word\<close> token (\<open>raw_string_assn\<close>).

  No formal content is lost: the correctness statements only distinguish the
  constructors (\<open>is_cfailed\<close>/\<open>is_cfound\<close>), never the message text. The \<open>R\<close> parameter
  of \<open>status_assn\<close> is kept (and ignored) for textual compatibility with the AFP
  signatures (\<open>status_assn raw_string_assn\<close>). Under the tag ordering,
  \<open>merge_cstatus\<close> (failure beats found beats success) is simply \<open>max\<close>.\<close>

type_synonym status_impl = \<open>8 word \<times> 64 word\<close>

definition status_code :: \<open>'a code_status \<Rightarrow> 8 word\<close> where
  \<open>status_code s = (case s of CSUCCESS \<Rightarrow> 0 | CFOUND \<Rightarrow> 1 | CFAILED _ \<Rightarrow> 2)\<close>

lemma status_code_simps[simp]:
  \<open>status_code CSUCCESS = 0\<close>
  \<open>status_code CFOUND = 1\<close>
  \<open>status_code (CFAILED e) = 2\<close>
  by (auto simp: status_code_def)

lemma is_cfailed_status_code: \<open>is_cfailed s \<longleftrightarrow> status_code s = 2\<close>
  by (cases s) auto

lemma is_cfound_status_code: \<open>is_cfound s \<longleftrightarrow> status_code s = 1\<close>
  by (cases s) auto

lemma status_code_merge:
  \<open>status_code (merge_cstatus a b) =
     (if status_code a < status_code b then status_code b else status_code a)\<close>
  by (cases a; cases b) (auto simp: word_less_def)

definition status_assn :: \<open>('e \<Rightarrow> 'ec \<Rightarrow> assn) \<Rightarrow> 'e code_status \<Rightarrow> status_impl \<Rightarrow> assn\<close> where
  \<open>status_assn R s c = \<up>(fst c = status_code s)\<close>

abbreviation raw_string_assn :: \<open>string \<Rightarrow> 1 word \<Rightarrow> assn\<close> where
  \<open>raw_string_assn \<equiv> \<lambda>_ _. \<box>\<close>

text \<open>Raw word-comparison triples, proved once in a throwaway interpreted context
  (cf. the \<open>ll_zext\<close> recipe in \<open>String_Hash_Map\<close>) \<emdash> not globally \<open>[vcg_rules]\<close>, since
  raw rules on 64-bit words would hijack snat/unat arithmetic elsewhere.\<close>

context
begin
interpretation llvm_prim_arith_setup .

lemma ll_icmp_eq_word_rule:
  \<open>llvm_htriple \<box> (ll_icmp_eq (a::'l::len word) b) (\<lambda>r. \<upharpoonleft>bool.assn (a = b) r)\<close>
  supply [simp] = bool.assn_def
  by vcg

lemma ll_icmp_ult_word_rule:
  \<open>llvm_htriple \<box> (ll_icmp_ult (a::'l::len word) b) (\<lambda>r. \<upharpoonleft>bool.assn (a < b) r)\<close>
  supply [simp] = bool.assn_def
  by vcg

end

text \<open>The postconditions of all the following rules are entirely pure, and the final
  reassembly (\<open>ENTAILS\<close> goals with an existential over a pure body) is out of reach for
  the frame inference \<emdash> the trailing \<open>auto\<close> with the extraction simps closes them.\<close>

lemmas status_pure_reassembly =
  ENTAILS_def entails_def sep_algebra_simps pred_lift_extract_simps sep_conj_exists
  vcg_tag_defs

lemma SUCCESS_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn (0, 0)), uncurry0 (RETURN CSUCCESS)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a status_assn R\<close>
  unfolding status_assn_def
  apply sepref_to_hoare
  by (vcg; auto simp: status_pure_reassembly)

lemma FOUND_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn (1, 0)), uncurry0 (RETURN CFOUND)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a status_assn R\<close>
  unfolding status_assn_def
  apply sepref_to_hoare
  by (vcg; auto simp: status_pure_reassembly)

definition is_cfailed_impl :: \<open>status_impl \<Rightarrow> 1 word llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>is_cfailed_impl \<equiv> \<lambda>(t, _). ll_icmp_eq t 2\<close>

lemma is_cfailed_hnr[sepref_fr_rules]:
  \<open>(is_cfailed_impl, RETURN o is_cfailed) \<in> (status_assn R)\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding bool1_rel_def bool.assn_is_rel[symmetric] is_cfailed_impl_def status_assn_def
  supply [vcg_rules] = ll_icmp_eq_word_rule
  supply [simp] = bool.assn_def is_cfailed_status_code
  apply sepref_to_hoare
  by (vcg; auto simp: status_pure_reassembly)

definition is_cfound_impl :: \<open>status_impl \<Rightarrow> 1 word llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>is_cfound_impl \<equiv> \<lambda>(t, _). ll_icmp_eq t 1\<close>

lemma is_cfound_hnr[sepref_fr_rules]:
  \<open>(is_cfound_impl, RETURN o is_cfound) \<in> (status_assn R)\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding bool1_rel_def bool.assn_is_rel[symmetric] is_cfound_impl_def status_assn_def
  supply [vcg_rules] = ll_icmp_eq_word_rule
  supply [simp] = bool.assn_def is_cfound_status_code
  apply sepref_to_hoare
  by (vcg; auto simp: status_pure_reassembly)

definition merge_cstatus_impl :: \<open>status_impl \<Rightarrow> status_impl \<Rightarrow> status_impl llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>merge_cstatus_impl \<equiv> \<lambda>(ta, la) (tb, lb). doM {
     b \<leftarrow> ll_icmp_ult ta tb;
     llc_if b (Mreturn (tb, lb)) (Mreturn (ta, la)) }\<close>

lemma merge_cstatus_hnr[sepref_fr_rules]:
  \<open>(uncurry merge_cstatus_impl, uncurry (RETURN oo merge_cstatus)) \<in>
    (status_assn R)\<^sup>k *\<^sub>a (status_assn R)\<^sup>k \<rightarrow>\<^sub>a status_assn R\<close>
  unfolding merge_cstatus_impl_def status_assn_def
  supply [vcg_rules] = ll_icmp_ult_word_rule
  supply [simp] = status_code_merge
  apply sepref_to_hoare
  by (vcg; auto simp: status_pure_reassembly)

section \<open>Arithmetic Operations\<close>

subsection \<open>Addition\<close>

(* We need a modified version of add_poly to make it compatible with our owning list implementation *)
definition \<open>add_poly_alt \<equiv> REC\<^sub>T
      (\<lambda>add_poly_alt (p, q).
        if q = [] then RETURN p
        else if p = [] then RETURN q
        else do {
          ((xs, n), p') \<leftarrow> mop_list_pop_front p;
          ((ys, m), q') \<leftarrow> mop_list_pop_front q;
          (if xs = ys then if n + m = 0 then add_poly_alt (p', q') else
             do {
               pq \<leftarrow> add_poly_alt (p', q');
               RETURN ((xs, n + m) # pq)
             }
          else if (xs, ys) \<in> term_order_rel
            then do {
               pq \<leftarrow> add_poly_alt (p', (ys, m) # q');
               RETURN ((xs, n) # pq)
          }
          else do {
               pq \<leftarrow> add_poly_alt ((xs, n) # p', q');
               RETURN ((ys, m) # pq)
          })
        })\<close>

lemma add_poly_alt: \<open>add_poly_l = add_poly_alt\<close>
  unfolding add_poly_l_def add_poly_alt_def
  apply (rule arg_cong[where f = \<open>REC\<^sub>T\<close>])
  apply (intro ext)
  subgoal for f x
    apply (cases x)
    subgoal for p q
      by (cases p; cases q)
         (auto simp: mop_list_pop_front_def split: prod.splits)
    done
  done

text \<open>The implementation add_poly_alt can only be implemented destructively.
  As a quick solution, we wrap the function into a version where we simply copy both polynomials
  TODO: Find a better way to do this.\<close>

definition \<open>add_poly_keep \<equiv> \<lambda>(x, y). add_poly_alt (COPY x, COPY y)\<close>

lemma add_poly_keep: \<open>add_poly_alt = add_poly_keep\<close>
  unfolding add_poly_keep_def COPY_def by simp

sepref_definition add_poly_impl
  is \<open>add_poly_l\<close>
  :: \<open>(poly_assn \<times>\<^sub>a poly_assn)\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  unfolding add_poly_alt add_poly_keep 
  apply (subst add_poly_keep_def)
  unfolding add_poly_alt_def
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
  by sepref

declare add_poly_impl.refine[sepref_fr_rules]

subsection \<open>Multiplication\<close>

sepref_register mult_monomials

text \<open>Like \<open>add_poly_l\<close>: the case-based definition is rewritten with
  \<open>mop_list_pop_front\<close> (the only head access available at
  \<open>monom_assn = ol_assn strl_assn\<close>), which makes the walk destructive; the keep-mode
  signature is then obtained by copying both monomials at entry (\<open>COPY\<close> resolves to
  \<open>monom_copy_impl\<close>). The variable comparison \<open>(x, y) \<in> var_order_rel\<close> is rewritten
  to \<open>x < y\<close> at \<open>char list\<close> (\<open>var_order_rel''\<close>), implemented by \<open>strl_lt\<close>.\<close>

definition mult_monoms_alt :: \<open>term_poly_list \<Rightarrow> term_poly_list \<Rightarrow> term_poly_list nres\<close> where
  \<open>mult_monoms_alt x y \<equiv> REC\<^sub>T
    (\<lambda>f (p, q).
      if q = [] then RETURN p
      else if p = [] then RETURN q
      else do {
        (x, p') \<leftarrow> mop_list_pop_front p;
        (y, q') \<leftarrow> mop_list_pop_front q;
        (if x = y then do {
           pq \<leftarrow> f (p', q');
           RETURN (x # pq)
         }
         else if (x, y) \<in> var_order_rel
         then do {
           pq \<leftarrow> f (p', y # q');
           RETURN (x # pq)
         }
         else do {
           pq \<leftarrow> f (x # p', q');
           RETURN (y # pq)
         })
      })
    (x, y)\<close>

lemma mult_monoms_alt: \<open>(RETURN oo mult_monoms) = mult_monoms_alt\<close>
  apply (intro ext)
  subgoal for x y
    unfolding mult_monoms_alt_def
    apply (subst eq_commute)
    apply (induction x y rule: mult_monoms.induct)
    subgoal for p
      by (subst RECT_unfold, refine_mono)
         (auto simp: mop_list_pop_front_def split: list.splits)
    subgoal for p
      by (subst RECT_unfold, refine_mono)
         (auto simp: mop_list_pop_front_def split: list.splits)
    subgoal for x p y q
      by (subst RECT_unfold, refine_mono)
         (auto simp: mop_list_pop_front_def split: list.splits)
    done
  done

definition \<open>mult_monoms_keep \<equiv> \<lambda>x y. mult_monoms_alt (COPY x) (COPY y)\<close>

lemma mult_monoms_keep: \<open>mult_monoms_alt = mult_monoms_keep\<close>
  unfolding mult_monoms_keep_def COPY_def by simp

sepref_definition mult_monoms_impl
  is \<open>uncurry (RETURN oo mult_monoms)\<close>
  :: \<open>(monom_assn)\<^sup>k *\<^sub>a (monom_assn)\<^sup>k \<rightarrow>\<^sub>a (monom_assn)\<close>
  supply [[goals_limit=1]]
  unfolding mult_monoms_alt mult_monoms_keep
  apply (subst mult_monoms_keep_def)
  unfolding mult_monoms_alt_def
    var_order_rel''
  by sepref

declare mult_monoms_impl.refine[sepref_fr_rules]

sepref_definition mult_monomials_impl
  is \<open>uncurry (RETURN oo mult_monomials)\<close>
  :: \<open>(monomial_assn)\<^sup>k *\<^sub>a (monomial_assn)\<^sup>k \<rightarrow>\<^sub>a (monomial_assn)\<close>
  supply [[goals_limit=1]]
  unfolding mult_monomials_def
  by sepref

definition map_append_poly_mult where
  \<open>map_append_poly_mult x = map_append (mult_monomials x)\<close>

declare mult_monomials_impl.refine[sepref_fr_rules]

text \<open>Same treatment as \<open>add_poly_l\<close>/\<open>mult_monoms\<close>: the \<open>case xs of x # xs \<Rightarrow> \<dots>\<close> walk
  becomes a destructive pop, so the walked polynomial \<open>xs\<close> must be copied at entry;
  the appended tail \<open>b\<close> is returned as part of the result (ownership transfer at the
  recursion leaf), so it is copied as well. The monomial \<open>a\<close> is only read by the
  keep-mode \<open>mult_monomials_impl\<close> and needs no copy.\<close>

definition map_append_poly_mult_alt
  :: \<open>char list list \<times> int \<Rightarrow> llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> llist_polynomial nres\<close>
where
  \<open>map_append_poly_mult_alt a b xs \<equiv> REC\<^sub>T
    (\<lambda>g xs.
      if xs = [] then RETURN b
      else do {
        (x, xs') \<leftarrow> mop_list_pop_front xs;
        y \<leftarrow> g xs';
        RETURN (mult_monomials a x # y)
      })
    xs\<close>

lemma map_append_poly_mult_alt:
  \<open>(RETURN ooo map_append_poly_mult) = map_append_poly_mult_alt\<close>
  apply (intro ext)
  subgoal for a b xs
    unfolding map_append_poly_mult_alt_def map_append_poly_mult_def
    apply (subst eq_commute)
    apply (induction \<open>mult_monomials a\<close> b xs rule: map_append.induct)
    subgoal by (subst RECT_unfold, refine_mono) auto
    subgoal by (subst RECT_unfold, refine_mono)
               (auto simp: mop_list_pop_front_def)
    done
  done

definition \<open>map_append_poly_mult_keep \<equiv> \<lambda>a b xs. map_append_poly_mult_alt a (COPY b) (COPY xs)\<close>

lemma map_append_poly_mult_keep: \<open>map_append_poly_mult_alt = map_append_poly_mult_keep\<close>
  unfolding map_append_poly_mult_keep_def COPY_def by simp

sepref_definition map_append_poly_mult_impl
  is \<open>uncurry2 (RETURN ooo map_append_poly_mult)\<close>
  :: \<open>monomial_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  supply [[goals_limit=1]]
  unfolding map_append_poly_mult_alt map_append_poly_mult_keep
  apply (subst map_append_poly_mult_keep_def)
  unfolding map_append_poly_mult_alt_def
  by sepref

declare map_append_poly_mult_impl.refine[sepref_fr_rules]

text \<open>The \<open>foldl\<close> over the first polynomial becomes a pop-based \<open>REC\<^sub>T\<close> threading the
  accumulator: \<open>p\<close> is walked destructively (copied at entry for the \<open>\<^sup>k\<close> signature),
  \<open>q\<close> is only read by the keep-mode \<open>map_append_poly_mult_impl\<close>, and the accumulator
  is \<^emph>\<open>moved\<close> through the recursion (the old accumulator is freed after each step
  \<emdash> \<open>map_append_poly_mult_impl\<close> copies it internally; making the accumulator
  argument \<open>\<^sup>d\<close> there would save those copies, cf. the TODO below). The initial \<open>[]\<close>
  is a producer at \<open>poly_assn\<close> and must be the named \<open>op_ol_empty\<close>.

  TODO: this (like the AFP original, cf. @{thm map_by_foldl}) is the worst possible
  implementation of map: quadratic accumulator copies.\<close>

definition mult_poly_raw_alt :: \<open>llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> llist_polynomial nres\<close>
where
  \<open>mult_poly_raw_alt p q \<equiv> REC\<^sub>T
    (\<lambda>g (p, b).
      if p = [] then RETURN b
      else do {
        (x, p') \<leftarrow> mop_list_pop_front p;
        g (p', map_append_poly_mult x b q)
      })
    (p, op_ol_empty)\<close>

lemma mult_poly_raw_alt:
  \<open>(RETURN oo mult_poly_raw) = mult_poly_raw_alt\<close>
  apply (intro ext)
  subgoal for p q
  proof -
    have H: \<open>REC\<^sub>T
      (\<lambda>g (p, b).
        if p = [] then RETURN b
        else do {
          (x, p') \<leftarrow> mop_list_pop_front p;
          g (p', map_append_poly_mult x b q)
        })
      (p, b) = RETURN (foldl (\<lambda>b x. map (mult_monomials x) q @ b) b p)\<close> for b
      apply (induction p arbitrary: b)
      subgoal by (subst RECT_unfold, refine_mono) auto
      subgoal
        by (subst RECT_unfold, refine_mono)
           (auto simp: mop_list_pop_front_def map_append_poly_mult_def map_append_alt_def)
      done
    show \<open>(RETURN oo mult_poly_raw) p q = mult_poly_raw_alt p q\<close>
      unfolding mult_poly_raw_alt_def mult_poly_raw_def op_ol_empty_def op_list_empty_def
      using H[of \<open>[]\<close>] by simp
  qed
  done

definition \<open>mult_poly_raw_keep \<equiv> \<lambda>p q. mult_poly_raw_alt (COPY p) q\<close>

lemma mult_poly_raw_keep: \<open>mult_poly_raw_alt = mult_poly_raw_keep\<close>
  unfolding mult_poly_raw_keep_def COPY_def by simp

sepref_definition mult_poly_raw_impl
  is \<open>uncurry (RETURN oo mult_poly_raw)\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  supply [[goals_limit=1]]
  unfolding mult_poly_raw_alt mult_poly_raw_keep
  apply (subst mult_poly_raw_keep_def)
  unfolding mult_poly_raw_alt_def
  by sepref

declare mult_poly_raw_impl.refine[sepref_fr_rules]

sepref_definition mult_poly_impl
  is \<open>uncurry mult_poly_full\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  supply [[goals_limit=1]]
  unfolding mult_poly_full_def
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
  by sepref

declare mult_poly_impl.refine[sepref_fr_rules]

lemma inverse_monomial:
  \<open>monom_rel\<inverse> \<times>\<^sub>r int_rel = (monom_rel \<times>\<^sub>r int_rel)\<inverse>\<close>
  by (auto)

lemma eq_poly_rel_eq[sepref_import_param]:
  \<open>((=), (=)) \<in> poly_rel \<rightarrow> poly_rel \<rightarrow> bool_rel\<close>
  using list_rel_sv[of \<open>monomial_rel\<close>, OF single_valued_monomial_rel]
  using list_rel_sv[OF single_valued_monomial_rel'[unfolded IS_LEFT_UNIQUE_def inv_list_rel_eq]]
  unfolding inv_list_rel_eq[symmetric]
  by (auto intro!: frefI simp:
      rel2p_def single_valued_def p2rel_def
    simp del: inv_list_rel_eq)

(* definition \<open>weak_equality_l_keep \<equiv> \<lambda>x y. weak_equality_l (COPY x) (COPY y)\<close>
 * 
 * lemma weak_equality_l_keep: \<open>weak_equality_l = weak_equality_l_keep\<close>
 *   unfolding weak_equality_l_keep_def COPY_def by simp *)

sepref_definition weak_equality_l_impl
  is \<open>uncurry weak_equality_l\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding weak_equality_l_def
  by sepref

declare weak_equality_l_impl.refine[sepref_fr_rules]
sepref_register add_poly_l mult_poly_full

text \<open>Error messages under the erasure: the message-\<^emph>\<open>string\<close> builders return the dummy
  token (their implementations do nothing), and \<open>error_msg\<close> \<emdash> which always produces
  \<open>CFAILED\<close> \<emdash> returns tag 2 with the line number as payload. This replaces the AFP's
  \<open>show\<close>-based import rules, which relied on strings being pure values executed by the
  SML code generator; in LLVM a string would be a heap object, and the messages are
  not worth the verified formatting code (the payload keeps the line number, which is
  the useful part).\<close>

lemma error_msg_notin_dom_hnr[sepref_fr_rules]:
  \<open>(\<lambda>_. Mreturn 0, RETURN o error_msg_notin_dom)
    \<in> (unat_assn' TYPE(64))\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
  apply sepref_to_hoare
  by (vcg; auto simp: status_pure_reassembly)

lemma error_msg_reused_dom_hnr[sepref_fr_rules]:
  \<open>(\<lambda>_. Mreturn 0, RETURN o error_msg_reused_dom)
    \<in> (unat_assn' TYPE(64))\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
  apply sepref_to_hoare
  by (vcg; auto simp: status_pure_reassembly)

lemma error_msg_hnr[sepref_fr_rules]:
  \<open>(uncurry (\<lambda>i _. Mreturn (2, i)), uncurry (RETURN oo error_msg))
    \<in> (unat_assn' TYPE(64))\<^sup>k *\<^sub>a raw_string_assn\<^sup>k \<rightarrow>\<^sub>a status_assn raw_string_assn\<close>
  unfolding status_assn_def error_msg_def
  apply sepref_to_hoare
  by (vcg; auto simp: status_pure_reassembly)

(* Dead in LPAC: Add/Mult step checkers + their error messages.
   The LPAC format replaced Add/Mult steps by linear-combination (CL) steps.
sepref_definition check_addition_l_impl
  is \<open>uncurry6 check_addition_l\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a vars_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a
        uint64_nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k  \<rightarrow>\<^sub>a status_assn raw_string_assn\<close>
  supply [[goals_limit=1]]
  unfolding mult_poly_full_def
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    check_addition_l_def
    in_dom_m_lookup_iff
    fmlookup'_def[symmetric]
    vars_llist_alt_def
  by sepref

declare check_addition_l_impl.refine[sepref_fr_rules]

sepref_register check_mult_l_dom_err

definition check_mult_l_dom_err_impl where
  \<open>check_mult_l_dom_err_impl pd p ia i =
    (if pd then ''The polynomial with id '' @ show (nat_of_uint64 p) @ '' was not found'' else '''') @
    (if ia then ''The id of the resulting id '' @ show (nat_of_uint64 i) @ '' was already given'' else '''')\<close>

definition check_mult_l_mult_err_impl where
  \<open>check_mult_l_mult_err_impl p q pq r =
    ''Multiplying '' @ show p @ '' by '' @ show q @ '' gives '' @ show pq @ '' and not '' @ show r\<close>

lemma [sepref_fr_rules]:
  \<open>(uncurry3 ((\<lambda>x y. return oo (check_mult_l_dom_err_impl x y))),
   uncurry3 (check_mult_l_dom_err)) \<in> bool_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_mult_l_dom_err_def check_mult_l_dom_err_impl_def list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done

lemma [sepref_fr_rules]:
  \<open>(uncurry3 ((\<lambda>x y. return oo (check_mult_l_mult_err_impl x y))),
   uncurry3 (check_mult_l_mult_err)) \<in> poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_mult_l_mult_err_def check_mult_l_mult_err_impl_def list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done

sepref_definition check_mult_l_impl
  is \<open>uncurry6 check_mult_l\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a vars_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k  \<rightarrow>\<^sub>a status_assn raw_string_assn\<close>
  supply [[goals_limit=1]]
  unfolding check_mult_l_def
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    in_dom_m_lookup_iff
    fmlookup'_def[symmetric]
    vars_llist_alt_def
  by sepref

declare check_mult_l_impl.refine[sepref_fr_rules]
*)

(* Dead in LPAC: old extension-step error messages.
   LPAC checks check_extension_l2 with its own impls + error messages (same names, shadowing).
definition check_ext_l_dom_err_impl :: \<open>uint64 \<Rightarrow> _\<close>  where
  \<open>check_ext_l_dom_err_impl p =
    ''There is already a polynomial with index '' @ show (nat_of_uint64 p)\<close>

lemma [sepref_fr_rules]:
  \<open>(((return o (check_ext_l_dom_err_impl))),
    (check_extension_l_dom_err)) \<in> uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_extension_l_dom_err_def check_ext_l_dom_err_impl_def list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done


definition check_extension_l_no_new_var_err_impl :: \<open>_ \<Rightarrow> _\<close>  where
  \<open>check_extension_l_no_new_var_err_impl p =
    ''No new variable could be found in polynomial '' @ show p\<close>

lemma [sepref_fr_rules]:
  \<open>(((return o (check_extension_l_no_new_var_err_impl))),
    (check_extension_l_no_new_var_err)) \<in> poly_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_extension_l_no_new_var_err_impl_def check_extension_l_no_new_var_err_def
     list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done

definition check_extension_l_side_cond_err_impl :: \<open>_ \<Rightarrow> _\<close>  where
  \<open>check_extension_l_side_cond_err_impl v p r s =
    ''Error while checking side conditions of extensions polynow, var is '' @ show v @
    '' polynomial is '' @ show p @ ''side condition p*p - p = '' @ show s @ '' and should be 0''\<close>

lemma [sepref_fr_rules]:
  \<open>((uncurry3 (\<lambda>x y. return oo (check_extension_l_side_cond_err_impl x y))),
    uncurry3 (check_extension_l_side_cond_err)) \<in> string_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_extension_l_side_cond_err_impl_def check_extension_l_side_cond_err_def
     list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done

definition check_extension_l_new_var_multiple_err_impl :: \<open>_ \<Rightarrow> _\<close>  where
  \<open>check_extension_l_new_var_multiple_err_impl v p =
    ''Error while checking side conditions of extensions polynow, var is '' @ show v @
    '' but it either appears at least once in the polynomial or another new variable is created '' @
    show p @ '' but should not.''\<close>

lemma [sepref_fr_rules]:
  \<open>((uncurry (return oo (check_extension_l_new_var_multiple_err_impl))),
    uncurry (check_extension_l_new_var_multiple_err)) \<in> string_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_extension_l_new_var_multiple_err_impl_def
     check_extension_l_new_var_multiple_err_def
     list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done
*)


sepref_register check_extension_l_dom_err fmlookup'
  check_extension_l_side_cond_err check_extension_l_no_new_var_err
  check_extension_l_new_var_multiple_err

definition uminus_poly :: \<open>llist_polynomial \<Rightarrow> llist_polynomial\<close> where
  \<open>uminus_poly p' = map (\<lambda>(a, b). (a, - b)) p'\<close>

sepref_register uminus_poly
lemma [sepref_import_param]:
  \<open>(map (\<lambda>(a, b). (a, - b)), uminus_poly) \<in> poly_rel \<rightarrow> poly_rel\<close>
  unfolding uminus_poly_def
  apply (intro fun_relI)
  subgoal for p p'
    by (induction p p' rule: list_rel_induct)
     auto
  done

sepref_register (* vars_of_poly_in is dead in LPAC *)
  weak_equality_l

lemma [safe_constraint_rules]:
  \<open>Sepref_Constraints.CONSTRAINT single_valued (the_pure monomial_assn)\<close> and
  single_valued_the_monomial_assn:
    \<open>single_valued (the_pure monomial_assn)\<close>
    \<open>single_valued ((the_pure monomial_assn)\<inverse>)\<close>
  unfolding IS_LEFT_UNIQUE_def[symmetric]
  by (auto simp: step_rewrite_pure single_valued_monomial_rel single_valued_monomial_rel' Sepref_Constraints.CONSTRAINT_def)

(* Dead in LPAC: old extension checker (LPAC synthesizes check_extension_l2, shadowing this name)
sepref_definition check_extension_l_impl
  is \<open>uncurry5 check_extension_l\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a vars_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a string_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a
     status_assn raw_string_assn\<close>
  supply option.splits[split] single_valued_the_monomial_assn[simp]
  supply [[goals_limit=1]]
  unfolding
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    in_dom_m_lookup_iff
    fmlookup'_def[symmetric]
    vars_llist_alt_def
    check_extension_l_def
    not_not
    option.case_eq_if
    uminus_poly_def[symmetric]
    HOL_list.fold_custom_empty
  by sepref


declare check_extension_l_impl.refine[sepref_fr_rules]
*)

sepref_definition check_del_l_impl
  is \<open>uncurry2 check_del_l\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a status_assn raw_string_assn\<close>
  supply [[goals_limit=1]]
  unfolding check_del_l_def
    in_dom_m_lookup_iff
    fmlookup'_def[symmetric]
  by sepref

lemmas [sepref_fr_rules] = check_del_l_impl.refine

abbreviation pac_step_rel where
  \<open>pac_step_rel \<equiv> p2rel (\<langle>Id, \<langle>monomial_rel\<rangle>list_rel, Id\<rangle> pac_step_rel_raw)\<close>

sepref_register PAC_Polynomials_Operations.normalize_poly
  pac_src1 pac_src2 new_id pac_mult case_pac_step check_mult_l
  check_addition_l check_del_l check_extension_l

lemma pac_step_rel_assn_alt_def2:
  \<open>hn_ctxt (pac_step_rel_assn nat_assn poly_assn id_assn) b bi =
       hn_val
        (p2rel
          (\<langle>nat_rel, poly_rel, Id :: (string \<times> _) set\<rangle>pac_step_rel_raw)) b bi\<close>
  unfolding poly_assn_list hn_ctxt_def
  by (induction nat_assn poly_assn \<open>id_assn :: string \<Rightarrow> _\<close> b bi rule: pac_step_rel_assn.induct)
   (auto simp: p2rel_def hn_val_unfold pac_step_rel_raw.simps relAPP_def
    pure_app_eq)


lemma is_AddD_import[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure K\<close>  \<open>CONSTRAINT is_pure V\<close>
  shows
    \<open>(return o pac_res, RETURN o pac_res) \<in> [\<lambda>x. is_Add x \<or> is_Mult x \<or> is_Extension x]\<^sub>a
       (pac_step_rel_assn K V R)\<^sup>k \<rightarrow> V\<close>
    \<open>(return o pac_src1, RETURN o pac_src1) \<in> [\<lambda>x. is_Add x \<or> is_Mult x \<or> is_Del x]\<^sub>a (pac_step_rel_assn K V R)\<^sup>k \<rightarrow> K\<close>
    \<open>(return o new_id, RETURN o new_id) \<in> [\<lambda>x. is_Add x \<or> is_Mult x \<or> is_Extension x]\<^sub>a (pac_step_rel_assn K V R)\<^sup>k \<rightarrow> K\<close>
    \<open>(return o is_Add, RETURN o is_Add) \<in>  (pac_step_rel_assn K V R)\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
    \<open>(return o is_Mult, RETURN o is_Mult) \<in> (pac_step_rel_assn K V R)\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
    \<open>(return o is_Del, RETURN o is_Del) \<in> (pac_step_rel_assn K V R)\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
    \<open>(return o is_Extension, RETURN o is_Extension) \<in> (pac_step_rel_assn K V R)\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  using assms
  by (sepref_to_hoare; sep_auto simp: pac_step_rel_assn_alt_def is_pure_conv ent_true_drop pure_app_eq
      split: pac_step.splits; fail)+

lemma [sepref_fr_rules]:
  \<open>CONSTRAINT is_pure K \<Longrightarrow>
  (return o pac_src2, RETURN o pac_src2) \<in> [\<lambda>x. is_Add x]\<^sub>a (pac_step_rel_assn K V R)\<^sup>k \<rightarrow> K\<close>
  \<open>CONSTRAINT is_pure V \<Longrightarrow>
  (return o pac_mult, RETURN o pac_mult) \<in> [\<lambda>x. is_Mult x]\<^sub>a (pac_step_rel_assn K V R)\<^sup>k \<rightarrow> V\<close>
  \<open>CONSTRAINT is_pure R \<Longrightarrow>
  (return o new_var, RETURN o new_var) \<in> [\<lambda>x. is_Extension x]\<^sub>a (pac_step_rel_assn K V R)\<^sup>k \<rightarrow> R\<close>
  by (sepref_to_hoare; sep_auto simp: pac_step_rel_assn_alt_def is_pure_conv ent_true_drop pure_app_eq
      split: pac_step.splits; fail)+

lemma is_Mult_lastI:
  \<open>\<not> is_Add b \<Longrightarrow> \<not>is_Mult b \<Longrightarrow> \<not>is_Extension b \<Longrightarrow> is_Del b\<close>
  by (cases b) auto

sepref_register is_cfailed is_Del

(* Dead in LPAC: shadowed by LPAC's own PAC_checker_l_step' (same name)
definition PAC_checker_l_step' ::  _ where
  \<open>PAC_checker_l_step' a b c d = PAC_checker_l_step a (b, c, d)\<close>

lemma PAC_checker_l_step_alt_def:
  \<open>PAC_checker_l_step a bcd e = (let (b,c,d) = bcd in PAC_checker_l_step' a b c d e)\<close>
  unfolding PAC_checker_l_step'_def by auto
*)

sepref_decl_intf ('k) acode_status is "('k) code_status"
sepref_decl_intf ('k, 'b, 'lbl) apac_step is "('k, 'b, 'lbl) pac_step"

sepref_register merge_cstatus full_normalize_poly new_var is_Add

lemma poly_rel_the_pure:
  \<open>poly_rel = the_pure poly_assn\<close> and
  nat_rel_the_pure:
  \<open>nat_rel = the_pure nat_assn\<close> and
 WTF_RF: \<open>pure (the_pure nat_assn) = nat_assn\<close>
  unfolding poly_assn_list
  by auto

lemma [safe_constraint_rules]:
    \<open>CONSTRAINT IS_LEFT_UNIQUE uint64_nat_rel\<close> and
  single_valued_uint64_nat_rel[safe_constraint_rules]:
    \<open>CONSTRAINT single_valued uint64_nat_rel\<close>
  by (auto simp: IS_LEFT_UNIQUE_def single_valued_def uint64_nat_rel_def br_def)

(* Dead in LPAC: shadowed by LPAC's own check_step_impl
sepref_definition check_step_impl
  is \<open>uncurry4 PAC_checker_l_step'\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a (status_assn raw_string_assn)\<^sup>d *\<^sub>a vars_assn\<^sup>d *\<^sub>a polys_assn\<^sup>d *\<^sub>a (pac_step_rel_assn (uint64_nat_assn) poly_assn (string_assn :: string \<Rightarrow> _))\<^sup>d \<rightarrow>\<^sub>a
    status_assn raw_string_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro] single_valued_uint64_nat_rel[simp]
  unfolding PAC_checker_l_step_def PAC_checker_l_step'_def
    pac_step.case_eq_if Let_def
     is_success_alt_def[symmetric]
    uminus_poly_def[symmetric]
    HOL_list.fold_custom_empty
  by sepref


declare check_step_impl.refine[sepref_fr_rules]
*)

sepref_register PAC_checker_l_step fully_normalize_poly_impl

(* Dead in LPAC: shadowed by LPAC's own PAC_checker_l' / PAC_checker_l_impl
definition PAC_checker_l' where
  \<open>PAC_checker_l' p \<V> A status steps = PAC_checker_l p (\<V>, A) status steps\<close>

lemma PAC_checker_l_alt_def:
  \<open>PAC_checker_l p \<V>A status steps =
    (let (\<V>, A) = \<V>A in PAC_checker_l' p \<V> A status steps)\<close>
  unfolding PAC_checker_l'_def by auto

sepref_definition PAC_checker_l_impl
  is \<open>uncurry4 PAC_checker_l'\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a vars_assn\<^sup>d *\<^sub>a polys_assn\<^sup>d *\<^sub>a (status_assn raw_string_assn)\<^sup>d *\<^sub>a
       (list_assn (pac_step_rel_assn (uint64_nat_assn) poly_assn string_assn))\<^sup>k \<rightarrow>\<^sub>a
     status_assn raw_string_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro]
  unfolding PAC_checker_l_def is_success_alt_def[symmetric] PAC_checker_l_step_alt_def
    nres_bind_let_law[symmetric] PAC_checker_l'_def
  apply (subst nres_bind_let_law)
  by sepref

declare PAC_checker_l_impl.refine[sepref_fr_rules]
*)

abbreviation polys_assn_input where
  \<open>polys_assn_input \<equiv> iam_fmap_assn nat_assn poly_assn\<close>

definition remap_polys_l_dom_err_impl :: \<open>_\<close>  where
  \<open>remap_polys_l_dom_err_impl =
    ''Error during initialisation. Too many polynomials where provided. If this happens,'' @
    ''please report the example to the authors, because something went wrong during '' @
    ''code generation (code generation to arrays is likely to be broken).''\<close>

lemma [sepref_fr_rules]:
  \<open>((uncurry0 (return (remap_polys_l_dom_err_impl))),
    uncurry0 (remap_polys_l_dom_err)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding remap_polys_l_dom_err_def
     remap_polys_l_dom_err_def
     list_assn_pure_conv
   by sepref_to_hoare sep_auto

text \<open>MLton is not able to optimise the calls to pow.\<close>
lemma pow_2_64: \<open>(2::nat) ^ 64 = 18446744073709551616\<close>
  by auto

sepref_register upper_bound_on_dom op_fmap_empty

sepref_definition remap_polys_l_impl
  is \<open>uncurry2 remap_polys_l2\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a vars_assn\<^sup>d *\<^sub>a polys_assn_input\<^sup>d \<rightarrow>\<^sub>a
    status_assn raw_string_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro] indom_mI[dest]
  unfolding remap_polys_l2_def op_fmap_empty_def[symmetric] while_eq_nfoldli[symmetric]
    while_upt_while_direct pow_2_64
    in_dom_m_lookup_iff
    fmlookup'_def[symmetric]
    union_vars_poly_alt_def[symmetric]
  apply (rewrite at \<open>fmupd \<hole>\<close> uint64_of_nat_conv_def[symmetric])
  apply (subst while_upt_while_direct)
  apply simp
  apply (rewrite at \<open>op_fmap_empty\<close> annotate_assn[where A=\<open>polys_assn\<close>])
  by sepref

lemma remap_polys_l2_remap_polys_l:
  \<open>(uncurry2 remap_polys_l2, uncurry2 remap_polys_l) \<in> (Id \<times>\<^sub>r \<langle>Id\<rangle>set_rel) \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI fun_relI nres_relI)
  using remap_polys_l2_remap_polys_l by auto

lemma [sepref_fr_rules]:
   \<open>(uncurry2 remap_polys_l_impl,
     uncurry2 remap_polys_l) \<in> poly_assn\<^sup>k *\<^sub>a vars_assn\<^sup>d *\<^sub>a polys_assn_input\<^sup>d \<rightarrow>\<^sub>a
       status_assn raw_string_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
   using hfcomp_tcomp_pre[OF remap_polys_l2_remap_polys_l remap_polys_l_impl.refine]
   by (auto simp: hrp_comp_def hfprod_def)

sepref_register remap_polys_l

(* Dead in LPAC: shadowed by LPAC's own full_checker_l_impl
sepref_definition full_checker_l_impl
  is \<open>uncurry2 full_checker_l\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a polys_assn_input\<^sup>d *\<^sub>a (list_assn (pac_step_rel_assn (uint64_nat_assn) poly_assn string_assn))\<^sup>k \<rightarrow>\<^sub>a
    status_assn raw_string_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro]
  unfolding full_checker_l_def hs.fold_custom_empty
    union_vars_poly_alt_def[symmetric]
    PAC_checker_l_alt_def
  by sepref
*)

sepref_definition PAC_update_impl
  is \<open>uncurry2 (RETURN ooo fmupd)\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a (polys_assn_input)\<^sup>d \<rightarrow>\<^sub>a polys_assn_input\<close>
  unfolding comp_def
  by sepref

(* Dead in LPAC: shadowed by LPAC's own PAC_empty_impl / empty_vars_impl
sepref_definition PAC_empty_impl
  is \<open>uncurry0 (RETURN fmempty)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a polys_assn_input\<close>
  unfolding op_iam_fmap_empty_def[symmetric] pat_fmap_empty
  by sepref

sepref_definition empty_vars_impl
  is \<open>uncurry0 (RETURN {})\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a vars_assn\<close>
  unfolding hs.fold_custom_empty
  by sepref
*)

(* Dead in LPAC: SML code-printing/hashcode hack \<emdash> LPAC redoes this setup itself
   (keeping it here would clash with LPAC's identical definitions).
text \<open>This is a hack for performance. There is no need to recheck that that a char is valid when
  working on chars coming from strings... It is not that important in most cases, but in our case
  the preformance difference is really large.\<close>


definition unsafe_asciis_of_literal :: \<open>_\<close> where
  \<open>unsafe_asciis_of_literal xs = String.asciis_of_literal xs\<close>

definition unsafe_asciis_of_literal' :: \<open>_\<close> where
  [simp, symmetric, code]: \<open>unsafe_asciis_of_literal' = unsafe_asciis_of_literal\<close>

code_printing
  constant unsafe_asciis_of_literal' \<rightharpoonup>
    (SML) "!(List.map (fn c => let val k = Char.ord c in IntInf.fromInt k end) /o String.explode)"

text \<open>
  Now comes the big and ugly and unsafe hack.

  Basically, we try to avoid the conversion to IntInf when calculating the hash. The performance
  gain is roughly 40\%, which is a LOT and definitively something we need to do. We are aware that the
  SML semantic encourages compilers to optimise conversions, but this does not happen here,
  corroborating our early observation on the verified SAT solver IsaSAT.x
\<close>
definition raw_explode where
  [simp]: \<open>raw_explode = String.explode\<close>
code_printing
  constant raw_explode \<rightharpoonup>
    (SML) "String.explode"

definition \<open>hashcode_literal' s \<equiv>
    foldl (\<lambda>h x. h * 33 + uint32_of_int (of_char x)) 5381
     (raw_explode s)\<close>

definition uint32_of_char :: \<open>char \<Rightarrow> uint32\<close>
  where [code_abbrev]: \<open>uint32_of_char x = uint32_of_int (int_of_char x)\<close>

code_printing
  constant uint32_of_char \<rightharpoonup>
    (SML) "!(Word32.fromInt /o (Char.ord))"

lemma [code]: \<open>hashcode s = hashcode_literal' s\<close>
  unfolding hashcode_literal_def hashcode_list_def
  apply (auto simp: unsafe_asciis_of_literal_def hashcode_list_def
     String.asciis_of_literal_def hashcode_literal_def hashcode_literal'_def)
  done
*)

(*
text \<open>We compile Pastèque in \<^file>\<open>PAC_Checker_MLton.thy\<close>.\<close>
export_code PAC_checker_l_impl PAC_update_impl PAC_empty_impl the_error is_cfailed is_cfound
  int_of_integer Del Add Mult nat_of_integer String.implode remap_polys_l_impl
  fully_normalize_poly_impl union_vars_poly_impl empty_vars_impl
  full_checker_l_impl check_step_impl CSUCCESS
  Extension hashcode_literal' version
  in SML_imp module_name PAC_Checker
*)

section \<open>Correctness theorem\<close>

context poly_embed
begin

definition full_poly_assn where
  \<open>full_poly_assn = hr_comp poly_assn (fully_unsorted_poly_rel O mset_poly_rel)\<close>

definition full_poly_input_assn where
  \<open>full_poly_input_assn = hr_comp
        (hr_comp polys_assn_input
          (\<langle>nat_rel, fully_unsorted_poly_rel O mset_poly_rel\<rangle>fmap_rel))
        polys_rel\<close>

(* Dead in LPAC: correctness-theorem plumbing.
   Only full_poly_assn / full_poly_input_assn above are reused (by LPAC_Efficient_Checker_Synthesis).
definition fully_pac_assn where
  \<open>fully_pac_assn = (list_assn
        (hr_comp (pac_step_rel_assn uint64_nat_assn poly_assn string_assn)
          (p2rel
            (\<langle>nat_rel,
             fully_unsorted_poly_rel O
             mset_poly_rel, var_rel\<rangle>pac_step_rel_raw))))\<close>

definition code_status_assn where
  \<open>code_status_assn = hr_comp (status_assn raw_string_assn)
                            code_status_status_rel\<close>

definition full_vars_assn where
  \<open>full_vars_assn = hr_comp (hs.assn string_assn)
                              (\<langle>var_rel\<rangle>set_rel)\<close>

lemma polys_rel_full_polys_rel:
  \<open>polys_rel_full = Id \<times>\<^sub>r polys_rel\<close>
  by (auto simp: polys_rel_full_def)

definition full_polys_assn :: \<open>_\<close> where
\<open>full_polys_assn = hr_comp (hr_comp polys_assn
                              (\<langle>nat_rel,
                               sorted_poly_rel O mset_poly_rel\<rangle>fmap_rel))
                            polys_rel\<close>
*)

(* Dead in LPAC: old end-to-end correctness theorem (LPAC states its own).
text \<open>

Below is the full correctness theorems. It basically states that:

  \<^enum> assuming that the input polynomials have no duplicate variables


Then:

\<^enum> if the checker returns \<^term>\<open>CFOUND\<close>, the spec is in the ideal
  and the PAC file is correct

\<^enum> if the checker returns \<^term>\<open>CSUCCESS\<close>, the PAC file is correct (but
there is no information on the spec, aka checking failed)

\<^enum> if the checker return \<^term>\<open>CFAILED err\<close>, then checking failed (and
\<^term>\<open>err\<close> \<^emph>\<open>might\<close> give you an indication of the error, but the correctness
theorem does not say anything about that).


The input parameters are:

\<^enum> the specification polynomial represented as a list

\<^enum> the input polynomials as hash map (as an array of option polynomial)

\<^enum> a represention of the PAC proofs.

\<close>

lemma PAC_full_correctness: (* \htmllink{PAC-full-correctness} *)
  \<open>(uncurry2 full_checker_l_impl,
     uncurry2 (\<lambda>spec A _. PAC_checker_specification spec A))
    \<in> (full_poly_assn)\<^sup>k *\<^sub>a (full_poly_input_assn)\<^sup>d *\<^sub>a (fully_pac_assn)\<^sup>k \<rightarrow>\<^sub>a hr_comp
      (code_status_assn \<times>\<^sub>a full_vars_assn \<times>\<^sub>a hr_comp polys_assn
                              (\<langle>nat_rel, sorted_poly_rel O mset_poly_rel\<rangle>fmap_rel))
                            {((st, G), st', G').
                             st = st' \<and> (st \<noteq> FAILED \<longrightarrow> (G, G') \<in> Id \<times>\<^sub>r polys_rel)}\<close>
  using
    full_checker_l_impl.refine[FCOMP full_checker_l_full_checker',
      FCOMP full_checker_spec',
      unfolded full_poly_assn_def[symmetric]
        full_poly_input_assn_def[symmetric]
        fully_pac_assn_def[symmetric]
        code_status_assn_def[symmetric]
        full_vars_assn_def[symmetric]
        polys_rel_full_polys_rel
        hr_comp_prod_conv
        full_polys_assn_def[symmetric]]
      hr_comp_Id2
   by auto
*)

text \<open>

It would be more efficient to move the parsing to Isabelle, as this
would be more memory efficient (and also reduce the TCB). But now
comes the fun part: It cannot work. A stream (of a file) is consumed
by side effects. Assume that this would work. The code could look like:

\<^term>\<open>
  let next_token = read_file file
  in f (next_token)
\<close>

This code is equal to (in the HOL sense of equality):
\<^term>\<open>
  let _ = read_file file;
      next_token = read_file file
  in f (next_token)
\<close>

However, as an hypothetical \<^term>\<open>read_file\<close> changes the underlying stream, we would get the next
token. Remark that this is already a weird point of ML compilers. Anyway, I see currently two
solutions to this problem:

\<^enum> The meta-argument: use it only in the Refinement Framework in a setup where copies are
disallowed. Basically, this works because we can express the non-duplication constraints on the type
level. However, we cannot forbid people from expressing things directly at the HOL level.

\<^enum> On the target language side, model the stream as the stream and the position. Reading takes two
arguments. First, the position to read. Second, the stream (and the current position) to read. If
the position to read does not match the current position, return an error. This would fit the
correctness theorem of the code generation (roughly ``if it terminates without exception, the answer
is the same''), but it is still unsatisfactory.
\<close>

end

(* Dead in LPAC: poly_embed instantiation that only fed the old correctness theorem
definition \<phi> :: \<open>string \<Rightarrow> nat\<close> where
  \<open>\<phi> = (SOME \<phi>. bij \<phi>)\<close>

lemma bij_\<phi>: \<open>bij \<phi>\<close>
  using someI[of \<open>\<lambda>\<phi> :: string \<Rightarrow> nat. bij \<phi>\<close>]
  unfolding \<phi>_def[symmetric]
  using poly_embed_EX
  by auto

global_interpretation PAC: poly_embed where
  \<phi> = \<phi>
  apply standard
  apply (use bij_\<phi> in \<open>auto simp: bij_def\<close>)
  done


text \<open>The full correctness theorem is @{thm PAC.PAC_full_correctness}.\<close>
*)

end
