(*
  Note that large portions of this file were generated using the
  "Fable 5" language model by Anthropic. An in-depth human
  review has not been carried out yet.

  Responsible: Milan Mueller, ALU Freiburg (student)
*)

theory IICF_Assoc_Map
  imports
    Isabelle_LLVM.IICF
    Isabelle_LLVM.Array_of_Array_List
    "HOL-Library.AList"
    IICF_Owning_List
begin

section \<open>A hash map from 64-bit keys to heap-owning values\<close>

text \<open>
  This is the replacement for the placeholder \<open>hm_assn\<close> (used through \<open>hm_fmap_assn\<close>
  in \<^file>\<open>PAC_Map_Rel.thy\<close>, instantiated as
  \<open>polys_assn = hm_fmap_assn uint64_nat_assn poly_assn\<close> in
  \<^file>\<open>PAC_Checker_Relation.thy\<close>).

  Design:

  \<^item> Keys are 64-bit machine words related to @{typ nat} by \<open>unat.assn\<close>. Note that the
    original key assertion \<open>uint64_nat_assn\<close> is based on \<^typ>\<open>64 Word.word\<close> wrapped in
    Native_Word's \<open>uint64\<close>, which is not an \<open>llvm_rep\<close> type; the migration has to switch
    the key assertion to \<open>unat_assn' TYPE(64)\<close> at the call sites anyway.
  \<^item> Since keys are plain numbers, no content hashing is needed: the bucket index is
    \<open>k mod nbins\<close> (a single \<open>ll_urem\<close>). If clustering of proof-step indices ever becomes
    a problem, a Fibonacci multiply can be inserted without touching the structure.
  \<^item> Values are \<^emph>\<open>heap-owning\<close> (for the checker: \<open>poly_assn\<close>, an array-list of monomials).
    Hence the IICF containers are unusable (they compose element assertions via
    \<open>\<langle>the_pure A\<rangle>list_rel\<close>). A bucket is an \<^emph>\<open>owning open list\<close>
    (\<^const>\<open>ol_assn\<close>, \<^file>\<open>IICF_Owning_List.thy\<close>) of (key, value) entry structs whose
    value components are owned; the outer bucket array owns its buckets via
    \<open>Array_of_Array_List.nao_assn\<close> (which, despite its home theory, is generic in the
    bucket assertion). Compared to an array-list bucket this trades contiguous scans
    for per-entry nodes, but buys: O(1) insert without capacity/\<open>max_snat\<close> side
    conditions, single-pointer bucket handles in the outer array (write-back only when
    the head changes), and \<^emph>\<open>reuse\<close> of the proven \<open>ol_seg\<close>/\<open>ol_delete\<close> infrastructure
    instead of re-deriving arl-plus-ownership lemmas per operation.
  \<^item> All bucket traversals are \<^emph>\<open>fused\<close> recursive operations in the style of
    \<^const>\<open>os_rem\<close>/\<^const>\<open>os_eq\<close>: one walk that compares the pure key components and
    acts on the hit node in place. Their abstract counterparts are exactly
    \<^const>\<open>AList.update\<close> (in-place replace of the first occurrence, append at the tail
    on miss) and \<^const>\<open>AList.delete\<close> (filter), so the bucket-level abstraction layer
    comes with library lemmas (@{thm AList.update_conv'} @{thm AList.distinct_update}
    @{thm AList.delete_conv'} @{thm AList.distinct_delete}).
  \<^item> The theory is generic in the value assertion \<open>V :: ('v, 'vi) dr_assn\<close> and, where
    deallocation or duplication of values is needed, parametrized by monadic functions
    \<open>vfree\<close> / \<open>vcopy\<close>: \<open>vfree\<close> via a \<open>MK_FREE (\<upharpoonleft>V) vfree\<close> assumption (the format of
    \<open>sepref_frame_free_rules\<close>), \<open>vcopy\<close> via a Hoare-triple assumption.

  Refinement chain:
    \<open>(nat, 'v) fmap\<close>  \<longleftarrow>[\<open>map_fmap_rel\<close>, in \<^file>\<open>PAC_Map_Rel.thy\<close>]\<longleftarrow>  \<open>nat \<rightharpoonup> 'v\<close>
    \<longleftarrow>[\<open>pam_rel\<close>: bucket invariant]\<longleftarrow>  \<open>(nat \<times> 'v) list list\<close>
    \<longleftarrow>[\<open>pam_assn\<close>: separation logic]\<longleftarrow>  \<open>64 word \<times> bucket ptr\<close>

  The heap-level rules below are stated purely against the bucket decomposition
  (\<open>bss ! pam_bucket_of (length bss) k\<close>); the bucket invariant \<open>pam_invar\<close> only enters
  in the subsequent \<open>hr_comp\<close> step (via \<open>pam_map_of_bucket\<close> etc.), keeping the
  Hoare-triple proofs invariant-free.

  The central design decision is \<^bold>\<open>lookup\<close>: the separation logic has no sharing, so a
  lookup cannot simply hand out the stored value while the map retains it. Options:
  \<^enum> \<^bold>\<open>Copy\<close> (implemented below): \<open>pam_lookup_impl vcopy\<close> returns a fresh copy of the
    value. Simple, sepref-friendly, correct \<comment> \<open>but linear in the polynomial size.\<close>
  \<^enum> \<^bold>\<open>Borrow\<close>: return the value struct and transfer ownership out of the map
    (hole-map style, like @{const nao_nth}/@{const nao_rejoin}), rejoining after use.
    Cleanest at the raw level, but sepref needs a \<open>WITH_SPLIT\<close>-style combinator
    (cf. \<open>Proto_IICF_EOArray\<close> in the Isabelle-LLVM sepref IICF implementations) and a
    restructuring of the abstract checker code around the borrow scope.
  \<^enum> \<^bold>\<open>Fused operations\<close>: never expose lookup; instead synthesize the few checker
    functions that inspect a stored polynomial as single fused operations on the map.

  We start with (1) and keep (2) open as an optimization; \<open>dom_m\<close>-membership tests
  (the most frequent use, via \<open>in_dom_m_lookup_iff\<close>) do not touch values at all and are
  served by \<open>pam_contains_impl\<close>, which has no ownership problem.
\<close>

subsection \<open>Concrete representation\<close>

type_synonym 'vi pam_entry_impl = \<open>64 word \<times> 'vi\<close>
(* Note that using @{term \<open>os_list\<close>} does not imply pure elements *)
type_synonym 'vi pam_bucket_impl = \<open>'vi pam_entry_impl os_list\<close>
type_synonym 'vi pam_impl = \<open>64 word \<times> 'vi pam_bucket_impl ptr\<close>

text \<open>An entry: pure key, owned value.\<close>

definition pam_entry_assn ::
  \<open>('v, 'vi::llvm_rep) dr_assn \<Rightarrow> (nat \<times> 'v, 'vi pam_entry_impl) dr_assn\<close> where
  \<open>pam_entry_assn V \<equiv> mk_assn (\<lambda>(k, v) (ki, vi). \<upharpoonleft>unat.assn k ki ** \<upharpoonleft>V v vi)\<close>

text \<open>The workhorse simp of this theory: atomize the entry assertion whenever both
  arguments are (syntactic) pairs. vcg splits the \<open>EXS\<close>-bound concrete entries of
  \<open>ol_seg_cons\<close> into pair components by itself, so during symbolic execution every
  \<^emph>\<open>applied\<close> occurrence reduces to plain \<open>unat.assn\<close>/\<open>V\<close> atoms (for which the generic
  arithmetic rules and the \<open>vcopy\<close>/\<open>vfree\<close> parameter rules fire directly), while the
  \<^emph>\<open>parameter\<close> occurrence inside \<open>ol_seg (\<upharpoonleft>(pam_entry_assn V))\<close> stays folded.
  IMPORTANT (found the hard way): never unfold \<open>pam_entry_assn_def\<close> itself in the
  operation proofs \<comment> \<open>that also rewrites the \<open>ol_seg\<close> parameter, and vcg's extraction
  then normalizes the pure key component inside the binder
  (\<open>\<upharpoonleft>unat.assn \<leadsto> \<up>\<flat>\<^sub>punat.assn\<close>) on the state side only, after which pre- and
  postcondition disagree on the assertion function and no reassembly ever matches.\<close>\<close>

lemma pam_entry_assn_pair[simp]:
  \<open>\<upharpoonleft>(pam_entry_assn V) (k, v) (ki, vi) = (\<upharpoonleft>unat.assn k ki ** \<upharpoonleft>V v vi)\<close>
  unfolding pam_entry_assn_def by simp

text \<open>A bucket: an owning open list of entries.\<close>

definition pam_bucket_assn ::
  \<open>('v, 'vi::llvm_rep) dr_assn \<Rightarrow> ((nat \<times> 'v) list, 'vi pam_bucket_impl) dr_assn\<close> where
  \<open>pam_bucket_assn V \<equiv> mk_assn (ol_assn (\<upharpoonleft>(pam_entry_assn V)))\<close>

lemma pam_bucket_assn_conv:
  \<open>\<upharpoonleft>(pam_bucket_assn V) = ol_assn (\<upharpoonleft>(pam_entry_assn V))\<close>
  unfolding pam_bucket_assn_def by (intro ext) simp

text \<open>The empty bucket is the null pointer, i.e. \<^const>\<open>init\<close> \<comment> \<open>this is what makes
  @{thm nao_new_init_rl} applicable, so \<open>calloc\<close>-style array initialization suffices.\<close>\<close>

lemma pam_bucket_assn_init: \<open>\<box> \<turnstile> \<upharpoonleft>(pam_bucket_assn V) [] init\<close>
  by (simp add: pam_bucket_assn_conv ol_assn_conv sep_algebra_simps)

text \<open>The map over bucket lists; a length-tagged @{const nao_assn} array of buckets.\<close>

definition pam_assn ::
  \<open>('v, 'vi::llvm_rep) dr_assn \<Rightarrow> ((nat \<times> 'v) list list, 'vi pam_impl) dr_assn\<close> where
  \<open>pam_assn V \<equiv> mk_assn (\<lambda>bss (ni, a).
       \<upharpoonleft>snat.assn (length bss) ni
    ** \<upharpoonleft>(Array_of_Array_List.nao_assn (pam_bucket_assn V) Map.empty) bss a)\<close>


subsection \<open>Bucket index\<close>

definition pam_bucket_of :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>pam_bucket_of n k \<equiv> k mod n\<close>

lemma pam_bucket_of_lt[simp]: \<open>0 < n \<Longrightarrow> pam_bucket_of n k < n\<close>
  by (simp add: pam_bucket_of_def)

text \<open>Bridge between the two word abstractions meeting at the \<open>ll_urem\<close>: the key is a
  full-range \<open>unat\<close>, the bin count a \<open>snat\<close> (as required by @{const nao_nth}). Since
  \<open>k mod n < n \<le> max_snat 64\<close>, the result is MSB-clear and hence a valid \<open>snat\<close> index.
  Proven once here so the operation rules below can simply use it as a \<open>vcg_rule\<close>.\<close>

text \<open>The arithmetic content, separated out: the divisor is nonzero (so the raw
  \<open>ll_urem\<close> rules fire), and the result is MSB-clear with the right \<open>snat\<close> value
  (\<open>unat (ki mod ni) = unat ki mod unat ni < unat ni < 2^63\<close>).\<close>

lemma ll_urem_unat_snat_aux:
  fixes ki ni :: \<open>'l::len2 word\<close>
  assumes I: \<open>snat_invar ni\<close> and NZ: \<open>0 < snat ni\<close>
  shows \<open>ni \<noteq> 0\<close>
    and \<open>snat_invar (ki mod ni)\<close>
    and \<open>snat (ki mod ni) = unat ki mod snat ni\<close>
proof -
  have U: \<open>unat ni = snat ni\<close>
    by (simp add: snat_eq_unat_aux2[OF I])
  have M: \<open>unat (ki mod ni) = unat ki mod unat ni\<close>
    by (simp add: unat_mod)
  have L: \<open>unat (ki mod ni) < unat ni\<close>
    using U NZ M by simp
  have I': \<open>snat_invar (ki mod ni)\<close>
    using I L unfolding snat_invar_def by (auto simp: msb_unat_big)
  show \<open>ni \<noteq> 0\<close>
    using NZ by (cases \<open>ni = 0\<close>) auto
  show \<open>snat_invar (ki mod ni)\<close>
    by (rule I')
  show \<open>snat (ki mod ni) = unat ki mod snat ni\<close>
    using M U by (simp add: snat_eq_unat_aux2[OF I'])
qed

text \<open>The triple itself. Both assertions are \<open>mk_pure_assn\<close>s
  (\<open>assn \<equiv> mk_pure_assn (\<lambda>a c. I c \<and> a = \<alpha> c)\<close> in @{locale standard_opr_abstraction}),
  so unfolding their definitions turns every atom into \<open>\<up>(\<dots>)\<close> and vcg extracts them as
  plain premises \<comment> \<open>this extraction is also why \<open>\<up>(0 < n)\<close> cannot be referenced before
  vcg runs: it is a conjunct of the \<^emph>\<open>goal\<close>'s precondition, not a fact of the proof
  context.\<close> The raw \<open>ll_urem\<close> support (\<open>ll_urem_simp\<close>, \<open>ll_urem_rule\<close>) lives behind
  \<open>llvm_prim_arith_setup\<close>, hence the throwaway interpretation context (the
  raw-arithmetic recipe from \<open>CLAUDE.md\<close>); the aux facts discharge the \<open>ni \<noteq> 0\<close> side
  condition and the postcondition conversion.\<close>

context begin

interpretation llvm_prim_arith_setup .

lemma ll_urem_unat_snat_rule:
  \<open>llvm_htriple
    (\<upharpoonleft>unat.assn k ki ** \<upharpoonleft>snat.assn n ni ** \<up>(0 < n))
    (ll_urem ki ni)
    (\<lambda>ri. \<upharpoonleft>snat.assn (k mod n) ri ** \<upharpoonleft>unat.assn k ki ** \<upharpoonleft>snat.assn n ni)\<close>
  supply [simp] = unat.assn_def snat.assn_def mk_pure_assn_def ll_urem_unat_snat_aux
  by vcg

end

subsection \<open>Bucket operations\<close>

text \<open>All bucket walks are recursive \<open>partial_function\<close>s following the
  \<^const>\<open>os_rem\<close>/\<^const>\<open>os_eq\<close> template; the proofs are inductions with one
  \<open>subst \<dots>.simps\<close> per case (never \<open>unfolding\<close>, which loops), the IH as \<open>vcg_rules\<close>,
  and the null-pointer cases split off before \<open>vcg\<close>
  (cf. \<open>ol_eq_rule\<close> in \<^file>\<open>IICF_Owning_List.thy\<close>).\<close>

subsubsection \<open>Singleton-bucket creation\<close>

text \<open>The one place where an entry assertion must be \<^emph>\<open>reassembled\<close> from nothing but a
  fresh node: the \<open>p = null\<close> branch of update. A general prepend rule
  (\<open>\<dots> ** ol_seg A es p null \<dots>\<close>) is useless as a \<open>vcg_rule\<close> here: in the empty case
  its \<open>ol_seg\<close> precondition atom would have to be conjured with schematic \<open>?es\<close> from
  an empty state, which frame inference cannot do. So the rule is specialized to the
  singleton case, and its residual \<open>ENTAILS\<close> is discharged by a private lemma matching
  the goal verbatim (the recipe from the proof notes in \<open>CLAUDE.md\<close>).\<close>

context begin

private lemma pam_entry_prepend_empty_aux:
  \<open>\<flat>\<^sub>punat.assn k ki \<Longrightarrow>
   ENTAILS
     (\<upharpoonleft>ll_bpto (Node (ki, vi) null) r ** \<upharpoonleft>V v vi)
     (ol_seg (\<upharpoonleft>(pam_entry_assn V)) [(k, v)] r null)\<close>
  unfolding vcg_tag_defs ENTAILS_def
  apply (simp only: ol_seg_cons ol_seg_empty sep_conj_exists)
  apply (rule entails_exI[where x = \<open>(ki, vi)\<close>])
  apply (rule entails_exI[where x = null])
  by (simp add: extract_pure_assn[OF unat.assn_pure] sep_algebra_simps)

lemma pam_entry_prepend_empty_rule[vcg_rules]:
  \<open>llvm_htriple
    (\<upharpoonleft>unat.assn k ki ** \<upharpoonleft>V v vi)
    (os_prepend (ki, vi) null)
    (\<lambda>r. ol_seg (\<upharpoonleft>(pam_entry_assn V)) [(k, v)] r null)\<close>
  unfolding os_prepend_def
  apply vcg
  subgoal by (rule pam_entry_prepend_empty_aux; assumption)
  done

end

subsubsection \<open>Membership (the workhorse for \<open>\<in># dom_m\<close> checks); values untouched\<close>

partial_function (M) pam_bucket_contains_impl ::
  \<open>64 word \<Rightarrow> 'vi::llvm_rep pam_bucket_impl \<Rightarrow> 1 word llM\<close> where
  \<open>pam_bucket_contains_impl k p = (if p = null then Mreturn 0
    else doM {
      n \<leftarrow> ll_load p;
      eq \<leftarrow> ll_icmp_eq (fst (node.val n)) k;
      if to_bool eq then Mreturn 1
      else pam_bucket_contains_impl k (node.next n)
    })\<close>

text \<open>First-order, so the recursion equations export directly.\<close>
lemmas [llvm_code] = pam_bucket_contains_impl.simps

lemma pam_bucket_contains_impl_rule[vcg_rules]:
  \<open>llvm_htriple
    (\<upharpoonleft>(pam_bucket_assn V) es p ** \<upharpoonleft>unat.assn k ki)
    (pam_bucket_contains_impl ki p)
    (\<lambda>r. \<upharpoonleft>(pam_bucket_assn V) es p ** \<upharpoonleft>unat.assn k ki
       ** \<upharpoonleft>bool.assn (k \<in> fst ` set es) r)\<close>
  unfolding pam_bucket_assn_conv ol_assn_conv
proof (induction es arbitrary: p)
  case Nil
  show ?case
    supply [simp] = bool.assn_def
    apply (subst pam_bucket_contains_impl.simps)
    by vcg
next
  case (Cons e es)
  interpret llvm_prim_ctrl_setup .
  note [vcg_rules] = Cons.IH
  show ?case
    supply [simp, named_ss fri_prepare_simps] = ol_seg_cons
    supply [simp] = bool.assn_def sep_conj_exists
    apply (subst pam_bucket_contains_impl.simps)
    apply (cases \<open>p = null\<close>; cases e; simp)
    by vcg
qed

subsubsection \<open>Lookup with copy\<close>

text \<open>Design option 1 (see the discussion above). Parametrized by \<open>vcopy\<close>, which must
  duplicate a value without consuming the original. If the key is absent, the returned
  value slot is \<open>init\<close> and must not be used. The abstract result is
  \<open>map_of es k\<close> \<comment> \<open>\<^const>\<open>map_of\<close> picks the first occurrence, exactly like the walk,
  so no distinctness assumption is needed at this level.\<close>

  NOTE (code generation): higher-order in \<open>vcopy\<close>; each concrete instantiation must be
  specialized into its own first-order \<open>[llvm_code]\<close> definition before export
  (cf. \<open>ol_delete\<close> in \<^file>\<open>IICF_Owning_List.thy\<close>).\<close>

partial_function (M) pam_bucket_lookup_impl ::
  \<open>('vi \<Rightarrow> 'vi llM) \<Rightarrow> 64 word \<Rightarrow> 'vi::llvm_rep pam_bucket_impl \<Rightarrow> (1 word \<times> 'vi) llM\<close>
  where
  \<open>pam_bucket_lookup_impl vcopy k p = (if p = null then Mreturn (0, init)
    else doM {
      n \<leftarrow> ll_load p;
      eq \<leftarrow> ll_icmp_eq (fst (node.val n)) k;
      if to_bool eq then doM {
        v' \<leftarrow> vcopy (snd (node.val n));
        Mreturn (1, v')
      }
      else pam_bucket_lookup_impl vcopy k (node.next n)
    })\<close>

context begin

text \<open>Residual reassembly entailment of the recursive (miss) branch, stated verbatim
  (the returned flag \<open>xa\<close> is only \<^emph>\<open>propositionally\<close> tied to the lookup result, so the
  two \<open>if\<close>s need a case split fri cannot do; and \<open>map_of ((a, b) # es) k\<close> reduces only
  under the branch knowledge \<open>k \<noteq> a\<close>).\<close>

private lemma pam_bucket_lookup_miss_aux:
  assumes \<open>k \<noteq> a\<close> \<open>\<flat>\<^sub>punat.assn a aa\<close> \<open>\<flat>\<^sub>punat.assn k ki\<close>
    \<open>(\<exists>y. map_of es k = Some y) = (xa \<noteq> 0)\<close>
  shows \<open>ENTAILS
     (ol_seg (\<upharpoonleft>(pam_entry_assn V)) es x null **
      (if xa = 0 then \<box> else \<upharpoonleft>V (the (map_of es k)) xaa) **
      \<upharpoonleft>ll_bpto (Node (aa, ba) x) p ** \<upharpoonleft>V b ba)
     (EXS aa' ba' x'.
        \<upharpoonleft>ll_bpto (Node (aa', ba') x') p ** \<upharpoonleft>unat.assn a aa' ** \<upharpoonleft>V b ba' **
        ol_seg (\<upharpoonleft>(pam_entry_assn V)) es x' null ** \<upharpoonleft>unat.assn k ki **
        \<up>((\<exists>y. map_of es k = Some y) = (xa \<noteq> 0)) **
        (if \<exists>y. map_of es k = Some y then \<upharpoonleft>V (the (map_of ((a, b) # es) k)) xaa
         else \<box>))\<close>
proof -
  from assms(1) have [simp]: \<open>a = k \<longleftrightarrow> False\<close> \<open>k = a \<longleftrightarrow> False\<close> by auto
  note [simp] = assms(2,3)
  show ?thesis
    using assms(4)
    unfolding vcg_tag_defs ENTAILS_def
    apply -
    apply (rule entails_exI[where x = aa])
    apply (rule entails_exI[where x = ba])
    apply (rule entails_exI[where x = x])
    apply (cases \<open>xa = 0\<close>)
    subgoal
      apply (simp add: extract_pure_assn[OF unat.assn_pure] sep_algebra_simps)
      by (simp add: sep_conj_aci entails_refl)
    subgoal
      apply (simp add: extract_pure_assn[OF unat.assn_pure] sep_algebra_simps)
      by (simp add: sep_conj_aci)
    done
qed

lemma pam_bucket_lookup_impl_rule[vcg_rules]:
  assumes VCOPY: \<open>\<And>v vi. llvm_htriple (\<upharpoonleft>V v vi) (vcopy vi) (\<lambda>r. \<upharpoonleft>V v vi ** \<upharpoonleft>V v r)\<close>
  shows \<open>llvm_htriple
    (\<upharpoonleft>(pam_bucket_assn V) es p ** \<upharpoonleft>unat.assn k ki)
    (pam_bucket_lookup_impl vcopy ki p)
    (\<lambda>(f, vi). \<upharpoonleft>(pam_bucket_assn V) es p ** \<upharpoonleft>unat.assn k ki
       ** \<upharpoonleft>bool.assn (map_of es k \<noteq> None) f
       ** (if map_of es k \<noteq> None then \<upharpoonleft>V (the (map_of es k)) vi else \<box>))\<close>
  unfolding pam_bucket_assn_conv ol_assn_conv
proof (induction es arbitrary: p)
  case Nil
  show ?case
    supply [simp] = bool.assn_def
    apply (subst pam_bucket_lookup_impl.simps)
    by vcg
next
  case (Cons e es)
  interpret llvm_prim_ctrl_setup .
  note [vcg_rules] = Cons.IH VCOPY
  show ?case
    supply [simp, named_ss fri_prepare_simps] = ol_seg_cons
    supply [simp] = bool.assn_def sep_conj_exists
    apply (subst pam_bucket_lookup_impl.simps)
    apply (cases \<open>p = null\<close>; cases e; simp)
    apply vcg
    subgoal by (rule pam_bucket_lookup_miss_aux; assumption)
    done
qed

end

subsubsection \<open>Update (\<open>fmupd\<close>)\<close>

text \<open>\<^bold>\<open>Consumes\<close> the value (the natural choice in a sharing-free logic \<comment> \<open>note the
  original Imperative-HOL version had \<open>poly_assn\<^sup>k\<close> here, which worked only because
  values were pure there; call sites must be adapted to \<open>V\<^sup>d\<close>.\<close> If the key is present,
  the old value is freed and replaced in the node; otherwise a fresh node is appended
  at the tail (where the walk ends) \<comment> \<open>which is exactly \<^const>\<open>AList.update\<close>.\<close>
  No capacity precondition: linked nodes never overflow an index type.\<close>

partial_function (M) pam_bucket_update_impl ::
  \<open>('vi \<Rightarrow> unit llM) \<Rightarrow> 64 word \<Rightarrow> 'vi \<Rightarrow> 'vi::llvm_rep pam_bucket_impl
    \<Rightarrow> 'vi pam_bucket_impl llM\<close> where
  \<open>pam_bucket_update_impl vfree k v p = (if p = null then os_prepend (k, v) null
    else doM {
      n \<leftarrow> ll_load p;
      eq \<leftarrow> ll_icmp_eq (fst (node.val n)) k;
      if to_bool eq then doM {
        vfree (snd (node.val n));
        ll_store (Node (k, v) (node.next n)) p;
        Mreturn p
      } else doM {
        q \<leftarrow> pam_bucket_update_impl vfree k v (node.next n);
        ll_store (Node (node.val n) q) p;
        Mreturn p
      }
    })\<close>

lemma pam_bucket_update_impl_rule[vcg_rules]:
  assumes VFREE: \<open>MK_FREE (\<upharpoonleft>V) vfree\<close>
  shows \<open>llvm_htriple
    (\<upharpoonleft>(pam_bucket_assn V) es p ** \<upharpoonleft>unat.assn k ki ** \<upharpoonleft>V v vi)
    (pam_bucket_update_impl vfree ki vi p)
    (\<lambda>r. \<upharpoonleft>(pam_bucket_assn V) (AList.update k v es) r ** \<upharpoonleft>unat.assn k ki)\<close>
  unfolding pam_bucket_assn_conv ol_assn_conv
proof (induction es arbitrary: p)
  case Nil
  show ?case
    apply (subst pam_bucket_update_impl.simps)
    by vcg
next
  case (Cons e es)
  interpret llvm_prim_ctrl_setup .
  note [vcg_rules] = Cons.IH MK_FREED[OF VFREE]
  show ?case
    supply [simp, named_ss fri_prepare_simps] = ol_seg_cons
    supply [simp] = bool.assn_def sep_conj_exists
    apply (subst pam_bucket_update_impl.simps)
    apply (cases \<open>p = null\<close>; cases e; simp)
    by vcg
qed

subsubsection \<open>Deletion (\<open>fmdrop\<close>, for Del steps)\<close>

text \<open>The \<^const>\<open>os_rem\<close> recursion with the key as match criterion and a \<open>vfree\<close> on hit;
  removes \<^emph>\<open>all\<close> matching nodes, so the abstract effect is \<^const>\<open>AList.delete\<close> (a
  filter) with no distinctness precondition \<comment> \<open>the swap-remove trick of an array-list
  bucket and its permutation caveat disappear.\<close>\<close>

partial_function (M) pam_bucket_delete_impl ::
  \<open>('vi \<Rightarrow> unit llM) \<Rightarrow> 64 word \<Rightarrow> 'vi::llvm_rep pam_bucket_impl
    \<Rightarrow> 'vi pam_bucket_impl llM\<close> where
  \<open>pam_bucket_delete_impl vfree k p = (if p = null then Mreturn null
    else doM {
      n \<leftarrow> ll_load p;
      q \<leftarrow> pam_bucket_delete_impl vfree k (node.next n);
      eq \<leftarrow> ll_icmp_eq (fst (node.val n)) k;
      if to_bool eq then doM {
        vfree (snd (node.val n));
        ll_free p;
        Mreturn q
      } else doM {
        ll_store (Node (node.val n) q) p;
        Mreturn p
      }
    })\<close>

lemma pam_bucket_delete_impl_rule[vcg_rules]:
  assumes VFREE: \<open>MK_FREE (\<upharpoonleft>V) vfree\<close>
  shows \<open>llvm_htriple
    (\<upharpoonleft>(pam_bucket_assn V) es p ** \<upharpoonleft>unat.assn k ki)
    (pam_bucket_delete_impl vfree ki p)
    (\<lambda>r. \<upharpoonleft>(pam_bucket_assn V) (AList.delete k es) r ** \<upharpoonleft>unat.assn k ki)\<close>
  unfolding pam_bucket_assn_conv ol_assn_conv
proof (induction es arbitrary: p)
  case Nil
  show ?case
    apply (subst pam_bucket_delete_impl.simps)
    by vcg
next
  case (Cons e es)
  interpret llvm_prim_ctrl_setup .
  note [vcg_rules] = Cons.IH MK_FREED[OF VFREE]
  show ?case
    supply [simp, named_ss fri_prepare_simps] = ol_seg_cons
    supply [simp] = bool.assn_def sep_conj_exists AList.delete_eq
    apply (subst pam_bucket_delete_impl.simps)
    apply (cases \<open>p = null\<close>; cases e; simp)
    by vcg
qed

subsubsection \<open>Deallocation\<close>

text \<open>Deep free is \<^const>\<open>ol_delete\<close> with an entry free function; the composed
  \<open>MK_FREE\<close> falls out of the proven \<open>ol_assn_free\<close>.\<close>

definition pam_entry_free_impl ::
  \<open>('vi \<Rightarrow> unit llM) \<Rightarrow> 'vi::llvm_rep pam_entry_impl \<Rightarrow> unit llM\<close> where
  \<open>pam_entry_free_impl vfree \<equiv> \<lambda>(_, v). vfree v\<close>

lemma pam_entry_assn_free:
  assumes \<open>MK_FREE (\<upharpoonleft>V) vfree\<close>
  shows \<open>MK_FREE (\<upharpoonleft>(pam_entry_assn V)) (pam_entry_free_impl vfree)\<close>
  supply [vcg_rules] = MK_FREED[OF assms]
  apply (rule MK_FREEI)
  unfolding pam_entry_assn_def pam_entry_free_impl_def
  subgoal for a c
    apply (cases a; cases c; simp)
    by vcg
  done

definition pam_bucket_free_impl ::
  \<open>('vi \<Rightarrow> unit llM) \<Rightarrow> 'vi::llvm_rep pam_bucket_impl \<Rightarrow> unit llM\<close> where
  \<open>pam_bucket_free_impl vfree \<equiv> ol_delete (pam_entry_free_impl vfree)\<close>

lemma pam_bucket_assn_free:
  assumes \<open>MK_FREE (\<upharpoonleft>V) vfree\<close>
  shows \<open>MK_FREE (\<upharpoonleft>(pam_bucket_assn V)) (pam_bucket_free_impl vfree)\<close>
  unfolding pam_bucket_free_impl_def pam_bucket_assn_conv
  by (rule ol_assn_free[OF pam_entry_assn_free[OF assms]])


subsection \<open>Map operations\<close>

text \<open>Creation.\<close>

definition pam_new_impl :: \<open>64 word \<Rightarrow> 'vi::llvm_rep pam_impl llM\<close> where [llvm_code]:
  \<open>pam_new_impl n \<equiv> doM {
    a \<leftarrow> nao_new TYPE('vi pam_bucket_impl) n;
    Mreturn (n, a)
  }\<close>

lemma pam_new_impl_rule[vcg_rules]:
  \<open>llvm_htriple
    (\<upharpoonleft>snat.assn n ni)
    (pam_new_impl ni)
    (\<lambda>r. \<upharpoonleft>(pam_assn V) (replicate n []) r)\<close>
  unfolding pam_new_impl_def pam_assn_def
  supply [vcg_rules] = nao_new_init_rl[OF pam_bucket_assn_init]
  by vcg

text \<open>Membership. The bucket is borrowed from the outer array (hole map), scanned
  read-only, and rejoined unchanged.\<close>

definition pam_contains_impl ::
  \<open>64 word \<Rightarrow> 'vi::llvm_rep pam_impl \<Rightarrow> 1 word llM\<close> where [llvm_code]:
  \<open>pam_contains_impl k \<equiv> \<lambda>(n, a). doM {
    i \<leftarrow> ll_urem k n;
    bin \<leftarrow> nao_nth a i;
    found \<leftarrow> pam_bucket_contains_impl k bin;
    nao_rejoin a i;
    Mreturn found
  }\<close>

lemma pam_contains_impl_rule[vcg_rules]:
  \<open>llvm_htriple
    (\<upharpoonleft>(pam_assn V) bss p ** \<upharpoonleft>unat.assn k ki ** \<up>(bss \<noteq> []))
    (pam_contains_impl ki p)
    (\<lambda>r. \<upharpoonleft>(pam_assn V) bss p ** \<upharpoonleft>unat.assn k ki
       ** \<upharpoonleft>bool.assn (k \<in> fst ` set (bss ! pam_bucket_of (length bss) k)) r)\<close>
  unfolding pam_contains_impl_def pam_assn_def pam_bucket_of_def
  supply [vcg_rules] = ll_urem_unat_snat_rule
  apply (cases p; simp)
  by vcg

text \<open>Lookup with copy.\<close>

definition pam_lookup_impl ::
  \<open>('vi \<Rightarrow> 'vi llM) \<Rightarrow> 64 word \<Rightarrow> 'vi::llvm_rep pam_impl \<Rightarrow> (1 word \<times> 'vi) llM\<close>
  where
  \<open>pam_lookup_impl vcopy k \<equiv> \<lambda>(n, a). doM {
    i \<leftarrow> ll_urem k n;
    bin \<leftarrow> nao_nth a i;
    r \<leftarrow> pam_bucket_lookup_impl vcopy k bin;
    nao_rejoin a i;
    Mreturn r
  }\<close>

lemma pam_lookup_impl_rule[vcg_rules]:
  assumes VCOPY: \<open>\<And>v vi. llvm_htriple (\<upharpoonleft>V v vi) (vcopy vi) (\<lambda>r. \<upharpoonleft>V v vi ** \<upharpoonleft>V v r)\<close>
  shows \<open>llvm_htriple
    (\<upharpoonleft>(pam_assn V) bss p ** \<upharpoonleft>unat.assn k ki ** \<up>(bss \<noteq> []))
    (pam_lookup_impl vcopy ki p)
    (\<lambda>(f, vi). \<upharpoonleft>(pam_assn V) bss p ** \<upharpoonleft>unat.assn k ki
       ** \<upharpoonleft>bool.assn (map_of (bss ! pam_bucket_of (length bss) k) k \<noteq> None) f
       ** (if map_of (bss ! pam_bucket_of (length bss) k) k \<noteq> None
           then \<upharpoonleft>V (the (map_of (bss ! pam_bucket_of (length bss) k) k)) vi else \<box>))\<close>
  unfolding pam_lookup_impl_def pam_assn_def pam_bucket_of_def
  supply [vcg_rules] = ll_urem_unat_snat_rule pam_bucket_lookup_impl_rule[OF VCOPY]
  apply (cases p; simp)
  by vcg

text \<open>It seems like in the PAC checker, every lookup is guarded with an assertion that
  the key is present so we only implement @{term op_map_the_lookup} and avoid having
  to define refinment assertion for optionals.\<close>
definition \<open>pam_the_lookup_impl vcopy k p \<equiv> doM { (_, v) \<leftarrow> pam_lookup_impl vcopy k p; Mreturn v }\<close> 

(* Probably not needed? *)
(* lemma pam_the_lookup_impl_rule[vcg_rules]:
 *   assumes VCOPY: \<open>\<And>v vi. llvm_htriple (\<upharpoonleft>V v vi) (vcopy vi) (\<lambda>r. \<upharpoonleft>V v vi ** \<upharpoonleft>V v r)\<close>
 *   shows \<open>llvm_htriple
 *     (\<upharpoonleft>(pam_assn V) bss p ** \<upharpoonleft>unat.assn k ki ** \<up>(bss \<noteq> [] \<and> map_of (bss ! pam_bucket_of (lenght bss) k) k \<noteq> None))
 *     (pam_the_lookup_impl vcopy ki p)
 *     (\<lambda>vi. \<upharpoonleft>(pam_ass V) bss p ** \<upharpoonleft>unat.assn k ki ** \<upharpoonleft>V (the (map_of (bss ! pam_bucket_of (length bss) k) k)) vi)
 *     \<close> *)


text \<open>Update. The bucket is taken out of the array, rebuilt by the fused walk (its head
  pointer changes iff the bucket was empty), and stored back into the hole.\<close>

definition pam_update_impl ::
  \<open>('vi \<Rightarrow> unit llM) \<Rightarrow> 64 word \<Rightarrow> 'vi \<Rightarrow> 'vi::llvm_rep pam_impl \<Rightarrow> 'vi pam_impl llM\<close>
  where
  \<open>pam_update_impl vfree k v \<equiv> \<lambda>(n, a). doM {
    i \<leftarrow> ll_urem k n;
    bin \<leftarrow> nao_nth a i;
    bin \<leftarrow> pam_bucket_update_impl vfree k v bin;
    a \<leftarrow> nao_upd a i bin;
    Mreturn (n, a)
  }\<close>

text \<open>Abstract counterpart on bucket lists.\<close>

definition pam_upd :: \<open>nat \<Rightarrow> 'v \<Rightarrow> (nat \<times> 'v) list list \<Rightarrow> (nat \<times> 'v) list list\<close> where
  \<open>pam_upd k v bss = (let i = pam_bucket_of (length bss) k in
     bss[i := AList.update k v (bss ! i)])\<close>

lemma pam_update_impl_rule[vcg_rules]:
  assumes VFREE: \<open>MK_FREE (\<upharpoonleft>V) vfree\<close>
  shows \<open>llvm_htriple
    (\<upharpoonleft>(pam_assn V) bss p ** \<upharpoonleft>unat.assn k ki ** \<upharpoonleft>V v vi ** \<up>(bss \<noteq> []))
    (pam_update_impl vfree ki vi p)
    (\<lambda>r. \<upharpoonleft>(pam_assn V) (pam_upd k v bss) r ** \<upharpoonleft>unat.assn k ki)\<close>
  \<comment> \<open>Note: NO \<open>max_snat\<close> bound on the bucket length \<comment> \<open>prepended nodes need no capacity.\<close>\<close>
  unfolding pam_update_impl_def pam_assn_def pam_upd_def Let_def pam_bucket_of_def
  supply [vcg_rules] = ll_urem_unat_snat_rule pam_bucket_update_impl_rule[OF VFREE]
  apply (cases p; simp)
  by vcg

text \<open>Deletion.\<close>

definition pam_delete_impl ::
  \<open>('vi \<Rightarrow> unit llM) \<Rightarrow> 64 word \<Rightarrow> 'vi::llvm_rep pam_impl \<Rightarrow> 'vi pam_impl llM\<close>
  where
  \<open>pam_delete_impl vfree k \<equiv> \<lambda>(n, a). doM {
    i \<leftarrow> ll_urem k n;
    bin \<leftarrow> nao_nth a i;
    bin \<leftarrow> pam_bucket_delete_impl vfree k bin;
    a \<leftarrow> nao_upd a i bin;
    Mreturn (n, a)
  }\<close>

definition pam_del :: \<open>nat \<Rightarrow> (nat \<times> 'v) list list \<Rightarrow> (nat \<times> 'v) list list\<close> where
  \<open>pam_del k bss = (let i = pam_bucket_of (length bss) k in
     bss[i := AList.delete k (bss ! i)])\<close>

lemma pam_delete_impl_rule[vcg_rules]:
  assumes VFREE: \<open>MK_FREE (\<upharpoonleft>V) vfree\<close>
  shows \<open>llvm_htriple
    (\<upharpoonleft>(pam_assn V) bss p ** \<upharpoonleft>unat.assn k ki ** \<up>(bss \<noteq> []))
    (pam_delete_impl vfree ki p)
    (\<lambda>r. \<upharpoonleft>(pam_assn V) (pam_del k bss) r ** \<upharpoonleft>unat.assn k ki)\<close>
  \<comment> \<open>No distinctness precondition: the fused walk removes ALL matching nodes
    \<open>= AList.delete =\<close> the filter in \<open>pam_del\<close>.\<close>
  unfolding pam_delete_impl_def pam_assn_def pam_del_def Let_def pam_bucket_of_def
  supply [vcg_rules] = ll_urem_unat_snat_rule pam_bucket_delete_impl_rule[OF VFREE]
  apply (cases p; simp)
  by vcg

text \<open>Deallocation.\<close>

definition pam_free_impl ::
  \<open>('vi \<Rightarrow> unit llM) \<Rightarrow> 'vi::llvm_rep pam_impl \<Rightarrow> unit llM\<close> where
  \<open>pam_free_impl vfree \<equiv> \<lambda>(n, a). nao_free (pam_bucket_free_impl vfree) a n\<close>

lemma pam_free_impl_rule:
  assumes VFREE: \<open>MK_FREE (\<upharpoonleft>V) vfree\<close>
  shows \<open>llvm_htriple (\<upharpoonleft>(pam_assn V) bss p) (pam_free_impl vfree p) (\<lambda>_. \<box>)\<close>
  supply [vcg_rules] = nao_free_rl[OF MK_FREED[OF pam_bucket_assn_free[OF VFREE]]]
  unfolding pam_free_impl_def pam_assn_def
  apply (cases p; simp)
  by vcg

    
subsection \<open>Bucket-level abstraction\<close>

definition pam_invar :: \<open>(nat \<times> 'v) list list \<Rightarrow> bool\<close> where
  \<open>pam_invar bss \<longleftrightarrow> bss \<noteq> [] \<and> distinct (map fst (concat bss)) \<and>
     (\<forall>i < length bss. \<forall>(k, _) \<in> set (bss ! i). pam_bucket_of (length bss) k = i)\<close>

definition pam_map_of :: \<open>(nat \<times> 'v) list list \<Rightarrow> (nat \<rightharpoonup> 'v)\<close> where
  \<open>pam_map_of \<equiv> map_of \<circ> concat\<close>

definition pam_rel :: \<open>((nat \<times> 'v) list list \<times> (nat \<rightharpoonup> 'v)) set\<close> where
  \<open>pam_rel \<equiv> br pam_map_of pam_invar\<close>

text \<open>Key/entry sets of the AList operations (the library provides the \<open>map_of\<close>-level
  facts @{thm AList.update_conv'} / @{thm AList.delete_conv'}; the invariant needs the
  set level, too).\<close>

lemma fst_set_alist_update: \<open>fst ` set (AList.update k v al) = insert k (fst ` set al)\<close>
  by (induction al) auto

lemma set_alist_update_subset: \<open>set (AList.update k v al) \<subseteq> insert (k, v) (set al)\<close>
  by (induction al) auto

lemma fst_set_alist_delete: \<open>fst ` set (AList.delete k al) = fst ` set al - {k}\<close>
  by (induction al) auto

lemma set_alist_delete_subset: \<open>set (AList.delete k al) \<subseteq> set al\<close>
  by (auto simp: AList.delete_eq)

text \<open>Under the invariant, the whole map restricted to \<open>k\<close> lives in \<open>k\<close>'s bucket; this
  is the abstract-side justification for all the heap rules above, which only speak
  about \<open>bss ! pam_bucket_of (length bss) k\<close>. The shared skeleton of all six lemmas
  below: split \<open>concat bss\<close> around bucket \<open>pam_bucket_of (length bss) k\<close>
  (@{thm id_take_nth_drop} / @{thm upd_conv_take_nth_drop}); the bucket-of condition
  makes \<open>k\<close> absent from the two outer parts.\<close>

context
  fixes bss :: \<open>(nat \<times> 'v) list list\<close> and k :: nat
  assumes I: \<open>pam_invar bss\<close>
begin

private lemma NE: \<open>bss \<noteq> []\<close>
  and D: \<open>distinct (map fst (concat bss))\<close>
  using I by (auto simp: pam_invar_def)

private lemma B: \<open>j < length bss \<Longrightarrow> (k', v') \<in> set (bss ! j)
  \<Longrightarrow> pam_bucket_of (length bss) k' = j\<close> for j k' v'
  using I by (auto simp: pam_invar_def)

private lemma IB: \<open>pam_bucket_of (length bss) k < length bss\<close>
  using NE by simp

private lemma concat_orig:
  \<open>concat bss = concat (take (pam_bucket_of (length bss) k) bss)
     @ bss ! pam_bucket_of (length bss) k
     @ concat (drop (Suc (pam_bucket_of (length bss) k)) bss)\<close>
proof -
  have \<open>bss = take (pam_bucket_of (length bss) k) bss
     @ bss ! pam_bucket_of (length bss) k
     # drop (Suc (pam_bucket_of (length bss) k)) bss\<close>
    by (rule id_take_nth_drop[OF IB])
  then show ?thesis
    by (metis concat.simps(2) concat_append)
qed

private lemma concat_upd:
  \<open>concat (bss[pam_bucket_of (length bss) k := b])
   = concat (take (pam_bucket_of (length bss) k) bss)
     @ b @ concat (drop (Suc (pam_bucket_of (length bss) k)) bss)\<close> for b
proof -
  have \<open>bss[pam_bucket_of (length bss) k := b]
     = take (pam_bucket_of (length bss) k) bss
       @ b # drop (Suc (pam_bucket_of (length bss) k)) bss\<close>
    by (rule upd_conv_take_nth_drop[OF IB])
  then show ?thesis
    by (metis concat.simps(2) concat_append)
qed

private lemma take_nomem: \<open>k \<notin> fst ` set (concat (take (pam_bucket_of (length bss) k) bss))\<close>
proof
  assume \<open>k \<in> fst ` set (concat (take (pam_bucket_of (length bss) k) bss))\<close>
  then obtain ys where Y: \<open>ys \<in> set (take (pam_bucket_of (length bss) k) bss)\<close>
    \<open>k \<in> fst ` set ys\<close> by auto
  from Y(1) obtain j where J: \<open>j < pam_bucket_of (length bss) k\<close> \<open>ys = bss ! j\<close>
    using IB by (auto simp: in_set_conv_nth)
  from Y(2) J obtain v' where \<open>(k, v') \<in> set (bss ! j)\<close> by auto
  with B[of j] J IB show False by auto
qed

private lemma drop_nomem:
  \<open>k \<notin> fst ` set (concat (drop (Suc (pam_bucket_of (length bss) k)) bss))\<close>
proof
  assume \<open>k \<in> fst ` set (concat (drop (Suc (pam_bucket_of (length bss) k)) bss))\<close>
  then obtain ys where Y: \<open>ys \<in> set (drop (Suc (pam_bucket_of (length bss) k)) bss)\<close>
    \<open>k \<in> fst ` set ys\<close> by auto
  from Y(1) obtain j where J: \<open>Suc (pam_bucket_of (length bss) k) + j < length bss\<close>
    \<open>ys = bss ! (Suc (pam_bucket_of (length bss) k) + j)\<close>
    by (metis in_set_drop_conv_nth le_Suc_ex)
  from Y(2) J obtain v' where \<open>(k, v') \<in> set (bss ! (Suc (pam_bucket_of (length bss) k) + j))\<close>
    by auto
  with B[of \<open>Suc (pam_bucket_of (length bss) k) + j\<close>] J show False
    by (metis lessI not_add_less1)
qed

private lemma take_None: \<open>map_of (concat (take (pam_bucket_of (length bss) k) bss)) k = None\<close>
  using take_nomem by (simp add: map_of_eq_None_iff)

private lemma drop_None:
  \<open>map_of (concat (drop (Suc (pam_bucket_of (length bss) k)) bss)) k = None\<close>
  using drop_nomem by (simp add: map_of_eq_None_iff)

lemma pam_map_of_bucket: \<open>pam_map_of bss k = map_of (bss ! pam_bucket_of (length bss) k) k\<close>
  unfolding pam_map_of_def comp_def
  by (subst concat_orig)
    (simp add: map_of_append map_add_def take_None drop_None split: option.splits)

lemma pam_contains_correct:
  \<open>k \<in> fst ` set (bss ! pam_bucket_of (length bss) k) \<longleftrightarrow> k \<in> dom (pam_map_of bss)\<close>
  using pam_map_of_bucket map_of_eq_None_iff[of \<open>bss ! pam_bucket_of (length bss) k\<close> k]
  by (auto simp: dom_def)

lemma pam_upd_invar: \<open>pam_invar (pam_upd k v bss)\<close> for v
proof -
  let ?ib = \<open>pam_bucket_of (length bss) k\<close>
  let ?b' = \<open>AList.update k v (bss ! ?ib)\<close>
  have D3: \<open>distinct (map fst (concat (take ?ib bss)) @ map fst (bss ! ?ib)
    @ map fst (concat (drop (Suc ?ib) bss)))\<close>
    using D by (metis concat_orig map_append)
  have DIST: \<open>distinct (map fst (concat (bss[?ib := ?b'])))\<close>
    using D3 take_nomem drop_nomem
    by (auto simp: concat_upd fst_set_alist_update AList.distinct_update)
  have BUCK: \<open>pam_bucket_of (length bss) k' = j\<close>
    if J: \<open>j < length bss\<close> and E: \<open>(k', v') \<in> set (bss[?ib := ?b'] ! j)\<close> for j k' v'
  proof (cases \<open>j = ?ib\<close>)
    case False
    with E J have \<open>(k', v') \<in> set (bss ! j)\<close> by simp
    with B J show ?thesis by simp
  next
    case True
    with E J IB have \<open>(k', v') \<in> set ?b'\<close> by simp
    with set_alist_update_subset have \<open>(k', v') \<in> insert (k, v) (set (bss ! ?ib))\<close>
      by fastforce
    with B[of ?ib] IB True show ?thesis by auto
  qed
  have NE': \<open>bss[?ib := ?b'] \<noteq> []\<close>
    by (metis NE length_0_conv length_list_update)
  show ?thesis
    using NE' DIST BUCK
    unfolding pam_upd_def Let_def pam_invar_def
    by (metis (mono_tags, lifting) case_prodI2 length_list_update)
qed

lemma pam_upd_abs: \<open>pam_map_of (pam_upd k v bss) = (pam_map_of bss)(k \<mapsto> v)\<close> for v
  unfolding pam_map_of_def comp_def pam_upd_def Let_def
  apply (subst concat_upd)
  apply (subst concat_orig)
  apply (rule ext)
  subgoal for k'
    by (cases \<open>k' = k\<close>)
      (auto simp: map_of_append map_add_def AList.update_conv' take_None drop_None
        split: option.splits)
  done

lemma pam_del_invar: \<open>pam_invar (pam_del k bss)\<close>
proof -
  let ?ib = \<open>pam_bucket_of (length bss) k\<close>
  let ?b' = \<open>AList.delete k (bss ! ?ib)\<close>
  have D3: \<open>distinct (map fst (concat (take ?ib bss)) @ map fst (bss ! ?ib)
    @ map fst (concat (drop (Suc ?ib) bss)))\<close>
    using D by (metis concat_orig map_append)
  have distA: \<open>distinct (map fst (concat (take ?ib bss)))\<close>
    and distB: \<open>distinct (map fst (bss ! ?ib))\<close>
    and distC: \<open>distinct (map fst (concat (drop (Suc ?ib) bss)))\<close>
    and AB: \<open>set (map fst (concat (take ?ib bss))) \<inter> set (map fst (bss ! ?ib)) = {}\<close>
    and AC: \<open>set (map fst (concat (take ?ib bss)))
      \<inter> set (map fst (concat (drop (Suc ?ib) bss))) = {}\<close>
    and BC: \<open>set (map fst (bss ! ?ib))
      \<inter> set (map fst (concat (drop (Suc ?ib) bss))) = {}\<close>
    using D3 distinct_append apply blast
    using D3 distinct_append apply blast
    apply (meson D3 distinct_append)
    apply (metis D3 append.assoc distinct_append)
    apply (metis D3 disjoint_iff distinct_append drop_append_miracle in_set_dropD)
    by (meson D3 distinct_append)
  have b'_keys: \<open>set (map fst ?b') = set (map fst (bss ! ?ib)) - {k}\<close>
    by (simp add: AList.delete_keys)
  have distB': \<open>distinct (map fst ?b')\<close>
    using AList.distinct_delete[OF distB] .
  have disjAB': \<open>set (map fst (concat (take ?ib bss))) \<inter> set (map fst ?b') = {}\<close>
    using AB b'_keys by auto
  have disjB'C: \<open>set (map fst ?b') \<inter> set (map fst (concat (drop (Suc ?ib) bss))) = {}\<close>
    using BC b'_keys by auto
  have DIST: \<open>distinct (map fst (concat (bss[?ib := ?b'])))\<close>
    unfolding concat_upd map_append
    using distA distC distB' AC disjAB' disjB'C
    by (simp add: distinct_append Int_Un_distrib Int_Un_distrib2)
  have BUCK: \<open>pam_bucket_of (length bss) k' = j\<close>
    if J: \<open>j < length bss\<close> and E: \<open>(k', v') \<in> set (bss[?ib := ?b'] ! j)\<close> for j k' v'
  proof (cases \<open>j = ?ib\<close>)
    case False
    with E J have \<open>(k', v') \<in> set (bss ! j)\<close> by simp
    with B J show ?thesis by simp
  next
    case True
    with E J IB have \<open>(k', v') \<in> set ?b'\<close> by simp
    with set_alist_delete_subset have \<open>(k', v') \<in> set (bss ! ?ib)\<close>
      by (metis subset_eq)
    with B[of ?ib] IB True show ?thesis by auto
  qed
  have NE': \<open>bss[?ib := ?b'] \<noteq> []\<close>
    by (metis NE length_0_conv length_list_update)
  show ?thesis
    using NE' DIST BUCK
    unfolding pam_del_def Let_def pam_invar_def
    by (metis (mono_tags, lifting) case_prodI2 length_list_update)
qed

lemma pam_del_abs: \<open>pam_map_of (pam_del k bss) = (pam_map_of bss)(k := None)\<close>
  unfolding pam_map_of_def comp_def pam_del_def Let_def
  apply (subst concat_upd)
  apply (subst concat_orig)
  apply (rule ext)
  subgoal for k'
    by (cases \<open>k' = k\<close>)
      (auto simp: map_of_append map_add_def AList.delete_conv' take_None drop_None
        split: option.splits)
  done

end

lemma pam_invar_replicate: \<open>0 < n \<Longrightarrow> pam_invar (replicate n [])\<close>
  by (auto simp: pam_invar_def)

lemma pam_map_of_replicate[simp]: \<open>pam_map_of (replicate n []) = Map.empty\<close>
  by (induction n) (auto simp: pam_map_of_def)


subsection \<open>The map interface\<close>

text \<open>One \<open>hr_comp\<close> step to @{typ \<open>nat \<rightharpoonup> 'v\<close>}; the further composition with
  \<open>map_fmap_rel\<close> to \<open>(nat, 'v) fmap\<close> lives in \<^file>\<open>PAC_Map_Rel.thy\<close>, where the
  abbreviation \<open>hm_fmap_assn K V \<equiv> hr_comp (hm_assn K V) map_fmap_rel\<close> should become

    \<open>pam_fmap_assn V \<equiv> hr_comp (pam_map_assn V) map_fmap_rel\<close>

  \<comment> \<open>the key-assertion parameter disappears: keys are fixed to 64-bit words here, and
  the Native_Word-based \<open>uint64_nat_assn\<close> at the call sites (e.g. \<open>polys_assn\<close> in
  \<^file>\<open>PAC_Checker_Relation.thy\<close>) must be replaced by \<open>unat_assn' TYPE(64)\<close> anyway,
  since \<open>uint64\<close> is not an \<open>llvm_rep\<close> type.\<close>\<close>

definition pam_map_assn :: \<open>('v, 'vi::llvm_rep) dr_assn \<Rightarrow> (nat \<rightharpoonup> 'v) \<Rightarrow> 'vi pam_impl \<Rightarrow> assn\<close>
  where \<open>pam_map_assn V \<equiv> hr_comp (\<upharpoonleft>(pam_assn V)) pam_rel\<close>

text \<open>Interface type for hfref arguments: the IICF map operations are registered
  against \<open>('k,'v) i_map\<close>, while \<open>intf_of_assn_fallback\<close> would assign the plain
  \<open>nat \<rightharpoonup> 'v\<close> type (see the analogous \<open>f_map\<close> note in \<open>Polys_Assn.thy\<close>).\<close>

lemma pam_map_assn_intf[intf_of_assn]:
  \<open>intf_of_assn (pam_map_assn V) TYPE((nat, 'v) i_map)\<close>
  by simp

text \<open>Default bin count, as for the string hash set. TODO: \<open>remap_polys\<close> knows
  \<open>upper_bound_on_dom\<close> of the input map; a size-hinted constructor would fit there.\<close>

text \<open>Bin count as an \<^emph>\<open>opaque\<close> definition. It must never be unfolded to the numeral
  \<open>16384\<close> inside the proofs below: the postconditions carry \<open>replicate pam_nbins []\<close>,
  and expanding \<open>pam_nbins\<close> would let \<open>replicate_numeral\<close> unfold that into a
  16384-element cons chain \<emdash> which is what makes \<open>vcg\<close>/\<open>simp\<close> crawl. All arithmetic
  facts about the count are proven once here (unfolding \<open>pam_nbins_def\<close> locally); the
  constant stays folded everywhere else.\<close>

definition pam_nbins :: nat where \<open>pam_nbins = 16384\<close>

lemma pam_nbins_pos: \<open>0 < pam_nbins\<close>
  by (simp add: pam_nbins_def)

definition pam_empty_impl :: \<open>unit \<Rightarrow> 'vi::llvm_rep pam_impl llM\<close> where [llvm_inline]:
  \<open>pam_empty_impl \<equiv> \<lambda>_. pam_new_impl (signed_nat 16384)\<close>
  \<comment> \<open>\<open>[llvm_inline]\<close>, NOT \<open>[llvm_code]\<close>: the \<open>unit\<close> argument becomes a literal \<open>()\<close> on
  the code equation's LHS (\<open>unit_meta_eq\<close>), which \<open>llc_parse_eqn\<close> rejects
  (\<open>arguments must be vars\<close>). Inlining dissolves the wrapper at all call sites.\<close>

text \<open>The size argument is a \<open>vcg_const\<close> literal (\<open>signed_nat 16384\<close>) passed \<^emph>\<open>directly\<close>
  to \<open>pam_new_impl\<close>, so vcg never derives a \<open>\<upharpoonleft>snat.assn n ni\<close> for it from the empty
  state \<open>\<box>\<close>. Establish that pure fact once, then strengthen \<open>pam_new_impl_rule\<close>'s
  precondition down to \<open>\<box>\<close>.\<close>

lemma snat_assn_pam_nbins:
  \<open>\<box> \<turnstile> \<upharpoonleft>snat.assn pam_nbins (signed_nat (16384::64 word))\<close>
proof -
  have \<open>pam_nbins < max_snat LENGTH(64)\<close>
    by (simp add: pam_nbins_def max_snat_def)
  then have \<open>snat_invar (signed_nat (16384::64 word))
      \<and> pam_nbins = snat (signed_nat (16384::64 word))\<close>
    by (simp add: signed_nat_def snat_invar_numeral pam_nbins_def max_snat_def)
  then show ?thesis
    by (simp add: snat.assn_def entails_def pred_lift_extract_simps sep_algebra_simps)
qed

lemma pam_empty_impl_aux_rule:
  \<open>llvm_htriple \<box> (pam_empty_impl u) (\<lambda>r. \<upharpoonleft>(pam_assn V) (replicate pam_nbins []) r)\<close>
  unfolding pam_empty_impl_def
  by (rule htriple_ent_pre[OF snat_assn_pam_nbins
        pam_new_impl_rule[where n = pam_nbins and ni = \<open>signed_nat 16384\<close>]])

lemma pam_empty_impl_hfref:
  \<open>(uncurry0 (pam_empty_impl ()), uncurry0 (RETURN (replicate pam_nbins [])))
     \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a \<upharpoonleft>(pam_assn V)\<close>
  apply sepref_to_hoare
  supply [vcg_rules] = pam_empty_impl_aux_rule
  by vcg

lemma pam_empty_rel:
  \<open>(uncurry0 (RETURN (replicate pam_nbins [])), uncurry0 (RETURN op_map_empty))
     \<in> unit_rel \<rightarrow>\<^sub>f \<langle>pam_rel\<rangle>nres_rel\<close>
  apply (rule fref_param0I)
  by (auto simp: pam_rel_def br_def pam_invar_replicate pam_map_of_replicate
      op_map_empty_def pam_nbins_pos intro!: nres_relI)

lemmas pam_empty_hnr[sepref_fr_rules] =
  pam_empty_impl_hfref[FCOMP pam_empty_rel, folded pam_map_assn_def]

text \<open>Update\<close>
lemma pam_update_impl_raw_hfref:
  assumes VFREE: \<open>MK_FREE (\<upharpoonleft>(mk_assn V)) vfree\<close>
  shows \<open>(uncurry2 (pam_update_impl vfree), uncurry2 (RETURN ooo pam_upd))
  \<in> [\<lambda>((k,v),bss). bss \<noteq> []]\<^sub>a (unat_assn' TYPE(64))\<^sup>k *\<^sub>a V\<^sup>d *\<^sub>a (\<upharpoonleft>(pam_assn (mk_assn V)))\<^sup>d \<rightarrow> \<upharpoonleft>(pam_assn (mk_assn V))\<close>
  unfolding unat_rel_def unat.assn_is_rel[symmetric]
  supply [vcg_rules] = pam_update_impl_rule[OF VFREE]
  apply sepref_to_hoare
  apply vcg
  subgoal by (rule VFREE)
  subgoal
    unfolding vcg_tag_defs    
    apply (erule STATE_monoI)
    by (simp add: extract_pure_assn[OF unat.assn_pure] sep_algebra_simps)
  done

lemma pam_update_rel:
  \<open>(uncurry2 (RETURN ooo pam_upd), uncurry2 (RETURN ooo op_map_update))
  \<in> (nat_rel \<times>\<^sub>r Id) \<times>\<^sub>r pam_rel \<rightarrow>\<^sub>f \<langle>pam_rel\<rangle>nres_rel\<close>
  by (auto simp: nres_rel_def fref_def in_br_conv pam_rel_def pam_upd_abs pam_upd_invar)

lemma pam_rel_nonempty[fcomp_prenorm_simps]:
  \<open>(bss, m) \<in> pam_rel \<Longrightarrow> bss \<noteq> []\<close>
  by (auto simp: pam_rel_def in_br_conv pam_invar_def)

lemmas pam_update_hnr[sepref_fr_rules] =
  pam_update_impl_raw_hfref[FCOMP pam_update_rel, folded pam_map_assn_def]

text \<open>Deletion. Unlike \<open>op_map_empty\<close> (empty precondition, hence FCOMP), the map
  argument is present in the precondition here, so \<open>hr_comp_def\<close> is already in \<open>EXS\<close>
  form and unfolds on both sides \<^emph>\<open>directly\<close> under \<open>sepref_to_hoare\<close> (cf.\
  \<open>shs_insert_hnr\<close> in \<^file>\<open>String_Hash_Map.thy\<close>). The bucket list extracted from the
  precondition witnesses the postcondition's \<open>hr_comp\<close>, and \<open>pam_invar bss\<close> discharges
  the \<open>bss \<noteq> []\<close> side condition of @{thm pam_delete_impl_rule}.

  The key sits at \<open>unat_assn' TYPE(64) = pure unat_rel\<close> in the interface but as the
  dr_assn \<open>\<upharpoonleft>unat.assn\<close> in the raw triple; @{thm unat.assn_is_rel} (folded with
  @{thm unat_rel_def}) bridges the two.\<close>

lemma pam_invar_nonempty[simp]: \<open>pam_invar bss \<Longrightarrow> bss \<noteq> []\<close>
  by (simp add: pam_invar_def)

lemma pam_delete_hnr[sepref_fr_rules]:
  assumes VFREE: \<open>MK_FREE (\<upharpoonleft>V) vfree\<close>
  shows \<open>(uncurry (pam_delete_impl vfree), uncurry (RETURN oo op_map_delete))
    \<in> (unat_assn' TYPE(64))\<^sup>k *\<^sub>a (pam_map_assn V)\<^sup>d \<rightarrow>\<^sub>a pam_map_assn V\<close>
  unfolding pam_map_assn_def unat_rel_def unat.assn_is_rel[symmetric]
  apply sepref_to_hoare
  supply [vcg_rules] = pam_delete_impl_rule[OF VFREE]
  supply [simp] = hr_comp_def pam_rel_def in_br_conv pam_del_invar pam_del_abs
    op_map_delete_def sep_conj_exists
  apply vcg
   apply (rule VFREE)
  subgoal for aa ai asf x a b sa
    unfolding vcg_tag_defs
    apply (erule STATE_monoI)
    apply (rule entails_exI[where x = \<open>(pam_map_of x)(aa := None)\<close>])
    apply (rule entails_exI[where x = \<open>pam_del aa x\<close>])
    by (simp add: extract_pure_assn[OF unat.assn_pure] pam_del_abs pam_del_invar
        sep_algebra_simps pred_lift_extract_simps entails_refl)
  done

text \<open>Membership. Same skeleton as deletion, but with both arguments kept: the
  bucket list extracted from the precondition witnesses the (unchanged)
  postcondition, and \<open>pam_contains_correct\<close> converts the bucket-local answer of
  @{thm pam_contains_impl_rule} into \<open>k \<in> dom (pam_map_of bss)\<close> under the
  invariant. The boolean result goes through @{thm bool.assn_is_rel} (folded
  with @{thm bool1_rel_def}) \<^emph>\<open>before\<close> \<open>sepref_to_hoare\<close>, exactly like the key
  through @{thm unat.assn_is_rel} (cf.\ \<open>hs_member_hnr\<close> in
  \<^file>\<open>IICF_Hash_Set.thy\<close>).\<close>

lemma pam_contains_hnr[sepref_fr_rules]:
  \<open>(uncurry pam_contains_impl, uncurry (RETURN oo op_map_contains_key))
    \<in> (unat_assn' TYPE(64))\<^sup>k *\<^sub>a (pam_map_assn V)\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding pam_map_assn_def unat_rel_def unat.assn_is_rel[symmetric]
    bool1_rel_def bool.assn_is_rel[symmetric]
  apply sepref_to_hoare
  supply [simp] = hr_comp_def pam_rel_def in_br_conv pam_contains_correct
    op_map_contains_key_def sep_conj_exists
  by vcg

text \<open>Lookup\<close>
context
begin
lemma pam_the_lookup_reassemble:
  assumes NF: \<open>nofail (ASSERT (\<exists>y. pam_map_of x k = Some y) \<bind>
                 (\<lambda>_. RETURN (the (pam_map_of x k))))\<close>
    and K: \<open>\<flat>\<^sub>punat.assn k ki\<close>
    and I: \<open>pam_invar x\<close>
  shows \<open>ENTAILS
    (\<upharpoonleft>(pam_assn V) x (n, a) \<and>*
     (if \<exists>y. pam_map_of x k = Some y
      then \<upharpoonleft>V (the (map_of (x ! pam_bucket_of (length x) k) k)) vi else \<box>))
    (\<lambda>s. \<exists>xa xb. (\<upharpoonleft>unat.assn k ki \<and>* \<upharpoonleft>(pam_assn V) xa (n, a) \<and>*
       \<up>(pam_map_of x = pam_map_of xa \<and> pam_invar xa) \<and>* \<up>True \<and>*
       \<upharpoonleft>V xb vi \<and>*
       \<up>(RETURN xb \<le> ASSERT (\<exists>y. pam_map_of x k = Some y) \<bind>
           (\<lambda>_. RETURN (the (pam_map_of x k))))) s)\<close>
proof -
  from NF have G[simp]: \<open>(\<exists>y. pam_map_of x k = Some y) = True\<close>
    by (auto simp: refine_pw_simps)
  note [simp] = pam_map_of_bucket[symmetric] K
  show ?thesis
    unfolding vcg_tag_defs ENTAILS_def
    apply (rule entails_exI[where x = x])
    apply (rule entails_exI[where x = \<open>the (pam_map_of x k)\<close>])
    using I
    by (simp add: extract_pure_assn[OF unat.assn_pure] refine_pw_simps pw_le_iff
        sep_algebra_simps pred_lift_extract_simps entails_refl)
qed

lemma pam_the_lookup_hnr[sepref_fr_rules]:
  assumes VCOPY: \<open>\<And>v vi. llvm_htriple (\<upharpoonleft>V v vi) (vcopy vi) (\<lambda>r. \<upharpoonleft>V v vi ** \<upharpoonleft>V v r)\<close>
  shows \<open>(uncurry (pam_the_lookup_impl vcopy), uncurry mop_map_the_lookup)
    \<in> (unat_assn' TYPE(64))\<^sup>k *\<^sub>a (pam_map_assn V)\<^sup>k \<rightarrow>\<^sub>a \<upharpoonleft>V\<close>
  unfolding pam_map_assn_def unat_rel_def unat.assn_is_rel[symmetric] 
  unfolding pam_the_lookup_impl_def
  apply sepref_to_hoare
  supply [vcg_rules] = pam_lookup_impl_rule[OF VCOPY] VCOPY
  supply [simp] = hr_comp_def pam_rel_def in_br_conv sep_conj_exists 
    pam_map_of_bucket[symmetric]
  apply vcg
  subgoal by (rule pam_the_lookup_reassemble; assumption)
  done
end

text \<open>Deallocation\<close>
  
lemma pam_assn_free:
  assumes VFREE: \<open>MK_FREE (\<upharpoonleft>V) vfree\<close>
  shows \<open>MK_FREE (\<upharpoonleft>(pam_assn V)) (pam_free_impl vfree)\<close>
  by (rule MK_FREEI) (rule pam_free_impl_rule[OF VFREE])

lemma pam_map_assn_free[sepref_frame_free_rules]:
  assumes \<open>MK_FREE (\<upharpoonleft>V) vfree\<close>
  shows \<open>MK_FREE (pam_map_assn V) (pam_free_impl vfree)\<close>
  unfolding pam_map_assn_def
  by (intro MK_FREE_hrcompI pam_assn_free assms)

text \<open>
  Open points:
  \<^item> \<^bold>\<open>fmupd argument mode\<close>: call sites currently use \<open>poly_assn\<^sup>k\<close> for the inserted
    value (pure values in Imperative HOL); with owning values this becomes \<open>V\<^sup>d\<close>,
    and the abstract code must stop using the polynomial after insertion (it
    already does, structurally) \<comment> \<open>otherwise a copy is needed at the call site.\<close>
  \<^item> \<^bold>\<open>Code export\<close>: \<open>pam_bucket_lookup_impl\<close>/\<open>pam_bucket_update_impl\<close>/
    \<open>pam_bucket_delete_impl\<close>/\<open>pam_bucket_free_impl\<close> (and the \<open>pam_*_impl\<close> wrappers)
    are higher-order in \<open>vfree\<close>/\<open>vcopy\<close>; the instantiation with \<open>poly_assn\<close>'s free and
    copy functions must be specialized into first-order \<open>[llvm_code]\<close> definitions
    before export.
\<close>


subsection \<open>Tests\<close>

experiment
begin

text \<open>End-to-end composition tests of the (fully proven) bucket layer with a concrete
  heap-owning value type: open lists of 64-bit words (\<open>os_list_assn\<close>). The value
  parameters instantiate to \<open>vfree = os_delete\<close> (@{thm raw_os_assn_free}) and
  \<open>vcopy = ol_copy Mreturn\<close> (@{thm os_copy_rule}). The initial empty bucket enters
  through the precondition (\<open>\<upharpoonleft>(pam_bucket_assn V) [] b\<close> forces \<open>b = null\<close>); the
  map-level operations are exercised once their wrapper triples are discharged.\<close>

abbreviation w64l_assn :: \<open>(64 word list, 64 word os_list) dr_assn\<close> where
  \<open>w64l_assn \<equiv> os_list_assn\<close>

lemma w64l_copy_rule:
  \<open>llvm_htriple
    (\<upharpoonleft>os_list_assn v vi)
    (ol_copy Mreturn vi)
    (\<lambda>r. \<upharpoonleft>os_list_assn v vi ** \<upharpoonleft>os_list_assn v r)\<close>
  using os_copy_rule[where A = id_assn, unfolded os_assn_def] by simp

lemmas test_rules[vcg_rules] =
  pam_bucket_update_impl_rule[OF raw_os_assn_free]
  pam_bucket_delete_impl_rule[OF raw_os_assn_free]
  pam_bucket_lookup_impl_rule[OF w64l_copy_rule]
  MK_FREED[OF pam_bucket_assn_free[OF raw_os_assn_free]]

text \<open>Insert \<rightarrow> member \<rightarrow> deep-free: the inserted key is found.\<close>

lemma insert_member_test:
  \<open>llvm_htriple
    (\<upharpoonleft>(pam_bucket_assn w64l_assn) [] b ** \<upharpoonleft>unat.assn k ki ** \<upharpoonleft>os_list_assn v vi)
    (doM {
      b \<leftarrow> pam_bucket_update_impl os_delete ki vi b;
      r \<leftarrow> pam_bucket_contains_impl ki b;
      pam_bucket_free_impl os_delete b;
      Mreturn r })
    (\<lambda>r. \<upharpoonleft>bool.assn True r)\<close>
  by vcg

text \<open>Insert \<rightarrow> delete \<rightarrow> member: the key is gone (and its value was freed by the
  delete walk \<comment> \<open>nothing leaks, as the \<open>\<box>\<close>-postcondition of the final free shows.\<close>\<close>

lemma insert_delete_member_test:
  \<open>llvm_htriple
    (\<upharpoonleft>(pam_bucket_assn w64l_assn) [] b ** \<upharpoonleft>unat.assn k ki ** \<upharpoonleft>os_list_assn v vi)
    (doM {
      b \<leftarrow> pam_bucket_update_impl os_delete ki vi b;
      b \<leftarrow> pam_bucket_delete_impl os_delete ki b;
      r \<leftarrow> pam_bucket_contains_impl ki b;
      pam_bucket_free_impl os_delete b;
      Mreturn r })
    (\<lambda>r. \<upharpoonleft>bool.assn False r)\<close>
  by vcg

text \<open>Two distinct keys coexist in one bucket (hash collisions are handled by the
  walk, not the hashing).\<close>

lemma two_keys_test:
  \<open>llvm_htriple
    (\<upharpoonleft>(pam_bucket_assn w64l_assn) [] b ** \<up>(k1 \<noteq> k2)
       ** \<upharpoonleft>unat.assn k1 k1i ** \<upharpoonleft>unat.assn k2 k2i
       ** \<upharpoonleft>os_list_assn v1 v1i ** \<upharpoonleft>os_list_assn v2 v2i)
    (doM {
      b \<leftarrow> pam_bucket_update_impl os_delete k1i v1i b;
      b \<leftarrow> pam_bucket_update_impl os_delete k2i v2i b;
      r1 \<leftarrow> pam_bucket_contains_impl k1i b;
      r2 \<leftarrow> pam_bucket_contains_impl k2i b;
      pam_bucket_free_impl os_delete b;
      Mreturn (r1, r2) })
    (\<lambda>(r1, r2). \<upharpoonleft>bool.assn True r1 ** \<upharpoonleft>bool.assn True r2)\<close>
  by vcg

text \<open>Replace \<rightarrow> lookup: the second insert frees the first value in place; the lookup
  copy holds the \<^emph>\<open>new\<close> value and \<^emph>\<open>outlives\<close> the freed map \<comment> \<open>the ownership-transfer
  point of design option 1.\<close>\<close>

lemma replace_lookup_test:
  \<open>llvm_htriple
    (\<upharpoonleft>(pam_bucket_assn w64l_assn) [] b ** \<upharpoonleft>unat.assn k ki
       ** \<upharpoonleft>os_list_assn v1 v1i ** \<upharpoonleft>os_list_assn v2 v2i)
    (doM {
      b \<leftarrow> pam_bucket_update_impl os_delete ki v1i b;
      b \<leftarrow> pam_bucket_update_impl os_delete ki v2i b;
      (f, wi) \<leftarrow> pam_bucket_lookup_impl (ol_copy Mreturn) ki b;
      pam_bucket_free_impl os_delete b;
      Mreturn (f, wi) })
    (\<lambda>(f, wi). \<upharpoonleft>bool.assn True f ** \<upharpoonleft>os_list_assn v2 wi)\<close>
  by vcg

end

end
