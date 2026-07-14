(*
  File:         PAC_Checker_Synthesis.thy
  Author:       Mathias Fleury, Daniela Kaufmann, JKU
  Maintainer:   Mathias Fleury, JKU
*)
theory LPAC_Checker_Synthesis
  imports
    LPAC_Checker
    LPAC_Version
    LPAC_Step_Assn
    PAC_Checker_LLVM.More_Loops
    PAC_Checker_LLVM.PAC_Checker_Relation
    PAC_Checker_LLVM.PAC_Checker_Synthesis
begin
hide_fact (open) PAC_Checker.PAC_checker_l_def
hide_const (open) PAC_Checker.PAC_checker_l

section \<open>Code Synthesis of the Complete Checker\<close>

(* For now we ignore printing - we will have to figure this out at some point though
definition check_linear_combi_l_pre_err_impl 
  :: \<open>nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> string\<close> where
  \<open>check_linear_combi_l_pre_err_impl i adom emptyl ivars =
  ''Precondition for '%' failed '' @ show i @jjj
  ''(already in domain: '' @ show adom @
  ''; empty CL'' @ show emptyl @re
  ''; new vars: '' @ show ivars @ '')''\<close>
*)

definition \<open>print4 \<equiv> \<lambda>_ _ _ _. RETURN 0\<close>

(* How to do printing: *)
sepref_def print4_impl is \<open>uncurry3 print4\<close>
  :: \<open>(unat_assn' TYPE(64))\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a (unat_assn' TYPE(1))\<close>
  unfolding print4_def
  apply (annot_unat_const "TYPE(1)")
  by sepref

lemma print4_refine: \<open>(uncurry3 print4, uncurry3 check_linear_combi_l_pre_err)
  \<in> (((Id \<times>\<^sub>r Id) \<times>\<^sub>r Id) \<times>\<^sub>r Id) \<rightarrow>\<^sub>f \<langle>{(a, b). True}\<rangle>nres_rel\<close>
  unfolding print4_def check_linear_combi_l_pre_err_def 
  apply (intro frefI nres_relI)
  apply auto
  by (simp add: RETURN_RES_refine)

lemmas [sepref_fr_rules] = print4_impl.refine[FCOMP print4_refine]
sepref_register check_linear_combi_l_pre_err
sepref_def test is \<open>uncurry3 check_linear_combi_l_pre_err\<close>
  :: \<open>[\<lambda>bb. True]⇩a (unat_assn' TYPE(64))⇧k *⇩a bool1_assn⇧k *⇩a bool1_assn⇧k *⇩a
        bool1_assn⇧k \<rightarrow> pure (unat_rel' TYPE(1) O {(b::(nat \<times> string)). True})\<close>
  by sepref

export_llvm test


(* lemma [sepref_fr_rules]:
 *   \<open>(print4, uncurry3 check_linear_combi_l_pre_err)
 *   \<in> (unat_assn' TYPE(64))\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
 *   unfolding check_linear_combi_l_pre_err_def
 *   apply sepref_to_hoare
 *   by (vcg; auto simp: status_pure_reassembly) *)

(* again - we ignore printing for now
definition check_linear_combi_l_dom_err_impl :: \<open> _ \<Rightarrow> uint64 \<Rightarrow> string\<close> where
  \<open>check_linear_combi_l_dom_err_impl xs i =
  ''Invalid polynomial '' @ show (nat_of_uint64 i)\<close>
*)

lemma [sepref_fr_rules]:
  \<open>(uncurry (\<lambda>_ _. Mreturn 0), uncurry (check_linear_combi_l_dom_err)) 
  \<in> poly_assn\<^sup>k *\<^sub>a (unat_assn' TYPE(64))\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
  unfolding check_linear_combi_l_dom_err_def
  apply sepref_to_hoare
  by (vcg; auto simp: status_pure_reassembly)

(* same thing here
definition check_linear_combi_l_mult_err_impl :: \<open> _ \<Rightarrow> _ \<Rightarrow> string\<close> where
  \<open>check_linear_combi_l_mult_err_impl xs ys =
  ''Invalid calculation, found'' @ show xs @ '' instead of '' @ show ys\<close>
*)

lemma [sepref_fr_rules]:
  \<open>(uncurry (\<lambda>_ _. Mreturn 0), uncurry check_linear_combi_l_mult_err) 
  \<in> poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
  unfolding check_linear_combi_l_mult_err_def
  unfolding check_linear_combi_l_dom_err_def
  apply sepref_to_hoare
  by (vcg; auto simp: status_pure_reassembly)

(* Elements of a linear combination *)
abbreviation \<open>lincomb_assn \<equiv> ol_assn (poly_assn \<times>\<^sub>a (unat_assn' TYPE(64)))\<close>
(* For now, we have to manually build llvm code to free the list.
 * TODO: Check if we could use a locale in Owning list to avoid this *)
definition lincomb_tup_free
  :: "(8 word node ptr node ptr \<times> (64 word \<times> 64 word \<times> 64 word ptr) \<times> 1 word) node ptr \<times> 64 word \<Rightarrow> unit llM" where [llvm_code]:
  \<open>lincomb_tup_free \<equiv> \<lambda>(p, n). doM { poly_free p; Mreturn () }\<close>
lemma lincomb_tup_assn_free[sepref_frame_free_rules]: \<open>MK_FREE (poly_assn \<times>\<^sub>a (unat_assn' TYPE(64))) lincomb_tup_free\<close>
  unfolding lincomb_tup_free_def
  using free_thms(2,3) poly_assn_free by blast
  
definition \<open>lincomb_free \<equiv> ol_delete lincomb_tup_free\<close>
lemma lincomb_free_simps[llvm_code]:
  \<open>lincomb_free l = (if l = null then Mreturn () else doM {
    n \<leftarrow> ll_load l; lincomb_tup_free (node.val n); ll_free l; lincomb_free (node.next n) })\<close>
  unfolding lincomb_free_def by (rule ol_delete.simps)

lemmas [llvm_pre_simp] = lincomb_free_def[symmetric]
lemma lincomb_assn_free[sepref_frame_free_rules]: \<open>MK_FREE lincomb_assn lincomb_free\<close>
  unfolding lincomb_free_def by (rule ol_assn_free[OF lincomb_tup_assn_free])

definition linear_combi_l2 where
  \<open>linear_combi_l2 i A \<V> xs = do {
    ASSERT(linear_combi_l_pre i A \<V> xs);
    WHILE\<^sub>T
      (\<lambda>(p, xs, err). xs \<noteq> [] \<and> \<not>is_cfailed err)
      (\<lambda>(p, xs, _). do {
         ASSERT(xs \<noteq> []);
         ASSERT(vars_llist p \<subseteq> \<V>);
         let ((q\<^sub>0 :: llist_polynomial, i), xs') = op_list_pop_front xs;
         if (i \<notin># dom_m A \<or> \<not>(vars_llist q\<^sub>0 \<subseteq> \<V>))
         then do {
           err \<leftarrow> check_linear_combi_l_dom_err q\<^sub>0 i;
           RETURN (p, (q\<^sub>0, i) # xs', error_msg i err)
         } else do {
           ASSERT(fmlookup A i \<noteq> None);
           let r = the (fmlookup A i);
           ASSERT(vars_llist r \<subseteq> \<V>);
           if q\<^sub>0 = [([], 1)]
           then do {
             pq \<leftarrow> add_poly_l (p, r);
             RETURN (pq, xs', CSUCCESS)
           }
           else do {
             q \<leftarrow> full_normalize_poly (q\<^sub>0);
             ASSERT(vars_llist q \<subseteq> \<V>);
             pq \<leftarrow> mult_poly_full q r;
             ASSERT(vars_llist pq \<subseteq> \<V>);
             pq \<leftarrow> add_poly_l (p, pq);
             RETURN (pq, xs', CSUCCESS)
          }
         }
      })
     ([], xs, CSUCCESS)
  }\<close>

lemma linear_combi_l2_linear_combi_l:
  \<open>linear_combi_l2 i A \<V> xs = linear_combi_l i A \<V> xs\<close>
proof -
  have H: \<open>(q\<^sub>0, ia) # tl ys = ys\<close> if \<open>hd ys = (q\<^sub>0, ia)\<close> \<open>ys \<noteq> []\<close>
    for q\<^sub>0 ia and ys :: \<open>(llist_polynomial \<times> nat) list\<close>
    using that by (cases ys) auto
  show ?thesis
    unfolding linear_combi_l2_def linear_combi_l_def op_list_pop_front_def
    apply (rule bind_cong[OF refl])
    apply (rule arg_cong2[where f = \<open>\<lambda>c b. WHILE\<^sub>T c b ([], xs, CSUCCESS)\<close>])
    subgoal by (rule refl)
    apply (intro ext)
    apply (clarsimp split!: prod.splits list.splits simp: H)
    apply (auto simp: H pw_eq_iff refine_pw_simps)
    done
qed

fun vars_of_monom_in where
  \<open>vars_of_monom_in [] _ = True\<close> |
  \<open>vars_of_monom_in (x # xs) \<V> \<longleftrightarrow> x \<in> \<V> \<and> vars_of_monom_in xs \<V>\<close>

fun vars_of_poly_in where
  \<open>vars_of_poly_in [] _ = True\<close> |
  \<open>vars_of_poly_in ((x, _) # xs) \<V> \<longleftrightarrow> vars_of_monom_in x \<V> \<and> vars_of_poly_in xs \<V>\<close>

lemma vars_of_monom_in_alt_def:
  \<open>vars_of_monom_in xs \<V> \<longleftrightarrow> set xs \<subseteq> \<V>\<close>
  by (induction xs)
   auto

lemma vars_llist_alt_def:
  \<open>vars_llist xs \<subseteq> \<V> \<longleftrightarrow> vars_of_poly_in xs \<V>\<close>
  by (induction xs)
   (auto simp: vars_llist_def vars_of_monom_in_alt_def)

partial_function (M) vars_of_monom_in_impl ::
  \<open>8 word os_list hs_impl \<Rightarrow> monom_conc \<Rightarrow> 1 word llM\<close> where
  \<open>vars_of_monom_in_impl vi p = (if p = null then Mreturn 1
    else doM {
      n \<leftarrow> ll_load p;
      b \<leftarrow> vars_hs_member_impl (node.val n) vi;
      if to_bool b then vars_of_monom_in_impl vi (node.next n)
      else Mreturn 0
    })\<close>

lemmas [llvm_code] = vars_of_monom_in_impl.simps

lemma vars_of_monom_in_impl_rule[vcg_rules]:
  \<open>llvm_htriple
    (monom_assn xs p ** vars_hs_assn \<V> vi)
    (vars_of_monom_in_impl vi p)
    (\<lambda>r. monom_assn xs p ** vars_hs_assn \<V> vi
       ** \<upharpoonleft>bool.assn (vars_of_monom_in xs \<V>) r)\<close>
  unfolding ol_assn_conv
proof (induction xs arbitrary: p)
  case Nil
  show ?case
    supply [simp] = bool.assn_def
    apply (subst vars_of_monom_in_impl.simps)
    by vcg
next
  case (Cons e es)
  note [vcg_rules] = Cons.IH vars_hs_member_rule
  show ?case
    supply [simp, named_ss fri_prepare_simps] = ol_seg_cons
    supply [simp] = bool.assn_def sep_conj_exists
    apply (subst vars_of_monom_in_impl.simps)
    apply (cases \<open>p = null\<close>; simp)
    by vcg
qed

partial_function (M) vars_of_poly_in_impl ::
  \<open>8 word os_list hs_impl \<Rightarrow> (monom_conc \<times> sbin_conc \<times> 1 word) os_list \<Rightarrow> 1 word llM\<close> where
  \<open>vars_of_poly_in_impl vi p = (if p = null then Mreturn 1
    else doM {
      n \<leftarrow> ll_load p;
      b \<leftarrow> vars_of_monom_in_impl vi (fst (node.val n));
      if to_bool b then vars_of_poly_in_impl vi (node.next n)
      else Mreturn 0
    })\<close>

lemmas [llvm_code] = vars_of_poly_in_impl.simps

lemma vars_of_poly_in_impl_rule[vcg_rules]:
  \<open>llvm_htriple
    (poly_assn xs p ** vars_hs_assn \<V> vi)
    (vars_of_poly_in_impl vi p)
    (\<lambda>r. poly_assn xs p ** vars_hs_assn \<V> vi
       ** \<upharpoonleft>bool.assn (vars_of_poly_in xs \<V>) r)\<close>
  unfolding ol_assn_conv
proof (induction xs arbitrary: p)
  case Nil
  show ?case
    supply [simp] = bool.assn_def
    apply (subst vars_of_poly_in_impl.simps)
    by vcg
next
  case (Cons e es)
  note [vcg_rules] = Cons.IH vars_of_monom_in_impl_rule[unfolded ol_assn_conv]
  show ?case
    supply [simp, named_ss fri_prepare_simps] = ol_seg_cons
    supply [simp] = bool.assn_def sep_conj_exists
    apply (subst vars_of_poly_in_impl.simps)
    apply (cases \<open>p = null\<close>; cases e; simp)
    by vcg
qed

sepref_register vars_of_poly_in

lemma vars_of_poly_in_hnr[sepref_fr_rules]:
  \<open>(uncurry (\<lambda>pi vi. vars_of_poly_in_impl vi pi), uncurry (RETURN oo vars_of_poly_in))
    \<in> poly_assn\<^sup>k *\<^sub>a vars_hs_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding bool1_rel_def bool.assn_is_rel[symmetric]
  apply sepref_to_hoare
  by vcg

(* Note that we have to destroy lincomb - Check in outer loop if 
   that could be tolerated by contiuing with tl, otherwise we need
   to copy the hd out of the list *)
sepref_definition linear_combi_l_impl
  is \<open>uncurry3 linear_combi_l\<close>
  :: \<open>(unat_assn' TYPE(64))\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a vars_hs_assn\<^sup>k *\<^sub>a lincomb_assn\<^sup>d
       \<rightarrow>\<^sub>a poly_assn \<times>\<^sub>a lincomb_assn \<times>\<^sub>a status_assn raw_string_assn\<close>
  unfolding linear_combi_l2_linear_combi_l[symmetric]
  unfolding linear_combi_l2_def
  unfolding check_linear_combi_l_def
  unfolding conv_to_is_Nil
  unfolding term_order_rel'_def[symmetric]
  unfolding term_order_rel'_alt_def
  unfolding fmlookup'_def[symmetric]
  unfolding fold_is_Nil_is_empty
  unfolding fold_ol_empty
  unfolding vars_llist_alt_def
  by sepref

definition has_failed :: \<open>bool nres\<close> where
  \<open>has_failed = RES UNIV\<close>

text \<open>The concrete side never fails spuriously: \<open>Mreturn 0\<close> refines the
  nondeterministic \<open>RES UNIV\<close> by always choosing \<open>False\<close>.\<close>

sepref_register has_failed
lemma has_failed_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0), uncurry0 has_failed) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding has_failed_def bool1_rel_def bool.assn_is_rel[symmetric]
  apply sepref_to_hoare
  by (vcg; auto simp: status_pure_reassembly bool.assn_def refine_pw_simps)

sepref_register check_linear_combi_l_pre_err

sepref_definition check_linear_combi_l_impl
  is \<open>uncurry5 check_linear_combi_l\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a vars_hs_assn\<^sup>k *\<^sub>a (unat_assn' TYPE(64))\<^sup>k *\<^sub>a
        lincomb_assn\<^sup>d *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a status_assn raw_string_assn\<close>
  supply [[goals_limit=1]]
  unfolding check_linear_combi_l_def
  unfolding linear_combi_l2_linear_combi_l[symmetric]
  unfolding linear_combi_l2_def
  unfolding conv_to_is_Nil
  unfolding term_order_rel'_def[symmetric]
  unfolding term_order_rel'_alt_def
  unfolding fmlookup'_def[symmetric]
  unfolding fold_is_Nil_is_empty
  unfolding fold_ol_empty
  unfolding vars_llist_alt_def
  unfolding has_failed_def[symmetric]
  by sepref

declare check_linear_combi_l_impl.refine[sepref_fr_rules]

sepref_register is_cfailed is_Del

definition PAC_checker_l_step' ::  _ where
  \<open>PAC_checker_l_step' a b c d = PAC_checker_l_step a (b, c, d)\<close>

lemma PAC_checker_l_step_alt_def:
  \<open>PAC_checker_l_step a bcd e = (let (b,c,d) = bcd in PAC_checker_l_step' a b c d e)\<close>
  unfolding PAC_checker_l_step'_def by auto

sepref_decl_intf ('k) acode_status is "('k) code_status"
sepref_decl_intf ('k, 'b, 'lbl) apac_step is "('k, 'b, 'lbl) pac_step"

sepref_register merge_cstatus full_normalize_poly new_var is_Add

sepref_register check_linear_combi_l check_extension_l2
    term check_extension_l2

definition check_extension_l2_cond :: \<open>nat \<Rightarrow> _\<close> where
  \<open>check_extension_l2_cond i A \<V> v = SPEC (\<lambda>b. b \<longrightarrow> i \<notin># dom_m A \<and> v \<notin> \<V>)\<close>

definition check_extension_l2_cond2 :: \<open>nat \<Rightarrow> _\<close> where
  \<open>check_extension_l2_cond2 i A \<V> v = RETURN (fmlookup' i A = None \<and> v \<notin> \<V>)\<close>

lemma lookup_none_by_contains:
  \<open>fmlookup' i A = None \<equiv> \<not>op_fmap_contains_key i A\<close>
  unfolding fmlookup'_def op_fmap_contains_key_def
  by (simp add: in_dom_m_lookup_iff)

sepref_definition check_extension_l2_cond2_impl
  is \<open>uncurry3 check_extension_l2_cond2\<close>
    :: \<open>(unat_assn' TYPE(64))\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a vars_hs_assn\<^sup>k *\<^sub>a strl_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [[goals_limit=1]]
  unfolding check_extension_l2_cond2_def lookup_none_by_contains
  by sepref

lemma check_extension_l2_cond2_check_extension_l2_cond:
  \<open>(uncurry3 check_extension_l2_cond2, uncurry3 check_extension_l2_cond) \<in>
  (((nat_rel \<times>\<^sub>r Id) \<times>\<^sub>r Id) \<times>\<^sub>r Id) \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  by (auto intro!: RES_refine nres_relI frefI
    simp: check_extension_l2_cond_def check_extension_l2_cond2_def in_dom_m_lookup_iff)

text \<open>The interface type must be given explicitly: a plain \<open>sepref_register\<close> derives it
  from the HOL type, leaving the map argument at plain \<^typ>\<open>(nat, 'v) fmap\<close> \<emdash> but the
  argument's assertion \<open>polys_assn\<close> yields interface \<open>(nat, 'v) f_map\<close>, so the id phase
  gets stuck on an unsolvable \<open>ID\<close> goal.\<close>
sepref_register check_extension_l2_cond
  :: \<open>nat \<Rightarrow> (nat, 'v) f_map \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool nres\<close>

lemmas [sepref_fr_rules] =
  check_extension_l2_cond2_impl.refine[FCOMP check_extension_l2_cond2_check_extension_l2_cond]

(* Again, we don't do printing for now
definition check_extension_l_side_cond_err_impl :: \<open>_ \<Rightarrow> _\<close>  where
  \<open>check_extension_l_side_cond_err_impl v r s =
    ''Error while checking side conditions of extensions polynow, var is '' @ show v @
    ''side condition p*p - p = '' @ show s @ '' and should be 0''\<close>
*)
term check_extension_l_side_cond_err
lemma [sepref_fr_rules]:
  \<open>(uncurry2 (\<lambda>_ _ _. Mreturn 0), uncurry2 (check_extension_l_side_cond_err)) 
  \<in> strl_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
  unfolding check_extension_l_side_cond_err_def
  apply sepref_to_hoare
  by (vcg; auto simp: status_pure_reassembly)

(* No printing for now
definition check_extension_l_new_var_multiple_err_impl :: \<open>_ \<Rightarrow> _\<close>  where
  \<open>check_extension_l_new_var_multiple_err_impl v p =
    ''Error while checking side conditions of extensions polynow, var is '' @ show v @
    '' but it either appears at least once in the polynomial or another new variable is created '' @
    show p @ '' but should not.''\<close>
*)

lemma [sepref_fr_rules]:
  \<open>(uncurry (\<lambda>_ _. Mreturn 0), uncurry (check_extension_l_new_var_multiple_err)) 
  \<in> strl_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
  unfolding
     check_extension_l_new_var_multiple_err_def
  apply sepref_to_hoare
  by (vcg; auto simp: status_pure_reassembly)

lemma[sepref_fr_rules]:
  \<open>(\<lambda>_. Mreturn 1, check_extension_l_dom_err)
  \<in> (unat_assn' TYPE(64))\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
  unfolding check_extension_l_dom_err_def
  apply sepref_to_hoare
  by vcg

definition \<open>pempty p \<equiv> (p = [])\<close> 

lemma weak_equality_l_pempty: \<open>(\<lambda>p. weak_equality_l p []) = RETURN o pempty\<close>
  using pempty_def weak_equality_l_def by fastforce

sepref_def pempty_impl is \<open>RETURN o pempty\<close>
  :: \<open>poly_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding pempty_def
  by sepref

sepref_register pempty
sepref_definition test is \<open>\<lambda>p. weak_equality_l p []\<close>
  :: \<open>poly_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding weak_equality_l_pempty
  by sepref

sepref_register weak_equality_l
sepref_definition check_extension_l_impl
  is \<open>uncurry5 check_extension_l2\<close>
    :: \<open>poly_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a vars_hs_assn\<^sup>k *\<^sub>a (unat_assn' TYPE(64))\<^sup>k *\<^sub>a
    strl_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a status_assn raw_string_assn\<close>
  supply [[goals_limit=1]]
  unfolding check_extension_l2_def
  unfolding not_not is_None_def
  unfolding uminus_poly_def[symmetric]
  unfolding check_extension_l2_cond_def[symmetric]
  unfolding vars_llist_alt_def
  unfolding weak_equality_l_pempty
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply sepref_dbg_side_unfold
  term uminus_poly (* this is gonna need some work *)
  oops

lemmas [sepref_fr_rules] =
  check_extension_l_impl.refine

lemma is_Mult_lastI:
  \<open>\<not> is_CL b \<Longrightarrow> \<not>is_Extension b \<Longrightarrow> is_Del b\<close>
  by (cases b) auto

sepref_definition check_step_impl
  is \<open>uncurry4 PAC_checker_l_step'\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a (status_assn raw_string_assn)\<^sup>d *\<^sub>a vars_hs_assn\<^sup>d *\<^sub>a polys_assn\<^sup>d 
      *\<^sub>a (pac_step_rel_assn (unat_assn' TYPE(64)) poly_assn strl_assn)\<^sup>d \<rightarrow>\<^sub>a
         status_assn raw_string_assn \<times>\<^sub>a vars_hs_assn \<times>\<^sub>a polys_assn\<close>
  unfolding PAC_checker_l_step_def PAC_checker_l_step'_def
    pac_step.case_eq_if Let_def
     is_success_alt_def[symmetric]
    uminus_poly_def[symmetric]
    HOL_list.fold_custom_empty
  apply sepref_dbg_keep
  oops

declare check_step_impl.refine[sepref_fr_rules]

sepref_register PAC_checker_l_step PAC_checker_l_step' fully_normalize_poly_impl

definition PAC_checker_l' where
  \<open>PAC_checker_l' p \<V> A status steps = PAC_checker_l p (\<V>, A) status steps\<close>

lemma PAC_checker_l_alt_def:
  \<open>PAC_checker_l p \<V>A status steps =
    (let (\<V>, A) = \<V>A in PAC_checker_l' p \<V> A status steps)\<close>
  unfolding PAC_checker_l'_def by auto


lemma step_rewrite_pure:
  fixes K :: \<open>('olbl \<times> 'lbl) set\<close>
  shows
    \<open>pure (p2rel (\<langle>K, V, R\<rangle>pac_step_rel_raw)) = pac_step_rel_assn (pure K) (pure V) (pure R)\<close>
  apply (intro ext)
  apply (case_tac x; case_tac xa)
  apply simp_all
  apply (simp_all add: relAPP_def p2rel_def pure_def)
  unfolding pure_def[symmetric] list_assn_pure_conv
  apply (auto simp: pure_def relAPP_def)
  done

(* these most likely won't work with llvm anyways
lemma safe_epac_step_rel_assn[safe_constraint_rules]:
  \<open>CONSTRAINT is_pure K \<Longrightarrow> CONSTRAINT is_pure V \<Longrightarrow> CONSTRAINT is_pure R \<Longrightarrow>
  CONSTRAINT is_pure (LPAC_Checker.pac_step_rel_assn K V R)\<close>
  by (auto simp: step_rewrite_pure(1)[symmetric] is_pure_conv)
*)

sepref_definition PAC_checker_l_impl
  is \<open>uncurry4 PAC_checker_l'\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a vars_hs_assn\<^sup>d *\<^sub>a polys_assn\<^sup>d *\<^sub>a (status_assn raw_string_assn)\<^sup>d *\<^sub>a
       (list_assn (pac_step_rel_assn (uint64_nat_assn) poly_assn string_assn))\<^sup>k \<rightarrow>\<^sub>a
     status_assn raw_string_assn \<times>\<^sub>a vars_hs_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro]
  unfolding PAC_checker_l_def is_success_alt_def[symmetric] PAC_checker_l_step_alt_def
    nres_bind_let_law[symmetric] PAC_checker_l'_def
    conv_to_is_Nil is_Nil_def
  apply (subst nres_bind_let_law)
  by sepref

declare PAC_checker_l_impl.refine[sepref_fr_rules]

abbreviation polys_assn_input where
  \<open>polys_assn_input \<equiv> iam_fmap_assn nat_assn poly_assn\<close>

(* ignore printing for now
definition remap_polys_l_dom_err_impl :: \<open>_\<close>  where
  \<open>remap_polys_l_dom_err_impl =
    ''Error during initialisation. Too many polynomials where provided. If this happens,'' @
    ''please report the example to the authors, because something went wrong during '' @
    ''code generation (code generation to arrays is likely to be broken).''\<close>
*)

lemma [sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0), uncurry0 (remap_polys_l_dom_err)) 
  \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding remap_polys_l_dom_err_def
     remap_polys_l_dom_err_def
     list_assn_pure_conv
   by sepref_to_hoare sep_auto

text \<open>MLton is not able to optimise the calls to pow.\<close>
lemma pow_2_64: \<open>(2::nat) ^ 64 = 18446744073709551616\<close>
  by auto

sepref_register upper_bound_on_dom op_fmap_empty

definition full_checker_l2
  :: \<open>llist_polynomial \<Rightarrow> (nat, llist_polynomial) fmap \<Rightarrow> (_, string, nat) pac_step list \<Rightarrow>
    (string code_status \<times> _) nres\<close>
where
  \<open>full_checker_l2 spec A st = do {
    spec' \<leftarrow> full_normalize_poly spec;
    (b, \<V>, A) \<leftarrow> remap_polys_l spec {} A;
    if is_cfailed b
    then RETURN (b, \<V>, A)
    else do {
      PAC_checker_l spec' (\<V>, A) b st
    }
  }\<close>

sepref_register remap_polys_l
sepref_definition full_checker_l_impl
  is \<open>uncurry2 full_checker_l2\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a polys_assn_input\<^sup>d *\<^sub>a (list_assn (pac_step_rel_assn (uint64_nat_assn) poly_assn string_assn))\<^sup>k \<rightarrow>\<^sub>a
    status_assn raw_string_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro]
  unfolding full_checker_l_def hs.fold_custom_empty
    union_vars_poly_alt_def[symmetric]
    PAC_checker_l_alt_def
    full_checker_l2_def
  by sepref

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

lemmas [code] =
  hashcode_literal_def[unfolded String.explode_code
    unsafe_asciis_of_literal_def[symmetric]]

definition uint32_of_char where
  [symmetric, code_unfold]: \<open>uint32_of_char x = uint32_of_int (int_of_char x)\<close>


code_printing
  constant uint32_of_char \<rightharpoonup>
    (SML) "!(Word32.fromInt /o (Char.ord))"

lemma [code]: \<open>hashcode s = hashcode_literal' s\<close>
  unfolding hashcode_literal_def hashcode_list_def
  apply (auto simp: unsafe_asciis_of_literal_def hashcode_list_def
     String.asciis_of_literal_def hashcode_literal_def hashcode_literal'_def)
  done

text \<open>We compile Pastèque in \<^file>\<open>LPAC_Checker_MLton.thy\<close>.\<close>
export_code PAC_checker_l_impl PAC_update_impl PAC_empty_impl the_error is_cfailed is_cfound
  int_of_integer Del nat_of_integer String.implode remap_polys_l_impl
  fully_normalize_poly_impl union_vars_poly_impl empty_vars_impl
  full_checker_l_impl check_step_impl CSUCCESS
  Extension hashcode_literal' version
  in SML_imp module_name PAC_Checker
  file_prefix checker


(* compile_generated_files _
 *   external_files
 *     \<open>code/no_sharing/parser.sml\<close>
 *     \<open>code/no_sharing/pasteque.sml\<close>
 *     \<open>code/no_sharing/pasteque.mlb\<close>
 *   where \<open>fn dir =>
 *   let
 * 
 *     val exec = Generated_Files.execute (Path.append (Path.append dir (Path.basic "code")) (Path.basic "no_sharing"));
 *     val _ = exec \<open>Copy files\<close> "ls" |> @{print}
 *     val _ = exec \<open>Copy files\<close> "ls .." |> @{print}
 *     val _ = exec \<open>Copy files\<close> "pwd" |> @{print}
 *     val _ = exec \<open>Copy files\<close> ("cp ../checker.ML .");
 *     val _ = exec \<open>Copy files\<close>
 *       ("cp ../checker.ML " ^ ((File.bash_path \<^path>\<open>$ISAFOL\<close>) ^ "/PAC_Checker2/code/no_sharing/checker.ML"));
 * (\*       val _ =
 *         exec \<open>Compilation\<close>
 *           (File.bash_path \<^path>\<open>$ISABELLE_MLTON\<close> ^ " " ^
 *             "-const 'MLton.safe false' -verbose 1 -default-type int64 -output pasteque " ^
 *             "-codegen native -inline 700 -cc-opt -O3 pasteque.mlb"); *\)
 *     in () end\<close>  *)


end
