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

sepref_register check_linear_combi_l_pre_err

lemma [sepref_fr_rules]:
  \<open>(uncurry3 (\<lambda>_ _ _ _. Mreturn 0), uncurry3 check_linear_combi_l_pre_err)
  \<in> (unat_assn' TYPE(64))\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
  unfolding check_linear_combi_l_pre_err_def
  apply sepref_to_hoare
  by (vcg; auto)

(* How to do printing: *)
(* definition \<open>print4 \<equiv> \<lambda>_ _ _ _. RETURN 0\<close> *)
(* sepref_def print4_impl is \<open>uncurry3 print4\<close>
 *   :: \<open>(unat_assn' TYPE(64))\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a (unat_assn' TYPE(1))\<close>
 *   unfolding print4_def
 *   apply (annot_unat_const "TYPE(1)")
 *   by sepref
 * 
 * lemma print4_refine: \<open>(uncurry3 print4, uncurry3 check_linear_combi_l_pre_err)
 *   \<in> (((Id \<times>\<^sub>r Id) \<times>\<^sub>r Id) \<times>\<^sub>r Id) \<rightarrow>\<^sub>f \<langle>{(a, b). True}\<rangle>nres_rel\<close>
 *   unfolding print4_def check_linear_combi_l_pre_err_def 
 *   apply (intro frefI nres_relI)
 *   apply auto
 *   by (simp add: RETURN_RES_refine)
 * 
 * lemmas [sepref_fr_rules] = print4_impl.refine[FCOMP print4_refine]
 * sepref_register check_linear_combi_l_pre_err
 * sepref_def test is \<open>uncurry3 check_linear_combi_l_pre_err\<close>
 *   :: \<open>[\<lambda>bb. True]\<^sub>a (unat_assn' TYPE(64))\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a
 *         bool1_assn\<^sup>k \<rightarrow> pure (unat_rel' TYPE(1) O {(b::(nat \<times> string)). True})\<close>
 *   by sepref *)


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
  by (vcg; auto)

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
  by (vcg; auto)

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

subsubsection \<open>Collecting the Variables of a Polynomial\<close>

text \<open>The var-collection sibling of the \<open>vars_of_poly_in\<close> walk: insert every
  variable of a (kept) polynomial into the variable hash set. \<open>vars_hs_insert\<close>
  keeps its element argument (it copies internally on actual insertion), so the
  walk borrows the strings from the polynomial without any explicit copies.\<close>

fun union_vars_monom :: \<open>string list \<Rightarrow> string set \<Rightarrow> string set\<close> where
  \<open>union_vars_monom [] \<V> = \<V>\<close> |
  \<open>union_vars_monom (x # xs) \<V> = union_vars_monom xs (insert x \<V>)\<close>

fun union_vars_poly :: \<open>llist_polynomial \<Rightarrow> string set \<Rightarrow> string set\<close> where
  \<open>union_vars_poly [] \<V> = \<V>\<close> |
  \<open>union_vars_poly ((ys, _) # xs) \<V> = union_vars_poly xs (union_vars_monom ys \<V>)\<close>

lemma union_vars_monom_alt_def:
  \<open>union_vars_monom xs \<V> = \<V> \<union> set xs\<close>
  by (induction xs arbitrary: \<V>) auto

lemma union_vars_poly_alt_def:
  \<open>union_vars_poly xs \<V> = \<V> \<union> vars_llist xs\<close>
proof (induction xs arbitrary: \<V>)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by (metis Un_ac(1) list.distinct(1) list.simps(1) prod.sel(1) union_vars_monom_alt_def union_vars_poly.elims vars_llist(3)) 
qed


(*
   (auto simp: vars_llist_def union_vars_monom_alt_def)
*)
lemma vars_hs_insert_rule:
  \<open>llvm_htriple
    (vars_hs_assn \<V> vi ** strl_assn x xi)
    (vars_hs_insert_impl xi vi)
    (\<lambda>r. vars_hs_assn (insert x \<V>) r ** strl_assn x xi)\<close>
  unfolding vars_hs_assn_def hs_set_assn_def vars_hs_insert_impl_def
  supply [vcg_rules] = hs_insert_impl_rule[OF strl_hash_rule str_eq_rule strl_copy_rule]
  supply [simp] = hr_comp_def hs_rel_def in_br_conv sep_conj_exists
  apply vcg
  by (smt (verit, best) ENTAILS_def entails_def hs_ins_abs hs_ins_invar pure_true_conv sep_conj_empty' set_concat)

partial_function (M) union_vars_monom_impl ::
  \<open>monom_conc \<Rightarrow> 8 word os_list hs_impl \<Rightarrow> 8 word os_list hs_impl llM\<close> where
  \<open>union_vars_monom_impl p vi = (if p = null then Mreturn vi
    else doM {
      n \<leftarrow> ll_load p;
      vi \<leftarrow> vars_hs_insert_impl (node.val n) vi;
      union_vars_monom_impl (node.next n) vi
    })\<close>

lemmas [llvm_code] = union_vars_monom_impl.simps

lemma union_vars_monom_impl_rule[vcg_rules]:
  \<open>llvm_htriple
    (monom_assn xs p ** vars_hs_assn \<V> vi)
    (union_vars_monom_impl p vi)
    (\<lambda>r. monom_assn xs p ** vars_hs_assn (union_vars_monom xs \<V>) r)\<close>
  unfolding ol_assn_conv
proof (induction xs arbitrary: p \<V> vi)
  case Nil
  show ?case
    apply (subst union_vars_monom_impl.simps)
    by vcg
next
  case (Cons e es)
  note [vcg_rules] = Cons.IH vars_hs_insert_rule
  show ?case
    supply [simp, named_ss fri_prepare_simps] = ol_seg_cons
    supply [simp] = sep_conj_exists
    apply (subst union_vars_monom_impl.simps)
    apply (cases \<open>p = null\<close>; simp)
    by vcg
qed

partial_function (M) union_vars_poly_impl ::
  \<open>(monom_conc \<times> sbin_conc \<times> 1 word) os_list \<Rightarrow> 8 word os_list hs_impl
     \<Rightarrow> 8 word os_list hs_impl llM\<close> where
  \<open>union_vars_poly_impl p vi = (if p = null then Mreturn vi
    else doM {
      n \<leftarrow> ll_load p;
      vi \<leftarrow> union_vars_monom_impl (fst (node.val n)) vi;
      union_vars_poly_impl (node.next n) vi
    })\<close>

lemmas [llvm_code] = union_vars_poly_impl.simps

lemma union_vars_poly_impl_rule[vcg_rules]:
  \<open>llvm_htriple
    (poly_assn xs p ** vars_hs_assn \<V> vi)
    (union_vars_poly_impl p vi)
    (\<lambda>r. poly_assn xs p ** vars_hs_assn (union_vars_poly xs \<V>) r)\<close>
  unfolding ol_assn_conv
proof (induction xs arbitrary: p \<V> vi)
  case Nil
  show ?case
    apply (subst union_vars_poly_impl.simps)
    by vcg
next
  case (Cons e es)
  note [vcg_rules] = Cons.IH union_vars_monom_impl_rule[unfolded ol_assn_conv]
  show ?case
    supply [simp, named_ss fri_prepare_simps] = ol_seg_cons
    supply [simp] = sep_conj_exists
    apply (subst union_vars_poly_impl.simps)
    apply (cases \<open>p = null\<close>; cases e; simp)
    by vcg
qed

sepref_register union_vars_poly

lemma union_vars_poly_hnr[sepref_fr_rules]:
  \<open>(uncurry union_vars_poly_impl, uncurry (RETURN oo union_vars_poly))
    \<in> poly_assn\<^sup>k *\<^sub>a vars_hs_assn\<^sup>d \<rightarrow>\<^sub>a vars_hs_assn\<close>
  apply sepref_to_hoare
  by vcg

(* Note that we have to destroy lincomb - Check in outer loop if 
   that could be tolerated by contiuing with tl, otherwise we need
   to copy the hd out of the list *)
sepref_def linear_combi_l_impl
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

sepref_register has_failed
lemma has_failed_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0), uncurry0 has_failed) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding has_failed_def bool1_rel_def bool.assn_is_rel[symmetric]
  apply sepref_to_hoare
  by (vcg; auto simp: status_pure_reassembly bool.assn_def)

sepref_def check_linear_combi_l_impl
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

sepref_register merge_cstatus full_normalize_poly new_var is_Add

text \<open>Explicit \<open>f_map\<close> interface for the polynomial-map slot (plain registration would
  use raw \<open>fmap\<close> and clash with the \<open>f_map\<close> interface that \<open>polys_assn\<close>'s
  \<open>intf_of_assn\<close> rule assigns to the argument, stalling the id phase of any caller).\<close>
sepref_register
  check_linear_combi_l :: \<open>llist_polynomial \<Rightarrow> (nat, llist_polynomial) f_map
    \<Rightarrow> string set \<Rightarrow> nat \<Rightarrow> (llist_polynomial \<times> nat) list \<Rightarrow> llist_polynomial
    \<Rightarrow> string code_status nres\<close>
sepref_register
  check_extension_l2 :: \<open>'a \<Rightarrow> (nat, 'v) f_map \<Rightarrow> string set \<Rightarrow> nat \<Rightarrow> string
    \<Rightarrow> llist_polynomial \<Rightarrow> string code_status nres\<close>

definition check_extension_l2_cond :: \<open>nat \<Rightarrow> _\<close> where
  \<open>check_extension_l2_cond i A \<V> v = SPEC (\<lambda>b. b \<longrightarrow> i \<notin># dom_m A \<and> v \<notin> \<V>)\<close>

definition check_extension_l2_cond2 :: \<open>nat \<Rightarrow> _\<close> where
  \<open>check_extension_l2_cond2 i A \<V> v = RETURN (fmlookup' i A = None \<and> v \<notin> \<V>)\<close>

lemma lookup_none_by_contains:
  \<open>fmlookup' i A = None \<equiv> \<not>op_fmap_contains_key i A\<close>
  unfolding fmlookup'_def op_fmap_contains_key_def
  by (simp add: in_dom_m_lookup_iff)

sepref_def check_extension_l2_cond2_impl
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

sepref_register weak_equality_l

definition add_poly_l_keep_snd where
  \<open>add_poly_l_keep_snd p q \<equiv> add_poly_l (p, COPY q)\<close>

lemma add_poly_l_keep_snd: \<open>add_poly_l (p, q) = add_poly_l_keep_snd p q\<close>
  unfolding add_poly_l_keep_snd_def COPY_def by simp

sepref_def check_extension_l_impl
  is \<open>uncurry5 check_extension_l2\<close>
    :: \<open>poly_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a vars_hs_assn\<^sup>k *\<^sub>a (unat_assn' TYPE(64))\<^sup>k *\<^sub>a
    strl_assn\<^sup>k *\<^sub>a poly_assn\<^sup>d \<rightarrow>\<^sub>a status_assn raw_string_assn\<close>
  supply [[goals_limit=1]]
  unfolding check_extension_l2_def
  unfolding not_not is_None_def
  unfolding uminus_poly_def[symmetric]
  unfolding check_extension_l2_cond_def[symmetric]
  unfolding add_poly_l_keep_snd
  unfolding add_poly_l_keep_snd_def
  unfolding vars_llist_alt_def
  unfolding fold_ol_empty
  by sepref

lemmas [sepref_fr_rules] =
  check_extension_l_impl.refine

lemma is_Mult_lastI:
  \<open>\<not> is_CL b \<Longrightarrow> \<not>is_Extension b \<Longrightarrow> is_Del b\<close>
  by (cases b) auto

sepref_def check_del_l_impl2
  is \<open>uncurry2 check_del_l\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a (unat_assn' TYPE(64))\<^sup>k \<rightarrow>\<^sub>a status_assn raw_string_assn\<close>
  unfolding check_del_l_def
  by sepref

declare check_del_l_impl2.refine[sepref_fr_rules]

text \<open>Needed for the \<open>-1\<close> literal below: \<open>-1 = uminus 1\<close>, resolved by \<open>sbi_inv_hnr\<close>
  over the registered \<open>1 :: int\<close> constant.\<close>
sepref_register \<open>uminus :: int \<Rightarrow> int\<close>

text \<open>Synthesis-level variant of \<open>PAC_checker_l_step\<close>: the \<open>case\<close> is replaced by
  discriminator tests plus the one-shot destructors \<open>mop_dest_CL\<close>/\<open>mop_dest_Extension\<close>/
  \<open>mop_dest_Del\<close> \<emdash> the owning accessors (\<open>pac_res\<close>, \<open>pac_srcs\<close>, \<open>new_var\<close>) have no hnr
  rules, since ownership must leave the step tuple exactly once. Two \<open>COPY\<close>s restore
  linearity: \<open>r\<close> is consumed by \<open>check_extension_l2\<close> (its last argument is \<open>^d\<close>) but
  reused for \<open>add_poly_l\<close>, and \<open>v\<close> is moved into the poly literal by pair/list
  construction but reused for the \<open>insert\<close> into the variable set.\<close>
definition PAC_checker_l_step2 :: \<open>_ \<Rightarrow> string code_status \<times> string set \<times> _ \<Rightarrow> (llist_polynomial, string, nat) pac_step \<Rightarrow> _\<close> where
  \<open>PAC_checker_l_step2 = (\<lambda>spec (st', \<V>, A) st. do {
    ASSERT(\<not>is_cfailed st');
    ASSERT(PAC_checker_l_step_inv spec st' \<V> A);
    if is_CL st
    then do {
      ASSERT (PAC_checker_l_step_inv spec st' \<V> A);
      (srcs, i, r\<^sub>0) \<leftarrow> mop_dest_CL st;
      r \<leftarrow> full_normalize_poly r\<^sub>0;
      eq \<leftarrow> check_linear_combi_l spec A \<V> i srcs r;
      let _ = eq;
      if \<not>is_cfailed eq
      then RETURN (merge_cstatus st' eq, \<V>, fmupd i r A)
      else RETURN (eq, \<V>, A)
    }
    else if is_Del st
    then do {
      ASSERT (PAC_checker_l_step_inv spec st' \<V> A);
      i \<leftarrow> mop_dest_Del st;
      eq \<leftarrow> check_del_l spec A i;
      let _ = eq;
      if \<not>is_cfailed eq
      then RETURN (merge_cstatus st' eq, \<V>, fmdrop i A)
      else RETURN (eq, \<V>, A)
    }
    else do {
      ASSERT (PAC_checker_l_step_inv spec st' \<V> A);
      (i, v, r\<^sub>0) \<leftarrow> mop_dest_Extension st;
      r \<leftarrow> full_normalize_poly r\<^sub>0;
      eq \<leftarrow> check_extension_l2 spec A \<V> i v (COPY r);
      if \<not>is_cfailed eq
      then do {
        ASSERT(v \<notin> vars_llist r \<and> vars_llist r \<subseteq> \<V>);
        r' \<leftarrow> add_poly_l ([([COPY v], -1)], r);
        RETURN (st', insert v \<V>, fmupd i r' A)
      }
      else RETURN (eq, \<V>, A)
    }
  })\<close>

lemma PAC_checker_l_step2_PAC_checker_l_step:
  \<open>PAC_checker_l_step = PAC_checker_l_step2\<close>
  apply (intro ext)
  subgoal for spec stVA st
    by (cases st; cases stVA)
      (auto simp: PAC_checker_l_step_def PAC_checker_l_step2_def
        mop_dest_CL_def mop_dest_Extension_def mop_dest_Del_def COPY_def
        Let_def pw_eq_iff refine_pw_simps)
  done

sepref_def check_step_impl
  is \<open>uncurry4 PAC_checker_l_step'\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a (status_assn raw_string_assn)\<^sup>d *\<^sub>a vars_hs_assn\<^sup>d *\<^sub>a polys_assn\<^sup>d
      *\<^sub>a (pac_step_assn poly_assn strl_assn)\<^sup>d \<rightarrow>\<^sub>a
         status_assn raw_string_assn \<times>\<^sub>a vars_hs_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]]
  unfolding PAC_checker_l_step'_def
  unfolding PAC_checker_l_step2_PAC_checker_l_step
    PAC_checker_l_step2_def
  unfolding Let_def fold_ol_empty
  by sepref

declare check_step_impl.refine[sepref_fr_rules]

sepref_register
  PAC_checker_l_step' :: \<open>llist_polynomial \<Rightarrow> string code_status \<Rightarrow> string set
    \<Rightarrow> (nat, llist_polynomial) f_map \<Rightarrow> (llist_polynomial, string, nat) i_pac_step
    \<Rightarrow> (string code_status \<times> string set \<times> (nat, llist_polynomial) f_map) nres\<close>
sepref_register fully_normalize_poly_impl

definition PAC_checker_l' where
  \<open>PAC_checker_l' p \<V> A status steps = PAC_checker_l p (\<V>, A) status steps\<close>

lemma PAC_checker_l_alt_def:
  \<open>PAC_checker_l p \<V>A status steps =
    (let (\<V>, A) = \<V>A in PAC_checker_l' p \<V> A status steps)\<close>
  unfolding PAC_checker_l'_def by auto

lemma PAC_checker_l_alt:
  \<open>PAC_checker_l spec A b st = do {
  (S, _) \<leftarrow> WHILE\<^sub>T
    (\<lambda>((b, A), n). \<not>is_cfailed b \<and> n \<noteq> [])
    (\<lambda>((bA), n). do {
      (hd, tl) \<leftarrow> mop_list_pop_front n;
      ASSERT(n \<noteq> []);
      S \<leftarrow> PAC_checker_l_step spec bA hd;
      RETURN (S, tl)
    })
    ((b, A), st);
  RETURN S
  }\<close>
proof -
  text \<open>Pointwise reasoning cannot look through \<open>WHILE\<^sub>T\<close> (a fixpoint), so we prove the
    two loop BODIES equal as functions and rewrite; the rest of the program is
    syntactically identical. Body equality is pointwise: for \<open>n = []\<close> both sides fail
    (the \<open>ASSERT\<close> inside \<open>mop_list_pop_front\<close> resp. the explicit one), otherwise the
    pop is exactly \<open>(hd n, tl n)\<close>.\<close>
  have H: \<open>(\<lambda>((bA), n). do {
      (hd, tl) \<leftarrow> mop_list_pop_front n;
      ASSERT(n \<noteq> []);
      S \<leftarrow> PAC_checker_l_step spec bA hd;
      RETURN (S, tl)
    }) = (\<lambda>((bA), n). do {
      ASSERT(n \<noteq> []);
      S \<leftarrow> PAC_checker_l_step spec bA (hd n);
      RETURN (S, tl n)
    })\<close>
    by (intro ext)
      (auto simp: pw_eq_iff refine_pw_simps split: prod.splits)
  show ?thesis
    unfolding PAC_checker_l_def H
    by (rule refl)
qed
text \<open>Deep free for the leftover steps list at loop exit (the \<open>lincomb_assn_free\<close>
  pattern): the composed \<open>MK_FREE\<close> instance is declared explicitly. (For \<open>export_llvm\<close>
  the \<open>ol_delete\<close> instance will additionally need a named first-order specialization
  with \<open>[llvm_code]\<close> simps, like \<open>lincomb_free\<close>.)\<close>
lemma steps_assn_free[sepref_frame_free_rules]:
  \<open>MK_FREE (ol_assn (pac_step_assn poly_assn strl_assn))
     (ol_delete (pac_step_free_impl poly_free os_delete))\<close>
  by (rule ol_assn_free[OF pac_step_assn_free[OF poly_assn_free os_assn_free]])

sepref_def PAC_checker_l_impl
  is \<open>uncurry4 PAC_checker_l'\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a vars_hs_assn\<^sup>d *\<^sub>a polys_assn\<^sup>d *\<^sub>a (status_assn raw_string_assn)\<^sup>d *\<^sub>a
       (ol_assn (pac_step_assn poly_assn strl_assn))\<^sup>d \<rightarrow>\<^sub>a
     status_assn raw_string_assn \<times>\<^sub>a vars_hs_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]]
  unfolding PAC_checker_l'_def PAC_checker_l_alt
    is_success_alt_def[symmetric]
    PAC_checker_l_step_alt_def
    nres_bind_let_law[symmetric]
    conv_to_is_Nil fold_is_Nil_is_empty
  apply (subst nres_bind_let_law)
  by sepref

(* Need some more setup to get the `ol_delete` function through
 * - its parameterized by the free function of the inner elements
 * so we don't get code export unless we specialize it for the pac_step
 * list.
 * *)
definition \<open>src_entries_free \<equiv> ol_delete (src_entry_free_impl poly_free)\<close>
lemma src_entries_free_simps[llvm_code]:
  \<open>src_entries_free l = (if l = null then Mreturn () else doM {
     n \<leftarrow> ll_load l; src_entry_free_impl poly_free (node.val n); ll_free l;
     src_entries_free (node.next n) })\<close>
  unfolding src_entries_free_def by (rule ol_delete.simps)
lemmas [llvm_pre_simp] = src_entries_free_def[symmetric]

definition step_free :: \<open>(_, 8 word os_list) pac_step_impl \<Rightarrow> unit llM\<close> where
  \<open>step_free \<equiv> pac_step_free_impl poly_free os_delete\<close>
lemma step_free_code[llvm_code]:
  \<open>step_free = (\<lambda>(t, idc, res, srcs, var).
     if t = 0 then doM { src_entries_free srcs; poly_free res }
     else if t = 1 then doM { os_delete var; poly_free res }
     else Mreturn ())\<close>
  unfolding step_free_def pac_step_free_impl_def src_entries_free_def by (rule refl)
lemmas [llvm_pre_simp] = step_free_def[symmetric]

definition \<open>steps_free \<equiv> ol_delete step_free\<close>
lemma steps_free_simps[llvm_code]:
  \<open>steps_free l = (if l = null then Mreturn () else doM {
     n \<leftarrow> ll_load l; step_free (node.val n); ll_free l; steps_free (node.next n) })\<close>
  unfolding steps_free_def by (rule ol_delete.simps)

(* Need these to get code export through *)
lemmas [llvm_pre_simp] = steps_free_def[symmetric]
lemmas [llvm_pre_simp] = pull_lambda_case

export_llvm PAC_checker_l_impl

declare PAC_checker_l_impl.refine[sepref_fr_rules]

sepref_register
  PAC_checker_l' :: \<open>llist_polynomial \<Rightarrow> string set \<Rightarrow> (nat, llist_polynomial) f_map
    \<Rightarrow> string code_status \<Rightarrow> (llist_polynomial, string, nat) i_pac_step list
    \<Rightarrow> (string code_status \<times> string set \<times> (nat, llist_polynomial) f_map) nres\<close>

(* don't this we need this, we will need array \<rightarrow> list translation for the parsed obejcts anyways *)
(* abbreviation polys_assn_input where
 *   \<open>polys_assn_input \<equiv> iam_fmap_assn nat_assn poly_assn\<close> *)

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
   unfolding remap_polys_l_dom_err_def remap_polys_l_dom_err_def
  apply sepref_to_hoare 
  apply vcg
  done

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

subsection \<open>Input Polynomials as an Association List\<close>

text \<open>No parser naturally produces the \<open>fmap\<close> that \<open>remap_polys_l\<close> consumes: the
  map only comes into existence during the remapping itself. \<open>remap_polys_l4\<close>
  therefore takes the input polynomials as an association list \<open>(id, polynomial)\<close>
  and folds \<open>fmupd\<close> over it (with normalization, variable collection and the spec
  check exactly as in \<open>remap_polys_l\<close>), consuming the list front-to-back with
  \<open>op_list_pop_front\<close> (cf. \<open>linear_combi_l2\<close>). Duplicate ids are rejected on the
  fly via the accumulated map's domain; this instantiates the \<open>failed\<close> branch of
  \<open>remap_polys_l\<close>, which unconditionally permits an error result. On the error
  path the variable set of \<open>remap_polys_l\<close>'s error result is its \<^emph>\<open>input\<close> set;
  since the fold consumes its set destructively, \<open>remap_polys_l4\<close> fixes the input
  set to \<open>{}\<close> (the only instantiation the checker uses) and returns a fresh empty
  set there.\<close>

definition remap_polys_l4 :: \<open>llist_polynomial \<Rightarrow> (nat \<times> llist_polynomial) list \<Rightarrow>
   (string code_status \<times> string set \<times> (nat, llist_polynomial) fmap) nres\<close> where
  \<open>remap_polys_l4 spec xs = do {
    (_, err, b, \<V>, A) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(xs, err, b, \<V>, A). xs \<noteq> [] \<and> \<not>is_cfailed err)
      (\<lambda>(xs, err, b, \<V>, A'). do {
         ASSERT (xs \<noteq> []);
         let ((i, p\<^sub>0), xs') = op_list_pop_front xs;
         if i \<in># dom_m A' then do {
           c \<leftarrow> remap_polys_l_dom_err;
           RETURN (xs', error_msg (0::nat) c, b, \<V>, A')
         } else do {
           let \<V> = union_vars_poly p\<^sub>0 \<V>;
           p \<leftarrow> full_normalize_poly p\<^sub>0;
           eq \<leftarrow> weak_equality_l p spec;
           RETURN (xs', err, b \<or> eq, \<V>, fmupd i p A')
         }
       })
      (xs, CSUCCESS, False, {}, fmempty);
    if is_cfailed err
    then RETURN (err, {}, fmempty)
    else RETURN (if b then CFOUND else CSUCCESS, \<V>, A)
  }\<close>

context
begin

private lemma bind_SPEC_refineI:
  \<open>\<Phi> x \<Longrightarrow> S \<le> \<Down>R (f x) \<Longrightarrow> S \<le> \<Down>R (do {x \<leftarrow> SPEC \<Phi>; f x})\<close>
  by (simp add: rhs_step_bind_SPEC)

private lemma bind_ASSERT_refineI:
  \<open>P \<Longrightarrow> S \<le> \<Down>R f \<Longrightarrow> S \<le> \<Down>R (do {ASSERT P; f})\<close>
  by (auto simp: pw_le_iff refine_pw_simps)

private lemma dom_m_fmap_of_list:
  \<open>i \<in># dom_m (fmap_of_list xs) \<longleftrightarrow> i \<in> fst ` set xs\<close>
  by (simp add: fmap_of_list.rep_eq in_dom_m_lookup_iff map_of_eq_None_iff)

private lemma fmlookup_fmap_of_list_nth:
  \<open>distinct (map fst xs) \<Longrightarrow> (i, p) \<in> set xs \<Longrightarrow> fmlookup (fmap_of_list xs) i = Some p\<close>
  by (simp add: fmlookup_of_list)

private lemma refine_Id_self: \<open>M \<le> \<Down>Id M\<close>
  by (auto simp: pw_le_iff refine_pw_simps)

private lemma R_st_step_witness:
  \<open>xs = pre @ (i, p\<^sub>0) # xs' \<Longrightarrow> i \<notin># dom_m A \<Longrightarrow> set_mset (dom_m A) = fst ` set pre \<Longrightarrow>
     \<exists>pre'. xs = pre' @ xs' \<and> set_mset (dom_m (fmupd i p A)) = fst ` set pre'\<close>
  by (rule exI[of _ \<open>pre @ [(i, p\<^sub>0)]\<close>]) auto

private lemma is_cfailed_error_msg[simp]: \<open>is_cfailed (error_msg n c)\<close>
  by (auto simp: error_msg_def)

private lemma l4_err_prefix_snocI:
  \<open>xs = pre @ y # xs' \<Longrightarrow> \<exists>pre'. xs = pre' @ xs'\<close>
  by (rule exI[of _ \<open>pre @ [y]\<close>]) auto

private lemma no_cons_eq_Nil[simp]: \<open>(\<forall>a b ys. ad \<noteq> (a, b) # ys) \<longleftrightarrow> ad = []\<close>
  by (cases ad) auto

text \<open>The error-case invariant holds for \<^emph>\<open>arbitrary\<close> results of the loop body's
  monadic steps, so all that is needed about them is that they cannot fail.\<close>

private lemma full_normalize_poly_nofail: \<open>nofail (full_normalize_poly p)\<close>
proof -
  have \<open>nofail (monadic_nfoldli p (\<lambda>_. RETURN True)
     (\<lambda>(a, n) b. do {a \<leftarrow> sort_coeff a; RETURN ((a, n) # b)}) acc)\<close> for acc
  proof (induction p arbitrary: acc)
    case Nil
    then show ?case by (subst monadic_nfoldli_eq) (auto simp: refine_pw_simps)
  next
    case (Cons x p)
    then show ?case
      by (subst monadic_nfoldli_eq)
        (auto simp: refine_pw_simps sort_coeff_def split: prod.splits)
  qed
  then show ?thesis
    unfolding full_normalize_poly_def sort_all_coeffs_def sort_poly_spec_def
    by (auto simp: refine_pw_simps)
qed

private lemma l4_err_step_witness:
  \<open>xs = pre @ (i, p\<^sub>0) # xs' \<Longrightarrow> i \<notin> fst ` set pre \<Longrightarrow> distinct (map fst pre) \<Longrightarrow>
   \<exists>pre'. xs = pre' @ xs' \<and> distinct (map fst pre') \<and>
      insert i (fst ` set pre) = fst ` set pre'\<close>
  by (rule exI[of _ \<open>pre @ [(i, p\<^sub>0)]\<close>]) auto

lemma remap_polys_l4_remap_polys_l:
  \<open>remap_polys_l4 spec xs \<le> \<Down>Id (remap_polys_l spec {} (fmap_of_list xs))\<close>
proof (cases \<open>distinct (map fst xs)\<close>)
  case True
  note dist = this
  text \<open>Simulate the \<open>FOREACH\<close> after resolving its nondeterminism: iterate the
    domain in list order, do not fail.\<close>
  define R_st :: \<open>((nat \<times> llist_polynomial) list \<times> string code_status \<times> bool \<times> string set \<times>
      (nat, llist_polynomial) fmap) \<times> nat list \<times> bool \<times> string set \<times> (nat, llist_polynomial) fmap \<Rightarrow> bool\<close>
    where \<open>R_st = (\<lambda>((xsr, err, b, \<V>, A), (itr, br, \<V>r, Ar)).
      itr = map fst xsr \<and> err = CSUCCESS \<and> br = b \<and> \<V>r = \<V> \<and> Ar = A \<and>
      (\<exists>pre. xs = pre @ xsr \<and> set_mset (dom_m A) = fst ` set pre))\<close>
  have init: \<open>R_st ((xs, CSUCCESS, False, {}, fmempty), (map fst xs, False, {}, fmempty))\<close>
    by (auto simp: R_st_def)
  show ?thesis
    unfolding remap_polys_l4_def remap_polys_l_def FOREACH_def FOREACHc_def FOREACHci_def
      FOREACHoci_def WHILET_def
    apply (insert dist)
    apply (rule bind_SPEC_refineI[where x = \<open>set (map fst xs)\<close>])
    subgoal by (auto simp: dom_m_fmap_of_list)
    apply (rule bind_SPEC_refineI[where x = False])
    subgoal by simp
    apply (simp only: if_False nres_monad1 nres_monad3)
    apply (rule bind_ASSERT_refineI)
    subgoal by simp
    apply (rule bind_SPEC_refineI[where x = \<open>map fst xs\<close>])
    subgoal by simp
    apply (refine_rcg WHILEIT_refine[where R = \<open>{(a, b). R_st (a, b)}\<close>])
    subgoal using init by simp
    subgoal by (auto simp: R_st_def FOREACH_cond_def)
    subgoal
      by (auto simp: pw_le_iff refine_pw_simps R_st_def FOREACH_body_def
        FOREACH_cond_def op_list_pop_front_def Let_def union_vars_poly_alt_def
        neq_Nil_conv dom_m_fmap_of_list fmlookup_fmap_of_list_nth
        intro: R_st_step_witness
        split: prod.splits if_splits)
    subgoal by (auto simp: R_st_def)
    subgoal \<comment> \<open>loop step\<close>
      apply (clarsimp simp: R_st_def FOREACH_body_def op_list_pop_front_def
        neq_Nil_conv Let_def union_vars_poly_alt_def nres_monad1 nres_monad3
        dom_m_fmap_of_list fset_of_list.rep_eq
        split: prod.splits)
      apply (refine_rcg)
      apply (auto simp: R_st_def fset_of_list.rep_eq pair_in_Id_conv
        remap_polys_l_dom_err_def
        intro: R_st_step_witness refine_Id_self)
      apply (metis list.sel(3))
      done
    subgoal \<comment> \<open>post-loop continuation\<close>
      by (auto simp: R_st_def nres_monad1 pw_le_iff refine_pw_simps)
    done
next
  case False
  text \<open>A duplicate id will be hit; the result is an error, which the \<open>failed\<close>
    branch of \<open>remap_polys_l\<close> permits.\<close>
  have l4_err: \<open>remap_polys_l4 spec xs \<le> SPEC (\<lambda>(err, \<V>, A).
      (\<exists>c. err = error_msg (0::nat) c) \<and> \<V> = {} \<and> A = fmempty)\<close>
    unfolding remap_polys_l4_def op_list_pop_front_def
    apply (insert False)
    apply (refine_vcg WHILET_rule[where
      I = \<open>\<lambda>(xsr, err, b, \<V>, A). \<exists>pre. xs = pre @ xsr \<and>
            (\<not>is_cfailed err \<longrightarrow> distinct (map fst pre) \<and> set_mset (dom_m A) = fst ` set pre) \<and>
            (is_cfailed err \<longrightarrow> (\<exists>c. err = error_msg (0::nat) c))\<close> and
      R = \<open>measure (\<lambda>(xsr, _). length xsr)\<close>])
    subgoal by auto
    subgoal by (rule exI[of _ \<open>[]\<close>]) auto
    apply (auto simp: neq_Nil_conv Let_def union_vars_poly_alt_def
      weak_equality_l_def full_normalize_poly_nofail remap_polys_l_dom_err_def
      pw_le_iff refine_pw_simps
      intro: l4_err_prefix_snocI l4_err_step_witness
      split: prod.splits)
    done
  show ?thesis
    apply (rule order_trans[OF l4_err])
    by (auto simp: remap_polys_l_def remap_polys_l_dom_err_def
      pw_le_iff refine_pw_simps)
qed

end

definition full_checker_l3
  :: \<open>llist_polynomial \<Rightarrow> (nat \<times> llist_polynomial) list \<Rightarrow> (_, string, nat) pac_step list \<Rightarrow>
    (string code_status \<times> _) nres\<close>
where
  \<open>full_checker_l3 spec xs st = do {
    spec' \<leftarrow> full_normalize_poly (COPY spec);
    (b, \<V>, A) \<leftarrow> remap_polys_l4 spec xs;
    if is_cfailed b
    then RETURN (b, \<V>, A)
    else do {
      PAC_checker_l spec' (\<V>, A) b st
    }
  }\<close>

lemma full_checker_l3_full_checker_l2:
  \<open>full_checker_l3 spec xs st \<le> \<Down>Id (full_checker_l2 spec (fmap_of_list xs) st)\<close>
  unfolding full_checker_l3_def full_checker_l2_def
  apply (rule bind_refine[where R' = Id])
  subgoal by auto
  apply (rule bind_refine[where R' = Id])
  subgoal by (rule remap_polys_l4_remap_polys_l)
  subgoal by (auto split: prod.splits)
  done

abbreviation inputs_assn where
  \<open>inputs_assn \<equiv> ol_assn (unat_assn' TYPE(64) \<times>\<^sub>a poly_assn)\<close>

sepref_def full_checker_l3_impl
  is \<open>uncurry2 full_checker_l3\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a inputs_assn\<^sup>d *\<^sub>a (ol_assn (pac_step_assn poly_assn strl_assn))\<^sup>d \<rightarrow>\<^sub>a
    status_assn raw_string_assn \<times>\<^sub>a vars_hs_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]]
  unfolding full_checker_l3_def
    remap_polys_l4_def
    PAC_checker_l_alt_def
    vars_hs.fold_custom_empty
    conv_to_is_Nil
    fold_is_Nil_is_empty
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  apply sepref_dbg_keep
  done

(* Don't think any of this stuff is needed for llvm... *)
(* sepref_definition PAC_empty_impl
 *   is \<open>uncurry0 (RETURN fmempty)\<close>
 *   :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a polys_assn\<close>
 *   unfolding op_iam_fmap_empty_def[symmetric] pat_fmap_empty
 *   by sepref
 * 
 * sepref_definition empty_vars_impl
 *   is \<open>uncurry0 (RETURN {})\<close>
 *   :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a vars_assn\<close>
 *   unfolding hs.fold_custom_empty
 *   by sepref
 * 
 * text \<open>This is a hack for performance. There is no need to recheck that that a char is valid when
 *   working on chars coming from strings... It is not that important in most cases, but in our case
 *   the preformance difference is really large.\<close>
 * 
 * 
 * definition unsafe_asciis_of_literal :: \<open>_\<close> where
 *   \<open>unsafe_asciis_of_literal xs = String.asciis_of_literal xs\<close>
 * 
 * definition unsafe_asciis_of_literal' :: \<open>_\<close> where
 *   [simp, symmetric, code]: \<open>unsafe_asciis_of_literal' = unsafe_asciis_of_literal\<close>
 * 
 * code_printing
 *   constant unsafe_asciis_of_literal' \<rightharpoonup>
 *     (SML) "!(List.map (fn c => let val k = Char.ord c in IntInf.fromInt k end) /o String.explode)"
 * 
 * text \<open>
 *   Now comes the big and ugly and unsafe hack.
 * 
 *   Basically, we try to avoid the conversion to IntInf when calculating the hash. The performance
 *   gain is roughly 40\%, which is a LOT and definitively something we need to do. We are aware that the
 *   SML semantic encourages compilers to optimise conversions, but this does not happen here,
 *   corroborating our early observation on the verified SAT solver IsaSAT.x
 * \<close>
 * definition raw_explode where
 *   [simp]: \<open>raw_explode = String.explode\<close>
 * code_printing
 *   constant raw_explode \<rightharpoonup>
 *     (SML) "String.explode"
 * 
 * lemmas [code] =
 *   hashcode_literal_def[unfolded String.explode_code
 *     unsafe_asciis_of_literal_def[symmetric]]
 * 
 * definition uint32_of_char where
 *   [symmetric, code_unfold]: \<open>uint32_of_char x = uint32_of_int (int_of_char x)\<close>
 * 
 * 
 * code_printing
 *   constant uint32_of_char \<rightharpoonup>
 *     (SML) "!(Word32.fromInt /o (Char.ord))"
 * 
 * lemma [code]: \<open>hashcode s = hashcode_literal' s\<close>
 *   unfolding hashcode_literal_def hashcode_list_def
 *   apply (auto simp: unsafe_asciis_of_literal_def hashcode_list_def
 *      String.asciis_of_literal_def hashcode_literal_def hashcode_literal'_def)
 *   done *)

(* TODO properly export code in separate theory *)
(* text \<open>We compile Pastèque in \<^file>\<open>LPAC_Checker_MLton.thy\<close>.\<close>
 * export_code PAC_checker_l_impl PAC_update_impl PAC_empty_impl the_error is_cfailed is_cfound
 *   int_of_integer Del nat_of_integer String.implode remap_polys_l_impl
 *   fully_normalize_poly_impl union_vars_poly_impl empty_vars_impl
 *   full_checker_l_impl check_step_impl CSUCCESS
 *   Extension hashcode_literal' version *)

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
