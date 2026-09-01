(*
  File:         PAC_Checker_Synthesis.thy
  Author:       Mathias Fleury, Daniela Kaufmann, JKU
  Maintainer:   Mathias Fleury, JKU
*)
theory LPAC_Checker_Synthesis
  imports LPAC_Error
begin
hide_fact (open) PAC_Checker.PAC_checker_l_def
hide_const (open) PAC_Checker.PAC_checker_l

section \<open>Code Synthesis of the Complete Checker\<close>

abbreviation \<open>poly_input_pair_assn \<equiv> polynomial_assn \<times>\<^sub>a si64_assn\<close>
abbreviation \<open>poly_input_assn \<equiv> cl_assn' poly_input_pair_assn\<close>

lemma linear_combi_alt:
\<open>linear_combi_l i A \<V> xs = do {
    ASSERT(linear_combi_l_pre i A \<V> xs);
    WHILE\<^sub>T
      (\<lambda>(p, xs, err). xs \<noteq> [] \<and> \<not>is_cfailed err)
      (\<lambda>(p, xs, _). do {
         ASSERT(xs \<noteq> []);
         ASSERT(vars_llist p \<subseteq> \<V>);
         ((q\<^sub>0 :: llist_polynomial, i), xt) \<leftarrow> mop_list_pop_hd xs;
         if (i \<notin># dom_m A \<or> \<not>(vars_llist q\<^sub>0 \<subseteq> \<V>))
         then do {
           err \<leftarrow> check_linear_combi_l_dom_err q\<^sub>0 i;
           RETURN (p, (q\<^sub>0, i) # xt, error_msg i err)
         } else do {
           ASSERT(fmlookup A i \<noteq> None);
           let r = the (fmlookup A i);
           ASSERT(vars_llist r \<subseteq> \<V>);
           if q\<^sub>0 = [([], 1)]
           then do {
             pq \<leftarrow> add_poly_l p r;
             RETURN (pq, xt, CSUCCESS)
           }
           else do {
             q \<leftarrow> full_normalize_poly (q\<^sub>0);
             ASSERT(vars_llist q \<subseteq> \<V>);
             pq \<leftarrow> mult_poly_full q r;
             ASSERT(vars_llist pq \<subseteq> \<V>);
             pq \<leftarrow> add_poly_l p pq;
             RETURN (pq, xt, CSUCCESS)
          }
         }
      })
     ([], xs, CSUCCESS)
  }\<close>
proof -
  have H: \<open>(q\<^sub>0, ia) # tl ys = ys\<close> if \<open>hd ys = (q\<^sub>0, ia)\<close> \<open>ys \<noteq> []\<close>
    for q\<^sub>0 ia and ys :: \<open>(llist_polynomial \<times> nat) list\<close>
    using that by (cases ys) auto
  show ?thesis
    unfolding linear_combi_l_def mop_list_pop_hd_def
    apply (rule bind_cong[OF refl])
    apply (rule arg_cong2[where f = \<open>\<lambda>c b. WHILE\<^sub>T c b ([], xs, CSUCCESS)\<close>])
    subgoal by (rule refl)
    apply (intro ext)
    apply (clarsimp split!: prod.splits list.splits simp: H)
    apply (auto simp: H pw_eq_iff refine_pw_simps)
    done
qed

sepref_def linear_combi_l_impl
  is \<open>uncurry3 linear_combi_l\<close>
  :: \<open>si64_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a vars_assn\<^sup>k *\<^sub>a poly_input_assn\<^sup>d  \<rightarrow>\<^sub>a
  polynomial_assn \<times>\<^sub>a poly_input_assn \<times>\<^sub>a status_assn\<close>
  (* supply [[goals_limit=1, show_types]] *)
  supply [[goals_limit=1]]
  unfolding linear_combi_alt
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    in_dom_by_contains
    fmlookup'_def[symmetric]
    vars_llist_alt_def
    ls_emp
  by sepref

definition has_failed :: \<open>bool nres\<close> where
  \<open>has_failed = RES UNIV\<close>

lemma [sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0), uncurry0 has_failed)\<in>unit_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  apply sepref_to_hoare
  apply vcg
  apply (auto simp: ENTAILS_def entails_def sep_algebra_simps
    bool1_rel_def bool.rel_def in_br_conv)
  by (simp add: has_failed_def)

sepref_register linear_combi_l ::
  \<open>'a \<Rightarrow> (nat, llist_polynomial) f_map \<Rightarrow> string set \<Rightarrow> (llist_polynomial \<times> nat) list \<Rightarrow>
    (llist_polynomial \<times> (llist_polynomial \<times> nat) list \<times> string code_status) nres\<close>

declare linear_combi_l_impl.refine[sepref_fr_rules]

text \<open>No \<open>llvm_inline\<close> here: the constant appears as the \<open>afree\<close> argument of
  \<open>freeable_assn.cl_free\<close>, and inlining it there would break the code-equation
  lookup for the interpreted \<open>lincomb.cl_free\<close>.\<close>
definition poly_input_pair_free :: \<open>poly_conc \<times> 64 word \<Rightarrow> unit llM\<close>
  where [llvm_code]:
  \<open>poly_input_pair_free \<equiv> \<lambda>(pi, _). doM { poly.cl_free pi; Mreturn () }\<close>

lemma poly_input_pair_free_mk_free: \<open>MK_FREE poly_input_pair_assn poly_input_pair_free\<close>
  using mk_free_pair[OF poly.cl_assn_free mk_free_pure]
  unfolding poly_input_pair_free_def by simp

interpretation lincomb: freeable_assn poly_input_pair_assn poly_input_pair_free
  by unfold_locales (rule poly_input_pair_free_mk_free)

sepref_register check_linear_combi_l_pre_err
sepref_def check_linear_combi_l_impl
  is \<open>uncurry5 check_linear_combi_l\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a vars_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k *\<^sub>a
        (cl_assn' (polynomial_assn \<times>\<^sub>a si64_assn))\<^sup>d *\<^sub>a polynomial_assn\<^sup>k  \<rightarrow>\<^sub>a status_assn\<close>
  unfolding check_mult_l_def  check_linear_combi_l_def
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    in_dom_by_contains
    fmlookup'_def[symmetric]
    vars_llist_alt_def
    has_failed_def[symmetric]
    ls_emp ls_emp'
  by sepref

sepref_register is_cfailed is_Del

sepref_decl_intf ('k) acode_status is "('k) code_status"
sepref_decl_intf ('k, 'b, 'lbl) apac_step is "('k, 'b, 'lbl) pac_step"

sepref_register merge_cstatus full_normalize_poly new_var is_Add
find_theorems is_CL RETURN

sepref_register check_linear_combi_l ::
  \<open>llist_polynomial \<Rightarrow> (nat, llist_polynomial) f_map \<Rightarrow> string set \<Rightarrow> nat \<Rightarrow>
    (llist_polynomial \<times> nat) list \<Rightarrow> llist_polynomial \<Rightarrow> string code_status nres\<close>
sepref_register check_extension_l2 ::
  \<open>'a \<Rightarrow> (nat, 'v) f_map \<Rightarrow> string set \<Rightarrow> nat \<Rightarrow>
    string \<Rightarrow> llist_polynomial \<Rightarrow> string code_status nres\<close>

text \<open>Needed so monadify hoists the compound literal argument in
  \<open>add_poly_l [([COPY v], -1)] r\<close> (unregistered operations do not get their
  arguments flattened, and trans then stalls on the nested application).\<close>
sepref_register add_poly_l

definition check_extension_l2_cond :: \<open>nat \<Rightarrow> _\<close> where
  \<open>check_extension_l2_cond i A \<V> v = SPEC (\<lambda>b. b \<longrightarrow> fmlookup' i A = None \<and> v \<notin> \<V>)\<close>

definition check_extension_l2_cond2 :: \<open>nat \<Rightarrow> _\<close> where
  \<open>check_extension_l2_cond2 i A \<V> v = RETURN (fmlookup' i A = None \<and> v \<notin> \<V>)\<close>

lemma fmlookup'_None_by_contains:
  \<open>(fmlookup' i A = None) = (\<not> op_fmap_contains_key i A)\<close>
  unfolding op_fmap_contains_key_def fmlookup'_def
  by (auto simp: in_dom_m_lookup_iff)

text \<open>The fold towards \<^const>\<open>check_extension_l2_cond\<close> must match the form the
  \<open>SPEC\<close> body takes \<^emph>\<open>after\<close> \<open>in_dom_by_contains\<close> has fired (the definition in
  \<open>check_extension_l2\<close> is stated via \<open>\<notin># dom_m\<close>, the condition via \<open>fmlookup'\<close>).\<close>
lemma check_extension_l2_cond_alt:
  \<open>SPEC (\<lambda>b. b \<longrightarrow> \<not> op_fmap_contains_key i A \<and> v \<notin> \<V>) = check_extension_l2_cond i A \<V> v\<close>
  unfolding check_extension_l2_cond_def fmlookup'_None_by_contains ..

sepref_register check_extension_l2_cond ::
  \<open>nat \<Rightarrow> (nat, 'v) f_map \<Rightarrow> 'c set \<Rightarrow> 'c \<Rightarrow> bool nres\<close>

sepref_def check_extension_l2_cond2_impl
  is \<open>uncurry3 check_extension_l2_cond2\<close>
    :: \<open>si64_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a vars_assn\<^sup>k *\<^sub>a strl_assn'\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [[goals_limit=1]]
  unfolding check_extension_l2_cond2_def
    fmlookup'_None_by_contains
    not_not
  by sepref

lemma check_extension_l2_cond2_check_extension_l2_cond:
  \<open>(uncurry3 check_extension_l2_cond2, uncurry3 check_extension_l2_cond) \<in>
  (((nat_rel \<times>\<^sub>r Id) \<times>\<^sub>r Id) \<times>\<^sub>r Id) \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  by (auto intro!: RES_refine nres_relI frefI
    simp: check_extension_l2_cond_def check_extension_l2_cond2_def)

lemmas [sepref_fr_rules] =
  check_extension_l2_cond2_impl.refine[FCOMP check_extension_l2_cond2_check_extension_l2_cond]

lemma check_extension_l2_alt_def:
  \<open>check_extension_l2 spec A \<V> i v p' = do {
  b \<leftarrow> SPEC(\<lambda>b. b \<longrightarrow> i \<notin># dom_m A \<and> v \<notin> \<V>);
  if \<not>b
  then do {
    c \<leftarrow> check_extension_l_dom_err i;
    RETURN (error_msg i c)
  } else do {
      let p' = COPY p';
      let b = vars_llist p' \<subseteq> \<V>;
      if \<not>b
      then do {
        c \<leftarrow> check_extension_l_new_var_multiple_err v p';
        RETURN (error_msg i c)
      }
      else do {
         ASSERT(vars_llist p' \<subseteq> \<V>);
         p2 \<leftarrow> mult_poly_full p' p';
         ASSERT(vars_llist p2 \<subseteq> \<V>);
         let p' = map (\<lambda>(a,b). (a, -b)) p';
         ASSERT(vars_llist p' \<subseteq> \<V>);
         q \<leftarrow> add_poly_l p2 p';
         ASSERT(vars_llist q \<subseteq> \<V>);
         eq \<leftarrow> weak_equality_l q [];
         if eq then do {
           RETURN (CSUCCESS)
         } else do {
          c \<leftarrow> check_extension_l_side_cond_err v p' q;
          RETURN (error_msg i c)
        }
      }
    }
  }\<close>
  unfolding check_extension_l2_def COPY_def by simp

sepref_def check_extension_l_impl
  is \<open>uncurry5 check_extension_l2\<close>
    :: \<open>polynomial_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a vars_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k *\<^sub>a
    strl_assn'\<^sup>k *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a status_assn\<close>
  unfolding check_extension_l2_alt_def
    in_dom_by_contains
    fmlookup'_def[symmetric]
    not_not is_None_def
    uminus_poly_def[symmetric]
    check_extension_l2_cond_alt
    vars_llist_alt_def
  by sepref

lemma is_Mult_lastI:
  \<open>\<not> is_CL b \<Longrightarrow> \<not>is_Extension b \<Longrightarrow> is_Del b\<close>
  by (cases b) auto

definition step_id_bounded :: \<open>lpac_step_hol \<Rightarrow> bool\<close> where
  \<open>step_id_bounded st \<longleftrightarrow> (\<not>is_Del st \<longrightarrow> new_id st + 1 < max_snat 64)\<close>

definition PAC_checker_l_step_alt where
  \<open>PAC_checker_l_step_alt spec st' \<V> A st = (
    if is_CL st then doN {
      (srcs, ni, res) \<leftarrow> mop_dest_cl st;
      ASSERT (ni + 1 < max_snat 64);
      r \<leftarrow> full_normalize_poly res;
      eq \<leftarrow> check_linear_combi_l spec A \<V> ni srcs r;
      if \<not>is_cfailed eq then doN {
        let st'' = merge_cstatus st' eq;
        let A' = fmupd ni (BOX r) A;
        RETURN (st'', \<V>, A')
      }
      else RETURN (eq, \<V>, A)
    }
    else if is_Del st then doN {
      s1 \<leftarrow> mop_dest_ldel st;
      eq \<leftarrow> check_del_l spec A s1;
      if \<not>is_cfailed eq then doN {
        let st'' = merge_cstatus st' eq;
        let A' = fmdrop s1 A;
        RETURN (st'', \<V>, A')
      }
      else RETURN (eq, \<V>, A)
    }
    else doN {
      (ni, v, res) \<leftarrow> mop_dest_lextension st;
      ASSERT (ni + 1 < max_snat 64);
      r \<leftarrow> full_normalize_poly res;
      eq \<leftarrow> check_extension_l2 spec A \<V> ni v r;
      if \<not>is_cfailed eq then doN {
        r' \<leftarrow> add_poly_l [([COPY v], -1)] r;
        let \<V>' = insert v \<V>;
        let A' = fmupd ni (BOX r') A;
        RETURN (st', \<V>', A')
      }
      else RETURN (eq, \<V>, A)
    })\<close>

definition PAC_checker_l_step' where
  \<open>PAC_checker_l_step' a b c d = PAC_checker_l_step a (b, c, d)\<close>

lemma PAC_checker_l_step_alt_PAC_checker_l_step':
  \<open>step_id_bounded st \<Longrightarrow>
     PAC_checker_l_step_alt spec st' \<V> A st \<le> \<Down>Id (PAC_checker_l_step' spec st' \<V> A st)\<close>
  unfolding PAC_checker_l_step_alt_def PAC_checker_l_step'_def PAC_checker_l_step_def
    mop_dest_cl_def mop_dest_lextension_def mop_dest_ldel_def
    step_id_bounded_def BOX_def COPY_def
  apply (cases st)
  apply (auto simp: dest_cl_def dest_lextension_def dest_ldel_def Let_def
    pw_le_iff refine_pw_simps)
  done

lemma PAC_checker_l_step_fref:
  \<open>(uncurry4 PAC_checker_l_step_alt, uncurry4 PAC_checker_l_step')
    \<in> [\<lambda>((((_, _), _), _), st). step_id_bounded st]\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  using PAC_checker_l_step_alt_PAC_checker_l_step' by auto

lemma PAC_checker_l_step_tuple:
  \<open>PAC_checker_l_step a bcd e = (let (b, c, d) = bcd in PAC_checker_l_step' a b c d e)\<close>
  unfolding PAC_checker_l_step'_def by (auto split: prod.splits)

sepref_definition check_step_impl [llvm_code]
  is \<open>uncurry4 PAC_checker_l_step_alt\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a status_assn\<^sup>d *\<^sub>a vars_assn\<^sup>d *\<^sub>a polys_assn\<^sup>d *\<^sub>a lpac_step_assn\<^sup>d \<rightarrow>\<^sub>a
    status_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro] 
  unfolding PAC_checker_l_step_alt_def 
    pac_step.case_eq_if Let_def
     is_success_alt_def[symmetric]
    uminus_poly_def[symmetric]
    ls_emp ls_emp'
  by sepref

declare check_step_impl.refine[sepref_fr_rules]

lemmas PAC_checker_l_step'_hnr[sepref_fr_rules] =
  check_step_impl.refine[FCOMP PAC_checker_l_step_fref]

sepref_register PAC_checker_l_step' ::
  \<open>llist_polynomial \<Rightarrow> string code_status \<Rightarrow> string set \<Rightarrow> (nat, llist_polynomial) f_map \<Rightarrow>
    lpac_step_hol \<Rightarrow>
    (string code_status \<times> string set \<times> (nat, llist_polynomial) f_map) nres\<close>

definition PAC_checker_l' where
  \<open>PAC_checker_l' p \<V> A status steps = PAC_checker_l p (\<V>, A) status steps\<close>

lemma PAC_checker_l_alt_def:
  \<open>PAC_checker_l p \<V>A status steps =
    (let (\<V>, A) = \<V>A in PAC_checker_l' p \<V> A status steps)\<close>
  unfolding PAC_checker_l'_def by auto

definition PAC_checker_l_loop
  :: \<open>llist_polynomial \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> string code_status \<Rightarrow> lpac_step_hol list \<Rightarrow> _\<close>
  where \<open>PAC_checker_l_loop spec \<V> A b st = do {
    (S, _) \<leftarrow> WHILE\<^sub>T
       (\<lambda>((b, _), n). \<not>is_cfailed b \<and> n \<noteq> [])
       (\<lambda>((bA), n). do {
          ASSERT(n \<noteq> []);
          (nh, nt) \<leftarrow> mop_list_pop_hd n;
          ASSERT(step_id_bounded nh);
          S \<leftarrow> PAC_checker_l_step spec bA nh;
          RETURN (S, nt)
        })
      ((b, (\<V>, A)), st);
    RETURN S
  }\<close>

lemma PAC_checker_l_step_rel_id:
  \<open>(bA, bA') \<in> Id \<Longrightarrow> (st, st') \<in> Id \<Longrightarrow>
     PAC_checker_l_step spec bA st \<le> \<Down>Id (PAC_checker_l_step spec bA' st')\<close>
  by auto

lemma PAC_checker_l_loop_PAC_checker_l':
  assumes \<open>list_all step_id_bounded st\<close>
  shows \<open>PAC_checker_l_loop spec \<V> A b st \<le> \<Down>Id (PAC_checker_l' spec \<V> A b st)\<close>
  unfolding PAC_checker_l_loop_def PAC_checker_l'_def PAC_checker_l_def
    mop_list_pop_hd_def
  apply (simp add: ASSERT_dup)
  apply (rule refine_IdD)
  apply (refine_rcg
      WHILET_refine[where R = \<open>Id \<times>\<^sub>r {(n, n'). n' = n \<and> list_all step_id_bounded n}\<close>]
      PAC_checker_l_step_rel_id)
  using assms by (auto simp: neq_Nil_conv)

lemma PAC_checker_l_loop_fref:
  \<open>(uncurry4 PAC_checker_l_loop, uncurry4 PAC_checker_l')
    \<in> [\<lambda>((((_, _), _), _), st). list_all step_id_bounded st]\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  using PAC_checker_l_loop_PAC_checker_l' by auto

sepref_register PAC_checker_l' ::
  \<open>llist_polynomial \<Rightarrow> string set \<Rightarrow> (nat, llist_polynomial) f_map \<Rightarrow>
    string code_status \<Rightarrow> lpac_step_hol list \<Rightarrow>
    (string code_status \<times> string set \<times> (nat, llist_polynomial) f_map) nres\<close>

sepref_def PAC_checker_l_impl
  is \<open>uncurry4 PAC_checker_l_loop\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a vars_assn\<^sup>d *\<^sub>a polys_assn\<^sup>d *\<^sub>a status_assn\<^sup>d *\<^sub>a (cl_assn' lpac_step_assn)\<^sup>d \<rightarrow>\<^sub>a
     status_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro]
  unfolding PAC_checker_l_loop_def is_success_alt_def[symmetric] PAC_checker_l_step_tuple
    nres_bind_let_law[symmetric]
    ls_emp
  apply (subst nres_bind_let_law)
  by sepref

lemmas PAC_checker_l_hnr[sepref_fr_rules] =
  PAC_checker_l_impl.refine[FCOMP PAC_checker_l_loop_fref]

sepref_register upper_bound_on_dom op_fmap_empty

definition full_checker_l2
  :: \<open>llist_polynomial \<Rightarrow> (nat, llist_polynomial) fmap \<Rightarrow> (_, string, nat) pac_step list \<Rightarrow>
    (string code_status \<times> _) nres\<close>
where
  \<open>full_checker_l2 spec A st = do {
    ASSERT (list_all step_id_bounded st);
    spec' \<leftarrow> full_normalize_poly (COPY spec);
    (b, \<V>, A) \<leftarrow> remap_polys_l spec {} A;
    if is_cfailed b
    then do {
      mop_free spec;
      RETURN (b, \<V>, A)
    }
    else do {
      mop_free spec;
      PAC_checker_l spec' (\<V>, A) b st
    }
  }\<close>

sepref_register remap_polys_l
find_theorems full_checker_l2
sepref_def full_checker_l_impl
  is \<open>uncurry2 full_checker_l2\<close>
  :: \<open>polynomial_assn\<^sup>d *\<^sub>a polys_assn_input\<^sup>d *\<^sub>a (cl_assn' lpac_step_assn)\<^sup>d \<rightarrow>\<^sub>a
    status_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
  supply is_Mult_lastI[intro]
  unfolding full_checker_l2_def
    union_vars_poly_alt_def[symmetric]
    PAC_checker_l_alt_def
  supply [sepref_fr_rules] = strl.hs_empty_2pow14_hnr
  by sepref

export_llvm full_checker_l_impl

(* sepref_definition PAC_empty_impl
 *   is \<open>uncurry0 (RETURN fmempty)\<close>
 *   :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a polys_assn_input\<close>
 *   unfolding op_iam_fmap_empty_def[symmetric] pat_fmap_empty
 *   by sepref
 * 
 * sepref_definition empty_vars_impl
 *   is \<open>uncurry0 (RETURN {})\<close>
 *   :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a vars_assn\<close>
 *   unfolding hs.fold_custom_empty
 *   by sepref *)

end
