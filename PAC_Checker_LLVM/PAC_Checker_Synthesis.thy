(*
  File:         PAC_Checker_Synthesis.thy
  Author:       Mathias Fleury, Daniela Kaufmann, JKU
  Maintainer:   Mathias Fleury, JKU
*)
theory PAC_Checker_Synthesis
  imports PAC_Checker_Error
begin

section \<open>Code Synthesis of the Complete Checker\<close>

text \<open>We here combine refine the full checker, using the initialisation provided in another file and
adding more efficient data structures (mostly replacing the set of variables by a more efficient
hash map).\<close>

interpretation strl: hashset_env
  \<open>strl_assn'\<close> \<open>strl.cl_free\<close> \<open>strl.cl_copy\<close> \<open>strl.cl_eq\<close>
  \<open>fnv1a_of_strl\<close> \<open>fnv1a_of_strl_impl\<close>
  apply unfold_locales
  by (rule fnv1a_of_strl_hnr)

abbreviation vars_assn where
  \<open>vars_assn \<equiv> strl.hs_assn'\<close>

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

lemma vars_of_monom_in_alt_def2:
  \<open>vars_of_monom_in xs \<V> \<longleftrightarrow> fold (\<lambda>x b. b \<and> x \<in> \<V>) xs True\<close>
  apply (subst foldr_fold[symmetric])
  subgoal by auto
  subgoal by (induction xs) auto
  done

text \<open>We use our custom read only fold for copying lists (to avoid copying)\<close>
definition \<open>fold_inner \<V> \<equiv> \<lambda>b x. b \<and> x \<in> \<V>\<close>
sepref_def fold_inner_impl is \<open>uncurry2 (RETURN ooo fold_inner)\<close>
  :: \<open>vars_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a strl_assn'\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding fold_inner_def
  by sepref
    
definition \<open>vars_of_monom_in_impl xs \<V> \<equiv> cl_fold (fold_inner_impl \<V>) (xs, 1)\<close>

lemma fold_inner_step_rule:
  \<open>llvm_htriple
    ((bool1_assn b bi ** vars_assn \<V> vi) ** strl_assn' x xi)
    (fold_inner_impl vi bi xi)
    (\<lambda>r. (bool1_assn (fold_inner \<V> b x) r ** vars_assn \<V> vi) ** strl_assn' x xi)\<close>
  supply [vcg_rules] = hfref_htriple_k3[OF fold_inner_impl.refine]
  apply vcg
  unfolding ENTAILS_def
  by (auto simp: entails_def pure_def sep_algebra_simps)

lemmas vars_of_monom_walk_rule =
  cl_fold_rule[where R = \<open>\<lambda>b r. bool1_assn b r ** vars_assn \<V> vi\<close>
    and fa = \<open>fold_inner \<V>\<close> and A = strl_assn' for \<V> vi,
    OF fold_inner_step_rule]

lemma vars_of_monom_in_foldl:
  \<open>foldl (fold_inner \<V>) b xs = (b \<and> vars_of_monom_in xs \<V>)\<close>
  by (induction xs arbitrary: b) (auto simp: fold_inner_def)

lemma vars_of_monom_in_impl_hnr[sepref_fr_rules]:
  \<open>(uncurry vars_of_monom_in_impl, uncurry (RETURN oo vars_of_monom_in))
  \<in> monom_assn\<^sup>k *\<^sub>a vars_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding vars_of_monom_in_impl_def
  apply sepref_to_hoare
  supply [vcg_rules] = vars_of_monom_walk_rule
  supply [simp] = vars_of_monom_in_foldl bool1_rel_def bool.rel_def in_br_conv
    pure_def
  by vcg

lemma vars_of_poly_in_alt_def2:
  \<open>vars_of_poly_in xs \<V> \<longleftrightarrow> fold (\<lambda>(x, _) b. b \<and> vars_of_monom_in x \<V>) xs True\<close>
  apply (subst foldr_fold[symmetric])
  subgoal by auto
  subgoal by (induction xs) auto
  done

text \<open>Again, we can use our readonly cl_fold; the step of the outer walk is the
  monom walk (on the pair's first component), synthesized by sepref from the
  registered monom rule.\<close>
definition \<open>vars_of_poly_in_inner \<V> \<equiv> \<lambda>b (vs, _). b \<and> vars_of_monom_in vs \<V>\<close>

sepref_def vars_of_poly_in_inner_impl is \<open>uncurry2 (RETURN ooo vars_of_poly_in_inner)\<close>
  :: \<open>vars_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a monomial_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding vars_of_poly_in_inner_def
  by sepref

definition \<open>vars_of_poly_in_impl xs \<V> \<equiv> cl_fold (vars_of_poly_in_inner_impl \<V>) (xs, 1)\<close>

lemma vars_of_poly_in_inner_step_rule:
  \<open>llvm_htriple
    ((bool1_assn b bi ** vars_assn \<V> vi) ** monomial_assn x xi)
    (vars_of_poly_in_inner_impl vi bi xi)
    (\<lambda>r. (bool1_assn (vars_of_poly_in_inner \<V> b x) r ** vars_assn \<V> vi) ** monomial_assn x xi)\<close>
  supply [vcg_rules] = hfref_htriple_k3[OF vars_of_poly_in_inner_impl.refine]
  apply vcg
  unfolding ENTAILS_def
  by (auto simp: entails_def pure_def sep_algebra_simps)

lemmas vars_of_poly_walk_rule =
  cl_fold_rule[where R = \<open>\<lambda>b r. bool1_assn b r ** vars_assn \<V> vi\<close>
    and fa = \<open>vars_of_poly_in_inner \<V>\<close> and A = monomial_assn for \<V> vi,
    OF vars_of_poly_in_inner_step_rule]

lemma vars_of_poly_in_foldl:
  \<open>foldl (vars_of_poly_in_inner \<V>) b xs = (b \<and> vars_of_poly_in xs \<V>)\<close>
  apply (induction xs arbitrary: b)
  subgoal by simp
  subgoal for p xs b by (cases p) (auto simp: vars_of_poly_in_inner_def)
  done

lemma vars_of_poly_in_impl_hnr[sepref_fr_rules]:
  \<open>(uncurry vars_of_poly_in_impl, uncurry (RETURN oo vars_of_poly_in))
  \<in> polynomial_assn\<^sup>k *\<^sub>a vars_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding vars_of_poly_in_impl_def
  apply sepref_to_hoare
  supply [vcg_rules] = vars_of_poly_walk_rule
  supply [simp] = vars_of_poly_in_foldl bool1_rel_def bool.rel_def in_br_conv
    pure_def
  by vcg

definition union_vars_monom :: \<open>string list \<Rightarrow> string set \<Rightarrow> string set\<close> where
\<open>union_vars_monom xs \<V> = fold insert xs \<V>\<close>

definition \<open>insert' \<equiv> \<lambda>\<V> x. insert (COPY x) \<V>\<close>

sepref_def insert'_impl is \<open>uncurry (RETURN oo insert')\<close>
  :: \<open>vars_assn\<^sup>d *\<^sub>a strl_assn'\<^sup>k \<rightarrow>\<^sub>a vars_assn\<close>
  unfolding insert'_def
  by sepref
  
lemma union_vars_monom_alt: \<open>union_vars_monom xs \<V> = foldl insert' \<V> xs\<close>
  unfolding union_vars_monom_def insert'_def COPY_def
  by (auto simp: foldl_conv_fold)

definition \<open>union_vars_monom_impl xs \<V> \<equiv> cl_fold insert'_impl (xs, \<V>)\<close>

lemma insert'_step_rule: \<open>llvm_htriple
    (vars_assn \<V> \<V>i ** strl_assn' x xi)
    (insert'_impl \<V>i xi)
    (\<lambda>r. vars_assn (insert' \<V> x) r ** strl_assn' x xi)\<close>
  supply [vcg_rules] = hfref_htriple_d1_k2[OF insert'_impl.refine]
  by vcg

lemma union_vars_monom_impl_hnr[sepref_fr_rules]:
  \<open>(uncurry union_vars_monom_impl, uncurry (RETURN oo union_vars_monom))
  \<in> monom_assn\<^sup>k *\<^sub>a vars_assn\<^sup>d \<rightarrow>\<^sub>a vars_assn\<close>
  unfolding union_vars_monom_alt union_vars_monom_impl_def
  apply sepref_to_hoare
  supply [vcg_rules] = cl_fold_rule[where
    R = \<open>vars_assn\<close> and A = \<open>strl_assn'\<close>
    and f = \<open>insert'_impl\<close>
    and fa = \<open>insert'\<close>,
    OF insert'_step_rule]
  supply [simp] = pure_def
  by vcg

definition union_vars_poly :: \<open>llist_polynomial \<Rightarrow> string set \<Rightarrow> string set\<close> where
\<open>union_vars_poly xs \<V> = fold (\<lambda>(xs, _) \<V>. union_vars_monom xs \<V>) xs \<V>\<close>

definition \<open>union_vars_poly_inner \<equiv> \<lambda>\<V> (xs,_). union_vars_monom xs \<V>\<close>

sepref_register union_vars_monom
sepref_def union_vars_poly_inner_impl is \<open>uncurry (RETURN oo union_vars_poly_inner)\<close>
  :: \<open>vars_assn\<^sup>d *\<^sub>a monomial_assn\<^sup>k \<rightarrow>\<^sub>a vars_assn\<close>
  unfolding union_vars_poly_inner_def
  by sepref

lemma union_vars_poly_comp: \<open>union_vars_poly xs \<V> = foldl union_vars_poly_inner \<V> xs\<close>
  unfolding union_vars_poly_def union_vars_poly_inner_def
  by (simp add: foldl_conv_fold split_def)

definition \<open>union_vars_poly_impl xsi \<V>i \<equiv> cl_fold (union_vars_poly_inner_impl) (xsi, \<V>i)\<close>

lemma union_vars_poly_inner_step_rule: \<open>llvm_htriple
    (vars_assn \<V> \<V>i ** monomial_assn m mi)
    (union_vars_poly_inner_impl \<V>i mi)
    (\<lambda>r. vars_assn (union_vars_poly_inner \<V> m) r ** monomial_assn m mi)\<close>
  supply [vcg_rules] = hfref_htriple_d1_k2[OF union_vars_poly_inner_impl.refine]
  by vcg

lemma union_vars_poly_impl_hnr[sepref_fr_rules]:
  \<open>(uncurry union_vars_poly_impl, uncurry (RETURN oo union_vars_poly))
  \<in> polynomial_assn\<^sup>k *\<^sub>a vars_assn\<^sup>d \<rightarrow>\<^sub>a vars_assn\<close>
  unfolding union_vars_poly_comp union_vars_poly_impl_def
  apply sepref_to_hoare
  supply [vcg_rules] = cl_fold_rule[where
    R = \<open>vars_assn\<close> and A = \<open>monomial_assn\<close>
    and f = \<open>union_vars_poly_inner_impl\<close>
    and fa = \<open>union_vars_poly_inner\<close>,
    OF union_vars_poly_inner_step_rule]
  supply [simp] = pure_def
  by vcg

lemma union_vars_monom_alt_def:
  \<open>union_vars_monom xs \<V> = \<V> \<union> set xs\<close>
  unfolding union_vars_monom_def
  apply (subst foldr_fold[symmetric])
  subgoal for x y
    by (cases x; cases y) auto
  subgoal
    by (induction xs) auto
  done

lemma union_vars_poly_alt_def:
  \<open>union_vars_poly xs \<V> = \<V> \<union> vars_llist xs\<close>
  unfolding union_vars_poly_def
  apply (subst foldr_fold[symmetric])
  subgoal for x y
    by (cases x; cases y)
      (auto simp: union_vars_monom_alt_def)
  subgoal
    by (induction xs)
     (auto simp: vars_llist_def union_vars_monom_alt_def)
   done

sepref_def add_poly_l_impl is \<open>uncurry add_poly_l\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a polynomial_assn\<close>
  unfolding add_poly_l_def add_poly_l1_def add_poly_l2_def
    apl_cond_def apl_body_def apl2_body_def ls_emp term_order_rel_by_lt
  by sepref

lemma var_order_rel_alt: \<open>(x,y) \<in> var_order_rel \<equiv> x < y\<close>
  unfolding var_order_rel_def less_char_def p2rel_def
  by (simp add: List.lexordp_def less_char_def less_char_inst
    less_list_def)

definition \<open>mult_monoms_inner p\<^sub>0 q\<^sub>0 \<equiv> WHILEIT
    (\<lambda>(r,p,q). mult_monoms p\<^sub>0 q\<^sub>0 = r @ mult_monoms p q)
    (\<lambda>(r,p,q). p\<noteq>[] \<and> q\<noteq>[])
    (\<lambda>(r,p,q). doN {
      (x,p) \<leftarrow> mop_list_pop_hd p;
      (y,q) \<leftarrow> mop_list_pop_hd q;
      if x = y then
        RETURN (op_list_append r x, p, q)
      else if (x,y) \<in> var_order_rel then
        RETURN (op_list_append r x, p, y#q)
      else 
        RETURN  (op_list_append r y, x#p, q)
    }) ([], p\<^sub>0, q\<^sub>0)\<close>

abbreviation \<open>monom_assn_tail \<equiv> clt_assn' strl_assn'\<close>

sepref_def mult_monoms_inner_impl is \<open>uncurry mult_monoms_inner\<close>
  :: \<open>monom_assn\<^sup>d *\<^sub>a monom_assn\<^sup>d \<rightarrow>\<^sub>a (monom_assn_tail \<times>\<^sub>a monom_assn \<times>\<^sub>a monom_assn)\<close>
  unfolding mult_monoms_inner_def ls_emp var_order_rel_alt
  unfolding fold_clt_empty 
  by sepref

lemma mult_monoms_inner_refine:
  \<open>mult_monoms_inner p\<^sub>0 q\<^sub>0 \<le> SPEC (\<lambda>(r,p,q). mult_monoms p\<^sub>0 q\<^sub>0 = r @ mult_monoms p q \<and> (p = [] \<or> q = []))\<close>
  unfolding mult_monoms_inner_def
  apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>(r,p,q). length p + length q)"])
  apply clarsimp_all
  apply (metis list.exhaust_sel mult_monoms.simps(3))+
  done

definition \<open>mult_monoms_alt \<equiv> \<lambda>p q. doN { 
    (r,p',q') \<leftarrow> mult_monoms_inner (COPY p) (COPY q);
    let rcl = op_clt_to_cl r;
    RETURN (rcl @ p' @ q')
  }\<close>

lemma mult_monoms_Nil_right[simp]: \<open>mult_monoms p [] = p\<close>
  by (cases p) auto

lemma mult_monoms_Nil_left[simp]: \<open>mult_monoms [] q = q\<close>
  by (cases q) auto

lemma mult_monoms_alt_spec:
  \<open>mult_monoms_alt p q \<le> SPEC (\<lambda>r. r = mult_monoms p q)\<close>
  unfolding mult_monoms_alt_def op_clt_to_cl_def COPY_def
  by (refine_vcg mult_monoms_inner_refine[THEN order_trans]) auto

lemma mult_monoms_alt_refine:
  \<open>(uncurry mult_monoms_alt, uncurry (RETURN oo mult_monoms))
  \<in> Id \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (auto simp: RETURN_SPEC_conv)
  using mult_monoms_alt_spec by auto

sepref_register mult_monoms_inner
sepref_def mult_monoms_impl is \<open>uncurry mult_monoms_alt\<close>
  :: \<open>monom_assn\<^sup>k *\<^sub>a monom_assn\<^sup>k \<rightarrow>\<^sub>a monom_assn\<close>
  unfolding mult_monoms_alt_def
  by sepref

lemmas mult_monoms_hnr[sepref_fr_rules] =
  mult_monoms_impl.refine[FCOMP mult_monoms_alt_refine]

sepref_def mult_monomials_impl
  is \<open>uncurry (RETURN oo mult_monomials)\<close>
  :: \<open>monomial_assn\<^sup>k *\<^sub>a monomial_assn\<^sup>k \<rightarrow>\<^sub>a monomial_assn\<close>
  unfolding mult_monomials_def
  by sepref

type_synonym monomial_abs = \<open>(term_poly_list \<times> int)\<close>
abbreviation \<open>polynomial_assn_tail \<equiv> clt_assn' monomial_assn\<close>

definition mult_poly_raw_inner :: \<open>monomial_abs \<Rightarrow> llist_polynomial \<Rightarrow> monomial_abs \<Rightarrow> llist_polynomial\<close>
  where \<open>mult_poly_raw_inner pm b qm \<equiv> b @ [(mult_monomials pm qm)]\<close>

sepref_register mult_monomials
sepref_def mult_poly_raw_inner_impl is \<open>uncurry2 (RETURN ooo mult_poly_raw_inner)\<close>
  :: \<open>monomial_assn\<^sup>k *\<^sub>a polynomial_assn_tail\<^sup>d *\<^sub>a monomial_assn\<^sup>k \<rightarrow>\<^sub>a polynomial_assn_tail\<close>
  unfolding mult_poly_raw_inner_def
  by sepref

definition poly_row_fold :: \<open>monomial_abs \<Rightarrow> llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> llist_polynomial\<close>
  where \<open>poly_row_fold pm \<equiv> foldl (mult_poly_raw_inner pm)\<close>

sepref_register poly_row_fold
lemma poly_row_fold_hnr[sepref_fr_rules]:
  \<open>(uncurry2 (\<lambda>pmi. cl_fold' (mult_poly_raw_inner_impl pmi)),
    uncurry2 (RETURN ooo poly_row_fold))
    \<in> monomial_assn\<^sup>k *\<^sub>a polynomial_assn_tail\<^sup>d *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a polynomial_assn_tail\<close>
  unfolding poly_row_fold_def[abs_def]
  by (rule cl_fold_hfref_param[OF mult_poly_raw_inner_impl.refine])

definition mult_poly_raw_inner2 :: \<open>monomial_abs \<Rightarrow> llist_polynomial \<Rightarrow> llist_polynomial\<close>
  where \<open>mult_poly_raw_inner2 pm q \<equiv> poly_row_fold pm [] q\<close>

sepref_register mult_poly_raw_inner2
sepref_def mult_poly_raw_inner2_impl is \<open>uncurry (RETURN oo mult_poly_raw_inner2)\<close>
  :: \<open>monomial_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a polynomial_assn_tail\<close>
  unfolding mult_poly_raw_inner2_def
  unfolding fold_clt_empty
  by sepref

definition mult_poly_raw_outer :: \<open>llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> monomial_abs \<Rightarrow> llist_polynomial\<close>
  where \<open>mult_poly_raw_outer q b pm \<equiv> mult_poly_raw_inner2 pm q @ b\<close>

sepref_def mult_poly_raw_outer_impl is \<open>uncurry2 (RETURN ooo mult_poly_raw_outer)\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a polynomial_assn_tail\<^sup>d *\<^sub>a monomial_assn\<^sup>k \<rightarrow>\<^sub>a polynomial_assn_tail\<close>
  unfolding mult_poly_raw_outer_def
  by sepref

definition poly_mult_fold :: \<open>llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> llist_polynomial\<close>
  where \<open>poly_mult_fold q \<equiv> foldl (mult_poly_raw_outer q)\<close>

sepref_register poly_mult_fold
lemma poly_mult_fold_hnr[sepref_fr_rules]:
  \<open>(uncurry2 (\<lambda>qi. cl_fold' (mult_poly_raw_outer_impl qi)),
    uncurry2 (RETURN ooo poly_mult_fold))
    \<in> polynomial_assn\<^sup>k *\<^sub>a polynomial_assn_tail\<^sup>d *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a polynomial_assn_tail\<close>
  unfolding poly_mult_fold_def[abs_def]
  by (rule cl_fold_hfref_param[OF mult_poly_raw_outer_impl.refine])

lemma foldl_snoc_conv_map: \<open>foldl (\<lambda>b x. b @ [g x]) b\<^sub>0 xs = b\<^sub>0 @ map g xs\<close>
  by (induction xs arbitrary: b\<^sub>0) auto

lemma mult_poly_raw_inner2_map: \<open>mult_poly_raw_inner2 pm q = map (mult_monomials pm) q\<close>
  unfolding mult_poly_raw_inner2_def poly_row_fold_def mult_poly_raw_inner_def[abs_def]
  by (simp add: foldl_snoc_conv_map)

lemma mult_poly_raw_alt:
  \<open>mult_poly_raw p q = op_clt_to_cl (poly_mult_fold q [] p)\<close>
  unfolding mult_poly_raw_def poly_mult_fold_def mult_poly_raw_outer_def[abs_def]
    op_clt_to_cl_def
  by (simp add: mult_poly_raw_inner2_map)

sepref_def mult_poly_raw_impl
  is \<open>uncurry (RETURN oo mult_poly_raw)\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a polynomial_assn\<close>
  unfolding mult_poly_raw_alt
  unfolding fold_clt_empty
  by sepref

definition merge_coeffs_inner :: \<open>llist_polynomial \<Rightarrow> (llist_polynomial \<times> llist_polynomial) nres\<close> where
  \<open>merge_coeffs_inner p\<^sub>0 \<equiv> WHILEIT
  (\<lambda>(r,p). merge_coeffs p\<^sub>0 = r @ merge_coeffs p)
  (\<lambda>(r,p). p\<noteq>[])
  (\<lambda>(r,p). doN {
    ((xs,n),p) \<leftarrow> mop_list_pop_hd p;
    if p=[] then RETURN (op_list_append r (xs,n), p)
    else doN {
      ((ys,m),p) \<leftarrow> mop_list_pop_hd p;
      if xs = ys then doN {
        let s = n + m;
        if s = 0 then RETURN (r,p)
        else RETURN (r, (xs, s)#p)
      }
      else
        RETURN (op_list_append r (xs,n), (ys,m)#p)
    }
  }) ([], p\<^sub>0)\<close>

lemma merge_coeffs_inner_refine:
  \<open>merge_coeffs_inner p\<^sub>0 \<le> SPEC (\<lambda>(r,p). r = merge_coeffs p\<^sub>0 \<and> p = [])\<close>
  unfolding merge_coeffs_inner_def
  apply (refine_vcg WHILEIT_rule[where R=\<open>measure (\<lambda>(r,p). length p)\<close>])
  apply clarsimp_all
  apply (metis list.exhaust_sel merge_coeffs.simps(2) merge_coeffs.simps(3))+
  done

definition merge_coeffs_alt :: \<open>llist_polynomial \<Rightarrow> llist_polynomial nres\<close> where
  \<open>merge_coeffs_alt p \<equiv> doN {
    (r, p') \<leftarrow> merge_coeffs_inner p;
    let rcl = op_clt_to_cl r;
    RETURN (rcl @ p')
  }\<close>

lemma merge_coeffs_alt_spec:
  \<open>merge_coeffs_alt p \<le> SPEC (\<lambda>r. r = merge_coeffs p)\<close>
  unfolding merge_coeffs_alt_def op_clt_to_cl_def
  by (refine_vcg merge_coeffs_inner_refine[THEN order_trans]) auto

lemma merge_coeffs_alt_refine:
  \<open>(merge_coeffs_alt, RETURN o merge_coeffs) \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (auto simp: RETURN_SPEC_conv)
  using merge_coeffs_alt_spec by auto

sepref_register merge_coeffs_inner
sepref_def merge_coeffs_inner_impl is \<open>merge_coeffs_inner\<close>
  :: \<open>polynomial_assn\<^sup>d \<rightarrow>\<^sub>a (polynomial_assn_tail \<times>\<^sub>a polynomial_assn)\<close>
  unfolding merge_coeffs_inner_def ls_emp ls_emp'
  unfolding fold_clt_empty
  by sepref

sepref_def merge_coeffs_impl is \<open>merge_coeffs_alt\<close>
  :: \<open>polynomial_assn\<^sup>d \<rightarrow>\<^sub>a polynomial_assn\<close>
  unfolding merge_coeffs_alt_def
  by sepref

lemmas merge_coeffs_hnr[sepref_fr_rules] =
  merge_coeffs_impl.refine[FCOMP merge_coeffs_alt_refine]

sepref_def mult_poly_impl
  is \<open>uncurry mult_poly_full\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a polynomial_assn\<close>
  unfolding mult_poly_full_def normalize_poly_def
  by sepref

sepref_register \<open>(=) :: llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> bool\<close>
sepref_def weak_equality_l_impl
  is \<open>uncurry weak_equality_l\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding weak_equality_l_def
  by sepref
    
interpretation polys: boxed_copying_pmap
  \<open>polynomial_assn\<close> \<open>poly.cl_free\<close> \<open>poly.cl_copy\<close>
  apply unfold_locales
  subgoal by (rule poly.cl_assn_free)
  subgoal by (rule poly.cl_copy_hnr)
  done

abbreviation polys_assn where
  \<open>polys_assn \<equiv> hr_comp (hr_comp polys.bx.pmap_assn' opt_list_map_rel) map_fmap_rel\<close>

lemma polys_assn_intf[intf_of_assn]:
  \<open>intf_of_assn polys_assn TYPE((nat, (char list list \<times> int) list) f_map)\<close>
  by simp

(* These lemmas used to exist similarly in PAC_Map_Rel.thy *)
lemmas fmap_empty_hnr[sepref_fr_rules] =
  polys.bx.pmap_empty_hnr2[FCOMP fmempty_empty, unfolded op_fmap_empty_def[symmetric]]

lemmas fmap_delete_hnr[sepref_fr_rules] =
  polys.bx.pmap_delete_hnr2[FCOMP fmdrop_set_None]

lemmas fmap_update_hnr[sepref_fr_rules] =
  polys.bx.pmap_update_hnr2[FCOMP map_upd_fmupd]

lemmas fmap_lookup_hnr[sepref_fr_rules] =
  polys.bx.cpmap_lookup_hnr2[FCOMP op_map_lookup_fmlookup]

lemma polys_assn_free[sepref_frame_free_rules]:
  \<open>MK_FREE polys_assn polys.bx.pmap_free\<close>
  by (intro MK_FREE_hrcompI polys.bx.pmap_free_rule)

sepref_register fmlookup' :: \<open>'k \<Rightarrow> ('k, 'v) f_map \<Rightarrow> 'v option\<close>
sepref_register fmupd :: \<open>'k \<Rightarrow> 'v \<Rightarrow> ('k, 'v) f_map \<Rightarrow> ('k, 'v) f_map\<close>
sepref_register fmdrop :: \<open>'k \<Rightarrow> ('k, 'v) f_map \<Rightarrow> ('k, 'v) f_map\<close>

lemma map_fmap_contains_key:
  \<open>(uncurry (RETURN oo op_map_contains_key), uncurry (RETURN oo op_fmap_contains_key))
     \<in> Id \<times>\<^sub>r map_fmap_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: map_fmap_rel_def
      br_def in_fdom_alt fmap.Abs_fmap_inverse split: option.splits)

lemmas fmap_contains_key_hnr[sepref_fr_rules] =
  polys.bx.pmap_contains_key_hnr2[FCOMP map_fmap_contains_key]

lemma in_dom_by_contains: \<open>k\<in># dom_m A = op_fmap_contains_key k A\<close>
  unfolding op_fmap_contains_key_def by simp

sepref_decl_op fmap_the_lookup: \<open>\<lambda>k m. the (fmlookup' k m)\<close>
  :: \<open>[\<lambda>(k, m). k \<in># dom_m m]\<^sub>f K \<times>\<^sub>r \<langle>K,V\<rangle>fmap_rel \<rightarrow> V\<close>
  using fmap_rel_in_dom_iff by fastforce

(* lemma the_lookup_alt:
 *   \<open>the (fmlookup' k m) = UNBOX (op_fmap_the_lookup k m)\<close>
 *   by simp *)

lemma op_the_lookup_refine:
  \<open>(uncurry (RETURN oo op_map_the_lookup), uncurry (RETURN oo op_fmap_the_lookup))
     \<in> [\<lambda>(k, m). k \<in># dom_m m]\<^sub>f Id \<times>\<^sub>r map_fmap_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  by (auto simp: map_fmap_rel_def br_def in_fdom_alt fmap.Abs_fmap_inverse)

lemma map_fmap_rel_dom_iff[fcomp_prenorm_simps]:
  \<open>(m, fm) \<in> map_fmap_rel \<Longrightarrow> (\<exists>y. m k = Some y) \<longleftrightarrow> k \<in># dom_m fm\<close>
  by (auto simp: map_fmap_rel_def br_def in_fdom_alt fmap.Abs_fmap_inverse)

lemmas fmap_the_lookup_hnr[sepref_fr_rules] =
  polys.bx.cpmap_the_lookup_hnr2[FCOMP op_the_lookup_refine]

lemma pat_fmap_the_lookup[def_pat_rules]:
  \<open>the$(fmlookup'$k$m) \<equiv> UNBOX$(op_fmap_the_lookup$k$m)\<close>
  by (simp add: UNBOX_def)

sepref_def check_addition_l_impl
  is \<open>uncurry6 check_addition_l\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a vars_assn\<^sup>k *\<^sub>a
  si64_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k
  \<rightarrow>\<^sub>a status_assn\<close>
  supply [[goals_limit=1]]
  unfolding
    check_addition_l_def
    mult_poly_full_def
    vars_llist_alt_def
    fmlookup'_def[symmetric]
    in_dom_by_contains
    fold_clt_empty
  by sepref

sepref_def check_mult_l_impl
  is \<open>uncurry6 check_mult_l\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a vars_assn\<^sup>k *\<^sub>a
  si64_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k  \<rightarrow>\<^sub>a status_assn\<close>
  supply [[goals_limit=1]]
  unfolding check_mult_l_def
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    in_dom_by_contains
    fmlookup'_def[symmetric]
    vars_llist_alt_def
  by sepref

definition uminus_poly :: \<open>llist_polynomial \<Rightarrow> llist_polynomial\<close> where
  \<open>uminus_poly p = map (\<lambda>(a,b). (a,-b)) p\<close>

definition uminus_poly_nres :: \<open>llist_polynomial \<Rightarrow> llist_polynomial nres\<close> where
  \<open>uminus_poly_nres = REC\<^sub>T (\<lambda>f p.
    if p = [] then RETURN p
    else do {
      ((a,b), p) \<leftarrow> mop_list_pop_hd p;
      r \<leftarrow> f p; RETURN ((a, -b) # r)
    })\<close>

lemma uminus_poly_nres_spec: \<open>uminus_poly_nres p = RETURN (uminus_poly p)\<close>
  unfolding uminus_poly_nres_def uminus_poly_def
proof (induction p)
  case Nil
  show ?case by (subst RECT_unfold, refine_mono) auto
next
  case (Cons x p)
  show ?case
    apply (subst RECT_unfold, refine_mono)
    by (auto simp: Cons.IH split: prod.splits)
qed

sepref_register uminus_poly

sepref_def uminus_poly_impl is \<open>uminus_poly_nres\<close>
  :: \<open>polynomial_assn\<^sup>d \<rightarrow>\<^sub>a polynomial_assn\<close>
  unfolding uminus_poly_nres_def
  by sepref

lemma uminus_poly_fref:
  \<open>(uminus_poly_nres, RETURN o uminus_poly) \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: uminus_poly_nres_spec)

lemmas uminus_poly_hnr[sepref_fr_rules] =
  uminus_poly_impl.refine[FCOMP uminus_poly_fref]

definition mnml_eq :: \<open>monomial_abs \<Rightarrow> monomial_abs \<Rightarrow> bool\<close> where
  \<open>mnml_eq a b \<longleftrightarrow> a = b\<close>

sepref_register mnml_eq

lemma mnml_eq_op_hnr[sepref_fr_rules]:
  \<open>(uncurry mnml_eq_impl', uncurry (RETURN oo mnml_eq))
  \<in> monomial_assn\<^sup>k *\<^sub>a monomial_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding mnml_eq_def by (rule mnml_eq_hnr)

definition remove1_imp :: \<open>monomial_abs \<Rightarrow> llist_polynomial \<Rightarrow> llist_polynomial nres\<close> where
  \<open>remove1_imp r cs \<equiv> REC\<^sub>T (\<lambda>f cs.
    if cs=[] then RETURN cs
    else doN {
      (c,cs) \<leftarrow> mop_list_pop_hd cs;
      if mnml_eq c r then
        RETURN cs
      else doN {
        rs \<leftarrow> f cs;
        RETURN (c#rs) 
      }
    }
  ) cs\<close>

lemma remove1_imp_spec:
  \<open>remove1_imp r cs = RETURN (remove1 r cs)\<close>
  unfolding remove1_imp_def
proof (induction cs)
  case Nil
  show ?case by (subst RECT_unfold, refine_mono) auto
next
  case (Cons c cs)
  show ?case
    apply (subst RECT_unfold, refine_mono)
    by (auto simp: mop_list_pop_hd_def mnml_eq_def Cons.IH pw_eq_iff refine_pw_simps)
qed

lemma remove1_imp_correct:
  \<open>(RETURN oo remove1) = remove1_imp\<close>
  by (intro ext) (simp add: remove1_imp_spec)

sepref_def remove1_impl is \<open>uncurry (RETURN oo remove1)\<close>
  :: \<open>monomial_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>d\<rightarrow>\<^sub>a polynomial_assn\<close>
  unfolding remove1_imp_correct remove1_imp_def ls_emp
  by sepref

(* TODO: check if we could also make the string destructively alternatively *)
definition check_extension_l_alt where
  \<open>check_extension_l_alt spec A \<V> i v p = do {
    let b = i \<notin># dom_m A \<and> v \<notin> \<V> \<and> ([COPY v], -1) \<in> set p;
    if \<not>b
    then do {
      c \<leftarrow> check_extension_l_dom_err i;
      RETURN (error_msg i c)
    } else do {
        let p' = remove1 ([COPY v], -1) (COPY p);
        let b = vars_llist p' \<subseteq> \<V>;
        if \<not>b
        then do {
          c \<leftarrow> check_extension_l_new_var_multiple_err v p';
          RETURN (error_msg i c)
        }
        else do {
           p2 \<leftarrow> mult_poly_full p' p';
           let p' = map (\<lambda>(a,b). (a, -b)) p';
           q \<leftarrow> add_poly_l p2 p';
           eq \<leftarrow> weak_equality_l q [];
           if eq then do {
             RETURN (CSUCCESS)
           } else do {
            c \<leftarrow> check_extension_l_side_cond_err v p p' q;
            RETURN (error_msg i c)
          }
        }
      }
    }\<close>

lemma check_extension_l_refine:
  \<open>(uncurry5 check_extension_l_alt, uncurry5 check_extension_l)
  \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding check_extension_l_def COPY_def check_extension_l_alt_def
  by auto

sepref_register remove1_imp mult_poly_full weak_equality_l check_extension_l_side_cond_err
  error_msg
sepref_def check_extension_l_impl
  is \<open>uncurry5 check_extension_l_alt\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a vars_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k *\<^sub>a strl_assn'\<^sup>k *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a
     status_assn\<close>
  (* supply [[show_types]] *)
  supply [[goals_limit=1]]
  unfolding check_extension_l_alt_def
    fmlookup'_def[symmetric]
    in_dom_by_contains
    vars_llist_alt_def
    uminus_poly_def[symmetric]
  by sepref

lemmas check_extension_l_hnr[sepref_fr_rules] =
  check_extension_l_impl.refine[FCOMP check_extension_l_refine]

sepref_def check_del_l_impl
  is \<open>uncurry2 check_del_l\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k \<rightarrow>\<^sub>a status_assn\<close>
  supply [[goals_limit=1]]
  unfolding check_del_l_def
    in_dom_by_contains
    fmlookup'_def[symmetric]
  by sepref

abbreviation pac_step_rel where
  \<open>pac_step_rel \<equiv> p2rel (\<langle>Id, \<langle>Id\<rangle>list_rel, Id\<rangle> pac_step_rel_raw)\<close>

sepref_register PAC_Polynomials_Operations.normalize_poly
  pac_src1 pac_src2 new_id pac_mult case_pac_step
sepref_register check_mult_l ::
  \<open>llist_polynomial \<Rightarrow> (nat, llist_polynomial) f_map \<Rightarrow> string set \<Rightarrow> nat \<Rightarrow>
    llist_polynomial \<Rightarrow> nat \<Rightarrow> llist_polynomial \<Rightarrow> string code_status nres\<close>
sepref_register check_addition_l ::
  \<open>llist_polynomial \<Rightarrow> (nat, llist_polynomial) f_map \<Rightarrow> string set \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> llist_polynomial \<Rightarrow> string code_status nres\<close>
sepref_register check_del_l
sepref_register check_extension_l ::
  \<open>'a \<Rightarrow> (nat, 'v) f_map \<Rightarrow> string set \<Rightarrow> nat \<Rightarrow>
    string \<Rightarrow> llist_polynomial \<Rightarrow> string code_status nres\<close>

lemma is_Mult_lastI:
  \<open>\<not> is_Add b \<Longrightarrow> \<not>is_Mult b \<Longrightarrow> \<not>is_Extension b \<Longrightarrow> is_Del b\<close>
  by (cases b) auto

sepref_register is_cfailed is_Del is_Mult is_Extension

definition PAC_checker_l_step' ::  _ where
  \<open>PAC_checker_l_step' a b c d = PAC_checker_l_step a (b, c, d)\<close>

lemma PAC_checker_l_step_alt_def:
  \<open>PAC_checker_l_step a bcd e = (let (b,c,d) = bcd in PAC_checker_l_step' a b c d e)\<close>
  unfolding PAC_checker_l_step'_def by auto

definition step_id_bounded :: \<open>(llist_polynomial, string, nat) pac_step \<Rightarrow> bool\<close> where
  \<open>step_id_bounded st \<longleftrightarrow> (\<not>is_Del st \<longrightarrow> new_id st + 1 < max_snat 64)\<close>

term fmupd
definition PAC_checker_l_step_mop :: _ where
  \<open>PAC_checker_l_step_mop spec st' \<V> A st = (
    if is_Add st then doN {
      (s1, s2, ni, res) \<leftarrow> mop_dest_add st;
      ASSERT (ni + 1 < max_snat 64);
      r \<leftarrow> full_normalize_poly res;
      eq \<leftarrow> check_addition_l spec A \<V> s1 s2 ni r;
      if \<not>is_cfailed eq then doN {
        let st'' = merge_cstatus st' eq;
        let A' = fmupd ni (BOX r) A;
        RETURN (st'', \<V>, A')
      }
      else RETURN (eq, \<V>, A)
    }
    else if is_Mult st then doN {
      (s1, mp, ni, res) \<leftarrow> mop_dest_mult st;
      ASSERT (ni + 1 < max_snat 64);
      r \<leftarrow> full_normalize_poly res;
      q \<leftarrow> full_normalize_poly mp;
      eq \<leftarrow> check_mult_l spec A \<V> s1 q ni r;
      if \<not>is_cfailed eq then doN {   
        let st'' = merge_cstatus st' eq;
        let A' = fmupd ni (BOX r) A;
        RETURN (st'', \<V>, A')
      }
      else
        RETURN (eq, \<V>, A)
    }
    else if is_Extension st then doN {
      (ni, v, res) \<leftarrow> mop_dest_extension st;
      ASSERT (ni + 1 < max_snat 64);
      r \<leftarrow> full_normalize_poly (([COPY v], -1) # res);
      eq \<leftarrow> check_extension_l spec A \<V> ni v r;
      if \<not>is_cfailed eq then doN {
        let \<V>' = insert v \<V>;
        let A' = fmupd ni (BOX r) A;
        RETURN (st', \<V>', A')
      }
      else RETURN (eq, \<V>, A)
    }
    else do {
      s1 \<leftarrow> mop_dest_del st;
      eq \<leftarrow> check_del_l spec A s1;
      if \<not>is_cfailed eq
      then doN {
        let st'' = merge_cstatus st' eq;
        let A' = fmdrop s1 A;
        RETURN (st'', \<V>, A')
      }
      else RETURN (eq, \<V>, A)
    })\<close>

lemma PAC_checker_l_step_mop_PAC_checker_l_step':
  \<open>step_id_bounded st \<Longrightarrow>
     PAC_checker_l_step_mop spec st' \<V> A st \<le> \<Down>Id (PAC_checker_l_step' spec st' \<V> A st)\<close>
  unfolding PAC_checker_l_step_mop_def PAC_checker_l_step'_def PAC_checker_l_step_def
    mop_dest_add_def mop_dest_mult_def mop_dest_extension_def mop_dest_del_def
    step_id_bounded_def BOX_def
  apply (cases st)
  apply (auto simp: dest_add_def dest_mult_def dest_extension_def dest_del_def Let_def)
  apply (metis (no_types, lifting) ext order_refl pac_step.sel(5))
  apply (metis (no_types, lifting) bind_cong order_refl pac_step.sel(6))
  apply (metis (lifting) ext order_refl pac_step.sel(12,7))
  apply (metis (no_types, lifting) ext dual_order.refl pac_step.sel(3))
  done

lemma PAC_checker_l_step_mop_fref:
  \<open>(uncurry4 PAC_checker_l_step_mop, uncurry4 PAC_checker_l_step')
    \<in> [\<lambda>((((_, _), _), _), st). step_id_bounded st]\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  using PAC_checker_l_step_mop_PAC_checker_l_step' by auto

sepref_register PAC_checker_l_step_mop ::
  \<open>llist_polynomial \<Rightarrow> string code_status \<Rightarrow> string set \<Rightarrow> (nat, llist_polynomial) f_map \<Rightarrow>
    (llist_polynomial, string, nat) pac_step \<Rightarrow>
    (string code_status \<times> string set \<times> (nat, llist_polynomial) f_map) nres\<close>

sepref_register PAC_checker_l_step' ::
  \<open>llist_polynomial \<Rightarrow> string code_status \<Rightarrow> string set \<Rightarrow> (nat, llist_polynomial) f_map \<Rightarrow>
    (llist_polynomial, string, nat) pac_step \<Rightarrow>
    (string code_status \<times> string set \<times> (nat, llist_polynomial) f_map) nres\<close>

sepref_register merge_cstatus full_normalize_poly new_var is_Add
sepref_def check_step_impl
  is \<open>uncurry4 PAC_checker_l_step_mop\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a status_assn\<^sup>d *\<^sub>a vars_assn\<^sup>d *\<^sub>a polys_assn\<^sup>d *\<^sub>a pac_step_assn\<^sup>d
  \<rightarrow>\<^sub>a status_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]]
  unfolding PAC_checker_l_step_mop_def
     is_success_alt_def[symmetric]
    uminus_poly_def[symmetric]
  by sepref

lemmas PAC_checker_l_step_mop_hnr[sepref_fr_rules] =
  check_step_impl.refine[FCOMP PAC_checker_l_step_mop_fref]

definition PAC_checker_l_alt
  :: \<open>llist_polynomial \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> string code_status \<Rightarrow> pac_step_hol list \<Rightarrow> _\<close>
  where \<open>PAC_checker_l_alt spec \<V> A b st = do {
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

definition PAC_checker_l' where
  \<open>PAC_checker_l' p \<V> A status steps = PAC_checker_l p (\<V>, A) status steps\<close>

lemma ASSERT_dup: \<open>ASSERT P \<bind> (\<lambda>_. ASSERT P \<bind> f) = ASSERT P \<bind> f\<close>
  by (auto simp: pw_eq_iff refine_pw_simps)

lemma PAC_checker_l_step_rel_id:
  \<open>(bA, bA') \<in> Id \<Longrightarrow> (st, st') \<in> Id \<Longrightarrow>
     PAC_checker_l_step spec bA st \<le> \<Down>Id (PAC_checker_l_step spec bA' st')\<close>
  by auto

lemma PAC_checker_l_alt_PAC_checker_l':
  assumes \<open>list_all step_id_bounded st\<close>
  shows \<open>PAC_checker_l_alt spec \<V> A b st \<le> \<Down>Id (PAC_checker_l' spec \<V> A b st)\<close>
  unfolding PAC_checker_l_alt_def PAC_checker_l'_def PAC_checker_l_def
    mop_list_pop_hd_def
  apply (simp add: ASSERT_dup)
  apply (rule refine_IdD)
  apply (refine_rcg
      WHILET_refine[where R = \<open>Id \<times>\<^sub>r {(n, n'). n' = n \<and> list_all step_id_bounded n}\<close>]
      PAC_checker_l_step_rel_id)
  using assms by (auto simp: neq_Nil_conv)

lemma PAC_checker_l_alt_fref:
  \<open>(uncurry4 PAC_checker_l_alt, uncurry4 PAC_checker_l')
    \<in> [\<lambda>((((_, _), _), _), st). list_all step_id_bounded st]\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  using PAC_checker_l_alt_PAC_checker_l' by auto

lemma PAC_checker_l_alt2:
  \<open>PAC_checker_l p \<V>A status steps =
    (let (\<V>, A) = \<V>A in PAC_checker_l' p \<V> A status steps)\<close>
  unfolding PAC_checker_l'_def by auto

sepref_register PAC_checker_l' ::
  \<open>llist_polynomial \<Rightarrow> string set \<Rightarrow> (nat, llist_polynomial) f_map \<Rightarrow>
    string code_status \<Rightarrow> (llist_polynomial, string, nat) pac_step list \<Rightarrow>
    (string code_status \<times> string set \<times> (nat, llist_polynomial) f_map) nres\<close>

sepref_def PAC_checker_l_impl
  is \<open>uncurry4 PAC_checker_l_alt\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a vars_assn\<^sup>d *\<^sub>a polys_assn\<^sup>d *\<^sub>a status_assn \<^sup>d *\<^sub>a (cl_assn' pac_step_assn)\<^sup>d \<rightarrow>\<^sub>a
     status_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
  unfolding is_success_alt_def[symmetric] PAC_checker_l_step_alt_def
    nres_bind_let_law[symmetric] ls_emp
    PAC_checker_l_alt_def
  apply (subst nres_bind_let_law)
  by sepref

lemmas PAC_checker_l_hnr[sepref_fr_rules] =
  PAC_checker_l_impl.refine[FCOMP PAC_checker_l_alt_fref]

lemma max_snat_val: \<open>max_snat 64 - 1 = 9223372036854775807\<close>
  unfolding max_snat_def by auto 

(* abbreviation polys_assn_input where
 *   \<open>polys_assn_input \<equiv> iam_fmap_assn nat_assn poly_assn\<close> *)
abbreviation \<open>polys_assn_input \<equiv> polys_assn\<close>

sepref_register upper_bound_on_dom :: \<open>('k, 'v) f_map \<Rightarrow> 'k nres\<close>
sepref_register op_fmap_empty :: \<open>('k, 'v) f_map\<close>

lemma map_fmap_dom_ub:
  \<open>(op_map_dom_ub, upper_bound_on_dom) \<in> map_fmap_rel \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: op_map_dom_ub_def upper_bound_on_dom_def pw_le_iff refine_pw_simps
      dom_def map_fmap_rel_dom_iff)

lemmas upper_bound_on_dom_hnr[sepref_fr_rules] =
  polys.bx.pmap_len_hnr2[FCOMP map_fmap_dom_ub]

lemma nfoldli_body_cong:
  assumes \<open>\<And>x s. x \<in> set l \<Longrightarrow> f x s = g x s\<close>
  shows \<open>nfoldli l c f s = nfoldli l c g s\<close>
  using assms apply (induction l arbitrary: s)
  by (auto intro: bind_cong)

text \<open>Inserting the update-bound assertion is invisible where the loop bounds hold
  (\<open>i\<close> below the domain bound \<open>n\<close>, \<open>n\<close> below \<open>max_snat 64 - 1\<close>).\<close>
lemma ASSERT_insert_bound:
  assumes \<open>i < n\<close> \<open>n < max_snat 64 - Suc 0\<close>
  shows \<open>do {ASSERT (Suc i < max_snat 64); m} = (m :: _ nres)\<close>
proof -
  from assms have \<open>Suc i < max_snat 64\<close> by linarith
  then show ?thesis by simp
qed

lemma remap_polys_l2_alt:
  \<open>remap_polys_l2 spec = (\<lambda>\<V> A. do{
   n \<leftarrow> upper_bound_on_dom A;
   b \<leftarrow> RETURN (n \<ge> max_snat 64 - 1);
   if b
   then do {
     c \<leftarrow> remap_polys_l_dom_err;
     mop_free A;
     RETURN (error_msg (0 ::nat) c, \<V>, fmempty)
   }
   else do {
       (b, \<V>, A') \<leftarrow> nfoldli ([0..<n]) (\<lambda>_. True)
       (\<lambda>i (b, \<V>, A').
          if i \<in># dom_m A
          then do {
            ASSERT(fmlookup A i \<noteq> None);
            p \<leftarrow> full_normalize_poly (the (fmlookup A i));
            eq \<leftarrow> weak_equality_l p spec;
            \<V> \<leftarrow> RETURN (\<V> \<union> vars_llist (the (fmlookup A i)));
            ASSERT(i + 1 < max_snat 64);
            RETURN(b \<or> eq, \<V>, fmupd i (BOX p) A')
          } else RETURN (b, \<V>, A')
        )
       (False, \<V>, fmempty);
     mop_free A;
     RETURN (if b then CFOUND else CSUCCESS, \<V>, A')
    }
 })\<close>
  unfolding remap_polys_l2_def mop_free_def
  apply (intro ext)
  apply (simp only: nres_monad1)
  apply (rule bind_cong[OF refl])
  apply (rule if_cong[OF refl refl])
  apply (rule bind_cong[OF _ refl])
  apply (rule nfoldli_body_cong)
  apply (auto simp: BOX_def not_le ASSERT_insert_bound split: prod.splits
      intro!: bind_cong[OF refl])
  done

sepref_def remap_polys_l_impl
  is \<open>uncurry2 remap_polys_l2\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a vars_assn\<^sup>d *\<^sub>a polys_assn_input\<^sup>d \<rightarrow>\<^sub>a
    status_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
  supply is_Mult_lastI[intro] indom_mI[dest]
  unfolding remap_polys_l2_alt op_fmap_empty_def[symmetric] while_eq_nfoldli[symmetric]
    while_upt_while_direct max_snat_val
    in_dom_by_contains
    fmlookup'_def[symmetric]
    union_vars_poly_alt_def[symmetric]
  apply (subst while_upt_while_direct)
  apply simp
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  (* supply [[show_types]] *)
  by sepref

lemma remap_polys_l2_remap_polys_l:
  \<open>(uncurry2 remap_polys_l2, uncurry2 remap_polys_l) \<in> (Id \<times>\<^sub>r \<langle>Id\<rangle>set_rel) \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI fun_relI nres_relI)
  using remap_polys_l2_remap_polys_l by auto

lemma [sepref_fr_rules]:
  \<open>(uncurry2 remap_polys_l_impl, uncurry2 remap_polys_l)
  \<in> polynomial_assn\<^sup>k *\<^sub>a vars_assn\<^sup>d *\<^sub>a polys_assn_input\<^sup>d \<rightarrow>\<^sub>a
       status_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
   using hfcomp_tcomp_pre[OF remap_polys_l2_remap_polys_l remap_polys_l_impl.refine]
   by (auto simp: hrp_comp_def hfprod_def)

sepref_register remap_polys_l ::
  \<open>llist_polynomial \<Rightarrow> string set \<Rightarrow> (nat, llist_polynomial) f_map \<Rightarrow>
    (string code_status \<times> string set \<times> (nat, llist_polynomial) f_map) nres\<close>

lemma full_checker_alt:
  \<open>full_checker_l spec A st = do {
    spec' \<leftarrow> full_normalize_poly (COPY spec);
    (b, \<V>, A) \<leftarrow> remap_polys_l spec' {} A;
    if is_cfailed b
    then RETURN (b, \<V>, A)
    else do {
      let \<V> = \<V> \<union> vars_llist spec;
      PAC_checker_l spec' (\<V>, A) b st
    }
  }\<close>
  unfolding full_checker_l_def by simp

definition full_checker_l_alt where
  \<open>full_checker_l_alt spec A st = do {
    ASSERT (list_all step_id_bounded st);
    spec' \<leftarrow> full_normalize_poly (COPY spec);
    (b, \<V>, A) \<leftarrow> remap_polys_l spec' {} A;
    if is_cfailed b
    then do {
      mop_free spec;
      RETURN (b, \<V>, A)
    }
    else do {
      let \<V> = \<V> \<union> vars_llist spec;
      mop_free spec;
      PAC_checker_l spec' (\<V>, A) b st
    }
  }\<close>

lemma full_checker_l_alt_full_checker_l:
  \<open>list_all step_id_bounded st \<Longrightarrow>
    full_checker_l_alt spec A st \<le> \<Down>Id (full_checker_l spec A st)\<close>
  unfolding full_checker_l_alt_def full_checker_alt mop_free_def
  apply (simp only: nres_monad1 Let_def)
  by (auto intro!: ASSERT_leI)

lemma full_checker_l_alt_fref:
  \<open>(uncurry2 full_checker_l_alt, uncurry2 full_checker_l)
    \<in> [\<lambda>((_, _), st). list_all step_id_bounded st]\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  using full_checker_l_alt_full_checker_l by auto

term union_vars_poly
declare strl.hs_empty_2pow14_def[llvm_code]
sepref_register union_vars_poly 
sepref_def full_checker_l_impl
  is \<open>uncurry2 full_checker_l_alt\<close>
  :: \<open>polynomial_assn\<^sup>d *\<^sub>a polys_assn_input\<^sup>d *\<^sub>a (cl_assn' pac_step_assn)\<^sup>d \<rightarrow>\<^sub>a
    status_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
  supply is_Mult_lastI[intro]
  unfolding full_checker_l_alt_def
    union_vars_poly_alt_def[symmetric]
    PAC_checker_l_alt2
  supply [sepref_fr_rules] = strl.hs_empty_2pow14_hnr
  by sepref

section \<open>Correctness theorem\<close>
(* TODO: Correctness theorem must assume precondition of step_id_bounded *)

(* context poly_embed
 * begin
 * 
 * definition full_poly_assn where
 *   \<open>full_poly_assn = hr_comp polynomial_assn (fully_unsorted_poly_rel O mset_poly_rel)\<close>
 * 
 * definition full_poly_input_assn where
 *   \<open>full_poly_input_assn = hr_comp
 *         (hr_comp polys_assn_input
 *           (\<langle>nat_rel, fully_unsorted_poly_rel O mset_poly_rel\<rangle>fmap_rel))
 *         polys_rel\<close>
 * 
 * definition fully_pac_assn where
 *   \<open>fully_pac_assn = (list_assn
 *         (hr_comp (pac_step_rel_assn si64_assn polynomial_assn strl_assn')
 *           (p2rel
 *             (\<langle>nat_rel,
 *              fully_unsorted_poly_rel O
 *              mset_poly_rel, var_rel\<rangle>pac_step_rel_raw))))\<close>
 * 
 * definition code_status_assn where
 *   \<open>code_status_assn = hr_comp (status_assn raw_string_assn)
 *                             code_status_status_rel\<close>
 * 
 * definition full_vars_assn where
 *   \<open>full_vars_assn = hr_comp (hs.assn string_assn)
 *                               (\<langle>var_rel\<rangle>set_rel)\<close>
 * 
 * lemma polys_rel_full_polys_rel:
 *   \<open>polys_rel_full = Id \<times>\<^sub>r polys_rel\<close>
 *   by (auto simp: polys_rel_full_def)
 * 
 * definition full_polys_assn :: \<open>_\<close> where
 * \<open>full_polys_assn = hr_comp (hr_comp polys_assn
 *                               (\<langle>nat_rel,
 *                                sorted_poly_rel O mset_poly_rel\<rangle>fmap_rel))
 *                             polys_rel\<close> *)

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

(* lemma PAC_full_correctness: (\* \htmllink{PAC-full-correctness} *\)
 *   \<open>(uncurry2 full_checker_l_impl,
 *      uncurry2 (\<lambda>spec A _. PAC_checker_specification spec A))
 *     \<in> (full_poly_assn)\<^sup>k *\<^sub>a (full_poly_input_assn)\<^sup>d *\<^sub>a (fully_pac_assn)\<^sup>k \<rightarrow>\<^sub>a hr_comp
 *       (code_status_assn \<times>\<^sub>a full_vars_assn \<times>\<^sub>a hr_comp polys_assn
 *                               (\<langle>nat_rel, sorted_poly_rel O mset_poly_rel\<rangle>fmap_rel))
 *                             {((st, G), st', G').
 *                              st = st' \<and> (st \<noteq> FAILED \<longrightarrow> (G, G') \<in> Id \<times>\<^sub>r polys_rel)}\<close>
 *   using
 *     full_checker_l_impl.refine[FCOMP full_checker_l_full_checker',
 *       FCOMP full_checker_spec',
 *       unfolded full_poly_assn_def[symmetric]
 *         full_poly_input_assn_def[symmetric]
 *         fully_pac_assn_def[symmetric]
 *         code_status_assn_def[symmetric]
 *         full_vars_assn_def[symmetric]
 *         polys_rel_full_polys_rel
 *         hr_comp_prod_conv
 *         full_polys_assn_def[symmetric]]
 *       hr_comp_Id2
 *    by auto *)

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

(* end *)

(* definition \<phi> :: \<open>string \<Rightarrow> nat\<close> where
 *   \<open>\<phi> = (SOME \<phi>. bij \<phi>)\<close>
 * 
 * lemma bij_\<phi>: \<open>bij \<phi>\<close>
 *   using someI[of \<open>\<lambda>\<phi> :: string \<Rightarrow> nat. bij \<phi>\<close>]
 *   unfolding \<phi>_def[symmetric]
 *   using poly_embed_EX
 *   by auto
 * 
 * global_interpretation PAC: poly_embed where
 *   \<phi> = \<phi>
 *   apply standard
 *   apply (use bij_\<phi> in \<open>auto simp: bij_def\<close>)
 *   done *)


(* text \<open>The full correctness theorem is @{thm PAC.PAC_full_correctness}.\<close> *)

end
