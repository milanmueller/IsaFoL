theory LPAC_Error
  imports LPAC_Checker LPAC_Version
    LPAC_Checker_Init
    More_Loops
    PAC_Checker_Relation
    PAC_Checker_Synthesis
    LPAC_Efficient_Checker_Refinement
    LLVM_Polynomials_Array
begin
hide_fact (open) PAC_Checker.PAC_checker_l_def
hide_const (open) PAC_Checker.PAC_checker_l

definition show_bool :: \<open>bool \<Rightarrow> string\<close> where
  \<open>show_bool b \<equiv> if b then cl_to_clt ''true'' else cl_to_clt ''false''\<close>

sepref_def show_bool_impl is \<open>RETURN o show_bool\<close>
  :: \<open>bool1_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding show_bool_def
  by sepref

definition check_linear_combi_l_pre_err_imp :: \<open>nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> string\<close> where
  \<open>check_linear_combi_l_pre_err_imp i adom emptyl ivars =
  cl_to_clt ''Precondition for '%' failed '' @ show_nat i @
  cl_to_clt ''(already in domain: '' @ show_bool adom @
  cl_to_clt ''; empty CL'' @ show_bool emptyl @
  cl_to_clt ''; new vars: '' @ show_bool ivars @ '')''\<close>

sepref_def check_linear_combi_l_pre_err_impl is 
  \<open>uncurry3 (RETURN oooo check_linear_combi_l_pre_err_imp)\<close>
  :: \<open>si64_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding check_linear_combi_l_pre_err_imp_def
  by sepref

lemma check_linear_combi_l_pre_err_fref:
  \<open>(uncurry3 (RETURN oooo check_linear_combi_l_pre_err_imp),
  uncurry3 check_linear_combi_l_pre_err)
  \<in> Id \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding check_linear_combi_l_pre_err_imp_def
    check_linear_combi_l_pre_err_def
  by auto

lemmas check_linear_combi_l_pre_err_hnr[sepref_fr_rules] =
  check_linear_combi_l_pre_err_impl.refine[FCOMP check_linear_combi_l_pre_err_fref]

definition check_linear_combi_l_dom_err_imp :: \<open> _ \<Rightarrow> nat \<Rightarrow> string\<close> where
  \<open>check_linear_combi_l_dom_err_imp xs i =
  cl_to_clt ''Invalid polynomial '' @ show_nat i\<close>

sepref_def check_linear_combi_l_dom_err_impl is
  \<open>uncurry (RETURN oo check_linear_combi_l_dom_err_imp)\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding check_linear_combi_l_dom_err_imp_def
  apply sepref
  done

lemma check_linear_combi_l_dom_err_fref:
  \<open>(uncurry (RETURN oo check_linear_combi_l_dom_err_imp),
  uncurry check_linear_combi_l_dom_err) \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding check_linear_combi_l_dom_err_imp_def
    check_linear_combi_l_dom_err_def
  by auto

lemmas check_linear_combi_l_dom_err_hnr[sepref_fr_rules] =
  check_linear_combi_l_dom_err_impl.refine[FCOMP check_linear_combi_l_dom_err_fref]

definition check_linear_combi_l_mult_err_imp :: \<open> _ \<Rightarrow> _ \<Rightarrow> string\<close> where
  \<open>check_linear_combi_l_mult_err_imp xs ys =
  cl_to_clt ''Invalid calculation, found'' @ poly_print xs @
  cl_to_clt '' instead of '' @ poly_print ys\<close>

sepref_def check_linear_combi_l_mult_err_impl is 
  \<open>uncurry (RETURN oo check_linear_combi_l_mult_err_imp)\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding check_linear_combi_l_mult_err_imp_def
  by sepref

lemma check_linear_combi_l_mult_err_fref:
  \<open>(uncurry (RETURN oo check_linear_combi_l_mult_err_imp),
  uncurry check_linear_combi_l_mult_err) \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding check_linear_combi_l_mult_err_imp_def
    check_linear_combi_l_mult_err_def
  by auto

lemmas check_linear_combi_l_mult_err_hnr[sepref_fr_rules] =
  check_linear_combi_l_mult_err_impl.refine[FCOMP check_linear_combi_l_mult_err_fref]

subsection \<open>Error Messages of the Extensions\<close>

definition check_extension_l2_side_cond_err_imp
  :: \<open>string \<Rightarrow> llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> string\<close>
where
  \<open>check_extension_l2_side_cond_err_imp v p' q =
  cl_to_clt ''Error while checking side conditions of extension, var is '' @ cl_to_clt v @
  cl_to_clt '' polynomial is '' @ poly_print p' @
  cl_to_clt '' side condition p*p - p = '' @ poly_print q @ cl_to_clt '' and should be 0''\<close>

text \<open>Two implementations: one over list-based strings and polynomials (used by
  \<^file>\<open>LPAC_Checker_Synthesis.thy\<close>) and one over array-based strings and polynomials.
  Both are registered; \<^text>\<open>sepref\<close> selects by the assertions of the arguments.\<close>
sepref_def check_extension_l2_side_cond_err_impl is
  \<open>uncurry2 (RETURN ooo check_extension_l2_side_cond_err_imp)\<close>
  :: \<open>strl_assn'\<^sup>k *\<^sub>a polynomial_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding check_extension_l2_side_cond_err_imp_def
  by sepref

sepref_def check_extension_l2_side_cond_erra_impl is
  \<open>uncurry2 (RETURN ooo check_extension_l2_side_cond_err_imp)\<close>
  :: \<open>stra_assn\<^sup>k *\<^sub>a polynomiala_assn\<^sup>k *\<^sub>a polynomiala_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding check_extension_l2_side_cond_err_imp_def
  by sepref

lemma check_extension_l2_side_cond_err_fref:
  \<open>(uncurry2 (RETURN ooo check_extension_l2_side_cond_err_imp),
  uncurry2 LPAC_Checker.check_extension_l_side_cond_err)
  \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding check_extension_l2_side_cond_err_imp_def
    LPAC_Checker.check_extension_l_side_cond_err_def
  by auto

lemmas check_extension_l2_side_cond_err_hnr[sepref_fr_rules] =
  check_extension_l2_side_cond_err_impl.refine[FCOMP check_extension_l2_side_cond_err_fref]

lemmas check_extension_l2_side_cond_erra_hnr[sepref_fr_rules] =
  check_extension_l2_side_cond_erra_impl.refine[FCOMP check_extension_l2_side_cond_err_fref]

definition check_linear_combi_l_pre_err_imp_s  where
  \<open>check_linear_combi_l_pre_err_imp_s i pd p mem =
    (if pd then cl_to_clt ''The polynomial with id '' @ show_nat i 
              @ cl_to_clt '' was not found'' else cl_to_clt '''') @
    (if p then cl_to_clt ''The co-factor from '' @ show_nat i 
              @ cl_to_clt '' was empty'' else cl_to_clt '''') @
    (if mem then cl_to_clt ''Memory out or new variable'' else cl_to_clt '''')\<close>

sepref_def check_linear_combi_l_pre_err_s_impl
  is \<open>uncurry3 (RETURN oooo check_linear_combi_l_pre_err_imp_s)\<close>
  :: \<open>si64_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding check_linear_combi_l_pre_err_imp_s_def
  by sepref

abbreviation monom_s_rel where
  \<open>monom_s_rel \<equiv> \<langle>nat_rel\<rangle>list_rel\<close>

abbreviation monom_s_assn where
  \<open>monom_s_assn \<equiv> cl_assn' si64_assn\<close>

abbreviation poly_s_assn where
  \<open>poly_s_assn \<equiv> cl_assn' (monom_s_assn \<times>\<^sub>a sbi_assn)\<close>

definition check_linear_combi_l_s_dom_err_imp  where
  \<open>check_linear_combi_l_s_dom_err_imp x p =
    cl_to_clt ''Poly not found in CL from x '' @ show_nat p\<close>

sepref_def check_linear_combi_l_s_dom_err_impl is
  \<open>uncurry (RETURN oo check_linear_combi_l_s_dom_err_imp)\<close>
  :: \<open>poly_s_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding check_linear_combi_l_s_dom_err_imp_def
  by sepref

lemma check_linear_combi_l_s_dom_err_fref:
  \<open>(uncurry (RETURN oo (check_linear_combi_l_s_dom_err_imp)),
    uncurry (check_linear_combi_l_s_dom_err)) 
   \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding check_linear_combi_l_s_dom_err_imp_def
    check_linear_combi_l_s_dom_err_def
  by auto

lemma check_linear_combi_l_pre_err_s_fref:
  \<open>(uncurry3 (RETURN oooo check_linear_combi_l_pre_err_imp_s),
    uncurry3 (check_linear_combi_l_pre_err)) 
   \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding check_linear_combi_l_pre_err_impl_def check_linear_combi_l_pre_err_def
  by auto

lemmas check_linear_combi_l_s_dom_err_hnr[sepref_fr_rules] =
  check_linear_combi_l_s_dom_err_impl.refine[FCOMP check_linear_combi_l_s_dom_err_fref]

lemmas check_linear_combi_l_pre_err_s_hnr[sepref_fr_rules] =
  check_linear_combi_l_pre_err_s_impl.refine[FCOMP check_linear_combi_l_pre_err_s_fref]

section \<open>Printing of Shared Polynomials\<close>

definition print_monom_s_inner :: \<open>char list \<Rightarrow> nat \<Rightarrow> char list\<close> where
  \<open>print_monom_s_inner \<equiv> \<lambda>acc v. acc @ cl_to_clt '' x'' @ show_nat v\<close>

definition print_monom_s :: \<open>nat list \<Rightarrow> char list\<close> where
  \<open>print_monom_s \<equiv> foldl print_monom_s_inner []\<close>

definition \<open>mnml_s_print \<equiv> \<lambda>(m,n). cl_to_clt (chars_of_int (COPY n)) @ print_monom_s m\<close>

sepref_def print_monom_s_inner_impl is \<open>uncurry (RETURN oo print_monom_s_inner)\<close>
  :: \<open>strlt_assn\<^sup>d *\<^sub>a si64_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding print_monom_s_inner_def
  by sepref

definition [llvm_code]: \<open>print_monom_s_impl \<equiv> \<lambda>m. doM {e \<leftarrow> clt_empty; cl_fold' print_monom_s_inner_impl e m}\<close>

lemma print_monom_s_rule: \<open>llvm_htriple
  (monom_s_assn m mi)
  (print_monom_s_impl mi)
  (\<lambda>r. monom_s_assn m mi ** strlt_assn (print_monom_s m) r)\<close>
proof -
  have INNER_vcg: \<open>llvm_htriple
    (strlt_assn acc acci ** si64_assn t ti)
    (print_monom_s_inner_impl acci ti)
    (\<lambda>r. strlt_assn (print_monom_s_inner acc t) r ** si64_assn t ti)\<close> for acc acci t ti
    apply (rule htriple_ent_post[OF _ hfref_htriple_d1_k2[OF print_monom_s_inner_impl.refine]])
    by (simp add: sep_conj_aci)
  show ?thesis
    unfolding print_monom_s_impl_def
    supply [vcg_rules] = cl_fold'_rule[where R="strlt_assn" and A="si64_assn"
      and f=print_monom_s_inner_impl and fa=print_monom_s_inner,
      OF INNER_vcg]
    supply [simp] = print_monom_s_def
    by vcg
qed

lemma print_monom_s_hnr[sepref_fr_rules]:
  \<open>(print_monom_s_impl, (RETURN o print_monom_s))
  \<in> monom_s_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding snat_rel_def snat.assn_is_rel[symmetric]
  apply (sepref_to_hoare)
  supply [vcg_rules] = print_monom_s_rule[unfolded snat_rel_def snat.assn_is_rel[symmetric]]
  supply [simp] = pure_def
  by vcg

sepref_def mnml_s_print_impl is \<open>RETURN o mnml_s_print\<close>
  :: \<open>(monom_s_assn \<times>\<^sub>a sbi_assn)\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding mnml_s_print_def
  by sepref

definition poly_s_print_inner :: \<open>char list \<Rightarrow> nat list \<times> int \<Rightarrow> char list\<close> where
  \<open>poly_s_print_inner \<equiv> \<lambda>acc p. acc @ mnml_s_print p\<close>

definition poly_s_print :: \<open>sllist_polynomial \<Rightarrow> string\<close> where
  \<open>poly_s_print \<equiv> foldl poly_s_print_inner []\<close>

sepref_def poly_s_print_inner_impl is \<open>uncurry (RETURN oo poly_s_print_inner)\<close>
  :: \<open>strlt_assn\<^sup>d *\<^sub>a (monom_s_assn \<times>\<^sub>a sbi_assn)\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding poly_s_print_inner_def
  by sepref

definition [llvm_code]: \<open>poly_s_print_impl \<equiv> \<lambda>ps. doM {e \<leftarrow> clt_empty; cl_fold' poly_s_print_inner_impl e ps}\<close>

lemma poly_s_print_rule: \<open>llvm_htriple
  (poly_s_assn ps psi)
  (poly_s_print_impl psi)
  (\<lambda>r. poly_s_assn ps psi ** strlt_assn (poly_s_print ps) r)\<close>
proof -
  have INNER_vcg: \<open>llvm_htriple
    (strlt_assn acc acci ** (monom_s_assn \<times>\<^sub>a sbi_assn) p pi)
    (poly_s_print_inner_impl acci pi)
    (\<lambda>r. strlt_assn (poly_s_print_inner acc p) r ** (monom_s_assn \<times>\<^sub>a sbi_assn) p pi)\<close> for acc acci p pi
    apply (rule htriple_ent_post[OF _ hfref_htriple_d1_k2[OF poly_s_print_inner_impl.refine]])
    by (simp add: sep_conj_aci)
  show ?thesis
    unfolding poly_s_print_impl_def
    supply [vcg_rules] = cl_fold'_rule[where R="strlt_assn" and A="monom_s_assn \<times>\<^sub>a sbi_assn"
      and f=poly_s_print_inner_impl and fa=poly_s_print_inner,
      OF INNER_vcg]
    supply [simp] = poly_s_print_def
    by vcg
qed

lemma poly_s_print_hnr[sepref_fr_rules]:
  \<open>(poly_s_print_impl, (RETURN o poly_s_print))
  \<in> poly_s_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding snat_rel_def snat.assn_is_rel[symmetric]
  apply (sepref_to_hoare)
  supply [vcg_rules] = poly_s_print_rule[unfolded snat_rel_def snat.assn_is_rel[symmetric]]
  supply [simp] = pure_def
  by vcg

definition check_linear_combi_l_s_mult_err_imp :: \<open>sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> string\<close> where
  \<open>check_linear_combi_l_s_mult_err_imp xs ys =
  cl_to_clt ''Unequal polynom found in CL '' @ poly_s_print xs @
  cl_to_clt '' but '' @ poly_s_print ys\<close>

lemma check_linear_combi_l_s_mult_err_fref:
  \<open>(uncurry (RETURN oo check_linear_combi_l_s_mult_err_imp),
    uncurry check_linear_combi_l_s_mult_err) \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding check_linear_combi_l_s_mult_err_imp_def
    check_linear_combi_l_s_mult_err_def
  by auto

sepref_def check_linear_combi_l_s_mult_err_impl is
  \<open>uncurry (RETURN oo check_linear_combi_l_s_mult_err_imp)\<close>
  :: \<open>poly_s_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding check_linear_combi_l_s_mult_err_imp_def
  by sepref

lemmas check_linear_combi_l_s_mult_err_hnr[sepref_fr_rules] =
  check_linear_combi_l_s_mult_err_impl.refine[FCOMP check_linear_combi_l_s_mult_err_fref]

definition check_extension_l_s_new_var_multiple_err_imp :: \<open>string \<Rightarrow> sllist_polynomial \<Rightarrow> string\<close> where
  \<open>check_extension_l_s_new_var_multiple_err_imp v p =
  cl_to_clt ''Variable already defined '' @ cl_to_clt v @
  cl_to_clt '' but '' @ poly_s_print p\<close>

lemma check_extension_l_s_new_var_multiple_err_fref:
  \<open>(uncurry (RETURN oo check_extension_l_s_new_var_multiple_err_imp),
    uncurry check_extension_l_s_new_var_multiple_err) \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding check_extension_l_s_new_var_multiple_err_imp_def
    check_extension_l_s_new_var_multiple_err_def
  by auto
sepref_def check_extension_l_s_new_var_multiple_err_impl is
  \<open>uncurry (RETURN oo check_extension_l_s_new_var_multiple_err_imp)\<close>
  :: \<open>stra_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding check_extension_l_s_new_var_multiple_err_imp_def
  by sepref

lemmas check_extension_l_s_new_var_multiple_err_hnr[sepref_fr_rules] =
  check_extension_l_s_new_var_multiple_err_impl.refine[FCOMP check_extension_l_s_new_var_multiple_err_fref]

definition check_extension_l_s_side_cond_err_imp
  :: \<open>string \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> string\<close>
where
  \<open>check_extension_l_s_side_cond_err_imp v p p' q' =
  cl_to_clt ''p^2- p != 0 '' @ cl_to_clt v @
  cl_to_clt '' but '' @ poly_s_print p @
  cl_to_clt '' and '' @ poly_s_print p' @
  cl_to_clt '' and '' @ poly_s_print q'\<close>

lemma check_extension_l_s_side_cond_err_fref:
  \<open>(uncurry3 (RETURN oooo check_extension_l_s_side_cond_err_imp),
    uncurry3 check_extension_l_s_side_cond_err) \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding check_extension_l_s_side_cond_err_imp_def
    check_extension_l_s_side_cond_err_def
  by auto

sepref_def check_extension_l_s_side_cond_err_impl is
  \<open>uncurry3 (RETURN oooo check_extension_l_s_side_cond_err_imp)\<close>
  :: \<open>stra_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding check_extension_l_s_side_cond_err_imp_def
  by sepref

lemmas check_extension_l_s_side_cond_err_hnr[sepref_fr_rules] =
  check_extension_l_s_side_cond_err_impl.refine[FCOMP check_extension_l_s_side_cond_err_fref]

definition memory_out_msg where
  \<open>memory_out_msg = cl_to_clt ''memory out''\<close>

sepref_def memory_out_msg_impl is \<open>uncurry0 (RETURN memory_out_msg)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding memory_out_msg_def
  by sepref

end
