theory LPAC_Error
  imports LPAC_Checker LPAC_Version
    LPAC_Checker_Init
    More_Loops
    PAC_Checker_Relation
    PAC_Checker_Synthesis
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

end
