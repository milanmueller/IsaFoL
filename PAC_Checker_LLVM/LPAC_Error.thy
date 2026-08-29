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

subsection \<open>Error Messages of the Extensions\<close>

definition check_extension_l2_side_cond_err_imp
  :: \<open>string \<Rightarrow> llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> string\<close>
where
  \<open>check_extension_l2_side_cond_err_imp v p' q =
  cl_to_clt ''Error while checking side conditions of extension, var is '' @ cl_to_clt v @
  cl_to_clt '' polynomial is '' @ poly_print p' @
  cl_to_clt '' side condition p*p - p = '' @ poly_print q @ cl_to_clt '' and should be 0''\<close>

sepref_def check_extension_l2_side_cond_err_impl is
  \<open>uncurry2 (RETURN ooo check_extension_l2_side_cond_err_imp)\<close>
  :: \<open>strl_assn'\<^sup>k *\<^sub>a polynomial_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
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

type_synonym sllist_polynomial = \<open>(nat list \<times> int) list\<close>

abbreviation monom_s_rel where
  \<open>monom_s_rel \<equiv> \<langle>nat_rel\<rangle>list_rel\<close>

abbreviation monom_s_assn where
  \<open>monom_s_assn \<equiv> cl_assn' si64_assn\<close>

abbreviation poly_s_assn where
  \<open>poly_s_assn \<equiv> cl_assn' (monom_s_assn \<times>\<^sub>a sbi_assn)\<close>

definition check_linear_combi_l_s_dom_err :: \<open>sllist_polynomial \<Rightarrow> nat \<Rightarrow> string nres\<close> where
  \<open>check_linear_combi_l_s_dom_err p r = SPEC (\<lambda>_. True)\<close>

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

lemmas check_linear_combi_l_s_dom_err_hnr[sepref_fr_rules] =
  check_linear_combi_l_s_dom_err_impl.refine[FCOMP check_linear_combi_l_s_dom_err_fref]

(* TODO - need a way to print sllist_polynomial 
definition check_linear_combi_l_s_mult_err_impl :: \<open>_ \<Rightarrow> _ \<Rightarrow> _\<close>  where
  \<open>check_linear_combi_l_s_mult_err_impl x p =
  ''Unequal polynom found in CL '' @ show (map (\<lambda>(a,b). (map nat_of_uint64 a, b)) p) @
  '' but '' @ show (map (\<lambda>(a,b). (map nat_of_uint64 a, b)) x)\<close>

lemma [sepref_fr_rules]:
  \<open>(uncurry (return oo (check_linear_combi_l_s_mult_err_impl)),
    uncurry (check_linear_combi_l_s_mult_err)) \<in> poly_s_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_linear_combi_l_s_mult_err_impl_def check_linear_combi_l_s_mult_err_def list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done

definition check_extension_l_s_new_var_multiple_err_impl :: \<open>String.literal \<Rightarrow> _ \<Rightarrow> _\<close>  where
  \<open>check_extension_l_s_new_var_multiple_err_impl x p =
  ''Variable already defined '' @ show x @
  '' but '' @ show (map (\<lambda>(a,b). (map nat_of_uint64 a, b)) p)\<close>

lemma [sepref_fr_rules]:
  \<open>(uncurry (return oo (check_extension_l_s_new_var_multiple_err_impl)),
    uncurry (check_extension_l_s_new_var_multiple_err)) \<in> string_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_extension_l_s_new_var_multiple_err_impl_def check_extension_l_s_new_var_multiple_err_def list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done

definition check_extension_l_s_side_cond_err_impl :: \<open>String.literal \<Rightarrow> _ \<Rightarrow> _\<close>  where
  \<open>check_extension_l_s_side_cond_err_impl x p p' q' =
  ''p^2- p != 0 '' @ show x @
  '' but '' @ show (map (\<lambda>(a,b). (map nat_of_uint64 a, b)) p) @
  '' and '' @ show (map (\<lambda>(a,b). (map nat_of_uint64 a, b)) p') @
   '' and ''  @ show (map (\<lambda>(a,b). (map nat_of_uint64 a, b)) q')\<close>

lemma [sepref_fr_rules]:
  \<open>(uncurry3 (return oooo (check_extension_l_s_side_cond_err_impl)),
    uncurry3 (check_extension_l_s_side_cond_err)) \<in> string_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k*\<^sub>a poly_s_assn\<^sup>k*\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_extension_l_s_side_cond_err_impl_def check_extension_l_s_side_cond_err_def list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done

*)

definition memory_out_msg where
  \<open>memory_out_msg = cl_to_clt ''memory out''\<close>

sepref_def memory_out_msg_impl is \<open>uncurry0 (RETURN memory_out_msg)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding memory_out_msg_def
  by sepref

end
