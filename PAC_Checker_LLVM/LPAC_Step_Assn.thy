theory LPAC_Step_Assn
  imports PAC_Step_Assn LPAC_Checker_Specification
begin

text \<open>Low-level implementation of the LPAC step datatype, mirroring \<open>PAC_Step_Assn\<close>:
  the type is only ever instantiated as
  @{typ \<open>(llist_polynomial, string, nat) LPAC_Checker_Specification.pac_step\<close>}, so we fix
  the types to keep implementation and proofs straightforward.\<close>

type_synonym srcs_conc = \<open>(poly_conc \<times> 64 word) cl_list\<close>
type_synonym lpac_step_hol = \<open>(llist_polynomial, string, nat) LPAC_Checker_Specification.pac_step\<close>

type_synonym lpac_step_conc =
  \<open>8 word \<times> 64 word \<times> poly_conc \<times> srcs_conc \<times> strl_conc\<close>
(* tag    \<times> id      \<times> res poly  \<times> lin-comb srcs \<times> var (for ext) *)

abbreviation \<open>srcs_assn \<equiv> cl_assn' (polynomial_assn \<times>\<^sub>a si64_assn)\<close>

definition lpac_step_assn :: \<open>lpac_step_hol \<Rightarrow> lpac_step_conc \<Rightarrow> assn\<close> where
  \<open>lpac_step_assn step \<equiv> \<lambda>(tag, idc, resi, srcsi, vari). case step of
  CL srcs ni res     \<Rightarrow> \<up>(tag = 0) ** srcs_assn srcs srcsi ** si64_assn ni idc
                                  ** polynomial_assn res resi
| Extension ni v res \<Rightarrow> \<up>(tag = 1) ** si64_assn ni idc ** strl_assn' v vari
                                  ** polynomial_assn res resi
| Del s1             \<Rightarrow> \<up>(tag = 2) ** si64_assn s1 idc\<close>

lemma lpac_step_assn_CL[simp]:
  \<open>lpac_step_assn (CL srcs ni res) (tag, idc, resi, srcsi, vari) =
    (\<up>(tag = 0) ** srcs_assn srcs srcsi ** si64_assn ni idc
     ** polynomial_assn res resi)\<close>
  unfolding lpac_step_assn_def by simp

lemma lpac_step_assn_Extension[simp]:
  \<open>lpac_step_assn (Extension ni v res) (tag, idc, resi, srcsi, vari) =
    (\<up>(tag = 1) ** si64_assn ni idc ** strl_assn' v vari
     ** polynomial_assn res resi)\<close>
  unfolding lpac_step_assn_def by simp

lemma lpac_step_assn_Del[simp]:
  \<open>lpac_step_assn (Del s1) (tag, idc, resi, srcsi, vari) =
    (\<up>(tag = 2) ** si64_assn s1 idc)\<close>
  unfolding lpac_step_assn_def by simp

section \<open>Producers\<close>

definition mk_cl_impl :: \<open>srcs_conc \<Rightarrow> 64 word \<Rightarrow> poly_conc \<Rightarrow> lpac_step_conc llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>mk_cl_impl srcsi nii resi \<equiv> Mreturn (0, nii, resi, srcsi, init)\<close>

definition mk_lext_impl :: \<open>64 word \<Rightarrow> strl_conc \<Rightarrow> poly_conc \<Rightarrow> lpac_step_conc llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>mk_lext_impl nii vi resi \<equiv> Mreturn (1, nii, resi, init, vi)\<close>

definition mk_ldel_impl :: \<open>64 word \<Rightarrow> lpac_step_conc llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>mk_ldel_impl s1i \<equiv> Mreturn (2, s1i, init, init, init)\<close>

lemma mk_cl_impl_hnr[sepref_fr_rules]:
  \<open>(uncurry2 mk_cl_impl, uncurry2 (RETURN ooo CL))
    \<in> srcs_assn\<^sup>d *\<^sub>a si64_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>d \<rightarrow>\<^sub>a lpac_step_assn\<close>
  unfolding mk_cl_impl_def
  apply sepref_to_hoare
  by (vcg; auto simp: step_pure_reassembly)

lemma mk_lext_impl_hnr[sepref_fr_rules]:
  \<open>(uncurry2 mk_lext_impl, uncurry2 (RETURN ooo Extension))
    \<in> si64_assn\<^sup>k *\<^sub>a strl_assn'\<^sup>d *\<^sub>a polynomial_assn\<^sup>d \<rightarrow>\<^sub>a lpac_step_assn\<close>
  unfolding mk_lext_impl_def
  apply sepref_to_hoare
  by (vcg; auto simp: step_pure_reassembly)

lemma mk_ldel_impl_hnr[sepref_fr_rules]:
  \<open>(mk_ldel_impl, RETURN o Del) \<in> si64_assn\<^sup>k \<rightarrow>\<^sub>a lpac_step_assn\<close>
  unfolding mk_ldel_impl_def
  apply sepref_to_hoare
  by (vcg; auto simp: step_pure_reassembly)

sepref_register CL
sepref_register Extension Del

end
