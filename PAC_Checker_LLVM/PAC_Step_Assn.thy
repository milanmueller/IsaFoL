theory PAC_Step_Assn
  imports IICF_Copying_List BigInt_LLVM.LLVM_CodeGen_Signed
    PAC_Checker LLVM_Polynomials
begin

text \<open>This theory defines the low-level implementation for the higher order @{typ \<open>('a, 'b, 'lbls) pac_step\<close>}.
  The pac step is only every instantiated as @{typ \<open>(llist_polynomial, string, nat) pac_step\<close>}, we fix the types here
  to make implemenation and proofs more straigth forward.\<close>

type_synonym strl_conc = \<open>8 word node ptr\<close>
type_synonym poly_conc = \<open>monomial_conc node ptr\<close>

text \<open>We represent the steps using a tagged product that can carry all required data
  of every constructor of the high level pac step. Unused slots are filled with `init`.\<close>
type_synonym pac_step_hol = \<open>(llist_polynomial, string, nat) pac_step\<close>
type_synonym pac_step_conc =
  \<open>8 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> poly_conc \<times> poly_conc \<times> strl_conc\<close>
(* tag    \<times> id op1  \<times> id op2  \<times> new id  \<times> mult poly \<times> res       \<times> var (for ext) *)

abbreviation \<open>si64_assn \<equiv> snat_assn' TYPE(64)\<close>

definition pac_step_assn :: \<open>pac_step_hol \<Rightarrow> pac_step_conc \<Rightarrow> assn\<close> where
  \<open>pac_step_assn step \<equiv> \<lambda>(tag, s1i, s2i, nii, multpi, resi, vari). case step of
  Add s1 s2 ni res   \<Rightarrow> \<up>(tag = 0) ** si64_assn s1 s1i ** si64_assn s2 s2i
                                  ** si64_assn ni nii ** polynomial_assn res resi
| Mult s1 mp ni res  \<Rightarrow> \<up>(tag = 1) ** si64_assn s1 s1i ** polynomial_assn mp multpi
                                  ** si64_assn ni nii ** polynomial_assn res resi
| Extension ni v res \<Rightarrow> \<up>(tag = 2) ** si64_assn ni nii ** strl_assn' v vari ** polynomial_assn res resi
| Del s1             \<Rightarrow> \<up>(tag = 3) ** si64_assn s1 s1i\<close>

lemma pac_step_assn_Add[simp]:
  \<open>pac_step_assn (Add s1 s2 ni res) (tag, s1i, s2i, nii, multpi, resi, vari) =
    (\<up>(tag = 0) ** si64_assn s1 s1i ** si64_assn s2 s2i
     ** si64_assn ni nii ** polynomial_assn res resi)\<close>
  unfolding pac_step_assn_def by simp

lemma pac_step_assn_Mult[simp]:
  \<open>pac_step_assn (Mult s1 mp ni res) (tag, s1i, s2i, nii, multpi, resi, vari) =
    (\<up>(tag = 1) ** si64_assn s1 s1i ** polynomial_assn mp multpi
     ** si64_assn ni nii ** polynomial_assn res resi)\<close>
  unfolding pac_step_assn_def by simp

lemma pac_step_assn_Extension[simp]:
  \<open>pac_step_assn (Extension ni v res) (tag, s1i, s2i, nii, multpi, resi, vari) =
    (\<up>(tag = 2) ** si64_assn ni nii ** strl_assn' v vari ** polynomial_assn res resi)\<close>
  unfolding pac_step_assn_def by simp

lemma pac_step_assn_Del[simp]:
  \<open>pac_step_assn (Del s1) (tag, s1i, s2i, nii, multpi, resi, vari) =
    (\<up>(tag = 3) ** si64_assn s1 s1i)\<close>
  unfolding pac_step_assn_def by simp

lemmas step_pure_reassembly =
  ENTAILS_def entails_def sep_algebra_simps pure_app_eq pure_def vcg_tag_defs

section \<open>Producers\<close>

definition mk_add_impl :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> poly_conc \<Rightarrow> pac_step_conc llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>mk_add_impl s1i s2i nii resi \<equiv> Mreturn (0, s1i, s2i, nii, init, resi, init)\<close>

definition mk_mult_impl :: \<open>64 word \<Rightarrow> poly_conc \<Rightarrow> 64 word \<Rightarrow> poly_conc \<Rightarrow> pac_step_conc llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>mk_mult_impl s1i mpi nii resi \<equiv> Mreturn (1, s1i, init, nii, mpi, resi, init)\<close>

definition mk_ext_impl :: \<open>64 word \<Rightarrow> strl_conc \<Rightarrow> poly_conc \<Rightarrow> pac_step_conc llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>mk_ext_impl nii vi resi \<equiv> Mreturn (2, init, init, nii, init, resi, vi)\<close>

definition mk_del_impl :: \<open>64 word \<Rightarrow> pac_step_conc llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>mk_del_impl s1i \<equiv> Mreturn (3, s1i, init, init, init, init, init)\<close>

lemma mk_add_impl_hnr[sepref_fr_rules]:
  \<open>(uncurry3 mk_add_impl, uncurry3 (RETURN oooo Add))
    \<in> si64_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>d \<rightarrow>\<^sub>a pac_step_assn\<close>
  unfolding mk_add_impl_def
  apply sepref_to_hoare
  by (vcg; auto simp: step_pure_reassembly)

lemma mk_mult_impl_hnr[sepref_fr_rules]:
  \<open>(uncurry3 mk_mult_impl, uncurry3 (RETURN oooo Mult))
    \<in> si64_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>d *\<^sub>a si64_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>d \<rightarrow>\<^sub>a pac_step_assn\<close>
  unfolding mk_mult_impl_def
  apply sepref_to_hoare
  by (vcg; auto simp: step_pure_reassembly)

lemma mk_ext_impl_hnr[sepref_fr_rules]:
  \<open>(uncurry2 mk_ext_impl, uncurry2 (RETURN ooo Extension))
    \<in> si64_assn\<^sup>k *\<^sub>a strl_assn'\<^sup>d *\<^sub>a polynomial_assn\<^sup>d \<rightarrow>\<^sub>a pac_step_assn\<close>
  unfolding mk_ext_impl_def
  apply sepref_to_hoare
  by (vcg; auto simp: step_pure_reassembly)

lemma mk_del_impl_hnr[sepref_fr_rules]:
  \<open>(mk_del_impl, RETURN o Del) \<in> si64_assn\<^sup>k \<rightarrow>\<^sub>a pac_step_assn\<close>
  unfolding mk_del_impl_def
  apply sepref_to_hoare
  by (vcg; auto simp: step_pure_reassembly)

sepref_register Add Mult Extension Del

end
