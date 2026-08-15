theory PAC_Step_Assn
  imports IICF_Copying_List BigInt_LLVM.LLVM_CodeGen_Signed
    PAC_Checker LLVM_Polynomials PAC_Checker_Specification
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

section \<open>Distriminators\<close>

definition isAdd_impl :: \<open>pac_step_conc \<Rightarrow> 1 word llM\<close> where [llvm_code, llvm_inline]:
  \<open>isAdd_impl \<equiv> \<lambda>(tag, s1i, s2i, nii, multpi, resi, vari).  Mreturn (ll_cmp'_eq tag 0)\<close>

definition isMult_impl :: \<open>pac_step_conc \<Rightarrow> 1 word llM\<close> where [llvm_code, llvm_inline]:
  \<open>isMult_impl \<equiv> \<lambda>(tag, s1i, s2i, nii, multpi, resi, vari).  Mreturn (ll_cmp'_eq tag 1)\<close>

definition isExtension_impl :: \<open>pac_step_conc \<Rightarrow> 1 word llM\<close> where [llvm_code, llvm_inline]:
  \<open>isExtension_impl \<equiv> \<lambda>(tag, s1i, s2i, nii, multpi, resi, vari).  Mreturn (ll_cmp'_eq tag 2)\<close>

definition isDel_impl :: \<open>pac_step_conc \<Rightarrow> 1 word llM\<close> where [llvm_code, llvm_inline]:
  \<open>isDel_impl \<equiv> \<lambda>(tag, s1i, s2i, nii, multpi, resi, vari).  Mreturn (ll_cmp'_eq tag 3)\<close>

lemma pac_step_assn_tag:
  \<open>pure_part (pac_step_assn step (tag, s1i, s2i, nii, multpi, resi, vari)) \<Longrightarrow>
     (tag = 0) = is_Add step \<and> (tag = 1) = is_Mult step \<and>
     (tag = 2) = is_Extension step \<and> (tag = 3) = is_Del step\<close>
  by (cases step) (auto simp: pac_step_assn_def dest!: pure_part_split_conj)

lemmas pac_step_assn_tagD = pure_partI[THEN pac_step_assn_tag]

lemma is_Add_hnr[sepref_fr_rules]:
  \<open>(isAdd_impl, RETURN o is_Add) \<in> pac_step_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding isAdd_impl_def ll_cmp'_eq_def
  apply (sepref_to_hoare; vcg)
  by (auto simp: step_pure_reassembly bool1_rel_def bool.rel_def in_br_conv
    dest!: pac_step_assn_tagD)

lemma is_Mult_hnr[sepref_fr_rules]:
  \<open>(isMult_impl, RETURN o is_Mult) \<in> pac_step_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding isMult_impl_def ll_cmp'_eq_def
  apply (sepref_to_hoare; vcg)
  by (auto simp: step_pure_reassembly bool1_rel_def bool.rel_def in_br_conv
    dest!: pac_step_assn_tagD)

lemma is_Extension_hnr[sepref_fr_rules]:
  \<open>(isExtension_impl, RETURN o is_Extension) \<in> pac_step_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding isExtension_impl_def ll_cmp'_eq_def
  apply (sepref_to_hoare; vcg)
  by (auto simp: step_pure_reassembly bool1_rel_def bool.rel_def in_br_conv
    dest!: pac_step_assn_tagD)

lemma is_Del_hnr[sepref_fr_rules]:
  \<open>(isDel_impl, RETURN o is_Del) \<in> pac_step_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding isDel_impl_def ll_cmp'_eq_def
  apply (sepref_to_hoare; vcg)
  by (auto simp: step_pure_reassembly bool1_rel_def bool.rel_def in_br_conv
    dest!: pac_step_assn_tagD)

section \<open>Destructors\<close>

definition dest_add :: \<open>pac_step_hol \<Rightarrow> nat \<times> nat \<times> nat \<times> llist_polynomial\<close> where
  \<open>dest_add step = (pac_src1 step, pac_src2 step, new_id step, pac_res step)\<close>

definition dest_mult :: \<open>pac_step_hol \<Rightarrow> nat \<times> llist_polynomial \<times> nat \<times> llist_polynomial\<close> where
  \<open>dest_mult step = (pac_src1 step, pac_mult step, new_id step, pac_res step)\<close>

definition dest_extension :: \<open>pac_step_hol \<Rightarrow> nat \<times> string \<times> llist_polynomial\<close> where
  \<open>dest_extension step = (new_id step, new_var step, pac_res step)\<close>

definition dest_del :: \<open>pac_step_hol \<Rightarrow> nat\<close> where
  \<open>dest_del step = pac_src1 step\<close>

definition dest_add_impl :: \<open>pac_step_conc \<Rightarrow> (64 word \<times> 64 word \<times> 64 word \<times> poly_conc) llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>dest_add_impl \<equiv> \<lambda>(tag, s1i, s2i, nii, multpi, resi, vari). Mreturn (s1i, s2i, nii, resi)\<close>

definition dest_mult_impl :: \<open>pac_step_conc \<Rightarrow> (64 word \<times> poly_conc \<times> 64 word \<times> poly_conc) llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>dest_mult_impl \<equiv> \<lambda>(tag, s1i, s2i, nii, multpi, resi, vari). Mreturn (s1i, multpi, nii, resi)\<close>

definition dest_extension_impl :: \<open>pac_step_conc \<Rightarrow> (64 word \<times> strl_conc \<times> poly_conc) llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>dest_extension_impl \<equiv> \<lambda>(tag, s1i, s2i, nii, multpi, resi, vari). Mreturn (nii, vari, resi)\<close>

definition dest_del_impl :: \<open>pac_step_conc \<Rightarrow> 64 word llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>dest_del_impl \<equiv> \<lambda>(tag, s1i, s2i, nii, multpi, resi, vari). Mreturn s1i\<close>

definition mop_dest_add :: \<open>pac_step_hol \<Rightarrow> (nat \<times> nat \<times> nat \<times> llist_polynomial) nres\<close> where
  \<open>mop_dest_add step = do {
     ASSERT (is_Add step);
     RETURN (dest_add step)
   }\<close>

definition mop_dest_mult :: \<open>pac_step_hol \<Rightarrow> (nat \<times> llist_polynomial \<times> nat \<times> llist_polynomial) nres\<close>
  where
  \<open>mop_dest_mult step = do {
     ASSERT (is_Mult step);
     RETURN (dest_mult step)
   }\<close>

definition mop_dest_extension :: \<open>pac_step_hol \<Rightarrow> (nat \<times> string \<times> llist_polynomial) nres\<close> where
  \<open>mop_dest_extension step = do {
     ASSERT (is_Extension step);
     RETURN (dest_extension step)
   }\<close>

definition mop_dest_del :: \<open>pac_step_hol \<Rightarrow> nat nres\<close> where
  \<open>mop_dest_del step = do {
     ASSERT (is_Del step);
     RETURN (dest_del step)
   }\<close>

lemma dest_add_hnr[sepref_fr_rules]:
  \<open>(dest_add_impl, mop_dest_add)
    \<in> pac_step_assn\<^sup>d \<rightarrow>\<^sub>a si64_assn \<times>\<^sub>a si64_assn \<times>\<^sub>a si64_assn \<times>\<^sub>a polynomial_assn\<close>
  unfolding dest_add_impl_def mop_dest_add_def dest_add_def
  apply sepref_to_hoare
  apply (case_tac x; simp_all add: refine_pw_simps)
  by (vcg; auto simp: step_pure_reassembly)

lemma dest_mult_hnr[sepref_fr_rules]:
  \<open>(dest_mult_impl, mop_dest_mult)
    \<in> pac_step_assn\<^sup>d \<rightarrow>\<^sub>a si64_assn \<times>\<^sub>a polynomial_assn \<times>\<^sub>a si64_assn \<times>\<^sub>a polynomial_assn\<close>
  unfolding dest_mult_impl_def mop_dest_mult_def dest_mult_def
  apply sepref_to_hoare
  apply (case_tac x; simp_all add: refine_pw_simps)
  by (vcg; auto simp: step_pure_reassembly)

lemma dest_extension_hnr[sepref_fr_rules]:
  \<open>(dest_extension_impl, mop_dest_extension)
    \<in> pac_step_assn\<^sup>d \<rightarrow>\<^sub>a si64_assn \<times>\<^sub>a strl_assn' \<times>\<^sub>a polynomial_assn\<close>
  unfolding dest_extension_impl_def mop_dest_extension_def dest_extension_def
  apply sepref_to_hoare
  apply (case_tac x; simp_all add: refine_pw_simps)
  by (vcg; auto simp: step_pure_reassembly)

lemma dest_del_hnr[sepref_fr_rules]:
  \<open>(dest_del_impl, mop_dest_del) \<in> pac_step_assn\<^sup>d \<rightarrow>\<^sub>a si64_assn\<close>
  unfolding dest_del_impl_def mop_dest_del_def dest_del_def
  apply sepref_to_hoare
  apply (case_tac x; simp_all add: refine_pw_simps)
  by (vcg; auto simp: step_pure_reassembly)

sepref_register mop_dest_add mop_dest_mult mop_dest_extension mop_dest_del

section \<open>Free\<close>

context begin
interpretation llvm_prim_arith_setup + llvm_prim_ctrl_setup .

definition pac_step_free :: \<open>pac_step_conc \<Rightarrow> unit llM\<close> where [llvm_code]:
  \<open>pac_step_free \<equiv> \<lambda>(tag, s1i, s2i, nii, multpi, resi, vari).
     llc_if (ll_cmp'_eq tag 0) (poly.cl_free resi)
     (llc_if (ll_cmp'_eq tag 1) (doM { poly.cl_free multpi; poly.cl_free resi })
     (llc_if (ll_cmp'_eq tag 2) (doM { strl.cl_free vari; poly.cl_free resi })
       (Mreturn ())))\<close>

lemma pac_step_assn_mk_free[sepref_frame_free_rules]: \<open>MK_FREE pac_step_assn pac_step_free\<close>
  apply (rule MK_FREEI)
  subgoal for a c
    unfolding pac_step_free_def ll_cmp'_eq_def
    by (cases a; cases c rule: prod_cases7; simp;
        vcg; auto simp: step_pure_reassembly to_bool_from_bool)
  done

end

interpretation pstep: freeable_assn pac_step_assn pac_step_free
  by unfold_locales (rule pac_step_assn_mk_free)

end
