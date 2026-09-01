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

section \<open>Distcriminators\<close>

definition is_CL_impl :: \<open>lpac_step_conc \<Rightarrow> 1 word llM\<close> where [llvm_code, llvm_inline]:
  \<open>is_CL_impl \<equiv> \<lambda>(tag, idc, resi, srcsi, vari). Mreturn (ll_cmp'_eq tag 0)\<close>

definition is_Extension_impl :: \<open>lpac_step_conc \<Rightarrow> 1 word llM\<close> where [llvm_code, llvm_inline]:
  \<open>is_Extension_impl \<equiv> \<lambda>(tag, idc, resi, srcsi, vari). Mreturn (ll_cmp'_eq tag 1)\<close>

definition is_Del_impl :: \<open>lpac_step_conc \<Rightarrow> 1 word llM\<close> where [llvm_code, llvm_inline]:
  \<open>is_Del_impl \<equiv> \<lambda>(tag, idc, resi, srcsi, vari). Mreturn (ll_cmp'_eq tag 2)\<close>

lemma lpac_step_assn_tag:
  \<open>pure_part (lpac_step_assn step (tag, idc, resi, srcsi, vari)) \<Longrightarrow>
    (tag = 0) = is_CL step \<and> (tag = 1) = is_Extension step \<and> (tag = 2) = is_Del step\<close>
  by (cases step; auto simp: lpac_step_assn_def dest!: pure_part_split_conj)

lemmas lpac_step_assn_tagD = pure_partI[THEN lpac_step_assn_tag]

lemma is_CL_hnr[sepref_fr_rules]:
  \<open>(is_CL_impl, RETURN o is_CL) \<in> lpac_step_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding is_CL_impl_def ll_cmp'_eq_def
  apply (sepref_to_hoare;vcg)
  by (auto simp: step_pure_reassembly bool1_rel_def bool.rel_def in_br_conv
    dest!: lpac_step_assn_tagD)

lemma is_Extension_hnr[sepref_fr_rules]:
  \<open>(is_Extension_impl, RETURN o is_Extension) \<in> lpac_step_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding is_Extension_impl_def ll_cmp'_eq_def
  apply (sepref_to_hoare;vcg)
  by (auto simp: step_pure_reassembly bool1_rel_def bool.rel_def in_br_conv
    dest!: lpac_step_assn_tagD)

lemma is_Del_hnr[sepref_fr_rules]:
  \<open>(is_Del_impl, RETURN o is_Del) \<in> lpac_step_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding is_Del_impl_def ll_cmp'_eq_def
  apply (sepref_to_hoare;vcg)
  by (auto simp: step_pure_reassembly bool1_rel_def bool.rel_def in_br_conv
    dest!: lpac_step_assn_tagD)

section \<open>Destructors\<close>

definition dest_cl :: \<open>lpac_step_hol \<Rightarrow> (llist_polynomial \<times> nat) list \<times> nat \<times> llist_polynomial\<close>
  where
  \<open>dest_cl step = (pac_srcs step, new_id step, pac_res step)\<close>

definition dest_lextension :: \<open>lpac_step_hol \<Rightarrow> nat \<times> string \<times> llist_polynomial\<close> where
  \<open>dest_lextension step = (new_id step, new_var step, pac_res step)\<close>

definition dest_ldel :: \<open>lpac_step_hol \<Rightarrow> nat\<close> where
  \<open>dest_ldel step = pac_src1 step\<close>

definition dest_cl_impl :: \<open>lpac_step_conc \<Rightarrow> (srcs_conc \<times> 64 word \<times> poly_conc) llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>dest_cl_impl \<equiv> \<lambda>(tag, idc, resi, srcsi, vari). Mreturn (srcsi, idc, resi)\<close>

definition dest_lextension_impl :: \<open>lpac_step_conc \<Rightarrow> (64 word \<times> strl_conc \<times> poly_conc) llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>dest_lextension_impl \<equiv> \<lambda>(tag, idc, resi, srcsi, vari). Mreturn (idc, vari, resi)\<close>

definition dest_ldel_impl :: \<open>lpac_step_conc \<Rightarrow> 64 word llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>dest_ldel_impl \<equiv> \<lambda>(tag, idc, resi, srcsi, vari). Mreturn idc\<close>

definition mop_dest_cl ::
  \<open>lpac_step_hol \<Rightarrow> ((llist_polynomial \<times> nat) list \<times> nat \<times> llist_polynomial) nres\<close> where
  \<open>mop_dest_cl step = do {
     ASSERT (is_CL step);
     RETURN (dest_cl step)
   }\<close>

definition mop_dest_lextension :: \<open>lpac_step_hol \<Rightarrow> (nat \<times> string \<times> llist_polynomial) nres\<close> where
  \<open>mop_dest_lextension step = do {
     ASSERT (is_Extension step);
     RETURN (dest_lextension step)
   }\<close>

definition mop_dest_ldel :: \<open>lpac_step_hol \<Rightarrow> nat nres\<close> where
  \<open>mop_dest_ldel step = do {
     ASSERT (is_Del step);
     RETURN (dest_ldel step)
   }\<close>

lemma dest_cl_hnr[sepref_fr_rules]:
  \<open>(dest_cl_impl, mop_dest_cl)
    \<in> lpac_step_assn\<^sup>d \<rightarrow>\<^sub>a srcs_assn \<times>\<^sub>a si64_assn \<times>\<^sub>a polynomial_assn\<close>
  unfolding dest_cl_impl_def mop_dest_cl_def dest_cl_def
  apply sepref_to_hoare
  apply (case_tac x; simp_all add: refine_pw_simps)
  by (vcg; auto simp: step_pure_reassembly)

lemma dest_lextension_hnr[sepref_fr_rules]:
  \<open>(dest_lextension_impl, mop_dest_lextension)
    \<in> lpac_step_assn\<^sup>d \<rightarrow>\<^sub>a si64_assn \<times>\<^sub>a strl_assn' \<times>\<^sub>a polynomial_assn\<close>
  unfolding dest_lextension_impl_def mop_dest_lextension_def dest_lextension_def
  apply sepref_to_hoare
  apply (case_tac x; simp_all add: refine_pw_simps)
  by (vcg; auto simp: step_pure_reassembly)

lemma dest_ldel_hnr[sepref_fr_rules]:
  \<open>(dest_ldel_impl, mop_dest_ldel) \<in> lpac_step_assn\<^sup>d \<rightarrow>\<^sub>a si64_assn\<close>
  unfolding dest_ldel_impl_def mop_dest_ldel_def dest_ldel_def
  apply sepref_to_hoare
  apply (case_tac x; simp_all add: refine_pw_simps)
  by (vcg; auto simp: step_pure_reassembly)

sepref_register mop_dest_cl mop_dest_lextension mop_dest_ldel

section \<open>Free\<close>

text \<open>The sources of a linear combination are a list of (polynomial, index) pairs; only
  the polynomial component owns memory.\<close>

text \<open>No \<open>llvm_inline\<close> here: the constant appears as the \<open>afree\<close> argument of
  \<open>freeable_assn.cl_free\<close>, and inlining it there would break the code-equation
  lookup for the interpreted \<open>srcs.cl_free\<close>.\<close>
definition srcs_pair_free :: \<open>poly_conc \<times> 64 word \<Rightarrow> unit llM\<close>
  where [llvm_code]:
  \<open>srcs_pair_free \<equiv> \<lambda>(pi, _). doM { poly.cl_free pi; Mreturn () }\<close>

lemma srcs_pair_free_mk_free:
  \<open>MK_FREE (polynomial_assn \<times>\<^sub>a si64_assn) srcs_pair_free\<close>
  using mk_free_pair[OF poly.cl_assn_free mk_free_pure]
  unfolding srcs_pair_free_def by simp

interpretation srcs: freeable_assn \<open>polynomial_assn \<times>\<^sub>a si64_assn\<close> srcs_pair_free
  by unfold_locales (rule srcs_pair_free_mk_free)

context begin
interpretation llvm_prim_arith_setup + llvm_prim_ctrl_setup .

definition lpac_step_free :: \<open>lpac_step_conc \<Rightarrow> unit llM\<close> where [llvm_code]:
  \<open>lpac_step_free \<equiv> \<lambda>(tag, idc, resi, srcsi, vari).
     llc_if (ll_cmp'_eq tag 0) (doM { srcs.cl_free srcsi; poly.cl_free resi })
     (llc_if (ll_cmp'_eq tag 1) (doM { strl.cl_free vari; poly.cl_free resi })
       (Mreturn ()))\<close>

lemma lpac_step_assn_mk_free[sepref_frame_free_rules]:
  \<open>MK_FREE lpac_step_assn lpac_step_free\<close>
  apply (rule MK_FREEI)
  subgoal for a c
    unfolding lpac_step_free_def ll_cmp'_eq_def
    by (cases a; cases c rule: prod_cases5; simp;
        vcg; auto simp: step_pure_reassembly to_bool_from_bool)
  done

end

interpretation lpstep: freeable_assn lpac_step_assn lpac_step_free
  by unfold_locales (rule lpac_step_assn_mk_free)

end
