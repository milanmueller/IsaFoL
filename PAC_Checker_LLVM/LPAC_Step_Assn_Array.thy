theory LPAC_Step_Assn_Array
  imports LPAC_Step_Assn LLVM_Polynomials_Array
begin

text \<open>Array-string variant of \<open>LPAC_Step_Assn\<close>: the result polynomials use
  \<open>polynomiala_assn\<close> and the extension variable is a \<open>stra_assn\<close>. The abstract
  operations (\<open>mop_dest_cl\<close>, \<open>is_CL\<close>, \<dots>) are shared with the list variant; only the
  refinement rules differ. The producers are not registered for \<open>sepref\<close> (steps are only
  built by the C import), so the two step assertions do not compete.\<close>

type_synonym srcsa_conc = \<open>(polya_conc \<times> 64 word) cl_list\<close>

type_synonym lpac_stepa_conc =
  \<open>8 word \<times> 64 word \<times> polya_conc \<times> srcsa_conc \<times> stra_conc\<close>
(* tag    \<times> id      \<times> res poly  \<times> lin-comb srcs \<times> var (for ext) *)

abbreviation \<open>srcsa_assn \<equiv> cl_assn' (polynomiala_assn \<times>\<^sub>a si64_assn)\<close>

definition lpac_stepa_assn :: \<open>lpac_step_hol \<Rightarrow> lpac_stepa_conc \<Rightarrow> assn\<close> where
  \<open>lpac_stepa_assn step \<equiv> \<lambda>(tag, idc, resi, srcsi, vari). case step of
  CL srcs ni res     \<Rightarrow> \<up>(tag = 0) ** srcsa_assn srcs srcsi ** si64_assn ni idc
                                  ** polynomiala_assn res resi
| Extension ni v res \<Rightarrow> \<up>(tag = 1) ** si64_assn ni idc ** stra_assn v vari
                                  ** polynomiala_assn res resi
| Del s1             \<Rightarrow> \<up>(tag = 2) ** si64_assn s1 idc\<close>

lemma lpac_stepa_assn_CL[simp]:
  \<open>lpac_stepa_assn (CL srcs ni res) (tag, idc, resi, srcsi, vari) =
    (\<up>(tag = 0) ** srcsa_assn srcs srcsi ** si64_assn ni idc
     ** polynomiala_assn res resi)\<close>
  unfolding lpac_stepa_assn_def by simp

lemma lpac_stepa_assn_Extension[simp]:
  \<open>lpac_stepa_assn (Extension ni v res) (tag, idc, resi, srcsi, vari) =
    (\<up>(tag = 1) ** si64_assn ni idc ** stra_assn v vari
     ** polynomiala_assn res resi)\<close>
  unfolding lpac_stepa_assn_def by simp

lemma lpac_stepa_assn_Del[simp]:
  \<open>lpac_stepa_assn (Del s1) (tag, idc, resi, srcsi, vari) =
    (\<up>(tag = 2) ** si64_assn s1 idc)\<close>
  unfolding lpac_stepa_assn_def by simp

section \<open>Producers\<close>

definition mk_cla_impl :: \<open>srcsa_conc \<Rightarrow> 64 word \<Rightarrow> polya_conc \<Rightarrow> lpac_stepa_conc llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>mk_cla_impl srcsi nii resi \<equiv> Mreturn (0, nii, resi, srcsi, init)\<close>

definition mk_lexta_impl :: \<open>64 word \<Rightarrow> stra_conc \<Rightarrow> polya_conc \<Rightarrow> lpac_stepa_conc llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>mk_lexta_impl nii vi resi \<equiv> Mreturn (1, nii, resi, init, vi)\<close>

definition mk_ldela_impl :: \<open>64 word \<Rightarrow> lpac_stepa_conc llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>mk_ldela_impl s1i \<equiv> Mreturn (2, s1i, init, init, init)\<close>

lemma mk_cla_impl_hnr:
  \<open>(uncurry2 mk_cla_impl, uncurry2 (RETURN ooo CL))
    \<in> srcsa_assn\<^sup>d *\<^sub>a si64_assn\<^sup>k *\<^sub>a polynomiala_assn\<^sup>d \<rightarrow>\<^sub>a lpac_stepa_assn\<close>
  unfolding mk_cla_impl_def
  apply sepref_to_hoare
  by (vcg; auto simp: step_pure_reassembly)

lemma mk_lexta_impl_hnr:
  \<open>(uncurry2 mk_lexta_impl, uncurry2 (RETURN ooo Extension))
    \<in> si64_assn\<^sup>k *\<^sub>a stra_assn\<^sup>d *\<^sub>a polynomiala_assn\<^sup>d \<rightarrow>\<^sub>a lpac_stepa_assn\<close>
  unfolding mk_lexta_impl_def
  apply sepref_to_hoare
  by (vcg; auto simp: step_pure_reassembly)

lemma mk_ldela_impl_hnr:
  \<open>(mk_ldela_impl, RETURN o Del) \<in> si64_assn\<^sup>k \<rightarrow>\<^sub>a lpac_stepa_assn\<close>
  unfolding mk_ldela_impl_def
  apply sepref_to_hoare
  by (vcg; auto simp: step_pure_reassembly)

section \<open>Distcriminators\<close>

definition is_CLa_impl :: \<open>lpac_stepa_conc \<Rightarrow> 1 word llM\<close> where [llvm_code, llvm_inline]:
  \<open>is_CLa_impl \<equiv> \<lambda>(tag, idc, resi, srcsi, vari). Mreturn (ll_cmp'_eq tag 0)\<close>

definition is_Extensiona_impl :: \<open>lpac_stepa_conc \<Rightarrow> 1 word llM\<close> where [llvm_code, llvm_inline]:
  \<open>is_Extensiona_impl \<equiv> \<lambda>(tag, idc, resi, srcsi, vari). Mreturn (ll_cmp'_eq tag 1)\<close>

definition is_Dela_impl :: \<open>lpac_stepa_conc \<Rightarrow> 1 word llM\<close> where [llvm_code, llvm_inline]:
  \<open>is_Dela_impl \<equiv> \<lambda>(tag, idc, resi, srcsi, vari). Mreturn (ll_cmp'_eq tag 2)\<close>

lemma lpac_stepa_assn_tag:
  \<open>pure_part (lpac_stepa_assn step (tag, idc, resi, srcsi, vari)) \<Longrightarrow>
    (tag = 0) = is_CL step \<and> (tag = 1) = is_Extension step \<and> (tag = 2) = is_Del step\<close>
  by (cases step; auto simp: lpac_stepa_assn_def dest!: pure_part_split_conj)

lemmas lpac_stepa_assn_tagD = pure_partI[THEN lpac_stepa_assn_tag]

lemma is_CLa_hnr[sepref_fr_rules]:
  \<open>(is_CLa_impl, RETURN o is_CL) \<in> lpac_stepa_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding is_CLa_impl_def ll_cmp'_eq_def
  apply (sepref_to_hoare;vcg)
  by (auto simp: step_pure_reassembly bool1_rel_def bool.rel_def in_br_conv
    dest!: lpac_stepa_assn_tagD)

lemma is_Extensiona_hnr[sepref_fr_rules]:
  \<open>(is_Extensiona_impl, RETURN o is_Extension) \<in> lpac_stepa_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding is_Extensiona_impl_def ll_cmp'_eq_def
  apply (sepref_to_hoare;vcg)
  by (auto simp: step_pure_reassembly bool1_rel_def bool.rel_def in_br_conv
    dest!: lpac_stepa_assn_tagD)

lemma is_Dela_hnr[sepref_fr_rules]:
  \<open>(is_Dela_impl, RETURN o is_Del) \<in> lpac_stepa_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding is_Dela_impl_def ll_cmp'_eq_def
  apply (sepref_to_hoare;vcg)
  by (auto simp: step_pure_reassembly bool1_rel_def bool.rel_def in_br_conv
    dest!: lpac_stepa_assn_tagD)

section \<open>Destructors\<close>

definition dest_cla_impl :: \<open>lpac_stepa_conc \<Rightarrow> (srcsa_conc \<times> 64 word \<times> polya_conc) llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>dest_cla_impl \<equiv> \<lambda>(tag, idc, resi, srcsi, vari). Mreturn (srcsi, idc, resi)\<close>

definition dest_lextensiona_impl :: \<open>lpac_stepa_conc \<Rightarrow> (64 word \<times> stra_conc \<times> polya_conc) llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>dest_lextensiona_impl \<equiv> \<lambda>(tag, idc, resi, srcsi, vari). Mreturn (idc, vari, resi)\<close>

definition dest_ldela_impl :: \<open>lpac_stepa_conc \<Rightarrow> 64 word llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>dest_ldela_impl \<equiv> \<lambda>(tag, idc, resi, srcsi, vari). Mreturn idc\<close>

lemma dest_cla_hnr[sepref_fr_rules]:
  \<open>(dest_cla_impl, mop_dest_cl)
    \<in> lpac_stepa_assn\<^sup>d \<rightarrow>\<^sub>a srcsa_assn \<times>\<^sub>a si64_assn \<times>\<^sub>a polynomiala_assn\<close>
  unfolding dest_cla_impl_def mop_dest_cl_def dest_cl_def
  apply sepref_to_hoare
  apply (case_tac x; simp_all add: refine_pw_simps)
  by (vcg; auto simp: step_pure_reassembly)

lemma dest_lextensiona_hnr[sepref_fr_rules]:
  \<open>(dest_lextensiona_impl, mop_dest_lextension)
    \<in> lpac_stepa_assn\<^sup>d \<rightarrow>\<^sub>a si64_assn \<times>\<^sub>a stra_assn \<times>\<^sub>a polynomiala_assn\<close>
  unfolding dest_lextensiona_impl_def mop_dest_lextension_def dest_lextension_def
  apply sepref_to_hoare
  apply (case_tac x; simp_all add: refine_pw_simps)
  by (vcg; auto simp: step_pure_reassembly)

lemma dest_ldela_hnr[sepref_fr_rules]:
  \<open>(dest_ldela_impl, mop_dest_ldel) \<in> lpac_stepa_assn\<^sup>d \<rightarrow>\<^sub>a si64_assn\<close>
  unfolding dest_ldela_impl_def mop_dest_ldel_def dest_ldel_def
  apply sepref_to_hoare
  apply (case_tac x; simp_all add: refine_pw_simps)
  by (vcg; auto simp: step_pure_reassembly)

section \<open>Free\<close>

text \<open>The sources of a linear combination are a list of (polynomial, index) pairs; only
  the polynomial component owns memory.\<close>

text \<open>No \<open>llvm_inline\<close> here: the constant appears as the \<open>afree\<close> argument of
  \<open>freeable_assn.cl_free\<close>, and inlining it there would break the code-equation
  lookup for the interpreted \<open>srcsa.cl_free\<close>.\<close>
definition srcsa_pair_free :: \<open>polya_conc \<times> 64 word \<Rightarrow> unit llM\<close>
  where [llvm_code]:
  \<open>srcsa_pair_free \<equiv> \<lambda>(pi, _). doM { polya.cl_free pi; Mreturn () }\<close>

lemma srcsa_pair_free_mk_free:
  \<open>MK_FREE (polynomiala_assn \<times>\<^sub>a si64_assn) srcsa_pair_free\<close>
  using mk_free_pair[OF polya.cl_assn_free mk_free_pure]
  unfolding srcsa_pair_free_def by simp

interpretation srcsa: freeable_assn \<open>polynomiala_assn \<times>\<^sub>a si64_assn\<close> srcsa_pair_free
  by unfold_locales (rule srcsa_pair_free_mk_free)

context begin
interpretation llvm_prim_arith_setup + llvm_prim_ctrl_setup .

definition lpac_stepa_free :: \<open>lpac_stepa_conc \<Rightarrow> unit llM\<close> where [llvm_code]:
  \<open>lpac_stepa_free \<equiv> \<lambda>(tag, idc, resi, srcsi, vari).
     llc_if (ll_cmp'_eq tag 0) (doM { srcsa.cl_free srcsi; polya.cl_free resi })
     (llc_if (ll_cmp'_eq tag 1) (doM { stra_free vari; polya.cl_free resi })
       (Mreturn ()))\<close>

lemma lpac_stepa_assn_mk_free[sepref_frame_free_rules]:
  \<open>MK_FREE lpac_stepa_assn lpac_stepa_free\<close>
  apply (rule MK_FREEI)
  subgoal for a c
    unfolding lpac_stepa_free_def ll_cmp'_eq_def
    by (cases a; cases c rule: prod_cases5; simp;
        vcg; auto simp: step_pure_reassembly to_bool_from_bool)
  done

end

interpretation lpstepa: freeable_assn lpac_stepa_assn lpac_stepa_free
  by unfold_locales (rule lpac_stepa_assn_mk_free)

end
