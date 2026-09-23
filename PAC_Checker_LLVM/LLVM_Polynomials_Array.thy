theory LLVM_Polynomials_Array
  imports LLVM_Polynomials PAC_Checker_Synthesis More_EOArray
begin

text \<open>Array-string variants of the polynomial refinement targets of
  \<open>LLVM_Polynomials\<close>: variable names are \<open>stra_assn\<close> (contiguous arrays, as
  handed over by the C parser) instead of \<open>strl_assn'\<close> (linked lists). The
  efficient shared checker works on these targets; the original checker keeps
  the list-string targets.\<close>

section \<open>Monomials (variable lists)\<close>

abbreviation \<open>monoma_assn \<equiv> cl_assn' stra_assn\<close>
lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure monoma_assn]

text \<open>\<open>stra\<close> (\<open>More_EOArray\<close>) provides the copyable instance of \<open>stra_assn\<close> with the
  exportable free \<open>stra_free\<close>, \<open>strla_ls\<close> (\<open>LLVM_String\<close>) the linorder instance; the
  comparison environment for sorting is added here.\<close>

interpretation monoma: cmp_env_impl
  \<open>(\<le>)\<close> \<open>stra_assn\<close> \<open>stra_free\<close> \<open>list_le_impl\<close>
  apply unfold_locales
  apply (rule stra_le_hnr | auto)+
  done

lemmas monoma_less_hnr[sepref_fr_rules] = strla_ls.cl_less_hnr[unfolded list_lt_less]
lemmas monoma_le_hnr[sepref_fr_rules] = strla_ls.cl_le_hnr[unfolded list_le_less_eq]

lemma monomla_freeable: \<open>freeable_assn (cl_assn' stra_assn) stra.cl_free\<close>
  by unfold_locales (rule stra.cl_assn_free)

lemmas [llvm_code] =
  freeable_assn.cl_free_def[OF monomla_freeable]
  freeable_assn.cl_hd\<^sub>d_def[OF monomla_freeable]

experiment
begin

sepref_definition monoma_empty_test is \<open>uncurry0 (RETURN [])\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a monoma_assn\<close>
  by sepref

sepref_definition monoma_lt_test is \<open>uncurry (RETURN oo (<))\<close>
  :: \<open>monoma_assn\<^sup>k *\<^sub>a monoma_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

sepref_definition monoma_le_test is \<open>uncurry (RETURN oo (\<le>))\<close>
  :: \<open>monoma_assn\<^sup>k *\<^sub>a monoma_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

sepref_definition monoma_eq_test is \<open>uncurry (RETURN oo (=))\<close>
  :: \<open>monoma_assn\<^sup>k *\<^sub>a monoma_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

sepref_definition monoma_free_test is
  \<open>\<lambda>m. do { mop_free m; RETURN (0::nat) }\<close>
  :: \<open>monoma_assn\<^sup>d \<rightarrow>\<^sub>a snat_assn' TYPE(64)\<close>
  apply (annot_snat_const "TYPE(64)")
  by sepref

sepref_definition monoma_copy_test is \<open>RETURN o COPY\<close>
  :: \<open>monoma_assn\<^sup>k \<rightarrow>\<^sub>a monoma_assn\<close>
  by sepref

end

section \<open>Monomials with coefficient\<close>

abbreviation \<open>monomiala_assn \<equiv> monoma_assn \<times>\<^sub>a sbi_assn\<close>
lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure monomiala_assn]

type_synonym monoma_conc = \<open>stra_conc node ptr\<close>
type_synonym monomiala_conc = \<open>monoma_conc \<times> sbi_conc\<close>
type_synonym polya_conc = \<open>monomiala_conc node ptr\<close>

definition mnmla_free :: \<open>monomiala_conc \<Rightarrow> unit llM\<close> where[llvm_code]:
  \<open>mnmla_free \<equiv> \<lambda>(m, c). doM { stra.cl_free m; sbi_free c }\<close>

lemma mnmla_free_rule[sepref_frame_free_rules]: \<open>MK_FREE monomiala_assn mnmla_free\<close>
  unfolding mnmla_free_def
  by (rule mk_free_pair[OF stra.cl_assn_free sbi_free_rule])

definition mnmla_copy :: \<open>monomiala_conc \<Rightarrow> monomiala_conc llM\<close> where [llvm_code]:
  \<open>mnmla_copy \<equiv> \<lambda>(m, c). doM { m' \<leftarrow> stra.cl_copy m; c' \<leftarrow> sbi_copy c; Mreturn (m', c')}\<close>

lemma mnmla_copy_rule[vcg_rules]: \<open>llvm_htriple
  (monomiala_assn x c) (mnmla_copy c) (\<lambda>r. monomiala_assn x c ** monomiala_assn x r)\<close>
  unfolding mnmla_copy_def
  apply (cases x; cases c; simp only: prod_assn_pair_conv prod.case)
  by vcg

lemma mnmla_copy_rule'[vcg_rules]: \<open>llvm_htriple
  (monoma_assn m mi ** sbi_assn n ni) (mnmla_copy (mi, ni))
  (\<lambda>r. monoma_assn m mi ** sbi_assn n ni ** monomiala_assn (m, n) r)\<close>
  using mnmla_copy_rule[of \<open>(m, n)\<close> \<open>(mi, ni)\<close>] by simp

lemmas mnmla_copy_rule''[vcg_rules] = mnmla_copy_rule'[unfolded pure_def]

lemma mnmla_copy_hnr[sepref_fr_rules]:
  \<open>(mnmla_copy, RETURN o COPY) \<in> monomiala_assn\<^sup>k \<rightarrow>\<^sub>a monomiala_assn\<close>
  by (sepref_to_hoare; vcg)

lemma mnmla_copy_is_copy[sepref_gen_algo_rules]:
  \<open>GEN_ALGO mnmla_copy (is_copy monomiala_assn)\<close>
  unfolding GEN_ALGO_def is_copy_def
  by (rule mnmla_copy_hnr)

definition monomiala_le_impl' :: \<open>monomiala_conc \<Rightarrow> monomiala_conc \<Rightarrow> 1 word llM\<close> where[llvm_code]:
  \<open>monomiala_le_impl' \<equiv> \<lambda>pii qii. doM {
    let (pm,pn) = pii;
    let (qm,qn) = qii;
    r \<leftarrow> strla_ls.cl_le pm qm;
    Mreturn r
  }\<close>

lemma monomiala_le_rule[vcg_rules]:
  \<open>llvm_htriple
    (monomiala_assn p pii ** monomiala_assn q qii)
    (monomiala_le_impl' pii qii)
    (\<lambda>r. monomiala_assn p pii ** monomiala_assn q qii ** bool1_assn (monomial_le p q) r)\<close>
  unfolding monomiala_le_impl'_def monomial_le_def
  supply [simp] = list_le_less_eq
  apply (cases p; cases q; cases pii; cases qii; simp)
  by vcg

lemma monomiala_le_hnr[sepref_fr_rules]:
  \<open>(uncurry monomiala_le_impl', uncurry (RETURN oo monomial_le))
  \<in> monomiala_assn\<^sup>k *\<^sub>a monomiala_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding monomiala_le_impl'_def monomial_le_def
  supply [simp] = list_le_less_eq pure_def
  by (sepref_to_hoare; vcg)

definition mnmla_eq_impl' :: \<open>monomiala_conc \<Rightarrow> monomiala_conc \<Rightarrow> 1 word llM\<close> where[llvm_code]:
  \<open>mnmla_eq_impl' \<equiv> \<lambda>pii qii. doM {
    let (pm,pn) = pii;
    let (qm,qn) = qii;
    r \<leftarrow> strla_ls.cl_eq pm qm;
    llc_if r (signed_big_int_eq_impl pn qn) (Mreturn 0)
  }\<close>

context begin
interpretation llvm_prim_ctrl_setup .

lemma mnmla_eq_hnr[sepref_fr_rules]:
  \<open>(uncurry mnmla_eq_impl', uncurry (RETURN oo (=)))
  \<in> monomiala_assn\<^sup>k *\<^sub>a monomiala_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding mnmla_eq_impl'_def
  supply [vcg_rules] = hfref_htriple_k2[OF signed_big_int_eq_impl_hnr]
  supply [simp] = pure_def bool1_rel_def bool.rel_def in_br_conv
  by (sepref_to_hoare; vcg)

end

section \<open>Polynomials\<close>

abbreviation \<open>polynomiala_assn \<equiv> cl_assn' monomiala_assn\<close>
lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure polynomiala_assn]

interpretation polya: copyable_assn \<open>monomiala_assn\<close> \<open>mnmla_free\<close> \<open>mnmla_copy\<close>
  apply unfold_locales
  subgoal by (rule mnmla_free_rule)
  subgoal by (rule mnmla_copy_hnr)
  done

interpretation polya: cmp_env_impl \<open>monomial_le\<close> \<open>monomiala_assn\<close> \<open>mnmla_free\<close> \<open>monomiala_le_impl'\<close>
  apply unfold_locales
  apply (rule monomiala_le_hnr | auto simp: monomial_le_def)+
  done

interpretation polya: eq_assn \<open>monomiala_assn\<close> \<open>mnmla_eq_impl'\<close>
  by unfold_locales (rule mnmla_eq_hnr)

lemma polyla_freeable: \<open>freeable_assn (cl_assn' monomiala_assn) polya.cl_free\<close>
  by unfold_locales (rule polya.cl_assn_free)

lemmas [llvm_code] =
  freeable_assn.cl_free_def[OF polyla_freeable]
  freeable_assn.cl_hd\<^sub>d_def[OF polyla_freeable]

experiment
begin

sepref_definition polynomiala_empty_impl is \<open>uncurry0 (RETURN [])\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a polynomiala_assn\<close>
  by sepref

sepref_definition polynomiala_eq_test is \<open>uncurry (RETURN oo (=))\<close>
  :: \<open>polynomiala_assn\<^sup>k *\<^sub>a polynomiala_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

end

section \<open>Finite maps of polynomials\<close>

interpretation polysa: boxed_copying_pmap
  \<open>polynomiala_assn\<close> \<open>polya.cl_free\<close> \<open>polya.cl_copy\<close>
  apply unfold_locales
  subgoal by (rule polya.cl_assn_free)
  subgoal by (rule polya.cl_copy_hnr)
  done

abbreviation polysa_assn where
  \<open>polysa_assn \<equiv> hr_comp (hr_comp polysa.bx.pmap_assn' opt_list_map_rel) map_fmap_rel\<close>

lemma polysa_assn_intf[intf_of_assn]:
  \<open>intf_of_assn polysa_assn TYPE((nat, (char list list \<times> int) list) f_map)\<close>
  by simp

lemmas fmapa_empty_hnr[sepref_fr_rules] =
  polysa.bx.pmap_empty_hnr2[FCOMP fmempty_empty, unfolded op_fmap_empty_def[symmetric]]

lemmas fmapa_delete_hnr[sepref_fr_rules] =
  polysa.bx.pmap_delete_hnr2[FCOMP fmdrop_set_None]

lemmas fmapa_update_hnr[sepref_fr_rules] =
  polysa.bx.pmap_update_hnr2[FCOMP map_upd_fmupd]

lemmas fmapa_lookup_hnr[sepref_fr_rules] =
  polysa.bx.cpmap_lookup_hnr2[FCOMP op_map_lookup_fmlookup]

lemma polysa_assn_free[sepref_frame_free_rules]:
  \<open>MK_FREE polysa_assn polysa.bx.pmap_free\<close>
  by (intro MK_FREE_hrcompI polysa.bx.pmap_free_rule)

lemmas fmapa_contains_key_hnr[sepref_fr_rules] =
  polysa.bx.pmap_contains_key_hnr2[FCOMP map_fmap_contains_key]

lemmas fmapa_the_lookup_hnr[sepref_fr_rules] =
  polysa.bx.cpmap_the_lookup_hnr2[FCOMP op_the_lookup_refine]

lemmas upper_bound_on_doma_hnr[sepref_fr_rules] =
  polysa.bx.pmap_len_hnr2[FCOMP map_fmap_dom_ub]

section \<open>Normalisation\<close>

text \<open>Array-string instances of the normalisation chain of \<open>PAC_Checker_Init\<close>. The
  abstract merge sorts (\<open>monom.msort\<close>, \<open>poly.msort\<close>) only depend on the comparison,
  so they are shared with the list-string instance; only the implementations differ.\<close>

sepref_def merge_coeffs0a_impl
  is \<open>RETURN o merge_coeffs0\<close>
  :: \<open>polynomiala_assn\<^sup>d \<rightarrow>\<^sub>a polynomiala_assn\<close>
  unfolding merge_coeffs1_correct[symmetric]
  unfolding merge_coeffs1_def mc_body_def ls_emp add_poly_l2_def apl2_body_def
  by sepref

lemmas sort_coeffa_impl[sepref_fr_rules] =
  monoma.msort_impl.refine[FCOMP msort_refine_sort_coeff]

sepref_def sort_all_coeffsa_impl is \<open>sort_all_coeffs\<close>
  :: \<open>polynomiala_assn\<^sup>d \<rightarrow>\<^sub>a polynomiala_assn\<close>
  unfolding sort_all_coeffs_alt
  by sepref

lemmas sort_polya_hnr[sepref_fr_rules] =
  polya.msort_impl.refine[FCOMP poly_msort_fref]

sepref_def fully_normalize_polya_impl
  is \<open>full_normalize_poly\<close>
  :: \<open>polynomiala_assn\<^sup>d \<rightarrow>\<^sub>a polynomiala_assn\<close>
  unfolding full_normalize_poly_def
  by sepref

section \<open>Printing\<close>

text \<open>Appending an array string to an output buffer (\<open>strlt_assn\<close>): the array-string
  implementation of \<open>cl_to_clt\<close>.\<close>

definition stra_to_clt_nres :: \<open>string \<Rightarrow> string nres\<close> where
  \<open>stra_to_clt_nres xs = doN {
    (r, _) \<leftarrow> WHILEIT
      (\<lambda>(r, i). i \<le> length xs \<and> r = take i xs)
      (\<lambda>(_, i). i < length xs)
      (\<lambda>(r, i). doN {
        ASSERT (i < length xs);
        let c = xs ! i;
        RETURN (r @ [c], i + 1)
      })
      (op_clt_empty, 0);
    RETURN r
  }\<close>

lemma stra_to_clt_nres_le: \<open>stra_to_clt_nres xs \<le> RETURN (cl_to_clt xs)\<close>
  unfolding stra_to_clt_nres_def cl_to_clt_id
  apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(_, i). length xs - i)\<close>])
  by (auto simp: take_Suc_conv_app_nth)

lemma stra_to_clt_nres_correct:
  \<open>(stra_to_clt_nres, RETURN o cl_to_clt) \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: stra_to_clt_nres_le)

sepref_def stra_to_clt_impl is \<open>stra_to_clt_nres\<close>
  :: \<open>stra_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding stra_to_clt_nres_def
  apply (annot_snat_const "TYPE(64)")
  by sepref

lemmas stra_to_clt_hnr[sepref_fr_rules] =
  stra_to_clt_impl.refine[FCOMP stra_to_clt_nres_correct]

sepref_def print_monoma_inner_impl is \<open>uncurry (RETURN oo print_monom_inner)\<close>
  :: \<open>strlt_assn\<^sup>d *\<^sub>a stra_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding print_monom_inner_def
  by sepref

definition print_monoma_impl where[llvm_code]:
  \<open>print_monoma_impl \<equiv> \<lambda>m. doM {e \<leftarrow> clt_empty; cl_fold' print_monoma_inner_impl e m}\<close>

lemma print_monoma_rule: \<open>llvm_htriple
  (monoma_assn m mi)
  (print_monoma_impl mi)
  (\<lambda>r. monoma_assn m mi ** strlt_assn (print_monom m) r)\<close>
proof -
  have INNER_vcg: \<open>llvm_htriple
    (strlt_assn acc acci ** stra_assn t ti)
    (print_monoma_inner_impl acci ti)
    (\<lambda>r. strlt_assn (print_monom_inner acc t) r ** stra_assn t ti)\<close> for acc acci t ti
    apply (rule htriple_ent_post[OF _ hfref_htriple_d1_k2[OF print_monoma_inner_impl.refine]])
    by (simp add: sep_conj_aci)
  show ?thesis
    unfolding print_monoma_impl_def
    supply [vcg_rules] = cl_fold'_rule[where R="strlt_assn" and A="stra_assn"
      and f=print_monoma_inner_impl and fa=print_monom_inner,
      OF INNER_vcg]
    supply [simp] = print_monom_def
    by vcg
qed

lemma print_monoma_hnr[sepref_fr_rules]:
  \<open>(print_monoma_impl, (RETURN o print_monom))
  \<in> monoma_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  apply (sepref_to_hoare)
  supply [vcg_rules] = print_monoma_rule[unfolded pure_def]
  by vcg

sepref_def mnmla_print_impl is \<open>RETURN o mnml_print\<close>
  :: \<open>monomiala_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding mnml_print_def
  by sepref

sepref_def polya_print_inner_impl is \<open>uncurry (RETURN oo poly_print_inner)\<close>
  :: \<open>strlt_assn\<^sup>d *\<^sub>a monomiala_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding poly_print_inner_def
  by sepref

definition polya_print_impl where[llvm_code]:
  \<open>polya_print_impl \<equiv> \<lambda>ps. doM {e \<leftarrow> clt_empty; cl_fold' polya_print_inner_impl e ps}\<close>

lemma polya_print_rule: \<open>llvm_htriple
  (polynomiala_assn ps psi)
  (polya_print_impl psi)
  (\<lambda>r. polynomiala_assn ps psi ** strlt_assn (poly_print ps) r)\<close>
proof -
  have INNER_vcg: \<open>llvm_htriple
    (strlt_assn acc acci ** monomiala_assn p pi)
    (polya_print_inner_impl acci pi)
    (\<lambda>r. strlt_assn (poly_print_inner acc p) r ** monomiala_assn p pi)\<close> for acc acci p pi
    apply (rule htriple_ent_post[OF _ hfref_htriple_d1_k2[OF polya_print_inner_impl.refine]])
    by (simp add: sep_conj_aci)
  show ?thesis
    unfolding polya_print_impl_def
    supply [vcg_rules] = cl_fold'_rule[where R="strlt_assn" and A="monomiala_assn"
      and f=polya_print_inner_impl and fa=poly_print_inner,
      OF INNER_vcg]
    supply [simp] = poly_print_def
    by vcg
qed

lemma polya_print_hnr[sepref_fr_rules]:
  \<open>(polya_print_impl, (RETURN o poly_print))
  \<in> polynomiala_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  apply (sepref_to_hoare)
  supply [vcg_rules] = polya_print_rule[unfolded pure_def]
  by vcg

end
