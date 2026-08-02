theory LLVM_Polynomials
  imports LLVM_String BigInt_LLVM.LLVM_CodeGen_Signed IICF_PartialMap
begin

text \<open>This theory defines refinment targets for polynomials in LLVM.
  The HOL-datatype we want to refine is `llist_polynomial` (i.e.
  @{typ \<open>(char list list \<times> int) list\<close>}, c.f. `PAC_Polynomials_Term`).\<close>

term strl_assn
abbreviation \<open>monom_assn \<equiv> cl_assn' strl_assn'\<close>

interpretation monom: copy_free_context \<open>strl_assn'\<close> \<open>strl.cl_free\<close> \<open>strl.cl_copy\<close>
  apply unfold_locales
  subgoal by (rule strl.cl_assn_free)
  subgoal by (rule strl.cl_copy_is_copy)
  done

interpretation monom: linord_copying_list \<open>strl_assn'\<close> \<open>strl.cl_eq\<close> \<open>strl.cl_less\<close>
  apply unfold_locales
  subgoal by (rule strl.cl_eq_hnr)
  subgoal by (rule strl.cl_less_hnr[unfolded list_lt_less])
  done

sepref_register \<open>(=) :: char list list \<Rightarrow> char list list \<Rightarrow> bool\<close>
sepref_register \<open>(<) :: char list list \<Rightarrow> char list list \<Rightarrow> bool\<close>
sepref_register \<open>(\<le>) :: char list list \<Rightarrow> char list list \<Rightarrow> bool\<close>

lemmas monom_less_hnr[sepref_fr_rules] = monom.cl_less_hnr[unfolded list_lt_less]
lemmas monom_le_hnr[sepref_fr_rules] = monom.cl_le_hnr[unfolded list_le_less_eq]

experiment
begin

sepref_definition monom_lt_test is \<open>uncurry (RETURN oo (<))\<close>
  :: \<open>monom_assn\<^sup>k *\<^sub>a monom_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

sepref_definition monom_le_test is \<open>uncurry (RETURN oo (\<le>))\<close>
  :: \<open>monom_assn\<^sup>k *\<^sub>a monom_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

sepref_definition monom_eq_test is \<open>uncurry (RETURN oo (=))\<close>
  :: \<open>monom_assn\<^sup>k *\<^sub>a monom_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

lemma monom_mk_free: \<open>MK_FREE monom_assn monom.cl_free\<close>
  by (rule monom.cl_assn_free)

sepref_definition monom_free_test is
  \<open>\<lambda>m. do { mop_free m; RETURN (0::nat) }\<close>
  :: \<open>monom_assn\<^sup>d \<rightarrow>\<^sub>a snat_assn' TYPE(64)\<close>
  apply (annot_snat_const "TYPE(64)")
  by sepref

sepref_definition monom_len_test is
  \<open>\<lambda>m. do { ASSERT (length m < max_snat 64); RETURN (length m) }\<close>
  :: \<open>monom_assn\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(64)\<close>
  by sepref

sepref_definition monom_copy_test is \<open>RETURN o COPY\<close>
  :: \<open>monom_assn\<^sup>k \<rightarrow>\<^sub>a monom_assn\<close>
  by sepref

end

section \<open>Monomials\<close>
abbreviation \<open>monomial_assn \<equiv> monom_assn \<times>\<^sub>a sbi_assn\<close>
text \<open>Since for tuples, we can not instatiate the copy setup from the copying list,
  we need to do some ground work for freeing and copying monomials.\<close>

type_synonym monom_conc = \<open>8 word node ptr node ptr\<close>
type_synonym bi_conc = \<open>64 word \<times> 64 word \<times> 64 word ptr\<close>
type_synonym sbi_conc = \<open>bi_conc \<times> 1 word\<close>
type_synonym monomial_conc = \<open>monom_conc \<times> sbi_conc\<close>

text \<open>To copy an sbi, we have to define a copy function for `arl_assn`\<close>

(* TODO: Move? *)
definition arl_copy :: \<open>('a::llvm_rep, 'l::len2) array_list \<Rightarrow> ('a, 'l) array_list llM\<close> where[llvm_code]:
  \<open>arl_copy al \<equiv> doM {
    let (l, c, a) = al;
    al' \<leftarrow> narray_new TYPE('a) l;
    arraycpy al' a l;
    Mreturn (l, l, al')    
  }\<close>

lemma arl_copy_rule[vcg_rules]: \<open>llvm_htriple
  (\<upharpoonleft>arl_assn xs xsi) (arl_copy xsi) (\<lambda>r. \<upharpoonleft>arl_assn xs xsi ** \<upharpoonleft>arl_assn xs r)\<close>
  unfolding arl_copy_def arl_assn_def arl_assn'_def
  by vcg

definition sbi_copy :: \<open>sbi_conc \<Rightarrow> sbi_conc llM\<close> where[llvm_code, llvm_inline]:
  \<open>sbi_copy \<equiv> \<lambda>(ai, s). doM { ai' \<leftarrow> arl_copy ai; Mreturn (ai', s) }\<close>

lemma sbi_copy_hnr[sepref_fr_rules]: \<open>(sbi_copy, RETURN o COPY) \<in> sbi_assn\<^sup>k \<rightarrow>\<^sub>a sbi_assn\<close>
  unfolding sbi_copy_def sbi_assn_def al_assn_def hr_comp_def
  by (sepref_to_hoare; vcg)

(* TODO: Move? *)
lemma copy_hnr_to_rule:
  assumes \<open>(cp, RETURN o COPY) \<in> A\<^sup>k \<rightarrow>\<^sub>a A\<close>
  shows \<open>llvm_htriple (A a c) (cp c) (\<lambda>r. A a c ** A a r)\<close>
proof -
  have \<open>hn_refine (fst (A\<^sup>k) a c) (cp c) (snd (A\<^sup>k) a c)
      ((\<lambda>_. A) a) ((\<lambda>_ _. True) c) ((RETURN o COPY) a)\<close>
    by (rule hfrefD[OF assms]) simp_all
  then have R: \<open>hn_refine (A a c) (cp c) (A a c) A (\<lambda>_. True) (RETURN a)\<close>
    by simp
  show ?thesis
    apply (rule htriple_ent_post[OF _ hn_refineD[OF R]])
    subgoal
      by (auto simp: entails_def sep_algebra_simps pred_lift_extract_simps
          sep_conj_exists pw_le_iff refine_pw_simps)
    subgoal by simp
    done
qed

lemma sbi_copy_rule[vcg_rules]:
  \<open>llvm_htriple (sbi_assn n c) (sbi_copy c) (\<lambda>r. sbi_assn n c ** sbi_assn n r)\<close>
  by (rule copy_hnr_to_rule[OF sbi_copy_hnr])

definition mnml_free :: \<open>monomial_conc \<Rightarrow> unit llM\<close> where[llvm_code]:
  \<open>mnml_free \<equiv> \<lambda>(m, c). doM { monom.cl_free m; sbi_free c }\<close>

lemma mnml_free_rule[sepref_frame_free_rules]: \<open>MK_FREE monomial_assn mnml_free\<close>
  unfolding mnml_free_def
  by (rule mk_free_pair[OF monom.cl_assn_free sbi_free_rule])

definition mnml_copy :: \<open>monomial_conc \<Rightarrow> monomial_conc llM\<close> where [llvm_code, llvm_inline]:
  \<open>mnml_copy \<equiv> \<lambda>(m, c). doM { m' \<leftarrow> monom.cl_copy m; c' \<leftarrow> sbi_copy c; Mreturn (m', c')}\<close>

lemma mnml_copy_rule[vcg_rules]: \<open>llvm_htriple
  (monomial_assn x c) (mnml_copy c) (\<lambda>r. monomial_assn x c ** monomial_assn x r)\<close>
  unfolding mnml_copy_def
  apply (cases x; cases c; simp only: prod_assn_pair_conv prod.case)
  by vcg

(* TODO: not sure if needed anymore? *)
lemma mnml_copy_rule'[vcg_rules]: \<open>llvm_htriple
  (monom_assn m mi ** sbi_assn n ni) (mnml_copy (mi, ni))
  (\<lambda>r. monom_assn m mi ** sbi_assn n ni ** monomial_assn (m, n) r)\<close>
  using mnml_copy_rule[of \<open>(m, n)\<close> \<open>(mi, ni)\<close>] by simp

lemma mnml_copy_hnr[sepref_fr_rules]:
  \<open>(mnml_copy, RETURN o COPY) \<in> monomial_assn\<^sup>k \<rightarrow>\<^sub>a monomial_assn\<close>
  by (sepref_to_hoare; vcg)

lemma mnml_copy_is_copy[sepref_gen_algo_rules]:
  \<open>GEN_ALGO mnml_copy (is_copy monomial_assn)\<close>
  unfolding GEN_ALGO_def is_copy_def
  by (rule mnml_copy_hnr)

section \<open>Polynomials\<close>
  
abbreviation \<open>polynomial_assn \<equiv> cl_assn' monomial_assn\<close>

interpretation poly: copy_free_context \<open>monomial_assn\<close> \<open>mnml_free\<close> \<open>mnml_copy\<close>
  apply unfold_locales
  subgoal by (rule mnml_free_rule)
  subgoal by (rule mnml_copy_is_copy)
  done

end
