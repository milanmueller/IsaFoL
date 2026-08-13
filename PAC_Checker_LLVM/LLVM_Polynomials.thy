theory LLVM_Polynomials
  imports LLVM_String BigInt_LLVM.LLVM_CodeGen_Signed IICF_PartialMap
    PAC_Polynomials_Term LLVM_ASCII_String IICF_Copying_List
begin

text \<open>This theory defines refinment targets for polynomials in LLVM.
  The HOL-datatype we want to refine is `llist_polynomial` (i.e.
  @{typ \<open>(char list list \<times> int) list\<close>}, c.f. `PAC_Polynomials_Term`).\<close>

term strl_assn
abbreviation \<open>monom_assn \<equiv> cl_assn' strl_assn'\<close>
lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure monom_assn]

interpretation monom: copyable_assn \<open>strl_assn'\<close> \<open>strl.cl_free\<close> \<open>strl.cl_copy\<close>
  apply unfold_locales
  subgoal by (rule strl.cl_assn_free)
  subgoal by (rule strl.cl_copy_hnr)
  done

interpretation monom: linorder_assn \<open>strl_assn'\<close> \<open>strl.cl_eq\<close> \<open>strl.cl_less\<close>
  apply unfold_locales
  subgoal by (rule strl.cl_eq_hnr)
  subgoal by (rule strl.cl_less_hnr[unfolded list_lt_less])
  done

sepref_register \<open>(=) :: char list list \<Rightarrow> char list list \<Rightarrow> bool\<close>
sepref_register \<open>(<) :: char list list \<Rightarrow> char list list \<Rightarrow> bool\<close>
sepref_register \<open>(\<le>) :: char list list \<Rightarrow> char list list \<Rightarrow> bool\<close>

lemmas monom_less_hnr[sepref_fr_rules] = monom.cl_less_hnr[unfolded list_lt_less]
lemmas monom_le_hnr[sepref_fr_rules] = monom.cl_le_hnr[unfolded list_le_less_eq]

interpretation monom: cmp_env_impl 
  \<open>(\<le>)\<close> \<open>strl_assn'\<close> \<open>strl.cl_free\<close> \<open>strl.cl_le\<close> 
  apply unfold_locales
  subgoal by auto
  subgoal by auto
  subgoal by (rule strl_le_hnr)
  done

experiment
begin

sepref_definition monom_empty_test is \<open>uncurry0 (RETURN [])\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a monom_assn\<close>
  by sepref

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
lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure monomial_assn]

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

text \<open>We also need an order on monomials that only considers the variables\<close>
definition monomial_le :: \<open>(term_poly_list \<times> int) \<Rightarrow> (term_poly_list \<times> int) \<Rightarrow> bool\<close> where
  \<open>monomial_le \<equiv> \<lambda>p q. fst p \<le> fst q\<close>

text \<open>refining with sepref can only give us a destructive implementation due to tuple
  unpacking, therefore we go down to llM level\<close>

definition monomial_le_impl' :: \<open>monomial_conc \<Rightarrow> monomial_conc \<Rightarrow> 1 word llM\<close> where[llvm_code]:
  \<open>monomial_le_impl' \<equiv> \<lambda>(pm,pn) (qm,qn).doM {
    r \<leftarrow> monom.cl_le pm qm;
    Mreturn r 
  }\<close>

lemma monomial_assn_unfold:
  \<open>ENTAILS (monomial_assn p pii) (case p of (pm,pn) \<Rightarrow> case pii of (pmi,pni) \<Rightarrow> monom_assn pm pmi ** sbi_assn pn pni)\<close>
  by (auto simp: sep_algebra_simps ENTAILS_def entails_def) 

lemma monomial_le_rule[vcg_rules]:
  \<open>llvm_htriple
    (monomial_assn p pii ** monomial_assn q qii)
    (monomial_le_impl' pii qii)
    (\<lambda>r. monomial_assn p pii ** monomial_assn q qii ** bool1_assn (monomial_le p q) r)\<close>
  unfolding monomial_le_impl'_def monomial_le_def 
  supply [simp] = list_le_less_eq
  apply (cases p; cases q; cases pii; cases qii; simp)
  by vcg

(* doesn't use the vcg rule due to bool1_assn mismatch somehow... *)
lemma monomial_le_hnr[sepref_fr_rules]:
  \<open>(uncurry monomial_le_impl', uncurry (RETURN oo monomial_le))
  \<in> monomial_assn\<^sup>k *\<^sub>a monomial_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding monomial_le_impl'_def monomial_le_def
  supply [simp] = list_le_less_eq pure_def
  by (sepref_to_hoare; vcg)

definition mnml_eq_impl' :: \<open>monomial_conc \<Rightarrow> monomial_conc \<Rightarrow> 1 word llM\<close> where[llvm_code]:
  \<open>mnml_eq_impl' \<equiv> \<lambda>(pm,pn) (qm,qn). doM {
    r \<leftarrow> monom.cl_eq pm qm;
    llc_if r (signed_big_int_eq_impl pn qn) (Mreturn 0)
  }\<close>

context begin
interpretation llvm_prim_ctrl_setup .

lemma mnml_eq_hnr[sepref_fr_rules]:
  \<open>(uncurry mnml_eq_impl', uncurry (RETURN oo (=)))
  \<in> monomial_assn\<^sup>k *\<^sub>a monomial_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding mnml_eq_impl'_def
  supply [vcg_rules] = hfref_htriple_k2[OF signed_big_int_eq_impl_hnr]
  supply [simp] = pure_def bool1_rel_def bool.rel_def in_br_conv 
  by (sepref_to_hoare; vcg)

end

section \<open>Polynomials\<close>

abbreviation \<open>polynomial_assn \<equiv> cl_assn' monomial_assn\<close>
lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure polynomial_assn]

interpretation poly: copyable_assn \<open>monomial_assn\<close> \<open>mnml_free\<close> \<open>mnml_copy\<close>
  apply unfold_locales
  subgoal by (rule mnml_free_rule)
  subgoal by (rule mnml_copy_hnr)
  done

interpretation poly: cmp_env_impl \<open>monomial_le\<close> \<open>monomial_assn\<close> \<open>mnml_free\<close> \<open>monomial_le_impl'\<close>
  apply unfold_locales
  subgoal unfolding monomial_le_def by auto
  subgoal unfolding monomial_le_def by auto
  subgoal by (rule monomial_le_hnr)
  done

interpretation poly: eq_assn \<open>monomial_assn\<close> \<open>mnml_eq_impl'\<close>
  by unfold_locales (rule mnml_eq_hnr)

experiment
begin

sepref_definition polynomial_empty_impl is \<open>uncurry0 (RETURN [])\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a polynomial_assn\<close>
  by sepref


sepref_register \<open>(=) :: llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> bool\<close>
sepref_definition polynomial_eq_test is \<open>uncurry (RETURN oo (=))\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

end

section \<open>Printing\<close>

text \<open>Note that printing is not verified, as that would require a semantics
  for polynomial strings which we currently don't have.\<close>

(* Todo: migrate to strlt_assn as follows and make ^k version - should be possible
 * by using fold for print_monom *)
abbreviation \<open>strlt_assn \<equiv> clt_assn' char_assn\<close>

definition print_monom_inner :: \<open>char list \<Rightarrow> char list \<Rightarrow> char list\<close> where
  \<open>print_monom_inner \<equiv> \<lambda>acc t. acc @ (cl_to_clt t)\<close>

sepref_def print_monom_inner_impl is \<open>uncurry (RETURN oo print_monom_inner)\<close>
  :: \<open>strlt_assn\<^sup>d *\<^sub>a strl_assn'\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding print_monom_inner_def
  by sepref

definition print_monom :: \<open>char list list \<Rightarrow> char list\<close> where
  \<open>print_monom \<equiv> foldl print_monom_inner []\<close>

definition \<open>print_monom_impl \<equiv> \<lambda>m. doM {e \<leftarrow> clt_empty; cl_fold' print_monom_inner_impl e m}\<close> 

lemma print_monom_rule: \<open>llvm_htriple
  (monom_assn m mi)
  (print_monom_impl mi)
  (\<lambda>r. monom_assn m mi ** strlt_assn (print_monom m) r)\<close>
proof -
  have INNER_vcg: \<open>llvm_htriple
    (strlt_assn acc acci ** strl_assn' t ti)
    (print_monom_inner_impl acci ti)
    (\<lambda>r. strlt_assn (print_monom_inner acc t) r ** strl_assn' t ti)\<close> for acc acci t ti
    apply (rule htriple_ent_post[OF _ hfref_htriple_d1_k2[OF print_monom_inner_impl.refine]])
    by (simp add: sep_conj_aci)
  show ?thesis
    unfolding print_monom_impl_def
    supply [vcg_rules] = cl_fold'_rule[where R="strlt_assn" and A="strl_assn'"
      and f=print_monom_inner_impl and fa=print_monom_inner,
      OF INNER_vcg]
    supply [simp] = print_monom_def
    by vcg
qed

lemma print_monom_hnr[sepref_fr_rules]:
  \<open>(print_monom_impl, (RETURN o print_monom))
  \<in> monom_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  apply (sepref_to_hoare)
  supply [vcg_rules] = print_monom_rule
  by vcg

definition \<open>mnml_print \<equiv> \<lambda>(m,n). cl_to_clt (chars_of_int (COPY n)) @ print_monom m\<close>

sepref_def mnml_print_impl is \<open>RETURN o mnml_print\<close>
  :: \<open>monomial_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding mnml_print_def
  by sepref

definition poly_print_inner :: \<open>char list \<Rightarrow> char list list \<times> int \<Rightarrow> char list\<close> where
  \<open>poly_print_inner \<equiv> \<lambda>acc p. acc @ mnml_print p\<close>

sepref_def poly_print_inner_impl is \<open>uncurry (RETURN oo poly_print_inner)\<close>
  :: \<open>strlt_assn\<^sup>d *\<^sub>a monomial_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding poly_print_inner_def
  by sepref

definition poly_print :: \<open>llist_polynomial \<Rightarrow> string\<close> where
  \<open>poly_print \<equiv> foldl poly_print_inner []\<close>

definition \<open>poly_print_impl \<equiv> \<lambda>ps. doM {e \<leftarrow> clt_empty; cl_fold' poly_print_inner_impl e ps}\<close>

lemma poly_print_rule: \<open>llvm_htriple
  (polynomial_assn ps psi)
  (poly_print_impl psi)
  (\<lambda>r. polynomial_assn ps psi ** strlt_assn (poly_print ps) r)\<close>
proof -
  have INNER_vcg: \<open>llvm_htriple
    (strlt_assn acc acci ** monomial_assn p pi)
    (poly_print_inner_impl acci pi)
    (\<lambda>r. strlt_assn (poly_print_inner acc p) r ** monomial_assn p pi)\<close> for acc acci p pi
    apply (rule htriple_ent_post[OF _ hfref_htriple_d1_k2[OF poly_print_inner_impl.refine]])
    by (simp add: sep_conj_aci)
  show ?thesis
    unfolding poly_print_impl_def
    supply [vcg_rules] = cl_fold'_rule[where R="strlt_assn" and A="monomial_assn"
      and f=poly_print_inner_impl and fa=poly_print_inner,
      OF INNER_vcg]
    supply [simp] = poly_print_def
    by vcg
qed

lemma poly_print_hnr[sepref_fr_rules]:
  \<open>(poly_print_impl, (RETURN o poly_print))
  \<in> polynomial_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  apply (sepref_to_hoare)
  supply [vcg_rules] = poly_print_rule
  by vcg

end
