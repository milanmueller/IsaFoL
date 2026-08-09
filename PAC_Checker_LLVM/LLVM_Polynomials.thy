theory LLVM_Polynomials
  imports LLVM_String BigInt_LLVM.LLVM_CodeGen_Signed IICF_PartialMap
    PAC_Polynomials_Term BigInt_String
begin

text \<open>This theory defines refinment targets for polynomials in LLVM.
  The HOL-datatype we want to refine is `llist_polynomial` (i.e.
  @{typ \<open>(char list list \<times> int) list\<close>}, c.f. `PAC_Polynomials_Term`).\<close>

text \<open>\<open>BigInt_String\<close> (via the old \<open>IICF_Open_List\<close>) registers a rule for
  @{term op_list_empty} at os-lists. Since it is a producer (its result
  assertion is unconstrained at rule-application time) and more recently
  declared than the copying-list rule, sepref would commit to it when
  synthesizing list literals, and fail later. All lists in this theory are
  copying lists, so we simply deregister it.\<close>
lemmas [sepref_fr_rules del] = os_empty_hnr

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

text \<open>Printing for monoms, using lists with tail pointer. Not verified!\<close>
definition print_monom :: \<open>char list list \<Rightarrow> char list nres\<close> where
  \<open>print_monom \<equiv> \<lambda>ms. doN {
    (r,_) \<leftarrow> WHILET
      (\<lambda>(r,ms). ms\<noteq>[])
      (\<lambda>(r,ms). doN {
        (m,ms) \<leftarrow> mop_list_pop_hd ms;
        (r',_) \<leftarrow> WHILET
          (\<lambda>(r',ms'). ms'\<noteq>[])
          (\<lambda>(r',ms'). doN {
            (m',ms') \<leftarrow> mop_list_pop_hd ms';
            RETURN (r'@[m'],ms') 
          }) ([], m);
        RETURN (r@r',ms)
      }) ([], ms);
    RETURN r 
  }\<close>

sepref_def print_monom_impl is \<open>print_monom\<close>
  :: \<open>monom_assn\<^sup>d \<rightarrow>\<^sub>a strl_assn'\<close>
  unfolding print_monom_def ls_emp
  by sepref

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

lemma stupid: \<open>monomial_assn = (monom_assn \<times>\<^sub>a sbi_assn)\<close> by simp

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

text \<open>Monomial equality: compare the variable lists first, the coefficients only
  on a match. Like @{term monomial_le_impl'} this is written at the llM level to
  keep both tuples intact.\<close>

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

section \<open>Printing of Polynomials\<close>

lemma char_of_digit_zero: \<open>char_of_word (ascii_of_digit 0) = CHR ''0''\<close>
  by eval

lemma char_of_word_hyphen_lit: \<open>char_of_word word_hyphen = CHR ''-''\<close>
  by eval

text \<open>Relating byte strings to their character strings.\<close>
definition char_bytes_rel :: \<open>(char list \<times> 8 word list) set\<close> where
  \<open>char_bytes_rel \<equiv> {(cs, bs). cs = map char_of_word bs}\<close>

subsection \<open>Unsigned big integers to strings\<close>

text \<open>Fused variant of @{term print_bi_ascii'} that produces HOL characters.\<close>
definition print_bi_strl :: \<open>big_int \<Rightarrow> char list nres\<close> where
  \<open>print_bi_strl bi \<equiv> doN {
    ASSERT (big_int_invar bi);
    if big_int_length bi = 0 then RETURN ''0''
    else doN {
      (_, res) \<leftarrow> WHILEIT
        (\<lambda>_. True)
        (\<lambda>(q, _). 0 < big_int_length q)
        (\<lambda>(q, res). doN {
          (q', r) \<leftarrow> bi_div_by_w64 q 10;
          RETURN (q', char_of_word (ascii_of_digit r) # res)
        })
        (bi, []);
      RETURN res
    }
  }\<close>

lemma print_bi_strl_refine:
  \<open>print_bi_strl bi \<le> \<Down> char_bytes_rel (print_bi_ascii' bi)\<close>
  unfolding print_bi_strl_def print_bi_ascii'_def
  apply (refine_rcg WHILEIT_refine[where R = \<open>Id \<times>\<^sub>r char_bytes_rel\<close>])
  apply refine_dref_type
  by (auto simp: char_bytes_rel_def conc_Id char_of_digit_zero)

sepref_register print_bi_strl
sepref_def print_bi_strl_impl is \<open>print_bi_strl\<close>
  :: \<open>bi_aux_assn\<^sup>d \<rightarrow>\<^sub>a strl_assn'\<close>
  unfolding print_bi_strl_def
  apply (annot_snat_const size_t)
  by sepref

subsection \<open>Signed big integers to strings\<close>

definition print_sbi_strl :: \<open>signed_big_int \<Rightarrow> char list nres\<close> where
  \<open>print_sbi_strl sbi \<equiv> doN {
    let \<sigma>_in = \<sigma> sbi;
    bi \<leftarrow> dest_extr_bi sbi;
    abs_str \<leftarrow> print_bi_strl bi;
    if \<sigma>_in then RETURN (CHR ''-'' # abs_str) else RETURN abs_str
  }\<close>

lemma print_sbi_strl_refine:
  \<open>print_sbi_strl sbi \<le> \<Down> char_bytes_rel (print_sbi_ascii sbi)\<close>
  unfolding print_sbi_strl_def print_sbi_ascii_def
  apply (refine_rcg print_bi_strl_refine)
  apply refine_dref_type
  by (auto simp: char_bytes_rel_def conc_Id char_of_word_hyphen_lit)

lemma print_sbi_strl_correct:
  assumes \<open>(sbi, i) \<in> signed_big_int_rel\<close>
  shows \<open>print_sbi_strl sbi \<le> SPEC (\<lambda>s. (s, i) \<in> ascii_str_int_rel)\<close>
  using print_sbi_strl_refine[of sbi] print_sbi_ascii_correct[OF assms]
  by (auto simp: pw_le_iff refine_pw_simps char_bytes_rel_def)

sepref_def print_sbi_strl_impl is \<open>print_sbi_strl\<close>
  :: \<open>sbi_aux_assn\<^sup>d \<rightarrow>\<^sub>a strl_assn'\<close>
  unfolding print_sbi_strl_def
  by sepref

subsection \<open>Integers to strings\<close>

text \<open>The abstract operation on the @{typ int} level: any decimal string
  representation of the integer. This is the operation to use in abstract
  programs whose integers are refined by @{term sbi_assn}.\<close>
definition strl_of_int :: \<open>int \<Rightarrow> char list nres\<close> where
  \<open>strl_of_int i \<equiv> SPEC (\<lambda>s. (s, i) \<in> ascii_str_int_rel)\<close>

lemma print_sbi_strl_fref:
  \<open>(print_sbi_strl, strl_of_int) \<in> signed_big_int_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: strl_of_int_def conc_Id intro!: print_sbi_strl_correct)

sepref_register strl_of_int
context notes [fcomp_norm_unfold] = sbi_assn_def[symmetric]
begin
lemmas strl_of_int_hnr[sepref_fr_rules] =
  print_sbi_strl_impl.refine[FCOMP print_sbi_strl_fref]
end

subsection \<open>Printing whole polynomials\<close>

text \<open>Like @{term print_monom}, the printing of polynomials is not verified.
  Monomials are printed as \<open>coefficient*variables\<close> and separated by \<open> + \<close>;
  the empty polynomial prints as \<open>0\<close>. Note that negative coefficients keep
  their sign, so a polynomial may print as e.g.\ \<open>2*xy + -1*z\<close>.\<close>

sepref_register print_monom

definition print_polynomial :: \<open>llist_polynomial \<Rightarrow> char list nres\<close> where
  \<open>print_polynomial \<equiv> \<lambda>p. doN {
    if p = [] then RETURN ''0''
    else doN {
      ((m, c), p) \<leftarrow> mop_list_pop_hd p;
      cs \<leftarrow> strl_of_int c;
      ms \<leftarrow> print_monom m;
      (r, _) \<leftarrow> WHILET
        (\<lambda>(r, p). p \<noteq> [])
        (\<lambda>(r, p). doN {
          ((m, c), p) \<leftarrow> mop_list_pop_hd p;
          cs \<leftarrow> strl_of_int c;
          ms \<leftarrow> print_monom m;
          RETURN (r @ '' + '' @ cs @ ''*'' @ ms, p)
        }) (cs @ ''*'' @ ms, p);
      RETURN r
    }
  }\<close>

sepref_def print_polynomial_impl is \<open>print_polynomial\<close>
  :: \<open>polynomial_assn\<^sup>d \<rightarrow>\<^sub>a strl_assn'\<close>
  unfolding print_polynomial_def ls_emp ls_emp'
  by sepref

end
