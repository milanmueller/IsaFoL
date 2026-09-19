theory LPAC_Efficient_Checker_Synthesis
  imports
    LPAC_Efficient_Checker_Refinement
    LPAC_Perfectly_Shared_Vars
    PAC_Checker_Synthesis
    LPAC_Error
begin

sepref_register add_poly_l_s_ifoldl

sepref_register mult_monoms_s_ifoldl

lemmas [safe_constraint_rules] =
  CN_FALSEI[of is_pure monom_s_assn]
  CN_FALSEI[of is_pure poly_s_assn]

definition mnml_s_free :: \<open>_ \<Rightarrow> unit llM\<close> where [llvm_code]:
  \<open>mnml_s_free \<equiv> \<lambda>(m, c). doM { snhm.val.cl_free m; sbi_free c }\<close>

lemma mnml_s_free_rule[sepref_frame_free_rules]:
  \<open>MK_FREE (monom_s_assn \<times>\<^sub>a sbi_assn) mnml_s_free\<close>
  unfolding mnml_s_free_def
  by (rule mk_free_pair[OF snhm.val.cl_assn_free sbi_free_rule])

definition mnml_s_copy where [llvm_code]:
  \<open>mnml_s_copy \<equiv> \<lambda>(m, c). doM { m' \<leftarrow> snhm.val.cl_copy m; c' \<leftarrow> sbi_copy c; Mreturn (m', c') }\<close>

lemma mnml_s_copy_rule[vcg_rules]: \<open>llvm_htriple
  ((monom_s_assn \<times>\<^sub>a sbi_assn) x c) (mnml_s_copy c)
  (\<lambda>r. (monom_s_assn \<times>\<^sub>a sbi_assn) x c ** (monom_s_assn \<times>\<^sub>a sbi_assn) x r)\<close>
  unfolding mnml_s_copy_def
  apply (cases x; cases c; simp only: prod_assn_pair_conv prod.case)
  by vcg

lemma mnml_s_copy_rule'[vcg_rules]: \<open>llvm_htriple
  (monom_s_assn m mi ** sbi_assn n ni) (mnml_s_copy (mi, ni))
  (\<lambda>r. monom_s_assn m mi ** sbi_assn n ni ** (monom_s_assn \<times>\<^sub>a sbi_assn) (m, n) r)\<close>
  using mnml_s_copy_rule[of \<open>(m, n)\<close> \<open>(mi, ni)\<close>] by simp

lemmas mnml_s_copy_rule''[vcg_rules] = mnml_s_copy_rule'[unfolded pure_def]

lemma mnml_s_copy_hnr[sepref_fr_rules]:
  \<open>(mnml_s_copy, RETURN o COPY) \<in> (monom_s_assn \<times>\<^sub>a sbi_assn)\<^sup>k \<rightarrow>\<^sub>a (monom_s_assn \<times>\<^sub>a sbi_assn)\<close>
  by (sepref_to_hoare; vcg)

interpretation poly_s: copyable_assn \<open>monom_s_assn \<times>\<^sub>a sbi_assn\<close> mnml_s_free mnml_s_copy
  apply unfold_locales
  subgoal by (rule mnml_s_free_rule)
  subgoal by (rule mnml_s_copy_hnr)
  done

section \<open>The \<open>ordered\<close> Result Type as a Tag Byte\<close>

definition ordered_code :: \<open>ordered \<Rightarrow> 8 word\<close> where
  \<open>ordered_code s = (case s of EQUAL \<Rightarrow> 0 | LESS \<Rightarrow> 1 | GREATER \<Rightarrow> 2 | UNKNOWN \<Rightarrow> 3)\<close>

lemma ordered_code_simps[simp]:
  \<open>ordered_code EQUAL = 0\<close>
  \<open>ordered_code LESS = 1\<close>
  \<open>ordered_code GREATER = 2\<close>
  \<open>ordered_code UNKNOWN = 3\<close>
  by (auto simp: ordered_code_def)

lemma ordered_code_inj[simp]: \<open>ordered_code a = ordered_code b \<longleftrightarrow> a = b\<close>
  by (cases a; cases b) auto

definition ordered_rel :: \<open>(8 word \<times> ordered) set\<close> where
  \<open>ordered_rel = {(w, s). w = ordered_code s}\<close>

definition is_EQUAL :: \<open>ordered \<Rightarrow> bool\<close> where [simp]: \<open>is_EQUAL s \<longleftrightarrow> s = EQUAL\<close>

definition is_LESS :: \<open>ordered \<Rightarrow> bool\<close> where [simp]: \<open>is_LESS s \<longleftrightarrow> s = LESS\<close>

definition is_GREATER :: \<open>ordered \<Rightarrow> bool\<close> where [simp]: \<open>is_GREATER s \<longleftrightarrow> s = GREATER\<close>

definition is_UNKNOWN :: \<open>ordered \<Rightarrow> bool\<close> where [simp]: \<open>is_UNKNOWN s \<longleftrightarrow> s = UNKNOWN\<close>

lemma fold_ordered_discriminators:
  \<open>(s = EQUAL) = is_EQUAL s\<close>
  \<open>(s = LESS) = is_LESS s\<close>
  \<open>(s = GREATER) = is_GREATER s\<close>
  \<open>(s = UNKNOWN) = is_UNKNOWN s\<close>
  \<open>(s \<noteq> EQUAL) = (\<not>is_EQUAL s)\<close>
  \<open>(s \<noteq> LESS) = (\<not>is_LESS s)\<close>
  \<open>(s \<noteq> GREATER) = (\<not>is_GREATER s)\<close>
  \<open>(s \<noteq> UNKNOWN) = (\<not>is_UNKNOWN s)\<close>
  by auto

abbreviation ordered_assn :: \<open>ordered \<Rightarrow> 8 word \<Rightarrow> assn\<close> where
  \<open>ordered_assn \<equiv> pure ordered_rel\<close>

context begin

interpretation llvm_prim_arith_setup .

lemma ll_icmp_eq_word_rule:
  \<open>llvm_htriple \<box> (ll_icmp_eq (a::'l::len word) b) (\<lambda>r. \<upharpoonleft>bool.assn (a = b) r)\<close>
  supply [simp] = bool.assn_def by vcg

end

sepref_register EQUAL LESS GREATER UNKNOWN get_var_nameS perfect_shared_var_order_s
  perfect_shared_term_order_rel_s

lemma ordered_constants_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0), uncurry0 (RETURN EQUAL)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a ordered_assn\<close>
  \<open>(uncurry0 (Mreturn 1), uncurry0 (RETURN LESS)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a ordered_assn\<close>
  \<open>(uncurry0 (Mreturn 2), uncurry0 (RETURN GREATER)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a ordered_assn\<close>
  \<open>(uncurry0 (Mreturn 3), uncurry0 (RETURN UNKNOWN)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a ordered_assn\<close>
  by (sepref_to_hoare;
    vcg; auto simp: mem_alloc_pure_reassembly pure_def ordered_rel_def)+

sepref_register is_EQUAL is_LESS is_GREATER is_UNKNOWN

lemma ordered_discriminators_hnr[sepref_fr_rules]:
  \<open>(\<lambda>w. ll_icmp_eq w 0, RETURN o is_EQUAL) \<in> ordered_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  \<open>(\<lambda>w. ll_icmp_eq w 1, RETURN o is_LESS) \<in> ordered_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  \<open>(\<lambda>w. ll_icmp_eq w 2, RETURN o is_GREATER) \<in> ordered_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  \<open>(\<lambda>w. ll_icmp_eq w 3, RETURN o is_UNKNOWN) \<in> ordered_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [vcg_rules] = ll_icmp_eq_word_rule
  by (sepref_to_hoare;
    vcg;
    auto simp: mem_alloc_pure_reassembly pure_def ordered_rel_def
      bool1_rel_unfolds bool.assn_def;
    case_tac x; auto)+

subsubsection \<open>Borrowing two elements of a string table\<close>

lemma strls_list_assn_focus2_ex:
  assumes I: \<open>i < length xs\<close> and J: \<open>j < length xs\<close> and IJ: \<open>i \<noteq> j\<close>
  shows \<open>\<exists>F. \<upharpoonleft>(list_assn (mk_assn strl_assn')) xs xsi =
    (strl_assn' (xs ! i) (xsi ! i) ** strl_assn' (xs ! j) (xsi ! j) **
      \<up>(length xsi = length xs) ** F)\<close>
proof -
  have KEY: \<open>\<exists>F. \<upharpoonleft>(list_assn (mk_assn strl_assn')) xs xsi =
      (strl_assn' (xs ! a) (xsi ! a) ** strl_assn' (xs ! b) (xsi ! b) **
        \<up>(length xsi = length xs) ** F)\<close>
    if ab: \<open>a < b\<close> and b: \<open>b < length xs\<close> for a b
  proof -
    have A: \<open>a < length xs\<close> using ab b by simp
    have K: \<open>b - Suc a < length (drop (Suc a) xs)\<close> using ab b by simp
    show ?thesis
    proof (cases \<open>length xsi = length xs\<close>)
      case False
      then have \<open>\<upharpoonleft>(list_assn (mk_assn strl_assn')) xs xsi = sep_false\<close>
        by (simp add: strls.list_assn_focus[OF A])
      then show ?thesis
        using False by (intro exI[of _ \<open>\<box>\<close>]) simp
    next
      case True
      have E1: \<open>drop (Suc a) xs ! (b - Suc a) = xs ! b\<close> using ab b by simp
      have E2: \<open>drop (Suc a) xsi ! (b - Suc a) = xsi ! b\<close> using ab b True by simp
      show ?thesis
        apply (rule exI[of _ \<open>\<upharpoonleft>(list_assn (mk_assn strl_assn')) (take a xs) (take a xsi) **
            \<upharpoonleft>(list_assn (mk_assn strl_assn')) (take (b - Suc a) (drop (Suc a) xs))
               (take (b - Suc a) (drop (Suc a) xsi)) **
            \<upharpoonleft>(list_assn (mk_assn strl_assn')) (drop (Suc (b - Suc a)) (drop (Suc a) xs))
               (drop (Suc (b - Suc a)) (drop (Suc a) xsi))\<close>])
        apply (subst strls.list_assn_focus[OF A])
        apply (subst strls.list_assn_focus[OF K])
        apply (simp only: E1 E2)
        apply (simp add: True sep_algebra_simps)
        apply (simp add: sep_conj_c)
        done
    qed
  qed
  show ?thesis
  proof (cases \<open>i < j\<close>)
    case True
    show ?thesis by (rule KEY[OF True J])
  next
    case False
    then have \<open>j < i\<close> using IJ by auto
    from KEY[OF this I] obtain F where
      F: \<open>\<upharpoonleft>(list_assn (mk_assn strl_assn')) xs xsi =
        (strl_assn' (xs ! j) (xsi ! j) ** strl_assn' (xs ! i) (xsi ! i) **
          \<up>(length xsi = length xs) ** F)\<close>
      by blast
    show ?thesis
      apply (rule exI[of _ F])
      apply (subst F)
      apply (simp add: sep_conj_c)
      done
  qed
qed

definition strls_focus2_rest ::
  \<open>string list \<Rightarrow> 8 word cl_list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> assn\<close> where
  \<open>strls_focus2_rest xs xsi i j = (SOME F. \<upharpoonleft>(list_assn (mk_assn strl_assn')) xs xsi =
    (strl_assn' (xs ! i) (xsi ! i) ** strl_assn' (xs ! j) (xsi ! j) **
      \<up>(length xsi = length xs) ** F))\<close>

lemma strls_list_assn_focus2:
  assumes \<open>i < length xs\<close> and \<open>j < length xs\<close> and \<open>i \<noteq> j\<close>
  shows \<open>\<upharpoonleft>(list_assn (mk_assn strl_assn')) xs xsi =
    (strl_assn' (xs ! i) (xsi ! i) ** strl_assn' (xs ! j) (xsi ! j) **
      \<up>(length xsi = length xs) ** strls_focus2_rest xs xsi i j)\<close>
  unfolding strls_focus2_rest_def
  by (rule someI_ex[OF strls_list_assn_focus2_ex[OF assms]])

subsubsection \<open>Comparing two entries of the string table in place\<close>

definition strls_less_impl :: \<open>(8 word cl_list, 64) array_list \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 1 word llM\<close>
  where [llvm_code]:
  \<open>strls_less_impl ali ii ji \<equiv> doM {
    xi \<leftarrow> arl_nth ali ii;
    yi \<leftarrow> arl_nth ali ji;
    strl.cl_less xi yi
  }\<close>

lemma strls_less_impl_rule_aux:
  assumes \<open>i < length xs\<close> and \<open>j < length xs\<close> and \<open>i \<noteq> j\<close>
  shows \<open>llvm_htriple
    (strls_assn xs ali ** \<upharpoonleft>snat.assn i ii ** \<upharpoonleft>snat.assn j ji)
    (strls_less_impl ali ii ji)
    (\<lambda>r. strls_assn xs ali ** bool1_assn (list_lt (xs ! i) (xs ! j)) r)\<close>
  unfolding strls_less_impl_def strls.oa_assn_def
  supply [vcg_rules] = strl.cl_less_rule[unfolded list_lt_less]
  supply [simp] = assms
  apply (simp only: sel_mk_assn strls_list_assn_focus2[OF assms])
  apply vcg
  done

lemma strls_less_impl_rule[vcg_rules]:
  \<open>llvm_htriple
    (strls_assn xs ali ** \<upharpoonleft>snat.assn i ii ** \<upharpoonleft>snat.assn j ji
      ** \<up>\<^sub>d(i < length xs \<and> j < length xs \<and> i \<noteq> j))
    (strls_less_impl ali ii ji)
    (\<lambda>r. strls_assn xs ali ** bool1_assn (xs ! i < xs ! j) r)\<close>
  apply (rule htriple_pure_preI)
  apply (clarsimp dest!: pure_part_split_conj simp: vcg_tag_defs sep_algebra_simps
    pred_lift_extract_simps)
  apply (rule strls_less_impl_rule_aux[unfolded list_lt_less]; assumption)
  done

definition perfect_shared_var_order_c_else_impl ::
  \<open>(64 word \<times> 64 word \<times> 8 word node ptr ptr) \<times>
   64 word \<times> 64 word \<times> (8 word node ptr \<times> 64 word ptr) node ptr ptr
    \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 8 word llM\<close> where [llvm_code]:
  \<open>perfect_shared_var_order_c_else_impl \<D> xi yi \<equiv> doM {
    let (strs, _) = \<D>;
    same \<leftarrow> ll_icmp_eq xi yi;
    llc_if same (Mreturn 2) (doM {
      cmp \<leftarrow> strls_less_impl strs xi yi;
      llc_if cmp (Mreturn 1) (Mreturn 2)
    })
  }\<close>

context begin

interpretation llvm_prim_ctrl_setup .

lemma perfect_shared_var_order_c_else_impl_rule[vcg_rules]:
  \<open>llvm_htriple
    (strls_assn xs strsi ** \<upharpoonleft>snat.assn i ii ** \<upharpoonleft>snat.assn j ji
      ** \<up>\<^sub>d(i < length xs \<and> j < length xs))
    (perfect_shared_var_order_c_else_impl (strsi, \<V>i) ii ji)
    (\<lambda>r. strls_assn xs strsi ** ordered_assn (if xs ! i < xs ! j then LESS else GREATER) r)\<close>
  unfolding perfect_shared_var_order_c_else_impl_def
  supply [simp] = pure_def bool1_rel_def bool.rel_def in_br_conv ordered_rel_def
    bool.assn_def from_bool_def
  apply (simp only: Let_def prod.case)?
  apply vcg
  done

end

lemmas perfect_shared_var_order_c_else_impl_rule'[vcg_rules] =
  perfect_shared_var_order_c_else_impl_rule[unfolded pure_def]

lemma perfect_shared_var_order_c_else_impl_refine:
  \<open>(uncurry2 perfect_shared_var_order_c_else_impl, uncurry2 perfect_shared_var_order_c_else)
    \<in> perfect_shared_vars_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k \<rightarrow>\<^sub>a ordered_assn\<close>
  unfolding perfect_shared_var_order_c_else_alt_def snat_rel_def
    snat.assn_is_rel[symmetric]
  apply sepref_to_hoare
  apply (clarsimp simp: refine_pw_simps split del: if_split)
  apply vcg
  done

sepref_register perfect_shared_var_order_s_else

lemma perfect_shared_var_order_s_else_hnr[sepref_fr_rules]:
  \<open>(uncurry2 perfect_shared_var_order_c_else_impl, uncurry2 perfect_shared_var_order_s_else)
    \<in> shared_vars_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k \<rightarrow>\<^sub>a ordered_assn\<close>
  using perfect_shared_var_order_c_else_impl_refine[FCOMP perfect_shared_var_order_c_else_fref]
  by auto

sepref_def perfect_shared_var_order_s_impl
  is \<open>uncurry2 perfect_shared_var_order_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k \<rightarrow>\<^sub>a ordered_assn\<close>
  unfolding
    perfect_shared_var_order_s_alt
    perfectly_shared_strings_equal_l_def
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    var_order_rel''
  by sepref

lemmas [sepref_fr_rules] = perfect_shared_var_order_s_impl.refine

sepref_def perfect_shared_term_order_rel_dir_impl
  is \<open>uncurry2 perfect_shared_term_order_rel_dir\<close>
  :: \<open>si64_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k *\<^sub>a shared_vars_assn\<^sup>k \<rightarrow>\<^sub>a dir_assn\<close>
  unfolding perfect_shared_term_order_rel_dir_def fold_ordered_discriminators
  by sepref

sepref_def perfect_shared_var_order_s_rel_f_impl
  is \<open>uncurry4 perfect_shared_term_order_rel_f\<close>
  :: \<open>ordered_assn\<^sup>d *\<^sub>a si64_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k *\<^sub>a shared_vars_assn\<^sup>k *\<^sub>a dir_assn\<^sup>k \<rightarrow>\<^sub>a ordered_assn\<close>
  unfolding perfect_shared_term_order_rel_f_def
  by sepref

sepref_def ordered_const_GREATER_impl is \<open>uncurry ordered_const_GREATER\<close>
  :: \<open>ordered_assn\<^sup>d *\<^sub>a si64_assn\<^sup>k \<rightarrow>\<^sub>a ordered_assn\<close>
  unfolding ordered_const_GREATER_def
  by sepref

sepref_def ordered_const_LESS_impl is \<open>uncurry ordered_const_LESS\<close>
  :: \<open>ordered_assn\<^sup>d *\<^sub>a si64_assn\<^sup>k \<rightarrow>\<^sub>a ordered_assn\<close>
  unfolding ordered_const_LESS_def
  by sepref

sepref_register perfect_shared_term_order_rel_s_ifoldl

lemmas perfect_shared_term_order_rel_s_ifoldl_hnr[sepref_fr_rules] =
  cl_ifoldl_ext_nres_hfref[OF perfect_shared_var_order_s_rel_f_impl.refine
    perfect_shared_term_order_rel_dir_impl.refine
    ordered_const_GREATER_impl.refine ordered_const_LESS_impl.refine,
    folded perfect_shared_term_order_rel_s_ifoldl_def]

sepref_def perfect_shared_term_order_rel_s_impl
  is \<open>uncurry2 perfect_shared_term_order_rel_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a monom_s_assn\<^sup>k *\<^sub>a monom_s_assn\<^sup>k \<rightarrow>\<^sub>a ordered_assn\<close>
  unfolding perfect_shared_term_order_rel_s_ifoldl_alt
  by sepref

lemmas [sepref_fr_rules] = perfect_shared_term_order_rel_s_impl.refine

abbreviation \<open>monomial_s_assn \<equiv> monom_s_assn \<times>\<^sub>a sbi_assn\<close>

sepref_def add_poly_l_s_dir_impl is \<open>uncurry2 add_poly_l_s_dir\<close>
  :: \<open>monomial_s_assn\<^sup>k *\<^sub>a monomial_s_assn\<^sup>k *\<^sub>a shared_vars_assn\<^sup>k \<rightarrow>\<^sub>a dir_assn\<close> 
  unfolding add_poly_l_s_dir_def fold_ordered_discriminators
  by sepref

sepref_def add_poly_l_s_f_impl is \<open>uncurry4 add_poly_l_s_f\<close>
  :: \<open>(clt_assn' monomial_s_assn)\<^sup>d *\<^sub>a monomial_s_assn\<^sup>k *\<^sub>a monomial_s_assn\<^sup>k
      *\<^sub>a shared_vars_assn\<^sup>k *\<^sub>a dir_assn\<^sup>k \<rightarrow>\<^sub>a clt_assn' monomial_s_assn\<close>
  unfolding add_poly_l_s_f_def
  by sepref

sepref_def add_poly_l_s_cpy_impl is \<open>uncurry add_poly_l_s_cpy\<close>
  :: \<open>(clt_assn' monomial_s_assn)\<^sup>d *\<^sub>a monomial_s_assn\<^sup>k \<rightarrow>\<^sub>a clt_assn' monomial_s_assn\<close>
  unfolding add_poly_l_s_cpy_def
  by sepref 

lemmas add_poly_l_s_ifoldl_hnr[sepref_fr_rules] =
  cl_ifoldl_ext_nres_hfref[OF add_poly_l_s_f_impl.refine add_poly_l_s_dir_impl.refine
    add_poly_l_s_cpy_impl.refine add_poly_l_s_cpy_impl.refine,
    folded add_poly_l_s_ifoldl_def]

sepref_def add_poly_l_prep_impl
  is \<open>uncurry add_poly_l_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a (poly_s_assn \<times>\<^sub>a poly_s_assn)\<^sup>k \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding add_poly_l_s_ifoldl_alt
  by sepref

sepref_def mult_monoms_s_dir_impl is \<open>uncurry2 mult_monoms_s_dir\<close>
  :: \<open>si64_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k *\<^sub>a shared_vars_assn\<^sup>k \<rightarrow>\<^sub>a dir_assn\<close>
  unfolding mult_monoms_s_dir_def fold_ordered_discriminators
  by sepref

sepref_def mult_monoms_s_f_impl is \<open>uncurry4 mult_monoms_s_f\<close>
  :: \<open>(clt_assn' si64_assn)\<^sup>d *\<^sub>a si64_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k
      *\<^sub>a shared_vars_assn\<^sup>k *\<^sub>a dir_assn\<^sup>k \<rightarrow>\<^sub>a clt_assn' si64_assn\<close>
  unfolding mult_monoms_s_f_def
  by sepref

sepref_def mult_monoms_s_cpy_impl is \<open>uncurry mult_monoms_s_cpy\<close>
  :: \<open>(clt_assn' si64_assn)\<^sup>d *\<^sub>a si64_assn\<^sup>k \<rightarrow>\<^sub>a clt_assn' si64_assn\<close>
  unfolding mult_monoms_s_cpy_def
  by sepref

lemmas mult_monoms_s_ifoldl_hnr[sepref_fr_rules] =
  cl_ifoldl_ext_nres_hfref[OF mult_monoms_s_f_impl.refine mult_monoms_s_dir_impl.refine
    mult_monoms_s_cpy_impl.refine mult_monoms_s_cpy_impl.refine,
    folded mult_monoms_s_ifoldl_def]

sepref_def mult_monoms_s_impl
  is \<open>uncurry2 mult_monoms_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a monom_s_assn\<^sup>k *\<^sub>a monom_s_assn\<^sup>k \<rightarrow>\<^sub>a monom_s_assn\<close>
  unfolding mult_monoms_s_ifoldl_alt
  by sepref

lemmas [sepref_fr_rules] =
  mult_monoms_s_impl.refine

sepref_register mult_monoms_s mult_term_s

sepref_def mult_term_s_step_impl
  is \<open>uncurry3 mult_term_s_step\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a monomial_s_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>d *\<^sub>a monomial_s_assn\<^sup>k
      \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding mult_term_s_step_def
  by sepref

sepref_register mult_term_s_foldl

lemmas mult_term_s_foldl_hnr[sepref_fr_rules] =
  cl_fold_env2_nres_hfref[OF mult_term_s_step_impl.refine, folded mult_term_s_foldl_def]

sepref_def mult_term_s_impl
  is \<open>uncurry3 mult_term_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k *\<^sub>a monomial_s_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>d
      \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding mult_term_s_alt_def
  by sepref

lemmas [sepref_fr_rules] =
  mult_term_s_impl.refine

sepref_def mult_poly_s_step_impl
  is \<open>uncurry3 mult_poly_s_step\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>d *\<^sub>a monomial_s_assn\<^sup>k
      \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding mult_poly_s_step_def
  by sepref

sepref_register mult_poly_s_foldl

lemmas mult_poly_s_foldl_hnr[sepref_fr_rules] =
  cl_fold_env2_nres_hfref[OF mult_poly_s_step_impl.refine, folded mult_poly_s_foldl_def]

sepref_def mult_poly_s_impl
  is \<open>uncurry2 mult_poly_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding mult_poly_s_alt_def
  by sepref

lemmas [sepref_fr_rules] =
  mult_poly_s_impl.refine

(*
lemma cl_assn_free_comp[sepref_frame_free_rules]:
  \<open>MK_FREE A f \<Longrightarrow> MK_FREE (cl_assn' A) (freeable_assn.cl_free f)\<close>
  by (intro freeable_assn.cl_assn_free freeable_assn.intro)
*)

interpretation monom_fa: freeable_assn monom_s_assn snhm.val.cl_free
  by unfold_locales (rule snhm.val.cl_assn_free)

sepref_register coeff_mcmp

sepref_def coeff_mcmp_impl is \<open>uncurry2 coeff_mcmp\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding coeff_mcmp_def rel2p_def var_order_rel''
  by sepref

sepref_register explode_while

sepref_def coeff_explode_impl is \<open>explode_while\<close>
  :: \<open>monom_s_assn\<^sup>d \<rightarrow>\<^sub>a cl_assn' monom_s_assn\<close>
  unfolding explode_while_def ls_emp
  by sepref

sepref_register coeff_merge_while

sepref_def coeff_merge_while_impl is \<open>uncurry2 coeff_merge_while\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a monom_s_assn\<^sup>d *\<^sub>a monom_s_assn\<^sup>d \<rightarrow>\<^sub>a monom_s_assn\<close>
  unfolding coeff_merge_while_def mcmp_merge_while_def mcmp_merge_while_inner_def
    ls_emp
  by sepref

sepref_register coeff_pass

sepref_def coeff_pass_impl is \<open>uncurry coeff_pass\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a (cl_assn' monom_s_assn)\<^sup>d \<rightarrow>\<^sub>a cl_assn' monom_s_assn\<close>
  unfolding coeff_pass_def mcmp_pass_def coeff_merge_while_def[symmetric]
    ls_emp ls_emp'
  by sepref

sepref_register coeff_run_passes

sepref_def coeff_run_passes_impl is \<open>uncurry coeff_run_passes\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a (cl_assn' monom_s_assn)\<^sup>d \<rightarrow>\<^sub>a cl_assn' monom_s_assn\<close>
  unfolding coeff_run_passes_def mcmp_run_passes_def coeff_pass_def[symmetric]
    ls_emp ls_emp'
  by sepref

sepref_register msort_coeffs

sepref_def msort_coeffs_impl is \<open>uncurry msort_coeffs\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a monom_s_assn\<^sup>d \<rightarrow>\<^sub>a monom_s_assn\<close>
  unfolding msort_coeffs_def mcmp_msort_def coeff_run_passes_def[symmetric]
    ls_emp ls_emp'
  by sepref

sepref_register term_mcmp

sepref_def term_mcmp_impl
  is \<open>uncurry2 term_mcmp\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a (monom_s_assn \<times>\<^sub>a sbi_assn)\<^sup>k *\<^sub>a (monom_s_assn \<times>\<^sub>a sbi_assn)\<^sup>k
     \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding term_mcmp_alt_def fold_ordered_discriminators
  by sepref

sepref_def term_explode_impl
  is \<open>explode_while\<close>
  :: \<open>poly_s_assn\<^sup>d \<rightarrow>\<^sub>a cl_assn' poly_s_assn\<close>
  unfolding explode_while_def ls_emp
  by sepref

sepref_register term_merge_while

sepref_def term_merge_while_impl
  is \<open>uncurry2 term_merge_while\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>d *\<^sub>a poly_s_assn\<^sup>d \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding term_merge_while_def mcmp_merge_while_def mcmp_merge_while_inner_def
    ls_emp
  by sepref

interpretation polys_s_ls: freeable_assn \<open>poly_s_assn\<close> \<open>poly_s.cl_free\<close>
  apply unfold_locales
  using poly_s.cl_assn_free by blast

sepref_register term_pass

sepref_def term_pass_impl
  is \<open>uncurry term_pass\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a (cl_assn' poly_s_assn)\<^sup>d \<rightarrow>\<^sub>a cl_assn' poly_s_assn\<close>
  unfolding term_pass_def mcmp_pass_def term_merge_while_def[symmetric]
    ls_emp ls_emp'
  by sepref

sepref_register term_run_passes

sepref_def term_run_passes_impl
  is \<open>uncurry term_run_passes\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a (cl_assn' poly_s_assn)\<^sup>d \<rightarrow>\<^sub>a cl_assn' poly_s_assn\<close>
  unfolding term_run_passes_def mcmp_run_passes_def term_pass_def[symmetric]
    ls_emp ls_emp'
  by sepref

interpretation poly_fa: copyable_assn poly_s_assn poly_s.cl_free poly_s.cl_copy
  apply unfold_locales
  apply (rule poly_s.cl_assn_free poly_s.cl_copy_hnr)+
  done

sepref_register msort_monoms

sepref_def msort_monoms_impl
  is \<open>uncurry msort_monoms\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>d \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding msort_monoms_def mcmp_msort_def term_run_passes_def[symmetric]
    ls_emp ls_emp'
  by sepref

lemmas [sepref_fr_rules] = msort_monoms_impl.refine

sepref_register sort_all_coeffs_s

sepref_def sort_all_coeffs_s'_impl is \<open>uncurry sort_all_coeffs_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>d \<rightarrow>\<^sub>a poly_s_assn\<close>
  supply [[goals_limit=1]]
  unfolding sort_all_coeffs_s_alt_def
    ls_emp ls_emp'
  by sepref

lemmas [sepref_fr_rules] = sort_all_coeffs_s'_impl.refine

interpretation si64: eq_assn si64_assn ll_icmp_eq
  by unfold_locales (rule hn_snat_ops(7))

sepref_register \<open>(=) :: nat list \<Rightarrow> nat list \<Rightarrow> bool\<close>

sepref_def merge_coeffs0_s_impl
  is \<open>RETURN o merge_coeffs0_s\<close>
  :: \<open>poly_s_assn\<^sup>d \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding merge_coeffs1_s_correct[symmetric]
  unfolding merge_coeffs1_s_def mc_body_s_def ls_emp ls_emp'
  by sepref
  

sepref_def full_normalize_poly'_impl
  is \<open>uncurry full_normalize_poly_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>d \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding full_normalize_poly_s_def
  by sepref

definition mnml_s_eq_impl' where [llvm_code]:
  \<open>mnml_s_eq_impl' \<equiv> \<lambda>pii qii. doM {
    let (pm,pn) = pii;
    let (qm,qn) = qii;
    r \<leftarrow> si64.cl_eq pm qm;
    llc_if r (signed_big_int_eq_impl pn qn) (Mreturn 0)
  }\<close>

context begin

interpretation llvm_prim_ctrl_setup .

lemma mnml_s_eq_hnr[sepref_fr_rules]:
  \<open>(uncurry mnml_s_eq_impl', uncurry (RETURN oo (=)))
  \<in> (monom_s_assn \<times>\<^sub>a sbi_assn)\<^sup>k *\<^sub>a (monom_s_assn \<times>\<^sub>a sbi_assn)\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding mnml_s_eq_impl'_def
  supply [vcg_rules] = hfref_htriple_k2[OF signed_big_int_eq_impl_hnr]
  supply [simp] = pure_def bool1_rel_def bool.rel_def in_br_conv
  by (sepref_to_hoare; vcg)

end

interpretation poly_s: eq_assn \<open>monom_s_assn \<times>\<^sub>a sbi_assn\<close> mnml_s_eq_impl'
  by unfold_locales (rule mnml_s_eq_hnr)

sepref_register poly_s_eq: \<open>(=) :: sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> bool\<close>

sepref_def weak_equality_l_s_impl
  is \<open>uncurry weak_equality_l_s\<close>
  :: \<open>poly_s_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding weak_equality_l_s_alt_def
  by sepref

interpretation polys_s: boxed_copying_pmap
  \<open>poly_s_assn\<close> \<open>poly_s.cl_free\<close> \<open>poly_s.cl_copy\<close>
  apply unfold_locales
  done

abbreviation polys_s_assn where
  \<open>polys_s_assn \<equiv> hr_comp (hr_comp polys_s.bx.pmap_assn' opt_list_map_rel) map_fmap_rel\<close>

lemma polys_s_assn_intf[intf_of_assn]:
  \<open>intf_of_assn polys_s_assn TYPE((nat, (nat list \<times> int) list) f_map)\<close>
  by simp

lemmas fmap_s_empty_hnr[sepref_fr_rules] =
  polys_s.bx.pmap_empty_hnr2[FCOMP fmempty_empty, unfolded op_fmap_empty_def[symmetric]]

lemmas fmap_s_delete_hnr[sepref_fr_rules] =
  polys_s.bx.pmap_delete_hnr2[FCOMP fmdrop_set_None]

lemmas fmap_s_update_hnr[sepref_fr_rules] =
  polys_s.bx.pmap_update_hnr2[FCOMP map_upd_fmupd]

lemmas fmap_s_contains_key_hnr[sepref_fr_rules] =
  polys_s.bx.pmap_contains_key_hnr2[FCOMP map_fmap_contains_key]

lemmas fmap_s_the_lookup_hnr[sepref_fr_rules] =
  polys_s.bx.cpmap_the_lookup_hnr2[FCOMP op_the_lookup_refine]

sepref_register import_monom_no_newS import_poly_no_newS check_linear_combi_l_pre_err

sepref_def import_monom_no_newS_impl
  is \<open>uncurry (import_monom_no_newS :: (nat,string)shared_vars \<Rightarrow> _ \<Rightarrow>( bool \<times> _) nres)\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a monom_assn\<^sup>d \<rightarrow>\<^sub>a bool1_assn \<times>\<^sub>a monom_s_assn\<close>
  unfolding import_monom_no_newS_alt_def ls_emp ls_emp'
  by sepref

lemmas [sepref_fr_rules] =
  import_monom_no_newS_impl.refine weak_equality_l_s_impl.refine

sepref_def import_poly_no_newS_impl
  is \<open>uncurry (import_poly_no_newS :: (nat,string)shared_vars \<Rightarrow> llist_polynomial \<Rightarrow>( bool \<times> sllist_polynomial) nres)\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>d \<rightarrow>\<^sub>a bool1_assn \<times>\<^sub>a poly_s_assn\<close>
  unfolding import_poly_no_newS_alt_def ls_emp ls_emp'
  by sepref

lemmas [sepref_fr_rules] =
  import_poly_no_newS_impl.refine

sepref_def s_fold_inner_impl is \<open>uncurry2 (RETURN ooo s_fold_inner)\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a strl_assn'\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding s_fold_inner_alt
  by sepref

definition [llvm_code]:
  \<open>vars_of_monom_in_s_impl xs \<V> \<equiv> cl_fold_env s_fold_inner_impl (\<V>, xs, 1)\<close>

lemma s_fold_inner_step_rule:
  \<open>llvm_htriple
    (shared_vars_assn \<V> vi ** bool1_assn b bi ** strl_assn' x xi)
    (s_fold_inner_impl vi bi xi)
    (\<lambda>r. shared_vars_assn \<V> vi ** bool1_assn (s_fold_inner \<V> b x) r ** strl_assn' x xi)\<close>
  supply [vcg_rules] = hfref_htriple_k3[OF s_fold_inner_impl.refine]
  apply vcg
  unfolding ENTAILS_def
  by (auto simp: entails_def pure_def sep_algebra_simps)

lemmas vars_of_monom_in_s_walk_rule =
  cl_fold_env_rule[where P = shared_vars_assn and R = bool1_assn and A = strl_assn'
    and f = s_fold_inner_impl and fa = s_fold_inner,
    OF s_fold_inner_step_rule]

lemma vars_of_monom_in_s_impl_hnr[sepref_fr_rules]:
  \<open>(uncurry vars_of_monom_in_s_impl, uncurry (RETURN oo vars_of_monom_in_s))
  \<in> monom_assn\<^sup>k *\<^sub>a shared_vars_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding vars_of_monom_in_s_impl_def
  apply sepref_to_hoare
  supply [vcg_rules] = vars_of_monom_in_s_walk_rule
  supply [simp] = vars_of_monom_in_s_foldl bool1_rel_def bool.rel_def in_br_conv
    pure_def
  by vcg

sepref_register vars_of_monom_in_s

sepref_def s_poly_inner_impl is \<open>uncurry2 (RETURN ooo s_poly_inner)\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a monomial_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding s_poly_inner_def
  by sepref

definition [llvm_code]:
  \<open>vars_of_poly_in_s_impl xs \<V> \<equiv> cl_fold_env s_poly_inner_impl (\<V>, xs, 1)\<close>

lemma s_poly_inner_step_rule:
  \<open>llvm_htriple
    (shared_vars_assn \<V> vi ** bool1_assn b bi ** monomial_assn x xi)
    (s_poly_inner_impl vi bi xi)
    (\<lambda>r. shared_vars_assn \<V> vi ** bool1_assn (s_poly_inner \<V> b x) r ** monomial_assn x xi)\<close>
  supply [vcg_rules] = hfref_htriple_k3[OF s_poly_inner_impl.refine]
  apply vcg
  unfolding ENTAILS_def
  by (auto simp: entails_def pure_def sep_algebra_simps)

lemmas vars_of_poly_in_s_walk_rule =
  cl_fold_env_rule[where P = shared_vars_assn and R = bool1_assn and A = monomial_assn
    and f = s_poly_inner_impl and fa = s_poly_inner,
    OF s_poly_inner_step_rule]

lemma vars_of_poly_in_s_impl_hnr[sepref_fr_rules]:
  \<open>(uncurry vars_of_poly_in_s_impl, uncurry (RETURN oo vars_of_poly_in_s))
  \<in> polynomial_assn\<^sup>k *\<^sub>a shared_vars_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding vars_of_poly_in_s_impl_def
  apply sepref_to_hoare
  supply [vcg_rules] = vars_of_poly_in_s_walk_rule
  supply [simp] = vars_of_poly_in_s_foldl bool1_rel_def bool.rel_def in_br_conv
    pure_def
  by vcg

sepref_register vars_of_poly_in_s

sepref_def vars_llist_in_s_impl
  is \<open>uncurry (RETURN oo vars_llist_in_s)\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding vars_llist_in_s_alt_def
  by sepref

lemmas [sepref_fr_rules] = vars_llist_in_s_impl.refine

sepref_register mult_poly_s normalize_poly_s

sepref_def normalize_poly_sharedS_impl
  is \<open>uncurry normalize_poly_sharedS\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>d \<rightarrow>\<^sub>a bool1_assn \<times>\<^sub>a poly_s_assn\<close>
  unfolding normalize_poly_sharedS_def
  by sepref

lemmas [sepref_fr_rules] = normalize_poly_sharedS_impl.refine
  mult_poly_s_impl.refine

sepref_def merge_coeffs_s_impl
  is \<open>(RETURN o merge_coeffs_s)\<close>
  :: \<open>poly_s_assn\<^sup>d \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding merge_coeffs2_s_correct[symmetric]
  unfolding merge_coeffs2_s_def mc2_body_s_def ls_emp ls_emp'
  by sepref

lemmas [sepref_fr_rules] = merge_coeffs_s_impl.refine

sepref_def normalize_poly_s_impl
  is \<open>uncurry normalize_poly_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>d \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding normalize_poly_s_def
  by sepref

lemmas [sepref_fr_rules] = normalize_poly_s_impl.refine

sepref_def mult_poly_full_s_impl
  is \<open>uncurry2 mult_poly_full_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k*\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding mult_poly_full_s_def
  by sepref

lemmas [sepref_fr_rules] = mult_poly_full_s_impl.refine
  add_poly_l_prep_impl.refine

section \<open>Fused Lookup\<close>
text \<open>In it's basic form, pasteque roughly does the following when checking linear combinations:
  \<open>p \<leftarrow> lookup A i  \<comment> \<open>To lookup polynomial p from A\<close>
  r \<leftarrow> add_poly r p \<comment> \<open>Update r to r + p\<close>\<close>
  Due to how the lookup map is implemented, (lookup copies the element out),
  This amounts to copying \<open>p\<close> for every addition, even though addition is implemented
  read-only (by use of interleaving fold) and does not consume \<open>p\<close>.
  As a solution, we implement a fused version of above code that will
  1. extract \<open>p\<close> from \<open>A\<close>, setting \<open>A[i := None]\<close>
  2. Update \<open>r \<leftarrow> r + p\<close>
  3. Put \<open>p\<close> back into \<open>A[i := p]\<close>
  which avoids the copy and moves \<open>p\<close> out and in again instead.
\<close>

definition fused_lookup_add 
  :: \<open>(nat, string) shared_vars \<Rightarrow> (nat, sllist_polynomial) fmap \<Rightarrow> 
       nat \<Rightarrow> sllist_polynomial \<Rightarrow> (nat list \<times> int) list nres\<close>
where
  \<open>fused_lookup_add \<V> A i p \<equiv> doN {
    let r = the (fmlookup A i);
    add_poly_l_s \<V> (p, r)
  }\<close>

lemma fused_lookup_rewrite:
  \<open>(let r = A \<propto> i in add_poly_l_s \<V> (p, r)) = fused_lookup_add \<V> A i p\<close>
  unfolding fused_lookup_add_def by simp 

definition[llvm_code]: \<open>fused_lookup_add_alt_impl \<equiv> \<lambda>\<V>i Ai ii pi. doM {
  (bi, Ai) \<leftarrow> polys_s.bx.pmap_extract ii Ai;
  ri \<leftarrow> ll_load bi;
  qi \<leftarrow> add_poly_l_prep_impl \<V>i (pi, ri);
  Ai \<leftarrow> arl_upd Ai ii bi;
  Mreturn qi
}\<close>

lemma ll_load_box_rule:
  \<open>llvm_htriple (\<upharpoonleft>(box_assn A) x p) (ll_load p) (\<lambda>c. \<upharpoonleft>ll_bpto c p ** A x c)\<close>
  unfolding box_assn_def by vcg

lemma box_assn_reassemble:
  \<open>\<upharpoonleft>ll_bpto c p ** A x c \<turnstile> \<upharpoonleft>(box_assn A) x p\<close>
  unfolding box_assn_def
  apply (simp add: sep_algebra_simps)
  apply (rule entails_exI[where x=c])
  by (rule entails_refl)

lemma hfref_nres_htriple_k1_k2_pair:
  assumes R: \<open>(uncurry fi, uncurry fn) \<in> P\<^sup>k *\<^sub>a (A \<times>\<^sub>a B)\<^sup>k \<rightarrow>\<^sub>a C\<close>
    and NF: \<open>nofail (fn e (a, b))\<close>
  shows \<open>llvm_htriple (P e ei ** A a ai ** B b bi) (fi ei (ai, bi))
    (\<lambda>r. P e ei ** A a ai ** B b bi ** (EXS x. C x r ** \<up>(RETURN x \<le> fn e (a, b))))\<close>
proof -
  note HT = R[to_hnr, unfolded autoref_tag_defs, THEN hn_refineD, OF NF]
  show ?thesis
    apply (rule htriple_ent_pre[OF _ htriple_ent_post[OF _ HT]])
    unfolding hn_ctxt_def
    subgoal by (simp add: prod_assn_def sep_conj_assoc entails_refl)
    subgoal
      by (auto simp: entails_def sep_algebra_simps sep_conj_exists invalid_assn_def
          prod_assn_def pred_lift_extract_simps)
    done
qed

lemmas add_poly_l_prep_rule = hfref_nres_htriple_k1_k2_pair[OF add_poly_l_prep_impl.refine]

lemma opt_list_contains_key_lt:
  \<open>opt_list_contains_key i xs \<Longrightarrow> i < length xs\<close>
  unfolding opt_list_contains_key_def by (auto split: if_splits)

lemma pmap_extract_present_rule:
  \<open>llvm_htriple
    (\<upharpoonleft>snat.assn i ii ** polys_s.bx.pmap_assn' xs ai ** \<up>\<^sub>d(i < length xs))
    (polys_s.bx.pmap_extract ii ai)
    (\<lambda>(a, ai'). polys_s.bx.pmap_assn' (xs[i := Option.None]) ai' **
      polys_s.bx.option_assn (opt_list_lookup i xs) a ** \<up>(ai' = ai))\<close>
  unfolding polys_s.bx.pmap_extract_def opt_list_lookup_def
  supply [simp] = polys_s.bx.pmap_assn_def polys_s.bx.dflt_is_init[symmetric]
  apply vcg
  subgoal
    unfolding ENTAILS_def
    apply (rule entails_trans[OF polys_s.bx.pmap_lookup_reassemble_present[unfolded ENTAILS_def]])
     apply assumption
    by (simp add: sep_algebra_simps pred_lift_extract_simps entails_refl)
  apply vcg
  done

lemma pure_entails_emp: \<open>\<up>P \<turnstile> \<box>\<close>
  by (auto simp: entails_def sep_algebra_simps pred_lift_extract_simps)

lemma pmap_put_back_reassemble:
  assumes K: \<open>k < length xs\<close> and N: \<open>xs ! k = Option.None\<close>
  shows \<open>ENTAILS
    (\<upharpoonleft>iarl_assn (xsi[k := vi]) ai **
     \<upharpoonleft>(list_assn (mk_assn polys_s.bx.option_assn)) xs xsi ** \<upharpoonleft>(box_assn poly_s_assn) v vi)
    (EXS z. \<upharpoonleft>iarl_assn z ai **
       \<upharpoonleft>(list_assn (mk_assn polys_s.bx.option_assn)) (xs[k := Option.Some v]) z)\<close>
proof (cases \<open>length xs = length xsi\<close>)
  case True
  have X: \<open>xs[k := Option.None] = xs\<close>
    using N by (metis list_update_id)
  text \<open>Both focusing equations regenerate their own left-hand side (modulo \<open>X\<close>),
    so they are applied once with \<open>subst\<close> rather than as simp rules.\<close>
  show ?thesis
    unfolding ENTAILS_def
    apply (subst polys_s.bx.list_assn_option_focus[OF K])
    apply (simp add: N X polys_s.bx.option_assn_None_conv sep_algebra_simps
        pred_lift_extract_simps)
    apply (rule entails_trans[OF conj_entails_mono[OF pure_entails_emp entails_refl]])
    apply (simp add: sep_algebra_simps)
    apply (rule entails_exI[where x=\<open>xsi[k := vi]\<close>])
    apply (subst polys_s.bx.list_assn_option_insert[OF K])
    apply (simp add: X)
    by (simp add: sep_conj_aci entails_refl)
next
  case False
  then show ?thesis
    unfolding ENTAILS_def by (auto simp: entails_def sep_algebra_simps)
qed

lemma pmap_put_back_rule:
  \<open>llvm_htriple
    (\<upharpoonleft>snat.assn k ki ** \<upharpoonleft>(box_assn poly_s_assn) v vi ** polys_s.bx.pmap_assn' xs ai **
      \<up>\<^sub>d(k < length xs \<and> xs ! k = Option.None))
    (arl_upd ai ki vi)
    (\<lambda>ai'. polys_s.bx.pmap_assn' (xs[k := Option.Some v]) ai' ** \<up>(ai' = ai))\<close>
  supply [simp] = polys_s.bx.pmap_assn_def
  apply vcg
  subgoal
    unfolding ENTAILS_def
    apply (rule entails_trans[OF pmap_put_back_reassemble[unfolded ENTAILS_def]])
      apply assumption
     apply assumption
    by (simp add: sep_algebra_simps pred_lift_extract_simps entails_refl)
  done

lemma pmap_put_back_open_box_rule:
  \<open>llvm_htriple
    (\<upharpoonleft>snat.assn k ki ** (\<upharpoonleft>ll_bpto c bi ** poly_s_assn v c) **
      polys_s.bx.pmap_assn' xs ai ** \<up>\<^sub>d(k < length xs \<and> xs ! k = Option.None))
    (arl_upd ai ki bi)
    (\<lambda>ai'. polys_s.bx.pmap_assn' (xs[k := Option.Some v]) ai' ** \<up>(ai' = ai))\<close>
  apply (rule htriple_ent_pre[OF _ pmap_put_back_rule])
  by (intro conj_entails_mono entails_refl box_assn_reassemble)

lemma opt_list_put_back:
  assumes \<open>opt_list_contains_key i xs\<close>
  shows \<open>xs[i := Option.Some (opt_list_the_lookup i xs)] = xs\<close>
  using assms unfolding opt_list_contains_key_def opt_list_the_lookup_def
  apply (cases \<open>xs ! i\<close>)
   apply (auto split: if_splits)
  by (metis list_update_id)

definition fused_lookup_add_ol
  :: \<open>(nat, string) shared_vars \<Rightarrow> sllist_polynomial opt_list \<Rightarrow>
       nat \<Rightarrow> sllist_polynomial \<Rightarrow> (nat list \<times> int) list nres\<close>
where
  \<open>fused_lookup_add_ol \<V> xs i p \<equiv> doN {
    let r = opt_list_the_lookup i xs;
    add_poly_l_s \<V> (p, r)
  }\<close>

lemma fused_lookup_add_ol_rule:
  assumes NF: \<open>nofail (fused_lookup_add_ol \<V> xs i p)\<close>
    and K: \<open>opt_list_contains_key i xs\<close>
  shows \<open>llvm_htriple
    (shared_vars_assn \<V> \<V>i ** polys_s.bx.pmap_assn' xs Ai ** \<upharpoonleft>snat.assn i ii **
      poly_s_assn p pc)
    (fused_lookup_add_alt_impl \<V>i Ai ii pc)
    (\<lambda>q. shared_vars_assn \<V> \<V>i ** polys_s.bx.pmap_assn' xs Ai ** \<upharpoonleft>snat.assn i ii **
      poly_s_assn p pc **
      (EXS x. poly_s_assn x q ** \<up>(RETURN x \<le> fused_lookup_add_ol \<V> xs i p)))\<close>
  unfolding fused_lookup_add_alt_impl_def
  supply [vcg_rules del] = polys_s.bx.pmap_extract_rule
  supply [vcg_rules] = pmap_extract_present_rule ll_load_box_rule add_poly_l_prep_rule
    pmap_put_back_open_box_rule
  supply [simp] = polys_s.bx.opt_list_the_lookup_conv[OF K] opt_list_put_back[OF K]
    opt_list_contains_key_lt[OF K]
  using NF unfolding fused_lookup_add_ol_def
  apply vcg
  done

lemma fused_lookup_add_ol_rule':
  \<open>llvm_htriple
    (shared_vars_assn \<V> \<V>i ** polys_s.bx.pmap_assn' xs Ai ** \<upharpoonleft>snat.assn i ii **
      poly_s_assn p pc **
      \<up>(nofail (fused_lookup_add_ol \<V> xs i p) \<and> opt_list_contains_key i xs))
    (fused_lookup_add_alt_impl \<V>i Ai ii pc)
    (\<lambda>q. shared_vars_assn \<V> \<V>i ** polys_s.bx.pmap_assn' xs Ai ** \<upharpoonleft>snat.assn i ii **
      poly_s_assn p pc **
      (EXS x. poly_s_assn x q ** \<up>(RETURN x \<le> fused_lookup_add_ol \<V> xs i p)))\<close>
proof (rule htriple_pure_preI)
  assume \<open>pure_part (shared_vars_assn \<V> \<V>i ** polys_s.bx.pmap_assn' xs Ai **
    \<upharpoonleft>snat.assn i ii ** poly_s_assn p pc **
    \<up>(nofail (fused_lookup_add_ol \<V> xs i p) \<and> opt_list_contains_key i xs))\<close>
  then have NF: \<open>nofail (fused_lookup_add_ol \<V> xs i p)\<close>
    and K: \<open>opt_list_contains_key i xs\<close>
    by (auto dest!: pure_part_split_conj)
  show ?thesis
    apply (rule htriple_ent_pre[OF _ fused_lookup_add_ol_rule[OF NF K]])
    by (auto simp: entails_def sep_algebra_simps pred_lift_extract_simps)
qed

lemma fused_lookup_add_ol_rule'':
  \<open>llvm_htriple
    (shared_vars_assn \<V> \<V>i ** polys_s.bx.pmap_assn' xs Ai ** snat_assn i ii **
      poly_s_assn p pc **
      \<up>(nofail (fused_lookup_add_ol \<V> xs i p) \<and> opt_list_contains_key i xs))
    (fused_lookup_add_alt_impl \<V>i Ai ii pc)
    (\<lambda>q. shared_vars_assn \<V> \<V>i ** polys_s.bx.pmap_assn' xs Ai ** snat_assn i ii **
      poly_s_assn p pc **
      (EXS x. poly_s_assn x q ** \<up>(RETURN x \<le> fused_lookup_add_ol \<V> xs i p)))\<close>
  unfolding snat_rel_def snat.assn_is_rel[symmetric]
  by (rule fused_lookup_add_ol_rule'[unfolded snat_rel_def snat.assn_is_rel[symmetric]])

lemma fused_lookup_add_ol_hnr:
  \<open>(uncurry3 fused_lookup_add_alt_impl, uncurry3 fused_lookup_add_ol)
  \<in> [\<lambda>(((\<V>, xs), i), p). opt_list_contains_key i xs]\<^sub>a
      shared_vars_assn\<^sup>k *\<^sub>a polys_s.bx.pmap_assn'\<^sup>k *\<^sub>a (snat_assn' TYPE(64))\<^sup>k *\<^sub>a
        poly_s_assn\<^sup>k
      \<rightarrow> poly_s_assn\<close>
  supply [vcg_rules] = fused_lookup_add_ol_rule''
  supply [simp] = pure_def
  by (sepref_to_hoare; vcg)

definition fused_lookup_add_m
  :: \<open>(nat, string) shared_vars \<Rightarrow> (nat \<rightharpoonup> sllist_polynomial) \<Rightarrow>
       nat \<Rightarrow> sllist_polynomial \<Rightarrow> (nat list \<times> int) list nres\<close>
where
  \<open>fused_lookup_add_m \<V> m i p \<equiv> doN {
    let r = the (m i);
    add_poly_l_s \<V> (p, r)
  }\<close>

lemma fused_lookup_add_ol_refine:
  \<open>(uncurry3 fused_lookup_add_ol, uncurry3 fused_lookup_add_m)
   \<in> [\<lambda>(((_, m), i), _). m i \<noteq> None]\<^sub>f
       ((Id \<times>\<^sub>r opt_list_map_rel) \<times>\<^sub>r nat_rel) \<times>\<^sub>r Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  by (auto simp: fused_lookup_add_ol_def fused_lookup_add_m_def opt_list_map_rel_def
      in_br_conv opt_list_the_lookup_def opt_list_\<alpha>_def split: if_splits)

lemma fused_lookup_add_m_refine:
  \<open>(uncurry3 fused_lookup_add_m, uncurry3 fused_lookup_add)
   \<in> [\<lambda>(((_, A), i), _). i \<in># dom_m A]\<^sub>f
       ((Id \<times>\<^sub>r map_fmap_rel) \<times>\<^sub>r Id) \<times>\<^sub>r Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  by (auto simp: fused_lookup_add_m_def fused_lookup_add_def map_fmap_rel_def br_def
      fmap.Abs_fmap_inverse)

lemma fmlookup_Some_dom_m: \<open>(\<exists>y. fmlookup A i = Some y) \<longleftrightarrow> i \<in># dom_m A\<close>
  by (cases \<open>fmlookup A i\<close>) (auto simp: in_fdom_alt)

lemmas fused_lookup_add_hnr_chain =
  fused_lookup_add_ol_hnr[FCOMP fused_lookup_add_ol_refine, FCOMP fused_lookup_add_m_refine]

lemma fused_lookup_add_alt_impl_hnr[sepref_fr_rules]:
  \<open>(uncurry3 fused_lookup_add_alt_impl, uncurry3 fused_lookup_add)
  \<in> [\<lambda>(((\<V>, A), i), p). i \<in># dom_m A]\<^sub>a
      shared_vars_assn\<^sup>k *\<^sub>a polys_s_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(64))\<^sup>k *\<^sub>a poly_s_assn\<^sup>k
      \<rightarrow> poly_s_assn\<close>
  using fused_lookup_add_hnr_chain by (simp add: fmlookup_Some_dom_m)

sepref_register fused_lookup_add ::
  \<open>(nat, string) shared_vars \<Rightarrow> (nat, sllist_polynomial) f_map \<Rightarrow> nat \<Rightarrow>
    sllist_polynomial \<Rightarrow> (nat list \<times> int) list nres\<close>

definition fused_lookup_mult :: 
  \<open>(nat, string) shared_vars \<Rightarrow> (nat, sllist_polynomial) fmap \<Rightarrow> nat \<Rightarrow>
    sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> (nat list \<times> int) list nres\<close> where
  \<open>fused_lookup_mult \<V> A i p q \<equiv> doN {
    let r = the (fmlookup A i);
    q \<leftarrow> mult_poly_full_s \<V> q r;
    add_poly_l_s \<V> (p, q) 
  }\<close>

lemma fused_lookup_mult_rewrite:
  \<open>(let r = A \<propto> i in do {
      q \<leftarrow> mult_poly_full_s \<V> q r;
      pq \<leftarrow> add_poly_l_s \<V> (p, q);
      f pq
    }) = do {
      pq \<leftarrow> fused_lookup_mult \<V> A i p q;
      f pq
    }\<close>
  unfolding fused_lookup_mult_def by (simp add: nres_monad_laws)

definition[llvm_code]: \<open>fused_lookup_mult_impl \<equiv> \<lambda>\<V>i Ai ii pi qi. doM {
  (bi, Ai) \<leftarrow> polys_s.bx.pmap_extract ii Ai;
  ri \<leftarrow> ll_load bi;
  qri \<leftarrow> mult_poly_full_s_impl \<V>i qi ri;
  si \<leftarrow> add_poly_l_prep_impl \<V>i (pi, qri);
  poly_s.cl_free qri;
  Ai \<leftarrow> arl_upd Ai ii bi;
  Mreturn si
  }\<close>

lemmas mult_poly_full_s_rule = hfref_nres_htriple_k1_k2_k3[OF mult_poly_full_s_impl.refine]

definition fused_lookup_mult_ol
  :: \<open>(nat, string) shared_vars \<Rightarrow> sllist_polynomial opt_list \<Rightarrow>
       nat \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> (nat list \<times> int) list nres\<close>
where
  \<open>fused_lookup_mult_ol \<V> xs i p q \<equiv> doN {
    let r = opt_list_the_lookup i xs;
    q \<leftarrow> mult_poly_full_s \<V> q r;
    add_poly_l_s \<V> (p, q) 
  }\<close>

lemma fused_lookup_mult_ol_nofailD:
  assumes \<open>nofail (fused_lookup_mult_ol \<V> xs i p q)\<close>
  shows \<open>nofail (mult_poly_full_s \<V> q (opt_list_the_lookup i xs))\<close>
    and \<open>RETURN x \<le> mult_poly_full_s \<V> q (opt_list_the_lookup i xs) \<Longrightarrow>
      nofail (add_poly_l_s \<V> (p, x))\<close>
  using assms unfolding fused_lookup_mult_ol_def
  by (auto simp: pw_le_iff refine_pw_simps)

lemma fused_lookup_mult_ol_post:
  assumes \<open>nofail (fused_lookup_mult_ol \<V> xs i p q)\<close>
    and \<open>RETURN x \<le> mult_poly_full_s \<V> q (opt_list_the_lookup i xs)\<close>
    and \<open>RETURN s \<le> add_poly_l_s \<V> (p, x)\<close>
  shows \<open>RETURN s \<le> fused_lookup_mult_ol \<V> xs i p q\<close>
  using assms unfolding fused_lookup_mult_ol_def
  by (auto simp: pw_le_iff refine_pw_simps)

lemma fused_lookup_mult_ol_rule:
  assumes NF: \<open>nofail (fused_lookup_mult_ol \<V> xs i p q)\<close>
    and K: \<open>opt_list_contains_key i xs\<close>
  shows \<open>llvm_htriple
    (shared_vars_assn \<V> \<V>i ** polys_s.bx.pmap_assn' xs Ai ** \<upharpoonleft>snat.assn i ii **
      poly_s_assn p pc ** poly_s_assn q qc)
    (fused_lookup_mult_impl \<V>i Ai ii pc qc)
    (\<lambda>s. shared_vars_assn \<V> \<V>i ** polys_s.bx.pmap_assn' xs Ai ** \<upharpoonleft>snat.assn i ii **
      poly_s_assn p pc ** poly_s_assn q qc **
      (EXS x. poly_s_assn x s ** \<up>(RETURN x \<le> fused_lookup_mult_ol \<V> xs i p q)))\<close>
  unfolding fused_lookup_mult_impl_def
  supply [vcg_rules del] = polys_s.bx.pmap_extract_rule
  supply [vcg_rules] = pmap_extract_present_rule ll_load_box_rule mult_poly_full_s_rule
    add_poly_l_prep_rule pmap_put_back_open_box_rule MK_FREED[OF poly_s.cl_assn_free]
  supply [simp] = polys_s.bx.opt_list_the_lookup_conv[OF K] opt_list_put_back[OF K]
    opt_list_contains_key_lt[OF K] fused_lookup_mult_ol_nofailD[OF NF]
    fused_lookup_mult_ol_post[OF NF]
  apply vcg
  done

lemma fused_lookup_mult_ol_rule':
  \<open>llvm_htriple
    (shared_vars_assn \<V> \<V>i ** polys_s.bx.pmap_assn' xs Ai ** \<upharpoonleft>snat.assn i ii **
      poly_s_assn p pc ** poly_s_assn q qc **
      \<up>(nofail (fused_lookup_mult_ol \<V> xs i p q) \<and> opt_list_contains_key i xs))
    (fused_lookup_mult_impl \<V>i Ai ii pc qc)
    (\<lambda>s. shared_vars_assn \<V> \<V>i ** polys_s.bx.pmap_assn' xs Ai ** \<upharpoonleft>snat.assn i ii **
      poly_s_assn p pc ** poly_s_assn q qc **
      (EXS x. poly_s_assn x s ** \<up>(RETURN x \<le> fused_lookup_mult_ol \<V> xs i p q)))\<close>
proof (rule htriple_pure_preI)
  assume \<open>pure_part (shared_vars_assn \<V> \<V>i ** polys_s.bx.pmap_assn' xs Ai **
    \<upharpoonleft>snat.assn i ii ** poly_s_assn p pc ** poly_s_assn q qc **
    \<up>(nofail (fused_lookup_mult_ol \<V> xs i p q) \<and> opt_list_contains_key i xs))\<close>
  then have NF: \<open>nofail (fused_lookup_mult_ol \<V> xs i p q)\<close>
    and K: \<open>opt_list_contains_key i xs\<close>
    by (auto dest!: pure_part_split_conj)
  show ?thesis
    apply (rule htriple_ent_pre[OF _ fused_lookup_mult_ol_rule[OF NF K]])
    by (auto simp: entails_def sep_algebra_simps pred_lift_extract_simps)
qed

lemma fused_lookup_mult_ol_rule'':
  \<open>llvm_htriple
    (shared_vars_assn \<V> \<V>i ** polys_s.bx.pmap_assn' xs Ai ** snat_assn i ii **
      poly_s_assn p pc ** poly_s_assn q qc **
      \<up>(nofail (fused_lookup_mult_ol \<V> xs i p q) \<and> opt_list_contains_key i xs))
    (fused_lookup_mult_impl \<V>i Ai ii pc qc)
    (\<lambda>s. shared_vars_assn \<V> \<V>i ** polys_s.bx.pmap_assn' xs Ai ** snat_assn i ii **
      poly_s_assn p pc ** poly_s_assn q qc **
      (EXS x. poly_s_assn x s ** \<up>(RETURN x \<le> fused_lookup_mult_ol \<V> xs i p q)))\<close>
  unfolding snat_rel_def snat.assn_is_rel[symmetric]
  by (rule fused_lookup_mult_ol_rule'[unfolded snat_rel_def snat.assn_is_rel[symmetric]])

lemma fused_lookup_mult_ol_hnr:
  \<open>(uncurry4 fused_lookup_mult_impl, uncurry4 fused_lookup_mult_ol)
  \<in> [\<lambda>((((\<V>, xs), i), p), q). opt_list_contains_key i xs]\<^sub>a
      shared_vars_assn\<^sup>k *\<^sub>a polys_s.bx.pmap_assn'\<^sup>k *\<^sub>a (snat_assn' TYPE(64))\<^sup>k *\<^sub>a
        poly_s_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k
      \<rightarrow> poly_s_assn\<close>
  supply [vcg_rules] = fused_lookup_mult_ol_rule''
  supply [simp] = pure_def
  by (sepref_to_hoare; vcg)

definition fused_lookup_mult_m
  :: \<open>(nat, string) shared_vars \<Rightarrow> (nat \<rightharpoonup> sllist_polynomial) \<Rightarrow>
       nat \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> (nat list \<times> int) list nres\<close>
where
  \<open>fused_lookup_mult_m \<V> m i p q \<equiv> doN {
    let r = the (m i);
    q \<leftarrow> mult_poly_full_s \<V> q r;
    add_poly_l_s \<V> (p, q)
  }\<close>

lemma fused_lookup_mult_ol_refine:
  \<open>(uncurry4 fused_lookup_mult_ol, uncurry4 fused_lookup_mult_m)
   \<in> [\<lambda>((((_, m), i), _), _). m i \<noteq> None]\<^sub>f
       (((Id \<times>\<^sub>r opt_list_map_rel) \<times>\<^sub>r nat_rel) \<times>\<^sub>r Id) \<times>\<^sub>r Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  by (auto simp: fused_lookup_mult_ol_def fused_lookup_mult_m_def opt_list_map_rel_def
      in_br_conv opt_list_the_lookup_def opt_list_\<alpha>_def split: if_splits)

lemma fused_lookup_mult_m_refine:
  \<open>(uncurry4 fused_lookup_mult_m, uncurry4 fused_lookup_mult)
   \<in> [\<lambda>((((_, A), i), _), _). i \<in># dom_m A]\<^sub>f
       (((Id \<times>\<^sub>r map_fmap_rel) \<times>\<^sub>r Id) \<times>\<^sub>r Id) \<times>\<^sub>r Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  by (auto simp: fused_lookup_mult_m_def fused_lookup_mult_def map_fmap_rel_def br_def
      fmap.Abs_fmap_inverse)

lemmas fused_lookup_mult_hnr_chain =
  fused_lookup_mult_ol_hnr[FCOMP fused_lookup_mult_ol_refine, FCOMP fused_lookup_mult_m_refine]

lemma fused_lookup_mult_impl_hnr[sepref_fr_rules]:
  \<open>(uncurry4 fused_lookup_mult_impl, uncurry4 fused_lookup_mult)
  \<in> [\<lambda>((((\<V>, A), i), p), q). i \<in># dom_m A]\<^sub>a
      shared_vars_assn\<^sup>k *\<^sub>a polys_s_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(64))\<^sup>k *\<^sub>a poly_s_assn\<^sup>k *\<^sub>a
        poly_s_assn\<^sup>k
      \<rightarrow> poly_s_assn\<close>
  using fused_lookup_mult_hnr_chain by (simp add: fmlookup_Some_dom_m)

sepref_register fused_lookup_mult ::
  \<open>(nat, string) shared_vars \<Rightarrow> (nat, sllist_polynomial) f_map \<Rightarrow> nat \<Rightarrow>
    sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> (nat list \<times> int) list nres\<close>

sepref_register add_poly_l_s
sepref_def linear_combi_l_prep_s_impl
  is \<open>uncurry3 linear_combi_l_prep_s\<close>
  :: \<open>si64_assn\<^sup>k *\<^sub>a polys_s_assn\<^sup>k *\<^sub>a shared_vars_assn\<^sup>k *\<^sub>a
  (cl_assn' (polynomial_assn \<times>\<^sub>a si64_assn))\<^sup>d  \<rightarrow>\<^sub>a
  poly_s_assn \<times>\<^sub>a (cl_assn' (polynomial_assn \<times>\<^sub>a si64_assn)) \<times>\<^sub>a status_assn
  \<close>
  supply [[goals_limit=1]]
  unfolding linear_combi_l_prep_s_alt
  unfolding fused_lookup_rewrite fused_lookup_mult_rewrite
  unfolding
    fmlookup'_def[symmetric]
    in_dom_by_contains
    ls_emp ls_emp'
  by sepref

lemmas [sepref_fr_rules] = linear_combi_l_prep_s_impl.refine

sepref_register linear_combi_l_prep_s ::
  \<open>nat \<Rightarrow> (nat, sllist_polynomial) f_map \<Rightarrow> (nat, string) shared_vars \<Rightarrow>
    (llist_polynomial \<times> nat) list \<Rightarrow>
    (sllist_polynomial \<times> (llist_polynomial \<times> nat) list \<times> string code_status) nres\<close>

sepref_def check_linear_combi_l_s_impl
  is \<open>uncurry5 check_linear_combi_l_s\<close>
  :: \<open>poly_s_assn\<^sup>k *\<^sub>a polys_s_assn\<^sup>k *\<^sub>a shared_vars_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k *\<^sub>a
  (cl_assn' (polynomial_assn \<times>\<^sub>a si64_assn))\<^sup>d *\<^sub>a polynomial_assn\<^sup>d \<rightarrow>\<^sub>a status_assn \<times>\<^sub>a poly_s_assn
  \<close>
  supply [[goals_limit=1]]
  unfolding check_linear_combi_l_s_def
    in_dom_by_contains
    ls_emp ls_emp'
  by sepref

sepref_register fmlookup'

sepref_register uminus_poly_s

sepref_def uminus_poly_s_impl is \<open>uminus_poly_s_nres\<close>
  :: \<open>poly_s_assn\<^sup>d \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding uminus_poly_s_nres_def ls_emp ls_emp'
  by sepref

lemmas uminus_poly_s_hnr[sepref_fr_rules] =
  uminus_poly_s_impl.refine[FCOMP uminus_poly_s_fref]

sepref_register import_monomS import_polyS

sepref_def import_monomS_impl
  is \<open>uncurry (import_monomS :: (nat, string) shared_vars \<Rightarrow> _)\<close>
  :: \<open>shared_vars_assn\<^sup>d *\<^sub>a monom_assn\<^sup>k \<rightarrow>\<^sub>a memory_allocation_assn \<times>\<^sub>a monom_s_assn \<times>\<^sub>a shared_vars_assn\<close>
  supply [[goals_limit=1]]
  unfolding import_monomS_alt_def
    ls_emp ls_emp'
  by sepref

lemmas [sepref_fr_rules] = import_monomS_impl.refine

sepref_def import_polyS_impl
  is \<open>uncurry (import_polyS :: (nat, string) shared_vars \<Rightarrow> llist_polynomial \<Rightarrow> _)\<close>
  :: \<open>shared_vars_assn\<^sup>d *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a memory_allocation_assn \<times>\<^sub>a poly_s_assn \<times>\<^sub>a shared_vars_assn\<close>
  supply [[goals_limit=1]]
  unfolding import_polyS_alt_def
    ls_emp ls_emp'
  by sepref

lemmas [sepref_fr_rules] = import_polyS_impl.refine

sepref_register mult_poly_full_s weak_equality_l_s check_extension_l_s_side_cond_err
     is_cfailed check_del_l

sepref_register check_extension_l2_s ::
  \<open>'b \<Rightarrow> (nat, 'c) f_map \<Rightarrow> (nat, string) shared_vars \<Rightarrow> nat \<Rightarrow> string \<Rightarrow>
    llist_polynomial \<Rightarrow>
    (string code_status \<times> sllist_polynomial \<times> (nat, string) shared_vars \<times> nat) nres\<close>

sepref_register check_linear_combi_l_s ::
  \<open>sllist_polynomial \<Rightarrow> (nat, sllist_polynomial) f_map \<Rightarrow> (nat, string) shared_vars \<Rightarrow>
    nat \<Rightarrow> (llist_polynomial \<times> nat) list \<Rightarrow> llist_polynomial \<Rightarrow>
    (string code_status \<times> sllist_polynomial) nres\<close>

sepref_def check_extension_l_impl
  is \<open>uncurry5 check_extension_l2_s\<close>
    :: \<open>poly_s_assn\<^sup>k *\<^sub>a polys_s_assn\<^sup>k *\<^sub>a shared_vars_assn\<^sup>d *\<^sub>a si64_assn\<^sup>k *\<^sub>a
    strl_assn'\<^sup>k *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a status_assn \<times>\<^sub>a poly_s_assn \<times>\<^sub>a shared_vars_assn \<times>\<^sub>a si64_assn
  \<close>
  supply [[goals_limit=1]]
  unfolding check_extension_l2_s_alt_def
    in_dom_by_contains
    ls_emp ls_emp'
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_def check_del_l_impl
  is \<open>uncurry2 check_del_l\<close>
  :: \<open>poly_s_assn\<^sup>k *\<^sub>a polys_s_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k \<rightarrow>\<^sub>a status_assn\<close>
  unfolding check_del_l_def
  by sepref

lemmas [sepref_fr_rules] =
  check_extension_l_impl.refine
  check_linear_combi_l_s_impl.refine
  check_del_l_impl.refine

sepref_def check_step_s_impl
  is \<open>uncurry4 PAC_checker_l_step_s_alt\<close>
  :: \<open>poly_s_assn\<^sup>k *\<^sub>a status_assn\<^sup>d *\<^sub>a shared_vars_assn\<^sup>d *\<^sub>a polys_s_assn\<^sup>d *\<^sub>a lpac_step_assn\<^sup>d \<rightarrow>\<^sub>a
    status_assn \<times>\<^sub>a shared_vars_assn \<times>\<^sub>a polys_s_assn\<close>
  supply [[goals_limit=1]]
  supply [sepref_frame_free_rules] = poly.cl_assn_free (* Need this to force our custom free *)
  unfolding PAC_checker_l_step_s_alt_def Let_def
    is_success_alt_def[symmetric]
    ls_emp ls_emp'
  by sepref

lemmas PAC_checker_l_step_s'_hnr[sepref_fr_rules] =
  check_step_s_impl.refine[FCOMP PAC_checker_l_step_s_fref]

sepref_register PAC_checker_l_step_s' ::
  \<open>sllist_polynomial \<Rightarrow> string code_status \<Rightarrow> (nat, string) shared_vars \<Rightarrow>
    (nat, sllist_polynomial) f_map \<Rightarrow> lpac_step_hol \<Rightarrow>
    (string code_status \<times> (nat, string) shared_vars \<times> (nat, sllist_polynomial) f_map) nres\<close>

sepref_def PAC_checker_l_s_impl
  is \<open>uncurry4 PAC_checker_l_s_loop\<close>
  :: \<open>poly_s_assn\<^sup>k *\<^sub>a shared_vars_assn\<^sup>d *\<^sub>a polys_s_assn\<^sup>d *\<^sub>a status_assn\<^sup>d *\<^sub>a
     (cl_assn' lpac_step_assn)\<^sup>d \<rightarrow>\<^sub>a
     status_assn \<times>\<^sub>a shared_vars_assn \<times>\<^sub>a polys_s_assn\<close>
  supply [[goals_limit=1]]
  unfolding PAC_checker_l_s_loop_def is_success_alt_def[symmetric]
    PAC_checker_l_step_s_tuple
    nres_bind_let_law[symmetric]
    ls_emp
  apply (subst nres_bind_let_law)
  by sepref

lemmas PAC_checker_l_s'_hnr[sepref_fr_rules] =
  PAC_checker_l_s_impl.refine[FCOMP PAC_checker_l_s_loop_fref]

sepref_register PAC_checker_l_s' ::
  \<open>sllist_polynomial \<Rightarrow> (nat, string) shared_vars \<Rightarrow> (nat, sllist_polynomial) f_map \<Rightarrow>
    string code_status \<Rightarrow> lpac_step_hol list \<Rightarrow>
    (string code_status \<times> (nat, string) shared_vars \<times> (nat, sllist_polynomial) f_map) nres\<close>

sepref_register import_variablesS import_poly_varsS memory_out_msg

sepref_def import_variablesS_impl
  is \<open>uncurry (import_variablesS :: string list \<Rightarrow> (nat, string) shared_vars \<Rightarrow> _)\<close>
  :: \<open>monom_assn\<^sup>k *\<^sub>a shared_vars_assn\<^sup>d \<rightarrow>\<^sub>a memory_allocation_assn \<times>\<^sub>a shared_vars_assn\<close>
  supply [[goals_limit=1]]
  unfolding import_variablesS_alt_def
    ls_emp ls_emp'
  by sepref

lemmas [sepref_fr_rules] =
  import_variablesS_impl.refine full_normalize_poly'_impl.refine

sepref_def import_poly_varsS_impl
  is \<open>uncurry import_poly_varsS\<close>
  :: \<open>shared_vars_assn\<^sup>d *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a memory_allocation_assn \<times>\<^sub>a shared_vars_assn\<close>
  supply [[goals_limit=1]]
  unfolding import_poly_varsS_def
    ls_emp ls_emp'
  by sepref

lemmas [sepref_fr_rules] = import_poly_varsS_impl.refine

sepref_def remap_polys_l2_with_err_s_impl
  is \<open>uncurry3 remap_polys_l2_with_err_s\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k *\<^sub>a polys_assn_input\<^sup>k *\<^sub>a shared_vars_assn\<^sup>d \<rightarrow>\<^sub>a
  status_assn \<times>\<^sub>a shared_vars_assn \<times>\<^sub>a polys_s_assn \<times>\<^sub>a poly_s_assn\<close>
  supply [[goals_limit=1]] indom_mI[dest]
  unfolding remap_polys_l2_with_err_s_alt
    op_fmap_empty_def[symmetric] while_eq_nfoldli[symmetric]
    while_upt_while_direct max_snat_val
    in_dom_by_contains
    fmlookup'_def[symmetric]
    ls_emp ls_emp'
  apply (subst while_upt_while_direct)
  apply simp
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemmas [sepref_fr_rules] =
  remap_polys_l2_with_err_s_impl.refine

sepref_register remap_polys_l2_with_err_s ::
  \<open>llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> (nat, llist_polynomial) f_map \<Rightarrow>
    (nat, string) shared_vars \<Rightarrow>
    (string code_status \<times> (nat, string) shared_vars \<times> (nat, sllist_polynomial) f_map \<times>
     sllist_polynomial) nres\<close>

sepref_register full_checker_l_s2 ::
  \<open>llist_polynomial \<Rightarrow> (nat, llist_polynomial) f_map \<Rightarrow> lpac_step_hol list \<Rightarrow>
    (string code_status \<times> (nat, string) shared_vars \<times> (nat, sllist_polynomial) f_map) nres\<close>

sepref_def full_checker_l_s2_impl
  is \<open>uncurry2 full_checker_l_s2\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a polys_assn_input\<^sup>k *\<^sub>a (cl_assn' lpac_step_assn)\<^sup>d \<rightarrow>\<^sub>a
  status_assn \<times>\<^sub>a shared_vars_assn \<times>\<^sub>a polys_s_assn\<close>
  supply [[goals_limit=1]]
  unfolding full_checker_l_s2_def
    PAC_checker_l_s_alt_def
    empty_shared_vars_def[symmetric]
  by sepref

end
