theory LLVM_String
  imports Printing_Setup IICF_Copying_List Isabelle_LLVM.IICF
    LLVM_List_Sorting
begin

text \<open>Here, we provide two implementations of strings:
  \<^item> One using our custom copying list @{term cl_assn}
  \<^item> One using @{term larray_assn}\<close>

section \<open>String by List\<close>
abbreviation \<open>strl_assn \<equiv> cl_assn char_assn\<close>
abbreviation \<open>strl_assn' \<equiv> cl_assn' char_assn\<close>
lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure strl_assn']

interpretation strl: copyable_assn char_assn \<open>\<lambda>_. Mreturn ()\<close> Mreturn
  apply unfold_locales
  subgoal by (rule char_assn_mk_free)
  subgoal by (rule hnr_pure_COPY) (simp add: char_assn_pure)
  done

interpretation strl: linorder_assn char_assn ll_icmp_eq ll_icmp_ult
  apply unfold_locales
  subgoal using char_eq_hnr char_eq_impl_def by auto
  subgoal using char_lt_hnr char_lt_impl_def by argo 
  done

interpretation strl: cmp_env_impl
  \<open>(\<le>)\<close> \<open>char_assn\<close>  \<open>\<lambda>_. Mreturn ()\<close> \<open>char_le_impl\<close>
  apply unfold_locales
  subgoal by auto
  subgoal by auto
  subgoal using char_le_hnr by blast 
  done

sepref_register \<open>(=) :: char list \<Rightarrow> char list \<Rightarrow> bool\<close>
sepref_register \<open>(<) :: char list \<Rightarrow> char list \<Rightarrow> bool\<close>
sepref_register \<open>(\<le>) :: char list \<Rightarrow> char list \<Rightarrow> bool\<close>

lemmas strl_less_hnr[sepref_fr_rules] = strl.cl_less_hnr[unfolded list_lt_less]
lemmas strl_le_hnr[sepref_fr_rules] = strl.cl_le_hnr[unfolded list_le_less_eq]

text \<open>A Hash function for Strings\<close>

definition \<open>fnv1a_of_strl \<equiv> 
  foldl (\<lambda>acc x. (acc XOR w64_of_char x) * fnv_prime) fnv_offset\<close>

definition \<open>fnv1a_of_strl_inner \<equiv> \<lambda>acc x. (acc XOR w64_of_char x) * fnv_prime\<close>

sepref_def fnv1a_of_strl_inner_impl is \<open>uncurry (RETURN oo fnv1a_of_strl_inner)\<close>
  :: \<open>(word_assn' TYPE(64))\<^sup>k *\<^sub>a char_assn\<^sup>k \<rightarrow>\<^sub>a (word_assn' TYPE(64))\<close>
  unfolding fnv1a_of_strl_inner_def
  by sepref

lemma fnv1a_of_strl_inner_rule: \<open>llvm_htriple
  ((word_assn' TYPE(64)) w wi ** char_assn c ci)
  (fnv1a_of_strl_inner_impl wi ci)
  (\<lambda>r. word_assn (fnv1a_of_strl_inner w c) r ** char_assn c ci)\<close>
  supply [vcg_rules] = hfref_htriple_k2[OF fnv1a_of_strl_inner_impl.refine]
  apply vcg
  by (auto simp: ENTAILS_def entails_def sep_algebra_simps pure_def)
  
definition fnv1a_of_strl_impl where[llvm_code]: 
  \<open>fnv1a_of_strl_impl xs \<equiv> cl_fold fnv1a_of_strl_inner_impl (xs, fnv_offset)\<close>

lemma fnv1a_of_strl_comp: \<open>fnv1a_of_strl = foldl fnv1a_of_strl_inner fnv_offset\<close>
  unfolding fnv1a_of_strl_def fnv1a_of_strl_inner_def by simp

lemma fnv1a_of_strl_inner_rule':
  \<open>llvm_htriple
    (\<up>(wi = w) ** char_assn c ci)
    (fnv1a_of_strl_inner_impl wi ci)
    (\<lambda>r. \<up>(r = fnv1a_of_strl_inner w c) ** char_assn c ci)\<close>
  using fnv1a_of_strl_inner_rule[of w wi c ci]
  by (simp add: pure_def)

text \<open>\<open>char_assn\<close> is an abbreviation for \<open>pure char_rel\<close> now, so the
  \<open>sepref_to_hoare\<close> normalization unfolds \<open>pure_def\<close> inside the \<open>cl_assn'\<close>
  parameter; the walk rule must be stated in that unfolded form to match.\<close>
lemmas fnv1a_of_strl_walk_rule =
  cl_fold_rule[where R = \<open>\<lambda>a c. \<up>(c = a)\<close> and A = \<open>\<lambda>a c. \<up>((c, a) \<in> char_rel)\<close>
    and f = \<open>fnv1a_of_strl_inner_impl\<close> and fa = \<open>fnv1a_of_strl_inner\<close>,
    OF fnv1a_of_strl_inner_rule'[unfolded pure_def]]

sepref_register fnv1a_of_strl

lemma fnv1a_of_strl_hnr[sepref_fr_rules]:
  \<open>(fnv1a_of_strl_impl, RETURN o fnv1a_of_strl) \<in> strl_assn'\<^sup>k \<rightarrow>\<^sub>a (word_assn' TYPE(64))\<close>
  unfolding fnv1a_of_strl_impl_def
  apply sepref_to_hoare
  supply [vcg_rules] = fnv1a_of_strl_walk_rule
  supply [simp] = fnv1a_of_strl_comp
  by vcg

experiment
begin

definition \<open>tststr \<equiv> ''aba''\<close>

sepref_definition tststr_impl is \<open>uncurry0 (RETURN tststr)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a strl_assn'\<close>
  unfolding tststr_def
  by sepref

sepref_definition strl_lt_test is \<open>uncurry (RETURN oo list_lt)\<close>
  :: \<open>strl_assn'\<^sup>k *\<^sub>a strl_assn'\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

sepref_definition strl_le_test is \<open>uncurry (RETURN oo list_le)\<close>
  :: \<open>strl_assn'\<^sup>k *\<^sub>a strl_assn'\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

sepref_register \<open>(=) :: char list \<Rightarrow> char list \<Rightarrow> bool\<close>

sepref_definition strl_eq_test is \<open>uncurry (RETURN oo (=))\<close>
  :: \<open>strl_assn'\<^sup>k *\<^sub>a strl_assn'\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

sepref_definition strl_copy_test is \<open>RETURN o COPY\<close>
  :: \<open>strl_assn'\<^sup>k \<rightarrow>\<^sub>a strl_assn'\<close>
  by sepref

definition prependtest :: \<open>char \<Rightarrow> char list \<Rightarrow> char list\<close> where
  \<open>prependtest c ss = c # ss\<close>

sepref_definition prependtest_impl is \<open>uncurry (RETURN oo prependtest)\<close>
  :: \<open>char_assn\<^sup>k *\<^sub>a strl_assn'\<^sup>d \<rightarrow>\<^sub>a strl_assn'\<close>
  unfolding prependtest_def 
  by sepref

end

section \<open>String by Array\<close>

abbreviation \<open>stra_assn \<equiv> larray_assn' TYPE(64) char_assn\<close>

subsection \<open>Comparisons\<close>

definition \<open>list_eq_nres \<equiv> \<lambda>xs ys. doN {
    let xl = length xs;  
    let yl = length ys;
    if xl \<noteq> yl then
      RETURN False 
    else doN {
      ASSERT (xl = yl);
      (_, r) \<leftarrow> WHILEIT
        (\<lambda>(i, r). i \<le> xl \<and> xl = yl \<and> length xs = xl \<and> length ys = yl
                  \<and> (r \<longleftrightarrow> take i xs = take i ys))
        (\<lambda>(i, r). r \<and> i < xl)
        (\<lambda>(i, r). doN {
          ASSERT(i < length xs \<and> i < length ys);        
          if (xs!i = ys!i) then
            RETURN (i+1, r)
          else
            RETURN (i+1, False)
        }) (0, True);
      RETURN r
    }
  }\<close> 

lemma list_eq_spec: \<open>list_eq_nres xs ys \<le> RETURN (xs = ys)\<close>
  unfolding list_eq_nres_def
  apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(i, _). length xs - i)\<close>])
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal
    apply auto
    by (metis take_Suc_conv_app_nth)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal
    apply auto
    by (metis nat_in_between_eq(2) nth_take)
  subgoal by auto
  subgoal by auto
  done

lemma list_eq_fref:
  \<open>(uncurry list_eq_nres, uncurry (RETURN oo (=))) \<in> Id \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: list_eq_spec)

sepref_def list_eq_impl is \<open>uncurry list_eq_nres\<close>
  :: \<open>stra_assn\<^sup>k *\<^sub>a stra_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding list_eq_nres_def
  apply (annot_snat_const "TYPE(64)")
  by sepref

lemmas list_eq_hnr[sepref_fr_rules] = list_eq_impl.refine[FCOMP list_eq_fref]


definition list_lt_nres :: \<open>'a::linorder list \<Rightarrow> 'a list \<Rightarrow> bool nres\<close> where
  \<open>list_lt_nres \<equiv> \<lambda>xs ys. doN {
    let xl = length xs;
    let yl = length ys;
    (i, _) \<leftarrow> WHILEIT
      (\<lambda>(i, cont). i \<le> xl \<and> i \<le> yl \<and> length xs = xl \<and> length ys = yl
                  \<and> take i xs = take i ys
                  \<and> (\<not>cont \<longrightarrow> i < xl \<and> i < yl \<and> xs!i \<noteq> ys!i))
      (\<lambda>(i, cont). cont \<and> i < xl \<and> i < yl)
      (\<lambda>(i, cont). doN {
        ASSERT(i < length xs \<and> i < length ys);
        if (xs!i = ys!i) then
          RETURN (i+1, cont)
        else
          RETURN (i, False)
      }) (0, True);
    if i < xl \<and> i < yl then doN {
      ASSERT(i < length xs \<and> i < length ys);
      RETURN (xs!i < ys!i)
    } else
      RETURN (xl < yl)
  }\<close>

lemma list_less_take_index_conv:
  \<open>xs < ys \<longleftrightarrow>
    (length xs < length ys \<and> take (length xs) ys = xs) \<or>
    (\<exists>i < min (length xs) (length ys). take i xs = take i ys \<and> xs!i < ys!i)\<close>
  for xs ys :: \<open>'a::linorder list\<close> 
  unfolding less_list_def List.lexordp_def lexord_take_index_conv by simp

lemma list_less_first_diff:
  fixes xs ys :: \<open>'a::linorder list\<close>
  assumes \<open>take i xs = take i ys\<close> \<open>i < length xs\<close> \<open>i < length ys\<close> \<open>xs!i \<noteq> ys!i\<close>
  shows \<open>xs < ys \<longleftrightarrow> xs!i < ys!i\<close>
proof -
  have eq: \<open>xs!j = ys!j\<close> if \<open>j < i\<close> for j
    using assms(1) that by (metis nth_take)
  show ?thesis
    unfolding list_less_take_index_conv
    using assms eq apply (auto simp: not_less_iff_gr_or_eq)
    subgoal by (metis nth_take)
    subgoal by (metis nat_neq_iff nth_take order_less_asym')
    done
qed

lemma list_less_no_diff:
  fixes xs ys :: \<open>'a::linorder list\<close>
  assumes \<open>take (min (length xs) (length ys)) xs = take (min (length xs) (length ys)) ys\<close>
  shows \<open>xs < ys \<longleftrightarrow> length xs < length ys\<close>
  using assms unfolding list_less_take_index_conv
  apply (auto simp: min_def)
  subgoal by (metis nth_take not_less_iff_gr_or_eq)
  subgoal by (metis not_less_iff_gr_or_eq nth_take)
  done

lemma list_lt_spec: \<open>list_lt_nres xs ys \<le> RETURN (list_lt xs ys)\<close>
  unfolding list_lt_nres_def list_lt_less
  apply (refine_vcg WHILEIT_rule[where
    R = \<open>measure (\<lambda>(i, cont). length xs - i + (if cont then 1 else 0))\<close>])
  apply (clarsimp_all simp: take_Suc_conv_app_nth list_less_first_diff)
  subgoal by auto
  subgoal by auto
  subgoal
    by (metis list_less_no_diff min.absorb2 min_simps(1)
    order_neq_le_trans)
  done

lemma list_lt_fref:
  \<open>(uncurry list_lt_nres, uncurry (RETURN oo list_lt)) \<in> Id \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: list_lt_spec)

sepref_register list_lt_nres
sepref_def list_lt_impl is \<open>uncurry (list_lt_nres :: string \<Rightarrow> _)\<close>
  :: \<open>stra_assn\<^sup>k *\<^sub>a stra_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding list_lt_nres_def
  apply (annot_snat_const "TYPE(64)")
  by sepref

lemmas list_lt_hnr[sepref_fr_rules] = list_lt_impl.refine[FCOMP list_lt_fref]
lemmas stra_less_hnr[sepref_fr_rules] = list_lt_hnr[unfolded list_lt_less]

definition list_le_nres :: \<open>'a::linorder list \<Rightarrow> 'a list \<Rightarrow> bool nres\<close> where
  \<open>list_le_nres \<equiv> \<lambda>xs ys. doN {
    lt \<leftarrow> list_lt_nres ys xs;
    RETURN (\<not>lt)
  }\<close>

lemma list_le_spec: \<open>list_le_nres xs ys \<le> RETURN (list_le xs ys)\<close>
  unfolding list_le_nres_def list_le_less_eq
  by (refine_vcg list_lt_spec[THEN order_trans]) (simp add: list_lt_less not_less)

lemma list_le_fref:
  \<open>(uncurry list_le_nres, uncurry (RETURN oo list_le)) \<in> Id \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: list_le_spec)

sepref_def list_le_impl is \<open>uncurry (list_le_nres :: string \<Rightarrow> _)\<close>
  :: \<open>stra_assn\<^sup>k *\<^sub>a stra_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding list_le_nres_def
  by sepref

lemmas list_le_hnr[sepref_fr_rules] = list_le_impl.refine[FCOMP list_le_fref]
lemmas stra_le_hnr[sepref_fr_rules] = list_le_hnr[unfolded list_le_less_eq]

interpretation strla_ls: eq_assn stra_assn list_eq_impl
  apply unfold_locales
  apply (rule list_eq_hnr)
  done

interpretation strla_ls: linorder_assn stra_assn list_eq_impl list_lt_impl
  apply (unfold_locales)
  apply (rule stra_less_hnr)
  done

term la_length_impl

subsection \<open>Conversion from list based string to array based string\<close>
text \<open>Since the length of list based string is not bounded, we can not
  convert every string to an array.
  What we do is truncate every string to it's longest representable prefix.\<close>
(* TODO: by eval might be considered evel, maybe we want to change it? *)
definition \<open>strl_ceil \<equiv> 9223372036854775807\<close>
lemma strl_ceil_val: \<open>strl_ceil = max_snat 64 - 1\<close> unfolding strl_ceil_def by eval

sepref_def strl_ceil_impl is \<open>uncurry0 (RETURN strl_ceil)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a (snat_assn' TYPE(64))\<close>
  unfolding strl_ceil_def
  apply (annot_snat_const "TYPE(64)")
  by sepref

definition capped_length :: \<open>'a list \<Rightarrow> nat nres\<close> where
  \<open>capped_length xs \<equiv> doN {
    (r,_) \<leftarrow> WHILEIT
      (\<lambda>(r,ys). r \<le> strl_ceil \<and> r + length ys = length xs)
      (\<lambda>(r,xs). r < strl_ceil \<and> xs \<noteq> [])
      (\<lambda>(r,xs). doN {
        ASSERT(r+1 < max_snat 64);
        (x,xs) \<leftarrow> mop_list_pop_hd xs;
        RETURN (r+1,xs) 
      }) (0, xs);
    RETURN r 
  }\<close>

lemma capped_length_spec:
  \<open>capped_length xs \<le> SPEC (\<lambda>r. r = min (length xs) strl_ceil)\<close>
  unfolding capped_length_def
  apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>(_,xs). length xs)"])
  apply clarsimp_all
  subgoal using strl_ceil_val by linarith
  subgoal by auto
  done 

context freeable_assn
begin
sepref_def capped_length_impl is \<open>capped_length\<close>
  :: \<open>(cl_assn' A)\<^sup>d \<rightarrow>\<^sub>a (snat_assn' TYPE(64))\<close>
  unfolding capped_length_def ls_emp
  apply (annot_snat_const "TYPE(64)")
  by sepref
end

definition stra_of_strl :: \<open>string \<Rightarrow> string nres\<close> where
  \<open>stra_of_strl xs = doN{ 
    l \<leftarrow> capped_length (COPY xs);
    let r = replicate l (char_of_word 0);
    (r,_,_) \<leftarrow> WHILET
      (\<lambda>(r,xs,i). xs\<noteq>[] \<and> i < l)
      (\<lambda>(r,xs,i). doN {
        ASSERT(i + 1 < max_snat 64);
        (s,xs) \<leftarrow> mop_list_pop_hd xs;
        r' \<leftarrow> mop_list_set r i s;
        RETURN (r',xs,i+1)
      })
      (r,xs,0::nat);
    RETURN r
  }\<close>

lemma stra_of_strl_nofail: \<open>stra_of_strl xs \<le> RES UNIV\<close>
  unfolding stra_of_strl_def
  apply (refine_vcg capped_length_spec[THEN order_trans]
      WHILET_rule[where
        I=\<open>\<lambda>(r,ys,i). length r = min (length xs) strl_ceil \<and> i \<le> length r\<close> and
        R=\<open>measure (\<lambda>(_,ys,_). length ys)\<close>])
  apply simp_all
  apply fastforce
  by (metis Suc_diff_1 Suc_less_eq max_snat_def nat_zero_less_power_iff
    numeral_2_eq_2 strl_ceil_val zero_less_Suc) 
  
sepref_register \<open>capped_length\<close>
sepref_def stra_of_strl_impl is \<open>stra_of_strl\<close>
  :: \<open>strl_assn'\<^sup>d \<rightarrow>\<^sub>a stra_assn\<close>
  unfolding stra_of_strl_def ls_emp 
    larray_fold_custom_replicate
  supply [sepref_fr_rules] = cl_length_hnr[where 'l=64]
  apply (annot_snat_const "TYPE(64)")
  by sepref

definition capped :: \<open>string \<Rightarrow> string\<close> where
  \<open>capped s = take strl_ceil s\<close>

lemma capped_idem[simp]: \<open>capped (capped s) = capped s\<close>
  unfolding capped_def by simp

lemma stra_of_strl_spec: \<open>stra_of_strl xs \<le> RETURN (capped xs)\<close>
  unfolding stra_of_strl_def capped_def COPY_def
  apply (refine_vcg capped_length_spec[THEN order_trans]
      WHILET_rule[where
        I=\<open>\<lambda>(r,ys,i). i \<le> min (length xs) strl_ceil \<and> ys = drop i xs \<and>
              r = take i xs @ replicate (min (length xs) strl_ceil - i) (char_of_word 0)\<close> and
        R=\<open>measure (\<lambda>(_,ys,_). length ys)\<close>])
  apply clarsimp_all
  subgoal by (metis strl_ceil_val less_diff_conv Suc_eq_plus1)
  subgoal by (metis drop_Suc tl_drop)
  subgoal
    by (smt (verit, ccfv_threshold) Cons_nth_drop_Suc One_nat_def
    append.right_neutral append_Cons append_eq_append_conv2 append_eq_conv_conj
    bot_nat_0.not_eq_extremum drop_Suc drop_all drop_replicate drop_tl
    le_eq_less_or_eq length_replicate length_take list.sel(1,2) min_eq_arg(2)
    min_simps(1) nat_neq_iff take_Nil take_Suc_conv_app_nth
    upd_conv_take_nth_drop)
  subgoal by simp
  subgoal by (auto simp: replicate_append_same)
  done

lemma stra_of_strl_fref:
  \<open>(stra_of_strl, RETURN o capped) \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: stra_of_strl_spec)

lemmas stra_of_strl_hnr[sepref_fr_rules] =
  stra_of_strl_impl.refine[FCOMP stra_of_strl_fref]

lemma stra_of_strl_impl_rule[vcg_rules]:
  \<open>llvm_htriple (strl_assn' xs xsi) (stra_of_strl_impl xsi) (\<lambda>r. stra_assn (capped xs) r)\<close>
  by (rule hfref_htriple_d1[OF stra_of_strl_hnr])

text \<open>Variant matching goals where @{method sepref_to_hoare} has unfolded @{thm pure_def}
  inside the @{const cl_assn'} element parameter.\<close>
lemmas stra_of_strl_impl_rule'[vcg_rules] = stra_of_strl_impl_rule[unfolded pure_def]

experiment
begin

definition \<open>tststr \<equiv> ''aba''\<close>

sepref_definition teststrl_impl is \<open>uncurry0 (RETURN tststr)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a strl_assn'\<close>
  unfolding tststr_def
  by sepref
lemmas [sepref_fr_rules] = teststrl_impl.refine

sepref_register stra_of_strl
sepref_definition tststra_impl is \<open>uncurry0 (stra_of_strl tststr)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a stra_assn\<close>
  by sepref

sepref_definition strl_lt_test is \<open>uncurry (RETURN oo list_lt)\<close>
  :: \<open>stra_assn\<^sup>k *\<^sub>a stra_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

sepref_definition strl_le_test is \<open>uncurry (RETURN oo list_le)\<close>
  :: \<open>stra_assn\<^sup>k *\<^sub>a stra_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

sepref_register \<open>(=) :: char list \<Rightarrow> char list \<Rightarrow> bool\<close>

sepref_definition strl_eq_test is \<open>uncurry (RETURN oo (=))\<close>
  :: \<open>stra_assn\<^sup>k *\<^sub>a stra_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

sepref_definition strl_copy_test is \<open>RETURN o COPY\<close>
  :: \<open>stra_assn\<^sup>k \<rightarrow>\<^sub>a stra_assn\<close>
  apply sepref_dbg_keep
  oops

end

end
