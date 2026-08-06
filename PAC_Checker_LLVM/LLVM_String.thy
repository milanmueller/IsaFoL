theory LLVM_String
  imports Char_Assn IICF_Copying_List Isabelle_LLVM.IICF
    PAC_Polynomials_Sort
begin

text \<open>Here, we provide two implementations of strings:
  \<^item> One using our custom copying list @{term cl_assn}
  \<^item> One using @{term larray_assn}\<close>

section \<open>String by List\<close>
abbreviation \<open>strl_assn \<equiv> cl_assn char_assn\<close>
abbreviation \<open>strl_assn' \<equiv> cl_assn' char_assn\<close>

interpretation strl: copyable_assn char_assn \<open>\<lambda>_. Mreturn ()\<close> Mreturn
  apply unfold_locales
  subgoal by (rule char_assn_mk_free)
  subgoal by (rule hnr_pure_COPY) (simp add: char_assn_pure)
  done

interpretation strl: linorder_assn char_assn ll_icmp_eq ll_icmp_ult
  apply unfold_locales
  subgoal by (rule char_eq_hnr)
  subgoal by (rule char_lt_hnr)
  done

interpretation strl: cmp_env_impl
  \<open>(\<le>)\<close> \<open>char_assn\<close>  \<open>\<lambda>_. Mreturn ()\<close> \<open>char_le_impl\<close>
  apply unfold_locales
  subgoal by auto
  subgoal by auto
  subgoal by (rule char_le_impl.refine)
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
  
definition \<open>fnv1a_of_strl_impl xs \<equiv> cl_fold fnv1a_of_strl_inner_impl (xs, fnv_offset)\<close>

lemma fnv1a_of_strl_comp: \<open>fnv1a_of_strl = foldl fnv1a_of_strl_inner fnv_offset\<close>
  unfolding fnv1a_of_strl_def fnv1a_of_strl_inner_def by simp

lemma fnv1a_of_strl_inner_rule':
  \<open>llvm_htriple
    (\<up>(wi = w) ** char_assn c ci)
    (fnv1a_of_strl_inner_impl wi ci)
    (\<lambda>r. \<up>(r = fnv1a_of_strl_inner w c) ** char_assn c ci)\<close>
  using fnv1a_of_strl_inner_rule[of w wi c ci]
  by (simp add: pure_def)

lemmas fnv1a_of_strl_walk_rule =
  cl_fold_rule[where R = \<open>\<lambda>a c. \<up>(c = a)\<close> and A = \<open>char_assn\<close>
    and f = \<open>fnv1a_of_strl_inner_impl\<close> and fa = \<open>fnv1a_of_strl_inner\<close>,
    OF fnv1a_of_strl_inner_rule']

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
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply sepref_dbg_side_unfold
  oops

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
definition \<open>stra_assn \<equiv> larray_assn char_assn\<close>
(* Deferred for now *)

experiment
begin

definition \<open>tststr \<equiv> ''aba''\<close>

sepref_definition tststr_impl is \<open>uncurry0 (RETURN tststr)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a stra_assn'\<close>
  unfolding tststr_def
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply sepref_dbg_side_unfold
  oops

sepref_definition strl_lt_test is \<open>uncurry (RETURN oo list_lt)\<close>
  :: \<open>stra_assn\<^sup>k *\<^sub>a stra_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  apply sepref_dbg_keep
  oops

sepref_definition strl_le_test is \<open>uncurry (RETURN oo list_le)\<close>
  :: \<open>stra_assn\<^sup>k *\<^sub>a stra_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  apply sepref_dbg_keep
  oops

sepref_register \<open>(=) :: char list \<Rightarrow> char list \<Rightarrow> bool\<close>

sepref_definition strl_eq_test is \<open>uncurry (RETURN oo (=))\<close>
  :: \<open>stra_assn\<^sup>k *\<^sub>a stra_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  apply sepref_dbg_keep
  oops

sepref_definition strl_copy_test is \<open>RETURN o COPY\<close>
  :: \<open>stra_assn\<^sup>k \<rightarrow>\<^sub>a stra_assn\<close>
  apply sepref_dbg_keep
  oops

end

end
