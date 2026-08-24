theory LPAC_Perfectly_Shared_Vars
  imports LPAC_Perfectly_Shared
    PAC_Checker_Relation
    PAC_Map_Rel
    More_EOArray
    IICF_HashMap
begin

type_synonym ('string2, 'nat) shared_vars_c = \<open>'string2 list \<times> ('string2, 'nat) fmap\<close>

definition perfect_shared_vars_rel_c :: \<open>('string2 \<times> 'string) set \<Rightarrow> (('string2, nat) shared_vars_c \<times> (nat, 'string)shared_vars) set\<close> where
  \<open>perfect_shared_vars_rel_c R =
  {((\<V>, \<A>), (\<D>', \<V>', \<A>')). (\<forall>i\<in>#dom_m \<V>'. i < length \<V>) \<and>
  (\<forall>i\<in>#dom_m \<V>'. i < length \<V> \<and> (\<V> ! i, the (fmlookup \<V>' i))\<in> R) \<and>
  (\<A>, \<A>') \<in> \<langle>R,nat_rel\<rangle>fmap_rel}\<close>

text \<open>Random conditions with the idea to use machine words eventually\<close>

definition find_new_idx_c :: \<open>('string, nat) shared_vars_c \<Rightarrow> (memory_allocation \<times> nat)  nres\<close> where
  \<open>find_new_idx_c = (\<lambda>(\<V>, \<A>). let k = length \<V> in if k < 2^63-1 then RETURN (Allocated, k) else RETURN (Mem_Out, 0) )\<close>

definition insert_variable_c :: \<open>'string \<Rightarrow> nat \<Rightarrow> ('string, nat) shared_vars_c \<Rightarrow> ('string, nat) shared_vars_c\<close>  where
  \<open>insert_variable_c v k' = (\<lambda>(\<V>, \<A>). (\<V> @ [v], fmupd v k' \<A>))\<close>

definition import_variable_c :: \<open>'string \<Rightarrow>  ('string, nat) shared_vars_c \<Rightarrow> (memory_allocation \<times> ('string, nat) shared_vars_c \<times> nat)  nres\<close> where
  \<open>import_variable_c v = (\<lambda>(\<V>\<A>). do {
  (err, k') \<leftarrow> find_new_idx_c (\<V>\<A>);
  if alloc_failed err then do {let k'=k'; RETURN (err, (\<V>\<A>), k')}
  else do {
    ASSERT(k' < 2^63-1);
    RETURN (Allocated, insert_variable_c v k' \<V>\<A>, k')
  }
})\<close>

lemma import_variable_c_alt_def:
  \<open>import_variable_c v = (\<lambda>(\<V>, \<A>). do {
  (err, k') \<leftarrow> find_new_idx_c (\<V>, \<A>);
  if alloc_failed err then do {let k'=k'; RETURN (err, (\<V>, \<A>), k')}
  else do {
    ASSERT(k' < 2^63-1);
    RETURN (Allocated, (\<V> @ [v], fmupd v k' \<A>), k')
  }
})\<close>
  unfolding import_variable_c_def insert_variable_c_def
  by auto


lemma import_variable_c_import_variableS:
  fixes A' :: \<open>(nat,'string) shared_vars\<close>
  assumes
    A: \<open>(A,A')\<in>perfect_shared_vars_rel_c R\<close> and
    v: \<open>(v,v')\<in>R\<close> \<open>single_valued R\<close> \<open>single_valued (R\<inverse>)\<close>
  shows \<open>import_variable_c v A \<le>\<Down>(Id \<times>\<^sub>r (perfect_shared_vars_rel_c R \<times>\<^sub>r nat_rel)) (import_variableS v' A')\<close>
proof -
  have [refine]: \<open>RETURN x2g \<le> \<Down> Id (RES UNIV)\<close> for x2g :: nat
    by auto
  have [refine]: \<open>find_new_idx_c a \<le> \<Down> {((err, k), (err', k')). err=err' \<and> k=k' \<and> (\<not>alloc_failed err \<longrightarrow> k < 2^63-1 \<and> k = length (fst a))} (find_new_idx b)\<close>
    if \<open>(a,b) \<in> perfect_shared_vars_rel_c R\<close>
    for b :: \<open>(nat,'string) shared_vars\<close> and a
    using that unfolding find_new_idx_c_def find_new_idx_def
    by (cases b; cases a)
      (auto intro!: RETURN_RES_refine simp: Let_def perfect_shared_vars_rel_c_def)

  show ?thesis
    unfolding import_variable_c_alt_def import_variableS_def find_new_idx_def[symmetric]
    apply refine_vcg
    subgoal using A by (auto simp: perfect_shared_vars_rel_c_def)
    subgoal by auto
    subgoal using A by (auto simp: perfect_shared_vars_rel_c_def)
    subgoal by auto
    subgoal
      using A v by (force simp: perfect_shared_vars_rel_c_def dest: in_diffD intro!: fmap_rel_fmupd_fmap_rel)
   done
qed


definition is_new_variable_c :: \<open>'string \<Rightarrow> ('string, 'nat) shared_vars_c \<Rightarrow> bool nres\<close> where
  \<open>is_new_variable_c v = (\<lambda>(\<V>, \<V>').
  RETURN (v \<notin># dom_m \<V>')
  )\<close>

lemma fset_fmdom_dom_m: \<open>fset (fmdom A) = set_mset (dom_m A)\<close>
  by (simp add: dom_m_def)

lemma fmap_rel_nat_rel_dom_m_iff:
  \<open>(A, B) \<in> \<langle>R, S\<rangle>fmap_rel \<Longrightarrow> (v,v')\<in>R \<Longrightarrow> v\<in>#dom_m A \<longleftrightarrow>v'\<in># dom_m B\<close>
  by (auto simp: fmap_rel_alt_def distinct_mset_dom fset_fmdom_dom_m
    dest!: multi_member_split
    simp del: fmap_rel_nat_the_fmlookup)


lemma is_new_variable_c_is_new_variableS:
  shows \<open>(uncurry is_new_variable_c, uncurry is_new_variableS) \<in> R \<times>\<^sub>r perfect_shared_vars_rel_c R \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  by (use  in \<open>auto simp: perfect_shared_vars_rel_c_def fmap_rel_nat_rel_dom_m
    fmap_rel_nat_rel_dom_m_iff is_new_variable_c_def is_new_variableS_def
    intro!: frefI nres_relI\<close>)


definition get_var_pos_c :: \<open> ('string, nat) shared_vars_c \<Rightarrow> _ \<Rightarrow> nat nres\<close> where
  \<open>get_var_pos_c = (\<lambda>(xs, \<V>) x. do {
    ASSERT(x \<in># dom_m \<V>);
    RETURN (the (fmlookup \<V> x))
  })\<close>


lemma get_var_pos_c_get_var_posS:
  fixes A' :: \<open>(nat,'string) shared_vars\<close>
  assumes
    V: \<open>single_valued R\<close> \<open>single_valued (R\<inverse>)\<close>
  shows \<open>(uncurry get_var_pos_c, uncurry get_var_posS) \<in> perfect_shared_vars_rel_c R \<times>\<^sub>r R \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>
  unfolding get_var_pos_c_def get_var_posS_def uncurry_def
    apply (clarify intro!: frefI nres_relI)
  apply refine_vcg
  subgoal using assms by (auto simp: perfect_shared_vars_rel_c_def fmap_rel_nat_rel_dom_m_iff)
  subgoal
    using assms by (auto simp: perfect_shared_vars_rel_c_def fmap_rel_nat_rel_dom_m_iff dest: fmap_rel_fmlookup_rel)
  done



definition get_var_name_c :: \<open> ('string, nat) shared_vars_c \<Rightarrow> nat \<Rightarrow> 'string nres\<close> where
  \<open>get_var_name_c = (\<lambda>(xs, \<V>) x. do {
    ASSERT(x < length xs);
    RETURN (xs ! x)
  })\<close>


lemma get_var_name_c_get_var_nameS:
  fixes A' :: \<open>(nat,'string) shared_vars\<close>
  assumes
    V: \<open>single_valued R\<close> \<open>single_valued (R\<inverse>)\<close>
  shows \<open>(uncurry get_var_name_c, uncurry get_var_nameS) \<in> perfect_shared_vars_rel_c R \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>R\<rangle>nres_rel\<close>
  unfolding get_var_name_c_def get_var_nameS_def uncurry_def
    apply (clarify intro!: frefI nres_relI)
  apply refine_vcg
  subgoal using assms by (auto dest!: multi_member_split simp: perfect_shared_vars_rel_c_def)
  subgoal
    using assms by (auto simp: perfect_shared_vars_rel_c_def fmap_rel_nat_rel_dom_m_iff
      dest: multi_member_split)
  done

interpretation snhm: hashmap_env
  \<open>strl_assn'\<close> \<open>strl.cl_free\<close>
  \<open>si64_assn\<close> \<open>\<lambda>_. Mreturn ()\<close> \<open>\<lambda>n. Mreturn n\<close>
  \<open>strl.cl_eq\<close> \<open>fnv1a_of_strl\<close> \<open>fnv1a_of_strl_impl\<close>
  apply unfold_locales
  subgoal by (metis free_thms(2))
  subgoal by (metis COPY_def eq_id_iff prio_impl_refine)  
  subgoal by (rule fnv1a_of_strl_hnr) 
  done 

term perfect_shared_vars_rel_c
typ \<open>(string, nat) shared_vars_c\<close>
term strl_assn'
term strls_assn 
term map_fmap_rel
term snhm.hm_assn

abbreviation \<open>hm_fmap_assn \<equiv> hr_comp snhm.hm_assn map_fmap_rel\<close>
abbreviation perfect_shared_vars_assn :: \<open>(string, nat) shared_vars_c \<Rightarrow> _ \<Rightarrow> assn\<close> where
  \<open>perfect_shared_vars_assn \<equiv> strls_assn \<times>\<^sub>a hm_fmap_assn\<close>
abbreviation shared_vars_assn where
  \<open>shared_vars_assn \<equiv> hr_comp perfect_shared_vars_assn (perfect_shared_vars_rel_c Id)\<close>

lemmas [sepref_fr_rules] = snhm.lshm_lookup_hnr[FCOMP op_map_lookup_fmlookup]

definition fmlookup_the where
  [simp]: \<open>fmlookup_the k A = the (fmlookup A k)\<close>

lemma map_fmap_rel_lookup[fcomp_prenorm_simps]:
  \<open>(m, A) \<in> map_fmap_rel \<Longrightarrow> m k = fmlookup A k\<close>
  by (auto simp: map_fmap_rel_def br_def fmap.Abs_fmap_inverse)

lemma op_map_the_lookup_fmlookup_the:
  \<open>(uncurry (RETURN oo op_map_the_lookup), uncurry (RETURN oo fmlookup_the))
    \<in> [\<lambda>(k, A). k \<in># dom_m A]\<^sub>f Id \<times>\<^sub>r map_fmap_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: map_fmap_rel_def br_def fmap.Abs_fmap_inverse in_dom_m_lookup_iff)

lemmas [sepref_fr_rules] = snhm.lshm_the_lookup_hnr[FCOMP op_map_the_lookup_fmlookup_the]

sepref_def get_var_pos_c_impl
  is \<open>uncurry get_var_pos_c\<close>
  :: \<open>perfect_shared_vars_assn\<^sup>k *\<^sub>a strl_assn'\<^sup>k \<rightarrow>\<^sub>a si64_assn\<close>
  supply [simp] = in_dom_m_lookup_iff
  unfolding get_var_pos_c_def fmlookup_the_def[symmetric]
  by sepref

definition fmap_contains where
  [simp]: \<open>fmap_contains k A \<longleftrightarrow> k \<in># dom_m A\<close>

lemma op_map_contains_key_fmap_contains:
  \<open>(op_map_contains_key, fmap_contains) \<in> Id \<rightarrow> map_fmap_rel \<rightarrow> bool_rel\<close>
  by (auto simp: map_fmap_rel_def br_def fmap.Abs_fmap_inverse in_dom_m_lookup_iff dom_def)

lemmas [sepref_fr_rules] = snhm.lshm_contains_key_hnr[FCOMP op_map_contains_key_fmap_contains]

sepref_def is_new_variable_c_impl
  is \<open>uncurry is_new_variable_c\<close>
  :: \<open>strl_assn'\<^sup>k  *\<^sub>a  perfect_shared_vars_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding is_new_variable_c_def fmap_contains_def[symmetric]
  by sepref

lemmas [sepref_fr_rules] =
  strls.oa_hnr strls.oa_len_hnr strls.oa_upd_hnr strls.oa_push_back_hnr

sepref_def get_var_name_c_impl
  is \<open>uncurry get_var_name_c\<close>
  :: \<open>perfect_shared_vars_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k \<rightarrow>\<^sub>a strl_assn'\<close>
  unfolding get_var_name_c_def
  by sepref

lemma [sepref_fr_rules]:
  \<open>(uncurry is_new_variable_c_impl, uncurry is_new_variableS) \<in> strl_assn'\<^sup>k *\<^sub>a shared_vars_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  using is_new_variable_c_impl.refine[FCOMP is_new_variable_c_is_new_variableS, of Id]
  by auto

lemma [sepref_fr_rules]:
  \<open>(uncurry get_var_pos_c_impl, uncurry get_var_posS) \<in> shared_vars_assn\<^sup>k *\<^sub>a strl_assn'\<^sup>k \<rightarrow>\<^sub>a si64_assn\<close>
  using get_var_pos_c_impl.refine[FCOMP get_var_pos_c_get_var_posS, of Id]
  by auto

lemma [sepref_fr_rules]:
  \<open>(uncurry get_var_name_c_impl, uncurry get_var_nameS) \<in> shared_vars_assn\<^sup>k *\<^sub>a  si64_assn\<^sup>k \<rightarrow>\<^sub>a strl_assn'\<close>
  using get_var_name_c_impl.refine[FCOMP get_var_name_c_get_var_nameS, of Id]
 by auto

sepref_register get_var_nameS get_var_posS is_new_variableS

definition memory_allocation_rel :: \<open>(bool \<times> memory_allocation) set\<close> where
  \<open>memory_allocation_rel = {(b, e). b = alloc_failed e}\<close>

abbreviation memory_allocation_assn :: \<open>memory_allocation \<Rightarrow> 1 word \<Rightarrow> assn\<close> where
  \<open>memory_allocation_assn \<equiv> pure (bool1_rel O memory_allocation_rel)\<close>

instantiation memory_allocation :: default
begin
  definition default_memory_allocation :: \<open>memory_allocation\<close> where
    \<open>default_memory_allocation = Allocated\<close>
instance
  ..
end

lemmas mem_alloc_pure_reassembly =
  ENTAILS_def entails_def sep_algebra_simps pred_lift_extract_simps
  sep_conj_exists vcg_tag_defs

lemma to_bool_01[simp]: \<open>\<not> to_bool (0 :: 1 word)\<close> \<open>to_bool (1 :: 1 word)\<close>
  by (auto simp: to_bool_def)

lemmas bool1_rel_unfolds =
  bool1_rel_def bool.rel_def in_br_conv

lemma in_mem_alloc_rel_iff:
  \<open>(w, e) \<in> bool1_rel O memory_allocation_rel \<longleftrightarrow> (w, alloc_failed e) \<in> bool1_rel\<close>
  by (auto simp: memory_allocation_rel_def bool1_rel_unfolds)

sepref_register Allocated Mem_Out alloc_failed

lemma alloc_failed_hnr[sepref_fr_rules]:
  \<open>(Mreturn, RETURN o alloc_failed) \<in> memory_allocation_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  apply sepref_to_hoare
  by (vcg; auto simp: mem_alloc_pure_reassembly memory_allocation_rel_def)

lemma Allocated_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0), uncurry0 (RETURN Allocated))
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a memory_allocation_assn\<close>
  apply sepref_to_hoare
  by (vcg; auto simp: mem_alloc_pure_reassembly pure_def in_mem_alloc_rel_iff
    memory_allocation_rel_def bool1_rel_unfolds)

lemma Mem_Out_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 1), uncurry0 (RETURN Mem_Out))
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a memory_allocation_assn\<close>
  apply sepref_to_hoare
  by (vcg; auto simp: mem_alloc_pure_reassembly pure_def in_mem_alloc_rel_iff
    memory_allocation_rel_def bool1_rel_unfolds)

lemma numeral_2p63m1: \<open>(2::nat) ^ 63 - 1 = 9223372036854775807\<close>
  by simp

sepref_def find_new_idx_c_impl
  is \<open>find_new_idx_c\<close>
  :: \<open>perfect_shared_vars_assn\<^sup>k \<rightarrow>\<^sub>a memory_allocation_assn \<times>\<^sub>a si64_assn\<close>
  unfolding find_new_idx_c_def numeral_2p63m1
  apply (annot_snat_const "TYPE(64)")
  by sepref

instantiation String.literal :: default
begin
definition default_literal :: \<open>String.literal\<close> where
  \<open>default_literal = String.implode ''''\<close>
instance
  ..
end

lemmas [sepref_fr_rules] = snhm.lshm_update_hnr[FCOMP map_upd_fmupd]

lemma insert_variable_c_synth_def:
  \<open>insert_variable_c v k' = (\<lambda>(\<V>, \<A>). (\<V> @ [COPY v], fmupd (COPY v) k' \<A>))\<close>
  unfolding insert_variable_c_def COPY_def by auto

sepref_def insert_variable_c_impl
  is \<open>uncurry2 (RETURN ooo insert_variable_c)\<close>
  :: \<open>[\<lambda>((v, k), (xs, \<A>)). length xs + 1 < max_snat 64]\<^sub>a
      strl_assn'\<^sup>k *\<^sub>a si64_assn\<^sup>k *\<^sub>a perfect_shared_vars_assn\<^sup>d \<rightarrow> perfect_shared_vars_assn\<close>
  unfolding insert_variable_c_synth_def
  by sepref

lemmas [sepref_fr_rules] =
  find_new_idx_c_impl.refine insert_variable_c_impl.refine

lemma import_variable_c_synth_def:
  \<open>import_variable_c v S = do {
    (err, k') \<leftarrow> find_new_idx_c S;
    if alloc_failed err then do {let k'=k'; RETURN (err, S, k')}
    else do {
      ASSERT (k' < 2^63-1);
      ASSERT (length (fst S) + 1 < max_snat 64);
      RETURN (Allocated, insert_variable_c v k' S, k')
    }
  }\<close>
  unfolding import_variable_c_def find_new_idx_c_def
  apply (auto intro!: ext simp: pw_eq_iff refine_pw_simps Let_def max_snat_def
    split: if_splits prod.splits)
  by fastforce

sepref_register find_new_idx_c 
sepref_def import_variable_c_impl
  is \<open>uncurry import_variable_c\<close>
  :: \<open>strl_assn'\<^sup>k *\<^sub>a perfect_shared_vars_assn\<^sup>d \<rightarrow>\<^sub>a memory_allocation_assn \<times>\<^sub>a perfect_shared_vars_assn \<times>\<^sub>a si64_assn\<close>
  unfolding import_variable_c_synth_def
  by sepref

lemma import_variable_c_import_variableS':
  assumes \<open>single_valued R\<close> \<open>single_valued (R\<inverse>)\<close>
  shows \<open>(uncurry import_variable_c, uncurry import_variableS) \<in> R \<times>\<^sub>r perfect_shared_vars_rel_c R \<rightarrow>\<^sub>f
    \<langle>Id \<times>\<^sub>r perfect_shared_vars_rel_c R \<times>\<^sub>r nat_rel\<rangle>nres_rel\<close>
  using import_variable_c_import_variableS[OF _ _ assms]
  by (auto intro!: frefI nres_relI)

lemma [sepref_fr_rules]:
  \<open>(uncurry import_variable_c_impl, uncurry import_variableS)
  \<in> strl_assn'\<^sup>k *\<^sub>a  shared_vars_assn\<^sup>d \<rightarrow>\<^sub>a memory_allocation_assn \<times>\<^sub>a shared_vars_assn \<times>\<^sub>a si64_assn\<close>
  using import_variable_c_impl.refine[FCOMP import_variable_c_import_variableS', of Id]
 by auto

definition empty_shared_vars :: \<open>(nat, string) shared_vars\<close> where
  \<open>empty_shared_vars =  ({#}, fmempty, fmempty)\<close>

definition empty_shared_vars_int :: \<open>(string, nat) shared_vars_c\<close> where
  \<open>empty_shared_vars_int =  ([], fmempty)\<close>

definition empty_vars_hm :: \<open>(string, nat) fmap\<close> where
  \<open>empty_vars_hm = fmempty\<close>

definition empty_vars_hm_impl where [llvm_code]:
  \<open>empty_vars_hm_impl \<equiv> doM {
    ni \<leftarrow> ll_const (signed_nat 16384);
    snhm.lshm_empty ni
  }\<close>

lemma empty_vars_hm_aux:
  \<open>snhm.hm_assn'' (snhm.lshm_op_map_empty 16384) r \<turnstile> hm_fmap_assn empty_vars_hm r\<close>
proof -
  have 1: \<open>(snhm.lshm_op_map_empty 16384, op_map_empty) \<in> snhm.lshm_rel\<close>
    by (rule snhm.lshm_empty_fref) simp
  have 2: \<open>(op_map_empty, empty_vars_hm) \<in> map_fmap_rel\<close>
    by (auto simp: map_fmap_rel_def br_def empty_vars_hm_def fmempty.abs_eq)
  show ?thesis
    unfolding hr_comp_def
    apply (simp add: sep_conj_exists)
    apply (rule entails_exI[where x = \<open>op_map_empty\<close>])
    apply (rule entails_exI[where x = \<open>snhm.lshm_op_map_empty 16384\<close>])
    using 1 2 by (simp add: sep_algebra_simps pred_lift_extract_simps entails_refl)
qed

lemma empty_vars_hm_impl_rule[vcg_rules]:
  \<open>llvm_htriple \<box> empty_vars_hm_impl (\<lambda>r. hm_fmap_assn empty_vars_hm r)\<close>
  unfolding empty_vars_hm_impl_def
  supply [simp] = max_snat_def
  apply vcg
  apply (auto simp: sep_algebra_simps ENTAILS_def entails_def)
  apply (erule empty_vars_hm_aux[unfolded entails_def, rule_format])
  done

lemma empty_vars_hm_hnr[sepref_fr_rules]:
  \<open>(uncurry0 empty_vars_hm_impl, uncurry0 (RETURN empty_vars_hm))
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a hm_fmap_assn\<close>
  apply sepref_to_hoare
  apply vcg
  unfolding ENTAILS_def entails_def
  by (auto simp: pure_def sep_algebra_simps pred_lift_extract_simps sep_conj_exists
    intro!: exI[where x = empty_vars_hm])

sepref_register empty_vars_hm

definition op_strls_empty :: \<open>string list\<close> where
  [simp]: \<open>op_strls_empty = op_list_empty\<close>

interpretation strls_empty: list_custom_empty strls_assn strls.oa_empty op_strls_empty
  apply unfold_locales
  subgoal by (rule strls.oa_empty_hnr)
  subgoal by (rule op_strls_empty_def)
  done

sepref_def empty_shared_vars_int_impl
  is \<open>uncurry0 (RETURN empty_shared_vars_int)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a perfect_shared_vars_assn\<close>
  unfolding empty_shared_vars_int_def empty_vars_hm_def[symmetric]
    strls_empty.fold_custom_empty
  by sepref

lemma empty_shared_vars_int_empty_shared_vars:
  \<open>(uncurry0 (RETURN empty_shared_vars_int), uncurry0 (RETURN empty_shared_vars)) \<in> unit_rel \<rightarrow>\<^sub>f \<langle>perfect_shared_vars_rel_c R\<rangle>nres_rel\<close>
  by (auto intro!: frefI nres_relI simp: perfect_shared_vars_rel_c_def empty_shared_vars_int_def
    empty_shared_vars_def)

lemma [sepref_fr_rules]:
  \<open>(uncurry0 empty_shared_vars_int_impl, uncurry0 (RETURN empty_shared_vars))
  \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a shared_vars_assn\<close>
  using empty_shared_vars_int_impl.refine[FCOMP empty_shared_vars_int_empty_shared_vars, of Id]
  by auto
sepref_register empty_shared_vars
end
