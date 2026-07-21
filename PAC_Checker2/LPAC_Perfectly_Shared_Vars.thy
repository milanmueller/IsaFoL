theory LPAC_Perfectly_Shared_Vars
  imports
    LPAC_Perfectly_Shared
    PAC_Checker_LLVM.PAC_Checker_Relation
    PAC_Checker_LLVM.PAC_Map_Rel
    PAC_Checker_LLVM.Shared_Vars_Assn
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
  else do{
    ASSERT(k' < 2^63-1);
    RETURN (Allocated, insert_variable_c v k' \<V>\<A>, k')
    }
    })\<close>

lemma import_variable_c_alt_def:
  \<open>import_variable_c v = (\<lambda>(\<V>, \<A>). do {
  (err, k') \<leftarrow> find_new_idx_c (\<V>, \<A>);
  if alloc_failed err then do {let k'=k'; RETURN (err, (\<V>, \<A>), k')}
  else do{
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


section \<open>LLVM implementation\<close>

text \<open>The abstract shared-variables triple \<open>(\<D>, \<V>, \<A>) :: (nat, string) shared_vars\<close>
  is implemented by the \<open>shared_vars_l\<close> triple of \<open>Shared_Vars_Assn\<close>
  (\<open>PAC_Checker_LLVM\<close>): a fresh-index counter \<open>n\<close> (replacing the
  multiset \<open>\<D>\<close>, which carries no executable content beyond freshness), the
  index-to-name map \<open>\<V>\<close> (pam with owning string values) and the name-to-index
  string hash map \<open>\<A>\<close>. The old middle layer (\<open>shared_vars_c\<close> over pure literal
  strings, arl + hashmap, uint64) is gone; the \<open>_c\<close> definitions above are kept
  only as documentation of the original design.

  Two mode changes against the old Imperative-HOL setup:
  \<^item> strings are heap-owned (\<open>strl_assn\<close>), so \<open>import_variableS\<close> \<^emph>\<open>consumes\<close> its
    name argument (\<open>\<^sup>d\<close>) \<comment> \<open>call sites that keep the name must \<open>COPY\<close>\<close>;
  \<^item> \<open>get_var_nameS\<close> returns a fresh copy of the stored name (the pam
    the-lookup copies via \<open>strl_copy\<close>).\<close>

subsection \<open>Relation to the abstract triple\<close>

definition perfect_shared_vars_rel_l
  :: \<open>(shared_vars_l \<times> (nat, string) shared_vars) set\<close>
where
  \<open>perfect_shared_vars_rel_l =
    {((n, \<V>, \<A>), (\<D>', \<V>', \<A>')). (\<forall>i\<in>#dom_m \<V>'. i < n) \<and>
      \<V> = fmlookup \<V>' \<and> \<A> = fmlookup \<A>'}\<close>

abbreviation shared_vars_assn
  :: \<open>(nat, string) shared_vars \<Rightarrow> shared_vars_l_impl \<Rightarrow> assn\<close>
where
  \<open>shared_vars_assn \<equiv> hr_comp shared_vars_l_assn perfect_shared_vars_rel_l\<close>

subsection \<open>Memory-allocation flags\<close>

text \<open>At the \<open>_l\<close> level allocation failure is a plain \<open>bool\<close> (\<open>True\<close> = failed); the
  \<open>memory_allocation\<close> datatype is recovered by relational composition.\<close>

definition memory_allocation_rel :: \<open>(bool \<times> memory_allocation) set\<close> where
  \<open>memory_allocation_rel = {(b, e). b = alloc_failed e}\<close>

abbreviation memory_allocation_assn
  :: \<open>memory_allocation \<Rightarrow> 1 word \<Rightarrow> assn\<close>
where
  \<open>memory_allocation_assn \<equiv> pure (bool1_rel O memory_allocation_rel)\<close>

text \<open>Pure reassembly bundle, cf. \<open>status_pure_reassembly\<close> in the
  \<open>PAC_Checker_LLVM\<close> synthesis (not in scope here).\<close>

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
  by (vcg; auto simp: mem_alloc_pure_reassembly pure_def in_mem_alloc_rel_iff
    memory_allocation_rel_def)

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

subsection \<open>Refinement of the operations\<close>

lemma find_new_idx_l_find_new_idx:
  assumes \<open>(S, S') \<in> perfect_shared_vars_rel_l\<close>
  shows \<open>find_new_idx_l S \<le> \<Down>{((b, k), (mem, k')).
      b = alloc_failed mem \<and> (\<not>b \<longrightarrow> k = k' \<and> k < 2^63-1 \<and> k = fst S)}
    (find_new_idx S')\<close>
proof -
  obtain n \<V> \<A> where S: \<open>S = (n, \<V>, \<A>)\<close> by (cases S)
  obtain \<D>' \<V>' \<A>' where S': \<open>S' = (\<D>', \<V>', \<A>')\<close> by (cases S')
  have fresh: \<open>n \<notin># dom_m \<V>'\<close>
    using assms unfolding S S' perfect_shared_vars_rel_l_def
    by force
  show ?thesis
    unfolding find_new_idx_l_def find_new_idx_def S S' prod.case
    apply (cases \<open>n < 2^63-1\<close>)
    subgoal
      by (auto intro!: RETURN_RES_refine exI[where x = \<open>(Allocated, n)\<close>]
        simp: fresh S)
    subgoal
      by (auto intro!: RETURN_RES_refine exI[where x = \<open>(Mem_Out, 0)\<close>])
    done
qed

lemma import_variable_l_import_variableS:
  \<open>(uncurry import_variable_l, uncurry import_variableS)
    \<in> Id \<times>\<^sub>r perfect_shared_vars_rel_l \<rightarrow>\<^sub>f
      \<langle>memory_allocation_rel \<times>\<^sub>r perfect_shared_vars_rel_l \<times>\<^sub>r nat_rel\<rangle>nres_rel\<close>
proof -
  have H: \<open>import_variable_l v S
    \<le> \<Down>(memory_allocation_rel \<times>\<^sub>r perfect_shared_vars_rel_l \<times>\<^sub>r nat_rel)
      (import_variableS v S')\<close>
    if SS: \<open>(S, S') \<in> perfect_shared_vars_rel_l\<close> for v S S'
  proof -
    obtain n \<V> \<A> where S: \<open>S = (n, \<V>, \<A>)\<close> by (cases S)
    obtain \<D>' \<V>' \<A>' where S': \<open>S' = (\<D>', \<V>', \<A>')\<close> by (cases S')
    note fni = find_new_idx_l_find_new_idx[OF SS, unfolded S S' fst_conv]
    show ?thesis
      unfolding import_variable_l_def import_variableS_def insert_variable_l_def
        S S' prod.case Let_def COPY_def
      apply (refine_rcg fni)
      subgoal by auto
      subgoal using SS
        by (auto simp: pw_le_iff refine_pw_simps memory_allocation_rel_def S S')
      subgoal using SS
        by (auto simp: pw_le_iff refine_pw_simps perfect_shared_vars_rel_l_def
            memory_allocation_rel_def fun_eq_iff S S'
            dest!: in_diffD)
      done
  qed
  show ?thesis
    by (intro frefI nres_relI) (use H in \<open>auto simp: uncurry_def\<close>)
qed

lemma is_new_variable_l_is_new_variableS:
  \<open>(uncurry is_new_variable_l, uncurry is_new_variableS)
    \<in> Id \<times>\<^sub>r perfect_shared_vars_rel_l \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: is_new_variable_l_def is_new_variableS_def
      perfect_shared_vars_rel_l_def in_dom_m_lookup_iff dom_def)

lemma get_var_pos_l_get_var_posS:
  \<open>(uncurry get_var_pos_l, uncurry get_var_posS)
    \<in> perfect_shared_vars_rel_l \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: get_var_pos_l_def get_var_posS_def perfect_shared_vars_rel_l_def
      in_dom_m_lookup_iff dom_def pw_le_iff refine_pw_simps)

lemma get_var_name_l_get_var_nameS:
  \<open>(uncurry get_var_name_l, uncurry get_var_nameS)
    \<in> perfect_shared_vars_rel_l \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>\<langle>Id\<rangle>list_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: get_var_name_l_def get_var_nameS_def perfect_shared_vars_rel_l_def
      in_dom_m_lookup_iff dom_def pw_le_iff refine_pw_simps)

subsection \<open>Composed refinement rules\<close>

lemma is_new_variableS_hnr[sepref_fr_rules]:
  \<open>(uncurry is_new_variable_l_impl, uncurry is_new_variableS)
    \<in> strl_assn\<^sup>k *\<^sub>a shared_vars_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  using is_new_variable_l_impl.refine[FCOMP is_new_variable_l_is_new_variableS]
  by auto

lemma get_var_posS_hnr[sepref_fr_rules]:
  \<open>(uncurry get_var_pos_l_impl, uncurry get_var_posS)
    \<in> shared_vars_assn\<^sup>k *\<^sub>a strl_assn\<^sup>k \<rightarrow>\<^sub>a unat_assn' TYPE(64)\<close>
  using get_var_pos_l_impl.refine[FCOMP get_var_pos_l_get_var_posS]
  by auto

lemma get_var_nameS_hnr[sepref_fr_rules]:
  \<open>(uncurry get_var_name_l_impl, uncurry get_var_nameS)
    \<in> shared_vars_assn\<^sup>k *\<^sub>a (unat_assn' TYPE(64))\<^sup>k \<rightarrow>\<^sub>a strl_assn\<close>
  using get_var_name_l_impl.refine[FCOMP get_var_name_l_get_var_nameS]
  by auto

lemma import_variableS_hnr[sepref_fr_rules]:
  \<open>(uncurry import_variable_l_impl, uncurry import_variableS)
    \<in> strl_assn\<^sup>d *\<^sub>a shared_vars_assn\<^sup>d \<rightarrow>\<^sub>a
      memory_allocation_assn \<times>\<^sub>a shared_vars_assn \<times>\<^sub>a unat_assn' TYPE(64)\<close>
  using import_variable_l_impl.refine[FCOMP import_variable_l_import_variableS]
  by auto

sepref_register get_var_nameS get_var_posS is_new_variableS import_variableS

subsection \<open>The empty store\<close>

definition empty_shared_vars :: \<open>(nat, string) shared_vars\<close> where
  \<open>empty_shared_vars =  ({#}, fmempty, fmempty)\<close>

lemma empty_shared_vars_l_empty_shared_vars:
  \<open>(uncurry0 (RETURN empty_shared_vars_l), uncurry0 (RETURN empty_shared_vars))
    \<in> unit_rel \<rightarrow>\<^sub>f \<langle>perfect_shared_vars_rel_l\<rangle>nres_rel\<close>
  by (auto intro!: frefI nres_relI
    simp: perfect_shared_vars_rel_l_def empty_shared_vars_l_def
      empty_shared_vars_def fun_eq_iff)

lemma empty_shared_vars_hnr[sepref_fr_rules]:
  \<open>(uncurry0 empty_shared_vars_l_impl, uncurry0 (RETURN empty_shared_vars))
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a shared_vars_assn\<close>
  using empty_shared_vars_l_impl.refine[FCOMP empty_shared_vars_l_empty_shared_vars]
  by auto

sepref_register empty_shared_vars

subsection \<open>Deallocation\<close>

definition shared_vars_free :: \<open>shared_vars_l_impl \<Rightarrow> unit llM\<close> where [llvm_code]:
  \<open>shared_vars_free \<equiv> \<lambda>(n, \<V>i, \<A>i). doM {
     pam_free_impl os_delete \<V>i;
     svm_free_impl \<A>i;
     Mreturn ()
   }\<close>

lemma shared_vars_l_assn_free[sepref_frame_free_rules]:
  \<open>MK_FREE shared_vars_l_assn shared_vars_free\<close>
  supply [vcg_rules] = vnm_assn_free[THEN MK_FREED] svm_assn_free[THEN MK_FREED]
  apply (rule MK_FREEI)
  unfolding shared_vars_free_def
  apply (clarsimp simp: prod_assn_def split: prod.splits)
  apply vcg
  apply (auto simp: mem_alloc_pure_reassembly pure_def)
  done

lemma shared_vars_assn_free[sepref_frame_free_rules]:
  \<open>MK_FREE shared_vars_assn shared_vars_free\<close>
  by (intro MK_FREE_hrcompI shared_vars_l_assn_free)

end
