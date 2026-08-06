theory IICF_HashSet
  imports IICF_Copying_List Isabelle_LLVM.Array_of_Array_List 
begin

text \<open>This theory defines Hash-Sets for arbitrary (possibly impure)
  objects, using @{term \<open>cl_assn\<close>} for buckets.
  The element interface is the \<open>hashset_env\<close> locale below, which combines the
  \<open>copyable_assn\<close>, \<open>eq_assn\<close> and \<open>hashable_assn\<close> locales from theory \<open>Assn_Env\<close>:
  insertion stores a copy of the (borrowed) element, deallocation frees the
  elements, bucket scans need equality and the bucket index needs a hash.\<close>

section \<open>Auxiliary word and bool lemmas\<close>

lemma snat_invar_mod:
  assumes B: \<open>snat_invar (b :: 'l::len2 word)\<close> and NZ: \<open>b \<noteq> 0\<close>
  shows \<open>snat_invar (a mod b)\<close>
proof -
  from B obtain m where M: \<open>LENGTH('l) = Suc m\<close> \<open>unat b < 2 ^ m\<close>
    by (auto simp: snat_invar_alt)
  have \<open>unat (a mod b) = unat a mod unat b\<close>
    by (simp add: unat_mod)
  also have \<open>\<dots> < unat b\<close>
    using NZ by (simp add: unat_gt_0)
  finally show ?thesis
    using M by (auto simp: snat_invar_alt)
qed

context begin
interpretation llvm_prim_arith_setup .

lemma ll_urem_hash_snat_rule:
  \<open>llvm_htriple
    (\<upharpoonleft>snat.assn n ni ** \<up>(0 < n))
    (ll_urem (h :: 'l::len2 word) ni)
    (\<lambda>r. \<upharpoonleft>snat.assn (unat h mod n) r ** \<upharpoonleft>snat.assn n ni)\<close>
  unfolding snat.assn_def
  supply [simp] = snat_invar_mod snat_eq_unat unat_mod unat_gt_0
  by vcg

end

text \<open>Extraction form of \<open>bool.assn\<close> facts on \<^emph>\<open>literal\<close> 1-words (e.g. the member
  flag consumed by \<open>llc_if\<close>).\<close>

lemma pure_bool_assn_iff: \<open>\<flat>\<^sub>pbool.assn b w \<longleftrightarrow> b = to_bool w\<close>
  unfolding bool.assn_def by simp

locale hashset_env =
  copyable_assn A afree acopy + eq_assn A aeq + hashable_assn A ahash ahash_impl
  for A :: \<open>'a \<Rightarrow> 'b::llvm_rep \<Rightarrow> assn\<close>
  and afree :: \<open>'b \<Rightarrow> unit llM\<close>
  and acopy :: \<open>'b \<Rightarrow> 'b llM\<close>
  and aeq :: \<open>'b \<Rightarrow> 'b \<Rightarrow> 1 word llM\<close>
  and ahash :: \<open>'a \<Rightarrow> 64 word\<close> \<comment> \<open>Note that keys are fixed to 64 word\<close>
  and ahash_impl :: \<open>'b \<Rightarrow> 64 word llM\<close>
begin

abbreviation \<open>bucket_assn \<equiv> cl_assn' A\<close>

text \<open>TODO list \<emdash> coverage of the @{theory Isabelle_LLVM.IICF_Set} interface.
  -- Required --
  \<^item> [ ] \<open>op_set_empty\<close>      empty hashset \<emdash> parameterized over size?
  \<^item> [ ] \<open>op_set_insert\<close>     stores \<open>acopy\<close> of the element; the caller keeps it
  \<^item> [ ] \<open>op_set_member\<close>     the hot operation: borrow the bucket, scan it with
                            \<open>aeq\<close>, put it back. Must not copy the bucket.

  Infrastructure (not interface ops):
  \<^item> [ ] \<open>MK_FREE\<close>           deep free (frees every bucket and every element)

  -- Not required --
  \<^item> [ ] \<open>op_set_delete\<close>     
  \<^item> [ ] \<open>op_set_is_empty\<close>   
  \<^item> [ ] \<open>op_set_union\<close>      
  \<^item> [ ] \<open>op_set_subseteq\<close>   
  \<^item> [ ] \<open>op_set_inter\<close>      
  \<^item> [ ] \<open>op_set_pick\<close>       
  \<^item> [ ] \<open>COPY\<close>\<close>

section \<open>High-level Hashset by nested lists.\<close>
text \<open>Like in IICF_Partial_Map, we first use abstract nested lists which we then refine down
  to llM level.\<close>


definition \<open>lshs_bucket_of n a \<equiv> unat (ahash a) mod n\<close>
definition \<open>lshs_invar xs \<equiv> xs\<noteq>[] \<and>
  (\<forall>i < length xs. \<forall>a \<in> set (xs!i). lshs_bucket_of (length xs) a = i)\<close>
definition \<open>lshs_\<alpha> xs = { a. \<exists>b\<in>set xs. a \<in> set b }\<close>
definition \<open>lshs_rel \<equiv> br lshs_\<alpha> lshs_invar\<close>

definition \<open>lshs_op_set_empty n \<equiv> replicate n ([] :: 'a list)\<close>
definition \<open>lshs_op_set_insert a xs \<equiv>
  xs[lshs_bucket_of (length xs) a := a # xs!(lshs_bucket_of (length xs) a)]\<close> 
definition \<open>lshs_op_set_member a xs \<equiv> a \<in> set (xs!(lshs_bucket_of (length xs) a))\<close>

lemma lshs_op_set_empty_refine:
  assumes \<open>0 < n\<close>
  shows \<open>(lshs_op_set_empty n, op_set_empty) \<in> lshs_rel\<close>
  unfolding lshs_rel_def in_br_conv lshs_op_set_empty_def op_set_empty_def
    lshs_\<alpha>_def lshs_invar_def
  using assms by simp

lemma lshs_op_set_insert_refine:
  \<open>(uncurry (RETURN oo lshs_op_set_insert), uncurry (RETURN oo op_set_insert))
  \<in> Id \<times>\<^sub>r lshs_rel \<rightarrow>\<^sub>f \<langle>lshs_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (auto simp: lshs_rel_def in_br_conv)
  subgoal
    by (metis (lifting) length_greater_0_conv list.set_intros(1) lshs_\<alpha>_def
    lshs_bucket_of_def lshs_invar_def lshs_op_set_insert_def mem_Collect_eq
    mod_less_divisor set_update_memI)
  subgoal
    by (smt (verit, best) in_set_upd_cases list.set_intros(2) list_update_id
    list_update_overwrite lshs_\<alpha>_def lshs_op_set_insert_def mem_Collect_eq
    set_update_memI)
  subgoal
    by (smt (verit, best) in_set_upd_cases lshs_\<alpha>_def lshs_op_set_insert_def
    mem_Collect_eq nth_mem set_ConsD)
  subgoal
    by (simp add: lshs_invar_def lshs_op_set_insert_def nth_list_update')
  done

lemma lshs_op_set_member_refine:
  \<open>(uncurry (RETURN oo lshs_op_set_member), uncurry (RETURN oo op_set_member))
  \<in> Id \<times>\<^sub>r lshs_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (auto simp: lshs_rel_def in_br_conv)
  subgoal
    using lshs_\<alpha>_def lshs_bucket_of_def lshs_invar_def lshs_op_set_member_def
    by fastforce
  subgoal 
    by (smt (verit, best) in_set_conv_nth lshs_\<alpha>_def lshs_invar_def
    lshs_op_set_member_def mem_Collect_eq)
  done

section \<open>Refining Operations\<close>

lemma lshs_bucket_of_lt[simp]: \<open>0 < n \<Longrightarrow> lshs_bucket_of n a < n\<close>
  by (simp add: lshs_bucket_of_def)

subsection \<open>Buckets\<close>

lemma hs_bucket_init: \<open>\<box> \<turnstile> \<upharpoonleft>(cl_assn A) [] init\<close>
  by (simp add: cl_assn'_def[symmetric] cl_assn_simps sep_algebra_simps)

subsection \<open>The hash-set assertion\<close>

type_synonym 'bi hs_conc = \<open>64 word \<times> 'bi node ptr ptr\<close>

definition hs_assn :: \<open>('a list list, 'b hs_conc) dr_assn\<close> where
  \<open>hs_assn \<equiv> mk_assn (\<lambda>xs (ni, ai).
     \<upharpoonleft>snat.assn (length xs) ni
  ** \<upharpoonleft>(Array_of_Array_List.nao_assn (cl_assn A) Map.empty) xs ai)\<close>

lemma hs_assn_conv:
  \<open>\<upharpoonleft>hs_assn xs (ni, ai) =
    (\<upharpoonleft>snat.assn (length xs) ni
     ** \<upharpoonleft>(Array_of_Array_List.nao_assn (cl_assn A) Map.empty) xs ai)\<close>
  unfolding hs_assn_def by simp

subsection \<open>Empty hash-set\<close>

definition hs_empty :: \<open>64 word \<Rightarrow> 'b hs_conc llM\<close> where [llvm_code, llvm_inline]:
  \<open>hs_empty ni \<equiv> doM {
    a \<leftarrow> nao_new TYPE('b cl_list) ni;
    Mreturn (ni, a)
  }\<close>

lemma hs_empty_rule[vcg_rules]:
  \<open>llvm_htriple
    (\<upharpoonleft>snat.assn n ni)
    (hs_empty ni)
    (\<lambda>p. \<upharpoonleft>hs_assn (lshs_op_set_empty n) p)\<close>
  unfolding hs_empty_def hs_assn_def lshs_op_set_empty_def
  supply [vcg_rules] = nao_new_init_rl[OF hs_bucket_init]
  by vcg

lemma hs_empty_hnr[sepref_fr_rules]:
  \<open>(hs_empty, (RETURN o lshs_op_set_empty))
  \<in> [\<lambda>n. 0 < n]\<^sub>a (snat_assn' TYPE(64))\<^sup>k \<rightarrow> \<upharpoonleft>hs_assn\<close>
  unfolding snat_rel_def snat.assn_is_rel[symmetric]
  by (sepref_to_hoare; vcg)

(* We can not register agains high level `op_set_empty_refine` *)
(* Without resizing implemented, I think it might be better to use the explicit lshs_op_set_empty then *)
(* lemmas hs_empty_hnr = hs_empty_hnr[FCOMP lshs_op_set_empty_refine] *)

subsection \<open>Insert\<close>

definition \<open>hs_bucket_of \<equiv> \<lambda>ii (li, ai). doM {
    hi \<leftarrow> ahash_impl ii;   
    hi \<leftarrow> ll_urem hi li;
    Mreturn hi
  }\<close>

lemma hs_bucket_of_rule[vcg_rules]:
  \<open>llvm_htriple
    (A i ii ** \<upharpoonleft>hs_assn xs (ni, ai) ** \<up>(xs \<noteq> []))
    (hs_bucket_of ii (ni, ai))
  (\<lambda>r. A i ii ** \<upharpoonleft>hs_assn xs (ni, ai)**
  \<upharpoonleft>snat.assn (lshs_bucket_of (length xs) i) r)\<close>
  unfolding hs_bucket_of_def
  supply [simp] = hs_assn_conv lshs_bucket_of_def pure_app_eq
  supply [vcg_rules] = ll_urem_hash_snat_rule
  by vcg


definition \<open>hs_insert \<equiv> \<lambda>ai (li, xsi). doM {
    hi \<leftarrow> hs_bucket_of ai (li, xsi); 
    bi \<leftarrow> nao_nth xsi hi;
    bi \<leftarrow> cl_prepend ai bi;
    xsi \<leftarrow> nao_upd xsi hi bi;
    Mreturn (li, xsi)
  }\<close>

lemma hs_insrt_rule[vcg_rules]:
  \<open>llvm_htriple
    (A a ai ** \<upharpoonleft>hs_assn xs (li, xsi) ** \<up>(xs\<noteq>[]))
    (hs_insert ai (li, xsi))
    (\<lambda>r. \<upharpoonleft>hs_assn (lshs_op_set_insert a xs) r)
  \<close>
  unfolding hs_insert_def
  supply [simp] = hs_assn_conv lshs_op_set_insert_def pure_app_eq
  supply [vcg_rules] = hs_bucket_of_rule[unfolded hs_assn_conv]
    cl_prepend_rule[unfolded cl_assn'_def]
  by vcg

lemma hs_insert_hnr:
  \<open>(uncurry hs_insert, uncurry (RETURN oo lshs_op_set_insert))
  \<in> [\<lambda>(a, xs). xs \<noteq> []]\<^sub>a A\<^sup>d *\<^sub>a \<upharpoonleft>hs_assn\<^sup>d \<rightarrow> \<upharpoonleft>hs_assn\<close>
  by (sepref_to_hoare; vcg)

lemmas [fcomp_prenorm_simps] = lshs_rel_def in_br_conv lshs_invar_def

lemmas hs_insert_hnr2[sepref_fr_rules] =
  hs_insert_hnr[FCOMP lshs_op_set_insert_refine]

section \<open>@{term op_set_member}\<close>

definition \<open>hs_member \<equiv> \<lambda>ai (li, xsi). doM{
    hi \<leftarrow> hs_bucket_of ai (li, xsi);
    bi \<leftarrow> nao_nth xsi hi;
    r \<leftarrow> cl_contains ai bi;
    nao_rejoin xsi hi;
    Mreturn r
  }\<close>

lemma hs_member_rule[vcg_rules]:
  \<open>llvm_htriple
  (A a ai ** \<upharpoonleft>hs_assn xs (li, xsi) ** \<up>(xs\<noteq>[]))
  (hs_member ai (li, xsi))
  (\<lambda>r. A a ai ** \<upharpoonleft>hs_assn xs (li, xsi) ** bool1_assn (lshs_op_set_member a xs) r)
  \<close>
  unfolding hs_member_def lshs_op_set_member_def bool1_rel_def
    pure_def
  supply [simp] = hs_assn_conv bool.assn_def bool.rel_def in_br_conv
  supply [vcg_rules] = hs_bucket_of_rule[unfolded hs_assn_conv]
    cl_contains_rule[unfolded cl_assn'_def]
  by vcg

lemma hs_member_hnr:
  \<open>(uncurry hs_member, uncurry (RETURN oo lshs_op_set_member))
  \<in> [\<lambda>(a, xs). xs \<noteq> []]\<^sub>a A\<^sup>k *\<^sub>a \<upharpoonleft>hs_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  supply [simp] = bool1_rel_def pure_def
  by (sepref_to_hoare; vcg)

lemmas hs_member_hnr2[sepref_fr_rules] =
  hs_member_hnr[FCOMP lshs_op_set_member_refine]

abbreviation \<open>hs_assn' \<equiv> hr_comp \<upharpoonleft>hs_assn lshs_rel\<close>

end

end
