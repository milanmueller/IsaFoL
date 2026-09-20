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

section \<open>Saturating element counter and table growth\<close>

text \<open>Shared by the hash-set and the hash-map: a 63-bit element counter that saturates instead of overflowing.
  This is used to increment the element counter which is only used for resizing and is not relevant to
  the correctness of the refinement.\<close>

abbreviation \<open>sat_max_count \<equiv> max_snat 64 - 1\<close>

definition sat_inc :: \<open>64 word \<Rightarrow> 64 word llM\<close> where [llvm_code, llvm_inline]:
  \<open>sat_inc li \<equiv> doM {
    b \<leftarrow> ll_icmp_ult li (signed_nat 9223372036854775807);
    llc_if b (ll_add li (signed_nat 1)) (Mreturn li)
  }\<close>

definition sat_dec :: \<open>64 word \<Rightarrow> 64 word llM\<close> where [llvm_code, llvm_inline]:
  \<open>sat_dec li \<equiv> doM {
    b \<leftarrow> ll_icmp_eq li (signed_nat 0);
    llc_if b (Mreturn li) (ll_sub li (signed_nat 1))
  }\<close>

lemma min_count_inc[simp]:
  \<open>min (Suc (min l M)) M = min (Suc l) M\<close>
  \<open>min (min l M + 1) M = min (l + 1) M\<close>
  by (auto simp: min_def)

lemma snat_assn_lt_max_snat:
  \<open>\<flat>\<^sub>p snat.assn n (w::'l::len2 word) \<Longrightarrow> n < max_snat LENGTH('l)\<close>
  unfolding snat.assn_def by (auto simp: snat_invar_alt snat_eq_unat max_snat_def)

lemma sat_inc_rule[vcg_rules]:
  \<open>llvm_htriple
    (\<upharpoonleft>snat.assn c li)
    (sat_inc li)
    (\<lambda>r. \<upharpoonleft>snat.assn (min (c + 1) sat_max_count) r)\<close>
  unfolding sat_inc_def
  supply [simp] = max_snat_def
  apply vcg_monadify
  apply vcg'
  subgoal for r ra
    apply (frule snat_assn_lt_max_snat)
    apply (subgoal_tac \<open>c = 9223372036854775807\<close>)
    subgoal by hypsubst vcg
    subgoal by simp
    done
  by (rule Defer_Slot.remove_slot)

lemma sat_dec_rule[vcg_rules]:
  \<open>llvm_htriple
    (\<upharpoonleft>snat.assn c li)
    (sat_dec li)
    (\<lambda>r. \<upharpoonleft>snat.assn (c - 1) r)\<close>
  unfolding sat_dec_def
  apply vcg_monadify
  by vcg

definition \<open>sat_inc_\<alpha> \<equiv> \<lambda>c. min (c+1) sat_max_count\<close>

lemma sat_inc_hnr[sepref_fr_rules]:
  \<open>(sat_inc, RETURN o sat_inc_\<alpha>)
  \<in> (snat_assn' TYPE(64))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(64)\<close>
  unfolding snat_rel_def snat.assn_is_rel[symmetric] sat_inc_\<alpha>_def
  by (sepref_to_hoare; vcg)

text \<open>Rehash loops build the new table as a fold over the buckets drained so far.\<close>

lemma fold_concat_take_Suc[simp]:
  \<open>i < length xs \<Longrightarrow> fold f (concat (take (Suc i) xs)) e = fold f (xs ! i) (fold f (concat (take i xs)) e)\<close>
  by (simp add: take_Suc_conv_app_nth)

text \<open>Capped doubling of the bucket count: doubling stays representable exactly while the
  count is below \<open>2^62\<close>; at the cap the table is not grown any further.\<close>

definition \<open>ht_grow n \<equiv> if n < 4611686018427387904 then 2 * n else n\<close>

sepref_def ht_grow_impl is \<open>RETURN o ht_grow\<close>
  :: \<open>(snat_assn' TYPE(64))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(64)\<close>
  unfolding ht_grow_def
  apply (annot_snat_const "TYPE(64)")
  by sepref

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
  \<^item> [ ] \<open>op_set_insert\<close>
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
definition \<open>lshs_invar \<equiv> \<lambda>(xs, l). xs\<noteq>[] \<and> l = length (concat xs) \<and>
  (\<forall>i < length xs. \<forall>a \<in> set (xs!i). lshs_bucket_of (length xs) a = i)\<close>
definition \<open>lshs_\<alpha> \<equiv> \<lambda>(xs,l). { a. \<exists>b\<in>set xs. a \<in> set b }\<close>
definition \<open>lshs_rel \<equiv> br lshs_\<alpha> lshs_invar\<close>

definition \<open>lshs_op_set_empty n \<equiv> (replicate n ([] :: 'a list), 0::nat)\<close>
definition \<open>lshs_op_set_insert \<equiv> \<lambda>a (xs, l::nat).
  (xs[lshs_bucket_of (length xs) a := a # xs!(lshs_bucket_of (length xs) a)], l+1)\<close> 
definition \<open>lshs_op_set_member \<equiv> \<lambda>a (xs,l). a \<in> set (xs!(lshs_bucket_of (length xs) a))\<close>
definition \<open>lshs_op_set_resize \<equiv> \<lambda>n (xs, l::nat). fold lshs_op_set_insert (concat xs) (lshs_op_set_empty n)\<close>

lemma lshs_op_set_empty_refine:
  assumes \<open>0 < n\<close>
  shows \<open>(lshs_op_set_empty n, op_set_empty) \<in> lshs_rel\<close>
  unfolding lshs_rel_def in_br_conv lshs_op_set_empty_def op_set_empty_def
    lshs_\<alpha>_def lshs_invar_def
  using assms by simp

lemma length_concat_update_cons:
  \<open>i < length xs \<Longrightarrow> length (concat (xs[i := a # xs!i])) = Suc (length (concat xs))\<close>
  by (simp add: length_concat map_update sum_list_update)

lemma lshs_op_set_insert_step:
  assumes \<open>lshs_invar s\<close>
  shows \<open>lshs_invar (lshs_op_set_insert a s)\<close>
    and \<open>lshs_\<alpha> (lshs_op_set_insert a s) = insert a (lshs_\<alpha> s)\<close>
proof -
  obtain xs l where [simp]: \<open>s = (xs, l)\<close> by (cases s)
  have NE: \<open>xs \<noteq> []\<close> using assms by (simp add: lshs_invar_def)
  hence LT: \<open>lshs_bucket_of (length xs) a < length xs\<close> by (simp add: lshs_bucket_of_def)
  show \<open>lshs_invar (lshs_op_set_insert a s)\<close>
    using assms LT
    by (auto simp: lshs_invar_def lshs_op_set_insert_def nth_list_update' length_concat_update_cons)
  show \<open>lshs_\<alpha> (lshs_op_set_insert a s) = insert a (lshs_\<alpha> s)\<close>
    using LT
    apply (auto simp: lshs_\<alpha>_def lshs_op_set_insert_def)
    subgoal by (metis in_set_upd_cases nth_mem set_ConsD)
    subgoal by (metis list.set_intros(1) set_update_memI)
    subgoal for b x
      apply (subst (asm) in_set_conv_nth, elim exE conjE)
      subgoal for j
        apply (cases \<open>j = lshs_bucket_of (length xs) a\<close>)
        subgoal
          by (rule bexI[of _ \<open>a # xs ! lshs_bucket_of (length xs) a\<close>]) (auto simp: set_update_memI)
        subgoal
          by (rule bexI[of _ \<open>xs ! j\<close>]) (metis length_list_update nth_list_update_neq nth_mem)+
        done
      done
    done
qed

lemma lshs_op_set_insert_refine:
  \<open>(uncurry (RETURN oo lshs_op_set_insert), uncurry (RETURN oo op_set_insert))
  \<in> Id \<times>\<^sub>r lshs_rel \<rightarrow>\<^sub>f \<langle>lshs_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  by (auto simp: lshs_rel_def in_br_conv lshs_op_set_insert_step)

lemma lshs_op_set_member_refine:
  \<open>(uncurry (RETURN oo lshs_op_set_member), uncurry (RETURN oo op_set_member))
  \<in> Id \<times>\<^sub>r lshs_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (auto simp: lshs_rel_def in_br_conv)
  subgoal
    using lshs_\<alpha>_def lshs_bucket_of_def lshs_invar_def lshs_op_set_member_def
    by (metis (mono_tags, lifting) length_greater_0_conv mem_Collect_eq
    mod_less_divisor nth_mem old.prod.case)
  subgoal 
    using lshs_\<alpha>_def lshs_bucket_of_def lshs_invar_def lshs_op_set_member_def
    by (smt (verit, best) in_set_conv_nth mem_Collect_eq old.prod.case)
  done

lemma lshs_fold_insert:
  assumes \<open>lshs_invar s\<close>
  shows \<open>lshs_invar (fold lshs_op_set_insert ys s)\<close>
    and \<open>lshs_\<alpha> (fold lshs_op_set_insert ys s) = lshs_\<alpha> s \<union> set ys\<close>
  using assms
  by (induction ys arbitrary: s) (auto simp: lshs_op_set_insert_step)

lemma lshs_\<alpha>_concat: \<open>lshs_\<alpha> (xs, l) = set (concat xs)\<close>
  by (auto simp: lshs_\<alpha>_def)

lemma lshs_op_set_resize_refine:
  assumes \<open>0 < n\<close>
      and \<open>lshs_invar (xs,l)\<close>
    shows \<open>lshs_invar (lshs_op_set_resize n (xs,l))\<close>
      and \<open>lshs_\<alpha> (xs,l) = lshs_\<alpha> (lshs_op_set_resize n (xs,l))\<close>
proof -
  have E: \<open>lshs_invar (lshs_op_set_empty n)\<close>
    using lshs_op_set_empty_refine[OF assms(1)] by (simp add: lshs_rel_def in_br_conv)
  have A: \<open>lshs_\<alpha> (lshs_op_set_empty n) = {}\<close>
    unfolding lshs_\<alpha>_def lshs_op_set_empty_def by auto
  show \<open>lshs_invar (lshs_op_set_resize n (xs,l))\<close>
    unfolding lshs_op_set_resize_def by (simp add: lshs_fold_insert(1)[OF E])
  have \<open>lshs_\<alpha> (fold lshs_op_set_insert (concat xs) (lshs_op_set_empty n))
    = lshs_\<alpha> (lshs_op_set_empty n) \<union> set (concat xs)\<close>
    using lshs_fold_insert(2)[OF E] by blast
  thus \<open>lshs_\<alpha> (xs,l) = lshs_\<alpha> (lshs_op_set_resize n (xs,l))\<close>
    unfolding lshs_op_set_resize_def by (simp add: A lshs_\<alpha>_concat)
qed

section \<open>Refining Operations\<close>

lemma lshs_bucket_of_lt[simp]: \<open>0 < n \<Longrightarrow> lshs_bucket_of n a < n\<close>
  by (simp add: lshs_bucket_of_def)

subsection \<open>Buckets\<close>

lemma hs_bucket_init: \<open>\<box> \<turnstile> \<upharpoonleft>(cl_assn A) [] init\<close>
  by (simp add: cl_assn'_def[symmetric] cl_assn_simps sep_algebra_simps)

subsection \<open>The hash-set assertion\<close>

type_synonym 'bi hs_conc = \<open>64 word \<times> 'bi node ptr ptr \<times> 64 word\<close>

definition hs_assn :: \<open>(('a list list \<times> nat), 'b hs_conc) dr_assn\<close> where
  \<open>hs_assn \<equiv> mk_assn (\<lambda>(xs,l) (ni, ai, li).
     \<upharpoonleft>snat.assn (min l sat_max_count) li
  ** \<upharpoonleft>snat.assn (length xs) ni
  ** \<upharpoonleft>(Array_of_Array_List.nao_assn (cl_assn A) Map.empty) xs ai)\<close>

lemma hs_assn_conv:
  \<open>\<upharpoonleft>hs_assn (xs,l) (ni, ai, li) =
       (\<upharpoonleft>snat.assn (min l sat_max_count) li
     ** \<upharpoonleft>snat.assn (length xs) ni
     ** \<upharpoonleft>(Array_of_Array_List.nao_assn (cl_assn A) Map.empty) xs ai)\<close>
  unfolding hs_assn_def by simp

lemma hs_assn_ex_pair_eq[simp]:
  \<open>(\<lambda>s. \<exists>a b. (\<upharpoonleft>hs_assn (a,b) c ** \<up>((a,b) = p)) s) = \<upharpoonleft>hs_assn p c\<close>
  by (cases p) (auto simp: fun_eq_iff sep_algebra_simps pred_lift_extract_simps)

subsection \<open>Empty hash-set\<close>

definition hs_empty :: \<open>64 word \<Rightarrow> 'b hs_conc llM\<close> where [llvm_code, llvm_inline]:
  \<open>hs_empty ni \<equiv> doM {
    a \<leftarrow> nao_new TYPE('b cl_list) ni;
    Mreturn (ni, a, signed_nat 0)
  }\<close>

lemma hs_empty_rule[vcg_rules]:
  \<open>llvm_htriple
    (\<upharpoonleft>snat.assn n ni)
    (hs_empty ni)
    (\<lambda>p. \<upharpoonleft>hs_assn (lshs_op_set_empty n) p)\<close>
  unfolding hs_empty_def hs_assn_def lshs_op_set_empty_def
  supply [vcg_rules] = nao_new_init_rl[OF hs_bucket_init]
  apply vcg_monadify
  by vcg

lemma hs_empty_hnr[sepref_fr_rules]:
  \<open>(hs_empty, (RETURN o lshs_op_set_empty))
  \<in> [\<lambda>n. 0 < n]\<^sub>a (snat_assn' TYPE(64))\<^sup>k \<rightarrow> \<upharpoonleft>hs_assn\<close>
  unfolding snat_rel_def snat.assn_is_rel[symmetric]
  by (sepref_to_hoare; vcg)

(* We can not register against high level `op_set_empty_refine` *)
(* Without resizing implemented, I think it might be better to use the explicit lshs_op_set_empty then *)
(* lemmas hs_empty_hnr = hs_empty_hnr[FCOMP lshs_op_set_empty_refine] *)

(* Instantiate Hashset with 2^14 elements (not sure if that number makes sense)*)
lemma hs_empty_fref_2pow14:
  \<open>(uncurry0 (RETURN (lshs_op_set_empty 16384)), uncurry0 (RETURN op_set_empty))
  \<in> unit_rel \<rightarrow>\<^sub>f \<langle>lshs_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  using lshs_op_set_empty_refine[of 16384] by (auto simp: lshs_rel_def in_br_conv)

sepref_definition hs_empty_2pow14 [llvm_code] is "uncurry0 (RETURN (lshs_op_set_empty 16384))"
  :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a \<upharpoonleft>hs_assn"
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemmas hs_empty_2pow14_hnr[sepref_fr_rules] = hs_empty_2pow14.refine[FCOMP hs_empty_fref_2pow14]

subsection \<open>Insert\<close>

definition [llvm_code]: \<open>hs_bucket_of \<equiv> \<lambda>ii (ni, ai, li). doM {
    hi \<leftarrow> ahash_impl ii;
    hi \<leftarrow> ll_urem hi ni;
    Mreturn hi
  }\<close>

lemma hs_bucket_of_rule[vcg_rules]:
  \<open>llvm_htriple
    (A i ii ** \<upharpoonleft>hs_assn (xs,l) (ni, ai, li) ** \<up>(xs \<noteq> []))
    (hs_bucket_of ii (ni, ai, li))
  (\<lambda>r. A i ii ** \<upharpoonleft>hs_assn (xs,l) (ni, ai, li) **
  \<upharpoonleft>snat.assn (lshs_bucket_of (length xs) i) r)\<close>
  unfolding hs_bucket_of_def
  supply [simp] = hs_assn_conv lshs_bucket_of_def pure_app_eq
  supply [vcg_rules] = ll_urem_hash_snat_rule
  by vcg

definition [llvm_code]: \<open>hs_insert \<equiv> \<lambda>ai (ni, xsi, li). doM {
    hi \<leftarrow> hs_bucket_of ai (ni, xsi, li);
    bi \<leftarrow> nao_nth xsi hi;
    bi \<leftarrow> cl_prepend ai bi;
    xsi \<leftarrow> nao_upd xsi hi bi;
    li \<leftarrow> sat_inc li;
    Mreturn (ni, xsi, li)
  }\<close>

lemma hs_insrt_rule[vcg_rules]:
  \<open>llvm_htriple
    (A a ai ** \<upharpoonleft>hs_assn (xs,l) (ni, xsi, li) ** \<up>(xs\<noteq>[]))
    (hs_insert ai (ni, xsi, li))
    (\<lambda>r. \<upharpoonleft>hs_assn (lshs_op_set_insert a (xs,l)) r)
  \<close>
  unfolding hs_insert_def
  supply [simp] = hs_assn_conv lshs_op_set_insert_def pure_app_eq
  supply [vcg_rules] = hs_bucket_of_rule[unfolded hs_assn_conv]
    cl_prepend_rule[unfolded cl_assn'_def]
  by vcg

lemma hs_insert_hnr:
  \<open>(uncurry hs_insert, uncurry (RETURN oo lshs_op_set_insert))
  \<in> [\<lambda>(a, (xs,l)). xs \<noteq> []]\<^sub>a A\<^sup>d *\<^sub>a \<upharpoonleft>hs_assn\<^sup>d \<rightarrow> \<upharpoonleft>hs_assn\<close>
  by (sepref_to_hoare; vcg)

sepref_register lshs_op_set_insert
lemma hs_insert_hnr_pr[sepref_fr_rules]:
  \<open>(uncurry hs_insert, uncurry (RETURN oo PR_CONST lshs_op_set_insert))
  \<in> [\<lambda>(a, (xs,l)). xs \<noteq> []]\<^sub>a A\<^sup>d *\<^sub>a \<upharpoonleft>hs_assn\<^sup>d \<rightarrow> \<upharpoonleft>hs_assn\<close>
  unfolding PR_CONST_def by (rule hs_insert_hnr)

subsection \<open>Resizing\<close>

lemma hs_insert_rule_gen:
  \<open>llvm_htriple
    (A a ai ** \<upharpoonleft>hs_assn hs s ** \<up>(fst hs \<noteq> []))
    (hs_insert ai s)
    (\<lambda>r. \<upharpoonleft>hs_assn (lshs_op_set_insert a hs) r)\<close>
proof -
  obtain xs l where H: \<open>hs = (xs,l)\<close> by (cases hs)
  obtain ni xsi li where C: \<open>s = (ni,xsi,li)\<close> by (cases s)
  show ?thesis unfolding H C fst_conv by vcg
qed

lemma lshs_op_set_insert_fst_ne[simp]: \<open>fst (lshs_op_set_insert a hs) \<noteq> [] \<longleftrightarrow> fst hs \<noteq> []\<close>
  by (cases hs) (simp add: lshs_op_set_insert_def)

lemma lshs_fold_insert_fst_ne[simp]: \<open>fst (fold lshs_op_set_insert ys hs) \<noteq> [] \<longleftrightarrow> fst hs \<noteq> []\<close>
  by (induction ys arbitrary: hs) auto

lemma lshs_op_set_empty_fst_ne[simp]: \<open>fst (lshs_op_set_empty n) \<noteq> [] \<longleftrightarrow> 0 < n\<close>
  by (simp add: lshs_op_set_empty_def)

text \<open>Drain one bucket into a hash-set. The bucket's nodes are freed on the way.\<close>

definition hs_insert_bucket :: \<open>'b cl_list \<times> 'b hs_conc \<Rightarrow> 'b hs_conc llM\<close> where [llvm_code]:
  \<open>hs_insert_bucket \<equiv> MMonad.REC (\<lambda>ff (bi, s).
    if bi = null then Mreturn s
    else doM {
      n \<leftarrow> ll_load bi;
      ll_free bi;
      s \<leftarrow> hs_insert (node.val n) s;
      ff (node.next n, s)
    })\<close>

lemmas hs_insert_bucket_unfold = REC_unfold_extr[OF hs_insert_bucket_def, discharge_monos]

lemma hs_insert_bucket_rule[vcg_rules]:
  \<open>llvm_htriple
    (cl_assn' A b bi ** \<upharpoonleft>hs_assn hs s ** \<up>(fst hs \<noteq> []))
    (hs_insert_bucket (bi, s))
    (\<lambda>r. \<upharpoonleft>hs_assn (fold lshs_op_set_insert b hs) r)\<close>
proof (induction b arbitrary: bi hs s)
  case Nil
  show ?case
    apply (rewrite hs_insert_bucket_unfold)
    supply [simp] = cl_assn_simps
    by vcg
next
  case (Cons a b)
  note [vcg_rules] = Cons.IH hs_insert_rule_gen
  show ?case
    apply (rewrite hs_insert_bucket_unfold)
    supply [simp] = cl_assn_simps sep_conj_exists
    by vcg
qed

definition hs_resize :: \<open>64 word \<Rightarrow> 'b hs_conc \<Rightarrow> 'b hs_conc llM\<close>
  where [llvm_code]: \<open>hs_resize \<equiv> \<lambda>nni (ni, ai, li). doM {
    s \<leftarrow> hs_empty nni;
    (_, s) \<leftarrow> llc_while
      (\<lambda>(ii, s). ll_icmp_ult ii ni)
      (\<lambda>(ii, s). doM {
        bi \<leftarrow> nao_nth ai ii;
        s \<leftarrow> hs_insert_bucket (bi, s);
        ii \<leftarrow> ll_add ii (signed_nat 1);
        Mreturn (ii, s)
      })
      (signed_nat 0, s);
    nao_open ai;
    narray_free ai;
    Mreturn s
  }\<close>

lemma hs_resize_rule[vcg_rules]:
  \<open>llvm_htriple
    (\<upharpoonleft>snat.assn nn nni ** \<upharpoonleft>hs_assn (xs,l) (ni, ai, li) ** \<up>(0 < nn))
    (hs_resize nni (ni, ai, li))
    (\<lambda>r. \<upharpoonleft>hs_assn (lshs_op_set_resize nn (xs,l)) r)\<close>
  unfolding hs_resize_def hs_assn_conv lshs_op_set_resize_def
  apply (rewrite annotate_llc_while[where
    I=\<open>\<lambda>(ii, s) t. EXS f i. \<upharpoonleft>snat.assn i ii
        ** \<upharpoonleft>(Array_of_Array_List.nao_assn (cl_assn A) (iseg_map i f)) xs ai
        ** \<up>(i \<le> length xs)
        ** \<upharpoonleft>hs_assn (fold lshs_op_set_insert (concat (take i xs)) (lshs_op_set_empty nn)) s
        ** \<up>\<^sub>!(t = length xs - i)\<close>
    and R=\<open>less_than\<close>])
  supply [simp] = iseg_map_upd_end_eq
  supply [vcg_rules] = hs_insert_bucket_rule[unfolded cl_assn'_def]
  apply vcg_monadify
  by vcg

lemma hs_resize_hnr:
  \<open>(uncurry hs_resize, uncurry (RETURN oo lshs_op_set_resize))
  \<in> [\<lambda>(n, (xs,l)). 0 < n]\<^sub>a (snat_assn' TYPE(64))\<^sup>k *\<^sub>a \<upharpoonleft>hs_assn\<^sup>d \<rightarrow> \<upharpoonleft>hs_assn\<close>
  unfolding snat_rel_def snat.assn_is_rel[symmetric]
  by (sepref_to_hoare; vcg)

sepref_register lshs_op_set_resize

lemma hs_resize_hnr_pr[sepref_fr_rules]:
  \<open>(uncurry hs_resize, uncurry (RETURN oo PR_CONST lshs_op_set_resize))
  \<in> [\<lambda>(n, (xs,l)). 0 < n]\<^sub>a (snat_assn' TYPE(64))\<^sup>k *\<^sub>a \<upharpoonleft>hs_assn\<^sup>d \<rightarrow> \<upharpoonleft>hs_assn\<close>
  unfolding PR_CONST_def by (rule hs_resize_hnr)

subsection \<open>Size and counter access\<close>

definition \<open>lshs_size \<equiv> \<lambda>(xs, l). length xs\<close>
definition \<open>lshs_count_sat \<equiv> \<lambda>(xs, l). min l sat_max_count\<close>

definition hs_size :: \<open>'b hs_conc \<Rightarrow> 64 word llM\<close> where [llvm_code, llvm_inline]:
  \<open>hs_size \<equiv> \<lambda>(ni, ai, li). Mreturn ni\<close>
definition hs_count :: \<open>'b hs_conc \<Rightarrow> 64 word llM\<close> where [llvm_code, llvm_inline]:
  \<open>hs_count \<equiv> \<lambda>(ni, ai, li). Mreturn li\<close>

lemma hs_size_rule[vcg_rules]:
  \<open>llvm_htriple
    (\<upharpoonleft>hs_assn (xs,l) (ni, ai, li))
    (hs_size (ni, ai, li))
    (\<lambda>r. \<upharpoonleft>hs_assn (xs,l) (ni, ai, li) ** \<upharpoonleft>snat.assn (lshs_size (xs,l)) r)\<close>
  unfolding hs_size_def lshs_size_def
  supply [simp] = hs_assn_conv
  by vcg

lemma hs_count_rule[vcg_rules]:
  \<open>llvm_htriple
    (\<upharpoonleft>hs_assn (xs,l) (ni, ai, li))
    (hs_count (ni, ai, li))
    (\<lambda>r. \<upharpoonleft>hs_assn (xs,l) (ni, ai, li) ** \<upharpoonleft>snat.assn (lshs_count_sat (xs,l)) r)\<close>
  unfolding hs_count_def lshs_count_sat_def
  supply [simp] = hs_assn_conv
  by vcg

sepref_register lshs_size lshs_count_sat

lemma hs_size_hnr[sepref_fr_rules]:
  \<open>(hs_size, RETURN o lshs_size) \<in> \<upharpoonleft>hs_assn\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(64)\<close>
  unfolding snat_rel_def snat.assn_is_rel[symmetric]
  by (sepref_to_hoare; vcg)

lemma hs_count_hnr[sepref_fr_rules]:
  \<open>(hs_count, RETURN o lshs_count_sat) \<in> \<upharpoonleft>hs_assn\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(64)\<close>
  unfolding snat_rel_def snat.assn_is_rel[symmetric]
  by (sepref_to_hoare; vcg)

section \<open>Inserting with resizing\<close>
text \<open>With insertion and resizing both in place, we combine the two to obtain a
  "proper" hashset implementation with automatic resizing.\<close>

text \<open>Insert, then grow the table when the element counter reached the bucket count
  and growing is still possible. The trigger condition is irrelevant for correctness
  (resizing is the identity on the abstract set), so it is chosen to be cheap to implement.\<close>

definition \<open>lshs_op_set_insert_resize a s \<equiv>
  let s = lshs_op_set_insert a s;
      n = lshs_size s;
      n' = ht_grow n
  in if n \<le> lshs_count_sat s \<and> n < n' then lshs_op_set_resize n' s else s\<close>

sepref_register lshs_op_set_insert_resize

sepref_def lshs_op_set_insert_resize_impl is \<open>uncurry (RETURN oo PR_CONST lshs_op_set_insert_resize)\<close>
  :: \<open>[\<lambda>(a, s). fst s \<noteq> []]\<^sub>a A\<^sup>d *\<^sub>a \<upharpoonleft>hs_assn\<^sup>d \<rightarrow> \<upharpoonleft>hs_assn\<close>
  unfolding lshs_op_set_insert_resize_def PR_CONST_def
  by sepref

lemma lshs_op_set_insert_resize_refine:
  \<open>(uncurry (RETURN oo lshs_op_set_insert_resize), uncurry (RETURN oo op_set_insert))
  \<in> Id \<times>\<^sub>r lshs_rel \<rightarrow>\<^sub>f \<langle>lshs_rel\<rangle>nres_rel\<close>
proof (intro frefI nres_relI, clarsimp simp: lshs_rel_def in_br_conv)
  fix a hs
  assume I: \<open>lshs_invar hs\<close>
  let ?s = \<open>lshs_op_set_insert a hs\<close>
  obtain xs l where S: \<open>?s = (xs, l)\<close> by (cases ?s)
  have IS: \<open>lshs_invar ?s\<close> and AS: \<open>lshs_\<alpha> ?s = insert a (lshs_\<alpha> hs)\<close>
    using lshs_op_set_insert_step[OF I] by simp_all
  show \<open>insert a (lshs_\<alpha> hs) = lshs_\<alpha> (lshs_op_set_insert_resize a hs) \<and>
        lshs_invar (lshs_op_set_insert_resize a hs)\<close>
    unfolding lshs_op_set_insert_resize_def Let_def
    using IS AS lshs_op_set_resize_refine[of \<open>ht_grow (lshs_size ?s)\<close> xs l]
    by (auto simp: S)
qed

lemmas [fcomp_prenorm_simps] = lshs_rel_def in_br_conv lshs_invar_def

lemmas hs_insert_resize_hnr[sepref_fr_rules] =
  lshs_op_set_insert_resize_impl.refine[unfolded PR_CONST_def, FCOMP lshs_op_set_insert_resize_refine]

section \<open>@{term op_set_member}\<close>

definition [llvm_code]: \<open>hs_member \<equiv> \<lambda>ai (ni, xsi, li). doM{
    hi \<leftarrow> hs_bucket_of ai (ni, xsi, li);
    bi \<leftarrow> nao_nth xsi hi;
    r \<leftarrow> cl_contains ai bi;
    nao_rejoin xsi hi;
    Mreturn r
  }\<close>

lemma hs_member_rule[vcg_rules]:
  \<open>llvm_htriple
  (A a ai ** \<upharpoonleft>hs_assn (xs,l) (ni, xsi, li) ** \<up>(xs\<noteq>[]))
  (hs_member ai (ni, xsi, li))
  (\<lambda>r. A a ai ** \<upharpoonleft>hs_assn (xs,l) (ni, xsi, li) ** bool1_assn (lshs_op_set_member a (xs,l)) r)
  \<close>
  unfolding hs_member_def lshs_op_set_member_def bool1_rel_def
    pure_def
  supply [simp] = hs_assn_conv bool.assn_def bool.rel_def in_br_conv
  supply [vcg_rules] = hs_bucket_of_rule[unfolded hs_assn_conv]
    cl_contains_rule[unfolded cl_assn'_def]
  by vcg

lemma hs_member_hnr:
  \<open>(uncurry hs_member, uncurry (RETURN oo lshs_op_set_member))
  \<in> [\<lambda>(a, (xs,l)). xs \<noteq> []]\<^sub>a A\<^sup>k *\<^sub>a \<upharpoonleft>hs_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  supply [simp] = bool1_rel_def pure_def
  by (sepref_to_hoare; vcg)

lemmas hs_member_hnr2[sepref_fr_rules] =
  hs_member_hnr[FCOMP lshs_op_set_member_refine]

abbreviation \<open>hs_assn' \<equiv> hr_comp \<upharpoonleft>hs_assn lshs_rel\<close>

end

end
