theory IICF_HashMap
  imports IICF_PartialMap IICF_HashSet Isabelle_LLVM.Proto_EOArray
begin

text \<open>Hashmap implementation, based on the existing {IICF_PartialMap} and the Hashable interface.
  We reuse the bucket implementation from {IICF_HashSet}.\<close>

text \<open>TODO list \<emdash> coverage of the @{theory Isabelle_LLVM.IICF_Map} interface
  \<^item> [x] \<open>op_map_empty\<close> (\<open>lshm_empty\<close>, parametric in the initial number of buckets)
  \<^item> [x] \<open>op_map_update\<close>
  \<^item> [x] \<open>op_map_delete\<close>
  \<^item> [x] \<open>op_map_contains_key\<close>
  \<^item> [ ] \<open>op_map_is_empty\<close> - Expensive without length in cl_list...
  \<^item> [x] \<open>op_map_lookup\<close>
  \<^item> [ ] \<open>op_map_the_lookup\<close>

  Infrastructure (not interface ops):
  \<^item> [x] \<open>MK_FREE\<close> bucket entry free (\<open>bucket_free_rule\<close>)
  \<^item> [ ] \<open>MK_FREE\<close> deep free of the whole map
\<close>

type_synonym ('k, 'v) hashmap = \<open>('k \<times> 'v) list list\<close>

locale hashmap_env =
  key: freeable_assn K kfree +
  val: copyable_assn V vfree vcopy +
  eq_assn K keq + hashable_assn K khash khash_impl
  for K :: \<open>'k \<Rightarrow> 'ki::llvm_rep \<Rightarrow> assn\<close>
  and kfree :: \<open>'ki \<Rightarrow> unit llM\<close>
  and V :: \<open>'v \<Rightarrow> 'vi::llvm_rep \<Rightarrow> assn\<close>
  and vfree :: \<open>'vi \<Rightarrow> unit llM\<close>
  and vcopy :: \<open>'vi \<Rightarrow> 'vi llM\<close>
  and keq :: \<open>'ki \<Rightarrow> 'ki \<Rightarrow> 1 word llM\<close>
  and khash :: \<open>'k \<Rightarrow> 64 word\<close>
  and khash_impl :: \<open>'ki \<Rightarrow> 64 word llM\<close>
begin

definition vopt_assn :: \<open>'v option \<Rightarrow> 'vi ptr \<Rightarrow> assn\<close> where
  \<open>vopt_assn w p \<equiv> case w of None \<Rightarrow> \<up>(p = null) | Some v \<Rightarrow> \<upharpoonleft>(box_assn V) v p\<close>

lemma vopt_assn_simps[simp]:
  \<open>vopt_assn None p = \<up>(p = null)\<close>
  \<open>vopt_assn (Some v) p = \<upharpoonleft>(box_assn V) v p\<close>
  unfolding vopt_assn_def by simp_all

text \<open>A bucket entry keeps the key inline in the node \<emdash> probing needs no indirection \<emdash>
  and boxes only the value.\<close>
abbreviation \<open>boxed_bucket_assn \<equiv> K \<times>\<^sub>a (\<lambda>v. vopt_assn (Some v))\<close>
abbreviation \<open>boxed_buckets_assn \<equiv> cl_assn' boxed_bucket_assn\<close>

definition bucket_free where [llvm_code, llvm_inline]:
  \<open>bucket_free \<equiv> \<lambda>(ki,bv). doM {kfree ki; box_free vfree bv}\<close>

lemma bucket_free_rule[sepref_frame_free_rules]: \<open>MK_FREE boxed_bucket_assn bucket_free\<close>
  supply [vcg_rules] = MK_FREED[OF box_free_rule[OF val.afree_free]]
  unfolding bucket_free_def
  apply (rule MK_FREEI)
  by vcg

interpretation bucket: freeable_assn boxed_bucket_assn bucket_free
  by unfold_locales (rule bucket_free_rule)

term bucket.cl_free

section \<open>High-level Hashmap by nested lists.\<close>
text \<open>Like in IICF_Partial_Map, we first use abstract nested lists which we then refine down
  to llM level.\<close>

definition \<open>lshm_bucket_of n k \<equiv> unat (khash k) mod n\<close>
definition lshm_invar :: \<open>('k, 'v) hashmap \<Rightarrow> bool\<close> where
  \<open>lshm_invar xs \<equiv> xs\<noteq>[] \<and> (\<forall>i < length xs.
  (distinct (map fst (xs!i))) \<and> (\<forall>(k,v) \<in> set (xs!i). lshm_bucket_of (length xs) k = i))\<close>
definition lshm_\<alpha> :: \<open>('k, 'v) hashmap \<Rightarrow> 'k \<Rightarrow> 'v option\<close> where
  \<open>lshm_\<alpha> xs k \<equiv> map_of (xs ! lshm_bucket_of (length xs) k) k\<close>
definition \<open>lshm_rel \<equiv> br lshm_\<alpha> lshm_invar\<close>

subsection \<open>High Level Implementation\<close>

definition \<open>lshm_op_map_empty n \<equiv> replicate n ([] :: ('k \<times> 'v) list)\<close>

term op_map_update
fun lshm_bucket_update :: \<open>'k \<Rightarrow> 'v \<Rightarrow> ('k \<times> 'v) list \<Rightarrow> ('k \<times> 'v) list\<close> where
  \<open>lshm_bucket_update k v [] = [(k, v)]\<close>
| \<open>lshm_bucket_update k v ((kc, vc) # xs) =
  (if k = kc then (k, v) # xs else (kc, vc) # lshm_bucket_update k v xs)\<close> 
definition \<open>lshm_op_map_update k v xs \<equiv>
  let bi = lshm_bucket_of (length xs) k in xs[bi:=lshm_bucket_update k v (xs!bi)]\<close>

term op_map_delete
fun lshm_bucket_delete :: \<open>'k \<Rightarrow> ('k \<times> 'v) list \<Rightarrow> ('k \<times> 'v) list\<close> where
  \<open>lshm_bucket_delete _ [] = []\<close>
| \<open>lshm_bucket_delete k ((ki, vi) # xs) =
  (if k = ki then xs else (ki, vi) # lshm_bucket_delete k xs)\<close>
definition \<open>lshm_op_map_delete k xs \<equiv>
  let bi = lshm_bucket_of (length xs) k in xs[bi:=lshm_bucket_delete k (xs!bi)]\<close>

fun lshm_bucket_contains :: \<open>'k \<Rightarrow> ('k \<times> 'v) list \<Rightarrow> bool\<close> where
  \<open>lshm_bucket_contains _ [] = False\<close>
| \<open>lshm_bucket_contains k ((ki, _) # xs) = (if k = ki then True else lshm_bucket_contains k xs)\<close>
definition \<open>lshm_op_map_contains_key k xs \<equiv>
  let bi = lshm_bucket_of (length xs) k in lshm_bucket_contains k (xs!bi)\<close>

fun lshm_bucket_lookup :: \<open>'k \<Rightarrow> ('k \<times> 'v) list \<Rightarrow> 'v option\<close> where
  \<open>lshm_bucket_lookup _ [] = None\<close>
| \<open>lshm_bucket_lookup k ((ki, vi) # xs) = (if k = ki then Some vi else lshm_bucket_lookup k xs)\<close>
definition \<open>lshm_op_map_lookup k xs \<equiv>
  let bi = lshm_bucket_of (length xs) k in lshm_bucket_lookup k (xs!bi)\<close>

term op_map_the_lookup
fun lshm_bucket_the_lookup :: \<open>'k \<Rightarrow> ('k \<times> 'v) list \<Rightarrow> 'v\<close> where
  \<open>lshm_bucket_the_lookup _ [] = undefined\<close>
| \<open>lshm_bucket_the_lookup k ((ki, vi) # xs) = (if k = ki then vi else lshm_bucket_the_lookup k xs)\<close>
definition \<open>lshm_the_lookup k xs \<equiv>
  let bi = lshm_bucket_of (length xs) k in lshm_bucket_the_lookup k (xs!bi)\<close>

lemma lshm_empty_fref:
  assumes \<open>0 < n\<close>
  shows \<open>(lshm_op_map_empty n, op_map_empty) \<in> lshm_rel\<close>
  unfolding lshm_rel_def lshm_\<alpha>_def lshm_bucket_of_def in_br_conv
    lshm_op_map_empty_def op_map_empty_def lshm_invar_def
  using assms by auto

lemma lshm_bucket_update_map_of:
  \<open>map_of (lshm_bucket_update k v b) = (map_of b)(k \<mapsto> v)\<close>
  by (induction b rule: lshm_bucket_update.induct) auto

lemma lshm_bucket_update_keys:
  \<open>fst ` set (lshm_bucket_update k v b) = insert k (fst ` set b)\<close>
  by (induction b rule: lshm_bucket_update.induct) auto

lemma lshm_bucket_update_distinct:
  \<open>distinct (map fst b) \<Longrightarrow> distinct (map fst (lshm_bucket_update k v b))\<close>
  by (induction b rule: lshm_bucket_update.induct) (auto simp: lshm_bucket_update_keys)

lemma lshm_bucket_update_set:
  \<open>set (lshm_bucket_update k v b) \<subseteq> insert (k, v) (set b)\<close>
  by (induction b rule: lshm_bucket_update.induct) auto

lemma lshm_update_\<alpha>:
  assumes I: \<open>lshm_invar xs\<close>
  shows \<open>lshm_\<alpha> (lshm_op_map_update k v xs) = (lshm_\<alpha> xs)(k \<mapsto> v)\<close>
proof (rule ext)
  fix k'
  from I have [simp]: \<open>0 < length xs\<close> unfolding lshm_invar_def by (cases xs) auto
  show \<open>lshm_\<alpha> (lshm_op_map_update k v xs) k' = ((lshm_\<alpha> xs)(k \<mapsto> v)) k'\<close>
  proof (cases \<open>lshm_bucket_of (length xs) k' = lshm_bucket_of (length xs) k\<close>)
    case True
    then show ?thesis
      apply (auto simp: lshm_\<alpha>_def lshm_op_map_update_def Let_def lshm_bucket_of_def
        lshm_bucket_update_map_of)
      using \<open>0 < length xs\<close> lshm_bucket_update_map_of apply auto[1]
      using \<open>0 < length xs\<close> lshm_bucket_update_map_of by auto
  next
    case False
    then have \<open>k' \<noteq> k\<close> by auto
    with False show ?thesis
      by (auto simp: lshm_\<alpha>_def lshm_op_map_update_def Let_def lshm_bucket_of_def)
  qed
qed

lemma lshm_update_invar:
  assumes \<open>lshm_invar xs\<close>
  shows \<open>lshm_invar (lshm_op_map_update k v xs)\<close>
  using assms
  unfolding lshm_invar_def lshm_op_map_update_def Let_def
  apply (auto simp: nth_list_update lshm_bucket_update_distinct
    dest!: set_mp[OF lshm_bucket_update_set])
  apply (simp add: lshm_bucket_update_distinct nth_list_update')
  by (smt (verit) case_prod_conv lshm_bucket_update_distinct
    lshm_bucket_update_map_of map_of_eq_Some_iff map_upd_Some_unfold
    nth_list_update_eq nth_list_update_neq)

lemma lshm_update_fref:
  \<open>(uncurry2 (RETURN ooo lshm_op_map_update), uncurry2 (RETURN ooo op_map_update))
  \<in> Id \<times>\<^sub>r lshm_rel \<rightarrow>\<^sub>f \<langle>lshm_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: lshm_rel_def in_br_conv lshm_update_\<alpha> lshm_update_invar)

lemma lshm_bucket_of_bound[simp]: \<open>0 < n \<Longrightarrow> lshm_bucket_of n k < n\<close>
  by (simp add: lshm_bucket_of_def)

lemma lshm_bucket_delete_map_of:
  \<open>distinct (map fst b) \<Longrightarrow> map_of (lshm_bucket_delete k b) = (map_of b)(k := None)\<close>
  apply (induction b rule: lshm_bucket_delete.induct)
  subgoal by auto
  subgoal by (auto simp: fun_upd_twist map_of_eq_None_iff)
  done

lemma lshm_bucket_delete_set: \<open>set (lshm_bucket_delete k b) \<subseteq> set b\<close>
  by (induction b rule: lshm_bucket_delete.induct) auto

lemma lshm_bucket_delete_keys: \<open>fst ` set (lshm_bucket_delete k b) \<subseteq> fst ` set b\<close>
  using lshm_bucket_delete_set by (rule image_mono)

lemma lshm_bucket_delete_distinct:
  \<open>distinct (map fst b) \<Longrightarrow> distinct (map fst (lshm_bucket_delete k b))\<close>
  by (induction b rule: lshm_bucket_delete.induct)
    (auto dest!: set_mp[OF lshm_bucket_delete_keys])

lemma lshm_delete_\<alpha>:
  assumes I: \<open>lshm_invar xs\<close>
  shows \<open>lshm_\<alpha> (lshm_op_map_delete k xs) = (lshm_\<alpha> xs)(k := None)\<close>
proof (rule ext)
  fix k'
  from I have [simp]: \<open>0 < length xs\<close> unfolding lshm_invar_def by (cases xs) auto
  from I have D: \<open>distinct (map fst (xs ! lshm_bucket_of (length xs) k))\<close>
    unfolding lshm_invar_def by auto
  show \<open>lshm_\<alpha> (lshm_op_map_delete k xs) k' = ((lshm_\<alpha> xs)(k := None)) k'\<close>
  proof (cases \<open>lshm_bucket_of (length xs) k' = lshm_bucket_of (length xs) k\<close>)
    case True
    with D show ?thesis
      apply (auto simp: lshm_\<alpha>_def lshm_op_map_delete_def Let_def lshm_bucket_delete_map_of)
      subgoal using \<open>0 < length xs\<close> lshm_bucket_delete_map_of by fastforce
      using \<open>0 < length xs\<close> lshm_bucket_delete_map_of by auto
  next
    case False
    then have \<open>k' \<noteq> k\<close> by auto
    with False show ?thesis
      by (auto simp: lshm_\<alpha>_def lshm_op_map_delete_def Let_def)
  qed
qed

lemma lshm_delete_invar:
  assumes \<open>lshm_invar xs\<close>
  shows \<open>lshm_invar (lshm_op_map_delete k xs)\<close>
  using assms
  unfolding lshm_invar_def lshm_op_map_delete_def Let_def
  apply (auto simp: nth_list_update lshm_bucket_delete_distinct
    dest!: set_mp[OF lshm_bucket_delete_set])
  by (metis (mono_tags, lifting) case_prod_conv length_greater_0_conv
    lshm_bucket_of_bound)

lemma lshm_delete_fref:
  \<open>(uncurry (RETURN oo lshm_op_map_delete), uncurry (RETURN oo op_map_delete))
    \<in> Id \<times>\<^sub>r lshm_rel \<rightarrow>\<^sub>f \<langle>lshm_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: lshm_rel_def in_br_conv lshm_delete_\<alpha> lshm_delete_invar)

lemma lshm_bucket_lookup_map_of[simp]:
  \<open>lshm_bucket_lookup k b = map_of b k\<close>
  by (induction b rule: lshm_bucket_lookup.induct) auto

lemma lshm_bucket_contains_map_of[simp]:
  \<open>lshm_bucket_contains k b \<longleftrightarrow> map_of b k \<noteq> None\<close>
  by (induction b rule: lshm_bucket_contains.induct) auto

lemma lshm_bucket_the_lookup_map_of:
  \<open>map_of b k \<noteq> None \<Longrightarrow> lshm_bucket_the_lookup k b = the (map_of b k)\<close>
  by (induction b rule: lshm_bucket_the_lookup.induct) (auto split: if_splits)

lemma lshm_lookup_\<alpha>: \<open>lshm_op_map_lookup k xs = lshm_\<alpha> xs k\<close>
  by (simp add: lshm_op_map_lookup_def lshm_\<alpha>_def Let_def)

lemma lshm_lookup_fref:
  \<open>(uncurry (RETURN oo lshm_op_map_lookup), uncurry (RETURN oo op_map_lookup))
    \<in> Id \<times>\<^sub>r lshm_rel \<rightarrow>\<^sub>f \<langle>\<langle>Id\<rangle>option_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: lshm_rel_def in_br_conv lshm_lookup_\<alpha>)

lemma lshm_contains_key_\<alpha>: \<open>lshm_op_map_contains_key k xs \<longleftrightarrow> lshm_\<alpha> xs k \<noteq> None\<close>
  by (simp add: lshm_op_map_contains_key_def lshm_\<alpha>_def Let_def)

lemma lshm_contains_key_fref:
  \<open>(uncurry (RETURN oo lshm_op_map_contains_key), uncurry (RETURN oo op_map_contains_key))
    \<in> Id \<times>\<^sub>r lshm_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: lshm_rel_def in_br_conv lshm_contains_key_\<alpha> dom_def)

lemma lshm_the_lookup_\<alpha>:
  \<open>lshm_\<alpha> xs k \<noteq> None \<Longrightarrow> lshm_the_lookup k xs = the (lshm_\<alpha> xs k)\<close>
  by (simp add: lshm_the_lookup_def lshm_\<alpha>_def Let_def lshm_bucket_the_lookup_map_of)

lemma lshm_the_lookup_fref:
  \<open>(uncurry (RETURN oo lshm_the_lookup), uncurry (RETURN oo op_map_the_lookup))
    \<in> [\<lambda>(k,m). m k \<noteq> None]\<^sub>f Id \<times>\<^sub>r lshm_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: lshm_rel_def in_br_conv lshm_the_lookup_\<alpha>)

section \<open>Bucket-level Implemenations\<close>
sepref_register "unat :: _ word \<Rightarrow> nat"
lemma unat_word_refine[sepref_import_param]:
  \<open>(id, unat) \<in> word_rel \<rightarrow> unat_rel' TYPE('a::len)\<close>
  by (auto simp: unat_rel_def unat.rel_def in_br_conv)

lemma lshm_bucket_of_alt:
  \<open>lshm_bucket_of n k = op_unat_snat_conv (unat (khash k) mod op_snat_unat_conv n)\<close>
  unfolding lshm_bucket_of_def by simp

lemma mod_lt_boundI: \<open>0 < n \<Longrightarrow> n \<le> N \<Longrightarrow> (m::nat) mod n < N\<close>
  by (meson mod_less_divisor less_le_trans)

sepref_register khash lshm_bucket_of
sepref_def lshm_bucket_of_impl is \<open>uncurry (RETURN oo PR_CONST lshm_bucket_of)\<close>
  :: \<open>[\<lambda>(n,_). 0 < n]\<^sub>a (snat_assn' TYPE(64))\<^sup>k *\<^sub>a K\<^sup>k \<rightarrow> (snat_assn' TYPE(64))\<close>
  unfolding PR_CONST_def lshm_bucket_of_alt
  supply mod_lt_boundI[intro]
  by sepref

lemma box_assn_expand: \<open>\<upharpoonleft>(box_assn A) x p = (EXS c. \<upharpoonleft>ll_bpto c p ** A x c)\<close>
  unfolding box_assn_def by simp

subsection \<open>Bucket update\<close>

definition lshm_bucket_update_impl
  :: \<open>'ki \<Rightarrow> 'vi \<Rightarrow> ('ki \<times> 'vi ptr) cl_list \<Rightarrow> ('ki \<times> 'vi ptr) cl_list llM\<close>
  where [llvm_code]:
  \<open>lshm_bucket_update_impl ki vi \<equiv> MMonad.REC (\<lambda>f p.
    if p = null then doM {
      bv \<leftarrow> ll_ref vi;
      ll_ref (Node (ki, bv) null)
    }
    else doM {
      n \<leftarrow> ll_load p;
      case node.val n of (kii, bv) \<Rightarrow> doM {
        eq \<leftarrow> keq ki kii;
        llc_if eq
          (doM {
            kfree ki; \<comment> \<open>the node keeps its key; the incoming one is freed\<close>
            ov \<leftarrow> ll_load bv;
            vfree ov;
            ll_store vi bv;
            Mreturn p
          })
          (doM {
            tl \<leftarrow> f (node.next n);
            ll_store (Node (kii, bv) tl) p;
            Mreturn p
          })
      }
    })\<close>

lemmas lshm_bucket_update_impl_unfold =
  REC_unfold_extr[OF lshm_bucket_update_impl_def, discharge_monos]

lemma lshm_bucket_update_rule[vcg_rules]: \<open>llvm_htriple
  (boxed_buckets_assn b bi ** K k ki ** V v vi)
  (lshm_bucket_update_impl ki vi bi)
  (\<lambda>r. boxed_buckets_assn (lshm_bucket_update k v b) r)\<close>
proof (induction b arbitrary: bi)
  case Nil
  show ?case
    apply (subst lshm_bucket_update_impl_unfold)
    supply [simp] = cl_assn_simps box_assn_expand prod_assn_pair_conv sep_conj_exists
    by vcg
next
  case (Cons e es)
  obtain kc vc where [simp]: \<open>e = (kc, vc)\<close> by (cases e)
  note [vcg_rules] = Cons.IH
  show ?case
    apply (subst lshm_bucket_update_impl_unfold)
    supply [simp] = cl_assn_simps box_assn_expand prod_assn_pair_conv sep_conj_exists
      bool.assn_def bool1_rel_def bool.rel_def in_br_conv pure_def from_bool_def
    by vcg
qed

sepref_register lshm_bucket_update
lemma lshm_bucket_update_hnr[sepref_fr_rules]:
  \<open>(uncurry2 lshm_bucket_update_impl, uncurry2 (RETURN ooo lshm_bucket_update))
    \<in> K\<^sup>d *\<^sub>a V\<^sup>d *\<^sub>a boxed_buckets_assn\<^sup>d \<rightarrow>\<^sub>a boxed_buckets_assn\<close>
  by (sepref_to_hoare; vcg)

subsection \<open>Bucket Delete\<close>

definition lshm_bucket_delete_impl
  :: \<open>'ki \<Rightarrow> ('ki \<times> 'vi ptr) cl_list \<Rightarrow> ('ki \<times> 'vi ptr) cl_list llM\<close>
  where [llvm_code]:
  \<open>lshm_bucket_delete_impl ki \<equiv> MMonad.REC (\<lambda> f p. doM {
    if p = null then Mreturn null
    else doM {
      n \<leftarrow> ll_load p;
      case node.val n of (kii, bv) \<Rightarrow> doM {
        eq \<leftarrow> keq ki kii;
        llc_if eq (doM {
          kfree kii;
          box_free vfree bv;
          ll_free p;
          Mreturn (node.next n)
        }) (doM {
          tl \<leftarrow> f (node.next n);
          ll_store (Node (kii, bv) tl) p;
          Mreturn p
        })
      }
    }
  })\<close>

lemmas lshm_bucket_delete_impl_unfold =
  REC_unfold_extr[OF lshm_bucket_delete_impl_def, discharge_monos]

lemma lshm_bucket_delete_rule[vcg_rules]: \<open>llvm_htriple
  (boxed_buckets_assn b bi ** K k ki)
  (lshm_bucket_delete_impl ki bi)
  (\<lambda>r. K k ki ** boxed_buckets_assn (lshm_bucket_delete k b) r)\<close>
proof (induction b arbitrary: bi)
  case Nil
  then show ?case
    apply (subst lshm_bucket_delete_impl_unfold)
    supply [simp] = cl_assn_simps sep_conj_exists Nil
    by vcg
next
  case (Cons e es)
  obtain kc vc where [simp]: \<open>e = (kc, vc)\<close> by (cases e)
  note [vcg_rules] = Cons.IH MK_FREED[OF box_free_rule[OF val.afree_free]]
  show ?case
    apply (subst lshm_bucket_delete_impl_unfold)
    supply [simp] = cl_assn_simps prod_assn_pair_conv sep_conj_exists
      bool.assn_def bool1_rel_def bool.rel_def in_br_conv pure_def from_bool_def
    by vcg
qed

sepref_register lshm_bucket_delete
lemma lshm_bucket_delete_hnr[sepref_fr_rules]:
  \<open>(uncurry lshm_bucket_delete_impl, uncurry (RETURN oo lshm_bucket_delete))
  \<in> K\<^sup>k *\<^sub>a boxed_buckets_assn\<^sup>d \<rightarrow>\<^sub>a boxed_buckets_assn\<close>
  by (sepref_to_hoare; vcg)

subsection \<open>Bucket Contains\<close>

definition \<open>lshm_bucket_contains_fold_inner x \<equiv> \<lambda>acc (k,v). acc \<or> (x = k)\<close> 

lemma lshm_bucket_contains_fold:
  \<open>lshm_bucket_contains k xs = foldl (lshm_bucket_contains_fold_inner k) False xs\<close>
  unfolding lshm_bucket_contains_fold_inner_def
  by (induction xs; auto simp: rev_induct)

definition lshm_bucket_contains_step where [llvm_code, llvm_inline]:
  \<open>lshm_bucket_contains_step ki \<equiv> \<lambda>acci (kii, bv). doM {
    eq \<leftarrow> keq ki kii;
    ll_or acci eq
  }\<close>

lemma lshm_bucket_contains_step_rule: \<open>llvm_htriple
  (K k ki ** bool1_assn a ai ** boxed_bucket_assn x xi)
  (lshm_bucket_contains_step ki ai xi)
  (\<lambda>r. K k ki ** bool1_assn (lshm_bucket_contains_fold_inner k a x) r ** boxed_bucket_assn x xi)\<close>
  unfolding lshm_bucket_contains_step_def lshm_bucket_contains_fold_inner_def
  apply (cases x; cases xi; simp only: prod_assn_pair_conv prod.case)
  supply [simp] = bool.assn_def bool1_rel_def bool.rel_def in_br_conv pure_def from_bool_def
  by vcg

text \<open>The step function must not capture \<open>ki\<close> (LLVM has no closures), so we use
  the lambda-lifted \<open>cl_fold_env\<close> that threads it through the recursion.\<close>
definition lshm_bucket_contains_impl :: \<open>'ki \<Rightarrow> ('ki \<times> 'vi ptr) cl_list \<Rightarrow> 1 word llM\<close>
  where [llvm_code]:
  \<open>lshm_bucket_contains_impl ki p \<equiv> cl_fold_env lshm_bucket_contains_step (ki, p, 0)\<close>

lemma lshm_bucket_contains_rule[vcg_rules]: \<open>llvm_htriple
  (boxed_buckets_assn b bi ** K k ki)
  (lshm_bucket_contains_impl ki bi)
  (\<lambda>r. boxed_buckets_assn b bi ** K k ki ** bool1_assn (lshm_bucket_contains k b) r)\<close>
  unfolding lshm_bucket_contains_impl_def lshm_bucket_contains_fold
  supply [vcg_rules] = cl_fold_env_rule[where P = K and R = bool1_assn
    and A = boxed_bucket_assn and f = lshm_bucket_contains_step
    and fa = lshm_bucket_contains_fold_inner
    and a = False, OF lshm_bucket_contains_step_rule]
  supply [simp] = bool1_rel_def bool.rel_def in_br_conv pure_def
  by vcg

sepref_register lshm_bucket_contains
lemma lshm_bucket_contains_hnr[sepref_fr_rules]:
  \<open>(uncurry lshm_bucket_contains_impl, uncurry (RETURN oo lshm_bucket_contains))
  \<in> K\<^sup>k *\<^sub>a boxed_buckets_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [simp] = bool1_rel_def bool.rel_def in_br_conv pure_def
  by (sepref_to_hoare; vcg)

subsection \<open>Bucket Lookup\<close>

definition lshm_bucket_lookup_impl
  :: \<open>'ki \<Rightarrow> ('ki \<times> 'vi ptr) cl_list \<Rightarrow> 'vi ptr llM\<close> where [llvm_code]:
  \<open>lshm_bucket_lookup_impl ki \<equiv> MMonad.REC (\<lambda>f p.
  if p = null then Mreturn null
  else doM {
    n \<leftarrow> ll_load p;
    case node.val n of (kii, bv) \<Rightarrow> doM {
      eq \<leftarrow> keq ki kii;
      llc_if eq (doM {
        ov \<leftarrow> ll_load bv;
        v \<leftarrow> vcopy ov;
        ll_ref v
      }) (f (node.next n))
    }
  })\<close>

lemmas lshm_bucket_lookup_impl_unfold =
  REC_unfold_extr[OF lshm_bucket_lookup_impl_def, discharge_monos]

lemma lshm_bucket_lookup_rule[vcg_rules]: \<open>llvm_htriple
  (boxed_buckets_assn b bi ** K k ki)
  (lshm_bucket_lookup_impl ki bi)
  (\<lambda>r. boxed_buckets_assn b bi ** K k ki ** vopt_assn (lshm_bucket_lookup k b) r)\<close>
proof (induction b arbitrary: bi)
  case Nil
  then show ?case
    apply (subst lshm_bucket_lookup_impl_unfold)
    supply [simp] = cl_assn_simps sep_conj_exists
    by vcg
next
  case (Cons e es)
  obtain kc vc where [simp]: \<open>e = (kc, vc)\<close> by (cases e)
  note [vcg_rules] = Cons.IH
  show ?case
    apply (subst lshm_bucket_lookup_impl_unfold)
    supply [simp] = cl_assn_simps box_assn_expand prod_assn_pair_conv sep_conj_exists
      bool.assn_def bool1_rel_def bool.rel_def in_br_conv pure_def from_bool_def
    by vcg
qed

sepref_register lshm_bucket_lookup
lemma lshm_bucket_lookup_hnr[sepref_fr_rules]:
  \<open>(uncurry lshm_bucket_lookup_impl, uncurry (RETURN oo lshm_bucket_lookup))
  \<in> K\<^sup>k *\<^sub>a boxed_buckets_assn\<^sup>k \<rightarrow>\<^sub>a vopt_assn\<close>
  by (sepref_to_hoare; vcg)

subsection \<open>Bucket the Lookup\<close>

definition lshm_bucket_the_lookup_impl
  :: \<open>'ki \<Rightarrow> ('ki \<times> 'vi ptr) cl_list \<Rightarrow> 'vi llM\<close> where[llvm_code]:
  \<open>lshm_bucket_the_lookup_impl ki p \<equiv> doM {
    vp \<leftarrow> lshm_bucket_lookup_impl ki p;
    v \<leftarrow> ll_load vp;
    ll_free vp;
    Mreturn v
  }\<close>

lemma lshm_bucket_the_lookup_rule[vcg_rules]:
  assumes \<open>lshm_bucket_contains k b\<close>
  shows \<open>llvm_htriple (boxed_buckets_assn b bi ** K k ki)
  (lshm_bucket_the_lookup_impl ki bi)
  (\<lambda>r. boxed_buckets_assn b bi ** K k ki ** V (lshm_bucket_the_lookup k b) r)\<close>
proof -
  from assms obtain v where [simp]: \<open>map_of b k = Some v\<close> by auto
  show ?thesis
    unfolding lshm_bucket_the_lookup_impl_def
    supply [simp] = lshm_bucket_the_lookup_map_of box_assn_expand sep_conj_exists
    by vcg
qed

sepref_register lshm_bucket_the_lookup
lemma lshm_bucket_the_lookup_hnr[sepref_fr_rules]:
  \<open>(uncurry lshm_bucket_the_lookup_impl, uncurry (RETURN oo lshm_bucket_the_lookup))
  \<in> [\<lambda>(k, b). lshm_bucket_contains k b]\<^sub>a K\<^sup>k *\<^sub>a boxed_buckets_assn\<^sup>k \<rightarrow> V\<close>
  by (sepref_to_hoare; vcg)

section \<open>Hashmap Implementation\<close>

text \<open>We use @{term oelem_assn} from Isabelle_LLVM.Proto_EOArray to temporarily move elements out of arrays.
  Note that this only applies to reasoning, we don't actually implement an option type for buckets
  (unlike for the values inside the bucket tuples, where we actually use a box).\<close>
definition hm_assn' :: \<open>(('k \<times> 'v) list option list, 64 word \<times> 64 word \<times> ('ki \<times> 'vi ptr) node ptr ptr) dr_assn\<close> where
  \<open>hm_assn' \<equiv> mk_assn (\<lambda>xs ali. EXS xsi. \<upharpoonleft>arl_assn xsi ali ** \<upharpoonleft>(list_assn (oelem_assn (mk_assn boxed_buckets_assn))) xs xsi)\<close>

definition hm_opt_rel :: \<open>(('k \<times> 'v) list option list \<times> ('k, 'v) hashmap) set\<close> where
  \<open>hm_opt_rel \<equiv> br (map the) (\<lambda>xs. None \<notin> set xs)\<close>

lemma in_hm_opt_rel_conv:
  \<open>(xs', xs) \<in> hm_opt_rel \<longleftrightarrow> xs = map the xs' \<and> None \<notin> set xs'\<close>
  unfolding hm_opt_rel_def by (simp add: in_br_conv)

definition hm_assn''
  :: \<open>('k, 'v) hashmap \<Rightarrow> 64 word \<times> 64 word \<times> ('ki \<times> 'vi ptr) node ptr ptr \<Rightarrow> assn\<close> where
  \<open>hm_assn'' \<equiv> hr_comp (\<upharpoonleft>hm_assn') hm_opt_rel\<close>

lemma hm_assn''_expand:
  \<open>hm_assn'' xs c = (EXS xs'. \<upharpoonleft>hm_assn' xs' c ** \<up>((xs', xs) \<in> hm_opt_rel))\<close>
  by (simp add: hm_assn''_def hr_comp_def)

lemma hm_opt_rel_length: \<open>(xs', xs) \<in> hm_opt_rel \<Longrightarrow> length xs' = length xs\<close>
  by (auto simp: in_hm_opt_rel_conv)

lemma hm_opt_rel_nth:
  assumes R: \<open>(xs', xs) \<in> hm_opt_rel\<close> and I: \<open>i < length xs\<close>
  shows \<open>xs' ! i = Some (xs ! i)\<close>
proof -
  from R have M: \<open>xs = map the xs'\<close> and N: \<open>None \<notin> set xs'\<close>
    by (auto simp: in_hm_opt_rel_conv)
  from I M have L: \<open>i < length xs'\<close> by simp
  with N have \<open>xs' ! i \<noteq> None\<close> using nth_mem by metis
  with L show ?thesis unfolding M by (cases \<open>xs' ! i\<close>) auto
qed

lemma hm_opt_rel_upd:
  \<open>(xs', xs) \<in> hm_opt_rel \<Longrightarrow> (xs'[i := Some b], xs[i := b]) \<in> hm_opt_rel\<close>
  by (auto simp: in_hm_opt_rel_conv map_update
    dest!: subsetD[OF set_update_subset_insert])

lemma hm_opt_rel_replicate: \<open>(replicate n (Some b), replicate n b) \<in> hm_opt_rel\<close>
  by (auto simp: in_hm_opt_rel_conv)

(* Pretty much copied from Proto_EOArray.thy *)
lemma hm_nth_rule[vcg_rules]: "llvm_htriple 
  (\<upharpoonleft>hm_assn' xs p \<and>* \<upharpoonleft>snat.assn i ii \<and>* \<up>\<^sub>d(i < length xs \<and> xs!i\<noteq>None)) 
  (arl_nth p ii)
  (\<lambda>ri. boxed_buckets_assn (the (xs!i)) ri \<and>* \<upharpoonleft>hm_assn' (xs[i:=None]) p)"  
  unfolding hm_assn'_def 
  supply [simp] = lo_extract_elem
  apply vcg
  done

lemma hm_upd_rule_snat[vcg_rules]: "llvm_htriple 
  (\<upharpoonleft>hm_assn' xs p \<and>* boxed_buckets_assn x xi \<and>* \<upharpoonleft>snat.assn i ii \<and>* \<up>\<^sub>d(i < length xs \<and> xs!i=None)) 
  (arl_upd p ii xi)
  (\<lambda>r. \<up>(r = p) \<and>* \<upharpoonleft>hm_assn' (xs[i := Some x]) p)"
  unfolding hm_assn'_def
  supply [simp] = lo_insert_elem
  apply vcg
  done

lemma hm_len_rule[vcg_rules]: \<open>llvm_htriple
  (\<upharpoonleft>hm_assn' xs p)
  (arl_len p)
  (\<lambda>r. \<upharpoonleft>hm_assn' xs p ** \<upharpoonleft>snat.assn (length xs) r)\<close>
  unfolding hm_assn'_def
  apply vcg
  apply (auto simp: sep_algebra_simps ENTAILS_def entails_def)
  by (smt (verit, del_insts) extract_pure_assn list_assn_neq_len(2)
    pure_true_conv sep.mult_commute sep_conj_empty sep_conj_false_left
    snat.assn_pure)

lemma lshm_bucket_of_impl_rule[vcg_rules]:
  assumes \<open>0 < n\<close>
  shows \<open>llvm_htriple
    (\<upharpoonleft>snat.assn n ni ** K k ki)
    (lshm_bucket_of_impl ni ki)
    (\<lambda>r. \<upharpoonleft>snat.assn n ni ** K k ki ** \<upharpoonleft>snat.assn (lshm_bucket_of n k) r)\<close>
proof -
  have PRE: \<open>(\<lambda>(n, _). 0 < n) (n, k)\<close> using assms by simp
  note HT = hfref_htriple_k1_k2_guard[OF lshm_bucket_of_impl.refine PRE,
    unfolded PR_CONST_def]
  show ?thesis
    using HT by (simp add: snat_rel_def snat.assn_is_rel[symmetric])
qed

subsection \<open>Update\<close>

definition [llvm_code]: \<open>lshm_op_map_update_impl \<equiv> \<lambda>ki vi xsi. doM {
    l \<leftarrow> arl_len xsi;
    bii \<leftarrow> lshm_bucket_of_impl l ki;
    bi \<leftarrow> arl_nth xsi bii; 
    bi \<leftarrow> lshm_bucket_update_impl ki vi bi;
    arl_upd xsi bii bi 
  }\<close>

lemma lshm_op_map_update_rule[vcg_rules]: \<open>llvm_htriple
  (K k ki ** V v vi ** hm_assn'' xs xsi ** \<up>\<^sub>d(xs \<noteq> []))
  (lshm_op_map_update_impl ki vi xsi)
  (\<lambda>r. hm_assn'' (lshm_op_map_update k v xs) r)\<close>
  unfolding lshm_op_map_update_impl_def hm_assn''_expand
  supply [simp] = hm_opt_rel_length hm_opt_rel_nth hm_opt_rel_upd
    lshm_op_map_update_def Let_def sep_conj_exists
  by vcg

lemma lshm_op_map_update_hnr:
  \<open>(uncurry2 lshm_op_map_update_impl, uncurry2 (RETURN ooo lshm_op_map_update))
  \<in> [\<lambda>((k,v),xs). xs\<noteq>[]]\<^sub>a K\<^sup>d *\<^sub>a V\<^sup>d *\<^sub>a hm_assn''\<^sup>d \<rightarrow> hm_assn''\<close>
  apply (sepref_to_hoare; vcg)
  done

lemma lshm_rel_nonempty[fcomp_prenorm_simps]: \<open>(xs', m) \<in> lshm_rel \<Longrightarrow> xs' \<noteq> []\<close>
  by (auto simp: lshm_rel_def in_br_conv lshm_invar_def)

lemmas lshm_update_hnr[sepref_fr_rules] =
  lshm_op_map_update_hnr[FCOMP lshm_update_fref]

subsection \<open>Delete\<close>

definition [llvm_code]: \<open>lshm_op_map_delete_impl \<equiv> \<lambda>ki xsi. doM {
    l \<leftarrow> arl_len xsi;
    bii \<leftarrow> lshm_bucket_of_impl l ki;
    bi \<leftarrow> arl_nth xsi bii; 
    bi \<leftarrow> lshm_bucket_delete_impl ki bi;
    arl_upd xsi bii bi   
  }\<close>

lemma lshm_op_map_delete_rule[vcg_rules]: \<open>llvm_htriple
  (K k ki ** hm_assn'' xs xsi ** \<up>\<^sub>d(xs \<noteq> []))
  (lshm_op_map_delete_impl ki xsi)
  (\<lambda>r. K k ki ** hm_assn'' (lshm_op_map_delete k xs) r)\<close>
  unfolding lshm_op_map_delete_impl_def hm_assn''_expand
  supply [simp] = hm_opt_rel_length hm_opt_rel_nth hm_opt_rel_upd
    lshm_op_map_delete_def Let_def sep_conj_exists
  by vcg

lemma lshm_op_map_delete_hnr:
  \<open>(uncurry lshm_op_map_delete_impl, uncurry (RETURN oo lshm_op_map_delete))
  \<in> [\<lambda>(k,xs). xs\<noteq>[]]\<^sub>a K\<^sup>k *\<^sub>a hm_assn''\<^sup>d \<rightarrow> hm_assn''\<close>
  apply (sepref_to_hoare; vcg)
  done

lemmas lshm_delete_hnr[sepref_fr_rules] = 
  lshm_op_map_delete_hnr[FCOMP lshm_delete_fref]

subsection \<open>Contains\<close>

lemma hm_opt_rel_restore:
  \<open>(xs', xs) \<in> hm_opt_rel \<Longrightarrow> i < length xs \<Longrightarrow> xs'[i := Some (xs ! i)] = xs'\<close>
  by (metis hm_opt_rel_nth list_update_id)

definition [llvm_code]: \<open>lshm_op_map_contains_key_impl \<equiv> \<lambda>ki xsi. doM {
    l \<leftarrow> arl_len xsi;
    bii \<leftarrow> lshm_bucket_of_impl l ki;
    bi \<leftarrow> arl_nth xsi bii;
    r \<leftarrow> lshm_bucket_contains_impl ki bi;
    arl_upd xsi bii bi;
    Mreturn r
  }\<close>

lemma lshm_op_map_contains_key_rule[vcg_rules]: \<open>llvm_htriple
  (K k ki ** hm_assn'' xs xsi ** \<up>\<^sub>d(xs \<noteq> []))
  (lshm_op_map_contains_key_impl ki xsi)
  (\<lambda>r. K k ki ** hm_assn'' xs xsi ** bool1_assn (lshm_op_map_contains_key k xs) r)\<close>
  unfolding lshm_op_map_contains_key_impl_def hm_assn''_expand
  supply [simp] = hm_opt_rel_length hm_opt_rel_nth hm_opt_rel_restore
    lshm_op_map_contains_key_def Let_def sep_conj_exists
  by vcg

lemma lshm_op_map_contains_key_hnr:
  \<open>(uncurry lshm_op_map_contains_key_impl, uncurry (RETURN oo lshm_op_map_contains_key))
  \<in> [\<lambda>(k,xs). xs\<noteq>[]]\<^sub>a K\<^sup>k *\<^sub>a hm_assn''\<^sup>k \<rightarrow> bool1_assn\<close>
  supply [simp] = bool1_rel_def bool.rel_def in_br_conv pure_def
  by (sepref_to_hoare; vcg)

lemmas lshm_contains_key_hnr[sepref_fr_rules] =
  lshm_op_map_contains_key_hnr[FCOMP lshm_contains_key_fref]

subsection \<open>Lookup\<close>

definition [llvm_code]: \<open>lshm_op_map_lookup_impl \<equiv> \<lambda>ki xsi. doM {
    l \<leftarrow> arl_len xsi;
    bii \<leftarrow> lshm_bucket_of_impl l ki;
    bi \<leftarrow> arl_nth xsi bii;
    r \<leftarrow> lshm_bucket_lookup_impl ki bi;
    arl_upd xsi bii bi;
    Mreturn r
  }\<close>

lemma lshm_op_map_lookup_rule[vcg_rules]: \<open>llvm_htriple
  (K k ki ** hm_assn'' xs xsi ** \<up>\<^sub>d(xs \<noteq> []))
  (lshm_op_map_lookup_impl ki xsi)
  (\<lambda>r. K k ki ** hm_assn'' xs xsi ** vopt_assn (lshm_op_map_lookup k xs) r)\<close>
  unfolding lshm_op_map_lookup_impl_def hm_assn''_expand
  supply [simp] = hm_opt_rel_length hm_opt_rel_nth hm_opt_rel_restore
    lshm_op_map_lookup_def Let_def sep_conj_exists
  by vcg

lemma lshm_op_map_lookup_hnr:
  \<open>(uncurry lshm_op_map_lookup_impl, uncurry (RETURN oo lshm_op_map_lookup))
  \<in> [\<lambda>(k,xs). xs\<noteq>[]]\<^sub>a K\<^sup>k *\<^sub>a hm_assn''\<^sup>k \<rightarrow> vopt_assn\<close>
  by (sepref_to_hoare; vcg)

lemmas lshm_lookup_hnr[sepref_fr_rules] =
  lshm_op_map_lookup_hnr[FCOMP lshm_lookup_fref]

subsection \<open>The-Lookup\<close>

definition [llvm_code]: \<open>lshm_the_lookup_impl \<equiv> \<lambda>ki xsi. doM {
    l \<leftarrow> arl_len xsi;
    bii \<leftarrow> lshm_bucket_of_impl l ki;
    bi \<leftarrow> arl_nth xsi bii;
    r \<leftarrow> lshm_bucket_the_lookup_impl ki bi;
    arl_upd xsi bii bi;
    Mreturn r
  }\<close>

lemma lshm_the_lookup_rule[vcg_rules]: \<open>llvm_htriple
  (K k ki ** hm_assn'' xs xsi ** \<up>\<^sub>d(xs \<noteq> [] \<and> lshm_op_map_contains_key k xs))
  (lshm_the_lookup_impl ki xsi)
  (\<lambda>r. K k ki ** hm_assn'' xs xsi ** V (lshm_the_lookup k xs) r)\<close>
  unfolding lshm_the_lookup_impl_def hm_assn''_expand
  supply [simp] = hm_opt_rel_length hm_opt_rel_nth hm_opt_rel_restore
    lshm_the_lookup_def lshm_op_map_contains_key_def Let_def sep_conj_exists
  by vcg

lemma lshm_the_lookup_impl_hnr:
  \<open>(uncurry lshm_the_lookup_impl, uncurry (RETURN oo lshm_the_lookup))
  \<in> [\<lambda>(k,xs). xs\<noteq>[] \<and> lshm_op_map_contains_key k xs]\<^sub>a K\<^sup>k *\<^sub>a hm_assn''\<^sup>k \<rightarrow> V\<close>
  by (sepref_to_hoare; vcg)

lemma lshm_rel_contains[fcomp_prenorm_simps]:
  \<open>(xs', m) \<in> lshm_rel \<Longrightarrow> lshm_op_map_contains_key k xs' \<longleftrightarrow> m k \<noteq> None\<close>
  by (auto simp: lshm_rel_def in_br_conv lshm_contains_key_\<alpha>)

lemmas lshm_the_lookup_hnr[sepref_fr_rules] =
  lshm_the_lookup_impl_hnr[FCOMP lshm_the_lookup_fref]

subsection \<open>Empty\<close>

definition lshm_empty :: \<open>64 word \<Rightarrow> (64 word \<times> 64 word \<times> ('ki \<times> 'vi ptr) node ptr ptr) llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>lshm_empty ni \<equiv> arl_new_repl_init TYPE(('ki \<times> 'vi ptr) node ptr) ni\<close>

lemma list_assn_oelem_replicate_empty[simp]:
  \<open>\<upharpoonleft>(list_assn (oelem_assn (mk_assn boxed_buckets_assn))) (replicate n (Some [])) (replicate n init) = \<box>\<close>
  by (induction n) (auto simp: sep_algebra_simps cl_assn_simps(1))

lemma lshm_empty_aux_rule:
  \<open>llvm_htriple
    (\<upharpoonleft>snat.assn n ni)
    (lshm_empty ni)
    (\<lambda>r. \<upharpoonleft>hm_assn' (replicate n (Some [])) r)\<close>
  unfolding lshm_empty_def hm_assn'_def
  apply vcg
  apply (auto simp: sep_algebra_simps ENTAILS_def entails_def)
  by (metis init_ptr_def list_assn_oelem_replicate_empty sep_conj_empty)

lemma lshm_empty_rule[vcg_rules]:
  \<open>llvm_htriple
    (\<upharpoonleft>snat.assn n ni)
    (lshm_empty ni)
    (\<lambda>r. hm_assn'' (lshm_op_map_empty n) r)\<close>
  unfolding hm_assn''_expand lshm_op_map_empty_def
  supply [vcg_rules] = lshm_empty_aux_rule
  supply [simp] = hm_opt_rel_replicate
  by vcg

subsection \<open>Free\<close>

text \<open>\<open>nulled_prefix\<close> and its bookkeeping are redefined here because the
  originals are scoped inside the \<open>array_pmap\<close> locale of \<open>IICF_PartialMap\<close>.\<close>

definition \<open>nulled_prefix (xs :: 'c option list) i = replicate i None @ drop i xs\<close>

lemma nulled_emp[simp]: \<open>nulled_prefix xs 0 = xs\<close>
  unfolding nulled_prefix_def by simp

lemma nulled_prefix_length[simp]:
  \<open>i \<le> length xs \<Longrightarrow> length (nulled_prefix xs i) = length xs\<close>
  unfolding nulled_prefix_def by simp

lemma nulled_prefix_nth[simp]:
  \<open>i < length xs \<Longrightarrow> nulled_prefix xs i ! i = xs ! i\<close>
  unfolding nulled_prefix_def
  by (metis Cons_nth_drop_Suc drop_append_miracle length_replicate nth_via_drop)

lemma nulled_prefix_step[simp]:
  \<open>i < length xs \<Longrightarrow> (nulled_prefix xs i)[i := Option.None] = nulled_prefix xs (Suc i)\<close>
  unfolding nulled_prefix_def
  by (metis Cons_nth_drop_Suc append_Cons length_replicate
            list_update_length replicate_Suc replicate_app_Cons_same)

lemma nulled_prefix_full[simp]:
  \<open>nulled_prefix xs (length xs) = replicate (length xs) Option.None\<close>
  unfolding nulled_prefix_def by simp

definition lshm_free :: \<open>64 word \<times> 64 word \<times> ('ki \<times> 'vi ptr) node ptr ptr \<Rightarrow> unit llM\<close>
  where [llvm_code]:
  \<open>lshm_free xsi \<equiv> doM {
    llc_while
      (\<lambda>i. doM { l \<leftarrow> arl_len xsi; ll_icmp_ult i l })
      (\<lambda>i. doM {
        bi \<leftarrow> arl_nth xsi i;
        bucket.cl_free bi;
        i \<leftarrow> ll_add i (signed_nat 1);
        Mreturn i
      }) (signed_nat 0);
    arl_free xsi
  }\<close>

lemma all_some_nth: \<open>None \<notin> set xs \<Longrightarrow> i < length xs \<Longrightarrow> xs ! i \<noteq> None\<close>
  by (metis nth_mem)

lemma list_assn_oelem_all_None:
  \<open>set xs \<subseteq> {None} \<Longrightarrow>
    \<upharpoonleft>(list_assn (oelem_assn A)) xs xsi = \<up>(length xsi = length xs)\<close>
proof (induction xs arbitrary: xsi)
  case Nil
  then show ?case by (cases xsi) (auto simp: sep_algebra_simps)
next
  case (Cons x xs)
  then show ?case
    by (cases xsi) (auto simp: sep_algebra_simps list_assn_cons1_conv Cons.IH)
qed

text \<open>Once all slots are freed, the remaining \<open>hm_assn'\<close> is just the raw array.\<close>
lemma lshm_free_arl_rule[vcg_rules]:
  \<open>llvm_htriple (\<upharpoonleft>hm_assn' xs ali ** \<up>\<^sub>d(set xs \<subseteq> {None})) (arl_free ali) (\<lambda>_. \<box>)\<close>
  unfolding hm_assn'_def
  supply [simp] = list_assn_oelem_all_None sep_conj_exists
  by vcg

lemma lshm_free_aux_rule:
  \<open>llvm_htriple
    (\<upharpoonleft>hm_assn' xs' ali ** \<up>\<^sub>d(None \<notin> set xs'))
    (lshm_free ali)
    (\<lambda>_. \<box>)\<close>
  unfolding lshm_free_def
  apply (rewrite annotate_llc_while[where
    I=\<open>\<lambda>ii t. EXS i. \<upharpoonleft>snat.assn i ii ** \<upharpoonleft>hm_assn' (nulled_prefix xs' i) ali
        ** \<up>(i \<le> length xs' \<and> None \<notin> set xs') ** \<up>\<^sub>!(t = length xs' - i)\<close>
    and R=\<open>less_than\<close>])
  supply [simp] = all_some_nth
  apply vcg_monadify
  apply vcg'
  done

lemma lshm_free_rule[vcg_rules]:
  \<open>llvm_htriple (hm_assn'' xs ali) (lshm_free ali) (\<lambda>_. \<box>)\<close>
  unfolding hm_assn''_expand
  supply [vcg_rules] = lshm_free_aux_rule
  supply [simp] = in_hm_opt_rel_conv sep_conj_exists
  by vcg

lemma lshm_free_mk_free[sepref_frame_free_rules]: \<open>MK_FREE hm_assn'' lshm_free\<close>
  by (rule MK_FREEI) (rule lshm_free_rule)

text \<open>Convenient top-level assertion for outside use\<close>
abbreviation \<open>hm_assn \<equiv> hr_comp hm_assn'' lshm_rel\<close>

end

end
