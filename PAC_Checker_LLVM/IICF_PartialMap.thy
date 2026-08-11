theory IICF_PartialMap
  imports
    Isabelle_LLVM.IICF
    Isabelle_LLVM.Proto_EOArray
    Isabelle_LLVM.LLVM_DS_Block_Alloc
    IICF_Copying_List
    (* TODO: We only really use IICF_Copying_List for the copying setup, maybe that should live somewhere else? *)
begin

text \<open>This theory implement a key-value map.
  It refines @{typ \<open>'a option list\<close>}, i.e. a partial map.
  It is inspired by @{theory Isabelle_LLVM.Proto_EOArray}
  and uses a similar construction.
  A lot of the proofs in here were found by Anthropic LLMs,
  they could most likely be much more concise and readable with some more ground work.\<close>

text \<open>TODO list \<emdash> coverage of the @{theory Isabelle_LLVM.IICF_Map} interface
  \<^item> [x] \<open>op_map_empty\<close>
  \<^item> [x] \<open>op_map_update\<close>
  \<^item> [x] \<open>op_map_delete\<close>
  \<^item> [x] \<open>op_map_contains_key\<close>
  \<^item> [ ] \<open>op_map_is_empty\<close> (needs a size field to be efficient, which we don't currently have
                           it's possible to have this in linear time, but that sounds like a
                           bad idea to even support...)

  -- Requires Copying --
  Lookup does not really make sense without copying, as it would destroy the map otherwise.
  It would require a different type signature for lookup where also the map is returned to 
  have a non-copying lookup. i.e. something like
    my_lookup :: \<open>'k \<Rightarrow> ('k, 'v) map \<Rightarrow> ('v, ('k, 'v) map)\<close>
  That however would also be awkward, as one would have to destroy the tuple to extract both
  the new list and the value. 
  It's however possible to implement a non-copying variant with a postcondition of somthing like
  \<open>[map_assn xs ai ... ] (op_map_lookup ki ai) [map_assn xs[ki:=None] ... ]\<close>
  but I don't know how to represent something like this on the HOL level for use with sepref...

  Implemented with an assumed copy operation for the contained type:
    \<^item> [x] \<open>op_map_lookup\<close>
    \<^item> [x] \<open>op_map_the_lookup\<close>

  Infrastructure (not interface ops):
    \<^item> [x] \<open>MK_FREE\<close> deep free
    \<^item> [ ] \<open>COPY\<close> deep copy (needs a copy function for the contained elements of course...)
\<close>

section \<open>High level map implementation by option list\<close>
text \<open>First, we implement maps using lists of optionals.
  We then later compose with the low level implementation.\<close>

type_synonym 'a opt_list = \<open>'a option list\<close>

definition \<open>opt_list_\<alpha> ol \<equiv> \<lambda>n. if n < length ol then ol ! n else None\<close>
lemma opt_list_dom_bound:
  assumes \<open>i \<in> dom (opt_list_\<alpha> ol)\<close>
    shows \<open>i < length ol\<close>
  unfolding opt_list_\<alpha>_def
  apply (cases \<open>i \<in> dom (opt_list_\<alpha> ol)\<close>)
  apply (meson domIff opt_list_\<alpha>_def)
  by (metis assms)

definition opt_list_map_rel :: \<open>('a opt_list \<times> (nat \<Rightarrow> 'a option)) set\<close> where
  \<open>opt_list_map_rel \<equiv> br opt_list_\<alpha> (\<lambda>_. True)\<close>

definition \<open>opt_list_empty \<equiv> ([] :: 'a opt_list)\<close>
definition \<open>opt_list_update k v m \<equiv> (m @ replicate (k + 1 - length m) None)[k:=Some v]\<close>
definition \<open>opt_list_delete k m \<equiv> if k < length m then m[k:=None] else m\<close>
definition \<open>opt_list_contains_key k m \<equiv> if k < length m then m!k \<noteq> None else False\<close>
definition \<open>opt_list_is_empty \<equiv> list_all (\<lambda>x. x = None)\<close>
definition \<open>opt_list_lookup k m \<equiv> if k < length m then m!k else None\<close>
definition \<open>opt_list_the_lookup k m \<equiv> the (m!k)\<close>

lemma opt_list_empty_refine:
  \<open>(uncurry0 (RETURN opt_list_empty), uncurry0 (RETURN op_map_empty))
  \<in> unit_rel \<rightarrow>\<^sub>f \<langle>opt_list_map_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  by (auto simp: opt_list_empty_def opt_list_map_rel_def in_br_conv opt_list_\<alpha>_def)

lemma opt_list_\<alpha>_update:
  \<open>opt_list_\<alpha> (opt_list_update k v m) = (opt_list_\<alpha> m)(k \<mapsto> v)\<close>
  by (auto simp: opt_list_update_def opt_list_\<alpha>_def nth_append nth_list_update fun_upd_def)

lemma opt_list_\<alpha>_delete:
  \<open>opt_list_\<alpha> (opt_list_delete k m) = (opt_list_\<alpha> m)(k := None)\<close>
  by (auto simp: opt_list_delete_def opt_list_\<alpha>_def nth_list_update fun_upd_def)

lemma opt_list_update_refine:
  \<open>(uncurry2 (RETURN ooo opt_list_update), uncurry2 (RETURN ooo op_map_update))
    \<in> (nat_rel \<times>\<^sub>r Id) \<times>\<^sub>r opt_list_map_rel \<rightarrow>\<^sub>f \<langle>opt_list_map_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  by (auto simp: opt_list_map_rel_def in_br_conv opt_list_\<alpha>_update)

lemma opt_list_delete_refine:
  \<open>(uncurry (RETURN oo opt_list_delete), uncurry (RETURN oo op_map_delete))
    \<in> nat_rel \<times>\<^sub>r opt_list_map_rel \<rightarrow>\<^sub>f \<langle>opt_list_map_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  by (auto simp: opt_list_map_rel_def in_br_conv opt_list_\<alpha>_delete)

lemma opt_list_contains_key_refine:
  \<open>(uncurry (RETURN oo opt_list_contains_key), uncurry (RETURN oo op_map_contains_key))
    \<in> nat_rel \<times>\<^sub>r opt_list_map_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  by (auto simp: opt_list_map_rel_def in_br_conv opt_list_contains_key_def opt_list_\<alpha>_def dom_def)

lemma opt_list_is_empty_refine:
  \<open>(RETURN o opt_list_is_empty, RETURN o op_map_is_empty)
    \<in> opt_list_map_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  by (auto simp: opt_list_map_rel_def in_br_conv opt_list_is_empty_def opt_list_\<alpha>_def list_all_length fun_eq_iff)

lemma opt_list_lookup_refine:
  \<open>(uncurry (RETURN oo opt_list_lookup), uncurry (RETURN oo op_map_lookup))
    \<in> nat_rel \<times>\<^sub>r opt_list_map_rel \<rightarrow>\<^sub>f \<langle>\<langle>Id\<rangle>option_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  by (auto simp: opt_list_map_rel_def in_br_conv opt_list_lookup_def opt_list_\<alpha>_def)

lemma opt_list_the_lookup_refine:
  \<open>(uncurry (RETURN oo opt_list_the_lookup), uncurry (RETURN oo op_map_the_lookup))
    \<in> [\<lambda>(k,m). m k \<noteq> None]\<^sub>f nat_rel \<times>\<^sub>r opt_list_map_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  by (auto simp: opt_list_map_rel_def in_br_conv opt_list_the_lookup_def opt_list_\<alpha>_def split: if_splits)

lemma opt_list_contains_key_fcomp[fcomp_prenorm_simps]:
  \<open>(ol, m) \<in> opt_list_map_rel \<Longrightarrow> opt_list_contains_key k ol \<longleftrightarrow> m k \<noteq> None\<close>
  by (auto simp: opt_list_map_rel_def in_br_conv opt_list_contains_key_def opt_list_\<alpha>_def)

section \<open>Low-level implementation\<close>
text \<open>Now we implement our option list on llvm level.\<close>

subsection \<open>Init-tailed array list\<close>
text \<open>@{term arl_assn} does not fill the tail with @{term init} on resize, so we'd have to initialize
  each element. Therefore we define a new init array list and reuse @{term arl_assn} where possible.\<close>

definition iarl_assn :: \<open>('a::llvm_rep list, ('a,64) array_list) dr_assn\<close> where
  \<open>iarl_assn \<equiv> mk_assn (\<lambda>xs (li,ci,ai). EXS c a.
      \<upharpoonleft>snat.assn (length xs) li ** \<upharpoonleft>snat.assn c ci ** \<upharpoonleft>narray_assn a ai
      ** \<up>(length xs \<le> c \<and> c = length a
            \<and> a = xs @ replicate (c - length xs) init))\<close>

lemma snat8_64[simp]: \<open>8 \<in> snats LENGTH(64)\<close>
  by (simp add: snats_def)

lemma iarl_new_raw_rule[vcg_rules]:
  \<open>llvm_htriple \<box>
     (arl_new_raw :: ('a::llvm_rep,64) array_list llM)
     (\<lambda>r. \<upharpoonleft>iarl_assn ([]::'a list) r)\<close>
  unfolding arl_new_raw_def arl_initial_size_def iarl_assn_def
  apply (vcg_monadify)
  apply vcg'
  by (metis snat8_64) 

lemma iarl_len_rule[vcg_rules]:
  \<open>llvm_htriple (\<upharpoonleft>iarl_assn xs ali) (arl_len ali)
     (\<lambda>li. \<upharpoonleft>iarl_assn xs ali ** \<upharpoonleft>snat.assn (length xs) li)\<close>
  unfolding iarl_assn_def arl_len_def
  by vcg

lemma iarl_nth_rule[vcg_rules]:
  \<open>llvm_htriple (\<upharpoonleft>iarl_assn xs ali ** \<upharpoonleft>snat.assn i ii ** \<up>\<^sub>d(i < length xs))
     (arl_nth ali ii)
     (\<lambda>x. \<upharpoonleft>iarl_assn xs ali ** \<up>(x = xs ! i))\<close>
  supply [simp] = nth_append
  unfolding iarl_assn_def arl_nth_def
  by vcg

lemma iarl_upd_rule[vcg_rules]:
  \<open>llvm_htriple (\<upharpoonleft>iarl_assn xs ali ** \<upharpoonleft>snat.assn i ii ** \<up>\<^sub>d(i < length xs))
     (arl_upd ali ii x)
     (\<lambda>ali'. \<upharpoonleft>iarl_assn (xs[i := x]) ali' ** \<up>(ali' = ali))\<close>
  supply [simp] = list_update_append
  unfolding iarl_assn_def arl_upd_def
  by vcg

definition iarl_resize :: \<open>64 word \<Rightarrow> ('a::llvm_rep, 64) array_list \<Rightarrow> ('a, 64) array_list llM\<close> where[llvm_code]:
  \<open>iarl_resize c' al \<equiv> doM {
    al \<leftarrow> arl_ensure_capacity c' al;  
    let (_, c, a) = al;
    Mreturn (c', c, a)
  }\<close>

lemma replicate_merge:
  assumes \<open>l \<le> x\<close> and \<open>x \<le> c\<close>
  shows \<open>replicate (x - l) i @ replicate (c - x) i = replicate (c - l) i\<close>
proof -
  from assms have \<open>(x - l) + (c - x) = c - l\<close> by arith
  then show ?thesis by (metis replicate_add)
qed

lemma iarl_resize_rule[vcg_rules]:
  \<open>llvm_htriple
    (\<upharpoonleft>iarl_assn xs ali ** \<upharpoonleft>snat.assn x xi ** \<up>\<^sub>d(length xs \<le> x))
    (iarl_resize xi ali)
    (\<lambda>ali'. \<upharpoonleft>iarl_assn (xs @ replicate (x - length xs) init) ali')\<close>
  supply [simp] = replicate_merge
  unfolding iarl_resize_def arl_ensure_capacity_def arl_resize_def iarl_assn_def
  by vcg'


locale array_pmap =
  dflt_option_private dflt A is_dflt + freeable_assn A afree
  for dflt and A :: \<open>'b \<Rightarrow> 'a::llvm_rep \<Rightarrow> assn\<close> and is_dflt
  and afree :: \<open>'a \<Rightarrow> unit llM\<close> +
  assumes dflt_is_init: \<open>dflt = init\<close>
begin

text \<open>Very similar to @{term nao_assn}, but we use the option assertion from the locale.
  Also, we use @{term arl_assn} to reuse it's resizing machinery.\<close>

(* We opt into 64-bit keys here, this makes proofs less noisy but maybe should be generalized at some point? *)
definition \<open>pmap_assn \<equiv> mk_assn (\<lambda>xs (p :: (_, 64) array_list). EXS xsi. \<upharpoonleft>iarl_assn xsi p ** \<upharpoonleft>(list_assn (mk_assn option_assn)) xs xsi)\<close>
abbreviation \<open>pmap_assn' \<equiv> \<upharpoonleft>pmap_assn\<close>
type_synonym 'c pmap_conc = \<open>('c, 64) array_list\<close>

text \<open>Basic simplifications of the locale's option assertion.\<close>

lemma option_assn_dflt[simp]: \<open>option_assn Option.None dflt = \<box>\<close>
  unfolding option_assn_def by (auto simp: sep_algebra_simps)

lemma option_assn_Some[simp]: \<open>option_assn (Option.Some x) c = A x c\<close>
  unfolding option_assn_def
  by (cases \<open>c = dflt\<close>) (auto simp: UU sep_algebra_simps)

lemma option_assn_None_conv: \<open>option_assn Option.None c = \<up>(c = dflt)\<close>
  unfolding option_assn_def by (auto simp: sep_algebra_simps)

lemma list_assn_option_replicate[simp]:
  \<open>\<upharpoonleft>(list_assn (mk_assn option_assn)) (replicate n Option.None) (replicate n init) = \<box>\<close>
  by (induction n) (auto simp: dflt_is_init[symmetric] sep_algebra_simps)

lemma list_assn_option_focus:
  assumes A: \<open>i < length xs\<close>
  shows \<open>\<upharpoonleft>(list_assn (mk_assn option_assn)) xs xsi =
    (option_assn (xs!i) (xsi!i) **
    \<upharpoonleft>(list_assn (mk_assn option_assn)) (xs[i := Option.None]) (xsi[i := dflt]))\<close>
proof (cases \<open>length xsi = length xs\<close>)
  case True
  obtain xs\<^sub>1 x xs\<^sub>2 where XSF: \<open>xs = xs\<^sub>1 @ x # xs\<^sub>2\<close> and LEN1: \<open>i = length xs\<^sub>1\<close>
    using id_take_nth_drop[OF A] A by fastforce
  obtain ys\<^sub>1 y ys\<^sub>2 where YSF: \<open>xsi = ys\<^sub>1 @ y # ys\<^sub>2\<close> and LEN2: \<open>length ys\<^sub>1 = length xs\<^sub>1\<close>
      and \<open>length ys\<^sub>2 = length xs\<^sub>2\<close>
    using split_list_according[OF XSF True] .
  show ?thesis
    unfolding XSF YSF LEN1
    by (simp add: LEN2 nth_append list_update_append sep_algebra_simps sep_conj_c)
next
  case False
  then show ?thesis by simp
qed

lemma list_assn_option_insert:
  assumes \<open>i < length xs\<close>
  shows \<open>\<upharpoonleft>(list_assn (mk_assn option_assn)) (xs[i := Option.Some v]) (xsi[i := vi]) =
    (A v vi ** \<upharpoonleft>(list_assn (mk_assn option_assn)) (xs[i := Option.None]) (xsi[i := dflt]))\<close>
proof (cases \<open>i < length xsi\<close>)
  case True
  from assms have \<open>i < length (xs[i := Option.Some v])\<close> by simp
  from list_assn_option_focus[OF this, of \<open>xsi[i := vi]\<close>] show ?thesis
    using assms True by simp
next
  case False
  then show ?thesis using assms by (simp add: sep_algebra_simps)
qed

lemma pmap_empty_hnr:
  \<open>(uncurry0 arl_new_raw, uncurry0 (RETURN opt_list_empty)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a pmap_assn'\<close>
  supply [simp] = pmap_assn_def opt_list_empty_def
  by (sepref_to_hoare; vcg)

lemmas pmap_empty_hnr2[sepref_fr_rules] =
  pmap_empty_hnr[FCOMP opt_list_empty_refine]

lemma pmap_free_slot_rule[vcg_rules]:
  \<open>llvm_htriple
     (\<upharpoonleft>(list_assn (mk_assn option_assn)) xs xsi ** \<up>\<^sub>d(i < length xs))
     (free_option afree (xsi ! i))
     (\<lambda>_. \<upharpoonleft>(list_assn (mk_assn option_assn)) (xs[i := Option.None]) (xsi[i := dflt]))\<close>
proof (cases \<open>i < length xs\<close>)
  case True
  show ?thesis
    supply [vcg_rules] = mk_free_option[OF afree_free, THEN MK_FREED]
    unfolding vcg_tag_defs list_assn_option_focus[OF True]
    by vcg
next
  case False
  show ?thesis
    unfolding vcg_tag_defs
    apply (rule htriple_realizable_preI)
    using False by (simp add: sep_algebra_simps)
qed

(* note that our update takes ownership *)
definition pmap_update :: \<open>64 word \<Rightarrow> 'a \<Rightarrow> 'a pmap_conc \<Rightarrow> 'a pmap_conc llM\<close> where[llvm_code]:
  \<open>pmap_update ki vi ai \<equiv> doM {
    l \<leftarrow> arl_len ai;
    b \<leftarrow> ll_icmp_ult ki l;
    llc_if b (doM {
      prev \<leftarrow> arl_nth ai ki;
      free_option afree prev;
      arl_upd ai ki vi
    }) (doM {
      k1 \<leftarrow> ll_add ki 1;
      ai \<leftarrow> iarl_resize k1 ai;
      arl_upd ai ki vi
    })
  }\<close>

lemma pmap_update_reassemble_present:
  assumes A: \<open>k < length xsi\<close>
  shows \<open>ENTAILS
    (\<upharpoonleft>iarl_assn (xsi[k := vi]) ai **
     \<upharpoonleft>(list_assn (mk_assn option_assn)) (xs[k := Option.None]) (xsi[k := dflt]) ** A v vi)
    (EXS z. \<upharpoonleft>iarl_assn z ai **
       \<upharpoonleft>(list_assn (mk_assn option_assn))
          ((xs @ replicate (Suc k - length xs) Option.None)[k := Option.Some v]) z)\<close>
proof (cases \<open>length xs = length xsi\<close>)
  case True
  with A have K: \<open>k < length xs\<close> by simp
  then have [simp]: \<open>Suc k - length xs = 0\<close> by simp
  show ?thesis
    unfolding ENTAILS_def
    apply simp
    apply (rule entails_exI[where x=\<open>xsi[k := vi]\<close>])
    by (simp add: list_assn_option_insert[OF K] sep_conj_aci)
next
  case False
  then show ?thesis
    unfolding ENTAILS_def by (auto simp: entails_def sep_algebra_simps)
qed

lemma pmap_update_reassemble_absent:
  assumes A: \<open>\<not> k < length xsi\<close>
  shows \<open>ENTAILS
    (\<upharpoonleft>iarl_assn ((xsi @ replicate (Suc k - length xsi) init)[k := vi]) ai **
     \<upharpoonleft>(list_assn (mk_assn option_assn)) xs xsi ** A v vi)
    (EXS z. \<upharpoonleft>iarl_assn z ai **
       \<upharpoonleft>(list_assn (mk_assn option_assn))
          ((xs @ replicate (Suc k - length xs) Option.None)[k := Option.Some v]) z)\<close>
proof (cases \<open>length xs = length xsi\<close>)
  case True
  with A have LE: \<open>length xs \<le> k\<close> by simp
  have K: \<open>k < length (xs @ replicate (Suc k - length xs) Option.None)\<close>
    using LE by simp
  have 1: \<open>(xs @ replicate (Suc k - length xs) Option.None)[k := Option.None]
         = xs @ replicate (Suc k - length xs) Option.None\<close>
    using LE by (simp add: list_update_append list_update_same_conv)
  have 2: \<open>(xsi @ replicate (Suc k - length xsi) init)[k := dflt]
         = xsi @ replicate (Suc k - length xsi) init\<close>
    using A by (simp add: list_update_append list_update_same_conv dflt_is_init)
  have 3: \<open>\<upharpoonleft>(list_assn (mk_assn option_assn)) (xs @ replicate (Suc k - length xs) Option.None)
             (xsi @ replicate (Suc k - length xsi) init)
         = \<upharpoonleft>(list_assn (mk_assn option_assn)) xs xsi\<close>
    using True by (simp add: sep_algebra_simps)
  show ?thesis
    unfolding ENTAILS_def
    apply (rule entails_exI[where x=\<open>(xsi @ replicate (Suc k - length xsi) init)[k := vi]\<close>])
    by (simp add: list_assn_option_insert[OF K] 1 2 3 sep_conj_aci)
next
  case False
  then show ?thesis
    unfolding ENTAILS_def by (auto simp: entails_def sep_algebra_simps)
qed

lemma pmap_update_rule[vcg_rules]:
  \<open>llvm_htriple
    (\<upharpoonleft>snat.assn k ki ** A v vi ** pmap_assn' xs ai ** \<up>\<^sub>d(k + 1 < max_snat 64))
    (pmap_update ki vi ai)
    (\<lambda>ai'. pmap_assn' (opt_list_update k v xs) ai')\<close>
  unfolding pmap_update_def opt_list_update_def
  supply [simp] = pmap_assn_def list_assn_option_focus
  apply vcg
  subgoal by (rule pmap_update_reassemble_present)
  apply vcg
  subgoal by (rule pmap_update_reassemble_absent)
  done

lemma pmap_update_hnr:
  \<open>(uncurry2 pmap_update, uncurry2 (RETURN ooo opt_list_update))
    \<in> [\<lambda>((k,_),_). k + 1 < max_snat 64]\<^sub>a
      (snat_assn' TYPE(64))\<^sup>k *\<^sub>a A\<^sup>d *\<^sub>a pmap_assn'\<^sup>d \<rightarrow> pmap_assn'\<close>
  unfolding snat_rel_def snat.assn_is_rel[symmetric]
  apply sepref_to_hoare
  by vcg

lemmas pmap_update_hnr2[sepref_fr_rules] =
  pmap_update_hnr[FCOMP opt_list_update_refine]

definition pmap_delete :: \<open>64 word \<Rightarrow> 'a pmap_conc \<Rightarrow> 'a pmap_conc llM\<close> where[llvm_code]:
  \<open>pmap_delete ii ai \<equiv> doM {
    l \<leftarrow> arl_len ai;
    cmp \<leftarrow> ll_icmp_ult ii l;
    llc_if cmp (doM {
      prev \<leftarrow> arl_nth ai ii;
      free_option afree prev;
      arl_upd ai ii init
    })
    (Mreturn ai)
  }\<close>

lemma pmap_delete_reassemble_present:
  assumes A: \<open>k < length xsi\<close>
  shows \<open>ENTAILS
    (\<upharpoonleft>iarl_assn (xsi[k := dflt]) ai **
     \<upharpoonleft>(list_assn (mk_assn option_assn)) (xs[k := Option.None]) (xsi[k := dflt]))
    (EXS z. \<upharpoonleft>iarl_assn z ai **
       \<upharpoonleft>(list_assn (mk_assn option_assn)) (if k < length xs then xs[k := Option.None] else xs) z)\<close>
proof (cases \<open>length xs = length xsi\<close>)
  case True
  with A have [simp]: \<open>k < length xs\<close> by simp
  show ?thesis
    unfolding ENTAILS_def
    apply simp
    apply (rule entails_exI[where x=\<open>xsi[k := dflt]\<close>])
    by (simp add: entails_refl)
next
  case False
  then show ?thesis
    unfolding ENTAILS_def by (auto simp: entails_def sep_algebra_simps)
qed

lemma pmap_delete_reassemble_absent:
  assumes A: \<open>\<not> k < length xsi\<close>
  shows \<open>ENTAILS
    (\<upharpoonleft>iarl_assn xsi ai ** \<upharpoonleft>(list_assn (mk_assn option_assn)) xs xsi)
    (EXS z. \<upharpoonleft>iarl_assn z ai **
       \<upharpoonleft>(list_assn (mk_assn option_assn)) (if k < length xs then xs[k := Option.None] else xs) z)\<close>
proof (cases \<open>length xs = length xsi\<close>)
  case True
  with A have [simp]: \<open>\<not> k < length xs\<close> by simp
  show ?thesis
    unfolding ENTAILS_def
    apply simp
    apply (rule entails_exI[where x=xsi])
    by (simp add: entails_refl)
next
  case False
  then show ?thesis
    unfolding ENTAILS_def by (auto simp: entails_def sep_algebra_simps)
qed

lemma pmap_delete_rule[vcg_rules]:
  \<open>llvm_htriple
    (\<upharpoonleft>snat.assn k ki ** pmap_assn' xs ai)
    (pmap_delete ki ai)
    (\<lambda>ai'. pmap_assn' (opt_list_delete k xs) ai')\<close>
  unfolding pmap_delete_def opt_list_delete_def
  supply [simp] = pmap_assn_def dflt_is_init[symmetric]
  apply vcg
  subgoal by (rule pmap_delete_reassemble_present)
  apply vcg
  subgoal by (rule pmap_delete_reassemble_absent)
  done

lemma pmap_delete_hnr:
  \<open>(uncurry pmap_delete, uncurry (RETURN oo opt_list_delete))
    \<in> (snat_assn' TYPE(64))\<^sup>k *\<^sub>a pmap_assn'\<^sup>d \<rightarrow>\<^sub>a pmap_assn'\<close>
  unfolding snat_rel_def snat.assn_is_rel[symmetric]
  apply sepref_to_hoare
  by vcg

lemmas pmap_delete_hnr2[sepref_fr_rules] =
  pmap_delete_hnr[FCOMP opt_list_delete_refine]

lemma A_ne_dflt_conv: \<open>A a c = (\<up>(c \<noteq> dflt) ** A a c)\<close>
  by (cases \<open>c = dflt\<close>) (auto simp: UU sep_algebra_simps)

lemma pmap_is_dflt_rule[vcg_rules]:
  \<open>llvm_htriple
     (\<upharpoonleft>(list_assn (mk_assn option_assn)) xs xsi ** \<up>\<^sub>d(i < length xs))
     (is_dflt (xsi ! i))
     (\<lambda>r. \<upharpoonleft>(list_assn (mk_assn option_assn)) xs xsi ** \<upharpoonleft>bool.assn (xs ! i = Option.None) r)\<close>
proof (cases \<open>i < length xs\<close>)
  case True
  note F = list_assn_option_focus[OF True]
  show ?thesis
  proof (cases \<open>xs ! i\<close>)
    case None
    show ?thesis
      supply [vcg_rules] = CMP
      unfolding vcg_tag_defs F None option_assn_None_conv
      by vcg
  next
    case (Some y)
    show ?thesis
      supply [vcg_rules] = CMP
      unfolding vcg_tag_defs F Some option_assn_Some
      apply (subst A_ne_dflt_conv)
      by vcg
  qed
next
  case False
  show ?thesis
    unfolding vcg_tag_defs
    apply (rule htriple_realizable_preI)
    using False by (simp add: sep_algebra_simps)
qed

definition pmap_contains_key :: \<open>64 word \<Rightarrow> 'a pmap_conc \<Rightarrow> 1 word llM\<close> where[llvm_code]:
  \<open>pmap_contains_key ii ai \<equiv> doM {
    l \<leftarrow> arl_len ai;
    isin \<leftarrow> ll_icmp_ult ii l;
    llc_if isin (doM {
      item \<leftarrow> arl_nth ai ii;
      d \<leftarrow> is_dflt item;
      llc_if d (Mreturn 0) (Mreturn 1)
    })
    (Mreturn 0)
  }\<close>

lemma pmap_contains_key_reassemble_absent_slot:
  assumes A: \<open>k < length xsi\<close> and B: \<open>xs ! k = Option.None\<close>
  shows \<open>ENTAILS
    (\<upharpoonleft>(list_assn (mk_assn option_assn)) xs xsi ** \<upharpoonleft>iarl_assn xsi ai)
    ((EXS z. \<upharpoonleft>iarl_assn z ai ** \<upharpoonleft>(list_assn (mk_assn option_assn)) xs z)
      ** \<upharpoonleft>bool.assn (if k < length xs then xs ! k \<noteq> Option.None else False) 0)\<close>
proof (cases \<open>length xs = length xsi\<close>)
  case True
  with A have [simp]: \<open>k < length xs\<close> by simp
  show ?thesis
    unfolding ENTAILS_def
    apply (simp add: B bool.assn_def sep_algebra_simps)
    apply (rule entails_exI[where x=xsi])
    by (simp add: sep_conj_aci entails_refl)
next
  case False
  then show ?thesis
    unfolding ENTAILS_def by (auto simp: entails_def sep_algebra_simps)
qed

lemma pmap_contains_key_reassemble_present_slot:
  assumes A: \<open>k < length xsi\<close> and B: \<open>xs ! k = Option.Some y\<close>
  shows \<open>ENTAILS
    (\<upharpoonleft>(list_assn (mk_assn option_assn)) xs xsi ** \<upharpoonleft>iarl_assn xsi ai)
    ((EXS z. \<upharpoonleft>iarl_assn z ai ** \<upharpoonleft>(list_assn (mk_assn option_assn)) xs z)
      ** \<upharpoonleft>bool.assn (if k < length xs then xs ! k \<noteq> Option.None else False) 1)\<close>
proof (cases \<open>length xs = length xsi\<close>)
  case True
  with A have [simp]: \<open>k < length xs\<close> by simp
  show ?thesis
    unfolding ENTAILS_def
    apply (simp add: B bool.assn_def sep_algebra_simps)
    apply (rule entails_exI[where x=xsi])
    by (simp add: sep_conj_aci entails_refl)
next
  case False
  then show ?thesis
    unfolding ENTAILS_def by (auto simp: entails_def sep_algebra_simps)
qed

lemma pmap_contains_key_reassemble_oob:
  assumes A: \<open>\<not> k < length xsi\<close>
  shows \<open>ENTAILS
    (\<upharpoonleft>iarl_assn xsi ai ** \<upharpoonleft>(list_assn (mk_assn option_assn)) xs xsi)
    ((EXS z. \<upharpoonleft>iarl_assn z ai ** \<upharpoonleft>(list_assn (mk_assn option_assn)) xs z)
      ** \<upharpoonleft>bool.assn (if k < length xs then xs ! k \<noteq> Option.None else False) 0)\<close>
proof (cases \<open>length xs = length xsi\<close>)
  case True
  with A have [simp]: \<open>\<not> k < length xs\<close> by simp
  show ?thesis
    unfolding ENTAILS_def
    apply (simp add: bool.assn_def sep_algebra_simps)
    apply (rule entails_exI[where x=xsi])
    by (simp add: sep_conj_aci entails_refl)
next
  case False
  then show ?thesis
    unfolding ENTAILS_def by (auto simp: entails_def sep_algebra_simps)
qed

lemma pmap_contains_key_rule[vcg_rules]:
  \<open>llvm_htriple
    (\<upharpoonleft>snat.assn k ki ** pmap_assn' xs ai)
    (pmap_contains_key ki ai)
    (\<lambda>r. pmap_assn' xs ai ** \<upharpoonleft>bool.assn (opt_list_contains_key k xs) r)\<close>
  unfolding pmap_contains_key_def opt_list_contains_key_def
  supply [simp] = pmap_assn_def
  apply vcg
  subgoal by (rule pmap_contains_key_reassemble_absent_slot)
  apply vcg
  subgoal by (rule pmap_contains_key_reassemble_present_slot)
  apply vcg
  subgoal by (rule pmap_contains_key_reassemble_oob)
  done

lemma pmap_contains_key_hnr:
  \<open>(uncurry pmap_contains_key, uncurry (RETURN oo opt_list_contains_key))
    \<in> (snat_assn' TYPE(64))\<^sup>k *\<^sub>a pmap_assn'\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding snat_rel_def snat.assn_is_rel[symmetric]
    bool1_rel_def bool.assn_is_rel[symmetric]
  apply sepref_to_hoare
  by vcg

lemmas pmap_contains_key_hnr2[sepref_fr_rules] =
  pmap_contains_key_hnr[FCOMP opt_list_contains_key_refine]

lemma pmap_lookup_reassemble_present:
  assumes A: \<open>k < length xsi\<close>
  shows \<open>ENTAILS
    (\<upharpoonleft>iarl_assn (xsi[k := dflt]) ai ** \<upharpoonleft>(list_assn (mk_assn option_assn)) xs xsi)
    ((EXS z. \<upharpoonleft>iarl_assn z ai **
        \<upharpoonleft>(list_assn (mk_assn option_assn)) (xs[k := Option.None]) z)
     ** option_assn (if k < length xs then xs ! k else Option.None) (xsi ! k))\<close>
proof (cases \<open>length xs = length xsi\<close>)
  case True
  with A have K: \<open>k < length xs\<close> by simp
  show ?thesis
    unfolding ENTAILS_def
    apply (simp add: K list_assn_option_focus[OF K] sep_conj_exists)
    apply (rule entails_exI[where x=\<open>xsi[k := dflt]\<close>])
    by (simp add: sep_conj_aci entails_refl)
next
  case False
  then show ?thesis
    unfolding ENTAILS_def by (auto simp: entails_def sep_algebra_simps)
qed

lemma pmap_lookup_reassemble_oob:
  assumes A: \<open>\<not> k < length xsi\<close>
  shows \<open>ENTAILS
    (\<upharpoonleft>iarl_assn xsi ai ** \<upharpoonleft>(list_assn (mk_assn option_assn)) xs xsi)
    ((EXS z. \<upharpoonleft>iarl_assn z ai **
        \<upharpoonleft>(list_assn (mk_assn option_assn)) (xs[k := Option.None]) z)
     ** option_assn (if k < length xs then xs ! k else Option.None) dflt)\<close>
proof (cases \<open>length xs = length xsi\<close>)
  case True
  with A have K: \<open>\<not> k < length xs\<close> by simp
  then have K2: \<open>length xs \<le> k\<close> by simp
  show ?thesis
    unfolding ENTAILS_def
    apply (simp add: K list_update_beyond[OF K2] sep_conj_exists)
    apply (rule entails_exI[where x=xsi])
    by (simp add: sep_conj_aci entails_refl)
next
  case False
  then show ?thesis
    unfolding ENTAILS_def by (auto simp: entails_def sep_algebra_simps)
qed

definition pmap_lookup :: \<open>64 word \<Rightarrow> 'a pmap_conc \<Rightarrow> 'a llM\<close> where[llvm_code]:
  \<open>pmap_lookup ii ai \<equiv> doM {
    l \<leftarrow> arl_len ai;
    b \<leftarrow> ll_icmp_ult ii l;
    llc_if b (doM {
      a \<leftarrow> arl_nth ai ii;
      arl_upd ai ii init;
      Mreturn a
    })
    (Mreturn init)
  }\<close>

lemma pmap_lookup_rule[vcg_rules]:
  \<open>llvm_htriple
    (\<upharpoonleft>snat.assn i ii ** pmap_assn' xs ai)
    (pmap_lookup ii ai)
    (\<lambda>r. pmap_assn' (xs[i := Option.None]) ai ** option_assn (opt_list_lookup i xs) r)\<close>
  unfolding pmap_lookup_def opt_list_lookup_def
  supply [simp] = pmap_assn_def dflt_is_init[symmetric]
  apply vcg
  subgoal by (rule pmap_lookup_reassemble_present)
  apply vcg
  subgoal by (rule pmap_lookup_reassemble_oob)
  done

(* it is questionably, whether this function will ever be useful,
 * unless sepref has some way of recognizing that the map is still
 * alive (but with a hole) *)
lemma pmap_lookup_opt_list_lookup:
  \<open>(uncurry pmap_lookup, uncurry (RETURN oo opt_list_lookup))
  \<in> (snat_assn' TYPE(64))\<^sup>k *\<^sub>a pmap_assn'\<^sup>d \<rightarrow>\<^sub>a option_assn\<close>
  apply sepref_to_hoare
  unfolding snat_rel_def snat.rel_def in_br_conv
  apply vcg
  oops (* Not sure if we even want to finish this one... *)

definition pmap_free :: \<open>'a pmap_conc \<Rightarrow> unit llM\<close> where[llvm_code]:
  \<open>pmap_free ai \<equiv> doM {
    llc_while
      (\<lambda>i. doM{ l \<leftarrow> arl_len ai; ll_icmp_ult i l})
      (\<lambda>i. doM {
        x \<leftarrow> arl_nth ai i;
        free_option afree x; 
        arl_upd ai i init;
        i \<leftarrow> ll_add i (signed_nat 1);
        Mreturn i
      }) (signed_nat 0);
    arl_free ai
  }\<close>

lemma iarl_free_rule[vcg_rules]: \<open>llvm_htriple (\<upharpoonleft>iarl_assn a c) (arl_free c) (\<lambda>_. \<box>)\<close>
  unfolding iarl_assn_def arl_free_def
  by vcg

lemma iarl_free_rl[sepref_frame_free_rules]: \<open>MK_FREE (\<upharpoonleft>iarl_assn) arl_free\<close>
  apply rule
  by (rule iarl_free_rule)

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
  by (metis Cons_nth_drop_Suc append_Cons fold_None length_replicate
            list_update_length replicate_Suc replicate_app_Cons_same)

lemma nulled_prefix_full[simp]:
  \<open>nulled_prefix xs (length xs) = replicate (length xs) Option.None\<close>
  unfolding nulled_prefix_def by simp

lemma list_assn_option_all_None:
  \<open>\<upharpoonleft>(list_assn (mk_assn option_assn)) (replicate n Option.None) xsi = \<up>(xsi = replicate n dflt)\<close>
  apply (induction n arbitrary: xsi; simp)
  by (auto simp: sep_algebra_simps list_assn_cons1_conv option_assn_None_conv)

lemma pmap_free_reassemble_step:
  assumes A: \<open>x < length xsi\<close>
      and B: \<open>x \<le> length xs\<close>
      and RD: \<open>\<flat>\<^sub>psnat.assn (Suc x) rd\<close>
  shows \<open>ENTAILS
    (\<upharpoonleft>iarl_assn (xsi[x := dflt]) ai **
     \<upharpoonleft>(list_assn (mk_assn option_assn)) ((nulled_prefix xs x)[x := Option.None]) (xsi[x := dflt]))
    (EXS t. (EXS i xsi'.
        \<upharpoonleft>snat.assn i rd ** \<upharpoonleft>iarl_assn xsi' ai **
        \<upharpoonleft>(list_assn (mk_assn option_assn)) (nulled_prefix xs i) xsi' **
        \<up>(i \<le> length xs) ** \<up>\<^sub>!(t = length xs - i)) **
      \<up>\<^sub>d((t, length xs - x) \<in> less_than) ** \<box>)\<close>
proof (cases \<open>length xs = length xsi\<close>)
  case True
  with A have K: \<open>x < length xs\<close> by simp
  then have K2: \<open>Suc x \<le> length xs\<close> and K3: \<open>length xs - Suc x < length xs - x\<close>
    by arith+
  show ?thesis
    unfolding ENTAILS_def vcg_tag_defs
    apply (simp add: sep_conj_exists)
    apply (rule entails_exI[where x=\<open>length xs - Suc x\<close>])
    apply (rule entails_exI[where x=\<open>Suc x\<close>])
    apply (rule entails_exI[where x=\<open>xsi[x := dflt]\<close>])
    using RD K K2 K3
    by (simp add: snat.assn_pure[THEN extract_pure_assn]
                  sep_algebra_simps pred_lift_extract_simps)
next
  case False
  with B have \<open>length ((nulled_prefix xs x)[x := Option.None]) \<noteq> length (xsi[x := dflt])\<close>
    by simp
  then show ?thesis
    unfolding ENTAILS_def by (auto simp: entails_def sep_algebra_simps)
qed

lemma pmap_free_reassemble_exit:
  assumes A: \<open>\<not> x < length xsi\<close>
      and B: \<open>x \<le> length xs\<close>
  shows \<open>ENTAILS (\<upharpoonleft>(list_assn (mk_assn option_assn)) (nulled_prefix xs x) xsi) \<box>\<close>
proof (cases \<open>length xs = length xsi\<close>)
  case True
  with A B have X: \<open>x = length xs\<close> by simp
  show ?thesis
    unfolding ENTAILS_def
    by (simp add: X list_assn_option_all_None entails_def
                  sep_algebra_simps pred_lift_extract_simps)
next
  case False
  with B have \<open>length (nulled_prefix xs x) \<noteq> length xsi\<close> by simp
  then show ?thesis
    unfolding ENTAILS_def by (auto simp: entails_def sep_algebra_simps)
qed

lemma pmap_free_rule[sepref_frame_free_rules]: \<open>MK_FREE pmap_assn' pmap_free\<close>
  apply rule
  unfolding pmap_free_def
  subgoal for xs ai
    apply (rewrite annotate_llc_while[where
    I="\<lambda>ii t. EXS i xsi. \<upharpoonleft>snat.assn i ii
      ** \<upharpoonleft>iarl_assn xsi ai
      ** \<upharpoonleft>(list_assn (mk_assn option_assn)) (nulled_prefix xs i) xsi
      ** \<up>(i\<le>length xs)
      ** \<up>\<^sub>!(t = length xs - i )"
    and R="less_than"
    ])
    supply [simp] = pmap_assn_def dflt_is_init[symmetric]
    apply vcg_monadify
    apply vcg
    subgoal by (rule pmap_free_reassemble_step)
    apply vcg
    subgoal by (rule pmap_free_reassemble_exit)
    done
  done

end

section \<open>Boxing\<close>
text \<open>To actually put arbitrary (impure) objects into our pmaps, we need to wrap them.\<close>

definition box_assn :: \<open>('a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn) \<Rightarrow> ('a, 'c ptr) dr_assn\<close> where
  \<open>box_assn A \<equiv> mk_assn (\<lambda>x p. EXS c. \<upharpoonleft>ll_bpto c p ** A x c)\<close>

lemma box_assn_null[simp]: \<open>\<upharpoonleft>(box_assn A) x null = sep_false\<close>
  unfolding box_assn_def by (auto simp: sep_algebra_simps)

subsection \<open>Operations\<close>

definition box_new :: \<open>'c::llvm_rep \<Rightarrow> 'c ptr llM\<close> where [llvm_code, llvm_inline]:
  \<open>box_new c \<equiv> ll_ref c\<close>

lemma box_new_rule[vcg_rules]:
  \<open>llvm_htriple (A x c) (box_new c) (\<lambda>p. \<upharpoonleft>(box_assn A) x p)\<close>
  unfolding box_new_def box_assn_def by vcg

definition box_open :: \<open>'c::llvm_rep ptr \<Rightarrow> 'c llM\<close> where [llvm_code]:
  \<open>box_open p \<equiv> doM {
    c \<leftarrow> ll_load p;
    ll_free p;
    Mreturn c
  }\<close>

definition BOX :: \<open>'v \<Rightarrow> 'v\<close> where \<open>BOX x \<equiv> x\<close>
definition UNBOX :: \<open>'v \<Rightarrow> 'v\<close> where \<open>UNBOX x \<equiv> x\<close>

lemma BOX_hnr[sepref_fr_rules]:
  \<open>(box_new, RETURN o BOX)
    \<in> A\<^sup>d \<rightarrow>\<^sub>a \<upharpoonleft>(box_assn A)\<close>
  apply sepref_to_hoare
  unfolding BOX_def box_new_def box_assn_def
  by vcg

lemma UNBOX_hnr[sepref_fr_rules]:
  \<open>(box_open, RETURN o UNBOX)
    \<in> (\<upharpoonleft>(box_assn A))\<^sup>d \<rightarrow>\<^sub>a A\<close>
  apply sepref_to_hoare
  unfolding UNBOX_def box_open_def box_assn_def
  by vcg

lemma box_open_rule[vcg_rules]:
  \<open>llvm_htriple (\<upharpoonleft>(box_assn A) x p) (box_open p) (\<lambda>c. A x c)\<close>
  unfolding box_open_def box_assn_def by vcg

definition box_free :: \<open>('c \<Rightarrow> unit llM) \<Rightarrow> 'c::llvm_rep ptr \<Rightarrow> unit llM\<close> where [llvm_code]:
  \<open>box_free fr p \<equiv> doM {
    c \<leftarrow> ll_load p;
    fr c;
    ll_free p
  }\<close>

lemma box_free_rule:
  assumes [THEN MK_FREED, vcg_rules]: \<open>MK_FREE A fr\<close>
  shows \<open>MK_FREE (\<upharpoonleft>(box_assn A)) (box_free fr)\<close>
  apply rule
  unfolding box_free_def box_assn_def
  by vcg

subsection \<open>Null test\<close>

context begin
interpretation llvm_prim_arith_setup .

lemma ll_ptrcmp_eq_null_simp:
  \<open>ll_ptrcmp_eq a null = doM { Mreturn (from_bool (a = null))}\<close>
  by (vcg_normalize; simp add: eq_commute[of null])

end

definition box_is_null :: \<open>'c::llvm_rep ptr \<Rightarrow> 1 word llM\<close> where [llvm_code, llvm_inline]:
  \<open>box_is_null p \<equiv> ll_ptrcmp_eq p null\<close>

lemma box_is_null_rule[vcg_rules]:
  \<open>llvm_htriple \<box> (box_is_null p) (\<lambda>r. \<upharpoonleft>bool.assn (p = null) r)\<close>
  unfolding box_is_null_def ll_ptrcmp_eq_null_simp
  supply [simp] = bool.assn_def
  by vcg

subsection \<open>The boxed map instance\<close>

locale boxed_pmap = freeable_assn A afree
  for A :: \<open>'a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn\<close> and afree
begin

text \<open>The qualifier separates the box-level \<open>freeable_assn\<close> instance (and its list
  operations) from the inherited element-level one.\<close>

sublocale bx: array_pmap \<open>null\<close> \<open>\<upharpoonleft>(box_assn A)\<close> box_is_null \<open>box_free afree\<close>
  apply unfold_locales
  subgoal by simp
  subgoal by (rule box_is_null_rule)
  subgoal by (rule box_free_rule[OF afree_free])
  subgoal by simp
  done

end

section \<open>Copying Partial Maps\<close>
text \<open>Our previous map did not assume that container elements can be copied.
  This implies that extracting function (like lookup) will move ownership out of the map.
  If we assume that elements can be copied, we can also provide an alternative variant
  were the map is kept intact and the caller isn't required to reassemble it.\<close>

locale copying_array_pmap =
  array_pmap dflt A is_dflt afree + copyable_assn A afree acopy
  for dflt and A :: \<open>'b \<Rightarrow> 'a::llvm_rep \<Rightarrow> assn\<close> and is_dflt and afree
  and acopy :: \<open>'a \<Rightarrow> 'a llM\<close>
begin

definition[llvm_inline]: \<open>copy_option cp c \<equiv> doM { d \<leftarrow> is_dflt c; llc_if d (Mreturn c) (cp c) } \<close>

lemma copy_option_rule[vcg_rules]:
  \<open>llvm_htriple
     (option_assn a c)
     (copy_option acopy c)
     (\<lambda>r. option_assn a c ** option_assn a r)\<close>
  supply [vcg_rules] = CMP
  supply [simp] = option_assn_None_conv UU
  unfolding copy_option_def
  apply (cases a; simp)
  apply vcg
  done

lemma pmap_copy_slot_rule[vcg_rules]:
  \<open>llvm_htriple
     (\<upharpoonleft>(list_assn (mk_assn option_assn)) xs xsi ** \<up>\<^sub>d(i < length xs))
     (copy_option acopy (xsi ! i))
     (\<lambda>r. \<upharpoonleft>(list_assn (mk_assn option_assn)) xs xsi ** option_assn (xs ! i) r)\<close>
proof (cases \<open>i < length xs\<close>)
  case True
  show ?thesis
    unfolding vcg_tag_defs list_assn_option_focus[OF True]
    by vcg
next
  case False
  show ?thesis
    unfolding vcg_tag_defs
    apply (rule htriple_realizable_preI)
    using False by (simp add: sep_algebra_simps)
qed

definition cpmap_lookup :: \<open>64 word \<Rightarrow> 'a pmap_conc \<Rightarrow> 'a llM\<close> where[llvm_code]:
  \<open>cpmap_lookup ii ai \<equiv> doM {
    l \<leftarrow> arl_len ai;
    b \<leftarrow> ll_icmp_ult ii l;
    llc_if b (doM {
      a \<leftarrow> arl_nth ai ii;
      a2 \<leftarrow> copy_option acopy a;
      arl_upd ai ii a2;
      Mreturn a
    })
    (Mreturn init)
  }\<close>

lemma cpmap_lookup_reassemble_hit:
  assumes A: \<open>i < length xsi\<close>
  shows \<open>ENTAILS
    (\<upharpoonleft>iarl_assn (xsi[i := rb]) ai **
     \<upharpoonleft>(list_assn (mk_assn option_assn)) xs xsi **
     option_assn (xs ! i) rb)
    ((EXS z. \<upharpoonleft>iarl_assn z ai ** \<upharpoonleft>(list_assn (mk_assn option_assn)) xs z)
     ** option_assn (if i < length xs then xs ! i else Option.None) (xsi ! i))\<close>
proof (cases \<open>length xs = length xsi\<close>)
  case True
  with A have K: \<open>i < length xs\<close> by simp
  show ?thesis
    unfolding ENTAILS_def
    apply (simp add: A K list_assn_option_focus[OF K] sep_conj_exists)
    apply (rule entails_exI[where x=\<open>xsi[i := rb]\<close>])
    by (simp add: A sep_conj_aci)
next
  case False
  then show ?thesis
    unfolding ENTAILS_def by (auto simp: entails_def sep_algebra_simps)
qed

lemma cpmap_lookup_reassemble_miss:
  assumes A: \<open>\<not> i < length xsi\<close>
  shows \<open>ENTAILS
    (\<upharpoonleft>iarl_assn xsi ai ** \<upharpoonleft>(list_assn (mk_assn option_assn)) xs xsi)
    ((EXS z. \<upharpoonleft>iarl_assn z ai ** \<upharpoonleft>(list_assn (mk_assn option_assn)) xs z)
     ** option_assn (if i < length xs then xs ! i else Option.None) init)\<close>
proof (cases \<open>length xs = length xsi\<close>)
  case True
  with A have K: \<open>\<not> i < length xs\<close> by simp
  show ?thesis
    unfolding ENTAILS_def
    apply (simp add: K dflt_is_init[symmetric] sep_algebra_simps)
    apply (rule entails_exI[where x=xsi])
    by (simp add: sep_conj_aci)
next
  case False
  then show ?thesis
    unfolding ENTAILS_def by (auto simp: entails_def sep_algebra_simps)
qed

lemma cpmap_lookup_rule[vcg_rules]:
  \<open>llvm_htriple
    (\<upharpoonleft>snat.assn i ii ** pmap_assn' xs ai)
    (cpmap_lookup ii ai)
    (\<lambda>r. pmap_assn' xs ai ** option_assn (opt_list_lookup i xs) r)\<close>
  unfolding cpmap_lookup_def opt_list_lookup_def
  supply [simp] = pmap_assn_def
  apply vcg
  subgoal by (rule cpmap_lookup_reassemble_hit)
  apply vcg
  subgoal by (rule cpmap_lookup_reassemble_miss)
  done

lemma cpmap_lookup_hnr:
  \<open>(uncurry cpmap_lookup, uncurry (RETURN oo opt_list_lookup))
  \<in> (snat_assn' TYPE(64))\<^sup>k *\<^sub>a pmap_assn'\<^sup>k \<rightarrow>\<^sub>a option_assn\<close>
  unfolding snat_rel_def snat.assn_is_rel[symmetric]
  apply sepref_to_hoare
  by vcg

lemmas cpmap_lookup_hnr2[sepref_fr_rules] =
  cpmap_lookup_hnr[FCOMP opt_list_lookup_refine]

lemma opt_list_the_lookup_conv:
  \<open>opt_list_contains_key k m \<Longrightarrow> opt_list_lookup k m = Option.Some (opt_list_the_lookup k m)\<close>
  unfolding opt_list_contains_key_def opt_list_lookup_def opt_list_the_lookup_def
  by (auto split: if_splits)

lemma cpmap_the_lookup_hnr:
  \<open>(uncurry cpmap_lookup, uncurry (RETURN oo opt_list_the_lookup))
  \<in> [\<lambda>(k,xs). opt_list_contains_key k xs]\<^sub>a (snat_assn' TYPE(64))\<^sup>k *\<^sub>a pmap_assn'\<^sup>k \<rightarrow> A\<close>
  unfolding snat_rel_def snat.assn_is_rel[symmetric]
  supply [simp] = opt_list_the_lookup_conv
  by (sepref_to_hoare; vcg)

lemmas cpmap_the_lookup_hnr2[sepref_fr_rules] =
  cpmap_the_lookup_hnr[FCOMP opt_list_the_lookup_refine]

end

subsection \<open>Copyable boxes\<close>
text \<open>To, again, use our copying pmap with arbitrary impure objects, we need to
  wrap the object in a box. Therefore we need some copy setup for boxes.\<close>

definition box_copy :: \<open>('c \<Rightarrow> 'c llM) \<Rightarrow> 'c::llvm_rep ptr \<Rightarrow> 'c ptr llM\<close> where[llvm_code]:
  \<open>box_copy acopy p \<equiv> doM {
    c \<leftarrow> ll_load p;
    c' \<leftarrow> acopy c;
    ll_ref c' 
  }\<close>

lemma is_copy_triple:
  assumes \<open>is_copy A acopy\<close>
  shows \<open>llvm_htriple (A x c) (acopy c) (\<lambda>r. A x c ** A x r)\<close>
proof -
  note HNR = assms[unfolded is_copy_def, to_hnr, unfolded autoref_tag_defs]
  note HT = HNR[THEN hn_refineD]
  show ?thesis
    apply (rule htriple_ent_pre[OF _ htriple_ent_post[OF _ HT]])
    unfolding hn_ctxt_def apply (rule entails_refl)
    subgoal by (auto simp: entails_def sep_algebra_simps)
    subgoal by simp
    done
qed

lemma box_copy_rule:
  assumes \<open>is_copy A acopy\<close>
    shows \<open>is_copy \<upharpoonleft>(box_assn A) (box_copy acopy)\<close>
  unfolding box_copy_def is_copy_def box_assn_def
  apply sepref_to_hoare
  supply [vcg_rules] = is_copy_triple[OF assms(1)]
  by vcg

locale boxed_copying_pmap = boxed_pmap A afree + copyable_assn A afree acopy
  for A :: \<open>'a \<Rightarrow> 'b::llvm_rep \<Rightarrow> assn\<close> and afree and acopy
begin

sublocale bx: copying_array_pmap \<open>null\<close> \<open>\<upharpoonleft>(box_assn A)\<close> \<open>box_is_null\<close> \<open>box_free afree\<close> \<open>box_copy acopy\<close>
  apply unfold_locales
  by ((rule box_is_null_rule box_free_rule[OF afree_free]
        box_copy_rule[OF acopy_is_copy, unfolded is_copy_def] | simp)+)?

end

section \<open>Experiments\<close>

text \<open>Sanity tests: instantiate the copying map with boxed 64-bit numbers
  (a \<open>nat \<rightharpoonup> nat\<close> map at the HOL level) and let sepref synthesize small test
  programs written against the IICF map interface. This exercises the registered
  \<open>sepref_fr_rules\<close> (empty/update/delete/contains\_key/lookup/the\_lookup) and the
  frame free rules (\<open>pmap_free\<close>, lifted through \<open>hr_comp\<close> by @{thm MK_FREE_hrcompI}).\<close>

experiment
begin

text \<open>A copy function for boxes with pure content: load and re-allocate.\<close>
definition box_copy :: \<open>'c::llvm_rep ptr \<Rightarrow> 'c ptr llM\<close> where [llvm_code, llvm_inline]:
  \<open>box_copy p \<equiv> doM { c \<leftarrow> ll_load p; ll_ref c }\<close>

lemma box_copy_pure_rule[vcg_rules]:
  \<open>llvm_htriple
    (\<upharpoonleft>(box_assn (pure R)) x p)
    (box_copy p)
    (\<lambda>r. \<upharpoonleft>(box_assn (pure R)) x p ** \<upharpoonleft>(box_assn (pure R)) x r)\<close>
  unfolding box_copy_def box_assn_def
  supply [simp] = pure_app_eq
  by vcg

lemma box_copy_hnr:
  \<open>(box_copy, RETURN o COPY) \<in> (\<upharpoonleft>(box_assn (pure R)))\<^sup>k \<rightarrow>\<^sub>a \<upharpoonleft>(box_assn (pure R))\<close>
  apply sepref_to_hoare
  apply (fold pure_def)
  by vcg

interpretation P: copying_array_pmap
  null \<open>\<upharpoonleft>(box_assn (snat_assn' TYPE(64)))\<close> box_is_null
  \<open>box_free (\<lambda>_. Mreturn ())\<close> box_copy
  apply unfold_locales
  subgoal by simp
  subgoal by (rule box_is_null_rule)
  subgoal by (rule box_free_rule[OF mk_free_pure])
  subgoal by simp
  subgoal by (rule box_copy_hnr)
  done

sepref_definition pmap_test1_impl is
  \<open>uncurry (\<lambda>k v. do {
      let m = op_map_empty;
      let m = op_map_update k (BOX v) m;
      let b\<^sub>1 = op_map_contains_key k m;
      let m = op_map_delete k m;
      let b\<^sub>2 = op_map_contains_key k m;
      RETURN (b\<^sub>1 \<and> \<not> b\<^sub>2)
    })\<close>
  :: \<open>[\<lambda>(k, v). k + 1 < max_snat 64]\<^sub>a
      (snat_assn' TYPE(64))\<^sup>k *\<^sub>a (snat_assn' TYPE(64))\<^sup>k \<rightarrow> bool1_assn\<close>
  by sepref

text \<open>Round-trip a value through the map (guarded lookup, key present by construction).\<close>
sepref_definition pmap_test2_impl is
  \<open>uncurry (\<lambda>k v. do {
      let m = op_map_update k (BOX v) op_map_empty;
      let x = op_map_the_lookup k m;
      RETURN (UNBOX x)
    })\<close>
  :: \<open>[\<lambda>(k, v). k + 1 < max_snat 64]\<^sub>a
      (snat_assn' TYPE(64))\<^sup>k *\<^sub>a (snat_assn' TYPE(64))\<^sup>k \<rightarrow> snat_assn' TYPE(64)\<close>
  by sepref

sepref_definition pmap_test3_impl is
  \<open>uncurry (\<lambda>k v. do {
      let m = op_map_update k (BOX v) op_map_empty;
      RETURN (op_map_lookup k m)
    })\<close>
  :: \<open>[\<lambda>(k, v). k + 1 < max_snat 64]\<^sub>a
      (snat_assn' TYPE(64))\<^sup>k *\<^sub>a (snat_assn' TYPE(64))\<^sup>k
      \<rightarrow> hr_comp P.option_assn (\<langle>nat_rel\<rangle>option_rel)\<close>
  by sepref

end

text \<open>Second experiment: an IMPURE element type. The map stores boxed dynamic arrays
  (\<open>al_assn\<close>) of 64-bit numbers, i.e. a \<open>nat \<rightharpoonup> nat list\<close> map at the HOL level. This
  exercises the @{locale boxed_copying_pmap} locale: the copying lookup duplicates the
  boxed array (\<open>box_copy arl_copy\<close>) while the map stays intact.\<close>

experiment
begin

text \<open>Array-list copy, replicated from
  \<open>isabelle_llvm/thys/examples/sorting/Sorting_Strings.thy\<close>
  (the sorting examples are not part of the \<open>Isabelle_LLVM\<close> session image).\<close>
definition arl_copy :: \<open>('a::llvm_rep,'l::len2) array_list \<Rightarrow> ('a,'l) array_list llM\<close>
  where [llvm_code]: \<open>arl_copy al \<equiv> doM {
    let (l,c,a) = al;
    a' \<leftarrow> narray_new TYPE('a) l;
    arraycpy a' a l;
    Mreturn (l,l,a')
  }\<close>

lemma arl_copy_rule[vcg_rules]: \<open>llvm_htriple
  (\<upharpoonleft>arl_assn xs xsi) (arl_copy xsi) (\<lambda>r. \<upharpoonleft>arl_assn xs xsi ** \<upharpoonleft>arl_assn xs r)\<close>
  unfolding arl_copy_def arl_assn_def arl_assn'_def
  by vcg

lemma al_copy_hnr: \<open>(arl_copy, RETURN o op_list_copy) \<in> (al_assn A)\<^sup>k \<rightarrow>\<^sub>a al_assn A\<close>
  unfolding al_assn_def hr_comp_def
  apply sepref_to_hoare
  by vcg

lemma al_copy_is_copy: \<open>is_copy (al_assn A) arl_copy\<close>
  using al_copy_hnr unfolding is_copy_def COPY_def op_list_copy_def .

abbreviation nl_assn :: \<open>nat list \<Rightarrow> (64 word, 64) array_list \<Rightarrow> assn\<close> where
  \<open>nl_assn \<equiv> al_assn' TYPE(64) (snat_assn' TYPE(64))\<close>

interpretation P: boxed_copying_pmap nl_assn arl_free arl_copy
  apply unfold_locales
  subgoal by (rule al_assn_free)
  subgoal by (rule al_copy_is_copy[unfolded is_copy_def])
  done

text \<open>Store a singleton array under a key, check membership, delete.\<close>
sepref_definition pmap_altest1_impl is
  \<open>uncurry (\<lambda>k v. do {
      let xs = op_list_append (op_al_empty TYPE(64)) v;
      let m = op_map_update k (BOX xs) op_map_empty;
      let b\<^sub>1 = op_map_contains_key k m;
      let m = op_map_delete k m;
      let b\<^sub>2 = op_map_contains_key k m;
      RETURN (b\<^sub>1 \<and> \<not> b\<^sub>2)
    })\<close>
  :: \<open>[\<lambda>(k, v). k + 1 < max_snat 64]\<^sub>a
      (snat_assn' TYPE(64))\<^sup>k *\<^sub>a (snat_assn' TYPE(64))\<^sup>k \<rightarrow> bool1_assn\<close>
  by sepref

text \<open>The copying lookup: read the stored array back TWICE which is only possible because
  \<open>op_map_the_lookup\<close> leaves the map intact.\<close>
sepref_definition pmap_altest2_impl is
  \<open>uncurry (\<lambda>k v. do {
      let xs = op_list_append (op_al_empty TYPE(64)) v;
      let m = op_map_update k (BOX xs) op_map_empty;
      let x\<^sub>1 = op_map_the_lookup k m;
      let x\<^sub>2 = op_map_the_lookup k m;
      RETURN (op_list_length (UNBOX x\<^sub>1) = op_list_length (UNBOX x\<^sub>2))
    })\<close>
  :: \<open>[\<lambda>(k, v). k + 1 < max_snat 64]\<^sub>a
      (snat_assn' TYPE(64))\<^sup>k *\<^sub>a (snat_assn' TYPE(64))\<^sup>k \<rightarrow> bool1_assn\<close>
  by sepref

end

end
