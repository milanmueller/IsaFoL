theory IICF_PartialMap
  imports
    Isabelle_LLVM.IICF
    Isabelle_LLVM.Proto_EOArray
    Isabelle_LLVM.LLVM_DS_Block_Alloc
begin

text \<open>This theory implement a key-value map.
  It refines @{typ \<open>'a option list\<close>}, i.e. a partial map.
  It is inspired by @{theory Isabelle_LLVM.Proto_EOArray}
  and uses a similar construction.\<close>

text \<open>TODO list \<emdash> coverage of the @{theory Isabelle_LLVM.IICF_Map} interface
  Done:
    (none yet)

  Missing, core operations:
    \<^item> [ ] \<open>op_map_empty\<close>        (fresh @{term narray_assn}; slots are \<open>init = dflt = None\<close>)
    \<^item> [ ] \<open>op_map_update\<close>       (must free the overwritten value if the key was present)
    \<^item> [ ] \<open>op_map_delete\<close>       (must free the removed value; leaves a \<open>dflt\<close> hole)
    \<^item> [ ] \<open>op_map_contains_key\<close> (pure; the \<open>is_dflt\<close> null test, no ownership transfer)
    \<^item> [ ] \<open>op_map_is_empty\<close>     (needs a size field or a full scan)

  Missing, extract a value (element leaves or is copied out of the map):
    \<^item> [ ] \<open>op_map_lookup\<close>       (returns an option)
    \<^item> [ ] \<open>op_map_the_lookup\<close>   (guarded, key must be present); like @{term op_list_hd}
                                 this needs a copying variant (keep the map intact,
                                 requires an element copy) and possibly a destructive one

  Infrastructure (not interface ops):
    \<^item> [ ] \<open>MK_FREE\<close> deep free   (free each present slot's value, then the array)
    \<^item> [ ] \<open>COPY\<close> deep copy      (needs an element copy)\<close>

section \<open>High level map implementation by option list\<close>
text \<open>First, we implement maps using lists of optionals. We then later compose with the low level implementation.\<close>

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
definition \<open>opt_map_is_empty \<equiv> list_all (\<lambda>x. x = None)\<close>
definition \<open>opt_map_lookup k m \<equiv> if k < length m then m!k else None\<close>
definition \<open>opt_map_the_lookup k m \<equiv> the (m!k)\<close>

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

lemma opt_map_is_empty_refine:
  \<open>(RETURN o opt_map_is_empty, RETURN o op_map_is_empty)
    \<in> opt_list_map_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  by (auto simp: opt_list_map_rel_def in_br_conv opt_map_is_empty_def opt_list_\<alpha>_def list_all_length fun_eq_iff)

lemma opt_map_lookup_refine:
  \<open>(uncurry (RETURN oo opt_map_lookup), uncurry (RETURN oo op_map_lookup))
    \<in> nat_rel \<times>\<^sub>r opt_list_map_rel \<rightarrow>\<^sub>f \<langle>\<langle>Id\<rangle>option_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  by (auto simp: opt_list_map_rel_def in_br_conv opt_map_lookup_def opt_list_\<alpha>_def)

lemma opt_map_the_lookup_refine:
  \<open>(uncurry (RETURN oo opt_map_the_lookup), uncurry (RETURN oo op_map_the_lookup))
    \<in> [\<lambda>(k,m). m k \<noteq> None]\<^sub>f nat_rel \<times>\<^sub>r opt_list_map_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  by (auto simp: opt_list_map_rel_def in_br_conv opt_map_the_lookup_def opt_list_\<alpha>_def split: if_splits)

section \<open>Low-level implementation\<close>
text \<open>Now we implement our option list on llvm level.\<close>

subsection \<open>Init-tailed array list\<close>
text \<open>@{term arl_assn} does not fill the tail with @{term init} on resize, so we'd have to initialize
  each element. Therefore we define a new init array list and reuse @{term arl_assn} where possible.\<close>

definition iarl_assn :: \<open>('a::llvm_rep list, ('a,'l::len2) array_list) dr_assn\<close> where
  \<open>iarl_assn \<equiv> mk_assn (\<lambda>xs (li,ci,ai). EXS c a.
      \<upharpoonleft>snat.assn (length xs) li ** \<upharpoonleft>snat.assn c ci ** \<upharpoonleft>narray_assn a ai
      ** \<up>(4 < LENGTH('l) \<and> length xs \<le> c \<and> c = length a
            \<and> a = xs @ replicate (c - length xs) init))\<close>

lemma iarl_new_raw_rule[vcg_rules]:
  \<open>llvm_htriple (\<up>(4 < LENGTH('l)))
     (arl_new_raw :: ('a::llvm_rep,'l::len2) array_list llM)
     (\<lambda>r. \<upharpoonleft>iarl_assn ([]::'a list) r)\<close>
  unfolding arl_new_raw_def arl_initial_size_def iarl_assn_def
  apply (vcg_monadify)
  by vcg'

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

(* TODO: implement resizing (that's the hard part) *)
    
locale array_pmap = dflt_option_private +
  fixes afree :: \<open>'a \<Rightarrow> unit llM\<close>
  (* We assume init to be identified by \<open>None\<close>. That way we get initialization
   * for free instead of having to initialize every element in the array *)
  assumes dflt_is_init: \<open>dflt = init\<close>
  assumes Afree: \<open>MK_FREE A afree\<close>
begin

text \<open>Very similar to @{term nao_assn}, but we use the option assertion from the locale.
  Also, we use @{term arl_assn} to reuse it's resizing machinery.\<close>

(* We opt into 64-bit keys here, this makes proofs less noisy but maybe should be generalized at some point? *)
definition \<open>pmap_assn \<equiv> mk_assn (\<lambda>xs (p :: (_, 64) array_list). EXS xsi. \<upharpoonleft>arl_assn xsi p ** \<upharpoonleft>(list_assn (mk_assn option_assn)) xs xsi)\<close>
abbreviation \<open>pmap_assn' \<equiv> \<upharpoonleft>pmap_assn\<close>
type_synonym 'c pmap_conc = \<open>('c, 64) array_list\<close>

lemma pmap_empty_hnr[sepref_fr_rules]:
  \<open>(uncurry0 arl_new_raw, uncurry0 (RETURN opt_list_empty)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a pmap_assn'\<close>
  supply [simp] = pmap_assn_def opt_list_empty_def
  by (sepref_to_hoare; vcg)

(* note that our update takes ownership *)
definition pmap_update :: \<open>64 word \<Rightarrow> 'a \<Rightarrow> 'a pmap_conc \<Rightarrow> 'a pmap_conc llM\<close> where[llvm_code]:
  \<open>pmap_update ki vi ai \<equiv> doM {
    l \<leftarrow> arl_len ai; 
    if (l < ki) then doM {
      prev \<leftarrow> arl_nth ai ki;
      free_option afree prev;
      arl_upd ai ki vi
    } else doM {
    
    }
  }\<close>

end

definition \<open>box_assn A \<equiv> mk_assn (\<lambda>x p. EXS c. \<upharpoonleft>ll_bpto p c ** A x c)\<close>

end
