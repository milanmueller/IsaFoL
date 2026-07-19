(*
  Note that large portions of this file were generated using the
  "Fable 5" language model by Anthropic. An in-depth human
  review has not been carried out yet.

  Responsible: Milan Mueller, ALU Freiburg (student)
*)

theory Shared_Vars_Assn
  imports String_Assn
begin

section \<open>The shared-variables store\<close>

text \<open>LLVM replacement for the shared-variables store of
  \<open>LPAC_Perfectly_Shared_Vars.thy\<close> (in \<open>PAC_Checker2\<close>): the old middle layer
  \<open>shared_vars_c = 'string list \<times> ('string, nat) fmap\<close> (a growing array of names
  plus a name-to-index hash map, both over \<^emph>\<open>pure\<close> literal strings) becomes a triple

    \<^item> \<open>n :: nat\<close>, the next fresh index (replacing \<open>length \<V>\<close>);
    \<^item> \<open>\<V> :: nat \<rightharpoonup> char list\<close>, index to name: a pam instance with owning string
      values (\<open>vnm_assn\<close>), where \<open>get_var_name\<close> is lookup-with-copy;
    \<^item> \<open>\<A> :: char list \<rightharpoonup> nat\<close>, name to index: the string hash map \<open>svm_assn\<close>
      of \<^file>\<open>String_Assn.thy\<close>.

  Strings are heap-owned here, so an import stores \<^emph>\<open>two\<close> copies of the name (one
  per map). The \<open>memory_allocation\<close> result of the old \<open>find_new_idx\<close> is a plain
  failure flag (\<open>bool\<close>, \<open>True\<close> = allocation failed) at this layer; the
  \<open>memory_allocation\<close> datatype lives in the LPAC theories, and its LLVM
  representation is a separate decision. The refinement lemmas towards the
  abstract \<open>\<dots>S\<close> operations (\<open>import_variableS\<close> etc. from
  \<open>LPAC_Perfectly_Shared\<close>) live downstream in \<open>PAC_Checker2\<close>, next to the
  checker.\<close>

subsection \<open>The index \<open>\<rightarrow>\<close> name map (\<open>vnm\<close>)\<close>

text \<open>Instance of the assoc map (\<^file>\<open>IICF_Assoc_Map.thy\<close>) with owning open-list
  strings as values: \<open>vfree = os_delete\<close>, \<open>vcopy = strl_copy\<close> (the-lookup returns a
  fresh copy of the stored name). Mirrors the \<open>polys_assn\<close> instance in
  \<open>Polys_Assn.thy\<close>, but stays at the \<open>\<rightharpoonup>\<close> level (no fmap step needed here).\<close>

definition vnm_assn :: \<open>(nat \<rightharpoonup> char list) \<Rightarrow> 8 word os_list pam_impl \<Rightarrow> assn\<close> where
  \<open>vnm_assn \<equiv> pam_map_assn (mk_assn strl_assn)\<close>

lemma vnm_assn_intf[intf_of_assn]:
  \<open>intf_of_assn vnm_assn TYPE((nat, char list) i_map)\<close>
  by simp

text \<open>Producer op with its own name (\<open>map_custom_empty\<close> idiom).\<close>

definition op_vnm_empty :: \<open>nat \<rightharpoonup> char list\<close> where [simp]:
  \<open>op_vnm_empty \<equiv> op_map_empty\<close>

interpretation vnm: map_custom_empty op_vnm_empty
  by unfold_locales simp

lemmas vnm_empty_hnr[sepref_fr_rules] =
  pam_empty_hnr[where V = \<open>mk_assn strl_assn\<close>, folded vnm_assn_def op_vnm_empty_def]

lemmas vnm_upd_hnr[sepref_fr_rules] =
  pam_update_hnr[where V = strl_assn, unfolded strl_dr_assn_conv,
    OF os_assn_free[where A = char_assn], folded vnm_assn_def]

lemmas vnm_the_lookup_hnr[sepref_fr_rules] =
  pam_the_lookup_hnr[where V = \<open>mk_assn strl_assn\<close>, unfolded strl_dr_assn_conv,
    OF strl_copy_rule, folded vnm_assn_def]

lemma vnm_assn_free[sepref_frame_free_rules]:
  \<open>MK_FREE vnm_assn (pam_free_impl os_delete)\<close>
  unfolding vnm_assn_def
  by (rule pam_map_assn_free[where V = \<open>mk_assn strl_assn\<close>,
        unfolded strl_dr_assn_conv, OF os_assn_free])

subsubsection \<open>First-order specializations (code export)\<close>

text \<open>The \<open>Polys_Assn.thy\<close> export pattern: named first-order bucket walks with
  \<open>[llvm_code]\<close> equations, \<open>[llvm_pre_simp]\<close> folds so the \<open>[llvm_inline]\<close>d map-level
  wrappers expose exactly these constants.\<close>

definition \<open>vnm_bucket_update \<equiv> pam_bucket_update_impl os_delete\<close>

lemma vnm_bucket_update_simps[llvm_code]:
  \<open>vnm_bucket_update k v p = (if p = null then os_prepend (k, v) null
     else doM {
       n \<leftarrow> ll_load p;
       eq \<leftarrow> ll_icmp_eq (fst (node.val n)) k;
       if to_bool eq then doM {
                os_delete (snd (node.val n));
                ll_store (Node (k, v) (node.next n)) p;
                Mreturn p
              }
       else doM {
        q \<leftarrow> vnm_bucket_update k v (node.next n);
        ll_store (Node (node.val n) q) p;
        Mreturn p
         }
     })\<close>
  unfolding vnm_bucket_update_def
  by (rule pam_bucket_update_impl.simps)

lemmas [llvm_pre_simp] = vnm_bucket_update_def[symmetric]

definition \<open>vnm_bucket_lookup \<equiv> pam_bucket_lookup_impl strl_copy\<close>

lemma vnm_bucket_lookup_simps[llvm_code]:
  \<open>vnm_bucket_lookup k p = (if p = null then Mreturn (0, init)
    else doM {
      n \<leftarrow> ll_load p;
      eq \<leftarrow> ll_icmp_eq (fst (node.val n)) k;
      if to_bool eq then doM {
        v' \<leftarrow> strl_copy (snd (node.val n));
        Mreturn (1, v')
      }
      else vnm_bucket_lookup k (node.next n)
    })\<close>
  unfolding vnm_bucket_lookup_def
  by (rule pam_bucket_lookup_impl.simps)

lemmas [llvm_pre_simp] = vnm_bucket_lookup_def[symmetric]

definition \<open>vnm_bucket_free \<equiv> pam_bucket_free_impl os_delete\<close>

lemma vnm_bucket_free_simps[llvm_code]:
  \<open>vnm_bucket_free p = (if p = null then Mreturn () else doM {
      n \<leftarrow> ll_load p;
      pam_entry_free_impl os_delete (node.val n);
      ll_free p;
      vnm_bucket_free (node.next n)
    })\<close>
  unfolding vnm_bucket_free_def pam_bucket_free_impl_def
  by (rule ol_delete.simps)

lemmas [llvm_pre_simp] = vnm_bucket_free_def[symmetric]

lemmas [llvm_inline] = pam_entry_free_impl_def pam_update_impl_def
  pam_lookup_impl_def pam_the_lookup_impl_def pam_free_impl_def

subsection \<open>The triple and its operations\<close>

type_synonym shared_vars_l = \<open>nat \<times> (nat \<rightharpoonup> char list) \<times> (char list \<rightharpoonup> nat)\<close>
type_synonym shared_vars_l_impl = \<open>64 word \<times> 8 word os_list pam_impl \<times> svm_impl\<close>

abbreviation shared_vars_l_assn :: \<open>shared_vars_l \<Rightarrow> shared_vars_l_impl \<Rightarrow> assn\<close> where
  \<open>shared_vars_l_assn \<equiv> unat_assn' TYPE(64) \<times>\<^sub>a vnm_assn \<times>\<^sub>a svm_assn\<close>

lemma pow_2_63_1: \<open>2 ^ 63 - 1 = (9223372036854775807 :: nat)\<close>
  by auto

text \<open>The counter guard \<open>n < 2^63 - 1\<close> is taken over verbatim from
  \<open>find_new_idx_c\<close>; it keeps \<open>n + 1\<close> comfortably inside the 64-bit unsigned range
  (indices are \<open>unat\<close> everywhere: pam keys, svm values).\<close>

definition find_new_idx_l :: \<open>shared_vars_l \<Rightarrow> (bool \<times> nat) nres\<close> where
  \<open>find_new_idx_l = (\<lambda>(n, \<V>, \<A>).
     if n < 2 ^ 63 - 1 then RETURN (False, n) else RETURN (True, 0))\<close>

text \<open>The name is stored in \<^emph>\<open>both\<close> maps: the argument (owned) goes into \<open>\<A>\<close> as key,
  an explicit \<open>COPY\<close> goes into \<open>\<V>\<close> as value \<comment> \<open>sepref cannot recover an owned
  argument after consumption, cf.\ the note at the lookup test in
  \<^file>\<open>String_Assn.thy\<close>. The \<open>let\<close> sequences the copy before either consumption.\<close>\<close>

definition insert_variable_l :: \<open>char list \<Rightarrow> nat \<Rightarrow> shared_vars_l \<Rightarrow> shared_vars_l nres\<close>
  where
  \<open>insert_variable_l v k' = (\<lambda>(n, \<V>, \<A>). do {
     ASSERT (k' < 2 ^ 63 - 1);
     let v' = COPY v;
     RETURN (k' + 1, \<V>(k' \<mapsto> v'), \<A>(v \<mapsto> k'))
   })\<close>

definition import_variable_l ::
  \<open>char list \<Rightarrow> shared_vars_l \<Rightarrow> (bool \<times> shared_vars_l \<times> nat) nres\<close> where
  \<open>import_variable_l v = (\<lambda>S. do {
     (err, k') \<leftarrow> find_new_idx_l S;
     if err then RETURN (err, S, k')
     else do {
       S \<leftarrow> insert_variable_l v k' S;
       RETURN (False, S, k')
     }
   })\<close>

definition is_new_variable_l :: \<open>char list \<Rightarrow> shared_vars_l \<Rightarrow> bool nres\<close> where
  \<open>is_new_variable_l v = (\<lambda>(n, \<V>, \<A>). RETURN (v \<notin> dom \<A>))\<close>

definition get_var_pos_l :: \<open>shared_vars_l \<Rightarrow> char list \<Rightarrow> nat nres\<close> where
  \<open>get_var_pos_l = (\<lambda>(n, \<V>, \<A>) x. mop_map_the_lookup x \<A>)\<close>

definition get_var_name_l :: \<open>shared_vars_l \<Rightarrow> nat \<Rightarrow> char list nres\<close> where
  \<open>get_var_name_l = (\<lambda>(n, \<V>, \<A>) x. mop_map_the_lookup x \<V>)\<close>

definition empty_shared_vars_l :: \<open>shared_vars_l\<close> where
  \<open>empty_shared_vars_l = (0, op_vnm_empty, op_svm_empty)\<close>

subsection \<open>LLVM synthesis\<close>

text \<open>The operations must be registered with \<^emph>\<open>explicit interface types\<close>: the two
  map components of the triple are \<open>(_, _) i_map\<close> on the argument side (via
  @{thm intf_of_prod_assn} and the \<open>vnm_assn\<close>/\<open>svm_assn\<close> intf rules), and plain
  \<open>sepref_register\<close> would derive the operations' interfaces from the raw HOL type,
  where \<open>\<rightharpoonup>\<close> inside the tuple stays unmapped \<comment> \<open>the identification phase then fails
  silently on the first \<^emph>\<open>call\<close> of a triple-taking operation (cf.\ the \<open>f_map\<close>
  notes in \<open>Polys_Assn.thy\<close>).\<close>\<close>

type_synonym i_shared_vars_l =
  \<open>nat \<times> (nat, char list) i_map \<times> (char list, nat) i_map\<close>

sepref_register find_new_idx_l :: \<open>i_shared_vars_l \<Rightarrow> (bool \<times> nat) nres\<close>
sepref_register insert_variable_l ::
  \<open>char list \<Rightarrow> nat \<Rightarrow> i_shared_vars_l \<Rightarrow> i_shared_vars_l nres\<close>
sepref_register import_variable_l ::
  \<open>char list \<Rightarrow> i_shared_vars_l \<Rightarrow> (bool \<times> i_shared_vars_l \<times> nat) nres\<close>
sepref_register is_new_variable_l :: \<open>char list \<Rightarrow> i_shared_vars_l \<Rightarrow> bool nres\<close>
sepref_register get_var_pos_l :: \<open>i_shared_vars_l \<Rightarrow> char list \<Rightarrow> nat nres\<close>
sepref_register get_var_name_l :: \<open>i_shared_vars_l \<Rightarrow> nat \<Rightarrow> char list nres\<close>
sepref_register empty_shared_vars_l :: i_shared_vars_l

sepref_def find_new_idx_l_impl is \<open>find_new_idx_l\<close>
  :: \<open>shared_vars_l_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn \<times>\<^sub>a unat_assn' TYPE(64)\<close>
  unfolding find_new_idx_l_def pow_2_63_1
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_def insert_variable_l_impl is \<open>uncurry2 insert_variable_l\<close>
  :: \<open>strl_assn\<^sup>d *\<^sub>a (unat_assn' TYPE(64))\<^sup>k *\<^sub>a shared_vars_l_assn\<^sup>d
      \<rightarrow>\<^sub>a shared_vars_l_assn\<close>
  unfolding insert_variable_l_def pow_2_63_1
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_def import_variable_l_impl is \<open>uncurry import_variable_l\<close>
  :: \<open>strl_assn\<^sup>d *\<^sub>a shared_vars_l_assn\<^sup>d
      \<rightarrow>\<^sub>a bool1_assn \<times>\<^sub>a shared_vars_l_assn \<times>\<^sub>a unat_assn' TYPE(64)\<close>
  unfolding import_variable_l_def
  by sepref

sepref_def is_new_variable_l_impl is \<open>uncurry is_new_variable_l\<close>
  :: \<open>strl_assn\<^sup>k *\<^sub>a shared_vars_l_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding is_new_variable_l_def
  by sepref

sepref_def get_var_pos_l_impl is \<open>uncurry get_var_pos_l\<close>
  :: \<open>shared_vars_l_assn\<^sup>k *\<^sub>a strl_assn\<^sup>k \<rightarrow>\<^sub>a unat_assn' TYPE(64)\<close>
  unfolding get_var_pos_l_def
  by sepref

sepref_def get_var_name_l_impl is \<open>uncurry get_var_name_l\<close>
  :: \<open>shared_vars_l_assn\<^sup>k *\<^sub>a (unat_assn' TYPE(64))\<^sup>k \<rightarrow>\<^sub>a strl_assn\<close>
  unfolding get_var_name_l_def
  by sepref

sepref_def empty_shared_vars_l_impl is \<open>uncurry0 (RETURN empty_shared_vars_l)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a shared_vars_l_assn\<close>
  unfolding empty_shared_vars_l_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

subsection \<open>Tests\<close>

experiment begin

  text \<open>Full life cycle through sepref: build the empty store, check freshness,
    import a variable (one \<open>COPY\<close> \<comment> \<open>the parameter is kept\<close>), look its position
    back up by name and its name back up by position, drop everything (the returned
    name copy and the whole store go through the \<open>MK_FREE\<close> rules).\<close>

  definition sv_roundtrip_test :: \<open>char list \<Rightarrow> nat nres\<close> where
    \<open>sv_roundtrip_test v = do {
       let S = empty_shared_vars_l;
       b \<leftarrow> is_new_variable_l v S;
       (err, S, k) \<leftarrow> import_variable_l (COPY v) S;
       if err then RETURN 0
       else do {
         p \<leftarrow> get_var_pos_l S v;
         w \<leftarrow> get_var_name_l S p;
         RETURN p
       }
     }\<close>

  sepref_def sv_roundtrip_test_impl is \<open>sv_roundtrip_test\<close>
    :: \<open>strl_assn\<^sup>k \<rightarrow>\<^sub>a unat_assn' TYPE(64)\<close>
    unfolding sv_roundtrip_test_def
    apply (annot_unat_const \<open>TYPE(64)\<close>)
    by sepref

  export_llvm sv_roundtrip_test_impl

end

end
