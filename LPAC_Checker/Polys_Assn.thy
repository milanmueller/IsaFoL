theory Polys_Assn
  imports IICF_Assoc_Map Poly_Assn PAC_Map_Rel
begin

section \<open>The polynomial store: \<open>nat \<Rightarrow> poly\<close> hash map\<close>

text \<open>
  This is the LLVM-level target assertion for the polynomial database threaded
  through the whole checker (\<open>full_checker_l_impl\<close>'s output / \<open>PAC_checker_l\<close>'s
  running state): abstractly \<open>(nat, llist_polynomial) fmap\<close>, concretely a
  \<^const>\<open>pam_assn\<close>-based hash map with heap-owning \<^const>\<open>poly_assn\<close> values.

  This is the second \<open>hr_comp\<close> step sketched in \<^file>\<open>IICF_Assoc_Map.thy\<close>: from
  \<open>nat \<rightharpoonup> 'v\<close> (\<^const>\<open>pam_map_assn\<close>) up to \<open>('k,'v) fmap\<close> via
  \<^const>\<open>map_fmap_rel\<close> (the same composition \<open>hm_fmap_assn\<close> used in
  \<^file>\<open>PAC_Map_Rel.thy\<close>, just with the placeholder \<open>hm_assn\<close> replaced by the real
  \<^const>\<open>pam_assn\<close>-based map). \<open>polys_assn\<close> used to live in
  \<^file>\<open>PAC_Checker_Relation.thy\<close> as \<open>hm_fmap_assn uint64_nat_assn poly_assn\<close>; it moved
  here once the placeholder was replaced, and the key assertion dropped (keys are
  fixed to \<open>nat\<close>/64-bit words by \<^const>\<open>pam_assn\<close> itself, no \<open>uint64_nat_assn\<close>
  parameter needed \<emdash> \<open>uint64\<close> is not an \<open>llvm_rep\<close> type anyway).
\<close>

definition pam_fmap_assn :: \<open>('v, 'vi::llvm_rep) dr_assn \<Rightarrow> (nat, 'v) fmap \<Rightarrow> 'vi pam_impl \<Rightarrow> assn\<close> where
  \<open>pam_fmap_assn V \<equiv> hr_comp (pam_map_assn V) map_fmap_rel\<close>

text \<open>hfref \<^emph>\<open>arguments\<close> refined by \<open>pam_fmap_assn\<close> must carry the \<open>f_map\<close>
  \<^emph>\<open>interface type\<close>: the fmap operations (\<open>sepref_decl_op\<close> in \<^file>\<open>PAC_Map_Rel.thy\<close>)
  are registered via \<open>INTF_OF_REL (\<langle>K,V\<rangle>fmap_rel) = f_map\<close>, so internally-created
  maps (\<open>op_fmap_empty\<close>, \<open>fmupd\<close> results) get \<open>f_map\<close> during identification, but
  without this rule an argument's interface type comes from
  \<open>intf_of_assn_fallback\<close> as the plain \<open>fmap\<close> type \<comment> \<open>and \<open>ID x _ TYPE(_ f_map)\<close>
  can then never be discharged from the hypothesis \<open>x ::\<^sub>i TYPE(_ fmap)\<close>. This
  never surfaced in the tests below because they build their maps internally;
  it strands any synthesis taking \<open>polys_assn\<close> as an argument (e.g.
  \<open>linear_combi_l\<close>).\<close>\<close>

text \<open>The value-type premise \<open>intf_of_assn (\<upharpoonleft>V) TYPE('v)\<close> is essential:
  without it \<open>'v\<close> is unconstrained, so an argument's interface type comes out
  as \<open>(nat, ?'v) f_map\<close> with a \<^emph>\<open>schematic\<close> value type, which the identification
  phase cannot resolve (it fails silently, leaving the whole program
  untranslated). The premise recurses into \<open>V\<close>'s own interface (here
  \<open>\<upharpoonleft>(mk_assn poly_assn) = poly_assn\<close>, resolved to \<open>llist_polynomial\<close> by
  \<open>intf_of_assn_fallback\<close>), pinning \<open>'v\<close>. Mirrors \<open>amt_assn_intf\<close> in
  \<open>IICF_Array_Map_Total\<close>.\<close>
lemma pam_fmap_assn_intf[intf_of_assn]:
  \<open>intf_of_assn (\<upharpoonleft>V) TYPE('v) \<Longrightarrow> intf_of_assn (pam_fmap_assn V) TYPE((nat, 'v) f_map)\<close>
  by simp

abbreviation polys_assn where
  \<open>polys_assn \<equiv> pam_fmap_assn (mk_assn poly_assn)\<close>

text \<open>Some setup taken from or inspired by PAC_Map_Rel\<close>
lemma fmempty_empty:
  \<open>(uncurry0 (RETURN op_map_empty), uncurry0 (RETURN fmempty)) \<in> unit_rel \<rightarrow>\<^sub>f \<langle>map_fmap_rel\<rangle>nres_rel\<close>
  by (auto simp: map_fmap_rel_def br_def fmempty_def frefI nres_relI)

lemmas pam_fmempty_hnr[sepref_fr_rules] =
  pam_empty_hnr[FCOMP fmempty_empty, folded pam_fmap_assn_def,
    unfolded op_fmap_empty_def[symmetric]]

lemmas pam_fmupd_hnr[sepref_fr_rules] =
  pam_update_hnr[FCOMP map_upd_fmupd, folded pam_fmap_assn_def,
    unfolded op_fmap_update_def[symmetric]]

lemmas pam_fmdrop_hnr[sepref_fr_rules] =
  pam_delete_hnr[FCOMP fmdrop_set_None, folded pam_fmap_assn_def,
    unfolded op_fmap_delete_def[symmetric]]

(* lemmas pam_fmempty_hnr[sepref_fr_rules] =
 *   pam_empty_hnr[FCOMP fmempty_empty, folded pam_fmap_assn_def] *)

(* lemmas pam_fmupd_hnr[sepref_fr_rules] =
 *   pam_update_hnr[FCOMP map_upd_fmupd, folded pam_fmap_assn_def] *)

(* lemmas pam_delete_hnr[sepref_fr_rules] = 
 *   pam_delete_hnr[FCOMP fmdrop_set_None, folded pam_fmap_assn_def] *)

lemma pat_fmupd[def_pat_rules]: \<open>fmupd$k$v$m \<equiv> op_fmap_update$k$v$m\<close> by simp
lemma pat_fmdrop[def_pat_rules]: \<open>fmdrop$k$m \<equiv> op_fmap_delete$k$m\<close> by simp

sepref_decl_op fmap_the_lookup: \<open>\<lambda>k m. the (fmlookup' k m)\<close>
  :: \<open>[\<lambda>(k, m). k \<in># dom_m m]\<^sub>f K \<times>\<^sub>r \<langle>K,V\<rangle>fmap_rel \<rightarrow> V\<close>
  using fmap_rel_in_dom_iff by fastforce

lemma pat_fmap_the_lookup[def_pat_rules]: \<open>the$(fmlookup'$k$m) \<equiv> op_fmap_the_lookup$k$m\<close>
  by simp

lemma mop_the_lookup_glue:
  \<open>(uncurry mop_map_the_lookup, uncurry mop_fmap_the_lookup)
     \<in> Id \<times>\<^sub>r map_fmap_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: mop_map_the_lookup_def mop_fmap_the_lookup_def map_fmap_rel_def
       br_def in_fdom_alt fmap.Abs_fmap_inverse pw_le_iff)

lemma sel_mk_assn': \<open>\<upharpoonleft>(mk_assn A) = A\<close>
  by (intro ext) simp

lemmas polys_the_lookup_hnr[sepref_fr_rules] =
  pam_the_lookup_hnr[where V = \<open>mk_assn poly_assn\<close>, unfolded sel_mk_assn',
    OF poly_copy_rule, FCOMP mop_the_lookup_glue, folded pam_fmap_assn_def]

lemma op_the_lookup_glue:
  \<open>(uncurry mop_map_the_lookup, uncurry (RETURN oo op_fmap_the_lookup))
     \<in> [\<lambda>(k, m). k \<in># dom_m m]\<^sub>f Id \<times>\<^sub>r map_fmap_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  by (auto simp: map_fmap_rel_def br_def in_fdom_alt fmap.Abs_fmap_inverse)

lemmas polys_the_lookup_op_hnr[sepref_fr_rules] =
  pam_the_lookup_hnr[where V = \<open>mk_assn poly_assn\<close>, unfolded sel_mk_assn',
    OF poly_copy_rule, FCOMP op_the_lookup_glue, folded pam_fmap_assn_def]

text \<open>Membership (\<open>k \<in># dom_m A\<close>): the identification-phase pattern
  @{thm op_map_contains_key} (\<^file>\<open>PAC_Map_Rel.thy\<close>) rewrites the \<open>dom_m\<close> test to
  \<^const>\<open>op_fmap_contains_key\<close>, implemented by the key-only bucket walk
  \<^const>\<open>pam_contains_impl\<close>; no value is touched, so no copy/free parameter and
  the rule is generic in \<open>V\<close>. Synthesis scripts must NOT unfold
  \<open>in_dom_m_lookup_iff\<close>, which would funnel the test into an option-returning
  \<open>fmlookup'\<close> that has no implementation here (an option assertion over
  heap-owning values does not exist).\<close>

lemma fmap_contains_key_glue:
  \<open>(uncurry (RETURN oo op_map_contains_key), uncurry (RETURN oo op_fmap_contains_key))
     \<in> Id \<times>\<^sub>r map_fmap_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: op_map_contains_key_def op_fmap_contains_key_def map_fmap_rel_def
      br_def in_fdom_alt fmap.Abs_fmap_inverse split: option.splits)

lemmas pam_fmap_contains_hnr[sepref_fr_rules] =
  pam_contains_hnr[FCOMP fmap_contains_key_glue, folded pam_fmap_assn_def]

lemma pam_fmap_assn_free[sepref_frame_free_rules]:
  assumes \<open>MK_FREE (\<upharpoonleft>V) vfree\<close>
  shows \<open>MK_FREE (pam_fmap_assn V) (pam_free_impl vfree)\<close>
  unfolding pam_fmap_assn_def
  by (intro MK_FREE_hrcompI pam_map_assn_free assms)

definition poly_bucket_update where \<open>poly_bucket_update \<equiv> pam_bucket_update_impl poly_free\<close>

lemma poly_bucket_update_simps[llvm_code]:
  \<open>poly_bucket_update k v p = (if p = null then os_prepend (k, v) null
     else do\<^sub>M {
       n \<leftarrow> ll_load p;
       eq \<leftarrow> ll_icmp_eq (fst (node.val n)) k;
       if to_bool eq then do\<^sub>M {
                poly_free (snd (node.val n));
                ll_store (Node (k, v) (node.next n)) p;
                return\<^sub>M p
              }
       else do\<^sub>M {
        q \<leftarrow> poly_bucket_update k v (node.next n);
        ll_store (Node (node.val n) q) p;
        return\<^sub>M p
         }
     })\<close>
  unfolding poly_bucket_update_def
  by (rule pam_bucket_update_impl.simps)

lemmas [llvm_pre_simp] = poly_bucket_update_def[symmetric]

definition \<open>poly_bucket_delete \<equiv> pam_bucket_delete_impl poly_free\<close>

lemma poly_bucket_delete_simps[llvm_code]:
  \<open>poly_bucket_delete k p = (if p = null then Mreturn null
    else doM {
      n \<leftarrow> ll_load p;
      q \<leftarrow> poly_bucket_delete k (node.next n);
      eq \<leftarrow> ll_icmp_eq (fst (node.val n)) k;
      if to_bool eq then do\<^sub>M {
          poly_free (snd (node.val n));
          ll_free p;
          return\<^sub>M q
        }
      else do\<^sub>M {
      ll_store (Node (node.val n) q) p;
      return\<^sub>M p
      }
    })
  \<close>
  unfolding poly_bucket_delete_def
  using pam_bucket_delete_impl.simps by blast

lemmas [llvm_pre_simp] = poly_bucket_delete_def[symmetric]

definition \<open>poly_bucket_lookup \<equiv> pam_bucket_lookup_impl poly_copy_impl\<close>

lemma poly_bucket_lookup_simps[llvm_code]:
  \<open>poly_bucket_lookup k p = (if p = null then Mreturn (0, init)
    else do\<^sub>M {
      n \<leftarrow> ll_load p;
      eq \<leftarrow> ll_icmp_eq (fst (node.val n)) k;
      if to_bool eq then do\<^sub>M {
        v' \<leftarrow> poly_copy_impl (snd (node.val n));
        return\<^sub>M (1, v')
      }
      else poly_bucket_lookup k (node.next n)
    })\<close>
  unfolding poly_bucket_lookup_def
  by (rule pam_bucket_lookup_impl.simps)

lemmas [llvm_pre_simp] = poly_bucket_lookup_def[symmetric]

definition \<open>poly_bucket_free \<equiv> pam_bucket_free_impl poly_free\<close>

text \<open>NOT the flat unfolding \<open>ol_delete (pam_entry_free_impl poly_free)\<close> as code
  equation: that re-exposes the higher-order \<open>ol_delete\<close>, which has no code equation.
  The recursion must go through the named constant itself.\<close>

lemma poly_bucket_free_simps[llvm_code]:
  \<open>poly_bucket_free p = (if p = null then Mreturn () else do\<^sub>M {
      n \<leftarrow> ll_load p;
      pam_entry_free_impl poly_free (node.val n);
      ll_free p;
      poly_bucket_free (node.next n)
    })\<close>
  unfolding poly_bucket_free_def pam_bucket_free_impl_def
  by (rule ol_delete.simps)

lemmas [llvm_pre_simp] = poly_bucket_free_def[symmetric]

subsubsection \<open>Map-level operations\<close>

text \<open>The map-level operations (\<open>pam_update_impl\<close>, \<open>pam_delete_impl\<close>,
  \<open>pam_the_lookup_impl\<close>, \<open>pam_free_impl\<close>, \<open>pam_entry_free_impl\<close>) are non-recursive
  wrappers around the bucket walks: mark their definitions \<open>[llvm_inline]\<close>, so the
  preprocessor substitutes their bodies; the exposed
  \<open>pam_bucket_\<dots>_impl poly_free/poly_copy_impl\<close> applications then fold to the named
  first-order instances above via the \<open>[llvm_pre_simp]\<close> folds.

  The free/copy arguments synthesized by sepref carry monad-law bloat:
  \<open>\<lambda>x. do\<^sub>M {poly_free x; return\<^sub>M ()}\<close> resp. \<open>\<lambda>x. Mbind (poly_copy_impl x) Mreturn\<close>.
  The latter collapses by the pre-registered right-unit law
  @{thm llvm_inline_bind_laws(1)}; the unit-typed variant needed for the former is
  added here.\<close>

text \<open>The \<open>fst\<close>/\<open>snd\<close> and unit-bind code-generator interceptors
  (\<open>inline_return_fst\<close>/\<open>inline_return_snd\<close>/\<open>Mbind_return_unit\<close>) used to live here;
  they are generic and now sit in \<^file>\<open>IICF_Assoc_Map.thy\<close>, shared with the string
  hash map export in \<open>String_Assn.thy\<close>.\<close>

lemmas [llvm_inline] = pam_entry_free_impl_def pam_update_impl_def pam_delete_impl_def
  pam_lookup_impl_def pam_the_lookup_impl_def pam_free_impl_def


text \<open>
  The abstract operations the checker actually needs against this store: 
  \<open>CL\<close>/\<open>Extension\<close> steps \<^emph>\<open>insert\<close> a
  freshly-checked polynomial under a new id, and every step kind \<^emph>\<open>looks up\<close> the
  polynomials it cites by id (\<open>the (fmlookup A n)\<close> in \<open>check_linear_comb\<close>,
  \<^file>\<open>../PAC_Checker2//LPAC_Checker.thy\<close> in \<open>PAC_Checker2\<close>). \<open>Del\<close> removes an entry. No lookup ever
  needs to distinguish \<open>None\<close> from \<open>Some\<close> at this layer \emdash presence is checked
  separately (\<open>k \<in># dom_m A\<close>) before the value is ever pulled out with \<open>the\<close>; hence
  the tests below target \<open>fmupd\<close> / \<open>the o fmlookup'\<close> / \<open>fmdrop\<close> / \<open>\<in># dom_m\<close>
  (\<open>op_fmap_contains_key\<close>), not a general \<open>option\<close>-returning lookup (which would
  additionally need an option assertion for \<^typ>\<open>'a option\<close> over a heap-owning \<open>'a\<close>
  \emdash not implemented, cf. \<^file>\<open>IICF_Assoc_Map.thy\<close>).
\<close>

subsection \<open>Test-driven-development harness\<close>

text \<open>
  These are high-level tests: abstract \<open>nres\<close> programs built from the same
  \<open>fmap\<close> primitives the checker itself uses (\<open>fmupd\<close>, \<open>fmlookup'\<close>, \<open>fmdrop\<close>,
  \<open>fmempty\<close>), each stated first as a plain functional-correctness fact (trivial,
  provable now) and then handed to \<open>sepref_definition\<close> to be refined down to
  \<open>polys_assn\<close>. Unlike the bucket-level \<open>llvm_htriple\<close> tests in
  \<^file>\<open>IICF_Assoc_Map.thy\<close>, nothing here talks about buckets, pointers, or the
  separation-logic heap directly \emdash only the map interface. The \<open>sepref\<close> calls
  are expected to fail to fully discharge for now (no \<open>hfref\<close> rules for
  \<open>fmupd\<close>/\<open>fmlookup'\<close>/\<open>fmdrop\<close>/\<open>fmempty\<close> against \<open>polys_assn\<close> exist yet, cf. the
  \<open>Open points\<close> in \<^file>\<open>IICF_Assoc_Map.thy\<close>); they are closed with \<open>sorry\<close> so this
  theory documents the target interface and can be re-run as those rules land \emdash
  the point of having them here at all is to flip \<open>sorry\<close> to a real proof
  (or watch \<open>sepref\<close> get further before getting stuck) as the hash-map port
  progresses.
\<close>

experiment
begin

paragraph \<open>Insert, then look the same key back up.\<close>

definition test_insert_lookup :: \<open>nat \<Rightarrow> llist_polynomial \<Rightarrow> llist_polynomial nres\<close> where
  \<open>test_insert_lookup k p \<equiv> do {
     let A = fmupd k p fmempty;
     ASSERT (k \<in># dom_m A);
     RETURN (the (fmlookup' k A))
   }\<close>

lemma test_insert_lookup_correct: \<open>test_insert_lookup k p \<le> RETURN p\<close>
  unfolding test_insert_lookup_def
  by (auto simp: in_fdom_alt)

sepref_definition test_insert_lookup_impl
  is \<open>uncurry test_insert_lookup\<close>
  :: \<open>(unat_assn' TYPE(64))\<^sup>k *\<^sub>a poly_assn\<^sup>d \<rightarrow>\<^sub>a poly_assn\<close>
  unfolding test_insert_lookup_def 
  by sepref

paragraph \<open>Two distinct keys coexist; each looks up its own value.\<close>

definition test_two_keys :: \<open>nat \<Rightarrow> nat \<Rightarrow> llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow>
    (llist_polynomial \<times> llist_polynomial) nres\<close> where
  \<open>test_two_keys k1 k2 p1 p2 \<equiv> do {
     ASSERT (k1 \<noteq> k2);
     let A = fmupd k1 p1 fmempty;
     let A = fmupd k2 p2 A;
     ASSERT (k1 \<in># dom_m A \<and> k2 \<in># dom_m A);
     RETURN (the (fmlookup' k1 A), the (fmlookup' k2 A))
   }\<close>

lemma test_two_keys_correct:
  \<open>k1 \<noteq> k2 \<Longrightarrow> test_two_keys k1 k2 p1 p2 \<le> RETURN (p1, p2)\<close>
  unfolding test_two_keys_def
  by (auto simp: in_fdom_alt)

sepref_definition test_two_keys_impl
  is \<open>uncurry3 test_two_keys\<close>
  :: \<open>(unat_assn' TYPE(64))\<^sup>k *\<^sub>a (unat_assn' TYPE(64))\<^sup>k *\<^sub>a poly_assn\<^sup>d *\<^sub>a poly_assn\<^sup>d \<rightarrow>\<^sub>a
       poly_assn \<times>\<^sub>a poly_assn\<close>
  unfolding test_two_keys_def
  by sepref

paragraph \<open>Executable membership: the \<open>dom_m\<close> test of the step checkers
  (\<open>linear_combi_l\<close> tests \<open>i \<notin># dom_m A\<close> in an \<open>if\<close>, not just in \<open>ASSERT\<close>s).\<close>

definition test_contains :: \<open>nat \<Rightarrow> nat \<Rightarrow> llist_polynomial \<Rightarrow> (bool \<times> bool) nres\<close> where
  \<open>test_contains k1 k2 p \<equiv> do {
     let A = fmupd k1 p fmempty;
     RETURN (k1 \<in># dom_m A, k2 \<in># dom_m A)
   }\<close>

lemma test_contains_correct:
  \<open>k1 \<noteq> k2 \<Longrightarrow> test_contains k1 k2 p \<le> RETURN (True, False)\<close>
  unfolding test_contains_def
  by (auto simp: in_fdom_alt)

sepref_definition test_contains_impl
  is \<open>uncurry2 test_contains\<close>
  :: \<open>(unat_assn' TYPE(64))\<^sup>k *\<^sub>a (unat_assn' TYPE(64))\<^sup>k *\<^sub>a poly_assn\<^sup>d \<rightarrow>\<^sub>a
       bool1_assn \<times>\<^sub>a bool1_assn\<close>
  unfolding test_contains_def
  by sepref

paragraph \<open>Membership with the map as an hfref \<^emph>\<open>argument\<close> (the checker's actual
  shape, cf. \<open>linear_combi_l\<close>): exercises the \<open>intf_of_assn\<close> rule (argument
  interface type \<open>f_map\<close>), which internally-built maps never need.\<close>

definition test_contains_arg :: \<open>nat \<Rightarrow> (nat, llist_polynomial) fmap \<Rightarrow> bool nres\<close> where
  \<open>test_contains_arg k A \<equiv> RETURN (k \<in># dom_m A)\<close>

sepref_definition test_contains_arg_impl
  is \<open>uncurry test_contains_arg\<close>
  :: \<open>(unat_assn' TYPE(64))\<^sup>k *\<^sub>a polys_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding test_contains_arg_def
  by sepref

paragraph \<open>The trivial-coefficient test of \<open>linear_combi_l\<close> (\<open>q = [([], 1)]\<close>):
  constructs the constant polynomial (empty monomial via \<open>op_ol_empty\<close>,
  coefficient \<open>1 :: int\<close> via \<open>signed_big_int1_impl\<close>, singleton via
  \<open>op_list_prepend\<close>) and compares with \<open>poly_eq_impl\<close>. Both \<open>[]\<close> literals are
  ol-level, hence the \<open>fold_ol_empty\<close> unfold.\<close>

definition test_trivial_coeff :: \<open>llist_polynomial \<Rightarrow> bool nres\<close> where
  \<open>test_trivial_coeff q \<equiv> RETURN (q = [([], 1)])\<close>

sepref_definition test_trivial_coeff_impl
  is \<open>test_trivial_coeff\<close>
  :: \<open>poly_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding test_trivial_coeff_def fold_ol_empty
  by sepref

paragraph \<open>Insert, delete, re-insert under the same id (the \<open>CL\<close>/\<open>Del\<close> pattern).\<close>

definition test_insert_delete_reinsert :: \<open>nat \<Rightarrow> llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow>
    llist_polynomial nres\<close> where
  \<open>test_insert_delete_reinsert k p p' \<equiv> do {
     let A = fmupd k p fmempty;
     let A = fmdrop k A;
     ASSERT (k \<notin># dom_m A);
     let A = fmupd k p' A;
     ASSERT (k \<in># dom_m A);
     RETURN (the (fmlookup' k A))
   }\<close>

lemma test_insert_delete_reinsert_correct:
  \<open>test_insert_delete_reinsert k p p' \<le> RETURN p'\<close>
  unfolding test_insert_delete_reinsert_def
  by (auto simp: in_fdom_alt)

sepref_def test_insert_delete_reinsert_impl
  is \<open>uncurry2 test_insert_delete_reinsert\<close>
  :: \<open>(unat_assn' TYPE(64))\<^sup>k *\<^sub>a poly_assn\<^sup>d *\<^sub>a poly_assn\<^sup>d \<rightarrow>\<^sub>a poly_assn\<close>
  unfolding test_insert_delete_reinsert_def
  by sepref

export_llvm test_insert_delete_reinsert_impl

end

end
