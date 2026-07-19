(*
  Note that large portions of this file were generated using the
  "Fable 5" language model by Anthropic. An in-depth human
  review has not been carried out yet.

  Responsible: Milan Mueller, ALU Freiburg (student)
*)

theory IICF_Hash_Map
  imports
    IICF_Assoc_Map
    IICF_Hash_Set
begin

section \<open>A hash map of heap-owning entries, built on the assoc map\<close>

text \<open>
  A map from arbitrary (heap-owning) keys to values, built \<^emph>\<open>on top of\<close> the
  64-bit-keyed association map of \<^file>\<open>IICF_Assoc_Map.thy\<close>: the pam key is the
  \<^emph>\<open>full 64-bit hash\<close> of the entry's key, and the pam \<^emph>\<open>value\<close> is the collision
  chain an owning open list (\<^const>\<open>ol_assn\<close>) of all entries whose keys share
  that hash. Since the pam discriminates by the full hash (its own \<open>mod nbins\<close>
  bucketing is internal), the chains only carry true 64-bit collisions and are
  singletons in practice.

  The theory is \<^emph>\<open>generic\<close>:
  \<^item> in the entry assertion \<open>A :: 'a \<Rightarrow> 'ai \<Rightarrow> assn\<close> (impure entries welcome
    \<open>the intended instantiation is \<open>strl_assn \<times>\<^sub>a unat_assn\<close> for string-keyed
    maps to machine numbers\<close>);
  \<^item> in the \<^emph>\<open>probe\<close> assertion \<open>B :: 'x \<Rightarrow> 'xi \<Rightarrow> assn\<close> and an abstract matching
    predicate \<open>eabs :: 'x \<Rightarrow> 'a \<Rightarrow> bool\<close>, implemented by a Hoare-triple parameter
    \<open>eeq\<close> (heterogeneous: it compares a probe against an entry, e.g. a string
    against the key component of a (string, value) pair);
  \<^item> in an extraction function \<open>ext\<close> for lookup, tied to an abstract projection
    \<open>fabs :: 'a \<Rightarrow> 'r\<close> and result assertion \<open>R for pure projections (the
    value component of an entry with pure values) no copy is ever made; an
    entry-copy is just the special case \<open>fabs = id\<close>, \<open>R = A\<close>.\<close>

  Operations (as requested): \<^emph>\<open>empty\<close>, \<^emph>\<open>insert\<close> (unconditional prepend
  \<open>callers check membership first; re-inserting an existing key shadows the old
  entry, which stays owned by the map and is reclaimed on free so insert still
  implements \<open>fmupd\<close> abstractly\<close>), \<^emph>\<open>contains\<close> (read-only, no copies), and
  \<^emph>\<open>the-lookup\<close> (asserted-present, avoiding option refinement).

  Refinement chain:
    \<open>'k \<rightharpoonup> 'a\<close>  \<longleftarrow>[\<open>phm_rel kabs hk\<close>: hash-bucket abstraction]\<longleftarrow>  \<open>nat \<rightharpoonup> 'a list\<close>
    \<longleftarrow>[\<open>pam_rel\<close>: pam bucket invariant]\<longleftarrow>  \<open>(nat \<times> 'a list) list list\<close>
    \<longleftarrow>[\<open>pam_assn (phm_chain_assn A)\<close>: separation logic]\<longleftarrow>  \<open>64 word \<times> bucket ptr\<close>

  where \<open>kabs :: 'a \<Rightarrow> 'k\<close> projects the abstract key out of an entry and
  \<open>hk :: 'k \<Rightarrow> 64 word\<close> is the abstract hash. Remarkably, the top abstraction
  step needs \<^emph>\<open>no invariant\<close>: the abstraction function \<open>phm_map_of\<close> only ever
  reads the chain at \<open>unat (hk x)\<close>, and all operations only write there.
\<close>

subsection \<open>Concrete representation\<close>

type_synonym 'ai phm_chain_impl = \<open>'ai os_list\<close>
type_synonym 'ai phm_impl = \<open>'ai phm_chain_impl pam_impl\<close>

text \<open>A collision chain: an owning open list of entries. Named dr_assn so it can
  serve as the (folded) pam value parameter (cf.\ \<open>hs_bucket_assn\<close>).\<close>

definition phm_chain_assn ::
  \<open>('a \<Rightarrow> 'ai::llvm_rep \<Rightarrow> assn) \<Rightarrow> ('a list, 'ai phm_chain_impl) dr_assn\<close> where
  \<open>phm_chain_assn A \<equiv> mk_assn (ol_assn A)\<close>

lemma phm_chain_assn_conv:
  \<open>\<upharpoonleft>(phm_chain_assn A) = ol_assn A\<close>
  unfolding phm_chain_assn_def by (intro ext) simp

text \<open>Prepend, restated at the folded chain assertion (specialized empty variant
  included: fri cannot conjure an \<open>ol_assn ?es null\<close> atom with schematic \<open>?es\<close>
  from an empty state, cf.\ the singleton-creation notes in
  \<^file>\<open>IICF_Assoc_Map.thy\<close>).\<close>

lemma phm_chain_prepend_rule:
  \<open>llvm_htriple
    (A x xi ** \<upharpoonleft>(phm_chain_assn A) ch p)
    (os_prepend xi p)
    (\<lambda>r. \<upharpoonleft>(phm_chain_assn A) (x # ch) r)\<close>
  unfolding phm_chain_assn_conv
  by (rule ol_prepend_rule)

lemma ol_assn_empty_null: \<open>\<box> \<turnstile> ol_assn A [] null\<close>
  by (simp add: ol_assn_conv sep_algebra_simps)

lemma phm_chain_prepend_empty_rule:
  \<open>llvm_htriple
    (A x xi)
    (os_prepend xi null)
    (\<lambda>r. \<upharpoonleft>(phm_chain_assn A) [x] r)\<close>
  apply (rule htriple_ent_pre[OF _ phm_chain_prepend_rule[where ch = \<open>[]\<close>]])
  unfolding phm_chain_assn_conv
  by (simp add: ol_assn_conv sep_algebra_simps)


subsection \<open>Chain operations\<close>

text \<open>The two chain walks follow the \<open>hs_bucket_member_impl\<close> template, but with a
  \<^emph>\<open>heterogeneous\<close> equality: \<open>eeq\<close> compares an entry (first argument) against the
  probe (second argument), deciding the abstract predicate \<open>eabs x e\<close>.

  NOTE (code generation): higher-order in \<open>eeq\<close>/\<open>ext\<close>; each concrete instantiation
  must be specialized into first-order \<open>[llvm_code]\<close> definitions before export.\<close>

partial_function (M) phm_chain_member_impl ::
  \<open>('ai \<Rightarrow> 'xi \<Rightarrow> 1 word llM) \<Rightarrow> 'xi \<Rightarrow> 'ai::llvm_rep phm_chain_impl \<Rightarrow> 1 word llM\<close>
  where
  \<open>phm_chain_member_impl eeq x p = (if p = null then Mreturn 0
    else doM {
      n \<leftarrow> ll_load p;
      eq \<leftarrow> eeq (node.val n) x;
      if to_bool eq then Mreturn 1
      else phm_chain_member_impl eeq x (node.next n)
    })\<close>

lemma phm_chain_member_impl_rule:
  assumes EEQ: \<open>\<And>e ei x' xi'. llvm_htriple (A e ei ** B x' xi') (eeq ei xi')
    (\<lambda>r. A e ei ** B x' xi' ** \<upharpoonleft>bool.assn (eabs x' e) r)\<close>
  shows \<open>llvm_htriple
    (\<upharpoonleft>(phm_chain_assn A) es p ** B x xi)
    (phm_chain_member_impl eeq xi p)
    (\<lambda>r. \<upharpoonleft>(phm_chain_assn A) es p ** B x xi ** \<upharpoonleft>bool.assn (\<exists>e\<in>set es. eabs x e) r)\<close>
  unfolding phm_chain_assn_conv ol_assn_conv
proof (induction es arbitrary: p)
  case Nil
  show ?case
    supply [simp] = bool.assn_def
    apply (subst phm_chain_member_impl.simps)
    by vcg
next
  case (Cons e es)
  interpret llvm_prim_ctrl_setup .
  note [vcg_rules] = Cons.IH EEQ
  show ?case
    supply [simp, named_ss fri_prepare_simps] = ol_seg_cons
    supply [simp] = bool.assn_def sep_conj_exists
    apply (subst phm_chain_member_impl.simps)
    apply (cases \<open>p = null\<close>; simp)
    by vcg
qed

text \<open>The-find: walk to the first matching entry and extract from it. Guarded by
  the presence precondition, so the \<open>null\<close> case is vacuous and no option is needed
  in the result.\<close>

partial_function (M) phm_chain_find_impl ::
  \<open>('ai \<Rightarrow> 'xi \<Rightarrow> 1 word llM) \<Rightarrow> ('ai \<Rightarrow> 'ri llM) \<Rightarrow> 'xi
    \<Rightarrow> 'ai::llvm_rep phm_chain_impl \<Rightarrow> 'ri::llvm_rep llM\<close>
  where
  \<open>phm_chain_find_impl eeq ext x p = (if p = null then Mreturn init
    else doM {
      n \<leftarrow> ll_load p;
      eq \<leftarrow> eeq (node.val n) x;
      if to_bool eq then ext (node.val n)
      else phm_chain_find_impl eeq ext x (node.next n)
    })\<close>

lemma phm_chain_find_impl_rule:
  assumes EEQ: \<open>\<And>e ei x' xi'. llvm_htriple (A e ei ** B x' xi') (eeq ei xi')
    (\<lambda>r. A e ei ** B x' xi' ** \<upharpoonleft>bool.assn (eabs x' e) r)\<close>
    and EXT: \<open>\<And>e ei. llvm_htriple (A e ei) (ext ei) (\<lambda>r. A e ei ** R (fabs e) r)\<close>
  shows \<open>llvm_htriple
    (\<upharpoonleft>(phm_chain_assn A) es p ** B x xi ** \<up>(\<exists>e\<in>set es. eabs x e))
    (phm_chain_find_impl eeq ext xi p)
    (\<lambda>r. \<upharpoonleft>(phm_chain_assn A) es p ** B x xi
       ** R (fabs (the (find (eabs x) es))) r)\<close>
  unfolding phm_chain_assn_conv ol_assn_conv
proof (induction es arbitrary: p)
  case Nil
  show ?case
    apply (subst phm_chain_find_impl.simps)
    by vcg
next
  case (Cons e es)
  interpret llvm_prim_ctrl_setup .
  note [vcg_rules] = Cons.IH EEQ EXT
  show ?case
    supply [simp, named_ss fri_prepare_simps] = ol_seg_cons
    supply [simp] = bool.assn_def sep_conj_exists
    apply (subst phm_chain_find_impl.simps)
    apply (cases \<open>p = null\<close>; simp)
    by vcg
qed


subsection \<open>Bucket operations\<close>

text \<open>The pam buckets now carry (hash, chain) entries: the pam value assertion is
  instantiated to \<^const>\<open>phm_chain_assn\<close>. The walks compare the pure hash keys
  (\<open>ll_icmp_eq\<close>) exactly like the pam walks and dispatch into the chain on a hit.\<close>

abbreviation phm_bucket_assn ::
  \<open>('a \<Rightarrow> 'ai::llvm_rep \<Rightarrow> assn)
    \<Rightarrow> ((nat \<times> 'a list) list, 'ai phm_chain_impl pam_bucket_impl) dr_assn\<close> where
  \<open>phm_bucket_assn A \<equiv> pam_bucket_assn (phm_chain_assn A)\<close>

text \<open>The chain stored under a key (empty if absent); the abstract counterpart of
  all bucket-level results.\<close>

definition phm_chain_of :: \<open>(nat \<times> 'a list) list \<Rightarrow> nat \<Rightarrow> 'a list\<close> where
  \<open>phm_chain_of es k = (case map_of es k of None \<Rightarrow> [] | Some ch \<Rightarrow> ch)\<close>

lemma phm_chain_of_simps[simp]:
  \<open>phm_chain_of [] k = []\<close>
  \<open>phm_chain_of ((k', ch) # es) k = (if k' = k then ch else phm_chain_of es k)\<close>
  unfolding phm_chain_of_def by auto

subsubsection \<open>Membership\<close>

partial_function (M) phm_bucket_member_impl ::
  \<open>('ai \<Rightarrow> 'xi \<Rightarrow> 1 word llM) \<Rightarrow> 64 word \<Rightarrow> 'xi
    \<Rightarrow> 'ai::llvm_rep phm_chain_impl pam_bucket_impl \<Rightarrow> 1 word llM\<close>
  where
  \<open>phm_bucket_member_impl eeq k x p = (if p = null then Mreturn 0
    else doM {
      n \<leftarrow> ll_load p;
      eq \<leftarrow> ll_icmp_eq (fst (node.val n)) k;
      if to_bool eq then phm_chain_member_impl eeq x (snd (node.val n))
      else phm_bucket_member_impl eeq k x (node.next n)
    })\<close>

lemma phm_bucket_member_impl_rule:
  assumes EEQ: \<open>\<And>e ei x' xi'. llvm_htriple (A e ei ** B x' xi') (eeq ei xi')
    (\<lambda>r. A e ei ** B x' xi' ** \<upharpoonleft>bool.assn (eabs x' e) r)\<close>
  shows \<open>llvm_htriple
    (\<upharpoonleft>(phm_bucket_assn A) es p ** \<upharpoonleft>unat.assn k ki ** B x xi)
    (phm_bucket_member_impl eeq ki xi p)
    (\<lambda>r. \<upharpoonleft>(phm_bucket_assn A) es p ** \<upharpoonleft>unat.assn k ki ** B x xi
       ** \<upharpoonleft>bool.assn (\<exists>e\<in>set (phm_chain_of es k). eabs x e) r)\<close>
  unfolding pam_bucket_assn_conv ol_assn_conv
proof (induction es arbitrary: p)
  case Nil
  show ?case
    supply [simp] = bool.assn_def
    apply (subst phm_bucket_member_impl.simps)
    by vcg
next
  case (Cons e es)
  interpret llvm_prim_ctrl_setup .
  note [vcg_rules] = Cons.IH phm_chain_member_impl_rule[OF EEQ]
  show ?case
    supply [simp, named_ss fri_prepare_simps] = ol_seg_cons
    supply [simp] = bool.assn_def sep_conj_exists
    apply (subst phm_bucket_member_impl.simps)
    apply (cases \<open>p = null\<close>; cases e; simp)
    by vcg
qed

subsubsection \<open>The-lookup\<close>

partial_function (M) phm_bucket_find_impl ::
  \<open>('ai \<Rightarrow> 'xi \<Rightarrow> 1 word llM) \<Rightarrow> ('ai \<Rightarrow> 'ri) \<Rightarrow> 64 word \<Rightarrow> 'xi
    \<Rightarrow> 'ai::llvm_rep phm_chain_impl pam_bucket_impl \<Rightarrow> 'ri::llvm_rep llM\<close>
  where
  \<open>phm_bucket_find_impl eeq ext k x p = (if p = null then Mreturn init
    else doM {
      n \<leftarrow> ll_load p;
      eq \<leftarrow> ll_icmp_eq (fst (node.val n)) k;
      if to_bool eq then phm_chain_find_impl eeq (Mreturn o ext) x (snd (node.val n))
      else phm_bucket_find_impl eeq ext k x (node.next n)
    })\<close>

text \<open>The extraction parameter is deliberately \<^emph>\<open>pure\<close> here (\<open>'ai \<Rightarrow> 'ri\<close>, wrapped
  by \<open>Mreturn o ext\<close> at the call): the intended instantiations project a by-value
  component out of the entry struct (e.g.\ the \<open>unat\<close> value of a (string, value)
  pair). A monadic \<open>ext\<close> (e.g.\ a deep copy) can reuse
  @{thm [source] phm_chain_find_impl_rule} directly at the chain level if ever
  needed; keeping the bucket-level parameter pure avoids higher-order unification
  headaches at the sepref layer.\<close>

lemma phm_bucket_find_impl_rule:
  assumes EEQ: \<open>\<And>e ei x' xi'. llvm_htriple (A e ei ** B x' xi') (eeq ei xi')
    (\<lambda>r. A e ei ** B x' xi' ** \<upharpoonleft>bool.assn (eabs x' e) r)\<close>
    and EXT: \<open>\<And>e ei. llvm_htriple (A e ei) (Mreturn (ext ei)) (\<lambda>r. A e ei ** R (fabs e) r)\<close>
  shows \<open>llvm_htriple
    (\<upharpoonleft>(phm_bucket_assn A) es p ** \<upharpoonleft>unat.assn k ki ** B x xi
       ** \<up>(\<exists>e\<in>set (phm_chain_of es k). eabs x e))
    (phm_bucket_find_impl eeq ext ki xi p)
    (\<lambda>r. \<upharpoonleft>(phm_bucket_assn A) es p ** \<upharpoonleft>unat.assn k ki ** B x xi
       ** R (fabs (the (find (eabs x) (phm_chain_of es k)))) r)\<close>
  unfolding pam_bucket_assn_conv ol_assn_conv
proof (induction es arbitrary: p)
  case Nil
  show ?case
    apply (subst phm_bucket_find_impl.simps)
    by vcg
next
  case (Cons e es)
  interpret llvm_prim_ctrl_setup .
  have EXT': \<open>llvm_htriple (A e ei) ((Mreturn o ext) ei) (\<lambda>r. A e ei ** R (fabs e) r)\<close>
    for e ei using EXT[of e ei] by simp
  note [vcg_rules] = Cons.IH
    phm_chain_find_impl_rule[where A = A and B = B and eabs = eabs and fabs = fabs
      and R = R, OF EEQ EXT']
  show ?case
    supply [simp, named_ss fri_prepare_simps] = ol_seg_cons
    supply [simp] = bool.assn_def sep_conj_exists
    apply (subst phm_bucket_find_impl.simps)
    apply (cases \<open>p = null\<close>; cases e; simp)
    by vcg
qed

subsubsection \<open>Insert\<close>

text \<open>Unconditional prepend into the chain at the key (creating a fresh singleton
  chain if the key is absent \<comment> \<open>appended at the bucket tail, where the walk ends,
  like \<^const>\<open>AList.update\<close>\<close>). The abstract counterpart:\<close>

fun phm_alist_ins :: \<open>nat \<Rightarrow> 'a \<Rightarrow> (nat \<times> 'a list) list \<Rightarrow> (nat \<times> 'a list) list\<close>
  where
  \<open>phm_alist_ins k x [] = [(k, [x])]\<close>
| \<open>phm_alist_ins k x ((k', ch) # es) =
    (if k' = k then (k', x # ch) # es else (k', ch) # phm_alist_ins k x es)\<close>

partial_function (M) phm_bucket_ins_impl ::
  \<open>64 word \<Rightarrow> 'ai \<Rightarrow> 'ai::llvm_rep phm_chain_impl pam_bucket_impl
    \<Rightarrow> 'ai phm_chain_impl pam_bucket_impl llM\<close>
  where
  \<open>phm_bucket_ins_impl k x p = (if p = null then doM {
      q \<leftarrow> os_prepend x null;
      os_prepend (k, q) null
    } else doM {
      n \<leftarrow> ll_load p;
      eq \<leftarrow> ll_icmp_eq (fst (node.val n)) k;
      if to_bool eq then doM {
        q \<leftarrow> os_prepend x (snd (node.val n));
        ll_store (Node (k, q) (node.next n)) p;
        Mreturn p
      } else doM {
        r \<leftarrow> phm_bucket_ins_impl k x (node.next n);
        ll_store (Node (node.val n) r) p;
        Mreturn p
      }
    })\<close>

lemma phm_bucket_ins_impl_rule:
  \<open>llvm_htriple
    (\<upharpoonleft>(phm_bucket_assn A) es p ** \<upharpoonleft>unat.assn k ki ** A x xi)
    (phm_bucket_ins_impl ki xi p)
    (\<lambda>r. \<upharpoonleft>(phm_bucket_assn A) (phm_alist_ins k x es) r ** \<upharpoonleft>unat.assn k ki)\<close>
  unfolding pam_bucket_assn_conv ol_assn_conv
proof (induction es arbitrary: p)
  case Nil
  show ?case
    \<comment> \<open>Both prepend rules must be pinned to the ambient \<open>A\<close>: with schematic
      assertion parameters vcg's higher-order unification tries degenerate
      instances against every atom in the state and the search blows up.\<close>
    supply [vcg_rules] = phm_chain_prepend_empty_rule[where A = A]
      pam_entry_prepend_empty_rule[where V = \<open>phm_chain_assn A\<close>]
    apply (subst phm_bucket_ins_impl.simps)
    by vcg
next
  case (Cons e es)
  interpret llvm_prim_ctrl_setup .
  note [vcg_rules] = Cons.IH phm_chain_prepend_rule
  show ?case
    supply [simp, named_ss fri_prepare_simps] = ol_seg_cons
    supply [simp] = bool.assn_def sep_conj_exists
    apply (subst phm_bucket_ins_impl.simps)
    apply (cases \<open>p = null\<close>; cases e; simp)
    by vcg
qed


subsection \<open>Map operations, hash value given\<close>

text \<open>The map-level operations take the (full 64-bit) hash value as an explicit
  argument and use it as the pam key; the abstract key is \<open>unat h\<close>. The
  \<open>\<upharpoonleft>unat.assn (unat h) h\<close> precondition of the bucket rules is trivially true:\<close>

lemma unat_assn_unat_self: \<open>\<upharpoonleft>unat.assn (unat h) h = \<box>\<close>
  by (simp add: unat.assn_def mk_pure_assn_def sep_algebra_simps)

text \<open>Bucket-rule variants with the key fixed to the hash and the trivial
  \<open>unat.assn\<close> atom removed, packaged for direct \<open>vcg_rules\<close> use.\<close>

lemma phm_bucket_member_impl_hash_rule:
  assumes EEQ: \<open>\<And>e ei x' xi'. llvm_htriple (A e ei ** B x' xi') (eeq ei xi')
    (\<lambda>r. A e ei ** B x' xi' ** \<upharpoonleft>bool.assn (eabs x' e) r)\<close>
  shows \<open>llvm_htriple
    (\<upharpoonleft>(phm_bucket_assn A) es p ** B x xi)
    (phm_bucket_member_impl eeq h xi p)
    (\<lambda>r. \<upharpoonleft>(phm_bucket_assn A) es p ** B x xi
       ** \<upharpoonleft>bool.assn (\<exists>e\<in>set (phm_chain_of es (unat h)). eabs x e) r)\<close>
  using phm_bucket_member_impl_rule[OF EEQ, where k = \<open>unat h\<close> and ki = h]
  by (simp add: unat_assn_unat_self sep_algebra_simps)

lemma phm_bucket_find_impl_hash_rule:
  assumes EEQ: \<open>\<And>e ei x' xi'. llvm_htriple (A e ei ** B x' xi') (eeq ei xi')
    (\<lambda>r. A e ei ** B x' xi' ** \<upharpoonleft>bool.assn (eabs x' e) r)\<close>
    and EXT: \<open>\<And>e ei. llvm_htriple (A e ei) (Mreturn (ext ei)) (\<lambda>r. A e ei ** R (fabs e) r)\<close>
  shows \<open>llvm_htriple
    (\<upharpoonleft>(phm_bucket_assn A) es p ** B x xi
       ** \<up>(\<exists>e\<in>set (phm_chain_of es (unat h)). eabs x e))
    (phm_bucket_find_impl eeq ext h xi p)
    (\<lambda>r. \<upharpoonleft>(phm_bucket_assn A) es p ** B x xi
       ** R (fabs (the (find (eabs x) (phm_chain_of es (unat h))))) r)\<close>
  using phm_bucket_find_impl_rule[where A = A and B = B and eabs = eabs
      and fabs = fabs and R = R and k = \<open>unat h\<close> and ki = h, OF EEQ EXT]
  by (simp add: unat_assn_unat_self sep_algebra_simps)

lemma phm_bucket_ins_impl_hash_rule:
  \<open>llvm_htriple
    (\<upharpoonleft>(phm_bucket_assn A) es p ** A x xi)
    (phm_bucket_ins_impl h xi p)
    (\<lambda>r. \<upharpoonleft>(phm_bucket_assn A) (phm_alist_ins (unat h) x es) r)\<close>
  using phm_bucket_ins_impl_rule[where k = \<open>unat h\<close> and ki = h]
  by (simp add: unat_assn_unat_self sep_algebra_simps)

text \<open>Creation and deallocation are pure instantiations of the pam ops.\<close>

abbreviation phm_map_impl_assn ::
  \<open>('a \<Rightarrow> 'ai::llvm_rep \<Rightarrow> assn)
    \<Rightarrow> ((nat \<times> 'a list) list list, 'ai phm_impl) dr_assn\<close> where
  \<open>phm_map_impl_assn A \<equiv> pam_assn (phm_chain_assn A)\<close>

definition phm_chain_free_impl ::
  \<open>('ai \<Rightarrow> unit llM) \<Rightarrow> 'ai::llvm_rep phm_chain_impl \<Rightarrow> unit llM\<close> where
  \<open>phm_chain_free_impl efree \<equiv> ol_delete efree\<close>

lemma phm_chain_assn_free:
  assumes \<open>MK_FREE A efree\<close>
  shows \<open>MK_FREE (\<upharpoonleft>(phm_chain_assn A)) (phm_chain_free_impl efree)\<close>
  unfolding phm_chain_free_impl_def phm_chain_assn_conv
  by (rule ol_assn_free[OF assms])

definition phm_free_impl ::
  \<open>('ai \<Rightarrow> unit llM) \<Rightarrow> 'ai::llvm_rep phm_impl \<Rightarrow> unit llM\<close> where
  \<open>phm_free_impl efree \<equiv> pam_free_impl (phm_chain_free_impl efree)\<close>

lemma phm_assn_free:
  assumes \<open>MK_FREE A efree\<close>
  shows \<open>MK_FREE (\<upharpoonleft>(phm_map_impl_assn A)) (phm_free_impl efree)\<close>
  unfolding phm_free_impl_def
  by (rule pam_assn_free[OF phm_chain_assn_free[OF assms]])

text \<open>Membership: bucket borrowed from the outer array, scanned read-only,
  rejoined unchanged.\<close>

definition phm_member_hashed_impl ::
  \<open>('ai \<Rightarrow> 'xi \<Rightarrow> 1 word llM) \<Rightarrow> 64 word \<Rightarrow> 'xi \<Rightarrow> 'ai::llvm_rep phm_impl
    \<Rightarrow> 1 word llM\<close>
  where
  \<open>phm_member_hashed_impl eeq h x \<equiv> \<lambda>(n, a). doM {
    i \<leftarrow> ll_urem h n;
    bin \<leftarrow> nao_nth a i;
    found \<leftarrow> phm_bucket_member_impl eeq h x bin;
    nao_rejoin a i;
    Mreturn found
  }\<close>

lemma phm_member_hashed_impl_rule:
  assumes EEQ: \<open>\<And>e ei x' xi'. llvm_htriple (A e ei ** B x' xi') (eeq ei xi')
    (\<lambda>r. A e ei ** B x' xi' ** \<upharpoonleft>bool.assn (eabs x' e) r)\<close>
  shows \<open>llvm_htriple
    (\<upharpoonleft>(phm_map_impl_assn A) bss p ** B x xi ** \<up>(bss \<noteq> []))
    (phm_member_hashed_impl eeq h xi p)
    (\<lambda>r. \<upharpoonleft>(phm_map_impl_assn A) bss p ** B x xi
       ** \<upharpoonleft>bool.assn (\<exists>e\<in>set (phm_chain_of
              (bss ! pam_bucket_of (length bss) (unat h)) (unat h)). eabs x e) r)\<close>
  unfolding phm_member_hashed_impl_def pam_assn_def pam_bucket_of_def
  supply [vcg_rules] = ll_urem_hash_snat_rule phm_bucket_member_impl_hash_rule[OF EEQ]
  apply (cases p; simp)
  by vcg

text \<open>The-lookup (asserted present).\<close>

definition phm_the_lookup_hashed_impl ::
  \<open>('ai \<Rightarrow> 'xi \<Rightarrow> 1 word llM) \<Rightarrow> ('ai \<Rightarrow> 'ri) \<Rightarrow> 64 word \<Rightarrow> 'xi
    \<Rightarrow> 'ai::llvm_rep phm_impl \<Rightarrow> 'ri::llvm_rep llM\<close>
  where
  \<open>phm_the_lookup_hashed_impl eeq ext h x \<equiv> \<lambda>(n, a). doM {
    i \<leftarrow> ll_urem h n;
    bin \<leftarrow> nao_nth a i;
    r \<leftarrow> phm_bucket_find_impl eeq ext h x bin;
    nao_rejoin a i;
    Mreturn r
  }\<close>

lemma phm_the_lookup_hashed_impl_rule:
  assumes EEQ: \<open>\<And>e ei x' xi'. llvm_htriple (A e ei ** B x' xi') (eeq ei xi')
    (\<lambda>r. A e ei ** B x' xi' ** \<upharpoonleft>bool.assn (eabs x' e) r)\<close>
    and EXT: \<open>\<And>e ei. llvm_htriple (A e ei) (Mreturn (ext ei)) (\<lambda>r. A e ei ** R (fabs e) r)\<close>
  shows \<open>llvm_htriple
    (\<upharpoonleft>(phm_map_impl_assn A) bss p ** B x xi ** \<up>(bss \<noteq> []
       \<and> (\<exists>e\<in>set (phm_chain_of (bss ! pam_bucket_of (length bss) (unat h)) (unat h)).
            eabs x e)))
    (phm_the_lookup_hashed_impl eeq ext h xi p)
    (\<lambda>r. \<upharpoonleft>(phm_map_impl_assn A) bss p ** B x xi
       ** R (fabs (the (find (eabs x)
              (phm_chain_of (bss ! pam_bucket_of (length bss) (unat h)) (unat h))))) r)\<close>
  unfolding phm_the_lookup_hashed_impl_def pam_assn_def pam_bucket_of_def
  supply [vcg_rules] = ll_urem_hash_snat_rule
    phm_bucket_find_impl_hash_rule[where A = A and B = B and eabs = eabs
      and fabs = fabs and R = R, OF EEQ EXT]
  apply (cases p; simp)
  by vcg

text \<open>Insert: the bucket is taken out, extended by the fused walk (head pointer
  changes iff the key was absent and the bucket rebuilt), and stored back.\<close>

definition phm_ins_hashed_impl ::
  \<open>64 word \<Rightarrow> 'ai \<Rightarrow> 'ai::llvm_rep phm_impl \<Rightarrow> 'ai phm_impl llM\<close>
  where
  \<open>phm_ins_hashed_impl h x \<equiv> \<lambda>(n, a). doM {
    i \<leftarrow> ll_urem h n;
    bin \<leftarrow> nao_nth a i;
    bin \<leftarrow> phm_bucket_ins_impl h x bin;
    a \<leftarrow> nao_upd a i bin;
    Mreturn (n, a)
  }\<close>

definition phm_pam_ins :: \<open>nat \<Rightarrow> 'a \<Rightarrow> (nat \<times> 'a list) list list
    \<Rightarrow> (nat \<times> 'a list) list list\<close> where
  \<open>phm_pam_ins k x bss = (let i = pam_bucket_of (length bss) k in
     bss[i := phm_alist_ins k x (bss ! i)])\<close>

lemma phm_ins_hashed_impl_rule:
  \<open>llvm_htriple
    (\<upharpoonleft>(phm_map_impl_assn A) bss p ** A x xi ** \<up>(bss \<noteq> []))
    (phm_ins_hashed_impl h xi p)
    (\<lambda>r. \<upharpoonleft>(phm_map_impl_assn A) (phm_pam_ins (unat h) x bss) r)\<close>
  unfolding phm_ins_hashed_impl_def pam_assn_def phm_pam_ins_def Let_def
    pam_bucket_of_def
  supply [vcg_rules] = ll_urem_hash_snat_rule phm_bucket_ins_impl_hash_rule
  apply (cases p; simp)
  by vcg


subsection \<open>Wrappers over hash functions\<close>

text \<open>Two hash parameters: \<open>hashx\<close> hashes a \<^emph>\<open>probe\<close> (tied to \<open>hk x\<close> on the
  abstract key), \<open>hashe\<close> hashes an \<^emph>\<open>entry\<close> (tied to \<open>hk (kabs e)\<close>); instances
  derive both from the same string-hash code.\<close>

definition phm_member_impl ::
  \<open>('xi \<Rightarrow> 64 word llM) \<Rightarrow> ('ai \<Rightarrow> 'xi \<Rightarrow> 1 word llM) \<Rightarrow> 'xi
    \<Rightarrow> 'ai::llvm_rep phm_impl \<Rightarrow> 1 word llM\<close>
  where
  \<open>phm_member_impl hashx eeq x p \<equiv> doM { h \<leftarrow> hashx x; phm_member_hashed_impl eeq h x p }\<close>

lemma phm_member_impl_rule:
  assumes HASHX: \<open>\<And>x' xi'. llvm_htriple (B x' xi') (hashx xi')
      (\<lambda>r. B x' xi' ** \<up>(r = hx x'))\<close>
    and EEQ: \<open>\<And>e ei x' xi'. llvm_htriple (A e ei ** B x' xi') (eeq ei xi')
      (\<lambda>r. A e ei ** B x' xi' ** \<upharpoonleft>bool.assn (eabs x' e) r)\<close>
  shows \<open>llvm_htriple
    (\<upharpoonleft>(phm_map_impl_assn A) bss p ** B x xi ** \<up>(bss \<noteq> []))
    (phm_member_impl hashx eeq xi p)
    (\<lambda>r. \<upharpoonleft>(phm_map_impl_assn A) bss p ** B x xi
       ** \<upharpoonleft>bool.assn (\<exists>e\<in>set (phm_chain_of
              (bss ! pam_bucket_of (length bss) (unat (hx x))) (unat (hx x))).
            eabs x e) r)\<close>
  unfolding phm_member_impl_def
  supply [vcg_rules] = HASHX phm_member_hashed_impl_rule[OF EEQ]
  by vcg

definition phm_the_lookup_impl ::
  \<open>('xi \<Rightarrow> 64 word llM) \<Rightarrow> ('ai \<Rightarrow> 'xi \<Rightarrow> 1 word llM) \<Rightarrow> ('ai \<Rightarrow> 'ri) \<Rightarrow> 'xi
    \<Rightarrow> 'ai::llvm_rep phm_impl \<Rightarrow> 'ri::llvm_rep llM\<close>
  where
  \<open>phm_the_lookup_impl hashx eeq ext x p \<equiv>
     doM { h \<leftarrow> hashx x; phm_the_lookup_hashed_impl eeq ext h x p }\<close>

lemma phm_the_lookup_impl_rule:
  assumes HASHX: \<open>\<And>x' xi'. llvm_htriple (B x' xi') (hashx xi')
      (\<lambda>r. B x' xi' ** \<up>(r = hx x'))\<close>
    and EEQ: \<open>\<And>e ei x' xi'. llvm_htriple (A e ei ** B x' xi') (eeq ei xi')
      (\<lambda>r. A e ei ** B x' xi' ** \<upharpoonleft>bool.assn (eabs x' e) r)\<close>
    and EXT: \<open>\<And>e ei. llvm_htriple (A e ei) (Mreturn (ext ei)) (\<lambda>r. A e ei ** R (fabs e) r)\<close>
  shows \<open>llvm_htriple
    (\<upharpoonleft>(phm_map_impl_assn A) bss p ** B x xi ** \<up>(bss \<noteq> []
       \<and> (\<exists>e\<in>set (phm_chain_of
              (bss ! pam_bucket_of (length bss) (unat (hx x))) (unat (hx x))).
            eabs x e)))
    (phm_the_lookup_impl hashx eeq ext xi p)
    (\<lambda>r. \<upharpoonleft>(phm_map_impl_assn A) bss p ** B x xi
       ** R (fabs (the (find (eabs x) (phm_chain_of
              (bss ! pam_bucket_of (length bss) (unat (hx x))) (unat (hx x)))))) r)\<close>
  unfolding phm_the_lookup_impl_def
  supply [vcg_rules] = HASHX
    phm_the_lookup_hashed_impl_rule[where A = A and B = B and eabs = eabs
      and fabs = fabs and R = R, OF EEQ EXT]
  by vcg

definition phm_ins_impl ::
  \<open>('ai \<Rightarrow> 64 word llM) \<Rightarrow> 'ai \<Rightarrow> 'ai::llvm_rep phm_impl \<Rightarrow> 'ai phm_impl llM\<close>
  where
  \<open>phm_ins_impl hashe x p \<equiv> doM { h \<leftarrow> hashe x; phm_ins_hashed_impl h x p }\<close>

lemma phm_ins_impl_rule:
  assumes HASHE: \<open>\<And>e ei. llvm_htriple (A e ei) (hashe ei)
      (\<lambda>r. A e ei ** \<up>(r = he e))\<close>
  shows \<open>llvm_htriple
    (\<upharpoonleft>(phm_map_impl_assn A) bss p ** A x xi ** \<up>(bss \<noteq> []))
    (phm_ins_impl hashe xi p)
    (\<lambda>r. \<upharpoonleft>(phm_map_impl_assn A) (phm_pam_ins (unat (he x)) x bss) r)\<close>
  unfolding phm_ins_impl_def
  supply [vcg_rules] = HASHE phm_ins_hashed_impl_rule
  by vcg


subsection \<open>Pam-level abstraction of insert\<close>

text \<open>The read-only operations are covered by the exported pam lemmas
  (@{thm pam_map_of_bucket}); insert needs its own invariant-preservation and
  abstraction lemmas, following \<open>pam_upd_invar\<close>/\<open>pam_upd_abs\<close>. The chain stored
  under a key, at the abstract-map level:\<close>

definition phm_mchain :: \<open>(nat \<rightharpoonup> 'a list) \<Rightarrow> nat \<Rightarrow> 'a list\<close> where
  \<open>phm_mchain m k = (case m k of None \<Rightarrow> [] | Some ch \<Rightarrow> ch)\<close>

lemma phm_chain_of_mchain: \<open>phm_chain_of es k = phm_mchain (map_of es) k\<close>
  unfolding phm_chain_of_def phm_mchain_def ..

text \<open>AList-style facts about \<^const>\<open>phm_alist_ins\<close>.\<close>

lemma fst_set_phm_alist_ins:
  \<open>fst ` set (phm_alist_ins k x es) = insert k (fst ` set es)\<close>
  by (induction es rule: phm_alist_ins.induct) auto

lemma distinct_phm_alist_ins:
  \<open>distinct (map fst es) \<Longrightarrow> distinct (map fst (phm_alist_ins k x es))\<close>
  by (induction es rule: phm_alist_ins.induct)
    (auto simp: fst_set_phm_alist_ins)

lemma set_phm_alist_ins_subset:
  \<open>set (phm_alist_ins k x es) \<subseteq> insert (k, x # phm_chain_of es k) (set es)\<close>
  by (induction es rule: phm_alist_ins.induct) auto

lemma map_of_phm_alist_ins:
  \<open>map_of (phm_alist_ins k x es) = (map_of es)(k \<mapsto> x # phm_chain_of es k)\<close>
  by (induction es rule: phm_alist_ins.induct) (auto simp: fun_upd_twist)

text \<open>Lifting to bucket lists, under \<^const>\<open>pam_invar\<close>. The concat-splitting
  helpers of \<^file>\<open>IICF_Assoc_Map.thy\<close> are \<open>private\<close> there, so they are re-derived
  here (same skeleton).\<close>

context
  fixes bss :: \<open>(nat \<times> 'a list) list list\<close> and k :: nat
  assumes I: \<open>pam_invar bss\<close>
begin

private lemma NE: \<open>bss \<noteq> []\<close>
  and D: \<open>distinct (map fst (concat bss))\<close>
  using I by (auto simp: pam_invar_def)

private lemma B: \<open>j < length bss \<Longrightarrow> (k', v') \<in> set (bss ! j)
  \<Longrightarrow> pam_bucket_of (length bss) k' = j\<close> for j k' v'
  using I by (auto simp: pam_invar_def)

private lemma IB: \<open>pam_bucket_of (length bss) k < length bss\<close>
  using NE by simp

private lemma concat_orig:
  \<open>concat bss = concat (take (pam_bucket_of (length bss) k) bss)
     @ bss ! pam_bucket_of (length bss) k
     @ concat (drop (Suc (pam_bucket_of (length bss) k)) bss)\<close>
proof -
  have \<open>bss = take (pam_bucket_of (length bss) k) bss
     @ bss ! pam_bucket_of (length bss) k
     # drop (Suc (pam_bucket_of (length bss) k)) bss\<close>
    by (rule id_take_nth_drop[OF IB])
  then show ?thesis
    by (metis concat.simps(2) concat_append)
qed

private lemma concat_upd:
  \<open>concat (bss[pam_bucket_of (length bss) k := b])
   = concat (take (pam_bucket_of (length bss) k) bss)
     @ b @ concat (drop (Suc (pam_bucket_of (length bss) k)) bss)\<close> for b
proof -
  have \<open>bss[pam_bucket_of (length bss) k := b]
     = take (pam_bucket_of (length bss) k) bss
       @ b # drop (Suc (pam_bucket_of (length bss) k)) bss\<close>
    by (rule upd_conv_take_nth_drop[OF IB])
  then show ?thesis
    by (metis concat.simps(2) concat_append)
qed

private lemma take_nomem:
  \<open>k \<notin> fst ` set (concat (take (pam_bucket_of (length bss) k) bss))\<close>
proof
  assume \<open>k \<in> fst ` set (concat (take (pam_bucket_of (length bss) k) bss))\<close>
  then obtain ys where Y: \<open>ys \<in> set (take (pam_bucket_of (length bss) k) bss)\<close>
    \<open>k \<in> fst ` set ys\<close> by auto
  from Y(1) obtain j where J: \<open>j < pam_bucket_of (length bss) k\<close> \<open>ys = bss ! j\<close>
    using IB by (auto simp: in_set_conv_nth)
  from Y(2) J obtain v' where \<open>(k, v') \<in> set (bss ! j)\<close> by auto
  with B[of j] J IB show False by auto
qed

private lemma drop_nomem:
  \<open>k \<notin> fst ` set (concat (drop (Suc (pam_bucket_of (length bss) k)) bss))\<close>
proof
  assume \<open>k \<in> fst ` set (concat (drop (Suc (pam_bucket_of (length bss) k)) bss))\<close>
  then obtain ys where Y: \<open>ys \<in> set (drop (Suc (pam_bucket_of (length bss) k)) bss)\<close>
    \<open>k \<in> fst ` set ys\<close> by auto
  from Y(1) obtain j where J: \<open>Suc (pam_bucket_of (length bss) k) + j < length bss\<close>
    \<open>ys = bss ! (Suc (pam_bucket_of (length bss) k) + j)\<close>
    by (metis in_set_drop_conv_nth le_Suc_ex)
  from Y(2) J obtain v' where
    \<open>(k, v') \<in> set (bss ! (Suc (pam_bucket_of (length bss) k) + j))\<close> by auto
  with B[of \<open>Suc (pam_bucket_of (length bss) k) + j\<close>] J show False
    by (metis lessI not_add_less1)
qed

private lemma take_None:
  \<open>map_of (concat (take (pam_bucket_of (length bss) k) bss)) k = None\<close>
  using take_nomem by (simp add: map_of_eq_None_iff)

private lemma drop_None:
  \<open>map_of (concat (drop (Suc (pam_bucket_of (length bss) k)) bss)) k = None\<close>
  using drop_nomem by (simp add: map_of_eq_None_iff)

lemma phm_pam_ins_invar: \<open>pam_invar (phm_pam_ins k x bss)\<close> for x
proof -
  let ?ib = \<open>pam_bucket_of (length bss) k\<close>
  let ?b' = \<open>phm_alist_ins k x (bss ! ?ib)\<close>
  have D3: \<open>distinct (map fst (concat (take ?ib bss)) @ map fst (bss ! ?ib)
    @ map fst (concat (drop (Suc ?ib) bss)))\<close>
    using D by (metis concat_orig map_append)
  have DIST: \<open>distinct (map fst (concat (bss[?ib := ?b'])))\<close>
    using D3 take_nomem drop_nomem
    by (auto simp: concat_upd fst_set_phm_alist_ins distinct_phm_alist_ins)
  have BUCK: \<open>pam_bucket_of (length bss) k' = j\<close>
    if J: \<open>j < length bss\<close> and E: \<open>(k', v') \<in> set (bss[?ib := ?b'] ! j)\<close> for j k' v'
  proof (cases \<open>j = ?ib\<close>)
    case False
    with E J have \<open>(k', v') \<in> set (bss ! j)\<close> by simp
    with B J show ?thesis by simp
  next
    case True
    with E J IB have \<open>(k', v') \<in> set ?b'\<close> by simp
    with set_phm_alist_ins_subset
    have \<open>(k', v') \<in> insert (k, x # phm_chain_of (bss ! ?ib) k) (set (bss ! ?ib))\<close>
      by fastforce
    with B[of ?ib] IB True show ?thesis by auto
  qed
  have NE': \<open>bss[?ib := ?b'] \<noteq> []\<close>
    by (metis NE length_0_conv length_list_update)
  show ?thesis
    using NE' DIST BUCK
    unfolding phm_pam_ins_def Let_def pam_invar_def
    by (metis (mono_tags, lifting) case_prodI2 length_list_update)
qed

lemma phm_pam_ins_abs:
  \<open>pam_map_of (phm_pam_ins k x bss)
   = (pam_map_of bss)(k \<mapsto> x # phm_mchain (pam_map_of bss) k)\<close> for x
proof -
  have CH: \<open>phm_chain_of (bss ! pam_bucket_of (length bss) k) k
      = phm_mchain (pam_map_of bss) k\<close>
    unfolding phm_chain_of_mchain phm_mchain_def
    by (simp add: pam_map_of_bucket[OF I])
  show ?thesis
    unfolding pam_map_of_def comp_def phm_pam_ins_def Let_def
    apply (subst concat_upd)
    apply (subst concat_orig)
    apply (rule ext)
    subgoal for k'
      using CH
      by (cases \<open>k' = k\<close>)
        (auto simp: map_of_append map_add_def map_of_phm_alist_ins
          phm_chain_of_mchain phm_mchain_def
          pam_map_of_def take_None drop_None split: option.splits)
    done
qed

lemma phm_member_correct:
  \<open>(\<exists>e\<in>set (phm_chain_of (bss ! pam_bucket_of (length bss) k) k). eabs e)
   \<longleftrightarrow> (\<exists>e\<in>set (phm_mchain (pam_map_of bss) k). eabs e)\<close> for eabs
  unfolding phm_chain_of_mchain phm_mchain_def
  by (simp add: pam_map_of_bucket[OF I])

lemma phm_find_correct:
  \<open>find eabs (phm_chain_of (bss ! pam_bucket_of (length bss) k) k)
   = find eabs (phm_mchain (pam_map_of bss) k)\<close> for eabs
  unfolding phm_chain_of_mchain phm_mchain_def
  by (simp add: pam_map_of_bucket[OF I])

end


subsection \<open>Key-level abstraction\<close>

text \<open>From \<open>nat \<rightharpoonup> 'a list\<close> (hash to chain) to \<open>'k \<rightharpoonup> 'a\<close> (key to entry), given the
  key projection \<open>kabs\<close> and abstract hash \<open>hk\<close>. At this layer the matching
  predicate is fixed to key equality, \<open>eabs x e = (kabs e = x)\<close>. No invariant is
  needed: the abstraction function reads exactly the chain the operations write.\<close>

definition phm_map_of :: \<open>('a \<Rightarrow> 'k) \<Rightarrow> ('k \<Rightarrow> 64 word) \<Rightarrow> (nat \<rightharpoonup> 'a list) \<Rightarrow> ('k \<rightharpoonup> 'a)\<close>
  where
  \<open>phm_map_of kabs hk m x = find (\<lambda>e. kabs e = x) (phm_mchain m (unat (hk x)))\<close>

definition phm_rel :: \<open>('a \<Rightarrow> 'k) \<Rightarrow> ('k \<Rightarrow> 64 word)
    \<Rightarrow> ((nat \<rightharpoonup> 'a list) \<times> ('k \<rightharpoonup> 'a)) set\<close> where
  \<open>phm_rel kabs hk \<equiv> br (phm_map_of kabs hk) (\<lambda>_. True)\<close>

lemma phm_map_of_empty[simp]: \<open>phm_map_of kabs hk Map.empty = Map.empty\<close>
  unfolding phm_map_of_def phm_mchain_def by auto

lemma phm_member_abs:
  \<open>(\<exists>e\<in>set (phm_mchain m (unat (hk x))). kabs e = x)
   \<longleftrightarrow> phm_map_of kabs hk m x \<noteq> None\<close>
  unfolding phm_map_of_def
  by (auto simp: find_None_iff)

lemma phm_the_lookup_abs:
  \<open>the (find (\<lambda>e. kabs e = x) (phm_mchain m (unat (hk x))))
   = the (phm_map_of kabs hk m x)\<close>
  unfolding phm_map_of_def ..

lemma phm_ins_abs:
  \<open>phm_map_of kabs hk (m(unat (hk (kabs e)) \<mapsto> e # phm_mchain m (unat (hk (kabs e)))))
   = (phm_map_of kabs hk m)(kabs e \<mapsto> e)\<close>
  apply (rule ext)
  subgoal for x
    unfolding phm_map_of_def phm_mchain_def
    by (cases \<open>x = kabs e\<close>; cases \<open>unat (hk x) = unat (hk (kabs e))\<close>)
      (auto split: option.splits)
  done


subsection \<open>The map interface\<close>

text \<open>Composed assertion: pam's map assertion instantiated at chains, then one more
  \<open>hr_comp\<close> step through \<^const>\<open>phm_rel\<close>.\<close>

definition phm_map_assn :: \<open>('a \<Rightarrow> 'k) \<Rightarrow> ('k \<Rightarrow> 64 word)
    \<Rightarrow> ('a, 'ai::llvm_rep) dr_assn \<Rightarrow> ('k \<rightharpoonup> 'a) \<Rightarrow> 'ai phm_impl \<Rightarrow> assn\<close>
  where
  \<open>phm_map_assn kabs hk A \<equiv> hr_comp (pam_map_assn (phm_chain_assn (\<upharpoonleft>A))) (phm_rel kabs hk)\<close>

lemma phm_map_assn_intf[intf_of_assn]:
  \<open>intf_of_assn (\<upharpoonleft>A) TYPE('a) \<Longrightarrow> intf_of_assn (phm_map_assn kabs hk A) TYPE(('k, 'a) i_map)\<close>
  by simp

text \<open>Deallocation.\<close>

lemma phm_map_assn_free[sepref_frame_free_rules]:
  assumes \<open>MK_FREE (\<upharpoonleft>A) efree\<close>
  shows \<open>MK_FREE (phm_map_assn kabs hk A) (phm_free_impl efree)\<close>
  unfolding phm_map_assn_def pam_map_assn_def phm_free_impl_def
  by (intro MK_FREE_hrcompI pam_assn_free phm_chain_assn_free assms)

text \<open>Creation: literally the pam constructor, composed one relation step further.
  NOT declared \<open>[sepref_fr_rules]\<close>: \<open>op_map_empty\<close> is a producer op (cf.\ the
  custom-empty notes in \<^file>\<open>IICF_Hash_Set.thy\<close>); instances register a custom
  empty op.\<close>

lemma phm_empty_rel:
  \<open>(uncurry0 (RETURN op_map_empty), uncurry0 (RETURN op_map_empty))
     \<in> unit_rel \<rightarrow>\<^sub>f \<langle>phm_rel kabs hk\<rangle>nres_rel\<close>
  apply (rule fref_param0I)
  by (auto simp: phm_rel_def in_br_conv op_map_empty_def intro!: nres_relI)

lemmas phm_empty_hnr =
  pam_empty_hnr[where V = \<open>phm_chain_assn (\<upharpoonleft>A)\<close>, FCOMP phm_empty_rel,
    folded phm_map_assn_def] for A

text \<open>Membership. The hnr statement is against \<^const>\<open>op_map_contains_key\<close>, with
  the probe refined by an arbitrary (possibly impure) key assertion \<open>B\<close> whose
  abstract side is the map's key type.\<close>

lemma phm_member_hnr:
  assumes HASHX: \<open>\<And>x' xi'. llvm_htriple (\<upharpoonleft>B x' xi') (hashx xi')
      (\<lambda>r. \<upharpoonleft>B x' xi' ** \<up>(r = hk x'))\<close>
    and EEQ: \<open>\<And>e ei x' xi'. llvm_htriple (\<upharpoonleft>A e ei ** \<upharpoonleft>B x' xi') (eeq ei xi')
      (\<lambda>r. \<upharpoonleft>A e ei ** \<upharpoonleft>B x' xi' ** \<upharpoonleft>bool.assn (kabs e = x') r)\<close>
  shows \<open>(uncurry (phm_member_impl hashx eeq), uncurry (RETURN oo op_map_contains_key))
    \<in> (\<upharpoonleft>B)\<^sup>k *\<^sub>a (phm_map_assn kabs hk A)\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding phm_map_assn_def pam_map_assn_def bool1_rel_def bool.assn_is_rel[symmetric]
  apply sepref_to_hoare
  supply [vcg_rules] = phm_member_impl_rule[where A = \<open>\<upharpoonleft>A\<close> and B = \<open>\<upharpoonleft>B\<close>
    and eabs = \<open>\<lambda>x' e. kabs e = x'\<close> and hx = hk, OF HASHX EEQ]
  supply [simp] = hr_comp_def phm_rel_def pam_rel_def in_br_conv sep_conj_exists
    phm_member_correct phm_member_abs op_map_contains_key_def
  by vcg

text \<open>Insert. Consumes the entry (\<open>A\<^sup>d\<close>) \<comment> \<open>the natural mode for a sharing-free
  logic; callers build the entry (copying borrowed parts) and hand it over.\<close>
  The abstract operation updates the map at the entry's own key:\<close>

definition phm_upd :: \<open>('a \<Rightarrow> 'k) \<Rightarrow> 'a \<Rightarrow> ('k \<rightharpoonup> 'a) \<Rightarrow> ('k \<rightharpoonup> 'a)\<close> where
  \<open>phm_upd kabs e m = m(kabs e \<mapsto> e)\<close>

context
begin

text \<open>Residual reassembly entailment of the insert hnr proof, stated verbatim
  (the simp set dissolves the two \<open>hr_comp\<close> layers into one plain-HOL existential
  over the updated bucket list).\<close>

private lemma phm_ins_hnr_aux:
  assumes I: \<open>pam_invar bss\<close>
  shows \<open>\<upharpoonleft>(phm_map_impl_assn (\<upharpoonleft>A)) (phm_pam_ins (unat (hk (kabs e))) e bss) ci \<turnstile>
    (\<lambda>s. \<exists>m'. pam_invar m' \<and>
       phm_map_of kabs hk (pam_map_of m')
         = (phm_map_of kabs hk (pam_map_of bss))(kabs e \<mapsto> e) \<and>
       \<upharpoonleft>(phm_map_impl_assn (\<upharpoonleft>A)) m' ci s)\<close>
  apply (rule entails_exI[where x = \<open>phm_pam_ins (unat (hk (kabs e))) e bss\<close>])
  by (simp add: phm_pam_ins_invar[OF I] phm_pam_ins_abs[OF I] phm_ins_abs entails_refl)

lemma phm_ins_hnr:
  assumes HASHE: \<open>\<And>e ei. llvm_htriple (\<upharpoonleft>A e ei) (hashe ei)
      (\<lambda>r. \<upharpoonleft>A e ei ** \<up>(r = hk (kabs e)))\<close>
  shows \<open>(uncurry (phm_ins_impl hashe), uncurry (RETURN oo (phm_upd kabs)))
    \<in> (\<upharpoonleft>A)\<^sup>d *\<^sub>a (phm_map_assn kabs hk A)\<^sup>d \<rightarrow>\<^sub>a phm_map_assn kabs hk A\<close>
  unfolding phm_map_assn_def pam_map_assn_def
  apply sepref_to_hoare
  supply [vcg_rules] = phm_ins_impl_rule[OF HASHE]
  supply [simp] = hr_comp_def phm_rel_def pam_rel_def in_br_conv sep_conj_exists
  apply vcg
  subgoal
    unfolding vcg_tag_defs ENTAILS_def
    apply (simp add: phm_upd_def sep_algebra_simps pred_lift_extract_simps)
    by (rule phm_ins_hnr_aux; assumption)
  done

end

text \<open>The-lookup. Presence is an assertion of the abstract (mop-style) operation,
  so composition never has to represent an option. Generic in the extraction
  \<open>ext\<close>/\<open>fabs\<close>/\<open>R\<close> \<comment> \<open>for entries that are (key, pure value) pairs, \<open>ext = snd\<close>
  returns the value with no copy at all.\<close>\<close>

definition phm_the_lookup :: \<open>('a \<Rightarrow> 'r) \<Rightarrow> 'k \<Rightarrow> ('k \<rightharpoonup> 'a) \<Rightarrow> 'r nres\<close> where
  \<open>phm_the_lookup fabs x m = do { ASSERT (m x \<noteq> None); RETURN (fabs (the (m x))) }\<close>

context
begin

private lemma phm_the_lookup_reassemble:
  assumes S: \<open>phm_map_of kabs hk (pam_map_of bss) x = Some y\<close>
    and I: \<open>pam_invar bss\<close>
  shows \<open>ENTAILS
    (\<upharpoonleft>(phm_map_impl_assn (\<upharpoonleft>A)) bss ci ** \<upharpoonleft>B x xi
       ** \<upharpoonleft>R (fabs (the (find (\<lambda>e. kabs e = x) (phm_chain_of
              (bss ! pam_bucket_of (length bss) (unat (hk x))) (unat (hk x)))))) ri)
    (\<lambda>s. \<exists>m' bss' rr. (\<upharpoonleft>B x xi \<and>* \<upharpoonleft>(phm_map_impl_assn (\<upharpoonleft>A)) bss' ci \<and>*
       \<up>(m' = pam_map_of bss' \<and> pam_invar bss') \<and>*
       \<up>(phm_map_of kabs hk (pam_map_of bss) = phm_map_of kabs hk m') \<and>*
       \<up>True \<and>* \<upharpoonleft>R rr ri \<and>* \<up>(rr = fabs y)) s)\<close>
proof -
  have F: \<open>find (\<lambda>e. kabs e = x) (phm_chain_of
      (bss ! pam_bucket_of (length bss) (unat (hk x))) (unat (hk x))) = Some y\<close>
    using S unfolding phm_map_of_def by (simp add: phm_find_correct[OF I])
  show ?thesis
    unfolding vcg_tag_defs ENTAILS_def
    apply (rule entails_exI[where x = \<open>pam_map_of bss\<close>])
    apply (rule entails_exI[where x = bss])
    apply (rule entails_exI[where x = \<open>fabs y\<close>])
    apply (simp add: F I sep_algebra_simps pred_lift_extract_simps)
    by (simp add: sep_conj_aci entails_refl)
qed

lemma phm_the_lookup_hnr:
  assumes HASHX: \<open>\<And>x' xi'. llvm_htriple (\<upharpoonleft>B x' xi') (hashx xi')
      (\<lambda>r. \<upharpoonleft>B x' xi' ** \<up>(r = hk x'))\<close>
    and EEQ: \<open>\<And>e ei x' xi'. llvm_htriple (\<upharpoonleft>A e ei ** \<upharpoonleft>B x' xi') (eeq ei xi')
      (\<lambda>r. \<upharpoonleft>A e ei ** \<upharpoonleft>B x' xi' ** \<upharpoonleft>bool.assn (kabs e = x') r)\<close>
    and EXT: \<open>\<And>e ei. llvm_htriple (\<upharpoonleft>A e ei) (Mreturn (ext ei))
      (\<lambda>r. \<upharpoonleft>A e ei ** \<upharpoonleft>R (fabs e) r)\<close>
  shows \<open>(uncurry (phm_the_lookup_impl hashx eeq ext), uncurry (phm_the_lookup fabs))
    \<in> (\<upharpoonleft>B)\<^sup>k *\<^sub>a (phm_map_assn kabs hk A)\<^sup>k \<rightarrow>\<^sub>a \<upharpoonleft>R\<close>
  unfolding phm_map_assn_def pam_map_assn_def
  apply sepref_to_hoare
  supply [vcg_rules] = phm_the_lookup_impl_rule[where A = \<open>\<upharpoonleft>A\<close> and B = \<open>\<upharpoonleft>B\<close>
    and eabs = \<open>\<lambda>x' e. kabs e = x'\<close> and fabs = fabs and R = \<open>\<upharpoonleft>R\<close> and hx = hk,
    OF HASHX EEQ EXT]
  supply [simp] = hr_comp_def phm_rel_def pam_rel_def in_br_conv sep_conj_exists
    phm_member_correct phm_member_abs phm_the_lookup_def refine_pw_simps
  apply vcg
  subgoal
    by (rule phm_the_lookup_reassemble; assumption)
  done

end

text \<open>
  Open points:
  \<^item> \<^bold>\<open>Code export\<close>: all walks and wrappers are higher-order in
    \<open>eeq\<close>/\<open>ext\<close>/\<open>hashx\<close>/\<open>hashe\<close>/\<open>efree\<close>; each concrete instantiation must be
    specialized into first-order \<open>[llvm_code]\<close> definitions before export.
  \<^item> \<^bold>\<open>Delete\<close> is not implemented (not needed for the shared-variables store);
    the fused walk would mirror \<open>pam_bucket_delete_impl\<close> with an inner chain
    filter.
  \<^item> \<^bold>\<open>Registration\<close>: the hnr lemmas are deliberately \<^emph>\<open>not\<close> \<open>[sepref_fr_rules]\<close>;
    their Hoare-triple premises are not solvable by sepref's constraint solver.
    Instances discharge the premises once and register the closed rules.
\<close>


subsection \<open>Code equations for the first-order operations\<close>

text \<open>The insert walk and its hashed wrapper carry no function parameters, so their
  code equations can be registered generically; all other walks and wrappers are
  higher-order in \<open>eeq\<close>/\<open>ext\<close>/\<open>hashx\<close>/\<open>hashe\<close>/\<open>efree\<close> and are specialized per
  instance (see the string instantiation in \<open>String_Assn.thy\<close>).\<close>

lemmas [llvm_code] = phm_bucket_ins_impl.simps

lemma phm_ins_hashed_impl_code[llvm_code]:
  \<open>phm_ins_hashed_impl h x s = (case s of (n, a) \<Rightarrow> doM {
      i \<leftarrow> ll_urem h n;
      bin \<leftarrow> nao_nth a i;
      bin \<leftarrow> phm_bucket_ins_impl h x bin;
      a \<leftarrow> nao_upd a i bin;
      Mreturn (n, a)
    })\<close>
  unfolding phm_ins_hashed_impl_def by (simp split: prod.split)


subsection \<open>Tests\<close>

experiment
begin

text \<open>End-to-end sanity checks with a concrete heap-owning entry type: entries are
  (64-word key, 64-word-list payload) pairs where the payload is an owning open
  list \<comment> \<open>impure, so this exercises the ownership plumbing.\<close> The probe is the bare
  key word; \<open>kabs = fst\<close>, matching compares the key components, extraction
  projects the (pure) key \<comment> \<open>the (string, unat) instantiation will look exactly
  like this with the roles of the components swapped.\<close>\<close>

text \<open>The entry assertion must be a \<^emph>\<open>named constant\<close> with an applied-form simp,
  NOT a raw lambda: as a lambda, vcg's extraction normalizes the pure key
  component \<^emph>\<open>inside\<close> the chain-assertion parameter on the state side only
  (\<open>\<upharpoonleft>unat.assn \<leadsto> \<up>\<flat>\<^sub>punat.assn\<close>), after which pre- and postcondition disagree on
  the assertion function forever (the composite-parameter recipe from
  \<^file>\<open>IICF_Assoc_Map.thy\<close>).\<close>

definition test_entry_assn :: \<open>nat \<times> 64 word list \<Rightarrow> 64 word \<times> 64 word os_list \<Rightarrow> assn\<close>
  where
  \<open>test_entry_assn \<equiv> \<lambda>(k, vs) (ki, vsi). \<upharpoonleft>unat.assn k ki ** \<upharpoonleft>os_list_assn vs vsi\<close>

lemma test_entry_assn_pair[simp]:
  \<open>test_entry_assn (k, vs) (ki, vsi) = (\<upharpoonleft>unat.assn k ki ** \<upharpoonleft>os_list_assn vs vsi)\<close>
  unfolding test_entry_assn_def by simp

abbreviation test_probe_assn :: \<open>nat \<Rightarrow> 64 word \<Rightarrow> assn\<close> where
  \<open>test_probe_assn \<equiv> \<upharpoonleft>unat.assn\<close>

definition test_eeq :: \<open>64 word \<times> 64 word os_list \<Rightarrow> 64 word \<Rightarrow> 1 word llM\<close> where
  \<open>test_eeq e x \<equiv> ll_icmp_eq (fst e) x\<close>

lemma test_eeq_rule:
  \<open>llvm_htriple
    (test_entry_assn e ei ** test_probe_assn x xi)
    (test_eeq ei xi)
    (\<lambda>r. test_entry_assn e ei ** test_probe_assn x xi ** \<upharpoonleft>bool.assn (fst e = x) r)\<close>
  unfolding test_eeq_def
  apply (cases e; cases ei; simp)
  by vcg

text \<open>Chain member on a two-entry chain finds the first key\<dots>\<close>

lemma test_chain_member:
  \<open>llvm_htriple
    (\<upharpoonleft>(phm_chain_assn test_entry_assn) [(k1, vs1), (k2, vs2)] p
       ** test_probe_assn k1 k1i)
    (phm_chain_member_impl test_eeq k1i p)
    (\<lambda>r. \<upharpoonleft>(phm_chain_assn test_entry_assn) [(k1, vs1), (k2, vs2)] p
       ** test_probe_assn k1 k1i ** \<upharpoonleft>bool.assn True r)\<close>
  supply [vcg_rules] = phm_chain_member_impl_rule[where A = test_entry_assn
    and B = test_probe_assn and eabs = \<open>\<lambda>x e. fst e = x\<close>, OF test_eeq_rule]
  by vcg

text \<open>\<dots>and the fused bucket insert-then-member round-trip works on an empty
  bucket, with the entry's payload owned by the map afterwards (deep free closes
  the heap).\<close>

definition test_entry_free :: \<open>64 word \<times> 64 word os_list \<Rightarrow> unit llM\<close> where
  \<open>test_entry_free \<equiv> \<lambda>(_, vs). os_delete vs\<close>

lemma test_entry_free_rule: \<open>MK_FREE test_entry_assn test_entry_free\<close>
  supply [vcg_rules] = MK_FREED[OF raw_os_assn_free]
  apply (rule MK_FREEI)
  unfolding test_entry_free_def
  subgoal for a c
    apply (cases a; cases c; simp)
    by vcg
  done

text \<open>The bucket member rule at the test instantiation (pinned, like all
  compositions against the eeq assumption).\<close>

lemmas test_bucket_member_rule = phm_bucket_member_impl_rule[where A = test_entry_assn
  and B = test_probe_assn and eabs = \<open>\<lambda>x e. fst e = x\<close>, OF test_eeq_rule]

text \<open>The ins rule with the entry pre-instantiated to a pair: the generic rule's
  precondition atom \<open>test_entry_assn ?x (ki, vsi)\<close> has a schematic abstract side,
  so the applied-form simp cannot atomize it and fri would have to match the
  folded constant against the atomized state \<comment> \<open>impossible. In pair form the
  precondition is already atoms.\<close>\<close>

lemma test_bucket_ins_rule:
  \<open>llvm_htriple
    (\<upharpoonleft>(phm_bucket_assn test_entry_assn) es p ** \<upharpoonleft>unat.assn k ki
       ** \<upharpoonleft>unat.assn k' ki' ** \<upharpoonleft>os_list_assn vs vsi)
    (phm_bucket_ins_impl ki (ki', vsi) p)
    (\<lambda>r. \<upharpoonleft>(phm_bucket_assn test_entry_assn) (phm_alist_ins k (k', vs) es) r
       ** \<upharpoonleft>unat.assn k ki)\<close>
  using phm_bucket_ins_impl_rule[where A = test_entry_assn
    and x = \<open>(k', vs)\<close> and xi = \<open>(ki', vsi)\<close>]
  by simp

lemma test_bucket_roundtrip:
  \<open>llvm_htriple
    (\<upharpoonleft>(phm_bucket_assn test_entry_assn) [] b ** \<upharpoonleft>unat.assn k ki
       ** \<upharpoonleft>os_list_assn vs vsi)
    (doM {
      b \<leftarrow> phm_bucket_ins_impl ki (ki, vsi) b;
      r \<leftarrow> phm_bucket_member_impl test_eeq ki ki b;
      pam_bucket_free_impl (phm_chain_free_impl test_entry_free) b;
      Mreturn r })
    (\<lambda>r. \<upharpoonleft>bool.assn True r ** \<upharpoonleft>unat.assn k ki)\<close>
  supply [vcg_rules] = test_bucket_ins_rule test_bucket_member_rule
    MK_FREED[OF pam_bucket_assn_free[OF phm_chain_assn_free[OF test_entry_free_rule]]]
  by vcg

end

end
