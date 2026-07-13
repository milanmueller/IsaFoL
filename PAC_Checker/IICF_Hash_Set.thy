(*
  Note that large portions of this file were generated using the
  "Fable 5" language model by Anthropic. An in-depth human
  review has not been carried out yet.

  Responsible: Milan Mueller, ALU Freiburg (student)
*)

theory IICF_Hash_Set
  imports
    Isabelle_LLVM.IICF
    Isabelle_LLVM.Array_of_Array_List
    IICF_Owning_List
begin

section \<open>A hash set of heap-owning elements\<close>

text \<open>
  This is the replacement for the placeholder \<open>hs_assn string_assn\<close> (used as \<open>vars_assn\<close>
  in \<^file>\<open>PAC_Checker_Synthesis.thy\<close>), built as the set sibling of the association map
  in \<^file>\<open>IICF_Assoc_Map.thy\<close> and superseding the array-list based prototype in
  \<^file>\<open>String_Hash_Map.thy\<close>.

  Design (mirroring \<open>IICF_Assoc_Map\<close>):

  \<^item> Elements are \<^emph>\<open>heap-owning\<close> (for the checker: strings as open lists of chars,
    \<open>strl_assn\<close> from \<^file>\<open>String_Assn.thy\<close>), so the IICF containers are unusable. A bucket
    is an \<^emph>\<open>owning open list\<close> (\<^const>\<open>ol_assn\<close>, \<^file>\<open>IICF_Owning_List.thy\<close>) of elements;
    the outer bucket array owns its buckets via \<open>Array_of_Array_List.nao_assn\<close>.
    Open-list buckets buy O(1) insert (prepend) without any capacity/\<open>max_snat\<close> side
    conditions \<comment> \<open>the prototype's \<open>bucket_len_bound\<close> gymnastics disappear.\<close>
  \<^item> The theory is layered as:
    \<^enum> bucket operations, generic in the element assertion \<open>A\<close> and an element-equality
      implementation \<open>eeq\<close> (a Hoare-triple parameter, like \<open>vfree\<close>/\<open>vcopy\<close> in the map);
    \<^enum> set operations taking the \<^emph>\<open>hash value\<close> as an explicit argument
      (\<open>hs_member_hashed_impl\<close>, \<open>hs_insert_hashed_impl\<close>) - \<open>independent of any hash
      function; the bucket index is \<open>unat h mod nbins\<close>, a single \<open>ll_urem\<close>;\<close>
    \<^enum> wrappers taking a \<^emph>\<open>hash function\<close> \<open>hash\<close> as a parameter, tied to an abstract
      hash \<open>habs :: 'e \<Rightarrow> 64 word\<close> by a Hoare-triple assumption;
    \<^enum> the bucket invariant \<open>hs_invar habs\<close> and one \<open>hr_comp\<close> step to @{typ \<open>'e set\<close>},
      with \<open>hfref\<close> rules for the IICF set interface (\<open>op_set_empty\<close>, \<open>op_set_member\<close>,
      \<open>op_set_insert\<close>) and a \<open>MK_FREE\<close> rule.
  \<^item> Insertion \<^emph>\<open>keeps\<close> the element (in the checker the strings come from a monomial that
    is only borrowed) and stores a fresh copy, obtained from an element-copy parameter
    \<open>ecopy\<close>; there is no sharing in this separation logic.

  Refinement chain:
    \<open>'e set\<close>  \<longleftarrow>[\<open>hs_rel habs\<close>: bucket invariant]\<longleftarrow>  \<open>'e list list\<close>
    \<longleftarrow>[\<open>hs_assn A\<close>: separation logic]\<longleftarrow>  \<open>64 word \<times> bucket ptr\<close>

  The heap-level rules are stated purely against the bucket decomposition
  (\<open>bss ! hs_bucket_of (length bss) h\<close>); the invariant only enters in the subsequent
  \<open>hr_comp\<close> step, keeping the Hoare-triple proofs invariant-free.
\<close>

subsection \<open>Concrete representation\<close>

type_synonym 'ei hs_bucket_impl = \<open>'ei os_list\<close>
type_synonym 'ei hs_impl = \<open>64 word \<times> 'ei hs_bucket_impl ptr\<close>

text \<open>A bucket: an owning open list of elements. Must be a \<^emph>\<open>named\<close> dr_assn so it can
  serve as the (folded) parameter of \<^const>\<open>Array_of_Array_List.nao_assn\<close>; the applied
  form is exposed only through the bucket-level rules below, never by unfolding
  (cf.\ the composite-parameter notes in \<open>CLAUDE.md\<close>).\<close>

definition hs_bucket_assn ::
  \<open>('e \<Rightarrow> 'ei::llvm_rep \<Rightarrow> assn) \<Rightarrow> ('e list, 'ei hs_bucket_impl) dr_assn\<close> where
  \<open>hs_bucket_assn A \<equiv> mk_assn (ol_assn A)\<close>

lemma hs_bucket_assn_conv:
  \<open>\<upharpoonleft>(hs_bucket_assn A) = ol_assn A\<close>
  unfolding hs_bucket_assn_def by (intro ext) simp

text \<open>The empty bucket is the null pointer, i.e. \<^const>\<open>init\<close> \<comment> \<open>this is what makes
  @{thm nao_new_init_rl} applicable, so \<open>calloc\<close>-style array initialization suffices.\<close>\<close>

lemma hs_bucket_assn_init: \<open>\<box> \<turnstile> \<upharpoonleft>(hs_bucket_assn A) [] init\<close>
  by (simp add: hs_bucket_assn_conv ol_assn_conv sep_algebra_simps)

text \<open>The set over bucket lists; a length-tagged @{const nao_assn} array of buckets.\<close>

definition hs_assn ::
  \<open>('e \<Rightarrow> 'ei::llvm_rep \<Rightarrow> assn) \<Rightarrow> ('e list list, 'ei hs_impl) dr_assn\<close> where
  \<open>hs_assn A \<equiv> mk_assn (\<lambda>bss (ni, a).
       \<upharpoonleft>snat.assn (length bss) ni
    ** \<upharpoonleft>(Array_of_Array_List.nao_assn (hs_bucket_assn A) Map.empty) bss a)\<close>


subsection \<open>Bucket index\<close>

definition hs_bucket_of :: \<open>nat \<Rightarrow> 64 word \<Rightarrow> nat\<close> where
  \<open>hs_bucket_of n h \<equiv> unat h mod n\<close>

lemma hs_bucket_of_lt[simp]: \<open>0 < n \<Longrightarrow> hs_bucket_of n h < n\<close>
  by (simp add: hs_bucket_of_def)

text \<open>\<open>ll_urem\<close> of an arbitrary word (the hash, possibly MSB-set, so \<^emph>\<open>not\<close> snat) by an
  snat divisor (the bin count, as required by @{const nao_nth}). The library's snat rule
  requires both operands to be snat, hence this mixed variant (taken from the
  \<open>String_Hash_Map\<close> prototype). Raw \<open>ll_urem\<close> support lives behind
  \<open>llvm_prim_arith_setup\<close>, hence the throwaway interpretation context.\<close>

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

text \<open>Extraction form of \<open>bool.assn\<close> facts on \<^emph>\<open>literal\<close> 1-words (the member flag
  consumed by \<open>llc_if\<close>), cf.\ the \<open>String_Hash_Map\<close> prototype.\<close>

lemma pure_bool_assn_iff: \<open>\<flat>\<^sub>pbool.assn b w \<longleftrightarrow> b = to_bool w\<close>
  unfolding bool.assn_def by simp


subsection \<open>Bucket operations\<close>

text \<open>The bucket walk is a recursive \<open>partial_function\<close> following the
  \<^const>\<open>os_eq\<close>/\<open>pam_bucket_contains_impl\<close> template; the proof is an induction with one
  \<open>subst \<dots>.simps\<close> per case (never \<open>unfolding\<close>, which loops), the IH and the
  element-equality parameter rule as \<open>vcg_rules\<close>, and the null-pointer case split off
  before \<open>vcg\<close>.

  NOTE (code generation): higher-order in \<open>eeq\<close>; each concrete instantiation must be
  specialized into its own first-order \<open>[llvm_code]\<close> definition before export
  (cf.\ \<open>ol_delete\<close> in \<^file>\<open>IICF_Owning_List.thy\<close>).\<close>

partial_function (M) hs_bucket_member_impl ::
  \<open>('ei \<Rightarrow> 'ei \<Rightarrow> 1 word llM) \<Rightarrow> 'ei \<Rightarrow> 'ei::llvm_rep hs_bucket_impl \<Rightarrow> 1 word llM\<close> where
  \<open>hs_bucket_member_impl eeq x p = (if p = null then Mreturn 0
    else doM {
      n \<leftarrow> ll_load p;
      eq \<leftarrow> eeq (node.val n) x;
      if to_bool eq then Mreturn 1
      else hs_bucket_member_impl eeq x (node.next n)
    })\<close>

lemma hs_bucket_member_impl_rule:
  assumes EEQ: \<open>\<And>a c a' c'. llvm_htriple (A a c ** A a' c') (eeq c c')
    (\<lambda>r. A a c ** A a' c' ** \<upharpoonleft>bool.assn (a = a') r)\<close>
  shows \<open>llvm_htriple
    (\<upharpoonleft>(hs_bucket_assn A) es p ** A x xi)
    (hs_bucket_member_impl eeq xi p)
    (\<lambda>r. \<upharpoonleft>(hs_bucket_assn A) es p ** A x xi ** \<upharpoonleft>bool.assn (x \<in> set es) r)\<close>
  unfolding hs_bucket_assn_conv ol_assn_conv
proof (induction es arbitrary: p)
  case Nil
  show ?case
    supply [simp] = bool.assn_def
    apply (subst hs_bucket_member_impl.simps)
    by vcg
next
  case (Cons e es)
  interpret llvm_prim_ctrl_setup .
  note [vcg_rules] = Cons.IH EEQ
  show ?case
    supply [simp, named_ss fri_prepare_simps] = ol_seg_cons
    supply [simp] = bool.assn_def sep_conj_exists
    apply (subst hs_bucket_member_impl.simps)
    apply (cases \<open>p = null\<close>; simp)
    by vcg
qed

text \<open>Prepend is O(1) at the bucket head; the raw op and its proof come for free from
  \<^file>\<open>IICF_Owning_List.thy\<close>, restated at the (folded) bucket assertion.\<close>

lemma hs_bucket_prepend_rule:
  \<open>llvm_htriple
    (A x xi ** \<upharpoonleft>(hs_bucket_assn A) es p)
    (os_prepend xi p)
    (\<lambda>r. \<upharpoonleft>(hs_bucket_assn A) (x # es) r)\<close>
  unfolding hs_bucket_assn_conv
  by (rule ol_prepend_rule)

text \<open>Deep free is \<^const>\<open>ol_delete\<close> with the element free function.\<close>

definition hs_bucket_free_impl ::
  \<open>('ei \<Rightarrow> unit llM) \<Rightarrow> 'ei::llvm_rep hs_bucket_impl \<Rightarrow> unit llM\<close> where
  \<open>hs_bucket_free_impl efree \<equiv> ol_delete efree\<close>

lemma hs_bucket_assn_free:
  assumes \<open>MK_FREE A efree\<close>
  shows \<open>MK_FREE (\<upharpoonleft>(hs_bucket_assn A)) (hs_bucket_free_impl efree)\<close>
  unfolding hs_bucket_free_impl_def hs_bucket_assn_conv
  by (rule ol_assn_free[OF assms])


subsection \<open>Set operations, hash value given\<close>

text \<open>Creation.\<close>

definition hs_new_impl :: \<open>64 word \<Rightarrow> 'ei::llvm_rep hs_impl llM\<close> where [llvm_code]:
  \<open>hs_new_impl n \<equiv> doM {
    a \<leftarrow> nao_new TYPE('ei hs_bucket_impl) n;
    Mreturn (n, a)
  }\<close>

lemma hs_new_impl_rule[vcg_rules]:
  \<open>llvm_htriple
    (\<upharpoonleft>snat.assn n ni)
    (hs_new_impl ni)
    (\<lambda>r. \<upharpoonleft>(hs_assn A) (replicate n []) r)\<close>
  unfolding hs_new_impl_def hs_assn_def
  supply [vcg_rules] = nao_new_init_rl[OF hs_bucket_assn_init]
  by vcg

text \<open>Membership. The bucket is borrowed from the outer array (hole map), scanned
  read-only, and rejoined unchanged.\<close>

definition hs_member_hashed_impl ::
  \<open>('ei \<Rightarrow> 'ei \<Rightarrow> 1 word llM) \<Rightarrow> 64 word \<Rightarrow> 'ei \<Rightarrow> 'ei::llvm_rep hs_impl \<Rightarrow> 1 word llM\<close>
  where
  \<open>hs_member_hashed_impl eeq h x \<equiv> \<lambda>(n, a). doM {
    i \<leftarrow> ll_urem h n;
    bin \<leftarrow> nao_nth a i;
    found \<leftarrow> hs_bucket_member_impl eeq x bin;
    nao_rejoin a i;
    Mreturn found
  }\<close>

lemma hs_member_hashed_impl_rule:
  assumes EEQ: \<open>\<And>a c a' c'. llvm_htriple (A a c ** A a' c') (eeq c c')
    (\<lambda>r. A a c ** A a' c' ** \<upharpoonleft>bool.assn (a = a') r)\<close>
  shows \<open>llvm_htriple
    (\<upharpoonleft>(hs_assn A) bss p ** A x xi ** \<up>(bss \<noteq> []))
    (hs_member_hashed_impl eeq h xi p)
    (\<lambda>r. \<upharpoonleft>(hs_assn A) bss p ** A x xi
       ** \<upharpoonleft>bool.assn (x \<in> set (bss ! hs_bucket_of (length bss) h)) r)\<close>
  unfolding hs_member_hashed_impl_def hs_assn_def hs_bucket_of_def
  supply [vcg_rules] = ll_urem_hash_snat_rule hs_bucket_member_impl_rule[OF EEQ]
  apply (cases p; simp)
  by vcg

text \<open>Insertion. The bucket is taken out of the array once; on a hit it is rejoined
  unchanged, on a miss a fresh copy of the element is prepended and the (new) bucket
  head is stored into the hole. No capacity precondition: linked nodes never overflow
  an index type.\<close>

definition hs_ins :: \<open>64 word \<Rightarrow> 'e \<Rightarrow> 'e list list \<Rightarrow> 'e list list\<close> where
  \<open>hs_ins h x bss = (let i = hs_bucket_of (length bss) h in
     if x \<in> set (bss ! i) then bss else bss[i := x # bss ! i])\<close>

definition hs_insert_hashed_impl ::
  \<open>('ei \<Rightarrow> 'ei \<Rightarrow> 1 word llM) \<Rightarrow> ('ei \<Rightarrow> 'ei llM) \<Rightarrow> 64 word \<Rightarrow> 'ei
    \<Rightarrow> 'ei::llvm_rep hs_impl \<Rightarrow> 'ei hs_impl llM\<close>
  where
  \<open>hs_insert_hashed_impl eeq ecopy h x \<equiv> \<lambda>(n, a). doM {
    i \<leftarrow> ll_urem h n;
    bin \<leftarrow> nao_nth a i;
    found \<leftarrow> hs_bucket_member_impl eeq x bin;
    llc_if found
      (doM { nao_rejoin a i; Mreturn (n, a) })
      (doM {
        x' \<leftarrow> ecopy x;
        bin \<leftarrow> os_prepend x' bin;
        a \<leftarrow> nao_upd a i bin;
        Mreturn (n, a)
      })
  }\<close>

lemma hs_insert_hashed_impl_rule:
  assumes EEQ: \<open>\<And>a c a' c'. llvm_htriple (A a c ** A a' c') (eeq c c')
    (\<lambda>r. A a c ** A a' c' ** \<upharpoonleft>bool.assn (a = a') r)\<close>
    and ECOPY: \<open>\<And>e c. llvm_htriple (A e c) (ecopy c) (\<lambda>r. A e c ** A e r)\<close>
  shows \<open>llvm_htriple
    (\<upharpoonleft>(hs_assn A) bss p ** A x xi ** \<up>(bss \<noteq> []))
    (hs_insert_hashed_impl eeq ecopy h xi p)
    (\<lambda>r. \<upharpoonleft>(hs_assn A) (hs_ins h x bss) r ** A x xi)\<close>
  unfolding hs_insert_hashed_impl_def hs_assn_def hs_ins_def Let_def hs_bucket_of_def
  supply [vcg_rules] = ll_urem_hash_snat_rule hs_bucket_member_impl_rule[OF EEQ]
    ECOPY hs_bucket_prepend_rule
  supply [simp] = pure_bool_assn_iff
  apply (cases p; simp)
  by vcg

text \<open>Deallocation.\<close>

definition hs_free_impl ::
  \<open>('ei \<Rightarrow> unit llM) \<Rightarrow> 'ei::llvm_rep hs_impl \<Rightarrow> unit llM\<close> where
  \<open>hs_free_impl efree \<equiv> \<lambda>(n, a). nao_free (hs_bucket_free_impl efree) a n\<close>

lemma hs_free_impl_rule:
  assumes EFREE: \<open>MK_FREE A efree\<close>
  shows \<open>llvm_htriple (\<upharpoonleft>(hs_assn A) bss p) (hs_free_impl efree p) (\<lambda>_. \<box>)\<close>
  supply [vcg_rules] = nao_free_rl[OF MK_FREED[OF hs_bucket_assn_free[OF EFREE]]]
  unfolding hs_free_impl_def hs_assn_def
  apply (cases p; simp)
  by vcg


subsection \<open>Wrappers over a hash function\<close>

text \<open>The hash function enters as a parameter \<open>hash\<close>, tied to an abstract hash
  \<open>habs :: 'e \<Rightarrow> 64 word\<close> by the assumption \<open>HASH\<close> below (a plain Hoare triple, so any
  side-effect-free implementation qualifies).\<close>

definition hs_member_impl ::
  \<open>('ei \<Rightarrow> 64 word llM) \<Rightarrow> ('ei \<Rightarrow> 'ei \<Rightarrow> 1 word llM) \<Rightarrow> 'ei
    \<Rightarrow> 'ei::llvm_rep hs_impl \<Rightarrow> 1 word llM\<close>
  where
  \<open>hs_member_impl hash eeq x p \<equiv> doM { h \<leftarrow> hash x; hs_member_hashed_impl eeq h x p }\<close>

lemma hs_member_impl_rule:
  assumes HASH: \<open>\<And>e c. llvm_htriple (A e c) (hash c) (\<lambda>r. A e c ** \<up>(r = habs e))\<close>
    and EEQ: \<open>\<And>a c a' c'. llvm_htriple (A a c ** A a' c') (eeq c c')
      (\<lambda>r. A a c ** A a' c' ** \<upharpoonleft>bool.assn (a = a') r)\<close>
  shows \<open>llvm_htriple
    (\<upharpoonleft>(hs_assn A) bss p ** A x xi ** \<up>(bss \<noteq> []))
    (hs_member_impl hash eeq xi p)
    (\<lambda>r. \<upharpoonleft>(hs_assn A) bss p ** A x xi
       ** \<upharpoonleft>bool.assn (x \<in> set (bss ! hs_bucket_of (length bss) (habs x))) r)\<close>
  unfolding hs_member_impl_def
  supply [vcg_rules] = HASH hs_member_hashed_impl_rule[OF EEQ]
  by vcg

definition hs_insert_impl ::
  \<open>('ei \<Rightarrow> 64 word llM) \<Rightarrow> ('ei \<Rightarrow> 'ei \<Rightarrow> 1 word llM) \<Rightarrow> ('ei \<Rightarrow> 'ei llM) \<Rightarrow> 'ei
    \<Rightarrow> 'ei::llvm_rep hs_impl \<Rightarrow> 'ei hs_impl llM\<close>
  where
  \<open>hs_insert_impl hash eeq ecopy x p \<equiv>
     doM { h \<leftarrow> hash x; hs_insert_hashed_impl eeq ecopy h x p }\<close>

lemma hs_insert_impl_rule:
  assumes HASH: \<open>\<And>e c. llvm_htriple (A e c) (hash c) (\<lambda>r. A e c ** \<up>(r = habs e))\<close>
    and EEQ: \<open>\<And>a c a' c'. llvm_htriple (A a c ** A a' c') (eeq c c')
      (\<lambda>r. A a c ** A a' c' ** \<upharpoonleft>bool.assn (a = a') r)\<close>
    and ECOPY: \<open>\<And>e c. llvm_htriple (A e c) (ecopy c) (\<lambda>r. A e c ** A e r)\<close>
  shows \<open>llvm_htriple
    (\<upharpoonleft>(hs_assn A) bss p ** A x xi ** \<up>(bss \<noteq> []))
    (hs_insert_impl hash eeq ecopy xi p)
    (\<lambda>r. \<upharpoonleft>(hs_assn A) (hs_ins (habs x) x bss) r ** A x xi)\<close>
  unfolding hs_insert_impl_def
  supply [vcg_rules] = HASH hs_insert_hashed_impl_rule[OF EEQ ECOPY]
  by vcg


subsection \<open>Bucket-level abstraction\<close>

text \<open>Relating bucket lists to sets. Distinctness of the concatenation is not needed for
  correctness of member/insert, but keeps the buckets duplicate-free (insert checks
  membership first) and would be needed for a size operation.\<close>

definition hs_invar :: \<open>('e \<Rightarrow> 64 word) \<Rightarrow> 'e list list \<Rightarrow> bool\<close> where
  \<open>hs_invar habs bss \<longleftrightarrow> bss \<noteq> [] \<and> distinct (concat bss) \<and>
     (\<forall>i < length bss. \<forall>x \<in> set (bss ! i). hs_bucket_of (length bss) (habs x) = i)\<close>

definition hs_rel :: \<open>('e \<Rightarrow> 64 word) \<Rightarrow> ('e list list \<times> 'e set) set\<close> where
  \<open>hs_rel habs \<equiv> br (\<lambda>bss. set (concat bss)) (hs_invar habs)\<close>

text \<open>Under the invariant, the element lives in its hash bucket (if anywhere); this is
  the abstract-side justification for all the heap rules above, which only speak about
  \<open>bss ! hs_bucket_of (length bss) (habs x)\<close>. The shared skeleton (from
  \<open>IICF_Assoc_Map\<close>): split \<open>concat bss\<close> around the hash bucket
  (@{thm id_take_nth_drop} / @{thm upd_conv_take_nth_drop}); the bucket-of condition
  makes \<open>x\<close> absent from the two outer parts.\<close>

context
  fixes habs :: \<open>'e \<Rightarrow> 64 word\<close> and bss :: \<open>'e list list\<close> and x :: 'e
  assumes I: \<open>hs_invar habs bss\<close>
begin

private lemma NE: \<open>bss \<noteq> []\<close>
  and D: \<open>distinct (concat bss)\<close>
  using I by (auto simp: hs_invar_def)

private lemma B: \<open>j < length bss \<Longrightarrow> x' \<in> set (bss ! j)
  \<Longrightarrow> hs_bucket_of (length bss) (habs x') = j\<close> for j x'
  using I by (auto simp: hs_invar_def)

private lemma IB: \<open>hs_bucket_of (length bss) (habs x) < length bss\<close>
  using NE by simp

private lemma concat_orig:
  \<open>concat bss = concat (take (hs_bucket_of (length bss) (habs x)) bss)
     @ bss ! hs_bucket_of (length bss) (habs x)
     @ concat (drop (Suc (hs_bucket_of (length bss) (habs x))) bss)\<close>
proof -
  have \<open>bss = take (hs_bucket_of (length bss) (habs x)) bss
     @ bss ! hs_bucket_of (length bss) (habs x)
     # drop (Suc (hs_bucket_of (length bss) (habs x))) bss\<close>
    by (rule id_take_nth_drop[OF IB])
  then show ?thesis
    by (metis concat.simps(2) concat_append)
qed

private lemma concat_upd:
  \<open>concat (bss[hs_bucket_of (length bss) (habs x) := b])
   = concat (take (hs_bucket_of (length bss) (habs x)) bss)
     @ b @ concat (drop (Suc (hs_bucket_of (length bss) (habs x))) bss)\<close> for b
proof -
  have \<open>bss[hs_bucket_of (length bss) (habs x) := b]
     = take (hs_bucket_of (length bss) (habs x)) bss
       @ b # drop (Suc (hs_bucket_of (length bss) (habs x))) bss\<close>
    by (rule upd_conv_take_nth_drop[OF IB])
  then show ?thesis
    by (metis concat.simps(2) concat_append)
qed

private lemma take_nomem:
  \<open>x \<notin> set (concat (take (hs_bucket_of (length bss) (habs x)) bss))\<close>
proof
  assume \<open>x \<in> set (concat (take (hs_bucket_of (length bss) (habs x)) bss))\<close>
  then obtain ys where Y: \<open>ys \<in> set (take (hs_bucket_of (length bss) (habs x)) bss)\<close>
    \<open>x \<in> set ys\<close> by auto
  from Y(1) obtain j where J: \<open>j < hs_bucket_of (length bss) (habs x)\<close> \<open>ys = bss ! j\<close>
    using IB by (auto simp: in_set_conv_nth)
  from Y(2) J B[of j x] IB show False by auto
qed

private lemma drop_nomem:
  \<open>x \<notin> set (concat (drop (Suc (hs_bucket_of (length bss) (habs x))) bss))\<close>
proof
  assume \<open>x \<in> set (concat (drop (Suc (hs_bucket_of (length bss) (habs x))) bss))\<close>
  then obtain ys where Y: \<open>ys \<in> set (drop (Suc (hs_bucket_of (length bss) (habs x))) bss)\<close>
    \<open>x \<in> set ys\<close> by auto
  from Y(1) obtain j where J:
    \<open>Suc (hs_bucket_of (length bss) (habs x)) + j < length bss\<close>
    \<open>ys = bss ! (Suc (hs_bucket_of (length bss) (habs x)) + j)\<close>
    by (metis in_set_drop_conv_nth le_Suc_ex)
  from Y(2) J B[of \<open>Suc (hs_bucket_of (length bss) (habs x)) + j\<close> x] show False
    by (metis lessI not_add_less1)
qed

lemma hs_member_correct:
  \<open>x \<in> set (bss ! hs_bucket_of (length bss) (habs x)) \<longleftrightarrow> x \<in> set (concat bss)\<close>
proof
  assume \<open>x \<in> set (bss ! hs_bucket_of (length bss) (habs x))\<close>
  with IB show \<open>x \<in> set (concat bss)\<close> by auto
next
  assume \<open>x \<in> set (concat bss)\<close>
  then obtain ys where ys: \<open>ys \<in> set bss\<close> \<open>x \<in> set ys\<close> by auto
  then obtain i where i: \<open>i < length bss\<close> \<open>bss ! i = ys\<close>
    by (auto simp: in_set_conv_nth)
  with B ys have \<open>hs_bucket_of (length bss) (habs x) = i\<close> by auto
  with ys i show \<open>x \<in> set (bss ! hs_bucket_of (length bss) (habs x))\<close> by simp
qed

lemma hs_ins_invar: \<open>hs_invar habs (hs_ins (habs x) x bss)\<close>
proof (cases \<open>x \<in> set (bss ! hs_bucket_of (length bss) (habs x))\<close>)
  case True
  then show ?thesis
    using I by (simp add: hs_ins_def Let_def)
next
  case False
  let ?i = \<open>hs_bucket_of (length bss) (habs x)\<close>
  let ?b' = \<open>x # bss ! ?i\<close>
  have EQ: \<open>hs_ins (habs x) x bss = bss[?i := ?b']\<close>
    using False by (simp add: hs_ins_def Let_def)
  have X: \<open>x \<notin> set (concat bss)\<close>
    using False hs_member_correct by blast
  have X': \<open>x \<notin> set (concat (take ?i bss))\<close> \<open>x \<notin> set (bss ! ?i)\<close>
    \<open>x \<notin> set (concat (drop (Suc ?i) bss))\<close>
    using take_nomem False drop_nomem by auto
  have D3: \<open>distinct (concat (take ?i bss) @ bss ! ?i @ concat (drop (Suc ?i) bss))\<close>
    using D concat_orig by metis
  have DIST: \<open>distinct (concat (bss[?i := ?b']))\<close>
    unfolding concat_upd
    using D3 X' by auto
  have BUCK: \<open>hs_bucket_of (length bss) (habs x') = j\<close>
    if J: \<open>j < length bss\<close> and E: \<open>x' \<in> set (bss[?i := ?b'] ! j)\<close> for j x'
  proof (cases \<open>j = ?i\<close>)
    case False
    with E J have \<open>x' \<in> set (bss ! j)\<close> by simp
    with B J show ?thesis by simp
  next
    case True
    with E J IB have \<open>x' \<in> set ?b'\<close> by simp
    then have \<open>x' = x \<or> x' \<in> set (bss ! ?i)\<close> by auto
    with B[of ?i x'] IB True show ?thesis by auto
  qed
  have NE': \<open>bss[?i := ?b'] \<noteq> []\<close>
    by (metis NE length_0_conv length_list_update)
  show ?thesis
    unfolding EQ hs_invar_def
    using NE' DIST BUCK
    by (metis length_list_update)
qed

lemma hs_ins_abs: \<open>set (concat (hs_ins (habs x) x bss)) = insert x (set (concat bss))\<close>
proof (cases \<open>x \<in> set (bss ! hs_bucket_of (length bss) (habs x))\<close>)
  case True
  then have \<open>x \<in> set (concat bss)\<close>
    using hs_member_correct by blast
  with True show ?thesis
    by (simp add: hs_ins_def Let_def insert_absorb)
next
  case False
  let ?i = \<open>hs_bucket_of (length bss) (habs x)\<close>
  have EQ: \<open>hs_ins (habs x) x bss = bss[?i := x # bss ! ?i]\<close>
    using False by (simp add: hs_ins_def Let_def)
  show ?thesis
    unfolding EQ
    apply (subst concat_upd)
    apply (subst concat_orig)
    by auto
qed

end

lemma concat_replicate_Nil[simp]: \<open>concat (replicate n []) = []\<close>
  by (induction n) auto

lemma hs_invar_replicate: \<open>0 < n \<Longrightarrow> hs_invar habs (replicate n [])\<close>
  by (auto simp: hs_invar_def)

lemma hs_invar_nonempty[simp]: \<open>hs_invar habs bss \<Longrightarrow> bss \<noteq> []\<close>
  by (simp add: hs_invar_def)


subsection \<open>The set interface\<close>

text \<open>One \<open>hr_comp\<close> step to @{typ \<open>'e set\<close>}.\<close>

definition hs_set_assn ::
  \<open>('e \<Rightarrow> 64 word) \<Rightarrow> ('e \<Rightarrow> 'ei::llvm_rep \<Rightarrow> assn) \<Rightarrow> 'e set \<Rightarrow> 'ei hs_impl \<Rightarrow> assn\<close>
  where \<open>hs_set_assn habs A \<equiv> hr_comp (\<upharpoonleft>(hs_assn A)) (hs_rel habs)\<close>

text \<open>No \<open>intf_of_assn\<close> rule is needed here: unlike maps (\<open>i_map\<close>/\<open>f_map\<close>,
  cf.\ the note in \<open>Polys_Assn.thy\<close>), the Isabelle-LLVM \<open>IICF_Set\<close> declares no
  separate interface type \<comment> \<open>its operations are registered at the plain \<open>'e set\<close>
  type, which is exactly what \<open>intf_of_assn_fallback\<close> assigns to arguments.\<close>\<close>

text \<open>Bin count as an \<^emph>\<open>opaque\<close> definition; never unfold it to the numeral in proofs
  (see the \<open>pam_nbins\<close> notes in \<^file>\<open>IICF_Assoc_Map.thy\<close> \<comment> \<open>\<open>replicate_numeral\<close> would
  expand \<open>replicate hs_nbins []\<close> into a 16384-element cons chain\<close>).\<close>

definition hs_nbins :: nat where \<open>hs_nbins = 16384\<close>

lemma hs_nbins_pos: \<open>0 < hs_nbins\<close>
  by (simp add: hs_nbins_def)

definition hs_empty_impl :: \<open>unit \<Rightarrow> 'ei::llvm_rep hs_impl llM\<close> where [llvm_inline]:
  \<open>hs_empty_impl \<equiv> \<lambda>_. hs_new_impl (signed_nat 16384)\<close>
  \<comment> \<open>\<open>[llvm_inline]\<close>, NOT \<open>[llvm_code]\<close>: the \<open>unit\<close> argument becomes a literal \<open>()\<close> on
  the code equation's LHS, which \<open>llc_parse_eqn\<close> rejects. Inlining dissolves the
  wrapper at all call sites.\<close>

lemma snat_assn_hs_nbins:
  \<open>\<box> \<turnstile> \<upharpoonleft>snat.assn hs_nbins (signed_nat (16384::64 word))\<close>
proof -
  have \<open>hs_nbins < max_snat LENGTH(64)\<close>
    by (simp add: hs_nbins_def max_snat_def)
  then have \<open>snat_invar (signed_nat (16384::64 word))
      \<and> hs_nbins = snat (signed_nat (16384::64 word))\<close>
    by (simp add: signed_nat_def snat_invar_numeral hs_nbins_def max_snat_def)
  then show ?thesis
    by (simp add: snat.assn_def entails_def sep_algebra_simps)
qed

lemma hs_empty_impl_aux_rule:
  \<open>llvm_htriple \<box> (hs_empty_impl u) (\<lambda>r. \<upharpoonleft>(hs_assn A) (replicate hs_nbins []) r)\<close>
  unfolding hs_empty_impl_def
  by (rule htriple_ent_pre[OF snat_assn_hs_nbins
        hs_new_impl_rule[where n = hs_nbins and ni = \<open>signed_nat 16384\<close>]])

lemma hs_empty_impl_hfref:
  \<open>(uncurry0 (hs_empty_impl ()), uncurry0 (RETURN (replicate hs_nbins [])))
     \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a \<upharpoonleft>(hs_assn A)\<close>
  apply sepref_to_hoare
  supply [vcg_rules] = hs_empty_impl_aux_rule
  by vcg

lemma hs_empty_rel:
  \<open>(uncurry0 (RETURN (replicate hs_nbins [])), uncurry0 (RETURN op_set_empty))
     \<in> unit_rel \<rightarrow>\<^sub>f \<langle>hs_rel habs\<rangle>nres_rel\<close>
  apply (rule fref_param0I)
  by (auto simp: hs_rel_def in_br_conv hs_invar_replicate hs_nbins_pos intro!: nres_relI)

text \<open>NOT declared \<open>[sepref_fr_rules]\<close> here: \<open>op_set_empty\<close> is a producer op, so a
  generic rule would commit every \<open>{}\<close> in every synthesis to this implementation
  (the \<open>list_custom_empty\<close> lesson from \<^file>\<open>IICF_Owning_List.thy\<close>). Concrete
  instantiations register it against a per-implementation custom-empty op via the
  \<open>set_custom_empty\<close> locale of \<open>IICF_Set\<close>.\<close>

lemmas hs_empty_hnr =
  hs_empty_impl_hfref[FCOMP hs_empty_rel, folded hs_set_assn_def]

text \<open>Member and insert are proved directly via \<open>sepref_to_hoare\<close>; @{thm hr_comp_def}
  is already in \<open>EXS\<close> form, so unfolding it works on both sides (extraction of the
  bucket list from the precondition, fri instantiation in the postcondition). The
  boolean result goes through @{thm bool.assn_is_rel} (folded with
  @{thm bool1_rel_def}) \<^emph>\<open>before\<close> \<open>sepref_to_hoare\<close>, cf.\ \<open>ol_less_hnr\<close>.\<close>

lemma hs_member_hnr:
  assumes HASH: \<open>\<And>e c. llvm_htriple (A e c) (hash c) (\<lambda>r. A e c ** \<up>(r = habs e))\<close>
    and EEQ: \<open>\<And>a c a' c'. llvm_htriple (A a c ** A a' c') (eeq c c')
      (\<lambda>r. A a c ** A a' c' ** \<upharpoonleft>bool.assn (a = a') r)\<close>
  shows \<open>(uncurry (hs_member_impl hash eeq), uncurry (RETURN oo op_set_member))
     \<in> A\<^sup>k *\<^sub>a (hs_set_assn habs A)\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding hs_set_assn_def bool1_rel_def bool.assn_is_rel[symmetric]
  apply sepref_to_hoare
  supply [vcg_rules] = hs_member_impl_rule[OF HASH EEQ]
  supply [simp] = hr_comp_def hs_rel_def in_br_conv hs_member_correct sep_conj_exists
  by vcg

lemma hs_insert_hnr:
  assumes HASH: \<open>\<And>e c. llvm_htriple (A e c) (hash c) (\<lambda>r. A e c ** \<up>(r = habs e))\<close>
    and EEQ: \<open>\<And>a c a' c'. llvm_htriple (A a c ** A a' c') (eeq c c')
      (\<lambda>r. A a c ** A a' c' ** \<upharpoonleft>bool.assn (a = a') r)\<close>
    and ECOPY: \<open>\<And>e c. llvm_htriple (A e c) (ecopy c) (\<lambda>r. A e c ** A e r)\<close>
  shows \<open>(uncurry (hs_insert_impl hash eeq ecopy), uncurry (RETURN oo op_set_insert))
     \<in> A\<^sup>k *\<^sub>a (hs_set_assn habs A)\<^sup>d \<rightarrow>\<^sub>a hs_set_assn habs A\<close>
  unfolding hs_set_assn_def
  apply sepref_to_hoare
  supply [vcg_rules] = hs_insert_impl_rule[OF HASH EEQ ECOPY]
  supply [simp] = hr_comp_def hs_rel_def in_br_conv sep_conj_exists
  apply vcg
  \<comment> \<open>Residual reassembly: fri cannot invent the \<open>EXS\<close> witnesses of the \<open>hr_comp\<close>
    postcondition (the result set and the updated bucket list), and the ambient
    simpset has normalized \<open>set (concat \<dots>)\<close> to \<open>\<Union> (set ` set \<dots>)\<close> \<comment> \<open>hence
    @{thm hs_ins_abs} enters \<open>[unfolded set_concat]\<close>.\<close> Recipe from
    \<open>pam_delete_hnr\<close> in \<^file>\<open>IICF_Assoc_Map.thy\<close>.\<close>
  subgoal for aa ai asf x a b sa
    unfolding vcg_tag_defs ENTAILS_def
    apply (rule entails_exI[where x = \<open>insert aa (\<Union> (set ` set x))\<close>])
    apply (rule entails_exI[where x = \<open>hs_ins (habs aa) aa x\<close>])
    by (simp add: hs_ins_invar hs_ins_abs[unfolded set_concat]
        sep_algebra_simps pred_lift_extract_simps;
        simp add: sep_conj_aci entails_refl)
  done

text \<open>Deallocation.\<close>

lemma hs_assn_free:
  assumes \<open>MK_FREE A efree\<close>
  shows \<open>MK_FREE (\<upharpoonleft>(hs_assn A)) (hs_free_impl efree)\<close>
  by (rule MK_FREEI) (rule hs_free_impl_rule[OF assms])

lemma hs_set_assn_free:
  assumes \<open>MK_FREE A efree\<close>
  shows \<open>MK_FREE (hs_set_assn habs A) (hs_free_impl efree)\<close>
  unfolding hs_set_assn_def
  by (intro MK_FREE_hrcompI hs_assn_free assms)

text \<open>
  Open points:
  \<^item> \<^bold>\<open>Code export\<close>: \<open>hs_bucket_member_impl\<close>, \<open>hs_bucket_free_impl\<close> and the wrappers are
    higher-order in \<open>eeq\<close>/\<open>ecopy\<close>/\<open>efree\<close>/\<open>hash\<close>; each concrete instantiation must be
    specialized into first-order \<open>[llvm_code]\<close> definitions before export (done for
    strings in \<^file>\<open>String_Assn.thy\<close>).
  \<^item> \<^bold>\<open>Size-hinted constructor\<close>: \<open>hs_empty_impl\<close> fixes \<open>hs_nbins\<close> bins; a variant taking
    the (known) number of input variables would fit \<open>remap_polys\<close>.
  \<^item> Further set-interface ops (\<open>op_set_delete\<close>, \<open>op_set_is_empty\<close>, iteration) are not
    needed for \<open>vars_assn\<close> and therefore not implemented.
\<close>

end
