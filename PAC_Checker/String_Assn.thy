theory String_Assn
  imports LLVM_Sort Char_Assn IICF_Hash_Set
begin

text \<open>Implement String by Open List\<close>

type_synonym str = \<open>char list\<close>

text \<open>The list interface implementation of \<open>IICF_Open_List\<close> is specialized to
  strings by instantiating the element assertion with \<open>char_assn\<close>. All interface
  rules require \<open>is_pure char_assn\<close>, discharged by \<open>char_assn_pure\<close>.\<close>

abbreviation strl_assn :: \<open>str \<Rightarrow> 8 word os_list \<Rightarrow> assn\<close> where
  \<open>strl_assn \<equiv> os_assn char_assn\<close>

definition \<open>string_rel \<equiv> \<langle>char_rel\<rangle>list_rel\<close>

subsection \<open>Lexicographic Order on Lists\<close>

text \<open>The linear order on lists (lexicographic) is needed already here so that the
  refinement rule for \<open>strl_lt\<close> can be stated against the abstract \<open>(<)\<close>. It used to live
  in \<open>PAC_Checker_Relation\<close>, but that theory is downstream of \<open>String_Assn\<close> \<emdash> moving the
  instantiation up makes \<open>(<) :: str \<Rightarrow> str \<Rightarrow> bool\<close> available here; \<open>PAC_Checker_Relation\<close>
  inherits it (via \<open>Monom_Assn\<close>).\<close>

instantiation list :: (linorder) linorder
begin
  definition less_list where  "less_list = lexordp (<)"
  definition less_eq_list where "less_eq_list = lexordp_eq"

instance
proof standard
  have [dest]: \<open>\<And>x y :: 'a :: linorder list. (x, y) \<in> lexord {(x, y). x < y} \<Longrightarrow>
           lexordp_eq y x \<Longrightarrow> False\<close>
    by (metis lexordp_antisym lexordp_conv_lexord lexordp_eq_conv_lexord)
  have [simp]: \<open>\<And>x y :: 'a :: linorder list. lexordp_eq x y \<Longrightarrow>
           \<not> lexordp_eq y x \<Longrightarrow>
           (x, y) \<in> lexord {(x, y). x < y}\<close>
    using lexordp_conv_lexord lexordp_conv_lexordp_eq by blast
  show
   \<open>(x < y) = Restricted_Predicates.strict (\<le>) x y\<close>
   \<open>x \<le> x\<close>
   \<open>x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z\<close>
   \<open>x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y\<close>
   \<open>x \<le> y \<or> y \<le> x\<close>
   for x y z :: \<open>'a :: linorder list\<close>
    by (auto simp: less_list_def less_eq_list_def List.lexordp_def
    lexordp_conv_lexord lexordp_into_lexordp_eq lexordp_antisym
    antisym_def lexordp_eq_refl lexordp_eq_linear intro: lexordp_eq_trans
    dest: lexordp_eq_antisym)
qed

end

text \<open>The defining recursion of the list order (matching @{const lexordp}'s \<open>[code]\<close> rules):
  supplied locally in the order proofs below rather than declared globally \<open>[simp]\<close>, to
  avoid perturbing downstream simpsets.\<close>

lemma list_less_Nil_left: \<open>(([]::'a::linorder list) < ys) = (ys \<noteq> [])\<close>
  by (cases ys) (auto simp: less_list_def lexordp_def)

lemma list_less_Nil_right: \<open>(xs < ([]::'a::linorder list)) = False\<close>
  by (auto simp: less_list_def lexordp_def)

lemma list_less_Cons: \<open>((x # xs) < (y # ys)) = (x < y \<or> (x = y \<and> xs < ys))\<close>
  for x :: \<open>'a::linorder\<close>
  by (auto simp: less_list_def lexordp_def)

subsection \<open>String Equality\<close>

text \<open>First-order specialization of the higher-order template, for code export.\<close>

definition str_eq :: \<open>8 word os_list \<Rightarrow> 8 word os_list \<Rightarrow> 1 word llM\<close> where
  \<open>str_eq \<equiv> os_eq ll_icmp_eq\<close>

lemma str_eq_simps[llvm_code]:
  \<open>str_eq p q = (
    if p = null then Mreturn (from_bool (q = null))
    else if q = null then Mreturn 0
    else doM {
      np \<leftarrow> ll_load p; nq \<leftarrow> ll_load q;
      b \<leftarrow> ll_icmp_eq (node.val np) (node.val nq);
      if to_bool b then str_eq (node.next np) (node.next nq)
      else Mreturn 0 })\<close>
  unfolding str_eq_def by (rule os_eq.simps)

lemma str_eq_rule[vcg_rules]:
  \<open>llvm_htriple (strl_assn xs p ** strl_assn ys q) (str_eq p q)
    (\<lambda>r. strl_assn xs p ** strl_assn ys q ** \<upharpoonleft>bool.assn (xs = ys) r)\<close>
  unfolding str_eq_def
  by (rule os_eq_rule[where A=char_assn and eqi=ll_icmp_eq, OF char_assn_pure char_eq_rule])

sepref_register \<open>(=) :: char list \<Rightarrow> char list \<Rightarrow> bool\<close>

lemma str_eq_hnr[sepref_fr_rules]:
  \<open>(uncurry str_eq, uncurry (RETURN oo (=))) \<in> strl_assn\<^sup>k *\<^sub>a strl_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding str_eq_def
  using ol_eq_hnr[where A=char_assn and eqi=ll_icmp_eq, OF char_eq_rule]
  unfolding ol_assn_pure_conv[OF char_assn_pure] .

subsection \<open>Lexicographic Order for Strings\<close>

text \<open>Generic template deciding the lexicographic order \<open>xs < ys\<close> on open lists, given an
  element \<^emph>\<open>strict less\<close> \<open>lti\<close> and an element \<^emph>\<open>equality\<close> \<open>eqi\<close>. The three-way node step
  mirrors @{const lexordp}'s \<open>[code]\<close> recursion \<open>x < y \<or> (x = y \<and> xs < ys)\<close>: if the heads
  are strictly ordered we are done (\<open>1\<close>/\<open>0\<close>), if they are equal we recurse, otherwise the
  left head is the greater one (\<open>0\<close>). The order-agnostic \<^emph>\<open>true\<close>/\<^emph>\<open>false\<close> literals \<open>1\<close>/\<open>0\<close>
  are \<open>from_bool True\<close>/\<open>from_bool False\<close>. Analogous to @{const os_eq}; not \<open>[llvm_code]\<close>
  (higher-order in \<open>lti\<close>/\<open>eqi\<close>), so instances are specialized first-order for export.\<close>

partial_function (M) os_less ::
  \<open>('c::llvm_rep \<Rightarrow> 'c \<Rightarrow> 1 word llM) \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> 1 word llM)
     \<Rightarrow> 'c os_list \<Rightarrow> 'c os_list \<Rightarrow> 1 word llM\<close> where
  \<open>os_less lti eqi p q = (
    if q = null then Mreturn 0
    else if p = null then Mreturn 1
    else doM {
      np \<leftarrow> ll_load p; nq \<leftarrow> ll_load q;
      b \<leftarrow> lti (node.val np) (node.val nq);
      if to_bool b then Mreturn 1
      else doM {
        e \<leftarrow> eqi (node.val np) (node.val nq);
        if to_bool e then os_less lti eqi (node.next np) (node.next nq)
        else Mreturn 0 } })\<close>

text \<open>Correctness at the owning-list level (arbitrary element assertion \<open>A\<close> over a
  \<open>linorder\<close>). Same recursion technique as @{thm ol_eq_rule}: one \<open>subst os_less.simps\<close>
  per case, induction hypothesis + the element rules as \<open>vcg_rules\<close>. The list-order
  recursion lemmas are supplied locally.\<close>

lemma ol_less_rule:
  assumes LT: \<open>\<And>a c a' c'. llvm_htriple (A a c ** A a' c') (lti c c')
    (\<lambda>r. A a c ** A a' c' ** \<upharpoonleft>bool.assn (a < a') r)\<close>
  and EQ: \<open>\<And>a c a' c'. llvm_htriple (A a c ** A a' c') (eqi c c')
    (\<lambda>r. A a c ** A a' c' ** \<upharpoonleft>bool.assn (a = a') r)\<close>
  shows \<open>llvm_htriple (ol_assn A xs p ** ol_assn A ys q) (os_less lti eqi p q)
    (\<lambda>r. ol_assn A xs p ** ol_assn A ys q ** \<upharpoonleft>bool.assn ((xs::'a::linorder list) < ys) r)\<close>
  unfolding ol_assn_conv
proof (induction xs arbitrary: ys p q)
  case Nil
  show ?case
    supply [simp] = bool.assn_def from_bool_def list_less_Nil_left
    apply (subst os_less.simps)
    apply (cases ys; cases \<open>q = null\<close>; simp)
    by vcg
next
  case (Cons x xs)
  interpret llvm_prim_ctrl_setup .
  note [vcg_rules] = Cons.IH LT EQ
  show ?case
    supply [simp, named_ss fri_prepare_simps] = ol_seg_cons
    supply [simp] = bool.assn_def from_bool_def sep_conj_exists
      list_less_Cons list_less_Nil_right
    apply (subst os_less.simps)
    apply (cases \<open>p = null\<close>; cases \<open>q = null\<close>; cases ys; simp)
    by vcg
qed

lemma os_less_rule:
  assumes P: \<open>is_pure A\<close>
  and LT: \<open>\<And>a c a' c'. llvm_htriple (A a c ** A a' c') (lti c c')
    (\<lambda>r. A a c ** A a' c' ** \<upharpoonleft>bool.assn (a < a') r)\<close>
  and EQ: \<open>\<And>a c a' c'. llvm_htriple (A a c ** A a' c') (eqi c c')
    (\<lambda>r. A a c ** A a' c' ** \<upharpoonleft>bool.assn (a = a') r)\<close>
  shows \<open>llvm_htriple (os_assn A xs p ** os_assn A ys q) (os_less lti eqi p q)
    (\<lambda>r. os_assn A xs p ** os_assn A ys q ** \<upharpoonleft>bool.assn ((xs::'a::linorder list) < ys) r)\<close>
  using ol_less_rule[where A=A and lti=lti and eqi=eqi, OF LT EQ]
  unfolding ol_assn_pure_conv[OF P] .

lemma ol_less_hnr:
  assumes LT: \<open>\<And>a c a' c'. llvm_htriple (A a c ** A a' c') (lti c c')
    (\<lambda>r. A a c ** A a' c' ** \<upharpoonleft>bool.assn (a < a') r)\<close>
  and EQ: \<open>\<And>a c a' c'. llvm_htriple (A a c ** A a' c') (eqi c c')
    (\<lambda>r. A a c ** A a' c' ** \<upharpoonleft>bool.assn (a = a') r)\<close>
  shows \<open>(uncurry (os_less lti eqi), uncurry (RETURN oo (<)))
    \<in> (ol_assn (A :: 'a::linorder \<Rightarrow> _))\<^sup>k *\<^sub>a (ol_assn A)\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding bool1_rel_def bool.assn_is_rel[symmetric]
  supply [vcg_rules] = ol_less_rule[OF LT EQ]
  apply sepref_to_hoare
  apply vcg_monadify
  by vcg'

text \<open>First-order specialization for code export (recursive call folded to \<open>strl_lt\<close>).\<close>

definition strl_lt :: \<open>8 word os_list \<Rightarrow> 8 word os_list \<Rightarrow> 1 word llM\<close> where
  \<open>strl_lt \<equiv> os_less ll_icmp_ult ll_icmp_eq\<close>

lemma strl_lt_simps[llvm_code]:
  \<open>strl_lt p q = (
    if q = null then Mreturn 0
    else if p = null then Mreturn 1
    else doM {
      np \<leftarrow> ll_load p; nq \<leftarrow> ll_load q;
      b \<leftarrow> ll_icmp_ult (node.val np) (node.val nq);
      if to_bool b then Mreturn 1
      else doM {
        e \<leftarrow> ll_icmp_eq (node.val np) (node.val nq);
        if to_bool e then strl_lt (node.next np) (node.next nq)
        else Mreturn 0 } })\<close>
  unfolding strl_lt_def by (rule os_less.simps)

lemma strl_lt_rule[vcg_rules]:
  \<open>llvm_htriple (strl_assn xs p ** strl_assn ys q) (strl_lt p q)
    (\<lambda>r. strl_assn xs p ** strl_assn ys q ** \<upharpoonleft>bool.assn (xs < ys) r)\<close>
  unfolding strl_lt_def
  by (rule os_less_rule[where A=char_assn and lti=ll_icmp_ult and eqi=ll_icmp_eq,
        OF char_assn_pure char_lt_rule char_eq_rule])

sepref_register \<open>(<) :: char list \<Rightarrow> char list \<Rightarrow> bool\<close>

lemma strl_lt_hnr[sepref_fr_rules]:
  \<open>(uncurry strl_lt, uncurry (RETURN oo (<))) \<in> strl_assn\<^sup>k *\<^sub>a strl_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding strl_lt_def
  using ol_less_hnr[where A=char_assn and lti=ll_icmp_ult and eqi=ll_icmp_eq,
      OF char_lt_rule char_eq_rule]
  unfolding ol_assn_pure_conv[OF char_assn_pure] .

text \<open>We are lazy and use an additional negation to implement \<le> (TODO: properly implement)\<close>

definition \<open>ls_le (a :: ('a::linorder) list) b \<equiv> \<not>(b < a)\<close>

lemma le_by_lt_str: \<open>(a :: ('a::linorder) list) \<le> b \<equiv> \<not>(b < a)\<close> 
  by (simp add: linorder_not_less)

sepref_def strl_le_impl is \<open>uncurry (RETURN oo ls_le)\<close>
  :: \<open>strl_assn\<^sup>k *\<^sub>a strl_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding ls_le_def 
  by sepref

sepref_register \<open>(\<le>) :: char list \<Rightarrow> char list \<Rightarrow> bool\<close>
lemma strl_le_hnr[sepref_fr_rules]:
  \<open>(uncurry strl_le_impl, uncurry (RETURN oo (\<le>)))
  \<in> strl_assn\<^sup>k *\<^sub>a strl_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  using strl_le_impl.refine unfolding ls_le_def le_by_lt_str .

text \<open>The \<open>\<le>\<close>-comparator in htriple form (for hand-written \<open>vcg\<close> proofs about code
  calling \<open>strl_le_impl\<close>): \<open>vcg\<close> after unfolding the synthesized \<open>strl_le_impl_def\<close>
  (a \<open>strl_lt\<close> call with swapped arguments plus a \<open>1 word\<close> negation), with
  \<open>strl_lt_rule\<close> in scope and \<open>le_by_lt_str\<close> for the abstract side.\<close>

lemma strl_le_rule[vcg_rules]:
  \<open>llvm_htriple (strl_assn xs p ** strl_assn ys q) (strl_le_impl p q)
    (\<lambda>r. strl_assn xs p ** strl_assn ys q ** \<upharpoonleft>bool.assn (xs \<le> ys) r)\<close>
  unfolding le_by_lt_str strl_le_impl_def
  by vcg

subsection \<open>String Copy\<close>

text \<open>Deep copy of a string: the \<open>ol_copy\<close> walk with the trivial element copy \<open>Mreturn\<close>
  (chars are pure). Registered against \<open>COPY\<close>, so sepref can duplicate strings whenever
  abstract code uses an owned string twice. First-order recursion equations are derived
  for code export, cf. \<open>str_eq_simps\<close>.\<close>

definition strl_copy :: \<open>8 word os_list \<Rightarrow> 8 word os_list llM\<close> where
  \<open>strl_copy \<equiv> ol_copy Mreturn\<close>

lemma strl_copy_simps[llvm_code]:
  \<open>strl_copy p = (if p = null then Mreturn null else doM {
      n \<leftarrow> ll_load p;
      c \<leftarrow> Mreturn (node.val n);
      t \<leftarrow> strl_copy (node.next n);
      os_prepend c t
    })\<close>
  unfolding strl_copy_def by (rule ol_copy.simps)

lemma strl_copy_rule[vcg_rules]:
  \<open>llvm_htriple (strl_assn xs p) (strl_copy p) (\<lambda>r. strl_assn xs p ** strl_assn xs r)\<close>
  using os_copy_rule[where A=char_assn, OF char_assn_pure]
  unfolding strl_copy_def .

lemma strl_copy_hnr[sepref_fr_rules]:
  \<open>(strl_copy, RETURN o COPY) \<in> strl_assn\<^sup>k \<rightarrow>\<^sub>a strl_assn\<close>
  using ol_copy_hnr[where A=char_assn and cp=Mreturn,
      OF pure_elem_copy_rule[OF char_assn_pure]]
  unfolding ol_assn_pure_conv[OF char_assn_pure] strl_copy_def .

subsection \<open>String Sorting\<close>

text \<open>Instance of the generic merge sort (\<open>LLVM_Sort\<close>) at \<open>strl_assn\<close>, sorting the
  characters of a string by the char order (\<open>char_le_hnr\<close> from \<open>Char_Assn\<close> is the
  comparator rule). The only missing list operation at the \<open>os_assn\<close> level is
  \<open>mop_list_pop_front\<close> \<emdash> for pure elements it coincides with the owning-list rule via
  @{thm ol_assn_pure_conv}. The empty producer in the split's base case resolves via
  the generic \<open>op_list_empty\<close> implementation (\<open>os_empty\<close>), so the plain
  \<open>alt_split_RECT\<close> variant applies.\<close>

lemma strl_pop_front_hnr[sepref_fr_rules]:
  \<open>(os_pop, mop_list_pop_front) \<in> strl_assn\<^sup>d \<rightarrow>\<^sub>a char_assn \<times>\<^sub>a strl_assn\<close>
  using ol_pop_front_hnr[where A=char_assn]
  unfolding ol_assn_pure_conv[OF char_assn_pure] .

definition merge_chars :: \<open>char list \<Rightarrow> char list \<Rightarrow> char list\<close> where
  \<open>merge_chars = merge (\<le>)\<close>

definition msort_chars :: \<open>char list \<Rightarrow> char list\<close> where
  \<open>msort_chars = msort_alt (\<le>)\<close>

sepref_register merge_chars msort_chars

sepref_def strl_merge_impl is \<open>uncurry (RETURN oo merge_chars)\<close>
  :: \<open>strl_assn\<^sup>d *\<^sub>a strl_assn\<^sup>d \<rightarrow>\<^sub>a strl_assn\<close>
  unfolding merge_chars_def merge_RECT
  by sepref

sepref_def strl_split_impl is \<open>RETURN o alt_split\<close>
  :: \<open>strl_assn\<^sup>d \<rightarrow>\<^sub>a strl_assn \<times>\<^sub>a strl_assn\<close>
  unfolding alt_split_RECT
  by sepref

sepref_def strl_msort_impl is \<open>RETURN o msort_chars\<close>
  :: \<open>strl_assn\<^sup>d \<rightarrow>\<^sub>a strl_assn\<close>
  unfolding msort_chars_def msort_alt_RECT merge_chars_def[symmetric]
  by sepref

lemma msort_chars_mset[simp]: \<open>mset (msort_chars xs) = mset xs\<close>
  unfolding msort_chars_def by simp

lemma msort_chars_sorted: \<open>sorted_wrt (\<le>) (msort_chars xs)\<close>
  unfolding msort_chars_def
  by (rule msort_alt_sorted) (auto intro: transpI)

section \<open>String Hashing (FNV-1a)\<close>

text \<open>The abstract hash function is taken over verbatim from the (array-string based)
  prototype in \<^file>\<open>String_Hash_Map.thy\<close>; the concrete implementation there
  (\<open>shs_hash_impl\<close>, an indexed loop over a character array) does not fit the open-list
  representation \<open>strl_assn\<close>, so the walk is re-implemented as a recursive node visit
  in the style of \<^const>\<open>os_eq\<close>. Values from
  \<^url>\<open>https://en.wikipedia.org/wiki/Fowler%E2%80%93Noll%E2%80%93Vo_hash_function\<close>.\<close>

definition uc8_64 :: \<open>8 word \<Rightarrow> 64 word\<close> where \<open>uc8_64 \<equiv> UCAST(8 \<rightarrow> 64)\<close>

definition fnv_prime :: \<open>64 word\<close> where \<open>fnv_prime = 1099511628211\<close>
definition fnv_offset_basis :: \<open>64 word\<close> where \<open>fnv_offset_basis = 14695981039346656037\<close>

definition fnv_step :: \<open>64 word \<Rightarrow> char \<Rightarrow> 64 word\<close> where
  \<open>fnv_step h c = (h XOR uc8_64 (of_char c)) * fnv_prime\<close>

definition fnv_1a_of_str :: \<open>char list \<Rightarrow> 64 word\<close> where
  \<open>fnv_1a_of_str = foldl fnv_step fnv_offset_basis\<close>

text \<open>Char/word bridge (copied from \<^file>\<open>String_Array_Assn.thy\<close>, which is not imported
  here): the concrete 8-bit word of a char-related pair is recovered by \<open>of_char\<close>.\<close>

lemma of_char_word_id: \<open>x = of_char (char_of (unat (x :: 8 word)))\<close>
  by (metis of_char_of of_nat_of_char unat_of_char_mod word_unat.Rep_inverse)

lemma of_char_char_of_word[simp]: \<open>of_char (char_of_word w) = w\<close>
  unfolding char_of_word_def comp_apply by (rule of_char_word_id[symmetric])

partial_function (M) strl_hash_aux :: \<open>64 word \<Rightarrow> 8 word os_list \<Rightarrow> 64 word llM\<close> where
  \<open>strl_hash_aux h p = (if p = null then Mreturn h
    else doM {
      n \<leftarrow> ll_load p;
      c \<leftarrow> ll_zext (node.val n) TYPE(64 word);
      h \<leftarrow> ll_xor h c;
      h \<leftarrow> ll_mul h 1099511628211;
      strl_hash_aux h (node.next n)
    })\<close>

text \<open>First-order, so the recursion equations export directly.\<close>
lemmas [llvm_code] = strl_hash_aux.simps

definition strl_hash :: \<open>8 word os_list \<Rightarrow> 64 word llM\<close> where [llvm_code]:
  \<open>strl_hash p \<equiv> strl_hash_aux 14695981039346656037 p\<close>

text \<open>Raw arithmetic rules for the loop body, proven once inside a throwaway
  \<open>llvm_prim_arith_setup\<close> context and supplied locally (the raw-arithmetic recipe
  from \<open>CLAUDE.md\<close>; do not declare them \<open>[vcg_rules]\<close> globally).\<close>

context begin
interpretation llvm_prim_arith_setup .

lemma strl_char_zext_rule:
  \<open>llvm_htriple (char_assn c ci) (ll_zext ci TYPE(64 word))
    (\<lambda>r. char_assn c ci ** \<up>(r = uc8_64 (of_char c)))\<close>
  unfolding char_assn_def char_rel_def uc8_64_def
  supply [simp] = pure_def in_br_conv is_up'
  by vcg

lemma strl_ll_xor64_rule:
  \<open>llvm_htriple \<box> (ll_xor (a :: 64 word) b) (\<lambda>r. \<up>(r = a XOR b))\<close>
  by vcg

lemma strl_ll_mul64_rule:
  \<open>llvm_htriple \<box> (ll_mul (a :: 64 word) b) (\<lambda>r. \<up>(r = a * b))\<close>
  by vcg

end

lemma strl_hash_aux_rule:
  \<open>llvm_htriple (ol_assn char_assn cs p) (strl_hash_aux h p)
    (\<lambda>r. ol_assn char_assn cs p ** \<up>(r = foldl fnv_step h cs))\<close>
  unfolding ol_assn_conv
proof (induction cs arbitrary: h p)
  case Nil
  show ?case
    apply (subst strl_hash_aux.simps)
    by vcg
next
  case (Cons c cs)
  interpret llvm_prim_ctrl_setup .
  note [vcg_rules] = Cons.IH strl_char_zext_rule strl_ll_xor64_rule strl_ll_mul64_rule
  show ?case
    supply [simp, named_ss fri_prepare_simps] = ol_seg_cons
    supply [simp] = sep_conj_exists fnv_step_def fnv_prime_def
    apply (subst strl_hash_aux.simps)
    apply (cases \<open>p = null\<close>; simp)
    by vcg
qed

lemma strl_hash_rule[vcg_rules]:
  \<open>llvm_htriple (strl_assn cs p) (strl_hash p)
    (\<lambda>r. strl_assn cs p ** \<up>(r = fnv_1a_of_str cs))\<close>
  unfolding strl_hash_def fnv_1a_of_str_def fnv_offset_basis_def
  by (rule strl_hash_aux_rule[unfolded ol_assn_pure_conv[OF char_assn_pure]])

section \<open>Hash Sets of Strings\<close>

text \<open>Instantiation of the generic hash set (\<^file>\<open>IICF_Hash_Set.thy\<close>) with open-list
  strings: elements \<open>strl_assn\<close>, equality \<^const>\<open>str_eq\<close>, copy \<^const>\<open>strl_copy\<close>,
  free \<^const>\<open>os_delete\<close>, hash \<^const>\<open>strl_hash\<close> / \<^const>\<open>fnv_1a_of_str\<close>. This is the
  replacement for the placeholder \<open>hs_assn string_assn\<close> (\<open>vars_assn\<close> in
  \<open>PAC_Checker_Synthesis\<close>).\<close>

definition vars_hs_assn :: \<open>char list set \<Rightarrow> 8 word os_list hs_impl \<Rightarrow> assn\<close> where
  \<open>vars_hs_assn \<equiv> hs_set_assn fnv_1a_of_str strl_assn\<close>

subsection \<open>First-order specializations (code export)\<close>

definition vars_hs_bucket_member_impl ::
  \<open>8 word os_list \<Rightarrow> 8 word os_list hs_bucket_impl \<Rightarrow> 1 word llM\<close> where
  \<open>vars_hs_bucket_member_impl \<equiv> hs_bucket_member_impl str_eq\<close>

lemma vars_hs_bucket_member_impl_simps[llvm_code]:
  \<open>vars_hs_bucket_member_impl x p = (if p = null then Mreturn 0
    else doM {
      n \<leftarrow> ll_load p;
      eq \<leftarrow> str_eq (node.val n) x;
      if to_bool eq then Mreturn 1
      else vars_hs_bucket_member_impl x (node.next n)
    })\<close>
  unfolding vars_hs_bucket_member_impl_def
  by (rule hs_bucket_member_impl.simps)

definition vars_hs_bucket_free_impl ::
  \<open>8 word os_list hs_bucket_impl \<Rightarrow> unit llM\<close> where
  \<open>vars_hs_bucket_free_impl \<equiv> hs_bucket_free_impl os_delete\<close>

lemma vars_hs_bucket_free_impl_simps[llvm_code]:
  \<open>vars_hs_bucket_free_impl p = (if p = null then Mreturn () else doM {
      n \<leftarrow> ll_load p;
      os_delete (node.val n);
      ll_free p;
      vars_hs_bucket_free_impl (node.next n)
    })\<close>
  unfolding vars_hs_bucket_free_impl_def hs_bucket_free_impl_def
  by (rule ol_delete.simps)

definition vars_hs_member_impl ::
  \<open>8 word os_list \<Rightarrow> 8 word os_list hs_impl \<Rightarrow> 1 word llM\<close> where
  \<open>vars_hs_member_impl \<equiv> hs_member_impl strl_hash str_eq\<close>

lemma vars_hs_member_impl_code[llvm_code]:
  \<open>vars_hs_member_impl x s = (case s of (n, a) \<Rightarrow> doM {
      h \<leftarrow> strl_hash x;
      i \<leftarrow> ll_urem h n;
      bin \<leftarrow> nao_nth a i;
      found \<leftarrow> vars_hs_bucket_member_impl x bin;
      nao_rejoin a i;
      Mreturn found
    })\<close>
  unfolding vars_hs_member_impl_def hs_member_impl_def hs_member_hashed_impl_def
    vars_hs_bucket_member_impl_def
  by (simp split: prod.split)

definition vars_hs_insert_impl ::
  \<open>8 word os_list \<Rightarrow> 8 word os_list hs_impl \<Rightarrow> 8 word os_list hs_impl llM\<close> where
  \<open>vars_hs_insert_impl \<equiv> hs_insert_impl strl_hash str_eq strl_copy\<close>

lemma vars_hs_insert_impl_code[llvm_code]:
  \<open>vars_hs_insert_impl x s = (case s of (n, a) \<Rightarrow> doM {
      h \<leftarrow> strl_hash x;
      i \<leftarrow> ll_urem h n;
      bin \<leftarrow> nao_nth a i;
      found \<leftarrow> vars_hs_bucket_member_impl x bin;
      llc_if found
        (doM { nao_rejoin a i; Mreturn (n, a) })
        (doM {
          x' \<leftarrow> strl_copy x;
          bin \<leftarrow> os_prepend x' bin;
          a \<leftarrow> nao_upd a i bin;
          Mreturn (n, a)
        })
    })\<close>
  unfolding vars_hs_insert_impl_def hs_insert_impl_def hs_insert_hashed_impl_def
    vars_hs_bucket_member_impl_def
  by (simp split: prod.split)

definition vars_hs_empty_impl :: \<open>unit \<Rightarrow> 8 word os_list hs_impl llM\<close>
  where [llvm_inline]:
  \<open>vars_hs_empty_impl \<equiv> hs_empty_impl\<close>

definition vars_hs_free_impl :: \<open>8 word os_list hs_impl \<Rightarrow> unit llM\<close> where
  \<open>vars_hs_free_impl \<equiv> hs_free_impl os_delete\<close>

lemma vars_hs_free_impl_code[llvm_code]:
  \<open>vars_hs_free_impl s = (case s of (n, a) \<Rightarrow> nao_free vars_hs_bucket_free_impl a n)\<close>
  unfolding vars_hs_free_impl_def hs_free_impl_def vars_hs_bucket_free_impl_def
  by (simp split: prod.split)

subsection \<open>Interface rules\<close>

text \<open>The producer op gets its own name (\<open>set_custom_empty\<close> idiom), so that other set
  implementations can coexist; use \<open>vars_hs.fold_custom_empty\<close> at synthesis sites.\<close>

definition op_vars_hs_empty :: \<open>char list set\<close> where [simp]:
  \<open>op_vars_hs_empty \<equiv> op_set_empty\<close>

interpretation vars_hs: set_custom_empty \<open>vars_hs_empty_impl ()\<close> op_vars_hs_empty
  by unfold_locales simp

lemma vars_hs_empty_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (vars_hs_empty_impl ()), uncurry0 (RETURN op_vars_hs_empty))
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a vars_hs_assn\<close>
  unfolding vars_hs_empty_impl_def vars_hs_assn_def op_vars_hs_empty_def
  by (rule hs_empty_hnr)

lemma vars_hs_member_hnr[sepref_fr_rules]:
  \<open>(uncurry vars_hs_member_impl, uncurry (RETURN oo op_set_member))
    \<in> strl_assn\<^sup>k *\<^sub>a vars_hs_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding vars_hs_member_impl_def vars_hs_assn_def
  by (rule hs_member_hnr[OF strl_hash_rule str_eq_rule])

text \<open>Membership as a plain triple at the \<^emph>\<open>composed\<close> \<open>vars_hs_assn\<close> level, for
  use as a \<open>vcg_rule\<close> inside hand-written walks that test many strings against
  the same set (e.g.\ the \<open>vars_of_monom_in\<close>/\<open>vars_of_poly_in\<close> ladder of the
  LPAC checker): the \<open>hr_comp\<close> is unfolded once here; callers keep the set
  assertion folded and never see the bucket list.\<close>

lemma vars_hs_member_rule:
  \<open>llvm_htriple
    (vars_hs_assn \<V> vi ** strl_assn x xi)
    (vars_hs_member_impl xi vi)
    (\<lambda>r. vars_hs_assn \<V> vi ** strl_assn x xi ** \<upharpoonleft>bool.assn (x \<in> \<V>) r)\<close>
  unfolding vars_hs_assn_def hs_set_assn_def vars_hs_member_impl_def
  supply [vcg_rules] = hs_member_impl_rule[OF strl_hash_rule str_eq_rule]
  supply [simp] = hr_comp_def hs_rel_def in_br_conv hs_member_correct sep_conj_exists
  by vcg

lemma vars_hs_insert_hnr[sepref_fr_rules]:
  \<open>(uncurry vars_hs_insert_impl, uncurry (RETURN oo op_set_insert))
    \<in> strl_assn\<^sup>k *\<^sub>a vars_hs_assn\<^sup>d \<rightarrow>\<^sub>a vars_hs_assn\<close>
  unfolding vars_hs_insert_impl_def vars_hs_assn_def
  by (rule hs_insert_hnr[OF strl_hash_rule str_eq_rule strl_copy_rule])

lemma vars_hs_assn_free[sepref_frame_free_rules]:
  \<open>MK_FREE vars_hs_assn vars_hs_free_impl\<close>
  unfolding vars_hs_assn_def vars_hs_free_impl_def
  by (rule hs_set_assn_free[OF os_assn_free])

section \<open>Testing\<close>

experiment begin

  text \<open>Smoke test for the hash-set interface rules: empty \<rightarrow> insert \<rightarrow> member
    composes through sepref (the intermediate set is consumed by insert, the final
    set is dropped via the \<open>MK_FREE\<close> rule).\<close>

  definition ins_mem_test :: \<open>char list \<Rightarrow> char list \<Rightarrow> bool\<close> where
    \<open>ins_mem_test a b = (a \<in> insert b {})\<close>

  sepref_def ins_mem_test_impl is \<open>uncurry (RETURN oo ins_mem_test)\<close>
    :: \<open>strl_assn\<^sup>k *\<^sub>a strl_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
    unfolding ins_mem_test_def vars_hs.fold_custom_empty
    by sepref

  definition eq_test :: \<open>str \<Rightarrow> str \<Rightarrow> bool\<close> where
    \<open>eq_test xs ys = (xs = ys)\<close>

  sepref_def eq_test_impl is \<open>uncurry (RETURN oo eq_test)\<close>
    :: \<open>strl_assn\<^sup>k *\<^sub>a strl_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
    unfolding eq_test_def by sepref

  definition lt_test :: \<open>str \<Rightarrow> str \<Rightarrow> bool\<close> where
    \<open>lt_test xs ys = (xs < ys)\<close>

  sepref_def lt_test_impl is \<open>uncurry (RETURN oo lt_test)\<close>
    :: \<open>strl_assn\<^sup>k *\<^sub>a strl_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
    unfolding lt_test_def by sepref

  definition test :: \<open>str \<Rightarrow> char\<close> where
    \<open>test cs \<equiv> (if cs = [] then (char_of_word (0::(8 word))) else hd cs)\<close>

  sepref_def test_impl is \<open>RETURN o test\<close>
    :: \<open>strl_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
    unfolding test_def
    by sepref

  (* export_llvm \<open>test_impl\<close> *)

  definition empty_check :: \<open>str \<Rightarrow> bool\<close> where
    \<open>empty_check cs \<equiv> cs = []\<close>

  sepref_def empty_check_impl is \<open>RETURN o empty_check\<close>
    :: \<open>strl_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
    unfolding empty_check_def
    by sepref

  (* export_llvm empty_check_impl *)

  definition cons_test :: \<open>str \<Rightarrow> char \<Rightarrow> str\<close> where
    \<open>cons_test cs c = c # cs\<close>

  sepref_def cons_test_impl is \<open>uncurry (RETURN oo cons_test)\<close>
    :: \<open>strl_assn\<^sup>d *\<^sub>a char_assn\<^sup>k \<rightarrow>\<^sub>a strl_assn\<close>
    unfolding cons_test_def
    by sepref

  definition tail_test :: \<open>str \<Rightarrow> str\<close> where
    \<open>tail_test cs = (if cs = [] then cs else tl cs)\<close>

  sepref_def tail_test_impl is \<open>RETURN o tail_test\<close>
    :: \<open>strl_assn\<^sup>d \<rightarrow>\<^sub>a strl_assn\<close>
    unfolding tail_test_def
    by sepref

  (* definition swap_test' :: \<open>str \<Rightarrow> str\<close> where
   *   \<open>swap_test' cs = (if cs = [] then cs else
   *     let a = hd cs; bs = tl cs in
   *     a # bs
   *   )\<close> *)

  definition dest_cons_test :: \<open>str \<Rightarrow> str\<close> where
    \<open>dest_cons_test cs = (case cs of
      [] \<Rightarrow> cs
    | (c # cs') \<Rightarrow> c # cs'
    )\<close>

  (* Pattern matching / case of does not work *)
  sepref_def dest_cons_test_impl is \<open>RETURN o dest_cons_test\<close>
    :: \<open>strl_assn\<^sup>d \<rightarrow>\<^sub>a strl_assn\<close>
    unfolding dest_cons_test_def
    apply sepref_dbg_keep
    apply sepref_dbg_trans_keep
    apply sepref_dbg_trans_step_keep
    apply sepref_dbg_side_unfold
    oops

  (* But a simple workaround is to unfold list.case_eq_if *)
  sepref_def dest_cons_test_impl' is \<open>RETURN o dest_cons_test\<close>
    :: \<open>strl_assn\<^sup>d \<rightarrow>\<^sub>a strl_assn\<close>
    unfolding dest_cons_test_def list.case_eq_if
    by sepref

  definition str_dup_test :: \<open>str \<Rightarrow> str \<times> str\<close> where
    \<open>str_dup_test cs = (cs, cs)\<close>

  text \<open>Exercises automatic \<open>COPY\<close> insertion: the argument is owned and used twice, so
    monadify inserts a \<open>COPY\<close>, resolved by \<open>strl_copy_hnr\<close>.\<close>
  sepref_def str_dup_test_impl is \<open>RETURN o str_dup_test\<close>
    :: \<open>strl_assn\<^sup>d \<rightarrow>\<^sub>a strl_assn \<times>\<^sub>a strl_assn\<close>
    unfolding str_dup_test_def
    by sepref

  export_llvm str_dup_test_impl

end

end
