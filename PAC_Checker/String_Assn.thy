theory String_Assn
  imports IICF_Owning_List Char_Assn
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

text \<open>Instantiation ladder for the generic \<open>os_eq\<close> template: the element comparison for
  chars is plain \<open>ll_icmp_eq\<close>, correct because \<open>char_rel\<close> is bi-unique (injectivity of
  \<open>char_of_word\<close>). Feeding the resulting \<open>str_eq_rule\<close> back into \<open>ol_eq_rule\<close> one level
  up gives monomial equality (\<open>os_eq str_eq\<close> at \<open>ol_assn strl_assn\<close>) \<emdash> no purity needed
  at that level.\<close>

lemma char_of_word_inj: \<open>char_of_word a = char_of_word b \<longleftrightarrow> a = b\<close>
proof
  assume \<open>char_of_word a = char_of_word b\<close>
  hence \<open>(of_char (char_of_word a) :: nat) = of_char (char_of_word b)\<close> by simp
  hence \<open>unat a = unat b\<close>
    unfolding char_of_word_def by (simp add: of_char_of unat_of_char_mod)
  thus \<open>a = b\<close> by (simp add: word_unat_eq_iff)
qed simp

text \<open>The element-equality rule in the htriple format expected by \<open>ol_eq_rule\<close>'s premise.
  Proven in a throwaway \<open>llvm_prim_arith_setup\<close> context (cf. CLAUDE.md); NOT declared
  \<open>[vcg_rules]\<close> globally \<emdash> a raw \<open>ll_icmp_eq\<close> rule could hijack snat/unat comparisons
  elsewhere.\<close>

context begin
interpretation llvm_prim_arith_setup .

lemma char_eq_rule:
  \<open>llvm_htriple (char_assn a c ** char_assn a' c') (ll_icmp_eq c c')
    (\<lambda>r. char_assn a c ** char_assn a' c' ** \<upharpoonleft>bool.assn (a = a') r)\<close>
  unfolding char_assn_def char_rel_def
  supply [simp] = pure_def in_br_conv bool.assn_def char_of_word_inj
  by vcg

end

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

text \<open>Element rule for chars: \<open>ll_icmp_ult\<close> on words decides \<open>(<)\<close> on chars, because
  \<open>char_of_word\<close> is order-preserving (unsigned word order matches char order). Proven in
  a throwaway \<open>llvm_prim_arith_setup\<close> context, cf. @{thm char_eq_rule}.\<close>

lemma char_of_word_less: \<open>char_of_word c < char_of_word c' \<longleftrightarrow> c < c'\<close>
  using unat_of_char_mod
  by (auto simp: char_of_word_def word_less_nat_alt PAC_Polynomials_Term.less_char_def
      simp flip: less_char_def)

context begin
interpretation llvm_prim_arith_setup .

lemma char_lt_rule:
  \<open>llvm_htriple (char_assn a c ** char_assn a' c') (ll_icmp_ult c c')
    (\<lambda>r. char_assn a c ** char_assn a' c' ** \<upharpoonleft>bool.assn (a < a') r)\<close>
  unfolding char_assn_def char_rel_def
  supply [simp] = pure_def in_br_conv bool.assn_def char_of_word_less
  by vcg

end

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

experiment begin

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

end

end
