section \<open>Monomials as Owning Lists of Strings\<close>
theory Monom_Assn
  imports String_Assn
begin

text \<open>Monomials (\<open>char list list\<close>) are represented as owning lists of strings: the outer
  spine owns the inner \<open>strl_assn\<close> strings (impure elements), cf. \<open>IICF_Owning_List\<close>.
  This theory also provides monomial equality by instantiating the generic \<open>os_eq\<close>
  template one level above \<open>str_eq\<close> \<emdash> the outer instance needs no purity of the element
  assertion, only \<open>str_eq_rule\<close> as the element-equality premise.\<close>

subsection \<open>Relations and Assertions\<close>

abbreviation monom_rel where
  \<open>monom_rel \<equiv> \<langle>string_rel\<rangle>list_rel\<close>

abbreviation monom_assn where
  \<open>monom_assn \<equiv> ol_assn strl_assn\<close>

lemma single_valued_string_rel:
  \<open>single_valued string_rel\<close>
  unfolding string_rel_def
  by (rule list_rel_sv) (auto simp: single_valued_def char_rel_def br_def)

lemma IS_LEFT_UNIQUE_string_rel:
  \<open>IS_LEFT_UNIQUE string_rel\<close>
  unfolding IS_LEFT_UNIQUE_def string_rel_def inv_list_rel_eq
  apply (rule list_rel_sv)
  apply (auto simp: single_valued_def char_rel_def br_def char_of_word_def
       word_unat_eq_iff)
  by (simp add: unat_of_char_mod)

lemmas IS_RIGHT_UNIQUE_string_rel = single_valued_string_rel

lemma single_valued_monom_rel: \<open>single_valued monom_rel\<close>
  by (rule list_rel_sv) (rule single_valued_string_rel)

lemma single_valued_monom_rel': \<open>IS_LEFT_UNIQUE monom_rel\<close>
  unfolding IS_LEFT_UNIQUE_def inv_list_rel_eq
  by (rule list_rel_sv) (rule IS_LEFT_UNIQUE_string_rel[unfolded IS_LEFT_UNIQUE_def])

lemma [safe_constraint_rules]:
  \<open>Sepref_Constraints.CONSTRAINT single_valued string_rel\<close>
  \<open>Sepref_Constraints.CONSTRAINT IS_LEFT_UNIQUE string_rel\<close>
  using single_valued_string_rel IS_LEFT_UNIQUE_string_rel
  by (auto simp: CONSTRAINT_def)

subsection \<open>Monomial Equality\<close>

text \<open>Replaces the AFP's \<open>eq_string_monom_hnr\<close>, whose proof (concrete \<open>(=)\<close> implements
  abstract \<open>(=)\<close>) relied on \<open>monom_assn\<close> being pure in Imperative-HOL. Here the concrete
  values are pointers, so equality is implemented by the \<open>os_eq\<close> walk with \<open>str_eq\<close> as
  element comparison; first-order recursion equations are derived for code export.\<close>

definition monom_eq_impl :: \<open>8 word os_list os_list \<Rightarrow> 8 word os_list os_list \<Rightarrow> 1 word llM\<close>
  where \<open>monom_eq_impl \<equiv> os_eq str_eq\<close>

lemma monom_eq_impl_simps[llvm_code]:
  \<open>monom_eq_impl p q = (
    if p = null then Mreturn (from_bool (q = null))
    else if q = null then Mreturn 0
    else doM {
      np \<leftarrow> ll_load p; nq \<leftarrow> ll_load q;
      b \<leftarrow> str_eq (node.val np) (node.val nq);
      if to_bool b then monom_eq_impl (node.next np) (node.next nq)
      else Mreturn 0 })\<close>
  unfolding monom_eq_impl_def by (rule os_eq.simps)

lemma monom_eq_rule[vcg_rules]:
  \<open>llvm_htriple (monom_assn xs p ** monom_assn ys q) (monom_eq_impl p q)
    (\<lambda>r. monom_assn xs p ** monom_assn ys q ** \<upharpoonleft>bool.assn (xs = ys) r)\<close>
  unfolding monom_eq_impl_def
  by (rule ol_eq_rule[where A=strl_assn and eqi=str_eq, OF str_eq_rule])

sepref_register \<open>(=) :: char list list \<Rightarrow> char list list \<Rightarrow> bool\<close>

lemma monom_eq_hnr[sepref_fr_rules]:
  \<open>(uncurry monom_eq_impl, uncurry (RETURN oo (=)))
    \<in> monom_assn\<^sup>k *\<^sub>a monom_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding monom_eq_impl_def
  by (rule ol_eq_hnr[where A=strl_assn and eqi=str_eq, OF str_eq_rule])

subsection \<open>Monomial Order\<close>

text \<open>The lexicographic order on monomials (\<open>char list list\<close>) is obtained by instantiating
  the generic \<open>os_less\<close> template one level above \<open>strl_lt\<close>: the element \<^emph>\<open>strict less\<close> is
  the string order \<open>strl_lt\<close> and the element \<^emph>\<open>equality\<close> is \<open>str_eq\<close>. No purity of the
  element assertion is needed \<emdash> only \<open>strl_lt_rule\<close>/\<open>str_eq_rule\<close> as the element premises,
  exactly as monomial equality reuses \<open>str_eq_rule\<close>. The abstract \<open>(<)\<close> here is the
  \<open>list :: linorder\<close> order over the (already \<open>linorder\<close>) strings.\<close>

definition monom_less_impl :: \<open>8 word os_list os_list \<Rightarrow> 8 word os_list os_list \<Rightarrow> 1 word llM\<close>
  where \<open>monom_less_impl \<equiv> os_less strl_lt str_eq\<close>

lemma monom_less_impl_simps[llvm_code]:
  \<open>monom_less_impl p q = (
    if q = null then Mreturn 0
    else if p = null then Mreturn 1
    else doM {
      np \<leftarrow> ll_load p; nq \<leftarrow> ll_load q;
      b \<leftarrow> strl_lt (node.val np) (node.val nq);
      if to_bool b then Mreturn 1
      else doM {
        e \<leftarrow> str_eq (node.val np) (node.val nq);
        if to_bool e then monom_less_impl (node.next np) (node.next nq)
        else Mreturn 0 } })\<close>
  unfolding monom_less_impl_def by (rule os_less.simps)

lemma monom_less_rule[vcg_rules]:
  \<open>llvm_htriple (monom_assn xs p ** monom_assn ys q) (monom_less_impl p q)
    (\<lambda>r. monom_assn xs p ** monom_assn ys q ** \<upharpoonleft>bool.assn (xs < ys) r)\<close>
  unfolding monom_less_impl_def
  by (rule ol_less_rule[where A=strl_assn and lti=strl_lt and eqi=str_eq,
        OF strl_lt_rule str_eq_rule])

sepref_register \<open>(<) :: char list list \<Rightarrow> char list list \<Rightarrow> bool\<close>

lemma monom_less_hnr[sepref_fr_rules]:
  \<open>(uncurry monom_less_impl, uncurry (RETURN oo (<)))
    \<in> monom_assn\<^sup>k *\<^sub>a monom_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding monom_less_impl_def
  by (rule ol_less_hnr[where A=strl_assn and lti=strl_lt and eqi=str_eq,
        OF strl_lt_rule str_eq_rule])

text \<open>Like with strings, we are lazy and use an additional negation to implement \<le> (TODO: properly implement)\<close>

sepref_def monom_le_impl is \<open>uncurry (RETURN oo ls_le)\<close>
  :: \<open>monom_assn\<^sup>k *\<^sub>a monom_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding ls_le_def 
  by sepref

sepref_register \<open>(\<le>) :: char list list \<Rightarrow> char list list \<Rightarrow> bool\<close>
lemma strl_le_hnr[sepref_fr_rules]:
  \<open>(uncurry monom_le_impl, uncurry (RETURN oo (\<le>)))
  \<in> monom_assn\<^sup>k *\<^sub>a monom_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  using monom_le_impl.refine unfolding ls_le_def le_by_lt_str .

lemma monom_le_rule[vcg_rules]:
  \<open>llvm_htriple (monom_assn xs p ** monom_assn ys q) (monom_le_impl p q)
    (\<lambda>r. monom_assn xs p ** monom_assn ys q ** \<upharpoonleft>bool.assn (xs \<le> ys) r)\<close>
  unfolding monom_le_impl_def 
  supply [simp] = linorder_not_less
  by vcg

subsection \<open>Monomial Copy\<close>

text \<open>Deep copy of a monomial: the \<open>ol_copy\<close> walk one level above \<open>strl_copy\<close>, with the
  string copy as element copy \<emdash> same nesting as \<open>monom_eq_impl\<close>/\<open>monom_less_impl\<close>.
  Registered against \<open>COPY\<close>, so sepref can duplicate monomials whenever abstract code
  violates linearity (an owned monomial used twice).\<close>

definition monom_copy_impl :: \<open>8 word os_list os_list \<Rightarrow> 8 word os_list os_list llM\<close>
  where \<open>monom_copy_impl \<equiv> ol_copy strl_copy\<close>

lemma monom_copy_impl_simps[llvm_code]:
  \<open>monom_copy_impl p = (if p = null then Mreturn null else doM {
      n \<leftarrow> ll_load p;
      c \<leftarrow> strl_copy (node.val n);
      t \<leftarrow> monom_copy_impl (node.next n);
      os_prepend c t
    })\<close>
  unfolding monom_copy_impl_def by (rule ol_copy.simps)

lemma monom_copy_rule[vcg_rules]:
  \<open>llvm_htriple (monom_assn xs p) (monom_copy_impl p)
    (\<lambda>r. monom_assn xs p ** monom_assn xs r)\<close>
  unfolding monom_copy_impl_def
  by (rule ol_copy_rule[where A=strl_assn and cp=strl_copy, OF strl_copy_rule])

lemma monom_copy_hnr[sepref_fr_rules]:
  \<open>(monom_copy_impl, RETURN o COPY) \<in> monom_assn\<^sup>k \<rightarrow>\<^sub>a monom_assn\<close>
  unfolding monom_copy_impl_def
  by (rule ol_copy_hnr[where A=strl_assn and cp=strl_copy, OF strl_copy_rule])

subsection \<open>Monomial Free\<close>

text \<open>Sepref inserts \<open>ol_delete os_delete\<close> as the free function for dropped monomials
  (via the conditional \<open>MK_FREE\<close> rules), so synthesized code can contain it. The
  template is higher-order in the element free, so code export needs a first-order
  specialization; the \<open>[llvm_pre_simp]\<close> fold rewrites synthesized code to use it
  (cf. \<open>ll_not1_inline\<close> in the library).\<close>

definition monom_free :: \<open>8 word os_list os_list \<Rightarrow> unit llM\<close> where
  \<open>monom_free \<equiv> ol_delete os_delete\<close>

lemma monom_free_simps[llvm_code]:
  \<open>monom_free p = (if p = null then Mreturn () else doM {
      n \<leftarrow> ll_load p;
      os_delete (node.val n);
      ll_free p;
      monom_free (node.next n)
    })\<close>
  unfolding monom_free_def by (rule ol_delete.simps)

lemmas [llvm_pre_simp] = monom_free_def[symmetric]

subsection \<open>Monomial Variable Sorting\<close>

text \<open>Sorting the variables of a monomial, by sepref synthesis at \<open>monom_assn\<close> with the
  string order as comparator. \<open>merge_vars\<close>/\<open>msort_vars\<close> are proper constants (sepref
  rejects partial applications like \<open>merge (\<le>)\<close> as rule heads). This replaces the role
  of the functional \<open>msort_monoms_impl\<close> in \<open>PAC_Checker_Init\<close>.\<close>

definition merge_vars :: \<open>char list list \<Rightarrow> char list list \<Rightarrow> char list list\<close> where
  \<open>merge_vars = merge (\<le>)\<close>

definition msort_vars :: \<open>char list list \<Rightarrow> char list list\<close> where
  \<open>msort_vars = msort_alt (\<le>)\<close>

sepref_register merge_vars msort_vars

sepref_def monom_merge_impl is \<open>uncurry (RETURN oo merge_vars)\<close>
  :: \<open>monom_assn\<^sup>d *\<^sub>a monom_assn\<^sup>d \<rightarrow>\<^sub>a monom_assn\<close>
  unfolding merge_vars_def merge_RECT
  by sepref

sepref_def monom_split_impl is \<open>RETURN o alt_split\<close>
  :: \<open>monom_assn\<^sup>d \<rightarrow>\<^sub>a monom_assn \<times>\<^sub>a monom_assn\<close>
  unfolding alt_split_RECT_ol
  by sepref

sepref_def monom_msort_impl is \<open>RETURN o msort_vars\<close>
  :: \<open>monom_assn\<^sup>d \<rightarrow>\<^sub>a monom_assn\<close>
  unfolding msort_vars_def msort_alt_RECT merge_vars_def[symmetric]
  by sepref

text \<open>Correctness at the abstract level, for composing against sorting specs.\<close>

lemma msort_vars_mset[simp]: \<open>mset (msort_vars xs) = mset xs\<close>
  unfolding msort_vars_def by simp

lemma msort_vars_sorted: \<open>sorted_wrt (\<le>) (msort_vars xs)\<close>
  unfolding msort_vars_def
  by (rule msort_alt_sorted) (auto intro: transpI)

subsection \<open>Tests\<close>

experiment begin

  definition monom_eq_test :: \<open>char list list \<Rightarrow> char list list \<Rightarrow> bool\<close> where
    \<open>monom_eq_test xs ys = (xs = ys)\<close>

  sepref_def monom_eq_test_impl is \<open>uncurry (RETURN oo monom_eq_test)\<close>
    :: \<open>monom_assn\<^sup>k *\<^sub>a monom_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
    unfolding monom_eq_test_def by sepref

  definition monom_lt_test :: \<open>char list list \<Rightarrow> char list list \<Rightarrow> bool\<close> where
    \<open>monom_lt_test xs ys = (xs < ys)\<close>

  sepref_def monom_lt_test_impl is \<open>uncurry (RETURN oo monom_lt_test)\<close>
    :: \<open>monom_assn\<^sup>k *\<^sub>a monom_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
    unfolding monom_lt_test_def by sepref

  definition monom_dup_test :: \<open>char list list \<Rightarrow> char list list \<times> char list list\<close> where
    \<open>monom_dup_test xs = (xs, xs)\<close>

  sepref_def monom_dup_test_impl is \<open>RETURN o monom_dup_test\<close>
    :: \<open>monom_assn\<^sup>d \<rightarrow>\<^sub>a monom_assn \<times>\<^sub>a monom_assn\<close>
    unfolding monom_dup_test_def
    by sepref

end

end
