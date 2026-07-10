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

subsection \<open>Regression Test\<close>

experiment begin

  definition monom_eq_test :: \<open>char list list \<Rightarrow> char list list \<Rightarrow> bool\<close> where
    \<open>monom_eq_test xs ys = (xs = ys)\<close>

  sepref_def monom_eq_test_impl is \<open>uncurry (RETURN oo monom_eq_test)\<close>
    :: \<open>monom_assn\<^sup>k *\<^sub>a monom_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
    unfolding monom_eq_test_def by sepref

  text \<open>Exercises the whole first-order code path
    (\<open>monom_eq_impl_simps\<close>/\<open>str_eq_simps\<close>/\<open>ll_icmp_eq\<close>).\<close>
  export_llvm monom_eq_test_impl

  definition monom_lt_test :: \<open>char list list \<Rightarrow> char list list \<Rightarrow> bool\<close> where
    \<open>monom_lt_test xs ys = (xs < ys)\<close>

  sepref_def monom_lt_test_impl is \<open>uncurry (RETURN oo monom_lt_test)\<close>
    :: \<open>monom_assn\<^sup>k *\<^sub>a monom_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
    unfolding monom_lt_test_def by sepref

  text \<open>Exercises the nested first-order code path
    (\<open>monom_less_impl_simps\<close>/\<open>strl_lt_simps\<close>/\<open>str_eq_simps\<close>/\<open>ll_icmp_ult\<close>/\<open>ll_icmp_eq\<close>).\<close>
  export_llvm monom_lt_test_impl

end

end
