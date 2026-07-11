theory Poly_Assn
  imports Monom_Assn
begin

subsection \<open>Refinment Assertion\<close>

abbreviation poly_rel where
  \<open>poly_rel \<equiv> \<langle>monomial_rel\<rangle>list_rel\<close>

abbreviation poly_assn where
  \<open>poly_assn \<equiv> ol_assn monomial_assn\<close>

subsection \<open>Polynomial Copy\<close>

text \<open>Deep copy of a polynomial: the \<open>ol_copy\<close> walk one level above the monomial-pair
  copy \<open>mnml_copy_impl\<close> \<emdash> the same ladder as \<open>monom_copy_impl\<close> over \<open>strl_copy\<close>.
  Registered against \<open>COPY\<close> at \<open>poly_assn\<close>: this is what makes keep-mode wrappers of
  consuming polynomial operations possible (copy at entry, run the destructive
  implementation on the copy), e.g. \<open>\<lambda>(p, q). add_poly_l (COPY p, COPY q)\<close>.\<close>

definition poly_copy_impl ::
  \<open>(monom_conc \<times> sbin_conc \<times> 1 word) os_list \<Rightarrow> (monom_conc \<times> sbin_conc \<times> 1 word) os_list llM\<close>
  where \<open>poly_copy_impl \<equiv> ol_copy mnml_copy_impl\<close>

lemma poly_copy_impl_simps[llvm_code]:
  \<open>poly_copy_impl p = (if p = null then Mreturn null else doM {
      n \<leftarrow> ll_load p;
      c \<leftarrow> mnml_copy_impl (node.val n);
      t \<leftarrow> poly_copy_impl (node.next n);
      os_prepend c t
    })\<close>
  unfolding poly_copy_impl_def by (rule ol_copy.simps)

lemma poly_copy_rule[vcg_rules]:
  \<open>llvm_htriple (poly_assn xs p) (poly_copy_impl p)
    (\<lambda>r. poly_assn xs p ** poly_assn xs r)\<close>
  unfolding poly_copy_impl_def
  by (rule ol_copy_rule[where A=monomial_assn and cp=mnml_copy_impl, OF mnml_copy_rule])

lemma poly_copy_hnr[sepref_fr_rules]:
  \<open>(poly_copy_impl, RETURN o COPY) \<in> poly_assn\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  unfolding poly_copy_impl_def
  by (rule ol_copy_hnr[where A=monomial_assn and cp=mnml_copy_impl, OF mnml_copy_rule])

end
