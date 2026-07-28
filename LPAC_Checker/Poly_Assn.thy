theory Poly_Assn
  imports Monom_Assn
    BigInt_LLVM.LLVM_CodeGen_Signed
begin

subsection \<open>Refinment Assertion\<close>

abbreviation poly_rel where
  \<open>poly_rel \<equiv> \<langle>monomial_rel\<rangle>list_rel\<close>

abbreviation poly_assn where
  \<open>poly_assn \<equiv> ol_assn monomial_assn\<close>

subsection \<open>Polynomial Equality\<close>

text \<open>The \<open>os_eq\<close> walk one level above \<open>mnml_eq_impl\<close> \<emdash> same ladder as monomial
  equality over \<open>str_eq\<close>. Registered against \<open>(=)\<close> at the polynomial type, which is
  what e.g. \<open>weak_equality_l\<close> (\<open>RETURN (p = q)\<close>) needs for its synthesis.\<close>

definition poly_eq_impl ::
  \<open>(monom_conc \<times> sbin_conc \<times> 1 word) os_list \<Rightarrow> (monom_conc \<times> sbin_conc \<times> 1 word) os_list \<Rightarrow> 1 word llM\<close>
  where \<open>poly_eq_impl \<equiv> os_eq mnml_eq_impl\<close>

lemma poly_eq_impl_simps[llvm_code]:
  \<open>poly_eq_impl p q = (
    if p = null then Mreturn (from_bool (q = null))
    else if q = null then Mreturn 0
    else doM {
      np \<leftarrow> ll_load p; nq \<leftarrow> ll_load q;
      b \<leftarrow> mnml_eq_impl (node.val np) (node.val nq);
      if to_bool b then poly_eq_impl (node.next np) (node.next nq)
      else Mreturn 0 })\<close>
  unfolding poly_eq_impl_def by (rule os_eq.simps)

lemma poly_eq_rule[vcg_rules]:
  \<open>llvm_htriple (poly_assn xs p ** poly_assn ys q) (poly_eq_impl p q)
    (\<lambda>r. poly_assn xs p ** poly_assn ys q ** \<upharpoonleft>bool.assn (xs = ys) r)\<close>
  unfolding poly_eq_impl_def
  by (rule ol_eq_rule[where A=monomial_assn and eqi=mnml_eq_impl, OF mnml_eq_rule])

sepref_register \<open>(=) :: (char list list \<times> int) list \<Rightarrow> (char list list \<times> int) list \<Rightarrow> bool\<close>

lemma poly_eq_hnr[sepref_fr_rules]:
  \<open>(uncurry poly_eq_impl, uncurry (RETURN oo (=)))
    \<in> poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding poly_eq_impl_def
  by (rule ol_eq_hnr[where A=monomial_assn and eqi=mnml_eq_impl, OF mnml_eq_rule])

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

subsection \<open>Free\<close>

lemma mk_free_mk_assn[sepref_frame_free_rules]:
  assumes \<open>MK_FREE A f\<close>
  shows \<open>MK_FREE (\<upharpoonleft>(mk_assn A)) f\<close>
  using assms unfolding MK_FREE_def by simp

lemmas monom_assn_free = ol_assn_free[OF os_assn_free, folded monom_free_def]

 definition sbi_free :: \<open>sbin_conc \<times> 1 word \<Rightarrow> unit llM\<close> where [llvm_code]:
  \<open>sbi_free \<equiv> \<lambda>(a, s). doM { arl_free a; Mreturn () }\<close>

lemmas sbi_free_rule[sepref_frame_free_rules] = sbi_assn_free[folded sbi_free_def]

definition mnml_free :: \<open>monom_conc \<times> sbin_conc \<times> 1 word \<Rightarrow> unit llM\<close> where [llvm_code]:
  \<open>mnml_free \<equiv> \<lambda>(m, c). doM { monom_free m; sbi_free c }\<close>

lemma mnml_assn_free[sepref_frame_free_rules]: \<open>MK_FREE monomial_assn mnml_free\<close>
  unfolding mnml_free_def monom_free_def
  by (rule mk_free_pair[OF monom_assn_free sbi_free_rule])

definition poly_free where \<open>poly_free \<equiv> ol_delete mnml_free\<close>

lemma poly_free_simps[llvm_code]:
  \<open>poly_free p = (if p = null then Mreturn () else doM {
     n \<leftarrow> ll_load p; mnml_free (node.val n); ll_free p; poly_free (node.next n) })\<close>
  unfolding poly_free_def by (rule ol_delete.simps)

lemmas [llvm_pre_simp] = poly_free_def[symmetric]

lemma poly_assn_free[sepref_frame_free_rules]: \<open>MK_FREE poly_assn poly_free\<close>
  unfolding poly_free_def by (rule ol_assn_free[OF mnml_assn_free])

subsection \<open>The Constant-One Polynomial\<close>

text \<open>Producer for the polynomial \<open>1\<close> (one monomial: empty variable list,
  coefficient \<open>1\<close>). Needed by the C import layer: a summand without an explicit
  coefficient polynomial (\<open>poly_ptr = NULL\<close>) denotes a factor of \<open>1\<close>.\<close>

definition poly_one :: \<open>(char list list \<times> int) list nres\<close> where
  \<open>poly_one = RETURN [([], 1)]\<close>

sepref_def poly_one_impl is \<open>uncurry0 poly_one\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  unfolding poly_one_def fold_ol_empty
  by sepref

end
