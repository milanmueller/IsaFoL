theory Char_Assn 
  imports Isabelle_LLVM.IICF PAC_Polynomials_Term
begin

text \<open>We need to tell sepref how to relate @{typ \<open>char\<close>} and @{typ \<open>8 word\<close>}\<close>

definition char_of_word :: \<open>8 word \<Rightarrow> char\<close> where
  \<open>char_of_word \<equiv> char_of \<circ> unat\<close>

definition char_rel :: \<open>(8 word \<times> char) set\<close> where
  \<open>char_rel \<equiv> br char_of_word (\<lambda>_. True)\<close>

definition \<open>char_assn \<equiv> pure char_rel\<close>
lemma char_assn_pure[safe_constraint_rules]: \<open>is_pure char_assn\<close>
  unfolding char_assn_def by simp

interpretation char_word: standard_opr_abstraction
  "char_of_word :: 8 word \<Rightarrow> char"
  "(\<lambda>_. True)"
  "(\<lambda>_ _ _. True)"
  "(\<lambda>_ _ _ _. True)"
  "(\<lambda>_ _. True)"
  by standard simp

lemma unat_of_char_mod: \<open>unat (a :: 8 word) mod 256 = unat a\<close>
proof -
  have \<open>unat a < 256\<close>
    by (rule less_le_trans[OF unat_lt2p]) simp
  then show ?thesis
    by simp
qed

lemma char_eq_is_cmp_op: "char_word.is_cmp_op ll_icmp_eq (=) (=)"
  apply (rule char_word.is_cmp_opI)
  unfolding ll_icmp_eq_def op_lift_cmp_def char_of_word_def
  apply (simp add: from_bool_lint_conv word_to_lint_eq)
  using unat_of_char_mod by auto

lemma char_ne_is_cmp_op: \<open>char_word.is_cmp_op ll_icmp_ne (\<noteq>) (\<noteq>)\<close>
  apply (rule char_word.is_cmp_opI)
  unfolding ll_icmp_ne_def op_lift_cmp_def char_of_word_def
  apply (simp add: from_bool_lint_conv word_to_lint_eq)
  using unat_of_char_mod by auto

instantiation char :: linorder
begin
  definition less_char where [symmetric, simp]: "less_char = PAC_Polynomials_Term.less_char"
  definition less_eq_char where [symmetric, simp]: "less_eq_char = PAC_Polynomials_Term.less_eq_char"
instance
  apply standard
  using char.linorder_axioms
  by (auto simp: class.linorder_def class.order_def class.preorder_def
       less_eq_char_def less_than_char_def class.order_axioms_def
       class.linorder_axioms_def p2rel_def less_char_def)
end

lemma char_lt_is_cmp_op: "char_word.is_cmp_op ll_icmp_ult (<) (<)"
  apply (rule char_word.is_cmp_opI)
  unfolding ll_icmp_ult_def op_lift_cmp_def char_of_word_def
  apply (simp add: from_bool_lint_conv word_to_lint_ult)
  using unat_of_char_mod
  by (auto simp: word_less_nat_alt PAC_Polynomials_Term.less_char_def 
           simp flip: less_char_def) 

lemma char_le_is_cmp_op: "char_word.is_cmp_op ll_icmp_ule (\<le>) (\<le>)"
  apply (rule char_word.is_cmp_opI)
  unfolding ll_icmp_ule_def op_lift_cmp_def char_of_word_def
  apply (simp add: from_bool_lint_conv word_to_lint_ule)
  using unat_of_char_mod 
  by (auto simp: word_le_nat_alt PAC_Polynomials_Term.less_eq_char_def 
           simp flip: less_eq_char_def)

sepref_register
  "(=) :: char \<Rightarrow> _"
  "(<) :: char \<Rightarrow> _"
  "(\<le>) :: char \<Rightarrow> _"

sepref_register op_neq_char: "op_neq :: char \<Rightarrow> _"

lemmas char_eq_hnr[sepref_fr_rules] =
  char_eq_is_cmp_op[THEN char_word.hn_cmp_op,
    unfolded char_word.assn_is_rel bool.assn_is_rel char_word.rel_def,
    folded bool1_rel_def char_rel_def char_assn_def]

lemmas char_ne_hnr[sepref_fr_rules] =
  char_ne_is_cmp_op[THEN char_word.hn_cmp_op,
    unfolded char_word.assn_is_rel bool.assn_is_rel char_word.rel_def,
    folded bool1_rel_def op_neq_def char_rel_def char_assn_def]

lemmas char_lt_hnr[sepref_fr_rules] =
  char_lt_is_cmp_op[THEN char_word.hn_cmp_op,
    unfolded char_word.assn_is_rel bool.assn_is_rel char_word.rel_def,
    folded bool1_rel_def char_rel_def char_assn_def char_rel_def]

lemmas char_le_hnr[sepref_fr_rules] =
  char_le_is_cmp_op[THEN char_word.hn_cmp_op,
    unfolded char_word.assn_is_rel bool.assn_is_rel char_word.rel_def,
    folded bool1_rel_def char_rel_def char_assn_def]

lemma char_of_word_hnr[sepref_fr_rules]:
  \<open>(Mreturn, RETURN o char_of_word) \<in> (hn_val word_rel)\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  unfolding char_assn_def 
  apply (intro hfrefI hn_refineI; vcg)
  apply (auto simp: in_br_conv ENTAILS_def entails_def char_rel_def char_of_word_def sep_algebra_simps br_def)
  by (smt (verit, best) Misc.IdD case_prodI fri_basic_extract_simps(1) import_param_3(2) mem_Collect_eq pure_app_eq)

lemma char_assn_mk_free[sepref_frame_free_rules]:
  \<open>MK_FREE char_assn (\<lambda>_. Mreturn ())\<close>
  unfolding char_assn_def
  by (rule mk_free_pure)

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

lemma char_of_word_less: \<open>char_of_word c < char_of_word c' \<longleftrightarrow> c < c'\<close>
  using unat_of_char_mod
  by (auto simp: char_of_word_def word_less_nat_alt PAC_Polynomials_Term.less_char_def
      simp flip: less_char_def)

context begin
interpretation llvm_prim_arith_setup .

lemma char_eq_rule:
  \<open>llvm_htriple (char_assn a c ** char_assn a' c') (ll_icmp_eq c c')
    (\<lambda>r. char_assn a c ** char_assn a' c' ** \<upharpoonleft>bool.assn (a = a') r)\<close>
  unfolding char_assn_def char_rel_def
  supply [simp] = pure_def in_br_conv bool.assn_def char_of_word_inj
  by vcg

lemma char_lt_rule:
  \<open>llvm_htriple (char_assn a c ** char_assn a' c') (ll_icmp_ult c c')
    (\<lambda>r. char_assn a c ** char_assn a' c' ** \<upharpoonleft>bool.assn (a < a') r)\<close>
  unfolding char_assn_def char_rel_def
  supply [simp] = pure_def in_br_conv bool.assn_def char_of_word_less
  by vcg

end

(* This is essentially just testing *)
sepref_definition char_eq_impl is \<open>uncurry (RETURN oo (=))\<close> 
  :: \<open>char_assn\<^sup>k *\<^sub>a char_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

sepref_definition char_ne_impl is \<open>uncurry (RETURN oo (\<noteq>))\<close> 
  :: \<open>char_assn\<^sup>k *\<^sub>a char_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

sepref_definition char_lt_impl is \<open>uncurry (RETURN oo (<))\<close> 
  :: \<open>char_assn\<^sup>k *\<^sub>a char_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

sepref_definition char_le_impl is \<open>uncurry (RETURN oo (\<le>))\<close> 
  :: \<open>char_assn\<^sup>k *\<^sub>a char_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

end
