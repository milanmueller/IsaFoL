(*
  File:         PAC_Checker_Relation.thy
  Author:       Mathias Fleury, Daniela Kaufmann, JKU
  Maintainer:   Mathias Fleury, JKU
*)
theory PAC_Checker_Relation
  imports
    PAC_Checker
    LLVM_Polynomials
begin

text \<open>This theory is essentially rewritten entirely and does not really share anything with
  it's original version. We implement sorting for monomials and define an order on polynomials.\<close>

subsection \<open>Polynomial Sorting\<close>

definition mnl_le :: \<open>char list list \<times> int \<Rightarrow> char list list \<times> int \<Rightarrow> bool\<close> where
  \<open>mnl_le \<equiv> \<lambda>(m, _) (m', _). m \<le> m'\<close>

(*
definition merge_mnls :: \<open>(char list list \<times> int) list \<Rightarrow> _ \<Rightarrow> _\<close> where
  \<open>merge_mnls = merge mnl_le\<close>

definition msort_mnls :: \<open>(char list list \<times> int) list \<Rightarrow> _\<close> where
  \<open>msort_mnls = msort_alt mnl_le\<close>

sepref_register mnl_le merge_mnls msort_mnls
*)
sepref_def mnl_le_impl is \<open>uncurry (RETURN oo mnl_le)\<close>
  :: \<open>monomial_assn\<^sup>k *\<^sub>a monomial_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding mnl_le_def
  by sepref

text \<open>Correctness at the abstract level: multiset preservation and sortedness w.r.t.
  the (weak) monomial order on pairs \<emdash> the ingredients for \<open>sort_poly_spec\<close>.\<close>
(*
lemma msort_mnls_mset[simp]: \<open>mset (msort_mnls xs) = mset xs\<close>
  unfolding msort_mnls_def by simp

lemma msort_mnls_sorted: \<open>sorted_wrt mnl_le (msort_mnls xs)\<close>
  unfolding msort_mnls_def
  by (rule msort_alt_sorted) (auto simp: mnl_le_def intro!: transpI)
*)
text \<open>String/monomial relations, assertions and equality (replacing the AFP's
  \<open>eq_string_monom_hnr\<close>) have moved to \<open>Monom_Assn\<close>.\<close>

definition term_order_rel' where
  [simp]: \<open>term_order_rel' x y = ((x, y) \<in> term_order_rel)\<close>

lemma term_order_rel[def_pat_rules]:
  \<open>(\<in>)$(x,y)$term_order_rel \<equiv> term_order_rel'$x$y\<close>
  by auto

lemma term_order_rel_alt_def:
  \<open>term_order_rel = lexord (p2rel char.lexordp)\<close>
  unfolding var_order_rel_def p2rel_def char.lexordp_conv_lexord
  apply (rule arg_cong[where f=lexord])
  by (auto simp: p2rel_def char.lexordp_conv_lexord less_than_char_def)

lemma term_order_rel'_alt_def_lexord:
    \<open>term_order_rel' x y = ord_class.lexordp x y\<close> and
  term_order_rel'_alt_def:
    \<open>term_order_rel' x y \<longleftrightarrow> x < y\<close>
proof -
  show
    \<open>term_order_rel' x y = ord_class.lexordp x y\<close>
    \<open>term_order_rel' x y \<longleftrightarrow> x < y\<close>
    by (auto simp: lexordp_conv_lexord less_eq_list_def
         less_list_def lexordp_def var_order_rel_def
         rel2p_def term_order_rel_alt_def p2rel_def less_char_inst)
qed

definition string2_rel :: \<open>(string \<times> string) set\<close> where
  \<open>string2_rel \<equiv> \<langle>Id\<rangle>list_rel\<close>

lemma char_of_word_less_iff: \<open>char_of_word a < char_of_word b \<longleftrightarrow> (a :: 8 word) < b\<close>
  using unat_of_char_mod
  by (auto simp: char_of_word_def word_less_nat_alt less_char_inst less_char_def)

lemma lexord_char_rel_mono_iff:
  assumes \<open>(xs, xs') \<in> \<langle>char_rel\<rangle>list_rel\<close> and
    \<open>(ys, ys') \<in> \<langle>char_rel\<rangle>list_rel\<close>
  shows \<open>(xs', ys') \<in> lexord {(x, y). x < y} \<longleftrightarrow> (xs, ys) \<in> lexord {(x, y). x < y}\<close>
  using assms
proof (induction xs arbitrary: ys xs' ys')
  case Nil
  then show ?case
    by (cases ys; cases xs'; cases ys')
      (auto simp: list_rel_split_right_iff list_rel_split_left_iff)
next
  case (Cons x xs)
  then show ?case
    apply (cases ys; cases xs'; cases ys') 
    apply (auto simp: list_rel_split_right_iff list_rel_split_left_iff
        in_br_conv char_rel_def char_of_word_less_iff char_nat_rel_def
        char_nat_rel_simps(3) less_char_def less_char_inst 
        unat.rel_def unat_arith_simps(2) unat_rel_def)
    using char_of_nat_inj by auto    
qed

(* lemma list_rel_list_rel_order_iff:
 *   assumes \<open>(a, b) \<in> \<langle>string_rel\<rangle>list_rel\<close> \<open>(a', b') \<in> \<langle>string_rel\<rangle>list_rel\<close>
 *   shows \<open>a < a' \<longleftrightarrow> b < b'\<close>
 * proof
 *   have H: \<open>(a, b) \<in> \<langle>string_rel\<rangle>list_rel \<Longrightarrow>
 *        (a, cs) \<in> \<langle>string_rel\<rangle>list_rel \<Longrightarrow> b = cs\<close> for cs
 *      using single_valued_monom_rel' IS_RIGHT_UNIQUE_string_rel
 *      unfolding string2_rel_def
 *      by (subst (asm)list_rel_sv_iff[symmetric])
 *        (auto simp: single_valued_def)
 *   assume \<open>a < a'\<close>
 *   then consider
 *     u u' where \<open>a' = a @ u # u'\<close> |
 *     u aa v w aaa where \<open>a = u @ aa # v\<close> \<open>a' = u @ aaa # w\<close> \<open>aa < aaa\<close>
 *     by (subst (asm) less_list_def)
 *      (auto simp: lexord_def List.lexordp_def
 *       list_rel_append1 list_rel_split_right_iff)
 *   then show \<open>b < b'\<close>
 *   proof cases
 *     case 1
 *     then show \<open>b < b'\<close>
 *       using assms
 *       by (subst less_list_def)
 *         (auto simp: lexord_def List.lexordp_def
 *         list_rel_append1 list_rel_split_right_iff dest: H)
 *   next
 *     case 2
 *     then obtain u' aa' v' w' aaa' where
 *        \<open>b = u' @ aa' # v'\<close> \<open>b' = u' @ aaa' # w'\<close>
 *        \<open>(aa, aa') \<in> string_rel\<close>
 *        \<open>(aaa, aaa') \<in> string_rel\<close>
 *       using assms
 *       by (smt (verit) list_rel_append1 list_rel_split_right_iff single_valued_def single_valued_monom_rel)
 *     have aa_lex: \<open>(aa, aaa) \<in> lexord {(x, y). x < y}\<close>
 *       using \<open>aa < aaa\<close> unfolding less_list_def lexordp_conv_lexord
 *       using List.lexordp_def by blast
 *     have \<open>aa' < aaa'\<close>
 *       unfolding less_list_def lexordp_conv_lexord
 *       using lexord_char_rel_mono_iff[OF \<open>(aa, aa') \<in> string_rel\<close>[unfolded string_rel_def]
 *           \<open>(aaa, aaa') \<in> string_rel\<close>[unfolded string_rel_def]] aa_lex
 *       using List.lexordp_def by blast
 *     then show \<open>b < b'\<close>
 *       using \<open>b = u' @ aa' # v'\<close> \<open>b' = u' @ aaa' # w'\<close>
 *       by (subst less_list_def)
 *         (fastforce simp: lexord_def List.lexordp_def
 *         list_rel_append1 list_rel_split_right_iff)
 *   qed
 * next
 *   have H: \<open>(a, b) \<in> \<langle>string_rel\<rangle>list_rel \<Longrightarrow>
 *        (a', b) \<in> \<langle>string_rel\<rangle>list_rel \<Longrightarrow> a = a'\<close> for a a' b
 *      using single_valued_monom_rel'
 *      by (auto simp: single_valued_def IS_LEFT_UNIQUE_def
 *        simp flip: inv_list_rel_eq)
 *   assume \<open>b < b'\<close>
 *   then consider
 *     u u' where \<open>b' = b @ u # u'\<close> |
 *     u aa v w aaa where \<open>b = u @ aa # v\<close> \<open>b' = u @ aaa # w\<close> \<open>aa < aaa\<close>
 *     by (subst (asm) less_list_def)
 *      (auto simp: lexord_def List.lexordp_def
 *       list_rel_append1 list_rel_split_right_iff)
 *   then show \<open>a < a'\<close>
 *   proof cases
 *     case 1
 *     then show \<open>a < a'\<close>
 *       using assms
 *       by (subst less_list_def)
 *         (auto simp: lexord_def List.lexordp_def
 *         list_rel_append2 list_rel_split_left_iff dest: H)
 *   next
 *     case 2
 *     then obtain u' aa' v' w' aaa' where
 *        \<open>a = u' @ aa' # v'\<close> \<open>a' = u' @ aaa' # w'\<close>
 *        \<open>(aa', aa) \<in> string_rel\<close>
 *        \<open>(aaa', aaa) \<in> string_rel\<close>
 *       using assms
 *       by (auto simp: lexord_def List.lexordp_def
 *         list_rel_append2 list_rel_split_left_iff dest: H)
 *     have aa_lex: \<open>(aa, aaa) \<in> lexord {(x, y). x < y}\<close>
 *       using \<open>aa < aaa\<close> unfolding less_list_def lexordp_conv_lexord
 *       using List.lexordp_def by blast
 *     have \<open>aa' < aaa'\<close>
 *       unfolding less_list_def lexordp_conv_lexord
 *       using lexord_char_rel_mono_iff[OF \<open>(aa', aa) \<in> string_rel\<close>[unfolded string_rel_def]
 *           \<open>(aaa', aaa) \<in> string_rel\<close>[unfolded string_rel_def]] aa_lex
 *       using List.lexordp_def by blast
 *     then show \<open>a < a'\<close>
 *       using \<open>a = u' @ aa' # v'\<close> \<open>a' = u' @ aaa' # w'\<close>
 *       by (subst less_list_def)
 *         (fastforce simp: lexord_def List.lexordp_def
 *         list_rel_append1 list_rel_split_right_iff)
 *   qed
 * qed *)

end
