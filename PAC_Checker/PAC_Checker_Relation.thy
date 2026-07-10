(*
  File:         PAC_Checker_Relation.thy
  Author:       Mathias Fleury, Daniela Kaufmann, JKU
  Maintainer:   Mathias Fleury, JKU
*)
theory PAC_Checker_Relation
  imports 
    PAC_Checker 
    WB_Sort 
    "Native_Word.Uint64" 
    "Native_Word.Uint32" 
    Collections.HashCode
    Monom_Assn
    BigInt_LLVM.LLVM_CodeGen_Signed
begin

section \<open>Various Refinement Relations\<close>

text \<open>When writing this, it was not possible to share the definition with the IsaSAT version.\<close>
definition uint64_nat_rel :: "(uint64 \<times> nat) set" where
 \<open>uint64_nat_rel = br nat_of_uint64 (\<lambda>_. True)\<close>

abbreviation uint64_nat_assn where
  \<open>uint64_nat_assn \<equiv> pure uint64_nat_rel\<close>

instantiation uint32 :: hashable
begin
definition hashcode_uint32 :: \<open>uint32 \<Rightarrow> uint32\<close> where
  \<open>hashcode_uint32 n = n\<close>

definition def_hashmap_size_uint32 :: \<open>uint32 itself \<Rightarrow> nat\<close> where
  \<open>def_hashmap_size_uint32 = (\<lambda>_. 16)\<close>
  \<comment> \<open>same as @{typ nat}\<close>
instance
  by standard (simp add: def_hashmap_size_uint32_def)
end

instantiation uint64 :: hashable
begin

context
  includes bit_operations_syntax
begin

definition hashcode_uint64 :: \<open>uint64 \<Rightarrow> uint32\<close> where
  \<open>hashcode_uint64 n = (uint32_of_nat (nat_of_uint64 ((n) AND ((2 :: uint64)^32 -1))))\<close>

end

definition def_hashmap_size_uint64 :: \<open>uint64 itself \<Rightarrow> nat\<close> where
  \<open>def_hashmap_size_uint64 = (\<lambda>_. 16)\<close>
  \<comment> \<open>same as @{typ nat}\<close>
instance
  by standard (simp add: def_hashmap_size_uint64_def)
end

lemma word_nat_of_uint64_Rep_inject[simp]: \<open>nat_of_uint64 ai = nat_of_uint64 bi \<longleftrightarrow> ai = bi\<close>
  by transfer (simp add: word_unat_eq_iff)

(* This will not work in llvm
instance uint64 :: heap
  by standard (auto simp: inj_def exI[of _ nat_of_uint64])
*)

instance uint64 :: semiring_numeral
  by standard

lemma nat_of_uint64_012[simp]: \<open>nat_of_uint64 0 = 0\<close> \<open>nat_of_uint64 2 = 2\<close> \<open>nat_of_uint64 1 = 1\<close>
  by (simp_all add: nat_of_uint64.rep_eq zero_uint64.rep_eq one_uint64.rep_eq)

definition uint64_of_nat_conv where
  [simp]: \<open>uint64_of_nat_conv (x :: nat) = x\<close>

lemma less_upper_bintrunc_id: \<open>n < 2 ^b \<Longrightarrow> n \<ge> 0 \<Longrightarrow> take_bit b n = n\<close> for n :: int
  by (rule take_bit_int_eq_self)

lemma nat_of_uint64_uint64_of_nat_id: \<open>n < 2^64 \<Longrightarrow> nat_of_uint64 (uint64_of_nat n) = n\<close>
  by transfer (simp add: take_bit_nat_eq_self unsigned_of_nat)

(* Does not make sense in llvm i think
lemma [sepref_fr_rules]:
  \<open>(return o uint64_of_nat, RETURN o uint64_of_nat_conv) \<in> [\<lambda>a. a < 2 ^64]\<^sub>a nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: uint64_nat_rel_def br_def nat_of_uint64_uint64_of_nat_id)
*)

    
definition  monomial_rel where
  \<open>monomial_rel \<equiv> monom_rel \<times>\<^sub>r signed_big_int_rel\<close>

abbreviation monomial_assn where
  \<open>monomial_assn \<equiv> monom_assn \<times>\<^sub>a sbi_assn\<close>

abbreviation poly_rel where
  \<open>poly_rel \<equiv> \<langle>monomial_rel\<rangle>list_rel\<close>

abbreviation poly_assn where
  \<open>poly_assn \<equiv> ol_assn monomial_assn\<close>

abbreviation polys_assn where
  \<open>polys_assn \<equiv> hm_fmap_assn uint64_nat_assn poly_assn\<close>

lemma single_valued_monomial_rel:
  \<open>single_valued monomial_rel\<close>
  unfolding monomial_rel_def signed_big_int_rel_def
  by (intro prod_rel_sv single_valued_monom_rel br_sv)

lemma IS_LEFT_UNIQUE_signed_big_int_rel:
  \<open>IS_LEFT_UNIQUE signed_big_int_rel\<close>
  unfolding IS_LEFT_UNIQUE_def signed_big_int_rel_def single_valued_def
  by (metis converse_iff in_br_conv signed_big_int_to_int_unique)

lemma single_valued_monomial_rel':
  \<open>IS_LEFT_UNIQUE monomial_rel\<close>
  unfolding monomial_rel_def IS_LEFT_UNIQUE_def inv_prod_rel_eq
  by (rule prod_rel_sv)
     (use single_valued_monom_rel' IS_LEFT_UNIQUE_signed_big_int_rel
        in \<open>simp_all add: IS_LEFT_UNIQUE_def\<close>)

subsection \<open>Polynomial Sorting\<close>

text \<open>Sorting a polynomial (list of monomial\<times>coefficient pairs) by the monomial
  component: the high-level merge sort from \<open>Monom_Assn\<close> instantiated at
  \<open>poly_assn = ol_assn monomial_assn\<close>, synthesized by sepref. The comparator projects
  the pairs to their monomials and uses the registered \<open>(\<le>)\<close> at \<open>monom_assn\<close>; it is
  synthesized separately (and registered) so that the pairs stay intact inside the
  merge synthesis. Note the comparator ignores the coefficient \<emdash> the abstract order
  is a \<^emph>\<open>weak\<close> ordering on pairs, which is fine: \<open>merge\<close>/\<open>msort_alt\<close> and their
  refinements never require order properties; sortedness enters only at the spec level
  (\<open>sort_poly_spec\<close> in \<open>PAC_Checker_Init\<close>, via \<open>msort_alt_mset\<close>/\<open>msort_alt_sorted\<close>).\<close>

definition mnl_le :: \<open>char list list \<times> int \<Rightarrow> char list list \<times> int \<Rightarrow> bool\<close> where
  \<open>mnl_le \<equiv> \<lambda>(m, _) (m', _). m \<le> m'\<close>

definition merge_mnls :: \<open>(char list list \<times> int) list \<Rightarrow> _ \<Rightarrow> _\<close> where
  \<open>merge_mnls = merge mnl_le\<close>

definition msort_mnls :: \<open>(char list list \<times> int) list \<Rightarrow> _\<close> where
  \<open>msort_mnls = msort_alt mnl_le\<close>

sepref_register mnl_le merge_mnls msort_mnls

sepref_def mnl_le_impl is \<open>uncurry (RETURN oo mnl_le)\<close>
  :: \<open>monomial_assn\<^sup>k *\<^sub>a monomial_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding mnl_le_def
  by sepref

sepref_def poly_merge_impl is \<open>uncurry (RETURN oo merge_mnls)\<close>
  :: \<open>poly_assn\<^sup>d *\<^sub>a poly_assn\<^sup>d \<rightarrow>\<^sub>a poly_assn\<close>
  unfolding merge_mnls_def merge_RECT
  by sepref

sepref_def poly_split_impl is \<open>RETURN o alt_split\<close>
  :: \<open>poly_assn\<^sup>d \<rightarrow>\<^sub>a poly_assn \<times>\<^sub>a poly_assn\<close>
  unfolding alt_split_RECT_ol
  by sepref

sepref_def poly_msort_impl is \<open>RETURN o msort_mnls\<close>
  :: \<open>poly_assn\<^sup>d \<rightarrow>\<^sub>a poly_assn\<close>
  unfolding msort_mnls_def msort_alt_RECT merge_mnls_def[symmetric]
  by sepref

text \<open>Correctness at the abstract level: multiset preservation and sortedness w.r.t.
  the (weak) monomial order on pairs \<emdash> the ingredients for \<open>sort_poly_spec\<close>.\<close>

lemma msort_mnls_mset[simp]: \<open>mset (msort_mnls xs) = mset xs\<close>
  unfolding msort_mnls_def by simp

lemma msort_mnls_sorted: \<open>sorted_wrt mnl_le (msort_mnls xs)\<close>
  unfolding msort_mnls_def
  by (rule msort_alt_sorted) (auto simp: mnl_le_def intro!: transpI)

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

text \<open>The \<open>list :: linorder\<close> instantiation (\<open>less_list = lexordp (<)\<close>,
  \<open>less_eq_list = lexordp_eq\<close>) has moved upstream to \<open>String_Assn\<close> so that the
  refinement rule for \<open>strl_lt\<close> can be stated against \<open>(<)\<close>; it is inherited here
  via \<open>Monom_Assn\<close>.\<close>


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
         rel2p_def term_order_rel_alt_def p2rel_def)
qed

definition string2_rel :: \<open>(string \<times> string) set\<close> where
  \<open>string2_rel \<equiv> \<langle>Id\<rangle>list_rel\<close>

lemma char_of_word_less_iff: \<open>char_of_word a < char_of_word b \<longleftrightarrow> (a :: 8 word) < b\<close>
  using unat_of_char_mod
  by (auto simp: char_of_word_def word_less_nat_alt PAC_Polynomials_Term.less_char_def
      simp flip: less_char_def)

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
        in_br_conv char_rel_def char_of_word_less_iff)
    by (metis char_of_word_less_iff less_le not_less)
    
qed

lemma list_rel_list_rel_order_iff:
  assumes \<open>(a, b) \<in> \<langle>string_rel\<rangle>list_rel\<close> \<open>(a', b') \<in> \<langle>string_rel\<rangle>list_rel\<close>
  shows \<open>a < a' \<longleftrightarrow> b < b'\<close>
proof
  have H: \<open>(a, b) \<in> \<langle>string_rel\<rangle>list_rel \<Longrightarrow>
       (a, cs) \<in> \<langle>string_rel\<rangle>list_rel \<Longrightarrow> b = cs\<close> for cs
     using single_valued_monom_rel' IS_RIGHT_UNIQUE_string_rel
     unfolding string2_rel_def
     by (subst (asm)list_rel_sv_iff[symmetric])
       (auto simp: single_valued_def)
  assume \<open>a < a'\<close>
  then consider
    u u' where \<open>a' = a @ u # u'\<close> |
    u aa v w aaa where \<open>a = u @ aa # v\<close> \<open>a' = u @ aaa # w\<close> \<open>aa < aaa\<close>
    by (subst (asm) less_list_def)
     (auto simp: lexord_def List.lexordp_def
      list_rel_append1 list_rel_split_right_iff)
  then show \<open>b < b'\<close>
  proof cases
    case 1
    then show \<open>b < b'\<close>
      using assms
      by (subst less_list_def)
        (auto simp: lexord_def List.lexordp_def
        list_rel_append1 list_rel_split_right_iff dest: H)
  next
    case 2
    then obtain u' aa' v' w' aaa' where
       \<open>b = u' @ aa' # v'\<close> \<open>b' = u' @ aaa' # w'\<close>
       \<open>(aa, aa') \<in> string_rel\<close>
       \<open>(aaa, aaa') \<in> string_rel\<close>
      using assms
      by (smt (verit) list_rel_append1 list_rel_split_right_iff single_valued_def single_valued_monom_rel)
    have aa_lex: \<open>(aa, aaa) \<in> lexord {(x, y). x < y}\<close>
      using \<open>aa < aaa\<close> unfolding less_list_def lexordp_conv_lexord
      using List.lexordp_def by blast
    have \<open>aa' < aaa'\<close>
      unfolding less_list_def lexordp_conv_lexord
      using lexord_char_rel_mono_iff[OF \<open>(aa, aa') \<in> string_rel\<close>[unfolded string_rel_def]
          \<open>(aaa, aaa') \<in> string_rel\<close>[unfolded string_rel_def]] aa_lex
      using List.lexordp_def by blast
    then show \<open>b < b'\<close>
      using \<open>b = u' @ aa' # v'\<close> \<open>b' = u' @ aaa' # w'\<close>
      by (subst less_list_def)
        (fastforce simp: lexord_def List.lexordp_def
        list_rel_append1 list_rel_split_right_iff)
  qed
next
  have H: \<open>(a, b) \<in> \<langle>string_rel\<rangle>list_rel \<Longrightarrow>
       (a', b) \<in> \<langle>string_rel\<rangle>list_rel \<Longrightarrow> a = a'\<close> for a a' b
     using single_valued_monom_rel'
     by (auto simp: single_valued_def IS_LEFT_UNIQUE_def
       simp flip: inv_list_rel_eq)
  assume \<open>b < b'\<close>
  then consider
    u u' where \<open>b' = b @ u # u'\<close> |
    u aa v w aaa where \<open>b = u @ aa # v\<close> \<open>b' = u @ aaa # w\<close> \<open>aa < aaa\<close>
    by (subst (asm) less_list_def)
     (auto simp: lexord_def List.lexordp_def
      list_rel_append1 list_rel_split_right_iff)
  then show \<open>a < a'\<close>
  proof cases
    case 1
    then show \<open>a < a'\<close>
      using assms
      by (subst less_list_def)
        (auto simp: lexord_def List.lexordp_def
        list_rel_append2 list_rel_split_left_iff dest: H)
  next
    case 2
    then obtain u' aa' v' w' aaa' where
       \<open>a = u' @ aa' # v'\<close> \<open>a' = u' @ aaa' # w'\<close>
       \<open>(aa', aa) \<in> string_rel\<close>
       \<open>(aaa', aaa) \<in> string_rel\<close>
      using assms
      by (auto simp: lexord_def List.lexordp_def
        list_rel_append2 list_rel_split_left_iff dest: H)
    have aa_lex: \<open>(aa, aaa) \<in> lexord {(x, y). x < y}\<close>
      using \<open>aa < aaa\<close> unfolding less_list_def lexordp_conv_lexord
      using List.lexordp_def by blast
    have \<open>aa' < aaa'\<close>
      unfolding less_list_def lexordp_conv_lexord
      using lexord_char_rel_mono_iff[OF \<open>(aa', aa) \<in> string_rel\<close>[unfolded string_rel_def]
          \<open>(aaa', aaa) \<in> string_rel\<close>[unfolded string_rel_def]] aa_lex
      using List.lexordp_def by blast
    then show \<open>a < a'\<close>
      using \<open>a = u' @ aa' # v'\<close> \<open>a' = u' @ aaa' # w'\<close>
      by (subst less_list_def)
        (fastforce simp: lexord_def List.lexordp_def
        list_rel_append1 list_rel_split_right_iff)
  qed
qed


lemma string_rel_le[sepref_import_param]:
  shows \<open>((<), (<)) \<in> \<langle>string_rel\<rangle>list_rel \<rightarrow>  \<langle>string_rel\<rangle>list_rel \<rightarrow> bool_rel\<close>
  by (auto intro!: fun_relI simp: list_rel_list_rel_order_iff)

(* TODO Move *)
lemma [sepref_import_param]:
  assumes \<open>CONSTRAINT IS_LEFT_UNIQUE R\<close>  \<open>CONSTRAINT IS_RIGHT_UNIQUE R\<close>
  shows \<open>(remove1, remove1) \<in> R \<rightarrow> \<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel\<close>
  apply (intro fun_relI)
  subgoal premises p for x y xs ys
    using p(2) p(1) assms
    by (induction xs ys rule: list_rel_induct)
      (auto simp: IS_LEFT_UNIQUE_def single_valued_def)
  done

(*
instantiation pac_step :: (heap, heap, heap) heap
begin

instance
proof standard
  obtain f :: \<open>'a \<Rightarrow> nat\<close> where
    f: \<open>inj f\<close>
    by blast
  obtain g :: \<open>nat \<times> nat \<times> nat \<times> nat \<times> nat \<Rightarrow> nat\<close> where
    g: \<open>inj g\<close>
    by blast
  obtain h :: \<open>'b \<Rightarrow> nat\<close> where
    h: \<open>inj h\<close>
    by blast
  obtain i :: \<open>'c \<Rightarrow> nat\<close> where
    i: \<open>inj i\<close>
    by blast
  have [iff]: \<open>g a = g b \<longleftrightarrow> a = b\<close>\<open>h a'' = h b'' \<longleftrightarrow> a'' = b''\<close>  \<open>f a' = f b' \<longleftrightarrow> a' = b'\<close>
    \<open>i a''' = i b''' \<longleftrightarrow> a''' = b'''\<close>  for a b a' b' a'' b'' a''' b'''
    using f g h i unfolding inj_def by blast+
  let ?f = \<open>\<lambda>x :: ('a, 'b, 'c) pac_step.
     g (case x of
        Add a b c d \<Rightarrow>     (0, i a,  i b,  i c, f d)
      | Del a  \<Rightarrow>          (1, i a,    0,   0,   0)
      | Mult a b c d \<Rightarrow>    (2, i a, f b, i c, f d)
      | Extension a b c \<Rightarrow> (3, i a, f c, 0, h b))\<close>
   have \<open>inj ?f\<close>
     apply (auto simp: inj_def)
     apply (case_tac x; case_tac y)
     apply auto
     done
   then show \<open>\<exists>f :: ('a, 'b, 'c) pac_step \<Rightarrow> nat. inj f\<close>
     by blast
qed

end
*)
end
