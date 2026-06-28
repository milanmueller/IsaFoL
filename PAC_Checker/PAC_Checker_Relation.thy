(*
  File:         PAC_Checker_Relation.thy
  Author:       Mathias Fleury, Daniela Kaufmann, JKU
  Maintainer:   Mathias Fleury, JKU
*)
theory PAC_Checker_Relation
  imports PAC_Checker HashMap "Native_Word.Uint64" "Native_Word.Uint32" Collections.HashCode
    String_Assn
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

(*
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

(*
lemma [sepref_fr_rules]:
  \<open>(return o uint64_of_nat, RETURN o uint64_of_nat_conv) \<in> [\<lambda>a. a < 2 ^64]\<^sub>a nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: uint64_nat_rel_def br_def nat_of_uint64_uint64_of_nat_id)
*)

(*
lemmas eq_string_eq_hnr =
   eq_string_eq[sepref_import_param]
*)

abbreviation \<open>string_assn \<equiv> larray_assn' TYPE(size_t) char_assn\<close>
definition \<open>string_rel \<equiv> \<langle>char_rel\<rangle>list_rel\<close>

abbreviation monom_rel where
  \<open>monom_rel \<equiv> \<langle>string_rel\<rangle>list_rel\<close>

abbreviation monom_assn where
  \<open>monom_assn \<equiv> al_assn' TYPE(size_t) string_assn\<close>

term aal_assn

term \<open>unat_assn' TYPE(size_t)\<close>

(* TODO: For now, we use sint_assn, but we want to eventually refine this to signed_big_int *)
abbreviation monomial_rel where
  \<open>monomial_rel \<equiv> monom_rel \<times>\<^sub>r int_rel\<close>

abbreviation monomial_assn where
  \<open>monomial_assn \<equiv> monom_assn \<times>\<^sub>a (sint_assn' TYPE(size_t))\<close>

abbreviation poly_rel where
  \<open>poly_rel \<equiv> \<langle>monomial_rel\<rangle>list_rel\<close>

abbreviation poly_assn where
  \<open>poly_assn \<equiv> al_assn' TYPE(size_t) monomial_assn\<close>

term poly_assn

term \<open>aal_assn' TYPE(size_t) TYPE(size_t) char_assn\<close>

definition \<open>monom_vars_assn \<equiv> aal_assn' TYPE(size_t) TYPE(size_t) char_assn\<close>
definition \<open>monom_coeffs_assn \<equiv> aal_assn' TYPE(size_t) TYPE(size_t) sbi_aux_assn\<close>
definition \<open>polys_lookup_assn \<equiv> aal_assn' TYPE(size_t) TYPE(size_t) (snat_assn' TYPE(size_t))\<close>


term \<open>aal_assn' TYPE(size_t)\<close>

(*
lemma poly_assn_alt_def:
  \<open>poly_assn = pure poly_rel\<close>
  by (simp add: list_assn_pure_conv)
*)

abbreviation polys_assn where
  \<open>polys_assn \<equiv> hashmap_fmap_assn uint64_nat_assn poly_assn\<close>

(*
lemma string_rel_string_assn:
  \<open>(\<up> ((c, a) \<in> string_rel)) = string_assn a c\<close>
  by (auto simp: pure_app_eq)
*)


lemma single_valued_string_rel: \<open>single_valued string_rel\<close>
  unfolding single_valued_def string_rel_def list_rel_def
  by (auto simp: list_all2_conv_all_nth br_def intro!: nth_equalityI)

lemma IS_LEFT_UNIQUE_string_rel:
   \<open>IS_LEFT_UNIQUE string_rel\<close>
  oops

lemma IS_RIGHT_UNIQUE_string_rel:
   \<open>IS_RIGHT_UNIQUE string_rel\<close>
  by (metis single_valued_string_rel)

(*
lemma single_valued_monom_rel: \<open>single_valued monom_rel\<close>
  by (simp add: list_rel_sv single_valued_string_rel)
*)

thm frefI
(*
lemma single_valued_monomial_rel: \<open>single_valued monomial_rel\<close>
  using single_valued_monom_rel
  by (auto intro!: frefI simp: rel2p_def single_valued_def 
      p2rel_def in_br_conv signed_big_int_rel_def)
*)
(*
lemma single_valued_monom_rel': \<open>IS_LEFT_UNIQUE monom_rel\<close>
  unfolding IS_LEFT_UNIQUE_def inv_list_rel_eq string2_rel_def
  by (rule list_rel_sv)+
   (auto intro!: frefI simp: string_rel_def
    rel2p_def single_valued_def p2rel_def literal.explode_inject)
*)

(*
lemma single_valued_monomial_rel':
  \<open>IS_LEFT_UNIQUE monomial_rel\<close>
  using single_valued_monom_rel'
  unfolding IS_LEFT_UNIQUE_def inv_list_rel_eq
  by (auto intro!: frefI simp:
    rel2p_def single_valued_def p2rel_def)
*)

(*
lemma [safe_constraint_rules]:
  \<open>Sepref_Constraints.CONSTRAINT single_valued string_rel\<close>
  \<open>Sepref_Constraints.CONSTRAINT IS_LEFT_UNIQUE string_rel\<close>
  by (auto simp: CONSTRAINT_def single_valued_def
    string_rel_def IS_LEFT_UNIQUE_def literal.explode_inject)
*)

(*
lemma eq_string_monom_hnr[sepref_fr_rules]:
  \<open>(uncurry (Mreturn oo (=)), uncurry (RETURN oo (=))) \<in> monom_assn\<^sup>k *\<^sub>a monom_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  using single_valued_monom_rel' single_valued_monom_rel
  apply sepref_dbg_keep
  oops
*)

definition term_order_rel' where
  [simp]: \<open>term_order_rel' x y = ((x, y) \<in> term_order_rel)\<close>

lemma term_order_rel[def_pat_rules]:
  \<open>(\<in>)$(x,y)$term_order_rel \<equiv> term_order_rel'$x$y\<close>
  by auto

lemma term_order_rel_alt_def:
  \<open>term_order_rel = lexord (p2rel char.lexordp)\<close>
  by (auto simp: p2rel_def char.lexordp_conv_lexord var_order_rel_def intro!: arg_cong[of _ _ lexord])

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

lemma list_rel_list_rel_order_iff:
  assumes \<open>(a, b) \<in> \<langle>string_rel\<rangle>list_rel\<close> \<open>(a', b') \<in> \<langle>string_rel\<rangle>list_rel\<close>
  shows \<open>a < a' \<longleftrightarrow> b < b'\<close>
proof
  have H: \<open>(xs, ys) \<in> \<langle>string_rel\<rangle>list_rel \<Longrightarrow>
       (xs, zs) \<in> \<langle>string_rel\<rangle>list_rel \<Longrightarrow> ys = zs\<close> for xs ys zs
     using list_rel_sv[OF single_valued_string_rel]
     by (auto simp: single_valued_def)
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
    have \<open>\<exists>u' aa' v' w' aaa'.
       b = u' @ aa' # v' \<and> b' = u' @ aaa' # w' \<and>
       (aa, aa') \<in> string_rel \<and>
       (aaa, aaa') \<in> string_rel\<close>
    proof -
      obtain cs y ys csa ya ysa where
        \<open>b = cs @ y # ys\<close> \<open>b' = csa @ ya # ysa\<close>
        \<open>(u, cs) \<in> \<langle>string_rel\<rangle>list_rel\<close>
        \<open>(u, csa) \<in> \<langle>string_rel\<rangle>list_rel\<close>
        \<open>(aa, y) \<in> string_rel\<close>
        \<open>(aaa, ya) \<in> string_rel\<close>
        using assms 2
        by (auto simp: list_rel_append1 list_rel_split_right_iff)
      have \<open>cs = csa\<close>
        using \<open>(u, cs) \<in> \<langle>string_rel\<rangle>list_rel\<close>
          \<open>(u, csa) \<in> \<langle>string_rel\<rangle>list_rel\<close>
        by (rule H)
      show ?thesis
        using \<open>b = cs @ y # ys\<close> \<open>b' = csa @ ya # ysa\<close>
          \<open>(aa, y) \<in> string_rel\<close> \<open>(aaa, ya) \<in> string_rel\<close>
          \<open>cs = csa\<close>
        by auto
    qed
    then obtain u' aa' v' w' aaa' where
       \<open>b = u' @ aa' # v'\<close> \<open>b' = u' @ aaa' # w'\<close>
       \<open>(aa, aa') \<in> string_rel\<close>
       \<open>(aaa, aaa') \<in> string_rel\<close>
      by blast
    with \<open>aa < aaa\<close> have \<open>aa' < aaa'\<close>
      by (auto simp: string_rel_def less_literal.rep_eq less_list_def
        lexordp_conv_lexord lexordp_def char.lexordp_conv_lexord
          simp flip: less_char_def PAC_Polynomials_Term.less_char_def)
    then show \<open>b < b'\<close>
      using \<open>b = u' @ aa' # v'\<close> \<open>b' = u' @ aaa' # w'\<close>
      by (subst less_list_def)
        (fastforce simp: lexord_def List.lexordp_def
        list_rel_append1 list_rel_split_right_iff)
  qed
next
  have H: \<open>(a, b) \<in> \<langle>string_rel\<rangle>list_rel \<Longrightarrow>
       (a', b) \<in> \<langle>string_rel\<rangle>list_rel \<Longrightarrow> a = a'\<close> for a a' b
     using list_rel_sv[of \<open>string_rel\<inverse>\<close>] IS_LEFT_UNIQUE_string_rel
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
    with \<open>aa < aaa\<close> have \<open>aa' < aaa'\<close>
      by (auto simp: string_rel_def less_literal.rep_eq less_list_def
        lexordp_conv_lexord lexordp_def char.lexordp_conv_lexord
          simp flip: less_char_def PAC_Polynomials_Term.less_char_def)
    then show \<open>a < a'\<close>
      using \<open>a = u' @ aa' # v'\<close> \<open>a' = u' @ aaa' # w'\<close>
      by (subst less_list_def)
        (fastforce simp: lexord_def List.lexordp_def
        list_rel_append1 list_rel_split_right_iff)
  qed
qed

(*
lemma less_char_param[sepref_import_param]:
  \<open>((<), (<)) \<in> char_rel \<rightarrow> char_rel \<rightarrow> bool_rel\<close>
  sorry
*)
(*
proof (intro fun_relI)
  fix w1 w2 :: \<open>8 word\<close> and c1 c2 :: char
  assume h1: \<open>(w1, c1) \<in> char_rel\<close> and h2: \<open>(w2, c2) \<in> char_rel\<close>
  then have c1: \<open>c1 = char_of (unat w1)\<close> and c2: \<open>c2 = char_of (unat w2)\<close>
    by (simp_all add: in_br_conv)
  have b1: \<open>unat w1 < 256\<close> and b2: \<open>unat w2 < 256\<close>
    using unat_lt2p[of w1] unat_lt2p[of w2] by simp_all
  show \<open>(w1 < w2) = (c1 < c2)\<close>
    unfolding c1 c2
    by (simp only: word_less_nat_alt less_char_def PAC_Polynomials_Term.less_char_def
                   of_char_of mod_less[OF b1] mod_less[OF b2])
qed
*)
(*
lemma string_rel_le[sepref_import_param]:
  shows \<open>((<), (<)) \<in> \<langle>string_rel\<rangle>list_rel \<rightarrow>  \<langle>string_rel\<rangle>list_rel \<rightarrow> bool_rel\<close>
  by (auto intro!: fun_relI simp: list_rel_list_rel_order_iff)
*)

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
