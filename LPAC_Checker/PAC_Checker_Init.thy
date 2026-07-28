(*
  File:         PAC_Checker_Init.thy
  Author:       Mathias Fleury, Daniela Kaufmann, JKU
  Maintainer:   Mathias Fleury, JKU
*)
theory PAC_Checker_Init
  imports  PAC_Checker PAC_Checker_Relation
begin

section \<open>Initial Normalisation of Polynomials\<close>

subsection \<open>Sorting\<close>

text \<open>Adapted from the theory \<^text>\<open>HOL-ex.MergeSort\<close> by Tobias Nipkow. We did not change much, but
   we refine it to executable code and try to improve efficiency.\<close>

text \<open>NOTE (LLVM port): \<open>merge\<close> and \<open>msort\<close> now live in \<open>IICF_Owning_List\<close> (imported via
  \<open>PAC_Checker_Relation\<close>), where the imperative implementation rules
  (\<open>ol_merge_rule\<close>/\<open>ol_msort_rule\<close>/\<open>ol_msort_hnr\<close>) are stated against them. Local
  duplicates would shadow those constants and the rules would not apply. The property
  lemmas below still hold verbatim.\<close>

lemma mset_merge [simp]:
  "mset (merge f xs ys) = mset xs + mset ys"
  by (induct f xs ys rule: merge.induct) (simp_all add: ac_simps)

lemma set_merge [simp]:
  "set (merge f xs ys) = set xs \<union> set ys"
  by (induct f xs ys rule: merge.induct) auto

lemma sorted_merge:
  "transp f \<Longrightarrow> (\<And>x y. f x y \<or> f y x) \<Longrightarrow>
   sorted_wrt f (merge f xs ys) \<longleftrightarrow> sorted_wrt f xs \<and> sorted_wrt f ys"
  apply (induct f xs ys rule: merge.induct)
  apply (auto simp add: ball_Un not_le less_le dest: transpD)
  apply blast
  apply (blast dest: transpD)
  done

lemma sorted_msort:
  "transp f \<Longrightarrow> (\<And>x y. f x y \<or> f y x) \<Longrightarrow>
   sorted_wrt f (msort f xs)"
  by (induct f xs rule: msort.induct) (simp_all add: sorted_merge)

lemma mset_msort[simp]:
  "mset (msort f xs) = mset xs"
  by (induction f xs rule: msort.induct)
    (simp_all add: union_code)

subsection \<open>Sorting applied to monomials\<close>

lemma merge_coeffs_alt_def:
  \<open>(RETURN o merge_coeffs) p =
   REC\<^sub>T (\<lambda>f p.
     if p = [] then RETURN p
     else do {
       ((xs, n), p) \<leftarrow> mop_list_pop_front p;
       if p = [] then RETURN ((xs, n) # p)
       else do {
         ((ys, m), p) \<leftarrow> mop_list_pop_front p;
         if xs = ys
         then let k = n + m in
           if k \<noteq> 0 then f ((xs, k) # p) else f p
         else do {
           p \<leftarrow> f ((ys, m) # p);
           RETURN ((xs, n) # p)
         }
       }
     })
    p\<close>
  apply (induction p rule: merge_coeffs.induct)
  subgoal by (subst RECT_unfold, refine_mono) (auto simp: refine_pw_simps)
  subgoal by (subst RECT_unfold, refine_mono) (auto simp: refine_pw_simps)
  subgoal premises IH for xs n ys m p
    apply (subst RECT_unfold, refine_mono)
    apply (cases \<open>xs = ys\<close>; cases \<open>n + m \<noteq> 0\<close>)
    subgoal using IH(1) by (auto simp: refine_pw_simps)
    subgoal using IH(2) by (auto simp: refine_pw_simps)
    subgoal using IH(3)[symmetric] by (auto simp: refine_pw_simps)
    subgoal using IH(3)[symmetric] by (auto simp: refine_pw_simps)
    done
  done

sepref_def merge_coeffs_impl
  is \<open>RETURN o merge_coeffs\<close>
  :: \<open>poly_assn\<^sup>d \<rightarrow>\<^sub>a poly_assn\<close>
  unfolding merge_coeffs_alt_def
  by sepref

lemma string_list_trans:
  \<open>(xa ::char list list, ya) \<in> lexord (lexord {(x, y). x < y}) \<Longrightarrow>
  (ya, z) \<in> lexord (lexord {(x, y). x < y}) \<Longrightarrow>
    (xa, z) \<in> lexord (lexord {(x, y). x < y})\<close>
  by (smt (verit) less_char_def char.less_trans less_than_char_def lexord_partial_trans p2rel_def)

subsection \<open>Lifting to polynomials\<close>

lemma le_term_order_rel':
  \<open>(\<le>) = (\<lambda>x y. x = y \<or>  term_order_rel' x y)\<close>
  apply (intro ext)
  apply (auto simp add: less_list_def less_eq_list_def
    lexordp_eq_conv_lexord lexordp_def)
  using term_order_rel'_alt_def_lexord term_order_rel'_def apply blast
  using term_order_rel'_alt_def_lexord term_order_rel'_def apply blast
  done

lemma var_order_rel':
  \<open>(\<le>) = (\<lambda>x y. x = y \<or> (x,y) \<in> var_order_rel)\<close>
  by (intro ext)
   (auto simp add: less_list_def less_eq_list_def
    lexordp_eq_conv_lexord lexordp_def var_order_rel_def
    lexordp_conv_lexord p2rel_def)

lemma var_order_rel'':
  \<open>(x,y) \<in> var_order_rel \<longleftrightarrow> x < y\<close>
  by (metis leD less_than_char_linear lexord_linear neq_iff var_order_rel' var_order_rel_antisym
      var_order_rel_def)

definition var_order' where
  [simp]: \<open>var_order' = var_order\<close>

lemma var_order_rel[def_pat_rules]:
  \<open>(\<in>)$(x,y)$var_order_rel \<equiv> var_order'$x$y\<close>
  by (auto simp: p2rel_def rel2p_def)

lemma var_order_rel_alt_def:
  \<open>var_order_rel = p2rel char.lexordp\<close>
  apply (auto simp: p2rel_def char.lexordp_conv_lexord var_order_rel_def)
  using char.lexordp_conv_lexord apply auto
  done

lemma var_order_rel_var_order:
  \<open>(x, y) \<in> var_order_rel \<longleftrightarrow> var_order x y\<close>
  by (auto simp: rel2p_def)

(* not sure if we maybe want this back?
lemma lexord_eq_conv_le: \<open>lexord_eq a b = ((\<le>) :: 'a::linorder list \<Rightarrow> _) a b\<close>
  apply (induction rule: lexord_eq.induct)
  using lexord_eq.simps(1) list_less_Nil_right not_le_imp_less apply blast
  apply (metis basic_trans_rules(24) lexord_eq.simps(2) linorder_linear linorder_not_less list_less_Cons)
  by (simp add: le_by_lt_str list_less_Nil_left)

sepref_register lexord_eq
sepref_definition lexord_eq_term
  is \<open>uncurry (RETURN oo lexord_eq)\<close>
  :: \<open>monom_assn\<^sup>k *\<^sub>a monom_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply[[goals_limit=1]]
  unfolding lexord_eq_conv_le 
  by sepref

declare lexord_eq_term.refine[sepref_fr_rules]
*)
lemma term_order_rel_trans:
  \<open>(a, aa) \<in> term_order_rel \<Longrightarrow> (aa, ab) \<in> term_order_rel \<Longrightarrow> (a, ab) \<in> term_order_rel\<close>
  by (metis Char_Assn.less_char_def p2rel_def string_list_trans var_order_rel_def)

lemma msort_mnls_sort_poly_spec_aux:
  \<open>fst x = fst y \<or> (fst x, fst y) \<in> term_order_rel \<equiv> mnl_le x y\<close>
  by (smt (verit) le_term_order_rel' mnl_le_def prod.collapse split_conv term_order_rel'_def)
  
lemma msort_mnls_sort_poly_spec:
  \<open>(RETURN o msort_mnls, sort_poly_spec) \<in> \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>\<langle>Id\<rangle>list_rel\<rangle>nres_rel\<close>
  unfolding sort_poly_spec_def
  apply (intro frefI nres_relI)
  apply (auto simp: sorted_wrt_map mnl_le_def rel2p_def le_term_order_rel' case_prod_beta)
  by (simp add:  msort_mnls_sorted msort_mnls_sort_poly_spec_aux)

lemmas sort_poly_spec_hnr_msort[sepref_fr_rules] =
  poly_msort_impl.refine[FCOMP msort_mnls_sort_poly_spec,
    unfolded list_rel_id_simp hr_comp_Id2]

declare merge_coeffs_impl.refine[sepref_fr_rules]

sepref_def normalize_poly_impl
  is \<open>normalize_poly\<close> :: \<open>poly_assn\<^sup>d \<rightarrow>\<^sub>a poly_assn\<close>
  unfolding normalize_poly_def
  by sepref

declare normalize_poly_impl.refine[sepref_fr_rules]

lemma total_on_lexord_less_than_char_linear2:
  \<open>xs \<noteq> ys \<Longrightarrow> (xs, ys) \<notin> lexord (less_than_char) \<longleftrightarrow>
       (ys, xs) \<in> lexord less_than_char\<close>
   using lexord_linear[of \<open>less_than_char\<close> xs ys]
   using lexord_linear[of \<open>less_than_char\<close>] less_than_char_linear
   apply (auto simp: Relation.total_on_def)
   using lexord_irrefl[OF irrefl_less_than_char]
     antisym_lexord[OF antisym_less_than_char irrefl_less_than_char]
   apply (auto simp: antisym_def)
   done

lemma string_trans:
  \<open>(xa, ya) \<in> lexord {(x::char, y::char). x < y} \<Longrightarrow>
  (ya, z) \<in> lexord {(x::char, y::char). x < y} \<Longrightarrow>
  (xa, z) \<in> lexord {(x::char, y::char). x < y}\<close>
  by (smt (verit) less_char_def char.less_trans less_than_char_def lexord_partial_trans p2rel_def)

lemma le_var_order_rel:
  \<open>(\<le>) = (\<lambda>x y. x = y \<or> (x, y) \<in> var_order_rel)\<close>
  by (intro ext)
   (auto simp add: less_list_def less_eq_list_def rel2p_def
      p2rel_def lexordp_conv_lexord p2rel_def var_order_rel_def
    lexordp_eq_conv_lexord lexordp_def)

text \<open>Pop-based recursion equations, cf. \<open>merge_coeffs_alt_def\<close>: the case patterns of
  \<open>merge_coeffs0\<close> would become keep-mode \<open>hd\<close>/\<open>tl\<close> (impossible at \<open>poly_assn\<close>). In the
  singleton branch the popped-empty tail \<open>p\<close> is reused, so no empty-list producer is
  needed; the dropped \<open>(xs, n)\<close> in the \<open>n = 0\<close> branches is freed by sepref via the
  registered \<open>MK_FREE\<close> rules.\<close>

lemma merge_coeffs0_alt_def:
  \<open>(RETURN o merge_coeffs0) p =
   REC\<^sub>T (\<lambda>f p.
     if p = [] then RETURN p
     else do {
       ((xs, n), p) \<leftarrow> mop_list_pop_front p;
       if p = [] then (if n = 0 then RETURN p else RETURN ((xs, n) # p))
       else do {
         ((ys, m), p) \<leftarrow> mop_list_pop_front p;
         if xs = ys
         then if n + m \<noteq> 0 then f ((xs, n + m) # p) else f p
         else if n = 0 then f ((ys, m) # p)
         else do { p \<leftarrow> f ((ys, m) # p); RETURN ((xs, n) # p) }
       }
     }) p\<close>
  apply (subst eq_commute)
  apply (induction p rule: merge_coeffs0.induct)
  subgoal by (subst RECT_unfold, refine_mono) auto
  subgoal by (subst RECT_unfold, refine_mono) (auto simp: refine_pw_simps)
  subgoal by (subst RECT_unfold, refine_mono) (auto simp: refine_pw_simps)
  done

sepref_def merge_coeffs0_impl
  is \<open>RETURN o merge_coeffs0\<close>
  :: \<open>poly_assn\<^sup>d \<rightarrow>\<^sub>a poly_assn\<close>
  unfolding merge_coeffs0_alt_def
  by sepref

declare merge_coeffs0_impl.refine[sepref_fr_rules]

subsection \<open>Sorting the variables of all monomials\<close>

text \<open>\<open>sort_all_coeffs\<close> is a \<open>monadic_nfoldli\<close> over the polynomial with the per-monomial
  spec \<open>sort_coeff\<close> in the body. Neither translates directly (no \<open>nfoldli\<close> rule at
  \<open>ol_assn\<close>, and the fold reads elements destructively), so we implement the whole
  function by a pop-based recursion with \<open>msort_vars\<close> in the body \<emdash> the accumulator
  automatically builds the reversed list, exactly as \<open>sort_all_coeffs\<close> does.\<close>

lemma rel2p_Id_var_order_le: \<open>rel2p (Id \<union> var_order_rel) = (\<le>)\<close>
  by (intro ext) (auto simp: rel2p_def le_var_order_rel)

definition sort_all_coeffs2 :: \<open>llist_polynomial \<Rightarrow> llist_polynomial nres\<close> where
  \<open>sort_all_coeffs2 xs\<^sub>0 = REC\<^sub>T (\<lambda>f (xs, b).
     if xs = [] then RETURN b
     else do {
       ((a, n), xs) \<leftarrow> mop_list_pop_front xs;
       f (xs, (msort_vars a, n) # b)
     }) (xs\<^sub>0, op_ol_empty)\<close>

lemma sort_all_coeffs2_aux:
  \<open>REC\<^sub>T (\<lambda>f (xs, b).
     if xs = [] then RETURN b
     else do {
       ((a, n), xs) \<leftarrow> mop_list_pop_front xs;
       f (xs, (msort_vars a, n) # b)
     }) (xs, b)
   \<le> monadic_nfoldli xs (\<lambda>_. RETURN True)
       (\<lambda>(a, n) b. do {a \<leftarrow> sort_coeff a; RETURN ((a, n) # b)}) b\<close>
proof (induction xs arbitrary: b)
  case Nil
  show ?case
    by (subst RECT_unfold, refine_mono) auto
next
  case (Cons x xs)
  obtain a n where x: \<open>x = (a, n)\<close> by (cases x) auto
  text \<open>The sorted result satisfies the per-monomial spec \<emdash> a small pointwise fact.\<close>
  have spec: \<open>RETURN (msort_vars a) \<le> sort_coeff a\<close>
    unfolding sort_coeff_def rel2p_Id_var_order_le
    by (auto simp: msort_vars_sorted pw_le_iff refine_pw_simps)
  show ?case
    apply (subst RECT_unfold, refine_mono)
    apply (simp add: x refine_pw_simps)
    apply (rule order_trans[OF Cons.IH])
    using spec by (auto simp: pw_le_iff refine_pw_simps)
qed

lemma sort_all_coeffs2_sort_all_coeffs:
  \<open>(sort_all_coeffs2, sort_all_coeffs) \<in> \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>\<langle>Id\<rangle>list_rel\<rangle>nres_rel\<close>
  unfolding sort_all_coeffs2_def sort_all_coeffs_def
  by (intro frefI nres_relI) (auto intro: sort_all_coeffs2_aux[simplified])

sepref_def sort_all_coeffs_impl
  is \<open>sort_all_coeffs2\<close>
  :: \<open>poly_assn\<^sup>d \<rightarrow>\<^sub>a poly_assn\<close>
  unfolding sort_all_coeffs2_def
  by sepref

lemmas sort_all_coeffs_hnr[sepref_fr_rules] =
  sort_all_coeffs_impl.refine[FCOMP sort_all_coeffs2_sort_all_coeffs,
    unfolded list_rel_id_simp hr_comp_Id2]

sepref_def fully_normalize_poly_impl
  is \<open>full_normalize_poly\<close>
  :: \<open>poly_assn\<^sup>d \<rightarrow>\<^sub>a poly_assn\<close>
  unfolding full_normalize_poly_def
  by sepref

declare fully_normalize_poly_impl.refine[sepref_fr_rules]

end
