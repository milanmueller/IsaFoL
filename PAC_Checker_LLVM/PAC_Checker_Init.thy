(*
  File:         PAC_Checker_Init.thy
  Author:       Mathias Fleury, Daniela Kaufmann, JKU
  Maintainer:   Mathias Fleury, JKU
*)
theory PAC_Checker_Init
  imports  PAC_Polynomials_Operations LLVM_Polynomials
begin

text \<open>This theory had some significant changes: It used to implement sorting for
  monimials and coefficients, based on WB_Sort which is now removed from the project entirely. 
  For sorting, we use the generic while-based merge sort implemented in 
  \<open>PAC_Polynomials_Sort\<close>.\<close>

section \<open>@{term \<open>merge_coeffs0\<close>}\<close>
text \<open>Here, the refinement uses the WHILE-based implementation
  from \<open>PAC_Polynomials_Operations\<close>.\<close>
sepref_def merge_coeffs0_impl
  is \<open>RETURN o merge_coeffs0\<close>
  :: \<open>polynomial_assn\<^sup>d \<rightarrow>\<^sub>a polynomial_assn\<close>
  unfolding merge_coeffs1_correct[symmetric] 
  unfolding merge_coeffs1_def mc_body_def ls_emp add_poly_l2_def apl2_body_def
  by sepref

section \<open>@{term \<open>sort_coeff\<close>}\<close>

context begin
private lemma str_le_is_lexord: \<open>(x::char list) \<le> y \<equiv> lexordp_eq x y\<close>
  by (simp add: less_eq_list_def)

lemma sort_coeff_aux:
  fixes x :: \<open>char list\<close> and y :: \<open>char list\<close>
  shows \<open>(rel2p (Id \<union> var_order_rel)) x y \<equiv> x \<le> y\<close>
  unfolding str_le_is_lexord rel2p_def var_order_rel_def
  by (simp add: less_char_inst lexordp_conv_lexord lexordp_eq_conv_lexord
    p2rel_def)
end

lemma sort_coeff_by_msort: \<open>monom.msort xs \<le> sort_coeff xs\<close>
  unfolding sort_coeff_def sort_coeff_aux
  using monom.msort_spec[where xs=xs]
  by (simp add: SPEC_cons_rule) 

lemma msort_refine_sort_coeff:
  \<open>(PR_CONST monom.msort, sort_coeff) \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: sort_coeff_by_msort)
    
lemmas sort_coeff_impl[sepref_fr_rules] =
  monom.msort_impl.refine[FCOMP msort_refine_sort_coeff]

section \<open>@{term \<open>sort_all_coeffs\<close>}\<close>

lemma sort_all_coeffs_alt_aux:
  \<open>monadic_nfoldli xs (\<lambda>_. RETURN True)
     (\<lambda>(a, n) b. do {a \<leftarrow> sort_coeff a; RETURN ((a, n) # b)}) b =
   REC\<^sub>T (\<lambda>sort_all_coeffs (xs, b).
     if xs = [] then RETURN b
     else doN {
       ((x,n),xs) \<leftarrow> mop_list_pop_hd xs;
       x' \<leftarrow> sort_coeff x;
       sort_all_coeffs (xs, (x',n) # b)
     }
   ) (xs, b)\<close>
proof (induction xs arbitrary: b)
  case Nil
  show ?case
    by (subst RECT_unfold, refine_mono) auto
next
  case (Cons a xs)
  show ?case
    by (subst RECT_unfold, refine_mono) (cases a; simp add: Cons.IH)
qed

lemma sort_all_coeffs_alt:
  \<open>sort_all_coeffs xs \<equiv> REC\<^sub>T (\<lambda>sort_all_coeffs (xs, b).
    if xs = [] then RETURN b
    else doN {
      ((x,n),xs) \<leftarrow> mop_list_pop_hd xs;
      x' \<leftarrow> sort_coeff x;
      sort_all_coeffs (xs, (x',n) # b)
    }
  ) (xs, [])\<close>
  unfolding sort_all_coeffs_def
  by (rule eq_reflection) (rule sort_all_coeffs_alt_aux)

sepref_def sort_all_coeffs_impl is \<open>sort_all_coeffs\<close>
  :: \<open>polynomial_assn\<^sup>d \<rightarrow>\<^sub>a polynomial_assn\<close>
  unfolding sort_all_coeffs_alt
  by sepref

section \<open>@{term \<open>sort_poly_spec\<close>}\<close>

lemma term_order_rel_alt_def:
  \<open>term_order_rel = lexord (p2rel char.lexordp)\<close>
  by (auto simp: p2rel_def char.lexordp_conv_lexord var_order_rel_def intro!: arg_cong[of _ _ lexord])

lemma term_order_rel_by_lt: \<open>(x,y) \<in> term_order_rel \<equiv> x < y\<close>
  by (rule eq_reflection)
    (auto simp: lexordp_conv_lexord less_eq_list_def less_list_def lexordp_def
      var_order_rel_def rel2p_def term_order_rel_alt_def p2rel_def less_char_inst)

lemma monomial_sort_spec:
  \<open>sorted_wrt (rel2p (Id \<union> term_order_rel)) (map fst p) = sorted_wrt monomial_le p\<close> 
  unfolding monomial_le_def rel2p_def 
  apply (induction p; auto)
  subgoal using term_order_rel_by_lt by fastforce
  subgoal using term_order_rel_by_lt by fastforce
  done

lemma poly_msort_refine: \<open>poly.msort \<le> sort_poly_spec\<close>
  unfolding sort_poly_spec_def
  using poly.msort_spec[unfolded monomial_sort_spec[symmetric], where xs=p]
  by (simp add: le_funI monomial_sort_spec poly.msort_spec)  

lemma poly_msort_fref:
  \<open>(PR_CONST poly.msort, sort_poly_spec) \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (simp add: le_funD poly_msort_refine)

lemmas sort_poly_hnr[sepref_fr_rules] =
  poly.msort_impl.refine[FCOMP poly_msort_fref]
  
sepref_def fully_normalize_poly_impl
  is \<open>full_normalize_poly\<close>
  :: \<open>polynomial_assn\<^sup>d \<rightarrow>\<^sub>a polynomial_assn\<close>
  unfolding full_normalize_poly_def
  by sepref

end
