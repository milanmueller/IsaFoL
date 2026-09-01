theory LPAC_Efficient_Checker_Synthesis
  imports LPAC_Efficient_Checker
    LPAC_Perfectly_Shared_Vars
    LPAC_Efficient_Checker_Sorting
    PAC_Checker_Synthesis
    LPAC_Error
begin

(* Overwrite the refinement target of check_linear_combi_l_pre_err *)
lemma check_linear_combi_l_pre_err_s_fref:
  \<open>(uncurry3 (RETURN oooo check_linear_combi_l_pre_err_imp_s),
    uncurry3 (check_linear_combi_l_pre_err)) 
   \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding check_linear_combi_l_pre_err_impl_def check_linear_combi_l_pre_err_def
  by auto

lemmas check_linear_combi_l_pre_err_s_hnr[sepref_fr_rules] =
  check_linear_combi_l_pre_err_s_impl.refine[FCOMP check_linear_combi_l_pre_err_s_fref]

lemma term_order_rel_trans:
  \<open>(a, aa) \<in> term_order_rel \<Longrightarrow>
       (aa, ab) \<in> term_order_rel \<Longrightarrow> (a, ab) \<in> term_order_rel\<close>
  using lexord_trans trans_var_order_rel by blast

lemma monadic_nfoldli_refine[refine]:
  assumes \<open>(l, l') \<in> \<langle>S\<rangle>list_rel\<close> and \<open>(s, s') \<in> R\<close>
    and \<open>\<And>s s'. (s, s') \<in> R \<Longrightarrow> c s \<le> \<Down>bool_rel (c' s')\<close>
    and \<open>\<And>x x' s s'. \<lbrakk>(x, x') \<in> S; (s, s') \<in> R\<rbrakk> \<Longrightarrow> f x s \<le> \<Down>R (f' x' s')\<close>
  shows \<open>monadic_nfoldli l c f s \<le> \<Down>R (monadic_nfoldli l' c' f' s')\<close>
  using assms(1,2)
proof (induction l arbitrary: l' s s')
  case Nil
  then show ?case by auto
next
  case (Cons x l)
  obtain x' l'' where l': \<open>l' = x' # l''\<close> and xx: \<open>(x, x') \<in> S\<close> and
    ll: \<open>(l, l'') \<in> \<langle>S\<rangle>list_rel\<close>
    using Cons.prems by (auto simp: list_rel_split_right_iff)
  show ?case
    unfolding l' monadic_nfoldli_simp
    apply (refine_rcg assms(3) assms(4)[OF xx] Cons.IH[OF ll])
    apply (use Cons.prems in \<open>auto\<close>)+
    done
qed
(* Original File from here *)

lemma in_set_rel_inD: \<open>(x,y) \<in>\<langle>R\<rangle>list_rel \<Longrightarrow> a \<in> set x \<Longrightarrow> \<exists>b \<in> set y. (a,b)\<in> R\<close>
  by (metis (no_types, lifting) Un_iff list.set_intros(1) list_relE3 list_rel_append1 set_append split_list_first)

lemma perfectly_shared_monom_eqD: \<open>(a, ab) \<in> perfectly_shared_monom \<V> \<Longrightarrow> ab = map ((the \<circ>\<circ> fmlookup) (fst (snd \<V>))) a\<close>
  by (induction a arbitrary: ab)
   (auto simp: append_eq_append_conv2 append_eq_Cons_conv Cons_eq_append_conv
    list_rel_append1 list_rel_split_right_iff perfectly_shared_var_rel_def br_def)

lemma perfectly_shared_monom_unique_left:
  \<open>(x, y) \<in> perfectly_shared_monom \<V> \<Longrightarrow> (x, y') \<in> perfectly_shared_monom \<V> \<Longrightarrow> y = y'\<close>
  using perfectly_shared_monom_eqD by blast

lemma perfectly_shared_monom_unique_right:
  \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel  \<Longrightarrow>
  (x, y) \<in> perfectly_shared_monom \<V> \<Longrightarrow> (x', y) \<in> perfectly_shared_monom \<V> \<Longrightarrow> x = x'\<close>
  by (induction x arbitrary: x' y)
   (auto simp: append_eq_append_conv2 append_eq_Cons_conv Cons_eq_append_conv
    list_rel_split_left_iff perfectly_shared_vars_rel_def perfectly_shared_vars_def
    list_rel_append1 list_rel_split_right_iff perfectly_shared_var_rel_def br_def
    add_mset_eq_add_mset
    dest!: multi_member_split[of _ \<open>dom_m _\<close>])

lemma perfectly_shared_polynom_unique_left:
  \<open>(x, y) \<in> perfectly_shared_polynom \<V> \<Longrightarrow> (x, y') \<in> perfectly_shared_polynom \<V> \<Longrightarrow> y = y'\<close>
  by (induction x arbitrary: y y')
    (auto dest: perfectly_shared_monom_unique_left simp: list_rel_split_right_iff)
lemma perfectly_shared_polynom_unique_right:
  \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel  \<Longrightarrow>
  (x, y) \<in> perfectly_shared_polynom \<V> \<Longrightarrow> (x', y) \<in> perfectly_shared_polynom \<V> \<Longrightarrow> x = x'\<close>
  by (induction x arbitrary: x' y)
   (auto dest: perfectly_shared_monom_unique_right simp: list_rel_split_left_iff
    list_rel_split_right_iff)

definition (in -)perfect_shared_var_order_s :: \<open>(nat, string)shared_vars \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ordered nres\<close> where
  \<open>perfect_shared_var_order_s \<D> x y = do {
    eq \<leftarrow> perfectly_shared_strings_equal_l \<D> x y;
    if eq then RETURN EQUAL
    else do {
      x \<leftarrow> get_var_nameS \<D> x;
      y \<leftarrow> get_var_nameS \<D> y;
      if (x, y) \<in> var_order_rel then RETURN (LESS)
      else RETURN (GREATER)
    }
  }\<close>

lemma perfect_shared_var_order_s_perfect_shared_var_order:
  assumes \<open>(\<V>, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>(i, i') \<in> perfectly_shared_var_rel \<V>\<close>and
    \<open>(j, j') \<in> perfectly_shared_var_rel \<V>\<close>
  shows \<open>perfect_shared_var_order_s \<V> i j \<le>\<Down>Id (perfect_shared_var_order \<V>\<D> i' j')\<close>
proof -
  show ?thesis
    unfolding perfect_shared_var_order_s_def perfect_shared_var_order_def
    apply (refine_rcg perfectly_shared_strings_equal_l_perfectly_shared_strings_equal
      get_var_nameS_spec)
    subgoal using assms by metis
    subgoal using assms by metis
    subgoal using assms by metis
    subgoal by auto
    subgoal using assms by auto
    subgoal using assms by metis
    subgoal using assms by metis
    subgoal using assms by metis
    subgoal by auto
    done
qed

definition (in -) perfect_shared_term_order_rel_s
  :: \<open>(nat, string) shared_vars \<Rightarrow> nat list\<Rightarrow> nat list \<Rightarrow> ordered nres\<close>
where
  \<open>perfect_shared_term_order_rel_s \<V> xs ys  = do {
    (b, _, _) \<leftarrow> WHILE\<^sub>T (\<lambda>(b, xs, ys). b = UNKNOWN)
    (\<lambda>(b, xs, ys). do {
       if xs = [] \<and> ys = [] then RETURN (EQUAL, xs, ys)
       else if xs = [] then RETURN (LESS, xs, ys)
       else if ys = [] then RETURN (GREATER, xs, ys)
       else do {
         ASSERT(xs \<noteq> [] \<and> ys \<noteq> []);
         eq \<leftarrow> perfect_shared_var_order_s \<V> (hd xs) (hd ys);
         if eq = EQUAL then RETURN (b, tl xs, tl ys)
         else RETURN (eq, xs, ys)
      }
    }) (UNKNOWN, xs, ys);
    RETURN b
  }\<close>

lemma perfect_shared_term_order_rel_s_alt_def:
  \<open>perfect_shared_term_order_rel_s \<V> xs ys = do {
    (b, _, _) \<leftarrow> WHILE\<^sub>T (\<lambda>(b, xs, ys). b = UNKNOWN)
    (\<lambda>(b, xs, ys). do {
       if xs = [] \<and> ys = [] then RETURN (EQUAL, xs, ys)
       else if xs = [] then RETURN (LESS, xs, ys)
       else if ys = [] then RETURN (GREATER, xs, ys)
       else do {
         ASSERT(xs \<noteq> [] \<and> ys \<noteq> []);
         (x, xs) \<leftarrow> mop_list_pop_hd xs;
         (y, ys) \<leftarrow> mop_list_pop_hd ys;
         eq \<leftarrow> perfect_shared_var_order_s \<V> x y;
         if eq = EQUAL then RETURN (b, xs, ys)
         else RETURN (eq, x # xs, y # ys)
      }
    }) (UNKNOWN, xs, ys);
    RETURN b
  }\<close>
proof -
  have 1: \<open>(\<lambda>(b, xs, ys). do {
       if xs = [] \<and> ys = [] then RETURN (EQUAL, xs, ys)
       else if xs = [] then RETURN (LESS, xs, ys)
       else if ys = [] then RETURN (GREATER, xs, ys)
       else do {
         ASSERT(xs \<noteq> [] \<and> ys \<noteq> []);
         (x, xs) \<leftarrow> mop_list_pop_hd xs;
         (y, ys) \<leftarrow> mop_list_pop_hd ys;
         eq \<leftarrow> perfect_shared_var_order_s \<V> x y;
         if eq = EQUAL then RETURN (b, xs, ys)
         else RETURN (eq, x # xs, y # ys)
      }
    }) = (\<lambda>(b, xs, ys). do {
       if xs = [] \<and> ys = [] then RETURN (EQUAL, xs, ys)
       else if xs = [] then RETURN (LESS, xs, ys)
       else if ys = [] then RETURN (GREATER, xs, ys)
       else do {
         ASSERT(xs \<noteq> [] \<and> ys \<noteq> []);
         eq \<leftarrow> perfect_shared_var_order_s \<V> (hd xs) (hd ys);
         if eq = EQUAL then RETURN (b, tl xs, tl ys)
         else RETURN (eq, xs, ys)
      }
    })\<close>
    by (intro ext)
      (auto simp: mop_list_pop_hd_def pw_eq_iff refine_pw_simps
        split: prod.splits list.splits)
  show ?thesis
    unfolding perfect_shared_term_order_rel_s_def 1 by auto
qed

lemma perfect_shared_term_order_rel_s_perfect_shared_term_order_rel:
  assumes \<open>(\<V>, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>(xs, xs') \<in> perfectly_shared_monom \<V>\<close> and
    \<open>(ys, ys') \<in> perfectly_shared_monom \<V>\<close>
  shows \<open>perfect_shared_term_order_rel_s \<V> xs ys \<le> \<Down>Id (perfect_shared_term_order_rel \<V>\<D> xs' ys')\<close>
  using assms
  unfolding perfect_shared_term_order_rel_s_def perfect_shared_term_order_rel_def 
  apply (refine_rcg WHILET_refine[where R = \<open>Id \<times>\<^sub>r perfectly_shared_monom \<V> \<times>\<^sub>r perfectly_shared_monom \<V>\<close>]
    perfect_shared_var_order_s_perfect_shared_var_order)
  subgoal by fastforce
  subgoal by fastforce
  subgoal by fastforce
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: neq_Nil_conv)
  subgoal by (auto simp: neq_Nil_conv)
  subgoal by auto
  subgoal by (auto simp: neq_Nil_conv)
  subgoal by (auto simp: neq_Nil_conv)
  subgoal by (auto simp: neq_Nil_conv)
  done

subsection \<open>Monadic mergesort: instantiation for the PAC term order\<close>

definition monom_abs :: \<open>(nat, string) shared_vars \<Rightarrow> nat list \<Rightarrow> string list\<close> where
  \<open>monom_abs \<V> m = map (the o fmlookup (fst (snd \<V>))) m\<close>

definition term_cmp :: \<open>(nat, string) shared_vars \<Rightarrow> nat list \<times> int \<Rightarrow> nat list \<times> int \<Rightarrow> bool\<close> where
  \<open>term_cmp \<V> x y \<equiv> (monom_abs \<V> (fst x), monom_abs \<V> (fst y)) \<in> Id \<union> term_order_rel\<close>

definition term_valid :: \<open>(nat, string) shared_vars \<Rightarrow> nat list \<times> int \<Rightarrow> bool\<close> where
  \<open>term_valid \<V> x \<equiv> (\<forall>a\<in>set (fst x). a \<in># dom_m (fst (snd \<V>)))\<close>

definition term_mcmp :: \<open>(nat, string) shared_vars \<Rightarrow> nat list \<times> int \<Rightarrow> nat list \<times> int \<Rightarrow> bool nres\<close> where
  \<open>term_mcmp \<V> x y = do {
    a \<leftarrow> perfect_shared_term_order_rel_s \<V> (fst x) (fst y);
    RETURN (a \<noteq> GREATER)
  }\<close>

definition msort_monoms :: \<open>(nat, string) shared_vars \<Rightarrow> (nat list \<times> int) list \<Rightarrow> (nat list \<times> int) list nres\<close> where
  \<open>msort_monoms \<V> xs = mcmp_msort (term_cmp \<V>) (term_valid \<V>) (term_mcmp \<V>) xs\<close>

context
  fixes \<V> :: \<open>(nat, string) shared_vars\<close> and \<V>\<D> :: \<open>(nat, string) vars\<close>
  assumes V_rel: \<open>(\<V>, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close>
begin

text \<open>Bridge: a valid monom is related to its lookup image.\<close>
lemma term_valid_monom_rel:
  assumes \<open>term_valid \<V> x\<close>
  shows \<open>(fst x, monom_abs \<V> (fst x)) \<in> perfectly_shared_monom \<V>\<close>
    and \<open>set (monom_abs \<V> (fst x)) \<subseteq> set_mset \<V>\<D>\<close>
proof -
  show \<open>(fst x, monom_abs \<V> (fst x)) \<in> perfectly_shared_monom \<V>\<close>
    using assms
    unfolding monom_abs_def term_valid_def perfectly_shared_var_rel_def
      list_rel_def
    by (auto simp: in_br_conv list.rel_map(2) list_all2_same
    prod.split_sel_asm)
next
  show \<open>set (monom_abs \<V> (fst x)) \<subseteq> set_mset \<V>\<D>\<close>
    using assms V_rel
    unfolding monom_abs_def term_valid_def
      perfectly_shared_vars_rel_def perfectly_shared_vars_def
    by (cases \<open>\<V>\<close>; auto simp: in_dom_m_lookup_iff)
qed

lemma term_mcmp_spec:
  assumes \<open>term_valid \<V> x\<close> \<open>term_valid \<V> y\<close>
  shows \<open>term_mcmp \<V> x y \<le> SPEC (\<lambda>b. b \<longleftrightarrow> term_cmp \<V> x y)\<close>
  unfolding term_mcmp_def
  apply (refine_vcg
    perfect_shared_term_order_rel_s_perfect_shared_term_order_rel[OF V_rel
      term_valid_monom_rel(1)[OF assms(1)]
      term_valid_monom_rel(1)[OF assms(2)],
      THEN order_trans]
  )
  unfolding conc_Id id_apply
  apply (rule perfect_shared_term_order_rel_spec[unfolded conc_Id id_apply,
    THEN order_trans])
  apply (rule term_valid_monom_rel(2)[OF assms(1)])
  apply (rule term_valid_monom_rel(2)[OF assms(2)])
  apply (rule SPEC_rule)
  apply (rename_tac b, case_tac b)
  by (auto simp: term_cmp_def pw_le_iff refine_pw_simps)
    (meson lexord_irreflexive term_order_rel_trans var_order_rel_antisym)+

interpretation term_sort: mcmp_env \<open>term_cmp \<V>\<close> \<open>term_valid \<V>\<close> \<open>term_mcmp \<V>\<close>
  apply unfold_locales
  subgoal for x y using term_mcmp_spec by blast
  subgoal for x y z
    by (metis Un_iff pair_in_Id_conv term_cmp_def term_order_rel_trans)
  subgoal for x y
    by (metis Un_iff lexord_linear pair_in_Id_conv term_cmp_def
    var_roder_rel_total)
  done

lemma msort_monoms_sort_poly_spec:
  assumes \<open>(xs, xs') \<in> perfectly_shared_polynom \<V>\<close>
    and \<open>vars_llist xs' \<subseteq> set_mset \<V>\<D>\<close>
  shows \<open>msort_monoms \<V> xs \<le> \<Down>(perfectly_shared_polynom \<V>) (sort_poly_spec xs')\<close>
proof -
  have valid: \<open>\<forall>a\<in>set xs. term_valid \<V> a\<close>
  proof (intro ballI)
    fix a assume \<open>a \<in> set xs\<close>
    then obtain a' where a': \<open>(a, a') \<in> perfectly_shared_monom \<V> \<times>\<^sub>r int_rel\<close>
      using in_set_rel_inD[OF assms(1)] by blast
    show \<open>term_valid \<V> a\<close>
      unfolding term_valid_def
    proof (intro ballI)
      fix v assume \<open>v \<in> set (fst a)\<close>
      moreover have \<open>(fst a, fst a') \<in> perfectly_shared_monom \<V>\<close>
        using a' by (cases a; cases a') (auto simp: prod_rel_def)
      ultimately obtain v' where \<open>(v, v') \<in> perfectly_shared_var_rel \<V>\<close>
        by (auto dest: in_set_rel_inD)
      then show \<open>v \<in># dom_m (fst (snd \<V>))\<close>
        by (cases \<V>) (auto simp: perfectly_shared_var_rel_def br_def)
    qed
  qed
  have poly_eq: \<open>xs' = map (\<lambda>x. (monom_abs \<V> (fst x), snd x)) xs\<close>
    using assms(1)
    apply (induction xs arbitrary: xs'; auto simp: list_rel_split_left_iff prod_rel_def monom_abs_def comp_def
        dest!: perfectly_shared_monom_eqD)
    by (smt (verit, del_insts) case_prod_conv fun_comp_eq_conv list_relE(3)
    mem_Collect_eq perfectly_shared_monom_eqD surj_pair)
  have rel: \<open>(r, map (\<lambda>x. (monom_abs \<V> (fst x), snd x)) r) \<in> perfectly_shared_polynom \<V>\<close>
    if \<open>\<forall>x\<in>set r. term_valid \<V> x\<close> for r
    using that
    by (induction r)
      (auto simp: list_rel_split_left_iff prod_rel_def case_prod_beta
        intro!: term_valid_monom_rel(1))
  have sorted_abs: \<open>sorted_wrt (rel2p (Id \<union> term_order_rel))
      (map fst (map (\<lambda>x. (monom_abs \<V> (fst x), snd x)) r))\<close>
    if sorted: \<open>sorted_wrt (term_cmp \<V>) r\<close> for r
  proof -
    have \<open>sorted_wrt
        (\<lambda>x y. rel2p (Id \<union> term_order_rel) (monom_abs \<V> (fst x)) (monom_abs \<V> (fst y))) r\<close>
      by (rule sorted_wrt_mono_rel[OF _ sorted]) (auto simp: term_cmp_def rel2p_def)
    then show ?thesis
      by (simp add: sorted_wrt_map comp_def)
  qed
  show ?thesis
    unfolding msort_monoms_def
    apply (rule term_sort.msort_spec[OF valid, THEN order_trans])
    unfolding sort_poly_spec_def
    apply (clarsimp simp: pw_le_iff refine_pw_simps)
    subgoal for r
      by (rule exI[of _ \<open>map (\<lambda>x. (monom_abs \<V> (fst x), snd x)) r\<close>])
        (use rel[of r] sorted_abs[of r] in \<open>auto simp: poly_eq\<close>)
    done
qed

end

text \<open>The coefficient-sort instance (replacing \<open>msort_coeff_s\<close>) is analogous:
  \<open>valid = (\<lambda>a. a \<in># dom_m (fst (snd \<V>)))\<close>,
  \<open>cmp = (\<lambda>a b. a = b \<or> var_order (fst (snd \<V>) \<propto> a) (fst (snd \<V>) \<propto> b))\<close>,
  \<open>mcmp\<close> via \<open>get_var_nameS\<close>; totality additionally needs injectivity of the
  lookup (perfectly_shared_var_rel_unique_right), which \<open>V_rel\<close> provides.

  Synthesis is per instance with \<open>\<V>\<close> explicit (no @{locale mcmp_env_impl}
  interpretation \<midarrow> the comparison impl needs heap ownership of \<open>\<V>\<close>, which a
  binary \<open>A\<^sup>k *\<^sub>a A\<^sup>k\<close> rule cannot capture): unfold \<open>msort_monoms_def\<close> together
  with the global program definitions \<open>mcmp_msort_def\<close>, \<open>mcmp_run_passes_def\<close>,
  \<open>mcmp_pass_def\<close>, \<open>mcmp_merge_while_def\<close>, \<open>mcmp_merge_while_inner_def\<close>
  (the locale-exported \<open>mcmp_env.msort_def\<close> etc. are unusable for unfolding:
  they are guarded by the locale predicate, which does not hold for arbitrary
  \<open>\<V>\<close>) and \<open>term_mcmp_def\<close>; the comparison then appears as
  \<open>perfect_shared_term_order_rel_s \<V> \<dots>\<close> with \<open>\<V>\<close> a real argument, so the
  existing impl rule (perfect_shared_term_order_rel_s_impl) applies.
  See the \<open>msort_coeffs\<close> synthesis chain below for a worked instance.\<close>


lemma perfectly_shared_var_rel_unique_left:
  \<open>(x, y) \<in> perfectly_shared_var_rel \<V> \<Longrightarrow> (x, y') \<in> perfectly_shared_var_rel \<V> \<Longrightarrow> y = y'\<close>
  using perfectly_shared_monom_unique_left[of \<open>[x]\<close>  \<open>[y]\<close> \<V> \<open>[y']\<close>] by auto

lemma perfectly_shared_var_rel_unique_right:
  \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel \<Longrightarrow> (x, y) \<in> perfectly_shared_var_rel \<V> \<Longrightarrow> (x', y) \<in> perfectly_shared_var_rel \<V> \<Longrightarrow> x = x'\<close>
  using perfectly_shared_monom_unique_right[of \<V> \<D>\<V> \<open>[x]\<close>  \<open>[y]\<close>  \<open>[x']\<close>]
  by auto

text \<open>The definitions are made outside the \<open>V_rel\<close> context: a definition made
  inside a context with assumptions exports its \<open>_def\<close> fact guarded by those
  assumptions, which makes it unusable for \<open>unfolding\<close> in the \<open>sepref\<close>
  syntheses below.\<close>

definition coeff_cmp :: \<open>(nat, string) shared_vars \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>coeff_cmp \<V> a b \<equiv> a = b \<or> var_order (fst (snd \<V>) \<propto> a) (fst (snd \<V>) \<propto> b)\<close>

definition coeff_valid :: \<open>(nat, string) shared_vars \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>coeff_valid \<V> a \<equiv> a \<in># dom_m (fst (snd \<V>))\<close>

definition coeff_mcmp :: \<open>(nat, string) shared_vars \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres\<close> where
  \<open>coeff_mcmp \<V> a b = do {
    x \<leftarrow> get_var_nameS \<V> a;
    y \<leftarrow> get_var_nameS \<V> b;
    RETURN (a = b \<or> var_order x y)
  }\<close>

definition msort_coeffs :: \<open>(nat, string) shared_vars \<Rightarrow> nat list \<Rightarrow> nat list nres\<close> where
  \<open>msort_coeffs \<V> xs = mcmp_msort (coeff_cmp \<V>) (coeff_valid \<V>) (coeff_mcmp \<V>) xs\<close>

context
  fixes \<V> :: \<open>(nat, string) shared_vars\<close> and \<V>\<D> :: \<open>(nat, string) vars\<close>
  assumes V_rel: \<open>(\<V>, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close>
begin

lemma coeff_valid_var_rel:
  \<open>coeff_valid \<V> a \<Longrightarrow> (a, fst (snd \<V>) \<propto> a) \<in> perfectly_shared_var_rel \<V>\<close>
  by (cases \<V>; auto simp: coeff_valid_def perfectly_shared_var_rel_def br_def)

lemma coeff_mcmp_spec:
  assumes \<open>coeff_valid \<V> x\<close> \<open>coeff_valid \<V> y\<close>
  shows \<open>coeff_mcmp \<V> x y \<le> SPEC (\<lambda>b. b \<longleftrightarrow> coeff_cmp \<V> x y)\<close>
  using assms
  unfolding coeff_mcmp_def get_var_nameS_def coeff_valid_def coeff_cmp_def
  by refine_vcg auto

lemma coeff_cmp_trans:
  assumes \<open>coeff_cmp \<V> x y\<close> \<open>coeff_cmp \<V> y z\<close>
  shows \<open>coeff_cmp \<V> x z\<close>
  using assms unfolding coeff_cmp_def rel2p_def
  by (metis transD trans_var_order_rel)

lemma coeff_cmp_total:
  assumes \<open>coeff_valid \<V> x\<close> \<open>coeff_valid \<V> y\<close>
  shows \<open>coeff_cmp \<V> x y \<or> coeff_cmp \<V> y x\<close>
proof -
  have \<open>fst (snd \<V>) \<propto> x = fst (snd \<V>) \<propto> y \<Longrightarrow> x = y\<close>
    using perfectly_shared_var_rel_unique_right[OF V_rel]
      coeff_valid_var_rel[OF assms(1)] coeff_valid_var_rel[OF assms(2)]
    by metis
  then show ?thesis
    unfolding coeff_cmp_def
    using var_roder_rel_total[of \<open>fst (snd \<V>) \<propto> x\<close> \<open>fst (snd \<V>) \<propto> y\<close>]
    by (auto simp: rel2p_def)
qed

interpretation coeff_sort: mcmp_env \<open>coeff_cmp \<V>\<close> \<open>coeff_valid \<V>\<close> \<open>coeff_mcmp \<V>\<close>
  apply unfold_locales
  subgoal for x y using coeff_mcmp_spec by blast
  subgoal for x y z using coeff_cmp_trans by blast
  subgoal for x y using coeff_cmp_total by blast
  done

lemma msort_coeffs_sort_coeff:
  assumes \<open>(xs, xs') \<in> perfectly_shared_monom \<V>\<close>
    and \<open>set xs' \<subseteq> set_mset \<V>\<D>\<close>
  shows \<open>msort_coeffs \<V> xs \<le> \<Down>(perfectly_shared_monom \<V>) (sort_coeff xs')\<close>
proof -
  have valid: \<open>\<forall>v\<in>set xs. coeff_valid \<V> v\<close>
  proof (intro ballI)
    fix v assume \<open>v \<in> set xs\<close>
    then obtain v' where \<open>(v, v') \<in> perfectly_shared_var_rel \<V>\<close>
      using in_set_rel_inD[OF assms(1)] by blast
    then show \<open>coeff_valid \<V> v\<close>
      by (cases \<V>; auto simp: coeff_valid_def perfectly_shared_var_rel_def br_def)
  qed
  have monom_eq: \<open>xs' = map (\<lambda>v. fst (snd \<V>) \<propto> v) xs\<close>
    using perfectly_shared_monom_eqD[OF assms(1)] by (simp add: comp_def)
  have rel: \<open>(r, map (\<lambda>v. fst (snd \<V>) \<propto> v) r) \<in> perfectly_shared_monom \<V>\<close>
    if \<open>\<forall>v\<in>set r. coeff_valid \<V> v\<close> for r
    using that
    by (induction r) (auto simp: list_rel_split_left_iff intro!: coeff_valid_var_rel)
  have sorted_abs: \<open>sorted_wrt (rel2p (Id \<union> var_order_rel)) (map (\<lambda>v. fst (snd \<V>) \<propto> v) r)\<close>
    if sorted: \<open>sorted_wrt (coeff_cmp \<V>) r\<close> for r
  proof -
    have \<open>sorted_wrt
        (\<lambda>v w. rel2p (Id \<union> var_order_rel) (fst (snd \<V>) \<propto> v) (fst (snd \<V>) \<propto> w)) r\<close>
      by (rule sorted_wrt_mono_rel[OF _ sorted]) (auto simp: coeff_cmp_def rel2p_def)
    then show ?thesis
      by (simp add: sorted_wrt_map)
  qed
  show ?thesis
    unfolding msort_coeffs_def
    apply (rule coeff_sort.msort_spec[OF valid, THEN order_trans])
    unfolding sort_coeff_def
    apply (clarsimp simp: pw_le_iff refine_pw_simps)
    subgoal for r
      by (rule exI[of _ \<open>map (\<lambda>v. fst (snd \<V>) \<propto> v) r\<close>])
        (use rel[of r] sorted_abs[of r] in \<open>auto simp: monom_eq\<close>)
    done
qed

end

definition sort_all_coeffs_s :: \<open>(nat,string)shared_vars \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial nres\<close> where
\<open>sort_all_coeffs_s \<V> xs = monadic_nfoldli xs (\<lambda>_. RETURN True) (\<lambda>(a, n) b. do {ASSERT((a,n)\<in>set xs);a \<leftarrow> msort_coeffs \<V> a; RETURN ((a, n) # b)}) []\<close>

fun merge_coeffs0_s :: \<open>sllist_polynomial \<Rightarrow> sllist_polynomial\<close> where
  \<open>merge_coeffs0_s[] = []\<close> |
  \<open>merge_coeffs0_s [(xs, n)] = (if n = 0 then [] else [(xs, n)])\<close> |
  \<open>merge_coeffs0_s ((xs, n) # (ys, m) # p) =
    (if xs = ys
    then if n + m \<noteq> 0 then merge_coeffs0_s ((xs, n + m) # p) else merge_coeffs0_s p
    else if n = 0 then merge_coeffs0_s ((ys, m) # p)
      else(xs, n) # merge_coeffs0_s ((ys, m) # p))\<close>

lemma merge_coeffs0_s_merge_coeffs0:
  fixes xs :: \<open>sllist_polynomial\<close> and
    \<V> :: \<open>(nat,string)shared_vars\<close>
  assumes
    \<open>(xs, xs') \<in> perfectly_shared_polynom \<V>\<close> and
    \<V>: \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
  shows \<open>(merge_coeffs0_s xs, merge_coeffs0 xs') \<in> perfectly_shared_polynom \<V>\<close>
  using assms
  apply (induction xs' arbitrary: xs rule: merge_coeffs0.induct)
  subgoal by auto
  subgoal by (auto simp: list_rel_split_left_iff)
  subgoal premises p for xs n ys m p xsa
    using p(1)[of \<open>(_, _ + _) # tl (tl xsa)\<close>] p(2)[of \<open>tl (tl xsa)\<close>] p(3)[of \<open>tl xsa\<close>] p(4)[of \<open>tl xsa\<close>] p(5-)
    using perfectly_shared_monom_unique_right[OF \<V>, of _ xs]
      perfectly_shared_monom_unique_left[of \<open>fst (hd xsa)\<close> _ \<V>]
    apply (auto 4 1 simp: list_rel_split_left_iff
      dest: )
    apply smt
    done
 done

lemma list_rel_mono_strong: \<open>A \<in> \<langle>R\<rangle>list_rel \<Longrightarrow> (\<And>xs. fst xs \<in> set (fst A) \<Longrightarrow> snd xs \<in> set (snd A) \<Longrightarrow> xs \<in> R \<Longrightarrow> xs \<in> R') \<Longrightarrow> A \<in> \<langle>R'\<rangle>list_rel\<close>
  unfolding list_rel_def
  apply (cases A)
  apply (simp add: list.rel_mono_strong)
  done

definition full_normalize_poly_s where
  \<open>full_normalize_poly_s \<V> p = do {
     p \<leftarrow> sort_all_coeffs_s \<V> p;
     p \<leftarrow> msort_monoms \<V> p;
    RETURN (merge_coeffs0_s p)
  }\<close>

lemma sort_all_coeffs_s_sort_all_coeffs:
  fixes xs :: \<open>sllist_polynomial\<close> and
    \<V> :: \<open>(nat,string)shared_vars\<close>
  assumes
    \<open>(xs, xs') \<in> perfectly_shared_polynom \<V>\<close> and
    \<V>: \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>vars_llist xs' \<subseteq> set_mset \<D>\<V>\<close>
  shows \<open>sort_all_coeffs_s \<V> xs \<le> \<Down>(perfectly_shared_polynom \<V>) (sort_all_coeffs xs')\<close>
proof -
  have [refine]: \<open>(xs, xs') \<in> \<langle>{(a,b). a\<in>set xs \<and> b\<in>set xs' \<and> (a,b)\<in> perfectly_shared_monom \<V> \<times>\<^sub>r int_rel}\<rangle>list_rel\<close>
    by (rule list_rel_mono_strong[OF assms(1)])
     (use assms(3) in auto)

  show ?thesis
    unfolding sort_all_coeffs_s_def sort_all_coeffs_def
    apply (refine_vcg \<V> msort_coeffs_sort_coeff[OF \<V>])
    apply (use assms in \<open>(force simp: vars_llist_def dest!: split_list)\<close>)+
    done
qed

definition vars_llist_in_s :: \<open>(nat, string) shared_vars \<Rightarrow> llist_polynomial \<Rightarrow> bool\<close> where
  \<open>vars_llist_in_s = (\<lambda>(\<V>,\<D>,\<D>') p. vars_llist p \<subseteq> set_mset (dom_m \<D>'))\<close>

lemma vars_llist_in_s_vars_llist[simp]:
  assumes \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
  shows \<open>vars_llist_in_s \<V> p \<longleftrightarrow> vars_llist p \<subseteq> set_mset \<D>\<V>\<close>
  using assms unfolding perfectly_shared_vars_rel_def perfectly_shared_vars_def vars_llist_in_s_def
  by auto

definition (in -)add_poly_l_s :: \<open>(nat,string)shared_vars \<Rightarrow> sllist_polynomial \<times> sllist_polynomial \<Rightarrow> sllist_polynomial nres\<close> where
  \<open>add_poly_l_s \<D> = REC\<^sub>T
  (\<lambda>add_poly_l (p, q).
  case (p,q) of
    (p, []) \<Rightarrow> RETURN p
    | ([], q) \<Rightarrow> RETURN q
    | ((xs, n) # p, (ys, m) # q) \<Rightarrow> do {
    comp \<leftarrow> perfect_shared_term_order_rel_s \<D> xs ys;
    if comp = EQUAL then if n + m = 0 then add_poly_l (p, q)
    else do {
      pq \<leftarrow> add_poly_l (p, q);
      RETURN ((xs, n + m) # pq)
    }
    else if comp = LESS
    then do {
      pq \<leftarrow> add_poly_l (p, (ys, m) # q);
      RETURN ((xs, n) # pq)
    }
    else do {
      pq \<leftarrow> add_poly_l ((xs, n) # p, q);
      RETURN ((ys, m) # pq)
    }
  })\<close>

lemma add_poly_l_s_alt_def_aux:
  \<open>add_poly_l_s \<D> (p,q) = REC\<^sub>T (\<lambda>add_poly_l (p, q). doN {
    if q = [] then RETURN p
    else if p = [] then RETURN q
    else doN {
      ((xs, n),p) \<leftarrow> mop_list_pop_hd p;
      ((ys, m),q) \<leftarrow> mop_list_pop_hd q;
      comp \<leftarrow> perfect_shared_term_order_rel_s \<D> xs ys;
      if comp = EQUAL then if n + m = 0 then add_poly_l (p, q)
      else do {
        pq \<leftarrow> add_poly_l (p, q);
        RETURN ((xs, n + m) # pq)
      }
      else if comp = LESS
      then do {
        pq \<leftarrow> add_poly_l (p, (ys, m) # q);
        RETURN ((xs, n) # pq)
      }
      else do {
        pq \<leftarrow> add_poly_l ((xs, n) # p, q);
        RETURN ((ys, m) # pq)
      }
    }
  }) (COPY p, COPY q)\<close>
  unfolding add_poly_l_s_def COPY_def
  apply (rule arg_cong[where f = \<open>\<lambda>F. REC\<^sub>T F (p, q)\<close>])
  apply (intro ext)
  subgoal for f x
    apply (cases x)
    subgoal for p q
      by (cases p; cases q)
        (auto simp: mop_list_pop_hd_def pw_eq_iff refine_pw_simps split: prod.splits)
    done
  done

lemma add_poly_l_s_alt_def:
  \<open>add_poly_l_s \<D> = (\<lambda>(p, q). REC\<^sub>T (\<lambda>add_poly_l (p, q). doN {
    if q = [] then RETURN p
    else if p = [] then RETURN q
    else doN {
      ((xs, n),p) \<leftarrow> mop_list_pop_hd p;
      ((ys, m),q) \<leftarrow> mop_list_pop_hd q;
      comp \<leftarrow> perfect_shared_term_order_rel_s \<D> (COPY xs) (COPY ys);
      if comp = EQUAL then if n + m = 0 then add_poly_l (p, q)
      else do {
        pq \<leftarrow> add_poly_l (p, q);
        RETURN ((xs, n + m) # pq)
      }
      else if comp = LESS
      then do {
        pq \<leftarrow> add_poly_l (p, (ys, m) # q);
        RETURN ((xs, n) # pq)
      }
      else do {
        pq \<leftarrow> add_poly_l ((xs, n) # p, q);
        RETURN ((ys, m) # pq)
      }
    }
  }) (p, q))\<close>
  unfolding COPY_def
  by (intro ext) (clarsimp simp: add_poly_l_s_alt_def_aux split: prod.splits)

lemma add_poly_l_s_add_poly_l:
  fixes xs :: \<open>sllist_polynomial \<times> sllist_polynomial\<close>
  assumes \<open>(\<V>, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>(xs, xs') \<in> perfectly_shared_polynom \<V> \<times>\<^sub>r perfectly_shared_polynom \<V>\<close>
  shows \<open>add_poly_l_s \<V> xs \<le> \<Down>(perfectly_shared_polynom \<V>) (add_poly_l_prep \<V>\<D> xs')\<close>
proof -
  have x: \<open>x \<in> \<langle>perfectly_shared_monom \<V> \<times>\<^sub>r int_rel\<rangle>list_rel \<Longrightarrow> x \<in> \<langle>perfectly_shared_monom \<V> \<times>\<^sub>r int_rel\<rangle>list_rel\<close> for x
    by auto
  show ?thesis
    unfolding add_poly_l_s_def add_poly_l_prep_def
    apply (refine_rcg assms perfect_shared_term_order_rel_s_perfect_shared_term_order_rel)
    apply (rule x)
    subgoal by auto
    apply (rule x)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule x)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
      (*many boring goals, some require unification*)
    by (auto)
qed

definition (in -) mult_monoms_s :: \<open>(nat,string)shared_vars \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list nres\<close> where
  \<open>mult_monoms_s \<D> xs ys = REC\<^sub>T (\<lambda>f (xs, ys).
 do {
    if xs = [] then RETURN ys
    else if ys = [] then RETURN xs
    else do {
      ASSERT(xs \<noteq> [] \<and> ys \<noteq> []);
      comp \<leftarrow> perfect_shared_var_order_s \<D> (hd xs) (hd ys);
      if comp = EQUAL then do {
        pq \<leftarrow> f (tl xs, tl ys);
        RETURN (hd xs # pq)
      }
      else if comp = LESS then do {
        pq \<leftarrow> f (tl xs, ys);
        RETURN (hd xs # pq)
      }
      else do {
        pq \<leftarrow> f (xs, tl ys);
        RETURN (hd ys # pq)
      }
   }
 }) (xs, ys)\<close>

lemma mult_monoms_s_simps:
  \<open>mult_monoms_s \<V> xs ys =
 do {
    if xs = [] then RETURN ys
    else if ys = [] then RETURN xs
    else do {
      ASSERT(xs \<noteq> [] \<and> ys \<noteq> []);
      comp \<leftarrow> perfect_shared_var_order_s \<V> (hd xs) (hd ys);
      if comp = EQUAL then do {
        pq \<leftarrow> mult_monoms_s \<V> (tl xs) (tl ys);
        RETURN (hd xs # pq)
      }
      else if comp = LESS then do {
        pq \<leftarrow> mult_monoms_s \<V> (tl xs) ys;
        RETURN (hd xs # pq)
      }
      else do {
        pq \<leftarrow> mult_monoms_s \<V> xs (tl ys);
        RETURN (hd ys # pq)
      }
   }
 }\<close>
  apply (subst mult_monoms_s_def)
  apply (subst RECT_unfold, refine_mono)
  unfolding prod.case[of _ \<open>(xs,ys)\<close>]
  apply (subst mult_monoms_s_def[symmetric])+
  apply (auto intro!: bind_cong[OF refl])
  done

lemma mult_monoms_s_mult_monoms_prep:
  fixes xs
  assumes \<open>(\<V>, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>(xs, xs') \<in> perfectly_shared_monom \<V>\<close>
    \<open>(ys, ys') \<in> perfectly_shared_monom \<V>\<close>
  shows \<open>mult_monoms_s \<V> xs ys \<le> \<Down>(perfectly_shared_monom \<V>) ((mult_monoms_prep \<V>\<D> xs' ys'))\<close>
proof -
  have [refine]: \<open>((xs, ys), xs', ys') \<in> perfectly_shared_monom \<V> \<times>\<^sub>r perfectly_shared_monom \<V>\<close>
    using assms by auto
  have x: \<open>a \<le> \<Down> (perfectly_shared_monom \<V>) b \<Longrightarrow> a \<le> \<Down> (perfectly_shared_monom \<V>) b\<close> for a b
    by auto
  show ?thesis
    using assms unfolding mult_monoms_s_def mult_monoms_prep_def
    apply (refine_vcg perfect_shared_var_order_s_perfect_shared_var_order)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: neq_Nil_conv)
    subgoal by (auto simp: neq_Nil_conv)
    subgoal by auto
    apply (rule x)
    subgoal by (auto simp: neq_Nil_conv)
    subgoal by (auto simp: neq_Nil_conv)
    subgoal by auto
    apply (rule x)
    subgoal by (auto simp: neq_Nil_conv)
    subgoal by (auto simp: neq_Nil_conv)
    apply (rule x)
    subgoal by (auto simp: neq_Nil_conv)
    subgoal by (auto simp: neq_Nil_conv)
    done
qed


definition (in -) mult_term_s
  :: \<open>(nat,string)shared_vars\<Rightarrow> sllist_polynomial \<Rightarrow>  _ \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial nres\<close>
where
  \<open>mult_term_s = (\<lambda>\<V> qs (p, m) b. nfoldli qs (\<lambda>_. True) (\<lambda>(q, n) b. do {pq \<leftarrow> mult_monoms_s \<V> p q; RETURN ((pq, m * n) # b)}) b)\<close>

definition mult_poly_s :: \<open>(nat,string) shared_vars\<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial nres\<close> where
  \<open>mult_poly_s \<V> p q = nfoldli p (\<lambda>_. True) (mult_term_s \<V> q) []\<close>

lemma mult_term_s_mult_monoms_prop:
  fixes xs
  assumes \<open>(\<V>, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>(xs, xs') \<in> perfectly_shared_polynom \<V>\<close>
    \<open>(ys, ys') \<in> perfectly_shared_monom \<V> \<times>\<^sub>r int_rel\<close>
    \<open>(zs, zs') \<in> perfectly_shared_polynom \<V>\<close>
  shows \<open>mult_term_s \<V> xs ys zs \<le> \<Down>(perfectly_shared_polynom \<V>) (mult_monoms_prop \<V>\<D> xs' ys' zs')\<close>
proof -
  show ?thesis
    using assms
    unfolding mult_term_s_def mult_monoms_prop_def
    by (refine_rcg mult_monoms_s_mult_monoms_prep)
     auto
qed

lemma mult_poly_s_mult_poly_raw_prop:
  fixes xs
  assumes \<open>(\<V>, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>(xs, xs') \<in> perfectly_shared_polynom \<V>\<close>
    \<open>(ys, ys') \<in> perfectly_shared_polynom \<V>\<close>
  shows \<open>mult_poly_s \<V> xs ys \<le> \<Down>(perfectly_shared_polynom \<V>) (mult_poly_raw_prop \<V>\<D> xs' ys')\<close>
proof -
  show ?thesis
    using assms
    unfolding mult_poly_s_def mult_poly_raw_prop_def
    by (refine_rcg mult_term_s_mult_monoms_prop)
     auto
qed

lemmas [safe_constraint_rules] =
  CN_FALSEI[of is_pure monom_s_assn]
  CN_FALSEI[of is_pure poly_s_assn]

definition mnml_s_free :: \<open>_ \<Rightarrow> unit llM\<close> where [llvm_code]:
  \<open>mnml_s_free \<equiv> \<lambda>(m, c). doM { snhm.val.cl_free m; sbi_free c }\<close>

lemma mnml_s_free_rule[sepref_frame_free_rules]:
  \<open>MK_FREE (monom_s_assn \<times>\<^sub>a sbi_assn) mnml_s_free\<close>
  unfolding mnml_s_free_def
  by (rule mk_free_pair[OF snhm.val.cl_assn_free sbi_free_rule])

definition mnml_s_copy where [llvm_code, llvm_inline]:
  \<open>mnml_s_copy \<equiv> \<lambda>(m, c). doM { m' \<leftarrow> snhm.val.cl_copy m; c' \<leftarrow> sbi_copy c; Mreturn (m', c') }\<close>

lemma mnml_s_copy_rule[vcg_rules]: \<open>llvm_htriple
  ((monom_s_assn \<times>\<^sub>a sbi_assn) x c) (mnml_s_copy c)
  (\<lambda>r. (monom_s_assn \<times>\<^sub>a sbi_assn) x c ** (monom_s_assn \<times>\<^sub>a sbi_assn) x r)\<close>
  unfolding mnml_s_copy_def
  apply (cases x; cases c; simp only: prod_assn_pair_conv prod.case)
  by vcg

lemma mnml_s_copy_rule'[vcg_rules]: \<open>llvm_htriple
  (monom_s_assn m mi ** sbi_assn n ni) (mnml_s_copy (mi, ni))
  (\<lambda>r. monom_s_assn m mi ** sbi_assn n ni ** (monom_s_assn \<times>\<^sub>a sbi_assn) (m, n) r)\<close>
  using mnml_s_copy_rule[of \<open>(m, n)\<close> \<open>(mi, ni)\<close>] by simp

lemmas mnml_s_copy_rule''[vcg_rules] = mnml_s_copy_rule'[unfolded pure_def]

lemma mnml_s_copy_hnr[sepref_fr_rules]:
  \<open>(mnml_s_copy, RETURN o COPY) \<in> (monom_s_assn \<times>\<^sub>a sbi_assn)\<^sup>k \<rightarrow>\<^sub>a (monom_s_assn \<times>\<^sub>a sbi_assn)\<close>
  by (sepref_to_hoare; vcg)

interpretation poly_s: copyable_assn \<open>monom_s_assn \<times>\<^sub>a sbi_assn\<close> mnml_s_free mnml_s_copy
  apply unfold_locales
  subgoal by (rule mnml_s_free_rule)
  subgoal by (rule mnml_s_copy_hnr)
  done

section \<open>The \<open>ordered\<close> Result Type as a Tag Byte\<close>

definition ordered_code :: \<open>ordered \<Rightarrow> 8 word\<close> where
  \<open>ordered_code s = (case s of EQUAL \<Rightarrow> 0 | LESS \<Rightarrow> 1 | GREATER \<Rightarrow> 2 | UNKNOWN \<Rightarrow> 3)\<close>

lemma ordered_code_simps[simp]:
  \<open>ordered_code EQUAL = 0\<close>
  \<open>ordered_code LESS = 1\<close>
  \<open>ordered_code GREATER = 2\<close>
  \<open>ordered_code UNKNOWN = 3\<close>
  by (auto simp: ordered_code_def)

lemma ordered_code_inj[simp]: \<open>ordered_code a = ordered_code b \<longleftrightarrow> a = b\<close>
  by (cases a; cases b) auto

definition ordered_rel :: \<open>(8 word \<times> ordered) set\<close> where
  \<open>ordered_rel = {(w, s). w = ordered_code s}\<close>

abbreviation ordered_assn :: \<open>ordered \<Rightarrow> 8 word \<Rightarrow> assn\<close> where
  \<open>ordered_assn \<equiv> pure ordered_rel\<close>

context begin
interpretation llvm_prim_arith_setup .

lemma ll_icmp_eq_word_rule:
  \<open>llvm_htriple \<box> (ll_icmp_eq (a::'l::len word) b) (\<lambda>r. \<upharpoonleft>bool.assn (a = b) r)\<close>
  supply [simp] = bool.assn_def by vcg

end

sepref_register EQUAL LESS GREATER UNKNOWN get_var_nameS perfect_shared_var_order_s
  perfect_shared_term_order_rel_s

lemma ordered_constants_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0), uncurry0 (RETURN EQUAL)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a ordered_assn\<close>
  \<open>(uncurry0 (Mreturn 1), uncurry0 (RETURN LESS)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a ordered_assn\<close>
  \<open>(uncurry0 (Mreturn 2), uncurry0 (RETURN GREATER)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a ordered_assn\<close>
  \<open>(uncurry0 (Mreturn 3), uncurry0 (RETURN UNKNOWN)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a ordered_assn\<close>
  by (sepref_to_hoare;
    vcg; auto simp: mem_alloc_pure_reassembly pure_def ordered_rel_def)+

lemma ordered_eq_hnr[sepref_fr_rules]:
  \<open>(uncurry ll_icmp_eq, uncurry (RETURN oo (=)))
    \<in> ordered_assn\<^sup>k *\<^sub>a ordered_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [vcg_rules] = ll_icmp_eq_word_rule
  apply sepref_to_hoare
  by (vcg; auto simp: mem_alloc_pure_reassembly pure_def ordered_rel_def
    bool1_rel_unfolds bool.assn_def)

definition is_EQUAL :: \<open>ordered \<Rightarrow> bool\<close> where [simp]: \<open>is_EQUAL s \<longleftrightarrow> s = EQUAL\<close>
definition is_LESS :: \<open>ordered \<Rightarrow> bool\<close> where [simp]: \<open>is_LESS s \<longleftrightarrow> s = LESS\<close>
definition is_GREATER :: \<open>ordered \<Rightarrow> bool\<close> where [simp]: \<open>is_GREATER s \<longleftrightarrow> s = GREATER\<close>
definition is_UNKNOWN :: \<open>ordered \<Rightarrow> bool\<close> where [simp]: \<open>is_UNKNOWN s \<longleftrightarrow> s = UNKNOWN\<close>

sepref_register is_EQUAL is_LESS is_GREATER is_UNKNOWN

lemma ordered_discriminators_hnr[sepref_fr_rules]:
  \<open>(\<lambda>w. ll_icmp_eq w 0, RETURN o is_EQUAL) \<in> ordered_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  \<open>(\<lambda>w. ll_icmp_eq w 1, RETURN o is_LESS) \<in> ordered_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  \<open>(\<lambda>w. ll_icmp_eq w 2, RETURN o is_GREATER) \<in> ordered_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  \<open>(\<lambda>w. ll_icmp_eq w 3, RETURN o is_UNKNOWN) \<in> ordered_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [vcg_rules] = ll_icmp_eq_word_rule
  by (sepref_to_hoare;
    vcg;
    auto simp: mem_alloc_pure_reassembly pure_def ordered_rel_def
      bool1_rel_unfolds bool.assn_def;
    case_tac x; auto)+

lemma fold_ordered_discriminators:
  \<open>(s = EQUAL) = is_EQUAL s\<close>
  \<open>(s = LESS) = is_LESS s\<close>
  \<open>(s = GREATER) = is_GREATER s\<close>
  \<open>(s = UNKNOWN) = is_UNKNOWN s\<close>
  \<open>(s \<noteq> EQUAL) = (\<not>is_EQUAL s)\<close>
  \<open>(s \<noteq> LESS) = (\<not>is_LESS s)\<close>
  \<open>(s \<noteq> GREATER) = (\<not>is_GREATER s)\<close>
  \<open>(s \<noteq> UNKNOWN) = (\<not>is_UNKNOWN s)\<close>
  by auto

lemma var_order_rel':
  \<open>(\<le>) = (\<lambda>x y. x = y \<or> (x,y) \<in> var_order_rel)\<close>
  apply (intro ext)
  apply (auto simp add: less_list_def less_eq_list_def
    lexordp_eq_conv_lexord lexordp_def var_order_rel_def
    lexordp_conv_lexord p2rel_def)
  using less_char_inst apply force
  using less_char_inst by force

lemma var_order_rel'':
  \<open>(x,y) \<in> var_order_rel \<longleftrightarrow> x < y\<close>
  by (metis leD less_than_char_linear lexord_linear neq_iff var_order_rel' var_order_rel_antisym
      var_order_rel_def)
term get_var_name_c_impl 
sepref_def perfect_shared_var_order_s_impl
  is \<open>uncurry2 perfect_shared_var_order_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k \<rightarrow>\<^sub>a ordered_assn\<close>
  unfolding perfect_shared_var_order_s_def perfectly_shared_strings_equal_l_def
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    var_order_rel''
  by sepref

lemmas [sepref_fr_rules] = perfect_shared_var_order_s_impl.refine

sepref_def perfect_shared_term_order_rel_s_impl
  is \<open>uncurry2 perfect_shared_term_order_rel_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a monom_s_assn\<^sup>d *\<^sub>a monom_s_assn\<^sup>d \<rightarrow>\<^sub>a ordered_assn\<close>
  unfolding perfect_shared_term_order_rel_s_alt_def
    fold_ordered_discriminators
  by sepref

lemmas [sepref_fr_rules] = perfect_shared_term_order_rel_s_impl.refine

sepref_def add_poly_l_prep_impl
  is \<open>uncurry add_poly_l_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a (poly_s_assn \<times>\<^sub>a poly_s_assn)\<^sup>d \<rightarrow>\<^sub>a poly_s_assn\<close>
  supply [[goals_limit=1]]
  unfolding add_poly_l_s_alt_def
    ls_emp ls_emp'
    fold_ordered_discriminators
  by sepref

text \<open>Pop-front form of the monomial product; the keep-mode signature is obtained by
  copying both monomials at entry.\<close>

lemma mult_monoms_s_alt_def:
  \<open>mult_monoms_s \<D> xs ys = do { xs \<leftarrow> RETURN (COPY xs); ys \<leftarrow> RETURN (COPY ys); REC\<^sub>T (\<lambda>f (xs, ys).
 do {
    if xs = [] then RETURN ys
    else if ys = [] then RETURN xs
    else do {
      ASSERT(xs \<noteq> [] \<and> ys \<noteq> []);
      (x, xs) \<leftarrow> mop_list_pop_hd xs;
      (y, ys) \<leftarrow> mop_list_pop_hd ys;
      comp \<leftarrow> perfect_shared_var_order_s \<D> x y;
      if comp = EQUAL then do {
        pq \<leftarrow> f (xs, ys);
        RETURN (x # pq)
      }
      else if comp = LESS then do {
        pq \<leftarrow> f (xs, y # ys);
        RETURN (x # pq)
      }
      else do {
        pq \<leftarrow> f (x # xs, ys);
        RETURN (y # pq)
      }
   }
 }) (xs, ys)}\<close>
proof -
  have 1: \<open>(\<lambda>f (xs, ys).
 do {
    if xs = [] then RETURN ys
    else if ys = [] then RETURN xs
    else do {
      ASSERT(xs \<noteq> [] \<and> ys \<noteq> []);
      (x, xs) \<leftarrow> mop_list_pop_hd xs;
      (y, ys) \<leftarrow> mop_list_pop_hd ys;
      comp \<leftarrow> perfect_shared_var_order_s \<D> x y;
      if comp = EQUAL then do {
        pq \<leftarrow> f (xs, ys);
        RETURN (x # pq)
      }
      else if comp = LESS then do {
        pq \<leftarrow> f (xs, y # ys);
        RETURN (x # pq)
      }
      else do {
        pq \<leftarrow> f (x # xs, ys);
        RETURN (y # pq)
      }
   }
 }) = (\<lambda>f (xs, ys).
 do {
    if xs = [] then RETURN ys
    else if ys = [] then RETURN xs
    else do {
      ASSERT(xs \<noteq> [] \<and> ys \<noteq> []);
      comp \<leftarrow> perfect_shared_var_order_s \<D> (hd xs) (hd ys);
      if comp = EQUAL then do {
        pq \<leftarrow> f (tl xs, tl ys);
        RETURN (hd xs # pq)
      }
      else if comp = LESS then do {
        pq \<leftarrow> f (tl xs, ys);
        RETURN (hd xs # pq)
      }
      else do {
        pq \<leftarrow> f (xs, tl ys);
        RETURN (hd ys # pq)
      }
   }
 })\<close>
    by (intro ext)
      (auto simp: mop_list_pop_hd_def pw_eq_iff refine_pw_simps
        split: prod.splits list.splits)
  show ?thesis
    unfolding COPY_def nres_monad1 1 mult_monoms_s_def ..
qed

sepref_def mult_monoms_s_impl
  is \<open>uncurry2 mult_monoms_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a monom_s_assn\<^sup>k *\<^sub>a monom_s_assn\<^sup>k \<rightarrow>\<^sub>a monom_s_assn\<close>
  supply [[goals_limit=1]]
  unfolding mult_monoms_s_alt_def
    ls_emp ls_emp' fold_ordered_discriminators
  by sepref

lemmas [sepref_fr_rules] =
  mult_monoms_s_impl.refine

sepref_register mult_monoms_s mult_term_s

lemma nfoldli_to_pop_RECT:
  fixes body :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'b nres\<close>
  shows \<open>nfoldli qs (\<lambda>_. True) body b = REC\<^sub>T (\<lambda>f (qs, b).
     if qs = [] then RETURN b
     else do {
       (x, qs) \<leftarrow> mop_list_pop_hd qs;
       b \<leftarrow> body x b;
       f (qs, b)
     }) (qs, b)\<close>
proof (induction qs arbitrary: b)
  case Nil
  show ?case
    by (subst RECT_unfold, refine_mono) auto
next
  case (Cons x qs)
  show ?case
    apply (subst RECT_unfold, refine_mono)
    apply (simp add: mop_list_pop_hd_def nfoldli_simps Cons.IH[symmetric]
      pw_eq_iff refine_pw_simps)
    done
qed

lemma mult_term_s_alt_def:
  \<open>mult_term_s = (\<lambda>\<V> qs (p, m) b. do {
     qs \<leftarrow> RETURN (COPY qs);
     REC\<^sub>T (\<lambda>f (qs, b).
       if qs = [] then RETURN b
       else do {
         ((q, n), qs) \<leftarrow> mop_list_pop_hd qs;
         pq \<leftarrow> mult_monoms_s \<V> p q;
         f (qs, ((pq, m * n) # b))
       }) (qs, b)})\<close>
proof -
  show ?thesis
    unfolding mult_term_s_def COPY_def nres_monad1
    apply (intro ext)
    subgoal for \<V> qs pm b
      apply (cases pm)
      apply (simp only: prod.case)
      apply (subst nfoldli_to_pop_RECT)
      apply (rule arg_cong2[where f = \<open>REC\<^sub>T\<close>])
      apply (auto simp: mop_list_pop_hd_def pw_eq_iff refine_pw_simps
          intro!: ext split: prod.splits)
      apply blast
      by blast
    done
qed

sepref_def mult_term_s_impl
  is \<open>uncurry3 mult_term_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k *\<^sub>a (monom_s_assn \<times>\<^sub>a sbi_assn)\<^sup>k *\<^sub>a poly_s_assn\<^sup>d \<rightarrow>\<^sub>a poly_s_assn\<close>
  supply [[goals_limit=1]]
  unfolding mult_term_s_alt_def
    ls_emp ls_emp'
  by sepref

lemmas [sepref_fr_rules] =
  mult_term_s_impl.refine

lemma mult_poly_s_alt_def:
  \<open>mult_poly_s \<V> p q = do {
     p \<leftarrow> RETURN (COPY p);
     REC\<^sub>T (\<lambda>f (p, b).
       if p = [] then RETURN b
       else do {
         (pm, p) \<leftarrow> mop_list_pop_hd p;
         b \<leftarrow> mult_term_s \<V> q pm b;
         f (p, b)
       }) (p, [])}\<close>
  unfolding mult_poly_s_def COPY_def nres_monad1
  by (subst nfoldli_to_pop_RECT) (rule refl)

sepref_def mult_poly_s_impl
  is \<open>uncurry2 mult_poly_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a poly_s_assn\<close>
  supply [[goals_limit=1]]
  unfolding mult_poly_s_alt_def
    ls_emp ls_emp'
  by sepref

lemmas [sepref_fr_rules] =
  mult_poly_s_impl.refine

section \<open>Refinement of Sorting  Implementation\<close>


fun merge_coeffs_s :: \<open>sllist_polynomial \<Rightarrow> sllist_polynomial\<close> where
  \<open>merge_coeffs_s [] = []\<close> |
  \<open>merge_coeffs_s [(xs, n)] = [(xs, n)]\<close> |
  \<open>merge_coeffs_s ((xs, n) # (ys, m) # p) =
    (if xs = ys
    then if n + m \<noteq> 0 then merge_coeffs_s ((xs, n + m) # p) else merge_coeffs_s p
      else (xs, n) # merge_coeffs_s ((ys, m) # p))\<close>

lemma perfectly_shared_merge_coeffs_merge_coeffs:
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(xs, xs') \<in> perfectly_shared_polynom \<V>\<close>
  shows \<open>(merge_coeffs_s xs, merge_coeffs xs') \<in> (perfectly_shared_polynom \<V>)\<close>
  using assms
  apply (induction xs arbitrary: xs' rule: merge_coeffs_s.induct)
  subgoal
    by auto
  subgoal
    by (auto simp: list_rel_split_right_iff)
  subgoal
    by(auto simp: list_rel_split_right_iff dest: perfectly_shared_monom_unique_left
      perfectly_shared_monom_unique_right)
  done

definition normalize_poly_s :: \<open>_\<close> where
  \<open>normalize_poly_s \<V> p =  do {
  p \<leftarrow> msort_monoms \<V> p;
  RETURN (merge_coeffs_s p)
  }\<close>

lemma normalize_poly_s_normalize_poly_s:
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(xs, xs') \<in> perfectly_shared_polynom \<V>\<close> and
    \<open>vars_llist xs' \<subseteq> set_mset \<D>\<V>\<close>
  shows \<open>normalize_poly_s \<V> xs \<le> \<Down> (perfectly_shared_polynom \<V>) (normalize_poly xs')\<close>
  unfolding normalize_poly_s_def normalize_poly_def
  by (refine_rcg msort_monoms_sort_poly_spec assms
    perfectly_shared_merge_coeffs_merge_coeffs)

definition mult_poly_full_s :: \<open>_\<close> where
  \<open>mult_poly_full_s \<V> p q = do {
    pq \<leftarrow> mult_poly_s \<V> p q;
   normalize_poly_s \<V> pq
  }\<close>

lemma mult_poly_full_s_mult_poly_full_prop:
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(xs, xs') \<in> perfectly_shared_polynom \<V>\<close> and
    \<open>(ys, ys') \<in> perfectly_shared_polynom \<V>\<close> and
    \<open>vars_llist xs' \<subseteq> set_mset \<D>\<V>\<close> and
    \<open>vars_llist ys' \<subseteq> set_mset \<D>\<V>\<close>
  shows \<open>mult_poly_full_s \<V> xs ys \<le> \<Down> (perfectly_shared_polynom \<V>) (mult_poly_full_prop \<D>\<V> xs' ys')\<close>
  unfolding mult_poly_full_s_def mult_poly_full_prop_def
  by (refine_rcg mult_poly_s_mult_poly_raw_prop assms normalize_poly_s_normalize_poly_s)
   (use assms in auto)
definition (in -)linear_combi_l_prep_s
  :: \<open>nat \<Rightarrow> _ \<Rightarrow> (nat, string) shared_vars \<Rightarrow> _ \<Rightarrow> (sllist_polynomial \<times> (llist_polynomial \<times> nat) list \<times> string code_status) nres\<close>
where
  \<open>linear_combi_l_prep_s i A \<V> xs = do {
  WHILE\<^sub>T
    (\<lambda>(p, xs, err). xs \<noteq> [] \<and> \<not>is_cfailed err)
    (\<lambda>(p, xs, _). do {
      ASSERT(xs \<noteq> []);
      let (q :: llist_polynomial, i) = hd xs;
      if (i \<notin># dom_m A \<or> \<not>(vars_llist_in_s \<V> q))
      then do {
        err \<leftarrow> check_linear_combi_l_s_dom_err p i;
        RETURN (p, xs, error_msg i err)
      } else do {
        ASSERT(fmlookup A i \<noteq> None);
        let r = the (fmlookup A i);
        if q = [([], 1)]
        then do {
          pq \<leftarrow> add_poly_l_s \<V> (p, r);
          RETURN (pq, tl xs, CSUCCESS)}
        else do {
          (no_new, q) \<leftarrow> normalize_poly_sharedS \<V> (q);
          q \<leftarrow> mult_poly_full_s \<V> q r;
          pq \<leftarrow> add_poly_l_s \<V> (p, q);
          RETURN (pq, tl xs, CSUCCESS)
        }
        }
        })
        ([], xs, CSUCCESS)
          }\<close>

lemma normalize_poly_sharedS_normalize_poly_shared:
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(xs, xs') \<in> Id\<close>
  shows \<open>normalize_poly_sharedS \<V> xs
    \<le> \<Down>(bool_rel \<times>\<^sub>r perfectly_shared_polynom \<V>)
    (normalize_poly_shared \<D>\<V> xs')\<close>
proof -
  have [refine]: \<open>full_normalize_poly xs \<le> \<Down> Id (full_normalize_poly xs')\<close>
    using assms by auto
  show ?thesis
    unfolding normalize_poly_sharedS_def normalize_poly_shared_def
    by (refine_rcg assms import_poly_no_newS_import_poly_no_new)
qed


lemma linear_combi_l_prep_s_linear_combi_l_prep:
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(A,B) \<in> \<langle>nat_rel, perfectly_shared_polynom \<V>\<rangle>fmap_rel\<close>
    \<open>(xs,xs') \<in> Id\<close>
  shows \<open>linear_combi_l_prep_s i A \<V> xs
    \<le> \<Down>(perfectly_shared_polynom \<V> \<times>\<^sub>r Id \<times>\<^sub>r Id)
    (linear_combi_l_prep2 j B \<D>\<V> xs')\<close>
proof -
  have [refine]: \<open>check_linear_combi_l_s_dom_err a b
    \<le> \<Down> Id
    (check_linear_combi_l_dom_err c d)\<close> for a b c d
    unfolding check_linear_combi_l_dom_err_def check_linear_combi_l_s_dom_err_def
    by auto
  show ?thesis
    unfolding linear_combi_l_prep_s_def linear_combi_l_prep2_def
    apply (refine_rcg normalize_poly_sharedS_normalize_poly_shared
      mult_poly_full_s_mult_poly_full_prop add_poly_l_s_add_poly_l)
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal using fmap_rel_nat_rel_dom_m[OF assms(2)] unfolding in_dom_m_lookup_iff by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    done
qed


definition check_linear_combi_l_s_mult_err :: \<open>sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> string nres\<close> where
  \<open>check_linear_combi_l_s_mult_err pq r = SPEC (\<lambda>_. True)\<close>

definition weak_equality_l_s :: \<open>sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> bool nres\<close> where
  \<open>weak_equality_l_s p q = RETURN (p = q)\<close>

definition check_linear_combi_l_s where
  \<open>check_linear_combi_l_s spec A \<V> i xs r = do {
  (mem_err, r) \<leftarrow> import_poly_no_newS \<V> r;
  if mem_err \<or> i \<in># dom_m A \<or> xs = []
  then do {
    err \<leftarrow> check_linear_combi_l_pre_err i (i \<in># dom_m A) (xs = []) (mem_err);
    RETURN (error_msg i err, r)
  }
  else do {
    (p, _, err) \<leftarrow> linear_combi_l_prep_s i A \<V> xs;
    if (is_cfailed err)
    then do {
      RETURN (err, r)
    }
    else do {
      b \<leftarrow> weak_equality_l_s p r;
      b' \<leftarrow> weak_equality_l_s r spec;
      if b then (if b' then RETURN (CFOUND, r) else RETURN (CSUCCESS, r)) else do {
        c \<leftarrow> check_linear_combi_l_s_mult_err p r;
        RETURN (error_msg i c, r)
      }
    }
        }}\<close>
definition weak_equality_l_s' :: \<open>_\<close> where
  \<open>weak_equality_l_s' _ =  weak_equality_l_s\<close>

definition weak_equality_l' :: \<open>_\<close> where
  \<open>weak_equality_l' _ =  weak_equality_l\<close>

lemma weak_equality_l_s_weak_equality_l:
  fixes a :: sllist_polynomial and b :: llist_polynomial and \<V> :: \<open>(nat,string)shared_vars\<close>
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(a,b) \<in> perfectly_shared_polynom \<V>\<close>
    \<open>(c,d) \<in> perfectly_shared_polynom \<V>\<close>
  shows
    \<open>weak_equality_l_s' \<V> a c \<le>\<Down>bool_rel (weak_equality_l' \<D>\<V> b d)\<close>
  using assms perfectly_shared_polynom_unique_left[OF assms(2), of d]
    perfectly_shared_polynom_unique_right[OF assms(1,2), of c]
  unfolding weak_equality_l_s_def weak_equality_l_def weak_equality_l'_def
    weak_equality_l_s'_def
  by auto

lemma check_linear_combi_l_s_check_linear_combi_l:
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(A,B) \<in> \<langle>nat_rel, perfectly_shared_polynom \<V>\<rangle>fmap_rel\<close> and
    \<open>(xs,xs')\<in> Id\<close>
    \<open>(r,r')\<in>Id\<close>
    \<open>(i,j)\<in>nat_rel\<close>
    \<open>(spec, spec') \<in> perfectly_shared_polynom \<V>\<close>
  shows \<open>check_linear_combi_l_s spec A \<V> i r xs
    \<le> \<Down>(Id \<times>\<^sub>r perfectly_shared_polynom \<V>)
    (check_linear_combi_l_prop spec' B \<D>\<V> j r' xs')\<close>
proof -
  have [refine]: \<open>check_linear_combi_l_pre_err a b c d \<le> \<Down>Id (check_linear_combi_l_pre_err u x y z)\<close>
    for a b c d u x y z
    by  (auto simp: check_linear_combi_l_pre_err_def)
  have [refine]: \<open>check_linear_combi_l_s_mult_err a b \<le> \<Down>Id (check_linear_combi_l_mult_err u x)\<close>
    for a b u x
    by  (auto simp: check_linear_combi_l_s_mult_err_def check_linear_combi_l_mult_err_def)

  show ?thesis
    unfolding check_linear_combi_l_s_def check_linear_combi_l_prop_def
    apply (refine_rcg import_poly_no_newS_import_poly_no_new assms
      linear_combi_l_prep_s_linear_combi_l_prep weak_equality_l_s_weak_equality_l[unfolded weak_equality_l'_def
      weak_equality_l_s'_def])
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using assms by auto
    done
qed

definition check_extension_l_s_new_var_multiple_err :: \<open>string \<Rightarrow> sllist_polynomial \<Rightarrow> string nres\<close> where
  \<open>check_extension_l_s_new_var_multiple_err v p = SPEC (\<lambda>_. True)\<close>

definition check_extension_l_s_side_cond_err
  :: \<open>string \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> string nres\<close>
where
  \<open>check_extension_l_s_side_cond_err v p p' q = SPEC (\<lambda>_. True)\<close>

definition (in -)check_extension_l2_s
  :: \<open>_ \<Rightarrow> _ \<Rightarrow> (nat,string)shared_vars \<Rightarrow> nat \<Rightarrow> string \<Rightarrow> llist_polynomial \<Rightarrow>
     (string code_status \<times> sllist_polynomial \<times> (nat,string)shared_vars \<times> nat) nres\<close>
where
  \<open>check_extension_l2_s spec A \<V> i v p = do {
  n \<leftarrow> is_new_variableS v \<V>;
  let pre = i \<notin># dom_m A \<and> n;
  let nonew = vars_llist_in_s \<V> p;
  (mem, p, \<V>) \<leftarrow> import_polyS \<V> p;
  let pre = (pre \<and> \<not>alloc_failed mem);
  if \<not>pre
  then do {
    c \<leftarrow> check_extension_l_dom_err i;
    RETURN (error_msg i c, [], \<V>, 0)
  } else do {
      if \<not>nonew
      then do {
        c \<leftarrow> check_extension_l_s_new_var_multiple_err v p;
        RETURN (error_msg i c, [], \<V>, 0)
      }
      else do {
        (mem', \<V>, v') \<leftarrow> import_variableS v \<V>;
        if alloc_failed mem'
        then do {
          c \<leftarrow> check_extension_l_dom_err i;
          RETURN (error_msg i c, [], \<V>, 0)
        } else
        do {
         p2 \<leftarrow> mult_poly_full_s \<V> p p;
         let p'' = map (\<lambda>(a,b). (a, -b)) p;
         q \<leftarrow> add_poly_l_s \<V> (p2, p'');
         eq \<leftarrow> weak_equality_l_s q [];
         if eq then do {
           RETURN (CSUCCESS, p, \<V>, v')
         } else do {
          c \<leftarrow> check_extension_l_s_side_cond_err v p p'' q;
          RETURN (error_msg i c, [], \<V>, v')
        }
      }
    }
  }
 }\<close>
lemma list_rel_tlD: \<open>(a, b) \<in> \<langle>R\<rangle>list_rel \<Longrightarrow> (tl a, tl b) \<in> \<langle>R\<rangle>list_rel\<close>
  by (metis list.sel(2) list.sel(3) list_rel_simp(1) list_rel_simp(2) list_rel_simp(4) neq_NilE)

lemma check_extension_l2_prop_alt_def:
  \<open>check_extension_l2_prop spec A \<V> i v p = do {
  n \<leftarrow> is_new_variable v \<V>;
  let pre = i \<notin># dom_m A \<and> n;
  let nonew = vars_llist p \<subseteq> set_mset \<V>;
  (mem, p, \<V>) \<leftarrow> import_poly \<V> p;
  (mem', \<V>, va) \<leftarrow> if pre \<and> nonew \<and> \<not> alloc_failed mem then import_variable v \<V> else RETURN (mem, \<V>, v);
  let pre = ((pre \<and> \<not>alloc_failed mem) \<and> \<not>alloc_failed mem');

  if \<not>pre
  then do {
    c \<leftarrow> check_extension_l_dom_err i;
    RETURN (error_msg i c, [], \<V>, va)
  } else do {
      if \<not>nonew
      then do {
        c \<leftarrow> check_extension_l_new_var_multiple_err v p;
        RETURN (error_msg i c, [], \<V>, va)
      }
      else do {
         ASSERT(vars_llist p \<subseteq> set_mset \<V>);
         p2 \<leftarrow>  mult_poly_full_prop \<V> p p;
         ASSERT(vars_llist p2 \<subseteq> set_mset \<V>);
         let p'' = map (\<lambda>(a,b). (a, -b)) p;
         ASSERT(vars_llist p'' \<subseteq> set_mset \<V>);
         q \<leftarrow> add_poly_l_prep \<V> (p2, p'');
         ASSERT(vars_llist q \<subseteq> set_mset \<V>);
         eq \<leftarrow> weak_equality_l q [];
         if eq then do {
           RETURN (CSUCCESS, p, \<V>, va)
         } else do {
          c \<leftarrow> check_extension_l_side_cond_err v p q;
          RETURN (error_msg i c, [], \<V>, va)
        }
      }
    }
  }\<close>
  unfolding check_extension_l2_prop_def Let_def check_extension_l_side_cond_err_def
     is_new_variable_def
  by (auto intro!: bind_cong[OF refl])

lemma check_extension_l2_prop_alt_def2:
  \<open>check_extension_l2_prop spec A \<V> i v p = do {
  n \<leftarrow> is_new_variable v \<V>;
  let pre = i \<notin># dom_m A \<and> n;
  let nonew = vars_llist p \<subseteq> set_mset \<V>;
  (mem, p, \<V>) \<leftarrow> import_poly \<V> p;
  let pre = (pre \<and> \<not>alloc_failed mem);
  if \<not>pre
  then do {
    c \<leftarrow> check_extension_l_dom_err i;
    RETURN (error_msg i c, [], \<V>, v)
   } else do {
      if \<not>nonew
      then do {
        c \<leftarrow> check_extension_l_new_var_multiple_err v p;
        RETURN (error_msg i c, [], \<V>, v)
      }
      else do {
      (mem', \<V>, va) \<leftarrow> import_variable v \<V>;
      if (alloc_failed mem')
      then do {
       c \<leftarrow> check_extension_l_dom_err i;
       RETURN (error_msg i c, [], \<V>, va)
      }
      else do {
         ASSERT(vars_llist p \<subseteq> set_mset \<V>);
         p2 \<leftarrow>  mult_poly_full_prop \<V> p p;
         ASSERT(vars_llist p2 \<subseteq> set_mset \<V>);
         let p'' = map (\<lambda>(a,b). (a, -b)) p;
         ASSERT(vars_llist p'' \<subseteq> set_mset \<V>);
         q \<leftarrow> add_poly_l_prep \<V> (p2, p'');
         ASSERT(vars_llist q \<subseteq> set_mset \<V>);
         eq \<leftarrow> weak_equality_l q [];
         if eq then do {
           RETURN (CSUCCESS, p, \<V>, va)
         } else do {
          c \<leftarrow> check_extension_l_side_cond_err v p q;
          RETURN (error_msg i c, [], \<V>, va)
        }
      }
     }
    }
  }\<close>
  unfolding check_extension_l2_prop_alt_def
  unfolding Let_def check_extension_l_side_cond_err_def de_Morgan_conj
    not_not
  by (subst if_conn(2))
    (auto intro!: bind_cong[OF refl])

lemma list_rel_mapI: \<open>(xs,ys) \<in> \<langle>R\<rangle>list_rel \<Longrightarrow> (\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> (x,y)\<in>R \<Longrightarrow> (f x, g y) \<in> S) \<Longrightarrow> (map f xs, map g ys) \<in> \<langle>S\<rangle>list_rel\<close>
  by (induction xs arbitrary: ys)
    (auto simp: list_rel_split_right_iff)

lemma perfectly_shared_var_rel_perfectly_shared_monom_mono:
  \<open>(\<forall>xs. xs \<in> perfectly_shared_var_rel \<A> \<longrightarrow> xs \<in> perfectly_shared_var_rel \<A>') \<longleftrightarrow>
  (\<forall>xs. xs \<in> perfectly_shared_monom \<A> \<longrightarrow> xs \<in> perfectly_shared_monom \<A>')\<close>
  by (metis list_rel_mono old.prod.exhaust list_rel_simp(2) list_rel_simp(4))

lemma perfectly_shared_var_rel_perfectly_shared_polynom_mono:
  \<open>(\<forall>xs. xs \<in> perfectly_shared_var_rel \<A> \<longrightarrow> xs \<in> perfectly_shared_var_rel \<A>') \<longleftrightarrow>
  (\<forall>xs. xs \<in> perfectly_shared_polynom \<A> \<longrightarrow> xs \<in> perfectly_shared_polynom \<A>')\<close>
  unfolding perfectly_shared_var_rel_perfectly_shared_monom_mono
  apply (auto intro: list_rel_mono)
    apply (drule_tac x =  \<open>[(a,1)]\<close> in spec)
    apply (drule_tac x =  \<open>[(b,1)]\<close> in spec)
    apply auto
    done

lemma check_extension_l2_s_check_extension_l2:
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(A,B) \<in> \<langle>nat_rel, perfectly_shared_polynom \<V>\<rangle>fmap_rel\<close> and
    \<open>(r,r')\<in>Id\<close>
    \<open>(i,j)\<in>nat_rel\<close>
    \<open>(spec, spec') \<in> perfectly_shared_polynom \<V>\<close>
    \<open>(v,v')\<in>Id\<close>
  shows \<open>check_extension_l2_s spec A \<V> i v r
    \<le> \<Down>{((err, p, A, v), (err', p', A', v')).
    (err, err') \<in> Id \<and>
    (\<not>is_cfailed err \<longrightarrow>
    (p, p') \<in> perfectly_shared_polynom A \<and> (v, v') \<in> perfectly_shared_var_rel A \<and>
      (A, A') \<in> {(a,b). (a,b) \<in> perfectly_shared_vars_rel \<and> perfectly_shared_polynom \<V> \<subseteq> perfectly_shared_polynom a})}
    (check_extension_l2_prop spec' B \<D>\<V> j v' r')\<close>
proof -
  have [refine]: \<open>check_extension_l_s_new_var_multiple_err a b \<le>\<Down>Id (check_extension_l_new_var_multiple_err a' b')\<close> for a a' b b'
    by (auto simp: check_extension_l_s_new_var_multiple_err_def check_extension_l_new_var_multiple_err_def)

  have [refine]: \<open>check_extension_l_dom_err i \<le> \<Down> (Id) (check_extension_l_dom_err j)\<close>
    by (auto simp: check_extension_l_dom_err_def)
  have [refine]: \<open>check_extension_l_s_side_cond_err a b c d \<le> \<Down>Id (check_extension_l_side_cond_err a' b' c')\<close> for a b c d a' b' c' d'
    by (auto simp: check_extension_l_s_side_cond_err_def check_extension_l_side_cond_err_def)
  have G: \<open>(a, b) \<in> import_poly_rel \<V> x \<Longrightarrow> \<not>alloc_failed (fst a) \<Longrightarrow>
    (snd (snd a), snd (snd b)) \<in> perfectly_shared_vars_rel\<close> for a b x
    by auto

  show ?thesis
    unfolding check_extension_l2_s_def check_extension_l2_prop_alt_def2 nres_monad3
    apply (refine_rcg import_polyS_import_poly assms mult_poly_full_s_mult_poly_full_prop
      import_variableS_import_variable[unfolded perfectly_shared_var_rel_perfectly_shared_polynom_mono]
      is_new_variable_spec)
    subgoal using assms by auto
    subgoal using assms by (auto simp add: perfectly_shared_vars_rel_def perfectly_shared_vars_def)
    subgoal using assms by (auto simp: error_msg_def)
    subgoal using assms by (auto)
    subgoal using assms by (auto simp: error_msg_def)
    subgoal using assms by (auto)
    subgoal using assms by auto
    subgoal using assms by (auto simp: error_msg_def)
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
      apply (rule add_poly_l_s_add_poly_l)
    subgoal by auto
    subgoal for _ _ x x' x1 x2 x1a x2a x1b x2b x1c x2c xa x'a x1d x2d x1e x2e x1f x2f x1g x2g p2 p2a
      using assms
      by ( auto intro!: list_rel_mapI[of _ _ \<open>perfectly_shared_monom x1g \<times>\<^sub>r int_rel\<close>])
    apply (rule weak_equality_l_s_weak_equality_l[unfolded weak_equality_l'_def
      weak_equality_l_s'_def])
    defer apply assumption
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using assms by auto
    apply (solves auto) (*one goal with unification*)
    done
qed

definition PAC_checker_l_step_s
  :: \<open>sllist_polynomial \<Rightarrow> string code_status \<times> (nat,string)shared_vars \<times> _ \<Rightarrow> (llist_polynomial, string, nat) pac_step \<Rightarrow> _\<close>
where
  \<open>PAC_checker_l_step_s = (\<lambda>spec (st', \<V>, A) st. do {
    ASSERT (\<not>is_cfailed st');
    case st of
     CL _ _ _ \<Rightarrow>
       do {
        let i = (new_id st);
        let lincomb = (pac_srcs st);
        let r = pac_res st;
        r \<leftarrow> full_normalize_poly r;
        (eq, r) \<leftarrow> check_linear_combi_l_s spec A \<V> i lincomb r;
        let _ = eq;
        if \<not>is_cfailed eq
        then RETURN (merge_cstatus st' eq, \<V>, fmupd i r A)
       else RETURN (eq, \<V>, A)
     }
    | Del _ \<Rightarrow>
       do {
        eq \<leftarrow> check_del_l spec A (pac_src1 st);
        let _ = eq;
        if \<not>is_cfailed eq
        then RETURN (merge_cstatus st' eq, \<V>, fmdrop (pac_src1 st) A)
        else RETURN (eq, \<V>, A)
     }
   | Extension _ _ _ \<Rightarrow>
       do {
         r \<leftarrow> full_normalize_poly (pac_res st);
        (eq, r, \<V>, v) \<leftarrow> check_extension_l2_s spec A (\<V>) (new_id st) (new_var st) r;
        if \<not>is_cfailed eq
        then do {
           r \<leftarrow> add_poly_l_s \<V> ([([v], -1)], r);
          RETURN (st', \<V>, fmupd (new_id st) r A)
        }
        else RETURN (eq, \<V>, A)
     }}
          )\<close>
lemma is_cfailed_merge_cstatus:
  "is_cfailed (merge_cstatus c d) \<longleftrightarrow> is_cfailed c \<or> is_cfailed d"
  by (cases c; cases d) auto
lemma (in -) fmap_rel_mono2:
  \<open>x \<in> \<langle>A,B\<rangle>fmap_rel \<Longrightarrow>  B \<subseteq>B' \<Longrightarrow> x \<in> \<langle>A,B'\<rangle>fmap_rel\<close>
  by (auto simp: fmap_rel_alt_def)

lemma PAC_checker_l_step_s_PAC_checker_l_step_s:
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(A,B) \<in> \<langle>nat_rel, perfectly_shared_polynom \<V>\<rangle>fmap_rel\<close> and
    \<open>(spec, spec') \<in> perfectly_shared_polynom \<V>\<close> and
    \<open>(err, err') \<in> Id\<close> and
    \<open>(st,st')\<in>Id\<close>
  shows \<open>PAC_checker_l_step_s spec (err, \<V>, A) st
    \<le> \<Down>{((err, \<V>', A'), (err', \<D>\<V>', B')).
    (err, err') \<in> Id \<and>
     (\<not>is_cfailed err \<longrightarrow> ((\<V>', \<D>\<V>') \<in> perfectly_shared_vars_rel \<and>(A',B') \<in> \<langle>nat_rel, perfectly_shared_polynom \<V>'\<rangle>fmap_rel \<and>
    perfectly_shared_polynom \<V> \<subseteq> perfectly_shared_polynom \<V>'))}
    (PAC_checker_l_step_prep spec' (err', \<D>\<V>, B) st')\<close>
proof -
  have [refine]: \<open>check_del_l spec A (LPAC_Checker_Specification.pac_step.pac_src1 st)
    \<le> \<Down> Id
    (check_del_l spec' B
    (LPAC_Checker_Specification.pac_step.pac_src1 st'))\<close>
    by (auto simp: check_del_l_def)
  have HID: \<open>f = f' \<Longrightarrow> f \<le> \<Down>Id f'\<close> for f f'
    by auto
  show ?thesis
    unfolding PAC_checker_l_step_s_def PAC_checker_l_step_prep_def pac_step.case_eq_if
      prod.simps Let_def[of \<open>LPAC_Checker_Specification.pac_step.new_id _\<close>]
      Let_def[of \<open>pac_srcs _\<close>] Let_def[of \<open>pac_res _\<close>]
    apply (refine_rcg check_linear_combi_l_s_check_linear_combi_l
      check_extension_l2_s_check_extension_l2 add_poly_l_s_add_poly_l)
    subgoal using assms by auto
    subgoal using assms by auto
    apply (rule HID)
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal using assms by (auto simp: is_cfailed_merge_cstatus intro!: fmap_rel_fmupd_fmap_rel)
    subgoal by auto
    subgoal using assms by auto
    apply (rule HID)
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    subgoal using assms by (auto intro!: fmap_rel_fmupd_fmap_rel  intro: fmap_rel_mono2)
    subgoal by auto
    subgoal by auto
    subgoal using assms by (auto intro!: fmap_rel_fmdrop_fmap_rel)
    subgoal by auto
    done
qed

lemma PAC_checker_l_step_s_PAC_checker_l_step_s2:
  assumes
    \<open>(st,st')\<in>Id\<close>
    \<open>(spec, spec') \<in> perfectly_shared_polynom (fst (snd err\<V>A))\<close> and
    \<open>((err\<V>A), (err'\<D>\<V>B)) \<in> Id \<times>\<^sub>r perfectly_shared_vars_rel \<times>\<^sub>r  \<langle>nat_rel, perfectly_shared_polynom (fst (snd err\<V>A))\<rangle>fmap_rel\<close>
  shows \<open>PAC_checker_l_step_s spec (err\<V>A) st
    \<le> \<Down>{((err, \<V>', A'), (err', \<D>\<V>', B')).
    (err, err') \<in> Id \<and>
     (\<not>is_cfailed err \<longrightarrow> ((\<V>', \<D>\<V>') \<in> perfectly_shared_vars_rel \<and>(A',B') \<in> \<langle>nat_rel, perfectly_shared_polynom \<V>'\<rangle>fmap_rel \<and>
    perfectly_shared_polynom (fst (snd err\<V>A)) \<subseteq> perfectly_shared_polynom \<V>'))}
    (PAC_checker_l_step_prep spec' (err'\<D>\<V>B) st')\<close>
  using PAC_checker_l_step_s_PAC_checker_l_step_s[of \<open>fst (snd err\<V>A)\<close> \<open>fst (snd err'\<D>\<V>B)\<close>
    \<open>snd (snd err\<V>A)\<close> \<open>snd (snd err'\<D>\<V>B)\<close> spec spec' \<open>fst (err\<V>A)\<close> \<open>fst (err'\<D>\<V>B)\<close> st st' ] assms
  by (cases err\<V>A; cases err'\<D>\<V>B)
   auto

definition fully_normalize_and_import where
  \<open>fully_normalize_and_import \<V> p = do {
    p \<leftarrow> sort_all_coeffs p;
   (err, p, \<V>) \<leftarrow> import_polyS \<V> p;
   if alloc_failed err
   then RETURN (err, p, \<V>)
   else do {
     p \<leftarrow> normalize_poly_s \<V> p;
     RETURN (err, p, \<V>)
  }}\<close>

fun vars_llist_l where
  \<open>vars_llist_l [] = []\<close> |
  \<open>vars_llist_l (x#xs) = fst x @ vars_llist_l xs\<close>

lemma set_vars_llist_l[simp]: \<open>set(vars_llist_l xs) = vars_llist xs\<close>
  by (induction xs)
    (auto)

lemma vars_llist_l_append[simp]: \<open>vars_llist_l (a @ b) = vars_llist_l a @ vars_llist_l b\<close>
  by (induction a) auto

definition (in -) remap_polys_s_with_err :: \<open>llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> (nat, string) shared_vars \<Rightarrow> (nat, llist_polynomial) fmap \<Rightarrow>
   (string code_status \<times> (nat, string) shared_vars \<times> (nat, sllist_polynomial) fmap \<times> sllist_polynomial) nres\<close> where
  \<open>remap_polys_s_with_err spec spec0 = (\<lambda>(\<V>:: (nat, string) shared_vars) A. do{
   ASSERT(vars_llist spec \<subseteq> vars_llist spec0);
   dom \<leftarrow> SPEC(\<lambda>dom. set_mset (dom_m A) \<subseteq> dom \<and> finite dom);
   (mem, \<V>) \<leftarrow> import_variablesS (vars_llist_l spec0) \<V>;
   (mem', spec, \<V>) \<leftarrow> if \<not>alloc_failed mem then import_polyS \<V> spec else RETURN (mem, [], \<V>);
   failed \<leftarrow> SPEC(\<lambda>b::bool. alloc_failed mem \<or> alloc_failed mem' \<longrightarrow> b);
   if failed
   then do {
      c \<leftarrow> remap_polys_l_dom_err;
      RETURN (error_msg (0 :: nat) c, \<V>, fmempty, [])
   }
   else do {
     (err, \<V>, A) \<leftarrow> FOREACH\<^sub>C dom (\<lambda>(err, \<V>,  A'). \<not>is_cfailed err)
       (\<lambda>i (err, \<V>,  A').
          if i \<in># dom_m A
        then  do {
           (err', p, \<V>) \<leftarrow> import_polyS \<V> (the (fmlookup A i));
            if alloc_failed err' then RETURN((CFAILED ''memory out'', \<V>, A'))
            else do {
              p \<leftarrow> full_normalize_poly_s \<V> p;
              eq  \<leftarrow> weak_equality_l_s' \<V> p spec;
              let \<V> = \<V>;
              RETURN((if eq then CFOUND else CSUCCESS), \<V>, fmupd i p A')
            }
          } else RETURN (err, \<V>, A'))
       (CSUCCESS, \<V>, fmempty);
     RETURN (err, \<V>, A, spec)
   }
  })\<close>

lemma full_normalize_poly_alt_def:
  \<open>full_normalize_poly p0 = do {
     p \<leftarrow> sort_all_coeffs p0;
     ASSERT(vars_llist p \<subseteq> vars_llist p0);
     p \<leftarrow> sort_poly_spec p;
     ASSERT(vars_llist p \<subseteq> vars_llist p0);
     RETURN (merge_coeffs0 p)
  }\<close> (is \<open>?A = ?B\<close>)
proof -
  have sort_poly_spec1: \<open>(p,p')\<in> Id \<Longrightarrow> sort_poly_spec p \<le> \<Down> Id (sort_poly_spec p')\<close> for p p'
    by auto

  have sort_all_coeffs2: \<open>sort_all_coeffs xs \<le>\<Down>{(ys,ys'). (ys,ys') \<in> Id \<and> vars_llist ys \<subseteq> vars_llist xs} (sort_all_coeffs xs)\<close> for xs
  proof -
    term xs
    have [refine]: \<open>(xs, xs) \<in> \<langle>{(ys,ys'). (ys,ys') \<in> Id \<and> ys \<in> set xs}\<rangle>list_rel\<close>
      by (rule list_rel_mono_strong[of _ Id])
        (auto)
    have [refine]: \<open>(x1a,x1)\<in> Id \<Longrightarrow> sort_coeff x1a  \<le> \<Down> {(ys,ys'). (ys,ys') \<in> Id \<and> set ys \<subseteq> set x1a} (sort_coeff x1)\<close> for x1a x1
      unfolding sort_coeff_def
      by (auto intro!: RES_refine dest: mset_eq_setD)

    show ?thesis
      unfolding sort_all_coeffs_def
      apply refine_vcg
      subgoal by auto
      subgoal by auto
      subgoal by (auto dest!: split_list)
      done
  qed

  have sort_poly_spec1: \<open>(p,p')\<in> Id \<Longrightarrow> sort_poly_spec p \<le> \<Down> Id (sort_poly_spec p')\<close> for p p'
    by auto
  have sort_poly_spec2: \<open>(p,p')\<in>Id \<Longrightarrow> sort_poly_spec p \<le> \<Down> {(ys,ys'). (ys,ys') \<in> Id \<and> vars_llist ys \<subseteq> vars_llist p} (sort_poly_spec p')\<close>
    for p p'
    by (auto simp: sort_poly_spec_def intro!: RES_refine dest: vars_llist_mset_eq)
  have \<open>?A \<le> \<Down>Id ?B\<close>
    unfolding full_normalize_poly_def
    by (refine_rcg sort_poly_spec1) auto
  moreover have \<open>?B \<le> \<Down>Id ?A\<close>
    unfolding full_normalize_poly_def
    apply (rule bind_refine[OF sort_all_coeffs2])
    apply (refine_vcg sort_poly_spec2)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
  ultimately show ?thesis
    by auto
qed

definition full_normalize_poly' :: \<open>_\<close> where
  \<open>full_normalize_poly' _ = full_normalize_poly\<close>

lemma full_normalize_poly_s_full_normalize_poly:
  fixes xs :: \<open>sllist_polynomial\<close> and
    \<V> :: \<open>(nat,string)shared_vars\<close>
  assumes
    \<open>(xs, xs') \<in> perfectly_shared_polynom \<V>\<close> and
    \<V>: \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>vars_llist xs' \<subseteq> set_mset \<D>\<V>\<close>
  shows \<open>full_normalize_poly_s \<V> xs \<le> \<Down>(perfectly_shared_polynom \<V>) (full_normalize_poly' \<D>\<V> xs')\<close>
proof -
  show ?thesis
    unfolding full_normalize_poly_s_def full_normalize_poly_alt_def full_normalize_poly'_def
    apply (refine_rcg sort_all_coeffs_s_sort_all_coeffs assms
      msort_monoms_sort_poly_spec merge_coeffs0_s_merge_coeffs0)
    subgoal using assms by auto
    done
qed

lemma remap_polys_l2_with_err_prep_alt_def:
  \<open>remap_polys_l2_with_err_prep spec spec0 = (\<lambda>(\<V>:: (nat, string) vars) A. do{
   ASSERT(vars_llist spec \<subseteq> vars_llist spec0);
   dom \<leftarrow> SPEC(\<lambda>dom. set_mset (dom_m A) \<subseteq> dom \<and> finite dom);
   (mem, \<V>) \<leftarrow> SPEC(\<lambda>(mem, \<V>'). \<not>alloc_failed mem \<longrightarrow> set_mset \<V>' = set_mset \<V> \<union> vars_llist spec0);
   (mem', spec, \<V>) \<leftarrow> if \<not>alloc_failed mem then import_poly \<V> spec else SPEC(\<lambda>_. True);
   failed \<leftarrow> SPEC(\<lambda>b::bool. alloc_failed mem \<or> alloc_failed mem' \<longrightarrow> b);
   if failed
   then do {
      c \<leftarrow> remap_polys_l_dom_err;
      SPEC (\<lambda>(mem, _, _, _). mem = error_msg (0::nat) c)
   }
   else do {
     (err, \<V>, A) \<leftarrow> FOREACH\<^sub>C dom (\<lambda>(err, \<V>,  A'). \<not>is_cfailed err)
       (\<lambda>i (err, \<V>,  A').
          if i \<in># dom_m A
          then  do {
           (err', p, \<V>) \<leftarrow> import_poly \<V> (the (fmlookup A i));
            if alloc_failed err' then RETURN((CFAILED ''memory out'', \<V>, A'))
            else do {
              ASSERT(vars_llist p \<subseteq> set_mset \<V>);
              p \<leftarrow> full_normalize_poly' \<V> p;
              eq  \<leftarrow> weak_equality_l' \<V> p spec;
              let \<V> = \<V>;
              RETURN((if eq then CFOUND else CSUCCESS), \<V>, fmupd i p A')
            }
          } else RETURN (err, \<V>, A'))
       (CSUCCESS, \<V>, fmempty);
     RETURN (err, \<V>, A, spec)
  }})\<close>
  unfolding full_normalize_poly'_def weak_equality_l'_def
  by(auto simp: remap_polys_l2_with_err_prep_def 
       intro!: ext bind_cong[OF refl])

lemma remap_polys_s_with_err_remap_polys_l2_with_err_prep:
  fixes \<V> :: \<open>(nat, string) shared_vars\<close>
  assumes
    \<V>: \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close> and
    AB: \<open>(A,B) \<in> \<langle>nat_rel, Id\<rangle>fmap_rel\<close> and
    \<open>(spec, spec') \<in> \<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r int_rel\<rangle>list_rel\<close> and
    spec0: \<open>(spec0, spec0') \<in> \<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r int_rel\<rangle>list_rel\<close>
  shows
    \<open>remap_polys_s_with_err spec spec0 \<V> A \<le>
    \<Down>{((err, \<V>, A, fspec), (err', \<V>', A', fspec')).
    (err, err') \<in> Id \<and>
   ( \<not>is_cfailed err \<longrightarrow> (fspec, fspec') \<in> perfectly_shared_polynom \<V> \<and>
     ((err, \<V>, A), (err', \<V>', A')) \<in> Id \<times>\<^sub>r perfectly_shared_vars_rel \<times>\<^sub>r\<langle>nat_rel, perfectly_shared_polynom \<V>\<rangle>fmap_rel)}
  (remap_polys_l2_with_err_prep spec' spec0' \<D>\<V> B)\<close>
proof -
  have vars_spec: \<open>(vars_llist_l spec0, vars_llist_l spec0) \<in> Id\<close>
    by auto
  have [refine]: \<open>import_variablesS (vars_llist_l spec0) \<V>
    \<le> \<Down> {((mem, \<V>\<V>), (mem', \<V>\<V>')). mem=mem' \<and> (\<not>alloc_failed mem \<longrightarrow>  (\<V>\<V>, \<V>\<V>') \<in> perfectly_shared_vars_rel \<and>
       perfectly_shared_polynom \<V> \<subseteq> perfectly_shared_polynom \<V>\<V>)}
      (SPEC (\<lambda>(mem, \<V>'). \<not>alloc_failed mem \<longrightarrow>  set_mset \<V>' = set_mset \<D>\<V> \<union> vars_llist spec0'))\<close>
    apply (rule import_variablesS_import_variables[OF \<V> vars_spec, THEN order_trans])
    apply (rule ref_two_step'[THEN order_trans])
    apply (rule import_variables_spec)
    apply (use spec0 in \<open>auto simp: conc_fun_RES
      dest!: spec[of _  \<open>\<D>\<V> + mset (vars_llist_l spec0)\<close>]\<close>)
    by (meson perfectly_shared_var_rel_perfectly_shared_polynom_mono subset_eq)

  have 1: \<open>inj_on id (dom :: nat set)\<close> for dom
    by (auto simp: inj_on_def)
  have [refine]: \<open>(x2e, x2c) \<in> perfectly_shared_vars_rel \<Longrightarrow>
    ((CSUCCESS, x2e, fmempty), CSUCCESS, x2c, fmempty)
    \<in>  {((mem,\<A>, A), (mem',\<A>', A')). (mem,mem') \<in> Id \<and>
    (\<not>is_cfailed mem \<longrightarrow> ((\<A>, A), (\<A>', A'))\<in> perfectly_shared_vars_rel \<times>\<^sub>r\<langle>nat_rel, perfectly_shared_polynom \<A>\<rangle>fmap_rel \<and>
      perfectly_shared_polynom x2e \<subseteq> perfectly_shared_polynom \<A>)}\<close>
    for x2e x2c
    by auto
  have [simp]: \<open>A \<propto> xb = B \<propto> xb\<close> for xb
    using AB unfolding fmap_rel_alt_def apply auto by (metis in_dom_m_lookup_iff)
  show ?thesis
    unfolding remap_polys_s_with_err_def remap_polys_l2_with_err_prep_alt_def Let_def
    apply (refine_rcg import_polyS_import_poly 1 full_normalize_poly_s_full_normalize_poly
      weak_equality_l_s_weak_equality_l)
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal by (auto intro!: RETURN_RES_refine)
    subgoal by auto
    subgoal by auto
    subgoal by (clarsimp simp: error_msg_def intro!:RETURN_RES_refine)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal by simp
    subgoal by auto
    subgoal
      by (auto intro!: fmap_rel_fmupd_fmap_rel
        intro: fmap_rel_mono2)
    subgoal by auto
    subgoal
      by (auto intro!: fmap_rel_fmupd_fmap_rel
        intro: fmap_rel_mono2)
    done
qed

definition PAC_checker_l_s where
  \<open>PAC_checker_l_s spec A b st = do {
  (S, _) \<leftarrow> WHILE\<^sub>T
  (\<lambda>((b, A), n). \<not>is_cfailed b \<and> n \<noteq> [])
  (\<lambda>((bA), n). do {
  ASSERT(n \<noteq> []);
  S \<leftarrow> PAC_checker_l_step_s spec bA (hd n);
  RETURN (S, tl n)
  })
  ((b, A), st);
  RETURN S
  }\<close>


lemma PAC_checker_l_s_PAC_checker_l_prep_s:
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(A,B) \<in> \<langle>nat_rel, perfectly_shared_polynom \<V>\<rangle>fmap_rel\<close> and
    \<open>(spec, spec') \<in> perfectly_shared_polynom \<V>\<close> and
    \<open>(err, err') \<in> Id\<close> and
    \<open>(st,st')\<in>Id\<close>
  shows \<open>PAC_checker_l_s spec (\<V>, A)  err st
    \<le> \<Down>{((err, \<V>', A'), (err', \<D>\<V>', B')).
    (err, err') \<in> Id \<and>
    (\<not>is_cfailed err \<longrightarrow> ((\<V>', \<D>\<V>') \<in> perfectly_shared_vars_rel \<and>(A',B') \<in> \<langle>nat_rel, perfectly_shared_polynom \<V>'\<rangle>fmap_rel))}
    (PAC_checker_l2 spec' (\<D>\<V>, B) err' st')\<close>
proof -
  show ?thesis
    unfolding PAC_checker_l_s_def PAC_checker_l2_def
    apply (refine_rcg PAC_checker_l_step_s_PAC_checker_l_step_s2
      WHILET_refine[where R = \<open>{((err, \<V>', A'), err', \<D>\<V>', B').
  (err, err') \<in> Id \<and> (\<not> is_cfailed err \<longrightarrow>
  (\<V>', \<D>\<V>') \<in> perfectly_shared_vars_rel \<and>
      (A', B') \<in> \<langle>nat_rel, perfectly_shared_polynom \<V>'\<rangle>fmap_rel \<and>
    perfectly_shared_polynom \<V> \<subseteq> perfectly_shared_polynom \<V>')}\<times>\<^sub>rId\<close>])
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal by force
    subgoal by auto
    done
qed

definition full_checker_l_s
  :: \<open>llist_polynomial \<Rightarrow> (nat, llist_polynomial) fmap \<Rightarrow> (_, string, nat) pac_step list \<Rightarrow>
    (string code_status \<times> _) nres\<close>
where
  \<open>full_checker_l_s spec A st = do {
    spec' \<leftarrow> full_normalize_poly spec;
    (b, \<V>, A, spec') \<leftarrow> remap_polys_s_with_err spec' spec ({#}, fmempty, fmempty) A;
    if is_cfailed b
    then RETURN (b, \<V>, A)
    else do {
      PAC_checker_l_s spec' (\<V>, A) b st
     }
  }\<close>
lemma full_checker_l_s_full_checker_l_prep:
  assumes
    \<open>(A,B) \<in> \<langle>nat_rel, Id\<rangle>fmap_rel\<close> and
    \<open>(spec, spec') \<in> \<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r int_rel\<rangle>list_rel\<close> and
    \<open>(st,st')\<in>Id\<close>
  shows \<open>full_checker_l_s spec A st
    \<le> \<Down>{((err, _), (err', _)). (err, err') \<in> Id}
    (full_checker_l_prep spec' B st')\<close>
proof -
  have [refine]: \<open>full_normalize_poly spec \<le> \<Down> (\<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r int_rel\<rangle>list_rel) (full_normalize_poly spec')\<close>
    using assms by auto
  have [refine]: \<open>(({#}, fmempty, fmempty), {#}) \<in> perfectly_shared_vars_rel\<close>
     by (auto simp: perfectly_shared_vars_rel_def perfectly_shared_vars_def)
   have H: \<open>(x1d, x1a) \<in> perfectly_shared_vars_rel\<close>
     \<open>(x1e, x1b) \<in> \<langle>nat_rel, perfectly_shared_polynom x1d\<rangle>fmap_rel\<close>
     \<open>(x2e, x2b) \<in> perfectly_shared_polynom x1d\<close>
     \<open>(x1c, x1) \<in> Id\<close>
     if \<open>(x, x')
       \<in> {((err, \<V>, A, fspec), err', \<V>', A', fspec').
       (err, err') \<in> Id \<and>
       (\<not> is_cfailed err \<longrightarrow>
       (fspec, fspec') \<in> perfectly_shared_polynom \<V> \<and>
       ((err, \<V>, A), err', \<V>', A')
       \<in> Id \<times>\<^sub>r perfectly_shared_vars_rel \<times>\<^sub>r \<langle>nat_rel, perfectly_shared_polynom \<V>\<rangle>fmap_rel)}\<close>
       \<open>x2a = (x1b, x2b)\<close>
       \<open>x2 = (x1a, x2a)\<close>
       \<open>x' = (x1, x2)\<close>
       \<open>x2d = (x1e, x2e)\<close>
       \<open>x2c = (x1d, x2d)\<close>
       \<open>x = (x1c, x2c)\<close>
       \<open>\<not> is_cfailed x1c\<close>
     for spec' spec'a x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e
     using that by auto
  term PAC_checker_l2
  thm PAC_checker_l_s_PAC_checker_l_prep_s
  show ?thesis
    unfolding full_checker_l_s_def full_checker_l_prep_def
    apply (refine_rcg PAC_checker_l_s_PAC_checker_l_prep_s[THEN order_trans]
      remap_polys_s_with_err_remap_polys_l2_with_err_prep assms)
    subgoal by (auto simp: perfectly_shared_vars_rel_def perfectly_shared_vars_def)
    subgoal using assms by auto
    apply (rule H(1); assumption)
    apply (rule H(2); assumption)
    apply (rule H(3); assumption)
    apply (rule H(4); assumption)
    subgoal by (auto intro!: conc_fun_R_mono)
    done
qed

lemma full_checker_l_s_full_checker_l_prep':
  \<open>(uncurry2 full_checker_l_s, uncurry2 full_checker_l_prep)\<in>
  (\<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r int_rel\<rangle>list_rel \<times>\<^sub>r \<langle>nat_rel, Id\<rangle>fmap_rel) \<times>\<^sub>r Id \<rightarrow>\<^sub>f
  \<langle>{((err, _), (err', _)). (err, err') \<in> Id}\<rangle>nres_rel\<close>
  by (auto intro!: frefI nres_relI full_checker_l_s_full_checker_l_prep[THEN order_trans])

lemma sort_all_coeffs_s_RECT_aux:
  \<open>set ys \<subseteq> set xs \<Longrightarrow>
   monadic_nfoldli ys (\<lambda>_. RETURN True)
     (\<lambda>(a, n) b. do {ASSERT((a,n)\<in>set xs); a \<leftarrow> msort_coeffs \<V> a; RETURN ((a, n) # b)}) b
   = REC\<^sub>T (\<lambda>f (ys, b).
       if ys = [] then RETURN b
       else do {
         ((a, n), ys) \<leftarrow> mop_list_pop_hd ys;
         a \<leftarrow> msort_coeffs \<V> a;
         f (ys, ((a, n) # b))
       }) (ys, b)\<close>
proof (induction ys arbitrary: b)
  case Nil
  show ?case
    by (subst RECT_unfold, refine_mono) auto
next
  case (Cons x ys)
  obtain a n where x: \<open>x = (a, n)\<close> by (cases x)
  show ?case
    apply (subst RECT_unfold, refine_mono)
    using Cons.prems
    by (auto simp: x mop_list_pop_hd_def Cons.IH[symmetric] pw_eq_iff
      refine_pw_simps)
qed

lemma sort_all_coeffs_s_alt_def:
  \<open>sort_all_coeffs_s \<V> xs = REC\<^sub>T (\<lambda>f (ys, b).
       if ys = [] then RETURN b
       else do {
         ((a, n), ys) \<leftarrow> mop_list_pop_hd ys;
         a \<leftarrow> msort_coeffs \<V> a;
         f (ys, ((a, n) # b))
       }) (xs, [])\<close>
  unfolding sort_all_coeffs_s_def
  by (rule sort_all_coeffs_s_RECT_aux) auto

lemma cl_assn_free_comp[sepref_frame_free_rules]:
  \<open>MK_FREE A f \<Longrightarrow> MK_FREE (cl_assn' A) (freeable_assn.cl_free f)\<close>
  by (intro freeable_assn.cl_assn_free freeable_assn.intro)

interpretation monom_fa: freeable_assn monom_s_assn snhm.val.cl_free
  by unfold_locales (rule snhm.val.cl_assn_free)

sepref_register coeff_mcmp
sepref_def coeff_mcmp_impl is \<open>uncurry2 coeff_mcmp\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding coeff_mcmp_def rel2p_def var_order_rel''
  by sepref

sepref_register explode_while
sepref_def coeff_explode_impl is \<open>explode_while\<close>
  :: \<open>monom_s_assn\<^sup>d \<rightarrow>\<^sub>a cl_assn' monom_s_assn\<close>
  unfolding explode_while_def ls_emp
  by sepref

definition coeff_merge_while :: \<open>(nat,string)shared_vars \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list nres\<close> where
  \<open>coeff_merge_while \<V> = mcmp_merge_while (coeff_cmp \<V>) (coeff_valid \<V>) (coeff_mcmp \<V>)\<close>

sepref_register coeff_merge_while
sepref_def coeff_merge_while_impl is \<open>uncurry2 coeff_merge_while\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a monom_s_assn\<^sup>d *\<^sub>a monom_s_assn\<^sup>d \<rightarrow>\<^sub>a monom_s_assn\<close>
  unfolding coeff_merge_while_def mcmp_merge_while_def mcmp_merge_while_inner_def
    ls_emp
  by sepref

definition coeff_pass :: \<open>(nat,string)shared_vars \<Rightarrow> nat list list \<Rightarrow> nat list list nres\<close> where
  \<open>coeff_pass \<V> = mcmp_pass (coeff_cmp \<V>) (coeff_valid \<V>) (coeff_mcmp \<V>)\<close>

sepref_register coeff_pass
sepref_def coeff_pass_impl is \<open>uncurry coeff_pass\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a (cl_assn' monom_s_assn)\<^sup>d \<rightarrow>\<^sub>a cl_assn' monom_s_assn\<close>
  unfolding coeff_pass_def mcmp_pass_def coeff_merge_while_def[symmetric]
    ls_emp ls_emp'
  by sepref

definition coeff_run_passes :: \<open>(nat,string)shared_vars \<Rightarrow> nat list list \<Rightarrow> nat list list nres\<close> where
  \<open>coeff_run_passes \<V> = mcmp_run_passes (coeff_cmp \<V>) (coeff_valid \<V>) (coeff_mcmp \<V>)\<close>

sepref_register coeff_run_passes
sepref_def coeff_run_passes_impl is \<open>uncurry coeff_run_passes\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a (cl_assn' monom_s_assn)\<^sup>d \<rightarrow>\<^sub>a cl_assn' monom_s_assn\<close>
  unfolding coeff_run_passes_def mcmp_run_passes_def coeff_pass_def[symmetric]
    ls_emp ls_emp'
  by sepref

sepref_register msort_coeffs
sepref_def msort_coeffs_impl is \<open>uncurry msort_coeffs\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a monom_s_assn\<^sup>d \<rightarrow>\<^sub>a monom_s_assn\<close>
  unfolding msort_coeffs_def mcmp_msort_def coeff_run_passes_def[symmetric]
    ls_emp ls_emp'
  by sepref

lemma term_mcmp_alt_def:
  \<open>term_mcmp \<V> = (\<lambda>(xs, n) (ys, m). doN {
    a \<leftarrow> perfect_shared_term_order_rel_s \<V> (COPY xs) (COPY ys);
    RETURN (a \<noteq> GREATER)
  })\<close>
  unfolding term_mcmp_def COPY_def
  by (auto intro!: ext split: prod.splits)

sepref_register term_mcmp
sepref_def term_mcmp_impl
  is \<open>uncurry2 term_mcmp\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a (monom_s_assn \<times>\<^sub>a sbi_assn)\<^sup>k *\<^sub>a (monom_s_assn \<times>\<^sub>a sbi_assn)\<^sup>k
     \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding term_mcmp_alt_def fold_ordered_discriminators
  by sepref

sepref_def term_explode_impl
  is \<open>explode_while\<close>
  :: \<open>poly_s_assn\<^sup>d \<rightarrow>\<^sub>a cl_assn' poly_s_assn\<close>
  unfolding explode_while_def ls_emp
  by sepref

definition term_merge_while :: \<open>(nat,string)shared_vars \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial nres\<close> where
  \<open>term_merge_while \<V> = mcmp_merge_while (term_cmp \<V>) (term_valid \<V>) (term_mcmp \<V>)\<close>

sepref_register term_merge_while
sepref_def term_merge_while_impl
  is \<open>uncurry2 term_merge_while\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>d *\<^sub>a poly_s_assn\<^sup>d \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding term_merge_while_def mcmp_merge_while_def mcmp_merge_while_inner_def
    ls_emp
  by sepref

definition term_pass :: \<open>(nat,string)shared_vars \<Rightarrow> sllist_polynomial list \<Rightarrow> sllist_polynomial list nres\<close> where
  \<open>term_pass \<V> = mcmp_pass (term_cmp \<V>) (term_valid \<V>) (term_mcmp \<V>)\<close>

sepref_register term_pass
sepref_def term_pass_impl
  is \<open>uncurry term_pass\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a (cl_assn' poly_s_assn)\<^sup>d \<rightarrow>\<^sub>a cl_assn' poly_s_assn\<close>
  unfolding term_pass_def mcmp_pass_def term_merge_while_def[symmetric]
    ls_emp ls_emp'
  by sepref

definition term_run_passes :: \<open>(nat,string)shared_vars \<Rightarrow> sllist_polynomial list \<Rightarrow> sllist_polynomial list nres\<close> where
  \<open>term_run_passes \<V> = mcmp_run_passes (term_cmp \<V>) (term_valid \<V>) (term_mcmp \<V>)\<close>

sepref_register term_run_passes
sepref_def term_run_passes_impl
  is \<open>uncurry term_run_passes\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a (cl_assn' poly_s_assn)\<^sup>d \<rightarrow>\<^sub>a cl_assn' poly_s_assn\<close>
  unfolding term_run_passes_def mcmp_run_passes_def term_pass_def[symmetric]
    ls_emp ls_emp'
  by sepref

interpretation poly_fa: freeable_assn poly_s_assn poly_s.cl_free
  by unfold_locales (rule poly_s.cl_assn_free)

sepref_register msort_monoms
sepref_def msort_monoms_impl
  is \<open>uncurry msort_monoms\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>d \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding msort_monoms_def mcmp_msort_def term_run_passes_def[symmetric]
    ls_emp ls_emp'
  by sepref

lemmas [sepref_fr_rules] = msort_monoms_impl.refine

sepref_register sort_all_coeffs_s
sepref_def sort_all_coeffs_s'_impl is \<open>uncurry sort_all_coeffs_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>d \<rightarrow>\<^sub>a poly_s_assn\<close>
  supply [[goals_limit=1]]
  unfolding sort_all_coeffs_s_alt_def
    ls_emp ls_emp'
  by sepref

lemmas [sepref_fr_rules] = sort_all_coeffs_s'_impl.refine

definition mc_body_s :: \<open>sllist_polynomial \<times> sllist_polynomial \<Rightarrow>
  (sllist_polynomial \<times> sllist_polynomial) nres\<close> where
  \<open>mc_body_s = (\<lambda>(r, p). doN {
        ((xs, n), p) \<leftarrow> mop_list_pop_hd p;
        if p = [] then
          if n = 0 then
            RETURN (r, p)
          else
            RETURN ((xs, n) # r, p)
        else doN {
          ((ys, m), p) \<leftarrow> mop_list_pop_hd p;
          if xs = ys then doN {
            let s = n + m;
            if s = 0 then
              RETURN (r, p)
            else
              RETURN (r, (xs, s) # p)
          } else
            if n = 0 then
              RETURN (r, (ys, m) # p)
            else
              RETURN ((xs, n) # r, (ys, m) # p)
        }
      })\<close>

definition merge_coeffs1_s :: \<open>sllist_polynomial \<Rightarrow> sllist_polynomial nres\<close> where
  \<open>merge_coeffs1_s p \<equiv> doN {
    (r, _) \<leftarrow> WHILE\<^sub>T (\<lambda>(_, p). p \<noteq> []) mc_body_s ([], p);
    RETURN (rev r)
  }\<close>

lemma merge_coeffs1_s_loop:
  \<open>WHILE\<^sub>T (\<lambda>(_, p). p \<noteq> []) mc_body_s (r, p) = RETURN (rev (merge_coeffs0_s p) @ r, [])\<close>
  apply (induction p arbitrary: r rule: merge_coeffs0_s.induct)
  subgoal by (simp add: WHILET_exit)
  subgoal by (subst WHILET_unfold) (auto simp: mc_body_s_def WHILET_exit)
  subgoal by (subst WHILET_unfold) (auto simp: mc_body_s_def WHILET_exit)
  done

lemma merge_coeffs1_s_correct:
  \<open>merge_coeffs1_s = (RETURN o merge_coeffs0_s)\<close>
  by (intro ext) (simp add: merge_coeffs1_s_def merge_coeffs1_s_loop)

interpretation si64: eq_assn si64_assn ll_icmp_eq
  by unfold_locales (rule hn_snat_ops(7))

sepref_register \<open>(=) :: nat list \<Rightarrow> nat list \<Rightarrow> bool\<close>
sepref_def merge_coeffs0_s_impl
  is \<open>RETURN o merge_coeffs0_s\<close>
  :: \<open>poly_s_assn\<^sup>d \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding merge_coeffs1_s_correct[symmetric]
  unfolding merge_coeffs1_s_def mc_body_s_def ls_emp ls_emp'
  by sepref
  
sepref_def full_normalize_poly'_impl
  is \<open>uncurry full_normalize_poly_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>d \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding full_normalize_poly_s_def
  by sepref

text \<open>Structural equality on shared polynomials: monoms compare via \<open>si64.cl_eq\<close>,
  coefficients via \<open>signed_big_int_eq_impl\<close>; the \<open>eq_assn\<close> interpretation lifts
  the pair equality to \<open>poly_s_assn\<close> (cf. \<open>mnml_eq_impl'\<close> in \<open>LLVM_Polynomials\<close>).\<close>

definition mnml_s_eq_impl' where [llvm_code]:
  \<open>mnml_s_eq_impl' \<equiv> \<lambda>(pm,pn) (qm,qn). doM {
    r \<leftarrow> si64.cl_eq pm qm;
    llc_if r (signed_big_int_eq_impl pn qn) (Mreturn 0)
  }\<close>

context begin
interpretation llvm_prim_ctrl_setup .

lemma mnml_s_eq_hnr[sepref_fr_rules]:
  \<open>(uncurry mnml_s_eq_impl', uncurry (RETURN oo (=)))
  \<in> (monom_s_assn \<times>\<^sub>a sbi_assn)\<^sup>k *\<^sub>a (monom_s_assn \<times>\<^sub>a sbi_assn)\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding mnml_s_eq_impl'_def
  supply [vcg_rules] = hfref_htriple_k2[OF signed_big_int_eq_impl_hnr]
  supply [simp] = pure_def bool1_rel_def bool.rel_def in_br_conv
  by (sepref_to_hoare; vcg)

end

interpretation poly_s: eq_assn \<open>monom_s_assn \<times>\<^sub>a sbi_assn\<close> mnml_s_eq_impl'
  by unfold_locales (rule mnml_s_eq_hnr)

sepref_register poly_s_eq: \<open>(=) :: sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> bool\<close>

lemma weak_equality_l_s_alt_def:
  \<open>weak_equality_l_s = RETURN oo (\<lambda>p q. p = q)\<close>
  unfolding weak_equality_l_s_def weak_equality_l_s_def by (auto intro!: ext)

sepref_def weak_equality_l_s_impl
  is \<open>uncurry weak_equality_l_s\<close>
  :: \<open>poly_s_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding weak_equality_l_s_alt_def
  by sepref

text \<open>The map from ids to shared polynomials, built exactly like \<open>polys_assn\<close>
  in \<open>PAC_Checker_Synthesis\<close>: a boxed copying partial map with \<open>poly_s_assn\<close>
  values, composed to the \<open>fmap\<close> interface. The generic \<open>fref\<close> lemmas
  (\<open>fmempty_empty\<close>, \<open>map_upd_fmupd\<close>, \<dots>) are inherited from that theory.\<close>

interpretation polys_s: boxed_copying_pmap
  \<open>poly_s_assn\<close> \<open>poly_s.cl_free\<close> \<open>poly_s.cl_copy\<close>
  apply unfold_locales
  apply (rule poly_s.cl_assn_free poly_s.cl_copy_hnr)+
  done

abbreviation polys_s_assn where
  \<open>polys_s_assn \<equiv> hr_comp (hr_comp polys_s.bx.pmap_assn' opt_list_map_rel) map_fmap_rel\<close>

lemma polys_s_assn_intf[intf_of_assn]:
  \<open>intf_of_assn polys_s_assn TYPE((nat, (nat list \<times> int) list) f_map)\<close>
  by simp

lemmas fmap_s_empty_hnr[sepref_fr_rules] =
  polys_s.bx.pmap_empty_hnr2[FCOMP fmempty_empty, unfolded op_fmap_empty_def[symmetric]]

lemmas fmap_s_delete_hnr[sepref_fr_rules] =
  polys_s.bx.pmap_delete_hnr2[FCOMP fmdrop_set_None]

lemmas fmap_s_update_hnr[sepref_fr_rules] =
  polys_s.bx.pmap_update_hnr2[FCOMP map_upd_fmupd]

lemmas fmap_s_lookup_hnr[sepref_fr_rules] =
  polys_s.bx.cpmap_lookup_hnr2[FCOMP op_map_lookup_fmlookup]

lemmas fmap_s_contains_key_hnr[sepref_fr_rules] =
  polys_s.bx.pmap_contains_key_hnr2[FCOMP map_fmap_contains_key]

lemmas fmap_s_the_lookup_hnr[sepref_fr_rules] =
  polys_s.bx.cpmap_the_lookup_hnr2[FCOMP op_the_lookup_refine]

lemma polys_s_assn_free[sepref_frame_free_rules]:
  \<open>MK_FREE polys_s_assn polys_s.bx.pmap_free\<close>
  by (intro MK_FREE_hrcompI polys_s.bx.pmap_free_rule)

text \<open>The abstract imports walk their input with \<open>hd\<close>/\<open>tl\<close>; on owned cl-lists
  this becomes a destructive pop-walk (mode \<open>d\<close>), cf. the non-efficient checker.\<close>

lemma import_monom_no_newS_alt_def:
  \<open>(import_monom_no_newS :: (nat,string)shared_vars \<Rightarrow> _) \<A> xs = do {
  (new, _, xs) \<leftarrow> WHILE\<^sub>T (\<lambda>(new, xs, _). \<not>new \<and> xs \<noteq> [])
    (\<lambda>(_, xs, ys). do {
      (x, xs) \<leftarrow> mop_list_pop_hd xs;
      b \<leftarrow> is_new_variableS x \<A>;
      if b
      then RETURN (True, xs, ys)
      else do {
        x \<leftarrow> get_var_posS \<A> x;
        RETURN (False, xs, x # ys)
       }
    })
    (False, xs, []);
  RETURN (new, rev xs)
 }\<close>
proof -
  have body_eq: \<open>(\<lambda>(_, xs, ys). do {
      ASSERT(xs \<noteq> []);
      let x = hd xs;
      b \<leftarrow> is_new_variableS x \<A>;
      if b
      then RETURN (True, tl xs, ys)
      else do {
        x \<leftarrow> get_var_posS \<A> x;
        RETURN (False, tl xs, x # ys)
       }
    }) = (\<lambda>(_, xs, ys). do {
      (x, xs) \<leftarrow> mop_list_pop_hd xs;
      b \<leftarrow> is_new_variableS x \<A>;
      if b
      then RETURN (True, xs, ys)
      else do {
        x \<leftarrow> get_var_posS \<A> x;
        RETURN (False, xs, x # ys)
       }
    })\<close> for \<A> :: \<open>(nat,string)shared_vars\<close>
    by (intro ext)
     (auto simp: mop_list_pop_hd_def pw_eq_iff refine_pw_simps Let_def split: prod.splits)
  show ?thesis
    unfolding import_monom_no_newS_def body_eq ..
qed

sepref_register import_monom_no_newS import_poly_no_newS check_linear_combi_l_pre_err

sepref_def import_monom_no_newS_impl
  is \<open>uncurry (import_monom_no_newS :: (nat,string)shared_vars \<Rightarrow> _ \<Rightarrow>( bool \<times> _) nres)\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a monom_assn\<^sup>d \<rightarrow>\<^sub>a bool1_assn \<times>\<^sub>a monom_s_assn\<close>
  unfolding import_monom_no_newS_alt_def ls_emp ls_emp'
  by sepref

lemmas [sepref_fr_rules] =
  import_monom_no_newS_impl.refine weak_equality_l_s_impl.refine

lemma import_poly_no_newS_alt_def:
  \<open>(import_poly_no_newS :: (nat,string)shared_vars \<Rightarrow> llist_polynomial \<Rightarrow> _) \<A> xs = do {
  (new, _, xs) \<leftarrow> WHILE\<^sub>T (\<lambda>(new, xs, _). \<not>new \<and> xs \<noteq> [])
    (\<lambda>(_, xs, ys). do {
      ((x, n), xs) \<leftarrow> mop_list_pop_hd xs;
      (b, x) \<leftarrow> import_monom_no_newS \<A> x;
      if b
      then RETURN (True, xs, ys)
      else do {
        RETURN (False, xs, (x, n) # ys)
       }
    })
    (False, xs, []);
  RETURN (new, rev xs)
 }\<close>
proof -
  have body_eq: \<open>(\<lambda>(_, xs, ys). do {
      ASSERT(xs \<noteq> []);
      let (x, n) = hd xs;
      (b, x) \<leftarrow> import_monom_no_newS \<A> x;
      if b
      then RETURN (True, tl xs, ys)
      else do {
        RETURN (False, tl xs, (x, n) # ys)
       }
    }) = (\<lambda>(_, xs, ys). do {
      ((x, n), xs) \<leftarrow> mop_list_pop_hd xs;
      (b, x) \<leftarrow> import_monom_no_newS \<A> x;
      if b
      then RETURN (True, xs, ys)
      else do {
        RETURN (False, xs, (x, n) # ys)
       }
    })\<close> for \<A> :: \<open>(nat,string)shared_vars\<close>
    by (intro ext)
     (auto simp: mop_list_pop_hd_def pw_eq_iff refine_pw_simps Let_def split: prod.splits)
  show ?thesis
    unfolding import_poly_no_newS_def body_eq ..
qed

sepref_def import_poly_no_newS_impl
  is \<open>uncurry (import_poly_no_newS :: (nat,string)shared_vars \<Rightarrow> llist_polynomial \<Rightarrow>( bool \<times> sllist_polynomial) nres)\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>d \<rightarrow>\<^sub>a bool1_assn \<times>\<^sub>a poly_s_assn\<close>
  unfolding import_poly_no_newS_alt_def ls_emp ls_emp'
  by sepref

lemmas [sepref_fr_rules] =
  import_poly_no_newS_impl.refine

text \<open>Read-only walk testing that all variables of a polynomial are known in
  the shared table, mirroring \<open>vars_of_poly_in\<close> in \<open>PAC_Checker_Synthesis\<close>:
  a \<open>cl_fold\<close> at the monom level (membership per variable) and another one at
  the poly level.\<close>

fun vars_of_monom_in_s :: \<open>string list \<Rightarrow> (nat, string) shared_vars \<Rightarrow> bool\<close> where
  \<open>vars_of_monom_in_s [] _ = True\<close> |
  \<open>vars_of_monom_in_s (x # xs) \<V> \<longleftrightarrow> x \<in># dom_m (snd (snd \<V>)) \<and> vars_of_monom_in_s xs \<V>\<close>

fun vars_of_poly_in_s :: \<open>llist_polynomial \<Rightarrow> (nat, string) shared_vars \<Rightarrow> bool\<close> where
  \<open>vars_of_poly_in_s [] _ = True\<close> |
  \<open>vars_of_poly_in_s ((xs, _) # p) \<V> \<longleftrightarrow> vars_of_monom_in_s xs \<V> \<and> vars_of_poly_in_s p \<V>\<close>

lemma vars_of_monom_in_s_alt_def:
  \<open>vars_of_monom_in_s xs \<V> \<longleftrightarrow> set xs \<subseteq> set_mset (dom_m (snd (snd \<V>)))\<close>
  by (induction xs) auto

lemma vars_llist_in_s_alt_def:
  \<open>vars_llist_in_s = (\<lambda>\<V> p. vars_of_poly_in_s p \<V>)\<close>
proof (intro ext)
  fix \<V> :: \<open>(nat, string) shared_vars\<close> and p
  show \<open>vars_llist_in_s \<V> p = vars_of_poly_in_s p \<V>\<close>
    by (cases \<V>)
     (induction p;
      auto simp: vars_llist_in_s_def vars_llist_def vars_of_monom_in_s_alt_def)
qed

definition s_fold_inner :: \<open>(nat, string) shared_vars \<Rightarrow> bool \<Rightarrow> string \<Rightarrow> bool\<close> where
  \<open>s_fold_inner \<V> \<equiv> \<lambda>b x. b \<and> x \<in># dom_m (snd (snd \<V>))\<close>

lemma s_fold_inner_alt:
  \<open>(RETURN ooo s_fold_inner) \<V> b x = do { n \<leftarrow> is_new_variableS x \<V>; RETURN (b \<and> \<not>n) }\<close>
  by (cases \<V>) (auto simp: s_fold_inner_def is_new_variableS_def)

sepref_def s_fold_inner_impl is \<open>uncurry2 (RETURN ooo s_fold_inner)\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a strl_assn'\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding s_fold_inner_alt
  by sepref

definition \<open>vars_of_monom_in_s_impl xs \<V> \<equiv> cl_fold (s_fold_inner_impl \<V>) (xs, 1)\<close>

lemma s_fold_inner_step_rule:
  \<open>llvm_htriple
    ((bool1_assn b bi ** shared_vars_assn \<V> vi) ** strl_assn' x xi)
    (s_fold_inner_impl vi bi xi)
    (\<lambda>r. (bool1_assn (s_fold_inner \<V> b x) r ** shared_vars_assn \<V> vi) ** strl_assn' x xi)\<close>
  supply [vcg_rules] = hfref_htriple_k3[OF s_fold_inner_impl.refine]
  apply vcg
  unfolding ENTAILS_def
  by (auto simp: entails_def pure_def sep_algebra_simps)

lemmas vars_of_monom_in_s_walk_rule =
  cl_fold_rule[where R = \<open>\<lambda>b r. bool1_assn b r ** shared_vars_assn \<V> vi\<close>
    and fa = \<open>s_fold_inner \<V>\<close> and A = strl_assn' for \<V> vi,
    OF s_fold_inner_step_rule]

lemma vars_of_monom_in_s_foldl:
  \<open>foldl (s_fold_inner \<V>) b xs = (b \<and> vars_of_monom_in_s xs \<V>)\<close>
  by (induction xs arbitrary: b) (auto simp: s_fold_inner_def)

lemma vars_of_monom_in_s_impl_hnr[sepref_fr_rules]:
  \<open>(uncurry vars_of_monom_in_s_impl, uncurry (RETURN oo vars_of_monom_in_s))
  \<in> monom_assn\<^sup>k *\<^sub>a shared_vars_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding vars_of_monom_in_s_impl_def
  apply sepref_to_hoare
  supply [vcg_rules] = vars_of_monom_in_s_walk_rule
  supply [simp] = vars_of_monom_in_s_foldl bool1_rel_def bool.rel_def in_br_conv
    pure_def
  by vcg

sepref_register vars_of_monom_in_s

definition s_poly_inner :: \<open>(nat, string) shared_vars \<Rightarrow> bool \<Rightarrow> string list \<times> int \<Rightarrow> bool\<close> where
  \<open>s_poly_inner \<V> \<equiv> \<lambda>b (vs, _). b \<and> vars_of_monom_in_s vs \<V>\<close>

sepref_def s_poly_inner_impl is \<open>uncurry2 (RETURN ooo s_poly_inner)\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a monomial_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding s_poly_inner_def
  by sepref

definition \<open>vars_of_poly_in_s_impl xs \<V> \<equiv> cl_fold (s_poly_inner_impl \<V>) (xs, 1)\<close>

lemma s_poly_inner_step_rule:
  \<open>llvm_htriple
    ((bool1_assn b bi ** shared_vars_assn \<V> vi) ** monomial_assn x xi)
    (s_poly_inner_impl vi bi xi)
    (\<lambda>r. (bool1_assn (s_poly_inner \<V> b x) r ** shared_vars_assn \<V> vi) ** monomial_assn x xi)\<close>
  supply [vcg_rules] = hfref_htriple_k3[OF s_poly_inner_impl.refine]
  apply vcg
  unfolding ENTAILS_def
  by (auto simp: entails_def pure_def sep_algebra_simps)

lemmas vars_of_poly_in_s_walk_rule =
  cl_fold_rule[where R = \<open>\<lambda>b r. bool1_assn b r ** shared_vars_assn \<V> vi\<close>
    and fa = \<open>s_poly_inner \<V>\<close> and A = monomial_assn for \<V> vi,
    OF s_poly_inner_step_rule]

lemma vars_of_poly_in_s_foldl:
  \<open>foldl (s_poly_inner \<V>) b xs = (b \<and> vars_of_poly_in_s xs \<V>)\<close>
  apply (induction xs arbitrary: b)
  subgoal by simp
  subgoal for p xs b by (cases p) (auto simp: s_poly_inner_def)
  done

lemma vars_of_poly_in_s_impl_hnr[sepref_fr_rules]:
  \<open>(uncurry vars_of_poly_in_s_impl, uncurry (RETURN oo vars_of_poly_in_s))
  \<in> polynomial_assn\<^sup>k *\<^sub>a shared_vars_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding vars_of_poly_in_s_impl_def
  apply sepref_to_hoare
  supply [vcg_rules] = vars_of_poly_in_s_walk_rule
  supply [simp] = vars_of_poly_in_s_foldl bool1_rel_def bool.rel_def in_br_conv
    pure_def
  by vcg

sepref_register vars_of_poly_in_s

sepref_def vars_llist_in_s_impl
  is \<open>uncurry (RETURN oo vars_llist_in_s)\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding vars_llist_in_s_alt_def
  by sepref
lemmas [sepref_fr_rules] = vars_llist_in_s_impl.refine



sepref_register mult_poly_s normalize_poly_s
sepref_def normalize_poly_sharedS_impl
  is \<open>uncurry normalize_poly_sharedS\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>d \<rightarrow>\<^sub>a bool1_assn \<times>\<^sub>a poly_s_assn\<close>
  unfolding normalize_poly_sharedS_def
  by sepref

lemmas [sepref_fr_rules] = normalize_poly_sharedS_impl.refine
  mult_poly_s_impl.refine
text \<open>Same accumulator-loop treatment as for \<open>merge_coeffs0_s\<close> above; the only
  differences are that a trailing singleton is kept unconditionally and that
  no zero-filtering happens in the \<open>\<noteq>\<close> branch.\<close>

definition mc2_body_s :: \<open>sllist_polynomial \<times> sllist_polynomial \<Rightarrow>
  (sllist_polynomial \<times> sllist_polynomial) nres\<close> where
  \<open>mc2_body_s = (\<lambda>(r, p). doN {
        ((xs, n), p) \<leftarrow> mop_list_pop_hd p;
        if p = [] then
          RETURN ((xs, n) # r, p)
        else doN {
          ((ys, m), p) \<leftarrow> mop_list_pop_hd p;
          if xs = ys then doN {
            let s = n + m;
            if s = 0 then
              RETURN (r, p)
            else
              RETURN (r, (xs, s) # p)
          } else
            RETURN ((xs, n) # r, (ys, m) # p)
        }
      })\<close>

definition merge_coeffs2_s :: \<open>sllist_polynomial \<Rightarrow> sllist_polynomial nres\<close> where
  \<open>merge_coeffs2_s p \<equiv> doN {
    (r, _) \<leftarrow> WHILE\<^sub>T (\<lambda>(_, p). p \<noteq> []) mc2_body_s ([], p);
    RETURN (rev r)
  }\<close>

lemma merge_coeffs2_s_loop:
  \<open>WHILE\<^sub>T (\<lambda>(_, p). p \<noteq> []) mc2_body_s (r, p) = RETURN (rev (merge_coeffs_s p) @ r, [])\<close>
  apply (induction p arbitrary: r rule: merge_coeffs_s.induct)
  subgoal by (simp add: WHILET_exit)
  subgoal by (subst WHILET_unfold) (auto simp: mc2_body_s_def WHILET_exit)
  subgoal by (subst WHILET_unfold) (auto simp: mc2_body_s_def WHILET_exit)
  done

lemma merge_coeffs2_s_correct:
  \<open>merge_coeffs2_s = (RETURN o merge_coeffs_s)\<close>
  by (intro ext) (simp add: merge_coeffs2_s_def merge_coeffs2_s_loop)

sepref_def merge_coeffs_s_impl
  is \<open>(RETURN o merge_coeffs_s)\<close>
  :: \<open>poly_s_assn\<^sup>d \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding merge_coeffs2_s_correct[symmetric]
  unfolding merge_coeffs2_s_def mc2_body_s_def ls_emp ls_emp'
  by sepref

lemmas [sepref_fr_rules] = merge_coeffs_s_impl.refine

sepref_def normalize_poly_s_impl
  is \<open>uncurry normalize_poly_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>d \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding normalize_poly_s_def
  by sepref

lemmas [sepref_fr_rules] = normalize_poly_s_impl.refine

sepref_def mult_poly_full_s_impl
  is \<open>uncurry2 mult_poly_full_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k*\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding mult_poly_full_s_def
  by sepref

lemmas [sepref_fr_rules] = mult_poly_full_s_impl.refine
  add_poly_l_prep_impl.refine

sepref_register add_poly_l_s

text \<open>The \<open>hd\<close>/\<open>tl\<close> walk over the linear combination becomes a pop-walk that
  re-prepends the pair in the error branch, exactly like \<open>linear_combi_alt\<close>
  in \<open>LPAC_Checker_Synthesis\<close>.\<close>

lemma linear_combi_l_prep_s_alt:
  \<open>linear_combi_l_prep_s i A \<V> xs = do {
  WHILE\<^sub>T
    (\<lambda>(p, xs, err). xs \<noteq> [] \<and> \<not>is_cfailed err)
    (\<lambda>(p, xs, _). do {
      ((q :: llist_polynomial, i), xt) \<leftarrow> mop_list_pop_hd xs;
      if (i \<notin># dom_m A \<or> \<not>(vars_llist_in_s \<V> q))
      then do {
        err \<leftarrow> check_linear_combi_l_s_dom_err p i;
        RETURN (p, (q, i) # xt, error_msg i err)
      } else do {
        ASSERT(fmlookup A i \<noteq> None);
        let r = the (fmlookup A i);
        if q = [([], 1)]
        then do {
          pq \<leftarrow> add_poly_l_s \<V> (p, r);
          RETURN (pq, xt, CSUCCESS)}
        else do {
          (no_new, q) \<leftarrow> normalize_poly_sharedS \<V> (q);
          q \<leftarrow> mult_poly_full_s \<V> q r;
          pq \<leftarrow> add_poly_l_s \<V> (p, q);
          RETURN (pq, xt, CSUCCESS)
        }
        }
        })
        ([], xs, CSUCCESS)
          }\<close>
proof -
  have H: \<open>(q\<^sub>0, ia) # tl ys = ys\<close> if \<open>hd ys = (q\<^sub>0, ia)\<close> \<open>ys \<noteq> []\<close>
    for q\<^sub>0 ia and ys :: \<open>(llist_polynomial \<times> nat) list\<close>
    using that by (cases ys) auto
  show ?thesis
    unfolding linear_combi_l_prep_s_def mop_list_pop_hd_def
    apply (rule arg_cong2[where f = \<open>\<lambda>c b. WHILE\<^sub>T c b ([], xs, CSUCCESS)\<close>])
    subgoal by (rule refl)
    apply (intro ext)
    apply (clarsimp split!: prod.splits list.splits simp: H)
    apply (auto simp: H pw_eq_iff refine_pw_simps)
    done
qed

sepref_def linear_combi_l_prep_s_impl
  is \<open>uncurry3 linear_combi_l_prep_s\<close>
  :: \<open>si64_assn\<^sup>k *\<^sub>a polys_s_assn\<^sup>k *\<^sub>a shared_vars_assn\<^sup>k *\<^sub>a
  (cl_assn' (polynomial_assn \<times>\<^sub>a si64_assn))\<^sup>d  \<rightarrow>\<^sub>a
  poly_s_assn \<times>\<^sub>a (cl_assn' (polynomial_assn \<times>\<^sub>a si64_assn)) \<times>\<^sub>a status_assn
  \<close>
  supply [[goals_limit=1]]
  unfolding linear_combi_l_prep_s_alt
    fmlookup'_def[symmetric]
    in_dom_by_contains
    ls_emp ls_emp'
  by sepref

lemmas [sepref_fr_rules] = linear_combi_l_prep_s_impl.refine


sepref_register linear_combi_l_prep_s ::
  \<open>nat \<Rightarrow> (nat, sllist_polynomial) f_map \<Rightarrow> (nat, string) shared_vars \<Rightarrow>
    (llist_polynomial \<times> nat) list \<Rightarrow>
    (sllist_polynomial \<times> (llist_polynomial \<times> nat) list \<times> string code_status) nres\<close>

section \<open>Printing of Shared Polynomials\<close>

text \<open>Error messages print shared polynomials with their \<^emph>\<open>numeric\<close> variable
  indices, as the original Pasteque did (\<open>show (map (\<lambda>(a,b). (map nat_of_uint64 a, b)) p)\<close>);
  the construction mirrors \<open>print_monom\<close>/\<open>poly_print\<close> in \<open>LLVM_Polynomials\<close>.\<close>

definition print_monom_s_inner :: \<open>char list \<Rightarrow> nat \<Rightarrow> char list\<close> where
  \<open>print_monom_s_inner \<equiv> \<lambda>acc v. acc @ cl_to_clt '' x'' @ show_nat v\<close>

sepref_def print_monom_s_inner_impl is \<open>uncurry (RETURN oo print_monom_s_inner)\<close>
  :: \<open>strlt_assn\<^sup>d *\<^sub>a si64_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding print_monom_s_inner_def
  by sepref

definition print_monom_s :: \<open>nat list \<Rightarrow> char list\<close> where
  \<open>print_monom_s \<equiv> foldl print_monom_s_inner []\<close>

definition \<open>print_monom_s_impl \<equiv> \<lambda>m. doM {e \<leftarrow> clt_empty; cl_fold' print_monom_s_inner_impl e m}\<close>

lemma print_monom_s_rule: \<open>llvm_htriple
  (monom_s_assn m mi)
  (print_monom_s_impl mi)
  (\<lambda>r. monom_s_assn m mi ** strlt_assn (print_monom_s m) r)\<close>
proof -
  have INNER_vcg: \<open>llvm_htriple
    (strlt_assn acc acci ** si64_assn t ti)
    (print_monom_s_inner_impl acci ti)
    (\<lambda>r. strlt_assn (print_monom_s_inner acc t) r ** si64_assn t ti)\<close> for acc acci t ti
    apply (rule htriple_ent_post[OF _ hfref_htriple_d1_k2[OF print_monom_s_inner_impl.refine]])
    by (simp add: sep_conj_aci)
  show ?thesis
    unfolding print_monom_s_impl_def
    supply [vcg_rules] = cl_fold'_rule[where R="strlt_assn" and A="si64_assn"
      and f=print_monom_s_inner_impl and fa=print_monom_s_inner,
      OF INNER_vcg]
    supply [simp] = print_monom_s_def
    by vcg
qed

lemma print_monom_s_hnr[sepref_fr_rules]:
  \<open>(print_monom_s_impl, (RETURN o print_monom_s))
  \<in> monom_s_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding snat_rel_def snat.assn_is_rel[symmetric]
  apply (sepref_to_hoare)
  supply [vcg_rules] = print_monom_s_rule[unfolded snat_rel_def snat.assn_is_rel[symmetric]]
  supply [simp] = pure_def
  by vcg

definition \<open>mnml_s_print \<equiv> \<lambda>(m,n). cl_to_clt (chars_of_int (COPY n)) @ print_monom_s m\<close>

sepref_def mnml_s_print_impl is \<open>RETURN o mnml_s_print\<close>
  :: \<open>(monom_s_assn \<times>\<^sub>a sbi_assn)\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding mnml_s_print_def
  by sepref

definition poly_s_print_inner :: \<open>char list \<Rightarrow> nat list \<times> int \<Rightarrow> char list\<close> where
  \<open>poly_s_print_inner \<equiv> \<lambda>acc p. acc @ mnml_s_print p\<close>

sepref_def poly_s_print_inner_impl is \<open>uncurry (RETURN oo poly_s_print_inner)\<close>
  :: \<open>strlt_assn\<^sup>d *\<^sub>a (monom_s_assn \<times>\<^sub>a sbi_assn)\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding poly_s_print_inner_def
  by sepref

definition poly_s_print :: \<open>sllist_polynomial \<Rightarrow> string\<close> where
  \<open>poly_s_print \<equiv> foldl poly_s_print_inner []\<close>

definition \<open>poly_s_print_impl \<equiv> \<lambda>ps. doM {e \<leftarrow> clt_empty; cl_fold' poly_s_print_inner_impl e ps}\<close>

lemma poly_s_print_rule: \<open>llvm_htriple
  (poly_s_assn ps psi)
  (poly_s_print_impl psi)
  (\<lambda>r. poly_s_assn ps psi ** strlt_assn (poly_s_print ps) r)\<close>
proof -
  have INNER_vcg: \<open>llvm_htriple
    (strlt_assn acc acci ** (monom_s_assn \<times>\<^sub>a sbi_assn) p pi)
    (poly_s_print_inner_impl acci pi)
    (\<lambda>r. strlt_assn (poly_s_print_inner acc p) r ** (monom_s_assn \<times>\<^sub>a sbi_assn) p pi)\<close> for acc acci p pi
    apply (rule htriple_ent_post[OF _ hfref_htriple_d1_k2[OF poly_s_print_inner_impl.refine]])
    by (simp add: sep_conj_aci)
  show ?thesis
    unfolding poly_s_print_impl_def
    supply [vcg_rules] = cl_fold'_rule[where R="strlt_assn" and A="monom_s_assn \<times>\<^sub>a sbi_assn"
      and f=poly_s_print_inner_impl and fa=poly_s_print_inner,
      OF INNER_vcg]
    supply [simp] = poly_s_print_def
    by vcg
qed

lemma poly_s_print_hnr[sepref_fr_rules]:
  \<open>(poly_s_print_impl, (RETURN o poly_s_print))
  \<in> poly_s_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding snat_rel_def snat.assn_is_rel[symmetric]
  apply (sepref_to_hoare)
  supply [vcg_rules] = poly_s_print_rule[unfolded snat_rel_def snat.assn_is_rel[symmetric]]
  supply [simp] = pure_def
  by vcg

section \<open>Error Messages for Shared Polynomials\<close>

definition check_linear_combi_l_s_mult_err_imp :: \<open>sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> string\<close> where
  \<open>check_linear_combi_l_s_mult_err_imp xs ys =
  cl_to_clt ''Unequal polynom found in CL '' @ poly_s_print xs @
  cl_to_clt '' but '' @ poly_s_print ys\<close>

sepref_def check_linear_combi_l_s_mult_err_impl is
  \<open>uncurry (RETURN oo check_linear_combi_l_s_mult_err_imp)\<close>
  :: \<open>poly_s_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding check_linear_combi_l_s_mult_err_imp_def
  by sepref

lemma check_linear_combi_l_s_mult_err_fref:
  \<open>(uncurry (RETURN oo check_linear_combi_l_s_mult_err_imp),
    uncurry check_linear_combi_l_s_mult_err) \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding check_linear_combi_l_s_mult_err_imp_def
    check_linear_combi_l_s_mult_err_def
  by auto

lemmas check_linear_combi_l_s_mult_err_hnr[sepref_fr_rules] =
  check_linear_combi_l_s_mult_err_impl.refine[FCOMP check_linear_combi_l_s_mult_err_fref]

definition check_extension_l_s_new_var_multiple_err_imp :: \<open>string \<Rightarrow> sllist_polynomial \<Rightarrow> string\<close> where
  \<open>check_extension_l_s_new_var_multiple_err_imp v p =
  cl_to_clt ''Variable already defined '' @ cl_to_clt v @
  cl_to_clt '' but '' @ poly_s_print p\<close>

sepref_def check_extension_l_s_new_var_multiple_err_impl is
  \<open>uncurry (RETURN oo check_extension_l_s_new_var_multiple_err_imp)\<close>
  :: \<open>strl_assn'\<^sup>k *\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding check_extension_l_s_new_var_multiple_err_imp_def
  by sepref

lemma check_extension_l_s_new_var_multiple_err_fref:
  \<open>(uncurry (RETURN oo check_extension_l_s_new_var_multiple_err_imp),
    uncurry check_extension_l_s_new_var_multiple_err) \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding check_extension_l_s_new_var_multiple_err_imp_def
    check_extension_l_s_new_var_multiple_err_def
  by auto

lemmas check_extension_l_s_new_var_multiple_err_hnr[sepref_fr_rules] =
  check_extension_l_s_new_var_multiple_err_impl.refine[FCOMP check_extension_l_s_new_var_multiple_err_fref]

definition check_extension_l_s_side_cond_err_imp
  :: \<open>string \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> string\<close>
where
  \<open>check_extension_l_s_side_cond_err_imp v p p' q' =
  cl_to_clt ''p^2- p != 0 '' @ cl_to_clt v @
  cl_to_clt '' but '' @ poly_s_print p @
  cl_to_clt '' and '' @ poly_s_print p' @
  cl_to_clt '' and '' @ poly_s_print q'\<close>

sepref_def check_extension_l_s_side_cond_err_impl is
  \<open>uncurry3 (RETURN oooo check_extension_l_s_side_cond_err_imp)\<close>
  :: \<open>strl_assn'\<^sup>k *\<^sub>a poly_s_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding check_extension_l_s_side_cond_err_imp_def
  by sepref

lemma check_extension_l_s_side_cond_err_fref:
  \<open>(uncurry3 (RETURN oooo check_extension_l_s_side_cond_err_imp),
    uncurry3 check_extension_l_s_side_cond_err) \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding check_extension_l_s_side_cond_err_imp_def
    check_extension_l_s_side_cond_err_def
  by auto

lemmas check_extension_l_s_side_cond_err_hnr[sepref_fr_rules] =
  check_extension_l_s_side_cond_err_impl.refine[FCOMP check_extension_l_s_side_cond_err_fref]

sepref_def check_linear_combi_l_s_impl
  is \<open>uncurry5 check_linear_combi_l_s\<close>
  :: \<open>poly_s_assn\<^sup>k *\<^sub>a polys_s_assn\<^sup>k *\<^sub>a shared_vars_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k *\<^sub>a
  (cl_assn' (polynomial_assn \<times>\<^sub>a si64_assn))\<^sup>d *\<^sub>a polynomial_assn\<^sup>d \<rightarrow>\<^sub>a status_assn \<times>\<^sub>a poly_s_assn
  \<close>
  supply [[goals_limit=1]]
  unfolding check_linear_combi_l_s_def
    in_dom_by_contains
    ls_emp ls_emp'
  by sepref

sepref_register fmlookup'
text \<open>Negation of a shared polynomial, mirroring \<open>uminus_poly\<close> in
  \<open>PAC_Checker_Synthesis\<close>: a destructive pop-walk negating each coefficient.\<close>

definition uminus_poly_s :: \<open>sllist_polynomial \<Rightarrow> sllist_polynomial\<close> where
  \<open>uminus_poly_s p = map (\<lambda>(a,b). (a,-b)) p\<close>

definition uminus_poly_s_nres :: \<open>sllist_polynomial \<Rightarrow> sllist_polynomial nres\<close> where
  \<open>uminus_poly_s_nres = REC\<^sub>T (\<lambda>f p.
    if p = [] then RETURN p
    else do {
      ((a,b), p) \<leftarrow> mop_list_pop_hd p;
      r \<leftarrow> f p; RETURN ((a, -b) # r)
    })\<close>

lemma uminus_poly_s_nres_spec: \<open>uminus_poly_s_nres p = RETURN (uminus_poly_s p)\<close>
  unfolding uminus_poly_s_nres_def uminus_poly_s_def
proof (induction p)
  case Nil
  show ?case by (subst RECT_unfold, refine_mono) auto
next
  case (Cons x p)
  show ?case
    apply (subst RECT_unfold, refine_mono)
    by (auto simp: Cons.IH split: prod.splits)
qed

sepref_register uminus_poly_s

sepref_def uminus_poly_s_impl is \<open>uminus_poly_s_nres\<close>
  :: \<open>poly_s_assn\<^sup>d \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding uminus_poly_s_nres_def ls_emp ls_emp'
  by sepref

lemma uminus_poly_s_fref:
  \<open>(uminus_poly_s_nres, RETURN o uminus_poly_s) \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: uminus_poly_s_nres_spec)

lemmas uminus_poly_s_hnr[sepref_fr_rules] =
  uminus_poly_s_impl.refine[FCOMP uminus_poly_s_fref]

text \<open>The alt-def only inserts the \<open>COPY\<close>s that the ownership discipline needs:
  \<open>p\<close> is still returned after being negated, and \<open>p''\<close> is consumed by
  \<open>add_poly_l_s\<close> but also printed in the side-condition error.\<close>

lemma check_extension_l2_s_alt_def:
  \<open>check_extension_l2_s spec A \<V> i v p = do {
  n \<leftarrow> is_new_variableS v \<V>;
  let pre = i \<notin># dom_m A \<and> n;
  let nonew = vars_llist_in_s \<V> p;
  (mem, p, \<V>) \<leftarrow> import_polyS \<V> p;
  let pre = (pre \<and> \<not>alloc_failed mem);
  if \<not>pre
  then do {
    c \<leftarrow> check_extension_l_dom_err i;
    RETURN (error_msg i c, [], \<V>, 0)
  } else do {
      if \<not>nonew
      then do {
        c \<leftarrow> check_extension_l_s_new_var_multiple_err v p;
        RETURN (error_msg i c, [], \<V>, 0)
      }
      else do {
        (mem', \<V>, v') \<leftarrow> import_variableS v \<V>;
        if alloc_failed mem'
        then do {
          c \<leftarrow> check_extension_l_dom_err i;
          RETURN (error_msg i c, [], \<V>, 0)
        } else
        do {
         p2 \<leftarrow> mult_poly_full_s \<V> p p;
         let p'' = uminus_poly_s (COPY p);
         q \<leftarrow> add_poly_l_s \<V> (p2, COPY p'');
         eq \<leftarrow> weak_equality_l_s q [];
         if eq then do {
           RETURN (CSUCCESS, p, \<V>, v')
         } else do {
          c \<leftarrow> check_extension_l_s_side_cond_err v p p'' q;
          RETURN (error_msg i c, [], \<V>, v')
        }
      }
     }
  }
  }\<close>
  unfolding check_extension_l2_s_def uminus_poly_s_def COPY_def
  by simp

sepref_register import_monomS import_polyS

text \<open>\<open>import_monomS\<close>/\<open>import_polyS\<close> keep the unconsumed remainder of their input
  in the loop state on allocation failure. The pop-walks below pop from a
  \<open>COPY\<close> of the input (so the argument stays in keep mode) and re-prepend the
  popped element on the failure path \<emdash> \<open>import_variableS\<close>/\<open>import_monomS\<close> keep
  their argument, so it is still owned there. This gives literal body equality.\<close>

lemma import_monomS_alt_def:
  \<open>(import_monomS :: (nat, string) shared_vars \<Rightarrow> _) \<A> xs0 = do {
     xs \<leftarrow> RETURN (COPY xs0);
     (mem, _, ys, \<A>) \<leftarrow> WHILE\<^sub>T (\<lambda>(mem, xs, _, _). \<not>alloc_failed mem \<and> xs \<noteq> [])
       (\<lambda>(_, xs, ys, \<A>). do {
          (x, xs) \<leftarrow> mop_list_pop_hd xs;
          b \<leftarrow> is_new_variableS x \<A>;
          if b then do {
            (mem, \<A>, x') \<leftarrow> import_variableS x \<A>;
            if alloc_failed mem
            then RETURN (mem, x # xs, ys, \<A>)
            else RETURN (mem, xs, x' # ys, \<A>)
          }
          else do { x' \<leftarrow> get_var_posS \<A> x; RETURN (Allocated, xs, x' # ys, \<A>) }
       }) (Allocated, xs, [], \<A>);
     RETURN (mem, rev ys, \<A>)
  }\<close>
proof -
  have H: \<open>hd ys # tl ys = ys\<close> if \<open>ys \<noteq> []\<close> for ys :: \<open>string list\<close>
    using that by (cases ys) auto
  have body_eq: \<open>(\<lambda>(_, xs, ys, \<A>). do {
          ASSERT(xs \<noteq> []);
          let x = hd xs;
          b \<leftarrow> is_new_variableS x \<A>;
          if b
          then do {
            (mem, \<A>, x) \<leftarrow> import_variableS x \<A>;
            if alloc_failed mem
            then RETURN (mem, xs, ys, \<A>)
            else RETURN (mem, tl xs, x # ys, \<A>)
          }
          else do {
            x \<leftarrow> get_var_posS \<A> x;
            RETURN (Allocated, tl xs, x # ys, \<A>)
           }
        }) = (\<lambda>(_, xs, ys, \<A>). do {
          (x, xs) \<leftarrow> mop_list_pop_hd xs;
          b \<leftarrow> is_new_variableS x \<A>;
          if b then do {
            (mem, \<A>, x') \<leftarrow> import_variableS x \<A>;
            if alloc_failed mem
            then RETURN (mem, x # xs, ys, \<A>)
            else RETURN (mem, xs, x' # ys, \<A>)
          }
          else do { x' \<leftarrow> get_var_posS \<A> x; RETURN (Allocated, xs, x' # ys, \<A>) }
       })\<close> for \<A> :: \<open>(nat, string) shared_vars\<close>
    by (intro ext)
     (auto simp: mop_list_pop_hd_def Let_def H pw_eq_iff refine_pw_simps
        split: prod.splits)
  show ?thesis
    unfolding import_monomS_def COPY_def nres_monad1 body_eq ..
qed

sepref_def import_monomS_impl
  is \<open>uncurry (import_monomS :: (nat, string) shared_vars \<Rightarrow> _)\<close>
  :: \<open>shared_vars_assn\<^sup>d *\<^sub>a monom_assn\<^sup>k \<rightarrow>\<^sub>a memory_allocation_assn \<times>\<^sub>a monom_s_assn \<times>\<^sub>a shared_vars_assn\<close>
  supply [[goals_limit=1]]
  unfolding import_monomS_alt_def
    ls_emp ls_emp'
  by sepref

lemmas [sepref_fr_rules] = import_monomS_impl.refine

text \<open>The monom-import inside the poly walk is the \<^emph>\<open>abstract\<close> \<open>import_monomS\<close>,
  so its rule (keep mode on the monom) applies; the popped pair is re-prepended
  on the failure path and freed on the success path.\<close>

lemma import_polyS_alt_def:
  \<open>(import_polyS :: (nat, string) shared_vars \<Rightarrow> llist_polynomial \<Rightarrow> _) \<A> xs0 = do {
     xs \<leftarrow> RETURN (COPY xs0);
     (mem, _, ys, \<A>) \<leftarrow> WHILE\<^sub>T (\<lambda>(mem, xs, _, _). \<not>alloc_failed mem \<and> xs \<noteq> [])
       (\<lambda>(_, xs, ys, \<A>). do {
          ((x, n), xs) \<leftarrow> mop_list_pop_hd xs;
          (mem, x', \<A>) \<leftarrow> import_monomS \<A> x;
          if alloc_failed mem
          then RETURN (mem, (x, n) # xs, ys, \<A>)
          else RETURN (mem, xs, (x', n) # ys, \<A>)
       }) (Allocated, xs, [], \<A>);
     RETURN (mem, rev ys, \<A>)
  }\<close>
proof -
  have body_eq: \<open>(\<lambda>(mem, xs, ys, \<A>). do {
      ASSERT(xs \<noteq> []);
      let (x, n) = hd xs;
      (mem, x, \<A>) \<leftarrow> import_monomS \<A> x;
      if alloc_failed mem
      then RETURN (mem, xs, ys, \<A>)
      else do {
       RETURN (mem, tl xs, (x, n) # ys, \<A>)
      }
    }) = (\<lambda>(_, xs, ys, \<A>). do {
          ((x, n), xs) \<leftarrow> mop_list_pop_hd xs;
          (mem, x', \<A>) \<leftarrow> import_monomS \<A> x;
          if alloc_failed mem
          then RETURN (mem, (x, n) # xs, ys, \<A>)
          else RETURN (mem, xs, (x', n) # ys, \<A>)
       })\<close> for \<A> :: \<open>(nat, string) shared_vars\<close>
    by (intro ext)
     (auto simp: mop_list_pop_hd_def Let_def pw_eq_iff refine_pw_simps
        split: prod.splits; metis hd_Cons_tl)
  show ?thesis
    unfolding import_polyS_def COPY_def nres_monad1 body_eq ..
qed

sepref_def import_polyS_impl
  is \<open>uncurry (import_polyS :: (nat, string) shared_vars \<Rightarrow> llist_polynomial \<Rightarrow> _)\<close>
  :: \<open>shared_vars_assn\<^sup>d *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a memory_allocation_assn \<times>\<^sub>a poly_s_assn \<times>\<^sub>a shared_vars_assn\<close>
  supply [[goals_limit=1]]
  unfolding import_polyS_alt_def
    ls_emp ls_emp'
  by sepref

lemmas [sepref_fr_rules] = import_polyS_impl.refine

sepref_register mult_poly_full_s weak_equality_l_s check_extension_l_s_side_cond_err
     is_cfailed check_del_l

sepref_register check_extension_l2_s ::
  \<open>'b \<Rightarrow> (nat, 'c) f_map \<Rightarrow> (nat, string) shared_vars \<Rightarrow> nat \<Rightarrow> string \<Rightarrow>
    llist_polynomial \<Rightarrow>
    (string code_status \<times> sllist_polynomial \<times> (nat, string) shared_vars \<times> nat) nres\<close>

sepref_register check_linear_combi_l_s ::
  \<open>sllist_polynomial \<Rightarrow> (nat, sllist_polynomial) f_map \<Rightarrow> (nat, string) shared_vars \<Rightarrow>
    nat \<Rightarrow> (llist_polynomial \<times> nat) list \<Rightarrow> llist_polynomial \<Rightarrow>
    (string code_status \<times> sllist_polynomial) nres\<close>

sepref_def check_extension_l_impl
  is \<open>uncurry5 check_extension_l2_s\<close>
    :: \<open>poly_s_assn\<^sup>k *\<^sub>a polys_s_assn\<^sup>k *\<^sub>a shared_vars_assn\<^sup>d *\<^sub>a si64_assn\<^sup>k *\<^sub>a
    strl_assn'\<^sup>k *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a status_assn \<times>\<^sub>a poly_s_assn \<times>\<^sub>a shared_vars_assn \<times>\<^sub>a si64_assn
  \<close>
  supply [[goals_limit=1]]
  unfolding check_extension_l2_s_alt_def
    in_dom_by_contains
    ls_emp ls_emp'
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref


sepref_def check_del_l_impl
  is \<open>uncurry2 check_del_l\<close>
  :: \<open>poly_s_assn\<^sup>k *\<^sub>a polys_s_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k \<rightarrow>\<^sub>a status_assn\<close>
  unfolding check_del_l_def
  by sepref

lemmas [sepref_fr_rules] =
  check_extension_l_impl.refine
  check_linear_combi_l_s_impl.refine
  check_del_l_impl.refine


text \<open>The step function follows \<open>PAC_checker_l_step_alt\<close> from
  \<open>LPAC_Checker_Synthesis\<close>: the \<open>pac_step\<close> datatype is destructed via the
  tagged-tuple destructors of \<open>LPAC_Step_Assn\<close>, values stored in the map are
  \<open>BOX\<close>ed, and the id bound is threaded through as an \<open>fref\<close> precondition.\<close>

lemma is_Mult_lastI:
  \<open>\<not> is_CL b \<Longrightarrow> \<not>is_Extension b \<Longrightarrow> is_Del b\<close>
  by (cases b) auto

definition step_id_bounded :: \<open>lpac_step_hol \<Rightarrow> bool\<close> where
  \<open>step_id_bounded st \<longleftrightarrow> (\<not>is_Del st \<longrightarrow> new_id st + 1 < max_snat 64)\<close>

definition PAC_checker_l_step_s_alt where
  \<open>PAC_checker_l_step_s_alt spec st' \<V> A st = (
    if is_CL st then doN {
      (srcs, ni, res) \<leftarrow> mop_dest_cl st;
      ASSERT (ni + 1 < max_snat 64);
      r \<leftarrow> full_normalize_poly res;
      (eq, r) \<leftarrow> check_linear_combi_l_s spec A \<V> ni srcs r;
      if \<not>is_cfailed eq then doN {
        let st'' = merge_cstatus st' eq;
        let A' = fmupd ni (BOX r) A;
        RETURN (st'', \<V>, A')
      }
      else RETURN (eq, \<V>, A)
    }
    else if is_Del st then doN {
      s1 \<leftarrow> mop_dest_ldel st;
      eq \<leftarrow> check_del_l spec A s1;
      if \<not>is_cfailed eq then doN {
        let st'' = merge_cstatus st' eq;
        let A' = fmdrop s1 A;
        RETURN (st'', \<V>, A')
      }
      else RETURN (eq, \<V>, A)
    }
    else doN {
      (ni, v, res) \<leftarrow> mop_dest_lextension st;
      ASSERT (ni + 1 < max_snat 64);
      r \<leftarrow> full_normalize_poly res;
      (eq, r, \<V>, v') \<leftarrow> check_extension_l2_s spec A \<V> ni v r;
      if \<not>is_cfailed eq then doN {
        r \<leftarrow> add_poly_l_s \<V> ([([v'], -1)], r);
        let A' = fmupd ni (BOX r) A;
        RETURN (st', \<V>, A')
      }
      else RETURN (eq, \<V>, A)
    })\<close>

definition PAC_checker_l_step_s' where
  \<open>PAC_checker_l_step_s' a b c d = PAC_checker_l_step_s a (b, c, d)\<close>

lemma PAC_checker_l_step_s_alt_PAC_checker_l_step_s':
  \<open>step_id_bounded st \<Longrightarrow>
     PAC_checker_l_step_s_alt spec st' \<V> A st \<le> \<Down>Id (PAC_checker_l_step_s' spec st' \<V> A st)\<close>
  unfolding PAC_checker_l_step_s_alt_def PAC_checker_l_step_s'_def PAC_checker_l_step_s_def
    mop_dest_cl_def mop_dest_lextension_def mop_dest_ldel_def
    step_id_bounded_def BOX_def COPY_def
  apply (cases st)
  apply (auto simp: dest_cl_def dest_lextension_def dest_ldel_def Let_def
    pw_le_iff refine_pw_simps)
  done

lemma PAC_checker_l_step_s_fref:
  \<open>(uncurry4 PAC_checker_l_step_s_alt, uncurry4 PAC_checker_l_step_s')
    \<in> [\<lambda>((((_, _), _), _), st). step_id_bounded st]\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  using PAC_checker_l_step_s_alt_PAC_checker_l_step_s' by auto

lemma PAC_checker_l_step_s_tuple:
  \<open>PAC_checker_l_step_s a bcd e = (let (b, c, d) = bcd in PAC_checker_l_step_s' a b c d e)\<close>
  unfolding PAC_checker_l_step_s'_def by (auto split: prod.splits)

sepref_definition check_step_s_impl
  is \<open>uncurry4 PAC_checker_l_step_s_alt\<close>
  :: \<open>poly_s_assn\<^sup>k *\<^sub>a status_assn\<^sup>d *\<^sub>a shared_vars_assn\<^sup>d *\<^sub>a polys_s_assn\<^sup>d *\<^sub>a lpac_step_assn\<^sup>d \<rightarrow>\<^sub>a
    status_assn \<times>\<^sub>a shared_vars_assn \<times>\<^sub>a polys_s_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro]
  unfolding PAC_checker_l_step_s_alt_def Let_def
    is_success_alt_def[symmetric]
    ls_emp ls_emp'
  by sepref

lemmas PAC_checker_l_step_s'_hnr[sepref_fr_rules] =
  check_step_s_impl.refine[FCOMP PAC_checker_l_step_s_fref]

sepref_register PAC_checker_l_step_s' ::
  \<open>sllist_polynomial \<Rightarrow> string code_status \<Rightarrow> (nat, string) shared_vars \<Rightarrow>
    (nat, sllist_polynomial) f_map \<Rightarrow> lpac_step_hol \<Rightarrow>
    (string code_status \<times> (nat, string) shared_vars \<times> (nat, sllist_polynomial) f_map) nres\<close>

fun vars_llist_s2 :: \<open>_ \<Rightarrow> _ list\<close> where
  \<open>vars_llist_s2 [] = []\<close> |
  \<open>vars_llist_s2 ((a,_) # xs) = a @ vars_llist_s2 xs\<close>

text \<open>The checker loop pops the step list (mirroring \<open>PAC_checker_l_loop\<close> in
  \<open>LPAC_Checker_Synthesis\<close>); the id bound of every step is carried as an
  \<open>fref\<close> precondition.\<close>

definition PAC_checker_l_s' where
  \<open>PAC_checker_l_s' p \<V> A status steps = PAC_checker_l_s p (\<V>, A) status steps\<close>

lemma PAC_checker_l_s_alt_def:
  \<open>PAC_checker_l_s p \<V>A status steps =
    (let (\<V>, A) = \<V>A in PAC_checker_l_s' p \<V> A status steps)\<close>
  unfolding PAC_checker_l_s'_def by auto

definition PAC_checker_l_s_loop
  :: \<open>sllist_polynomial \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> string code_status \<Rightarrow> lpac_step_hol list \<Rightarrow> _\<close>
  where \<open>PAC_checker_l_s_loop spec \<V> A b st = do {
    (S, _) \<leftarrow> WHILE\<^sub>T
       (\<lambda>((b, _), n). \<not>is_cfailed b \<and> n \<noteq> [])
       (\<lambda>((bA), n). do {
          ASSERT(n \<noteq> []);
          (nh, nt) \<leftarrow> mop_list_pop_hd n;
          ASSERT(step_id_bounded nh);
          S \<leftarrow> PAC_checker_l_step_s spec bA nh;
          RETURN (S, nt)
        })
      ((b, (\<V>, A)), st);
    RETURN S
  }\<close>

lemma PAC_checker_l_step_s_rel_id:
  \<open>(bA, bA') \<in> Id \<Longrightarrow> (st, st') \<in> Id \<Longrightarrow>
     PAC_checker_l_step_s spec bA st \<le> \<Down>Id (PAC_checker_l_step_s spec bA' st')\<close>
  by auto

lemma PAC_checker_l_s_loop_PAC_checker_l_s':
  assumes \<open>list_all step_id_bounded st\<close>
  shows \<open>PAC_checker_l_s_loop spec \<V> A b st \<le> \<Down>Id (PAC_checker_l_s' spec \<V> A b st)\<close>
  unfolding PAC_checker_l_s_loop_def PAC_checker_l_s'_def PAC_checker_l_s_def
    mop_list_pop_hd_def
  apply (simp add: ASSERT_dup)
  apply (rule refine_IdD)
  apply (refine_rcg
      WHILET_refine[where R = \<open>Id \<times>\<^sub>r {(n, n'). n' = n \<and> list_all step_id_bounded n}\<close>]
      PAC_checker_l_step_s_rel_id)
  using assms by (auto simp: neq_Nil_conv)

lemma PAC_checker_l_s_loop_fref:
  \<open>(uncurry4 PAC_checker_l_s_loop, uncurry4 PAC_checker_l_s')
    \<in> [\<lambda>((((_, _), _), _), st). list_all step_id_bounded st]\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  using PAC_checker_l_s_loop_PAC_checker_l_s' by auto

sepref_definition PAC_checker_l_s_impl
  is \<open>uncurry4 PAC_checker_l_s_loop\<close>
  :: \<open>poly_s_assn\<^sup>k *\<^sub>a shared_vars_assn\<^sup>d *\<^sub>a polys_s_assn\<^sup>d *\<^sub>a status_assn\<^sup>d *\<^sub>a
     (cl_assn' lpac_step_assn)\<^sup>d \<rightarrow>\<^sub>a
     status_assn \<times>\<^sub>a shared_vars_assn \<times>\<^sub>a polys_s_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro]
  unfolding PAC_checker_l_s_loop_def is_success_alt_def[symmetric]
    PAC_checker_l_step_s_tuple
    nres_bind_let_law[symmetric]
    ls_emp
  apply (subst nres_bind_let_law)
  by sepref

lemmas PAC_checker_l_s'_hnr[sepref_fr_rules] =
  PAC_checker_l_s_impl.refine[FCOMP PAC_checker_l_s_loop_fref]

sepref_register PAC_checker_l_s' ::
  \<open>sllist_polynomial \<Rightarrow> (nat, string) shared_vars \<Rightarrow> (nat, sllist_polynomial) f_map \<Rightarrow>
    string code_status \<Rightarrow> lpac_step_hol list \<Rightarrow>
    (string code_status \<times> (nat, string) shared_vars \<times> (nat, sllist_polynomial) f_map) nres\<close>

text \<open>Importing all variables of a polynomial, monomial by monomial (the flat
  list \<open>vars_llist_s2 spec0\<close> of the previous formulation has no owning-list
  producer). Defined before the remap definition that uses it.\<close>

definition import_poly_varsS
  :: \<open>(nat, string) shared_vars \<Rightarrow> llist_polynomial \<Rightarrow> (memory_allocation \<times> (nat, string) shared_vars) nres\<close>
where
  \<open>import_poly_varsS \<V> p = do {
     p \<leftarrow> RETURN (COPY p);
     (mem, \<V>, _) \<leftarrow> WHILE\<^sub>T (\<lambda>(mem, \<V>, p). \<not>alloc_failed mem \<and> p \<noteq> [])
       (\<lambda>(_, \<V>, p). do {
          ((m, c), p) \<leftarrow> mop_list_pop_hd p;
          (mem, \<V>) \<leftarrow> import_variablesS m \<V>;
          RETURN (mem, \<V>, p)
       }) (Allocated, \<V>, p);
     RETURN (mem, \<V>)
  }\<close>

definition (in -) remap_polys_l2_with_err_s :: \<open>llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> (nat, llist_polynomial) fmap \<Rightarrow> (nat, string) shared_vars \<Rightarrow>
   (string code_status \<times> (nat, string) shared_vars \<times> (nat, sllist_polynomial) fmap \<times> sllist_polynomial) nres\<close> where
  \<open>remap_polys_l2_with_err_s spec spec0 A (\<V> :: (nat, string) shared_vars) =  do{
   ASSERT(vars_llist spec \<subseteq> vars_llist spec0);
    n \<leftarrow> upper_bound_on_dom A;
   (mem, \<V>) \<leftarrow> import_poly_varsS \<V> spec0;
   (mem', spec, \<V>) \<leftarrow> if \<not>alloc_failed mem then import_polyS \<V> spec else RETURN (mem, [], \<V>);
   failed \<leftarrow> RETURN (alloc_failed mem \<or> alloc_failed mem' \<or> n \<ge> max_snat 64 - 1);
   if failed
   then do {
     c \<leftarrow> remap_polys_l_dom_err;
     RETURN (error_msg (0::nat) c, \<V>, fmempty, [])
   }
   else do {
     (err, A, \<V>) \<leftarrow>  nfoldli ([0..<n]) (\<lambda>(err, A', \<V>). \<not>is_cfailed err)
       (\<lambda>i (err, A'  :: (nat, sllist_polynomial) fmap, \<V> :: (nat,string) shared_vars).
          if i \<in># dom_m A
          then  do {
           (err', p, \<V>  :: (nat,string) shared_vars) \<leftarrow> import_polyS (\<V> :: (nat,string) shared_vars) (the (fmlookup A i));
            if alloc_failed err' then RETURN((CFAILED ''memory out'',  A', \<V>  :: (nat,string) shared_vars))
            else do {
              p \<leftarrow> full_normalize_poly_s \<V> p;
              eq  \<leftarrow> weak_equality_l_s p spec;
              RETURN((if eq then CFOUND else CSUCCESS),  fmupd i p A', \<V>  :: (nat,string) shared_vars)
            }
          } else RETURN (err, A', \<V>  :: (nat,string) shared_vars))
       (CSUCCESS, fmempty :: (nat, sllist_polynomial) fmap,  \<V> :: (nat,string) shared_vars);
     RETURN (err, \<V>, A, spec)
  }}\<close>

lemma set_vars_llist_s2 [simp]: \<open>set (vars_llist_s2 b) = vars_llist b\<close>
  by (induction b)
    (auto simp: vars_llist_def)

sepref_register import_variablesS import_poly_varsS memory_out_msg

text \<open>The variable-import walks pop from a \<open>COPY\<close> (both branches of the abstract
  body drop the head, so no re-prepending is needed).\<close>

lemma import_variablesS_alt_def:
  \<open>(import_variablesS :: string list \<Rightarrow> (nat, string) shared_vars \<Rightarrow> _) vs0 \<V> = do {
     vs \<leftarrow> RETURN (COPY vs0);
     (mem, \<V>, _) \<leftarrow> WHILE\<^sub>T (\<lambda>(mem, \<V>, vs). \<not>alloc_failed mem \<and> vs \<noteq> [])
       (\<lambda>(_, \<V>, vs). do {
          (v, vs) \<leftarrow> mop_list_pop_hd vs;
          a \<leftarrow> is_new_variableS v \<V>;
          if \<not>a then RETURN (Allocated, \<V>, vs)
          else do {
            (mem, \<V>, _) \<leftarrow> import_variableS v \<V>;
            RETURN (mem, \<V>, vs)
          }
       }) (Allocated, \<V>, vs);
     RETURN (mem, \<V>)
  }\<close>
proof -
  have body_eq: \<open>(\<lambda>(_, \<V>, vs). do {
    ASSERT(vs \<noteq> []);
    let v = hd vs;
    a \<leftarrow> is_new_variableS v \<V>;
    if \<not>a then RETURN (Allocated ,\<V>, tl vs)
    else do {
      (mem, \<V>, _) \<leftarrow> import_variableS v \<V>;
      RETURN(mem, \<V>, tl vs)
    }
    }) = (\<lambda>(_, \<V>, vs). do {
          (v, vs) \<leftarrow> mop_list_pop_hd vs;
          a \<leftarrow> is_new_variableS v \<V>;
          if \<not>a then RETURN (Allocated, \<V>, vs)
          else do {
            (mem, \<V>, _) \<leftarrow> import_variableS v \<V>;
            RETURN (mem, \<V>, vs)
          }
       })\<close> for \<V> :: \<open>(nat, string) shared_vars\<close>
    by (intro ext)
     (auto simp: mop_list_pop_hd_def Let_def pw_eq_iff refine_pw_simps
        split: prod.splits)
  show ?thesis
    unfolding import_variablesS_def COPY_def nres_monad1 body_eq ..
qed

sepref_def import_variablesS_impl
  is \<open>uncurry (import_variablesS :: string list \<Rightarrow> (nat, string) shared_vars \<Rightarrow> _)\<close>
  :: \<open>monom_assn\<^sup>k *\<^sub>a shared_vars_assn\<^sup>d \<rightarrow>\<^sub>a memory_allocation_assn \<times>\<^sub>a shared_vars_assn\<close>
  supply [[goals_limit=1]]
  unfolding import_variablesS_alt_def
    ls_emp ls_emp'
  by sepref

lemmas [sepref_fr_rules] =
  import_variablesS_impl.refine full_normalize_poly'_impl.refine

sepref_def import_poly_varsS_impl
  is \<open>uncurry import_poly_varsS\<close>
  :: \<open>shared_vars_assn\<^sup>d *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a memory_allocation_assn \<times>\<^sub>a shared_vars_assn\<close>
  supply [[goals_limit=1]]
  unfolding import_poly_varsS_def
    ls_emp ls_emp'
  by sepref

lemmas [sepref_fr_rules] = import_poly_varsS_impl.refine

text \<open>The synthesized form of the remap loop \<open>BOX\<close>es the polynomials stored in
  the map and carries the update-bound assertion, mirroring
  \<open>remap_polys_l2_alt\<close> in \<open>PAC_Checker_Synthesis\<close>.\<close>

lemma remap_polys_l2_with_err_s_alt:
  \<open>remap_polys_l2_with_err_s spec spec0 A \<V> =  do{
   ASSERT(vars_llist spec \<subseteq> vars_llist spec0);
    n \<leftarrow> upper_bound_on_dom A;
   (mem, \<V>) \<leftarrow> import_poly_varsS \<V> spec0;
   (mem', spec, \<V>) \<leftarrow> if \<not>alloc_failed mem then import_polyS \<V> spec else RETURN (mem, [], \<V>);
   failed \<leftarrow> RETURN (alloc_failed mem \<or> alloc_failed mem' \<or> n \<ge> max_snat 64 - 1);
   if failed
   then do {
     c \<leftarrow> remap_polys_l_dom_err;
     RETURN (error_msg (0::nat) c, \<V>, fmempty, [])
   }
   else do {
     (err, A, \<V>) \<leftarrow>  nfoldli ([0..<n]) (\<lambda>(err, A', \<V>). \<not>is_cfailed err)
       (\<lambda>i (err, A', \<V>).
          if i \<in># dom_m A
          then  do {
           (err', p, \<V>) \<leftarrow> import_polyS \<V> (the (fmlookup A i));
            if alloc_failed err' then RETURN((CFAILED ''memory out'',  A', \<V>))
            else do {
              p \<leftarrow> full_normalize_poly_s \<V> p;
              eq  \<leftarrow> weak_equality_l_s p spec;
              ASSERT(i + 1 < max_snat 64);
              RETURN((if eq then CFOUND else CSUCCESS),  fmupd i (BOX p) A', \<V>)
            }
          } else RETURN (err, A', \<V>))
       (CSUCCESS, fmempty,  \<V>);
     RETURN (err, \<V>, A, spec)
  }}\<close>
  unfolding remap_polys_l2_with_err_s_def case_prod_beta
  apply (simp only: nres_monad1)
  apply (rule bind_cong[OF refl])
  apply (rule bind_cong[OF refl])
  apply (rule bind_cong[OF refl])
  apply (rule bind_cong[OF refl])
  apply (rule if_cong[OF refl refl])
  apply (rule bind_cong[OF _ refl])
  apply (rule nfoldli_body_cong)
  apply (auto simp: BOX_def not_le ASSERT_insert_bound split: prod.splits
      intro!: bind_cong[OF refl])
  done

sepref_def remap_polys_l2_with_err_s_impl
  is \<open>uncurry3 remap_polys_l2_with_err_s\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k *\<^sub>a polys_assn_input\<^sup>k *\<^sub>a shared_vars_assn\<^sup>d \<rightarrow>\<^sub>a
  status_assn \<times>\<^sub>a shared_vars_assn \<times>\<^sub>a polys_s_assn \<times>\<^sub>a poly_s_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro] indom_mI[dest]
  unfolding remap_polys_l2_with_err_s_alt
    op_fmap_empty_def[symmetric] while_eq_nfoldli[symmetric]
    while_upt_while_direct max_snat_val
    in_dom_by_contains
    fmlookup'_def[symmetric]
    ls_emp ls_emp'
  apply (subst while_upt_while_direct)
  apply simp
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemmas [sepref_fr_rules] =
  remap_polys_l2_with_err_s_impl.refine

text \<open>Like \<open>full_checker_l2\<close> in \<open>LPAC_Checker_Synthesis\<close>: the id bound of all
  steps is asserted up front (threaded into the step loop's precondition), and
  the specification polynomial is copied before normalization since the
  original is also handed to the remap.\<close>

definition full_checker_l_s2
  :: \<open>llist_polynomial \<Rightarrow> (nat, llist_polynomial) fmap \<Rightarrow> (llist_polynomial, string, nat) pac_step list \<Rightarrow>
    (string code_status \<times> _) nres\<close>
where
  \<open>full_checker_l_s2 spec A st = do {
    ASSERT (list_all step_id_bounded st);
    spec' \<leftarrow> full_normalize_poly (COPY spec);
    (b, \<V>, A, spec') \<leftarrow> remap_polys_l2_with_err_s spec' spec A ({#}, fmempty, fmempty);
    if is_cfailed b
    then RETURN (b, \<V>, A)
    else do {
      PAC_checker_l_s spec' (\<V>, A) b st
     }
   }\<close>

sepref_register remap_polys_l2_with_err_s ::
  \<open>llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> (nat, llist_polynomial) f_map \<Rightarrow>
    (nat, string) shared_vars \<Rightarrow>
    (string code_status \<times> (nat, string) shared_vars \<times> (nat, sllist_polynomial) f_map \<times>
     sllist_polynomial) nres\<close>

sepref_register full_checker_l_s2 ::
  \<open>llist_polynomial \<Rightarrow> (nat, llist_polynomial) f_map \<Rightarrow> lpac_step_hol list \<Rightarrow>
    (string code_status \<times> (nat, string) shared_vars \<times> (nat, sllist_polynomial) f_map) nres\<close>

sepref_def full_checker_l_s2_impl
  is \<open>uncurry2 full_checker_l_s2\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a polys_assn_input\<^sup>k *\<^sub>a (cl_assn' lpac_step_assn)\<^sup>d \<rightarrow>\<^sub>a
  status_assn \<times>\<^sub>a shared_vars_assn \<times>\<^sub>a polys_s_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro]
  unfolding full_checker_l_s2_def
    PAC_checker_l_s_alt_def
    empty_shared_vars_def[symmetric]
  by sepref

section \<open>Correctness theorem\<close>

context poly_embed
begin

definition fully_epac_assn where
  \<open>fully_epac_assn = hr_comp (cl_assn' lpac_step_assn)
     (\<langle>p2rel
        (\<langle>nat_rel,
         fully_unsorted_poly_rel O
         mset_poly_rel, var_rel\<rangle>pac_step_rel_raw)\<rangle>list_rel)\<close>


text \<open>

Below is the full correctness theorems. It basically states that:

  \<^enum> assuming that the input polynomials have no duplicate variables


Then:

\<^enum> if the checker returns \<^term>\<open>CFOUND\<close>, the spec is in the ideal
  and the PAC file is correct

\<^enum> if the checker returns \<^term>\<open>CSUCCESS\<close>, the PAC file is correct (but
there is no information on the spec, aka checking failed)

\<^enum> if the checker return \<^term>\<open>CFAILED err\<close>, then checking failed (and
\<^term>\<open>err\<close> \<^emph>\<open>might\<close> give you an indication of the error, but the correctness
theorem does not say anything about that).


The input parameters are:

\<^enum> the specification polynomial represented as a list

\<^enum> the input polynomials as hash map (as an array of option polynomial)

\<^enum> a represention of the PAC proofs.

  \<close>

subsection \<open>Relating the nested and the flat variable import\<close>

lemma import_variablesS_Nil:
  \<open>import_variablesS [] (\<V> :: (nat, string) shared_vars) = RETURN (Allocated, \<V>)\<close>
  unfolding import_variablesS_def
  by (subst WHILET_unfold) auto
(*
lemma import_variablesS_Cons:
  \<open>import_variablesS (v # vs) (\<V> :: (nat, string) shared_vars) = do {
     a \<leftarrow> is_new_variableS v \<V>;
     if \<not>a then import_variablesS vs \<V>
     else do {
       (mem, \<V>', _) \<leftarrow> import_variableS v \<V>;
       if alloc_failed mem then RETURN (mem, \<V>')
       else import_variablesS vs \<V>'
     }
  }\<close>
proof -
  have exit: \<open>WHILE\<^sub>T (\<lambda>(mem, \<V>, vs). \<not>alloc_failed mem \<and> vs \<noteq> []) b (Mem_Out, \<V>0, vs0)
      = RETURN (Mem_Out, \<V>0, vs0)\<close>
    for b :: \<open>memory_allocation \<times> (nat, string) shared_vars \<times> string list \<Rightarrow> _\<close> and \<V>0 vs0
    by (subst WHILET_unfold) auto
  show ?thesis
    apply (subst import_variablesS_def)
    apply (subst WHILET_unfold)
    unfolding import_variablesS_def
    by (auto simp: is_new_variableS_def exit Let_def pw_eq_iff refine_pw_simps
      split: prod.splits memory_allocation.splits intro!: bind_cong[OF refl])
qed

lemma import_variablesS_append:
  \<open>import_variablesS (xs @ ys) (\<V> :: (nat, string) shared_vars) = do {
     (mem, \<V>) \<leftarrow> import_variablesS xs \<V>;
     if alloc_failed mem then RETURN (mem, \<V>) else import_variablesS ys \<V>
  }\<close>
  apply (induction xs arbitrary: \<V>)
  subgoal by (auto simp: import_variablesS_Nil)
  subgoal for v xs \<V>
    by (auto simp: import_variablesS_Cons pw_eq_iff refine_pw_simps
        split: memory_allocation.splits intro!: bind_cong[OF refl])
  done

lemma import_poly_varsS_Nil:
  \<open>import_poly_varsS \<V> [] = RETURN (Allocated, \<V>)\<close>
  unfolding import_poly_varsS_def COPY_def nres_monad1
  by (subst WHILET_unfold) auto
*)
(*
lemma import_poly_varsS_Cons:
  \<open>import_poly_varsS \<V> ((m, c) # p) = do {
     (mem, \<V>) \<leftarrow> import_variablesS m \<V>;
     if alloc_failed mem then RETURN (mem, \<V>) else import_poly_varsS \<V> p
  }\<close>
proof -
  have exit: \<open>WHILE\<^sub>T (\<lambda>(mem, \<V>, p). \<not>alloc_failed mem \<and> p \<noteq> []) b (Mem_Out, \<V>0, p0)
      = RETURN (Mem_Out, \<V>0, p0)\<close>
    for b :: \<open>memory_allocation \<times> (nat, string) shared_vars \<times> llist_polynomial \<Rightarrow> _\<close> and \<V>0 p0
    by (subst WHILET_unfold) auto
  show ?thesis
    apply (subst import_poly_varsS_def)
    apply (simp only: COPY_def id_apply nres_monad1)
    apply (subst WHILET_unfold)
    unfolding import_poly_varsS_def COPY_def nres_monad1
    by (auto simp: mop_list_pop_hd_def exit Let_def pw_eq_iff refine_pw_simps
      split: prod.splits memory_allocation.splits intro!: bind_cong[OF refl])
qed

lemma import_poly_varsS_import_variablesS:
  \<open>import_poly_varsS \<V> p = import_variablesS (vars_llist_s2 p) \<V>\<close>
  apply (induction p arbitrary: \<V>)
  subgoal by (simp add: import_poly_varsS_Nil import_variablesS_Nil)
  subgoal for x p \<V>
    by (cases x)
      (auto simp: import_poly_varsS_Cons import_variablesS_append pw_eq_iff refine_pw_simps
        intro!: bind_cong[OF refl])
  done

lemma remap_polys_l2_with_err_s_remap_polys_s_with_err:
  assumes \<open>((spec, a, b, c), (spec', a', c', b')) \<in> Id\<close>
  shows \<open>remap_polys_l2_with_err_s spec a b c
    \<le> \<Down> Id
  (remap_polys_s_with_err spec' a' b' c')\<close>
proof -
  have [refine]: \<open>(A, A') \<in> Id \<Longrightarrow> upper_bound_on_dom A
    \<le> \<Down> {(n, dom). dom = set [0..<n]} (SPEC (\<lambda>dom. set_mset (dom_m A') \<subseteq> dom \<and> finite dom))\<close> for A A'
    unfolding upper_bound_on_dom_def
    apply (rule RES_refine)
    apply (auto simp: upper_bound_on_dom_def)
    done
  have 3: \<open>(n, dom) \<in> {(n, dom). dom = set [0..<n]} \<Longrightarrow>
    ([0..<n], dom) \<in> \<langle>nat_rel\<rangle>list_set_rel\<close> for n dom
    by (auto simp: list_set_rel_def br_def)
  have 4: \<open>(p,q) \<in> Id \<Longrightarrow>
    weak_equality_l p spec \<le> \<Down>Id (weak_equality_l q spec)\<close> for p q spec
    by auto

  have 6: \<open>a = b \<Longrightarrow> (a, b) \<in> Id\<close> for a b
    by auto

  have id: \<open>f=g \<Longrightarrow> f \<le>\<Down>Id g\<close> for f g
    by auto
  have [simp]: \<open>vars_llist_s2 x = vars_llist_l x\<close> for x
    by (induction x rule: vars_llist_s2.induct) auto
  have [simp]: \<open>import_poly_varsS \<V> p = import_variablesS (vars_llist_l p) \<V>\<close>
    for \<V> :: \<open>(nat, string) shared_vars\<close> and p
    by (simp add: import_poly_varsS_import_variablesS)
  show ?thesis
    supply [[goals_limit=1]]
    unfolding remap_polys_l2_with_err_s_def remap_polys_s_with_err_def
    apply (refine_rcg
      LFOc_refine[where R= \<open>{((a,b,c), (a',b',c')). ((a,b,c), (a',c',b'))\<in>Id}\<close>])
    subgoal using assms by auto
    subgoal using assms by auto
    apply (rule id)
    subgoal using assms by auto
    subgoal using assms by auto
    apply (rule id)
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule 3)
    subgoal by auto
    subgoal by auto
    subgoal using assms by auto
    apply (rule id)
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    apply (rule id)
    subgoal by auto
    apply (rule id)
    subgoal unfolding weak_equality_l_s'_def by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

lemma full_checker_l_s2_full_checker_l_s:
  \<open>(uncurry2 full_checker_l_s2, uncurry2 full_checker_l_s)
    \<in> [\<lambda>((_, _), st). list_all step_id_bounded st]\<^sub>f (Id \<times>\<^sub>r Id) \<times>\<^sub>r Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
proof -
  have id: \<open>f=g \<Longrightarrow> f \<le>\<Down>Id g\<close> for f g
    by auto
  show ?thesis
    apply (intro frefI nres_relI)
    unfolding uncurry_def
    apply clarify
    unfolding full_checker_l_s2_def
      full_checker_l_s_def COPY_def id_apply
    apply (refine_rcg remap_polys_l2_with_err_s_remap_polys_s_with_err)
    subgoal by auto
    apply (rule id)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule id)
    subgoal by auto
    done
qed

lemma full_poly_input_assn_alt_def:
  \<open>full_poly_input_assn = (hr_comp
  (hr_comp (hr_comp polys_assn_input (\<langle>nat_rel, Id\<rangle>fmap_rel))
  (\<langle>nat_rel, fully_unsorted_poly_rel O mset_poly_rel\<rangle>fmap_rel))
  polys_rel)\<close>
proof -
  have [simp]: \<open>\<langle>nat_rel, Id\<rangle>fmap_rel = Id\<close>
    apply (auto simp: fmap_rel_def)
    by (metis (no_types, opaque_lifting) fmap_ext_fmdom fmlookup_dom_iff fset_eqI option.sel)
  show ?thesis
    unfolding full_poly_input_assn_def
    by auto
qed

lemma PAC_full_correctness: (* \htmllink{PAC-full-correctness} *)
  \<open>(uncurry2 full_checker_l_s2_impl,
 uncurry2 (\<lambda>spec A _. PAC_checker_specification spec A))
\<in> full_poly_assn\<^sup>k *\<^sub>a full_poly_input_assn\<^sup>k *\<^sub>a
  fully_epac_assn\<^sup>k \<rightarrow>\<^sub>a hr_comp (status_assn raw_string_assn \<times>\<^sub>a shared_vars_assn \<times>\<^sub>a polys_s_assn)
            {((err, _), err', _). (err, err') \<in> code_status_status_rel}\<close>
proof -
  have 1: \<open>(uncurry2 full_checker_l_s2, uncurry2 (\<lambda>spec A _. PAC_checker_specification spec A))
    \<in> (\<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r int_rel\<rangle>list_rel O fully_unsorted_poly_rel O mset_poly_rel \<times>\<^sub>r
    (\<langle>nat_rel, Id\<rangle>fmap_rel O \<langle>nat_rel, fully_unsorted_poly_rel O mset_poly_rel\<rangle>fmap_rel) O
    polys_rel) \<times>\<^sub>r
    \<langle>p2rel
    (\<langle>nat_rel, fully_unsorted_poly_rel O mset_poly_rel,
    var_rel\<rangle>LPAC_Checker.pac_step_rel_raw)\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>(({((err, _), err', _).
    (err, err') \<in> Id} O
    {((b, A, st), b', A', st').
    (\<not> is_cfailed b \<longrightarrow> (A, A') \<in> {(x, y). y = set_mset x} \<and> (st, st') \<in> Id) \<and>
    (b, b') \<in> Id}) O
    {((err, \<V>, A), err', \<V>', A').
    ((err, \<V>, A), err', \<V>', A')
    \<in> code_status_status_rel \<times>\<^sub>r
    vars_rel2 err \<times>\<^sub>r
    {(xs, ys).
    \<not> is_cfailed err \<longrightarrow>
    (xs, ys) \<in> \<langle>nat_rel, sorted_poly_rel O mset_poly_rel\<rangle>fmap_rel \<and>
    (\<forall>i\<in>#dom_m xs. vars_llist (xs \<propto> i) \<subseteq> \<V>)}}) O
    {((st, G), st', G').
    (st, st') \<in> status_rel \<and> (st \<noteq> FAILED \<longrightarrow> (G, G') \<in> Id \<times>\<^sub>r polys_rel)}\<rangle>nres_rel\<close>
    using full_checker_l_s2_full_checker_l_s[
      FCOMP full_checker_l_s_full_checker_l_prep',
      FCOMP full_checker_l_prep_full_checker_l2',
      FCOMP full_checker_l_full_checker',
      FCOMP full_checker_spec',
      unfolded full_poly_assn_def[symmetric]
      full_poly_input_assn_def[symmetric]
      fully_epac_assn_def[symmetric]
      code_status_assn_def[symmetric]
      full_vars_assn_def[symmetric]
      polys_rel_full_polys_rel
      hr_comp_prod_conv
      full_polys_assn_def[symmetric]
      full_poly_input_assn_alt_def[symmetric]] by auto
  have 2: \<open>A \<subseteq> B \<Longrightarrow> \<langle>A\<rangle>nres_rel \<subseteq> \<langle>B\<rangle>nres_rel\<close> for A B
    by (auto simp: nres_rel_def conc_fun_R_mono conc_trans_additional(6))

  have 3: \<open>(uncurry2 full_checker_l_s2, uncurry2 (\<lambda>spec A _. PAC_checker_specification spec A))
    \<in> (\<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r int_rel\<rangle>list_rel O fully_unsorted_poly_rel O mset_poly_rel \<times>\<^sub>r
    (\<langle>nat_rel, Id\<rangle>fmap_rel O \<langle>nat_rel, fully_unsorted_poly_rel O mset_poly_rel\<rangle>fmap_rel) O
    polys_rel) \<times>\<^sub>r
    \<langle>p2rel
    (\<langle>nat_rel, fully_unsorted_poly_rel O mset_poly_rel,
    var_rel\<rangle>LPAC_Checker.pac_step_rel_raw)\<rangle>list_rel \<rightarrow>\<^sub>f
    \<langle>{((err, _), err', _). (err, err') \<in> code_status_status_rel}\<rangle>nres_rel\<close>
    apply (rule set_mp[OF _ 1])
    unfolding fref_param1[symmetric]
    apply (rule fun_rel_mono)
    apply auto[]
    apply (rule 2)
    apply auto
    done

  have 4: \<open>\<langle>nat_rel, Id\<rangle>fmap_rel = Id\<close>
    apply (auto simp: fmap_rel_def)
    by (metis (no_types, opaque_lifting) fmap_ext_fmdom fmlookup_dom_iff fset_eqI option.sel)
  have H: \<open>full_poly_assn = (hr_comp poly_assn
    (\<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r int_rel\<rangle>list_rel O fully_unsorted_poly_rel O mset_poly_rel))\<close>
    \<open>full_poly_input_assn = hr_comp polys_assn_input
   ((Id O \<langle>nat_rel, fully_unsorted_poly_rel O mset_poly_rel\<rangle>fmap_rel) O polys_rel)\<close>
    unfolding full_poly_assn_def fully_epac_assn_def full_poly_input_assn_def
      hr_comp_assoc O_assoc
    by auto
  show ?thesis
    using full_checker_l_s2_impl.refine[FCOMP 3]
    unfolding full_poly_assn_def[symmetric]
      full_poly_input_assn_def[symmetric]
      fully_epac_assn_def[symmetric]
      code_status_assn_def[symmetric]
      full_vars_assn_def[symmetric]
      polys_rel_full_polys_rel
      hr_comp_prod_conv
      full_polys_assn_def[symmetric]
      full_poly_input_assn_alt_def[symmetric]
      4 H[symmetric]
    by auto
qed

text \<open>

It would be more efficient to move the parsing to Isabelle, as this
would be more memory efficient (and also reduce the TCB). But now
comes the fun part: It cannot work. A stream (of a file) is consumed
by side effects. Assume that this would work. The code could look like:

\<^term>\<open>
  let next_token = read_file file
  in f (next_token)
\<close>

This code is equal to (in the HOL sense of equality):
\<^term>\<open>
  let _ = read_file file;
      next_token = read_file file
  in f (next_token)
\<close>

However, as an hypothetical \<^term>\<open>read_file\<close> changes the underlying stream, we would get the next
token. Remark that this is already a weird point of ML compilers. Anyway, I see currently two
solutions to this problem:

\<^enum> The meta-argument: use it only in the Refinement Framework in a setup where copies are
disallowed. Basically, this works because we can express the non-duplication constraints on the type
level. However, we cannot forbid people from expressing things directly at the HOL level.

\<^enum> On the target language side, model the stream as the stream and the position. Reading takes two
arguments. First, the position to read. Second, the stream (and the current position) to read. If
the position to read does not match the current position, return an error. This would fit the
correctness theorem of the code generation (roughly ``if it terminates without exception, the answer
is the same''), but it is still unsatisfactory.
\<close>

*)

end
end
