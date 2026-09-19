theory LPAC_Efficient_Checker_Refinement
  imports
    LPAC_Efficient_Checker
    LPAC_Efficient_Checker_Sorting
    Interleaving_Fold
    PAC_Checker_Synthesis
begin

text \<open>Abstract refinement layer of the efficient (perfectly-shared) LPAC checker:
  the \<open>nres\<close>-level programs and their refinement proofs. No LLVM/sepref
  material lives here.\<close>

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

definition perfect_shared_term_order_rel_dir
  :: \<open>nat \<Rightarrow> nat \<Rightarrow> (nat, string) shared_vars \<Rightarrow> direction nres\<close>
where
  \<open>perfect_shared_term_order_rel_dir x y \<V> \<equiv> doN {
    eq \<leftarrow> perfect_shared_var_order_s \<V> x y;
    if eq = EQUAL then RETURN BOTH else RETURN STOP
  }\<close>

definition perfect_shared_term_order_rel_f
  :: \<open>ordered \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat, string) shared_vars \<Rightarrow> direction \<Rightarrow> ordered nres\<close>
where
  \<open>perfect_shared_term_order_rel_f b x y \<V> dir \<equiv>
    if dir = STOP then perfect_shared_var_order_s \<V> x y else RETURN b\<close>

lemma perfect_shared_var_order_s_det:
  \<open>perfect_shared_var_order_s \<V> x y = FAIL \<or>
    (\<exists>v. v \<noteq> UNKNOWN \<and> perfect_shared_var_order_s \<V> x y = RETURN v)\<close>
  unfolding perfect_shared_var_order_s_def perfectly_shared_strings_equal_l_def
    get_var_nameS_def
  by (auto simp: bind_ASSERT_eq_if)

lemma foldl_nres_const:
  \<open>foldl_nres (\<lambda>_ _. RETURN c) acc xs = RETURN (if xs = [] then acc else c)\<close>
  by (induction xs arbitrary: acc) (auto simp: foldl_nres_Cons)

lemma perfect_shared_term_order_rel_s_alt_def:
  \<open>perfect_shared_term_order_rel_s \<V> xs ys =
    ifoldl_ext_nres perfect_shared_term_order_rel_f perfect_shared_term_order_rel_dir
      (\<lambda>_ _. RETURN GREATER) (\<lambda>_ _. RETURN LESS) EQUAL xs ys \<V>\<close>
proof (induction xs arbitrary: ys)
  case Nil
  show ?case
    unfolding perfect_shared_term_order_rel_s_def ifoldl_ext_nres_Nil1 foldl_nres_const
    by (cases ys) (subst WHILET_unfold; simp; subst WHILET_unfold; simp)+
next
  case (Cons x xs)
  note IH = Cons.IH[unfolded perfect_shared_term_order_rel_s_def]
  show ?case
  proof (cases ys)
    case Nil
    show ?thesis
      unfolding Nil perfect_shared_term_order_rel_s_def ifoldl_ext_nres_Nil2 foldl_nres_const
      by (subst WHILET_unfold; simp; subst WHILET_unfold; simp)
  next
    case (Cons y ys')
    show ?thesis
      using perfect_shared_var_order_s_det[of \<V> x y]
    proof (elim disjE exE conjE)
      assume F: \<open>perfect_shared_var_order_s \<V> x y = FAIL\<close>
      show ?thesis
        unfolding Cons perfect_shared_term_order_rel_s_def ifoldl_ext_nres_Cons
        by (subst WHILET_unfold) (simp add: F perfect_shared_term_order_rel_dir_def)
    next
      fix v
      assume v: \<open>v \<noteq> UNKNOWN\<close> and R: \<open>perfect_shared_var_order_s \<V> x y = RETURN v\<close>
      show ?thesis
        unfolding Cons perfect_shared_term_order_rel_s_def ifoldl_ext_nres_Cons
        apply (subst WHILET_unfold)
        apply (simp add: R perfect_shared_term_order_rel_dir_def
          perfect_shared_term_order_rel_f_def)
        apply (cases v)
        subgoal by (simp, subst WHILET_unfold, simp)
        subgoal using IH[of ys'] by simp
        subgoal by (simp, subst WHILET_unfold, simp)
        subgoal using v by simp
        done
    qed
  qed
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

type_synonym sllist_polynomial = \<open>(nat list \<times> int) list\<close>

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

definition \<open>add_poly_l_s_dir \<equiv> \<lambda>(xs, n) (ys, m) \<D>. doN{
    comp \<leftarrow> perfect_shared_term_order_rel_s \<D> xs ys; 
    if comp = EQUAL then
      RETURN BOTH
    else if comp = LESS then
      RETURN LEFT 
    else
      RETURN RIGHT
  }\<close>

text \<open>Note that copying is genuinely needed here, as we actually need
  to duplicate the respective monomials.\<close>

definition \<open>add_poly_l_s_f \<equiv> \<lambda>r (xs, n) (ys, m) \<D> dir. doN {
    if dir = BOTH then doN {
      let s = n + m;
      if s = 0 then
        RETURN r
      else
        RETURN (r@[(COPY xs, s)])    
    } else if dir = LEFT then
        RETURN (r@[(COPY xs, COPY n)])
    else
        RETURN (r@[(COPY ys, COPY m)])
  }\<close>

definition \<open>add_poly_l_s_cpy r x \<equiv> RETURN (r @ [COPY x])\<close>

lemma add_poly_l_s_simps:
  \<open>add_poly_l_s \<D> (p, []) = RETURN p\<close>
  \<open>add_poly_l_s \<D> ([], q) = RETURN q\<close>
  \<open>add_poly_l_s \<D> ((xs, n) # p, (ys, m) # q) = do {
    comp \<leftarrow> perfect_shared_term_order_rel_s \<D> xs ys;
    if comp = EQUAL then if n + m = 0 then add_poly_l_s \<D> (p, q)
    else do {
      pq \<leftarrow> add_poly_l_s \<D> (p, q);
      RETURN ((xs, n + m) # pq)
    }
    else if comp = LESS
    then do {
      pq \<leftarrow> add_poly_l_s \<D> (p, (ys, m) # q);
      RETURN ((xs, n) # pq)
    }
    else do {
      pq \<leftarrow> add_poly_l_s \<D> ((xs, n) # p, q);
      RETURN ((ys, m) # pq)
    }
  }\<close>
  subgoal
    by (subst add_poly_l_s_def, subst RECT_unfold, refine_mono) (cases p; simp)
  subgoal
    apply (subst add_poly_l_s_def, subst RECT_unfold, refine_mono)
    by (simp add: list.case_eq_if)
  subgoal
    apply (subst add_poly_l_s_def, subst RECT_unfold, refine_mono)
    apply (subst add_poly_l_s_def[symmetric])+
    by simp
  done

lemma foldl_nres_add_poly_l_s_cpy:
  \<open>foldl_nres add_poly_l_s_cpy acc xs = RETURN (acc @ xs)\<close>
  by (induction xs arbitrary: acc) (auto simp: foldl_nres_Cons add_poly_l_s_cpy_def)

lemma add_poly_l_s_ifoldl_acc:
  \<open>ifoldl_ext_nres add_poly_l_s_f add_poly_l_s_dir add_poly_l_s_cpy add_poly_l_s_cpy acc p q \<D>
    = do { r \<leftarrow> add_poly_l_s \<D> (p, q); RETURN (acc @ r) }\<close>
proof (induction \<open>length p + length q\<close> arbitrary: p q acc rule: less_induct)
  case less
  consider
      (N2) \<open>q = []\<close>
    | (N1) \<open>p = []\<close> \<open>q \<noteq> []\<close>
    | (C) xx p' yy q' where \<open>p = xx # p'\<close> \<open>q = yy # q'\<close>
    by (cases p; cases q) auto
  then show ?case
  proof cases
    case N2
    then show ?thesis
      by (simp add: ifoldl_ext_nres_Nil2 foldl_nres_add_poly_l_s_cpy add_poly_l_s_simps)
  next
    case N1
    then show ?thesis
      by (simp add: ifoldl_ext_nres_Nil1 foldl_nres_add_poly_l_s_cpy add_poly_l_s_simps)
  next
    case C
    obtain xs n where xx: \<open>xx = (xs, n)\<close> by (cases xx)
    obtain ys m where yy: \<open>yy = (ys, m)\<close> by (cases yy)
    have L1: \<open>length p' + length q' < length p + length q\<close>
      and L2: \<open>length p' + length ((ys, m) # q') < length p + length q\<close>
      and L3: \<open>length ((xs, n) # p') + length q' < length p + length q\<close>
      by (simp_all add: C)
    have IH1: \<open>ifoldl_ext_nres add_poly_l_s_f add_poly_l_s_dir add_poly_l_s_cpy add_poly_l_s_cpy
        acc' p' q' \<D> = do { r \<leftarrow> add_poly_l_s \<D> (p', q'); RETURN (acc' @ r) }\<close> for acc'
      using L1 less.hyps by auto
    have IH2: \<open>ifoldl_ext_nres add_poly_l_s_f add_poly_l_s_dir add_poly_l_s_cpy add_poly_l_s_cpy
        acc' p' ((ys, m) # q') \<D>
        = do { r \<leftarrow> add_poly_l_s \<D> (p', (ys, m) # q'); RETURN (acc' @ r) }\<close> for acc'
      using L2 less by presburger
    have IH3: \<open>ifoldl_ext_nres add_poly_l_s_f add_poly_l_s_dir add_poly_l_s_cpy add_poly_l_s_cpy
        acc' ((xs, n) # p') q' \<D>
        = do { r \<leftarrow> add_poly_l_s \<D> ((xs, n) # p', q'); RETURN (acc' @ r) }\<close> for acc'
      using L3 less by auto
    have dir_app: \<open>add_poly_l_s_dir (xs, n) (ys, m) \<D> = doN {
        comp \<leftarrow> perfect_shared_term_order_rel_s \<D> xs ys;
        if comp = EQUAL then RETURN BOTH
        else if comp = LESS then RETURN LEFT
        else RETURN RIGHT }\<close>
      by (simp add: add_poly_l_s_dir_def)
    have f_app: \<open>add_poly_l_s_f r (xs, n) (ys, m) \<D> dir =
        (if dir = BOTH then (if n + m = 0 then RETURN r else RETURN (r @ [(xs, n + m)]))
         else if dir = LEFT then RETURN (r @ [(xs, n)])
         else RETURN (r @ [(ys, m)]))\<close> for r dir
      by (simp add: add_poly_l_s_f_def Let_def)
    show ?thesis
      unfolding C xx yy ifoldl_ext_nres_Cons add_poly_l_s_simps(3) dir_app f_app
      apply (simp only: nres_monad_laws)
      apply (intro bind_cong[OF refl])
      subgoal for comp
        by (cases comp; simp_all add: IH1 IH2 IH3 nres_monad_laws Let_def)
      done
  qed
qed

definition add_poly_l_s_ifoldl
  :: \<open>sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow>
      (nat, string) shared_vars \<Rightarrow> sllist_polynomial nres\<close>
where
  \<open>add_poly_l_s_ifoldl \<equiv>
    ifoldl_ext_nres add_poly_l_s_f add_poly_l_s_dir add_poly_l_s_cpy add_poly_l_s_cpy\<close>

lemma add_poly_l_s_ifoldl_alt:
  \<open>add_poly_l_s \<D> = (\<lambda>(p, q). doN {
    rt \<leftarrow> add_poly_l_s_ifoldl op_clt_empty p q \<D>;
    RETURN (op_clt_to_cl rt)
  })\<close>
  unfolding add_poly_l_s_ifoldl_def
  by (auto simp: add_poly_l_s_ifoldl_acc nres_monad_laws split: prod.splits)

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

lemma mult_monoms_s_Nil2: \<open>mult_monoms_s \<V> xs [] = RETURN xs\<close>
  by (subst mult_monoms_s_simps) simp

lemma mult_monoms_s_Nil1: \<open>mult_monoms_s \<V> [] ys = RETURN ys\<close>
  by (subst mult_monoms_s_simps) simp

lemma mult_monoms_s_Cons:
  \<open>mult_monoms_s \<V> (x # xs) (y # ys) = do {
    comp \<leftarrow> perfect_shared_var_order_s \<V> x y;
    if comp = EQUAL then do {
      pq \<leftarrow> mult_monoms_s \<V> xs ys;
      RETURN (x # pq)
    }
    else if comp = LESS then do {
      pq \<leftarrow> mult_monoms_s \<V> xs (y # ys);
      RETURN (x # pq)
    }
    else do {
      pq \<leftarrow> mult_monoms_s \<V> (x # xs) ys;
      RETURN (y # pq)
    }
  }\<close>
  apply (subst mult_monoms_s_simps; simp)
  by (smt (verit, best) bind_cong list.sel(1,3))

definition \<open>mult_monoms_s_dir x y \<D> \<equiv> doN {
    comp \<leftarrow> perfect_shared_var_order_s \<D> x y;
    if comp = EQUAL then
      RETURN BOTH
    else if comp = LESS then
      RETURN LEFT
    else
      RETURN RIGHT
  }\<close>

definition \<open>mult_monoms_s_f \<equiv> \<lambda>r x y \<D> dir.
    if dir = RIGHT then RETURN (r @ [y]) else RETURN (r @ [x])\<close>

definition \<open>mult_monoms_s_cpy r x \<equiv> RETURN (r @ [x])\<close>

lemma foldl_nres_mult_monoms_s_cpy:
  \<open>foldl_nres mult_monoms_s_cpy acc xs = RETURN (acc @ xs)\<close>
  by (induction xs arbitrary: acc) (auto simp: foldl_nres_Cons mult_monoms_s_cpy_def)

lemma mult_monoms_s_ifoldl_acc:
  \<open>ifoldl_ext_nres mult_monoms_s_f mult_monoms_s_dir mult_monoms_s_cpy mult_monoms_s_cpy acc xs ys \<D>
    = do { r \<leftarrow> mult_monoms_s \<D> xs ys; RETURN (acc @ r) }\<close>
proof (induction \<open>length xs + length ys\<close> arbitrary: xs ys acc rule: less_induct)
  case less
  consider
      (N2) \<open>ys = []\<close>
    | (N1) \<open>xs = []\<close> \<open>ys \<noteq> []\<close>
    | (C) x xs' y ys' where \<open>xs = x # xs'\<close> \<open>ys = y # ys'\<close>
    by (cases xs; cases ys) auto
  then show ?case
  proof cases
    case N2
    then show ?thesis
      by (simp add: ifoldl_ext_nres_Nil2 foldl_nres_mult_monoms_s_cpy mult_monoms_s_Nil2)
  next
    case N1
    then show ?thesis
      by (simp add: ifoldl_ext_nres_Nil1 foldl_nres_mult_monoms_s_cpy mult_monoms_s_Nil1)
  next
    case C
    have L1: \<open>length xs' + length ys' < length xs + length ys\<close>
      and L2: \<open>length xs' + length (y # ys') < length xs + length ys\<close>
      and L3: \<open>length (x # xs') + length ys' < length xs + length ys\<close>
      by (simp_all add: C)
    have IH1: \<open>ifoldl_ext_nres mult_monoms_s_f mult_monoms_s_dir mult_monoms_s_cpy mult_monoms_s_cpy
        acc' xs' ys' \<D> = do { r \<leftarrow> mult_monoms_s \<D> xs' ys'; RETURN (acc' @ r) }\<close> for acc'
      using L1 less.hyps by auto
    have IH2: \<open>ifoldl_ext_nres mult_monoms_s_f mult_monoms_s_dir mult_monoms_s_cpy mult_monoms_s_cpy
        acc' xs' (y # ys') \<D>
        = do { r \<leftarrow> mult_monoms_s \<D> xs' (y # ys'); RETURN (acc' @ r) }\<close> for acc'
      using L2 less by presburger
    have IH3: \<open>ifoldl_ext_nres mult_monoms_s_f mult_monoms_s_dir mult_monoms_s_cpy mult_monoms_s_cpy
        acc' (x # xs') ys' \<D>
        = do { r \<leftarrow> mult_monoms_s \<D> (x # xs') ys'; RETURN (acc' @ r) }\<close> for acc'
      using L3 less by auto
    have dir_app: \<open>mult_monoms_s_dir x y \<D> = doN {
        comp \<leftarrow> perfect_shared_var_order_s \<D> x y;
        if comp = EQUAL then RETURN BOTH
        else if comp = LESS then RETURN LEFT
        else RETURN RIGHT }\<close>
      by (simp add: mult_monoms_s_dir_def)
    have f_app: \<open>mult_monoms_s_f r x y \<D> dir =
        (if dir = RIGHT then RETURN (r @ [y]) else RETURN (r @ [x]))\<close> for r dir
      by (simp add: mult_monoms_s_f_def)
    show ?thesis
      unfolding C ifoldl_ext_nres_Cons mult_monoms_s_Cons dir_app f_app
      apply (simp only: nres_monad_laws)
      apply (intro bind_cong[OF refl])
      subgoal for comp
        by (cases comp; simp_all add: IH1 IH2 IH3 nres_monad_laws)
      done
  qed
qed

definition mult_monoms_s_ifoldl
  :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> (nat, string) shared_vars \<Rightarrow> nat list nres\<close>
where
  \<open>mult_monoms_s_ifoldl \<equiv>
    ifoldl_ext_nres mult_monoms_s_f mult_monoms_s_dir mult_monoms_s_cpy mult_monoms_s_cpy\<close>

lemma mult_monoms_s_ifoldl_alt:
  \<open>mult_monoms_s \<D> xs ys = doN {
    rt \<leftarrow> mult_monoms_s_ifoldl op_clt_empty xs ys \<D>;
    RETURN (op_clt_to_cl rt)
  }\<close>
  unfolding mult_monoms_s_ifoldl_def
  by (simp add: mult_monoms_s_ifoldl_acc nres_monad_laws)

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


definition \<open>perfect_shared_var_order_s_else \<D> x y \<equiv> doN {
  x \<leftarrow> get_var_nameS \<D> x;
  y \<leftarrow> get_var_nameS \<D> y;
  if x < y then RETURN (LESS)
  else RETURN (GREATER) 
}\<close>

subsubsection \<open>The comparison itself\<close>

definition perfect_shared_var_order_c_else ::
  \<open>(string, nat) shared_vars_c \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ordered nres\<close> where
  \<open>perfect_shared_var_order_c_else \<D> x y = doN {
    x \<leftarrow> get_var_name_c \<D> x;
    y \<leftarrow> get_var_name_c \<D> y;
    if x < y then RETURN LESS else RETURN GREATER
  }\<close>

lemma perfect_shared_var_order_c_else_alt_def:
  \<open>perfect_shared_var_order_c_else = (\<lambda>(xs, \<V>) x y. doN {
    ASSERT (x < length xs);
    ASSERT (y < length xs);
    RETURN (if xs ! x < xs ! y then LESS else GREATER)
  })\<close>
  unfolding perfect_shared_var_order_c_else_def get_var_name_c_def
  by (intro ext) auto

lemma perfect_shared_var_order_c_else_fref:
  \<open>(uncurry2 perfect_shared_var_order_c_else, uncurry2 perfect_shared_var_order_s_else)
    \<in> (perfect_shared_vars_rel_c Id \<times>\<^sub>r nat_rel) \<times>\<^sub>r nat_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  unfolding perfect_shared_var_order_c_else_def perfect_shared_var_order_s_else_def
    get_var_name_c_def get_var_nameS_def uncurry_def
  apply (clarify intro!: frefI nres_relI)
  apply refine_vcg
  apply (auto dest!: multi_member_split simp: perfect_shared_vars_rel_c_def)
  done

lemma perfect_shared_var_order_s_alt:
  \<open>perfect_shared_var_order_s \<D> x y= do { 
    eq \<leftarrow> perfectly_shared_strings_equal_l \<D> x y;
    if eq then RETURN EQUAL
    else perfect_shared_var_order_s_else \<D> x y
  }\<close>
  unfolding perfect_shared_var_order_s_def
    perfect_shared_var_order_s_else_def
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    var_order_rel''
  by simp

definition ordered_const_GREATER :: \<open>ordered \<Rightarrow> nat \<Rightarrow> ordered nres\<close> where
  \<open>ordered_const_GREATER _ _ = RETURN GREATER\<close>

definition ordered_const_LESS :: \<open>ordered \<Rightarrow> nat \<Rightarrow> ordered nres\<close> where
  \<open>ordered_const_LESS _ _ = RETURN LESS\<close>

definition perfect_shared_term_order_rel_s_ifoldl
  :: \<open>ordered \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> (nat, string) shared_vars \<Rightarrow> ordered nres\<close>
where
  \<open>perfect_shared_term_order_rel_s_ifoldl \<equiv>
    ifoldl_ext_nres perfect_shared_term_order_rel_f perfect_shared_term_order_rel_dir
      ordered_const_GREATER ordered_const_LESS\<close>

lemma perfect_shared_term_order_rel_s_ifoldl_alt:
  \<open>perfect_shared_term_order_rel_s \<V> xs ys =
    perfect_shared_term_order_rel_s_ifoldl EQUAL xs ys \<V>\<close>
  unfolding perfect_shared_term_order_rel_s_alt_def perfect_shared_term_order_rel_s_ifoldl_def
    ordered_const_GREATER_def[abs_def] ordered_const_LESS_def[abs_def] ..

lemma nfoldli_foldl_nres:
  \<open>nfoldli xs (\<lambda>_. True) (\<lambda>x a. f a x) a = foldl_nres f a xs\<close>
proof (induction xs arbitrary: a)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
    by (simp add: foldl_nres_Cons) (intro bind_cong[OF refl], simp add: Cons.IH)
qed

text \<open>Both multiplication loops only read the traversed list, so we implement them
  with the read-only @{term cl_fold_env} instead of copying the list and popping
  it. The fixed operands of each loop form the (kept) environment of the fold.\<close>

definition mult_term_s_step
  :: \<open>(nat,string) shared_vars \<Rightarrow> nat list \<times> int \<Rightarrow> sllist_polynomial \<Rightarrow> nat list \<times> int
      \<Rightarrow> sllist_polynomial nres\<close>
where
  \<open>mult_term_s_step = (\<lambda>\<V> (p, m) b (q, n). do {
     pq \<leftarrow> mult_monoms_s \<V> p q;
     RETURN ((pq, m * n) # b)})\<close>

definition mult_term_s_foldl where
  \<open>mult_term_s_foldl \<equiv> \<lambda>\<V> pm. foldl_nres (mult_term_s_step \<V> pm)\<close>

lemma mult_term_s_alt_def:
  \<open>mult_term_s = (\<lambda>\<V> qs pm b. mult_term_s_foldl \<V> pm b qs)\<close>
  unfolding mult_term_s_def mult_term_s_foldl_def mult_term_s_step_def
  apply (intro ext)
  subgoal for \<V> qs pm b
    by (cases pm) (simp add: nfoldli_foldl_nres[symmetric] split_def)
  done

definition mult_poly_s_step
  :: \<open>(nat,string) shared_vars \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> nat list \<times> int
      \<Rightarrow> sllist_polynomial nres\<close>
where
  \<open>mult_poly_s_step = (\<lambda>\<V> q b pm. mult_term_s \<V> q pm b)\<close>

definition mult_poly_s_foldl where
  \<open>mult_poly_s_foldl \<equiv> \<lambda>\<V> q. foldl_nres (mult_poly_s_step \<V> q)\<close>

lemma mult_poly_s_alt_def:
  \<open>mult_poly_s \<V> p q = mult_poly_s_foldl \<V> q [] p\<close>
  unfolding mult_poly_s_def mult_poly_s_foldl_def mult_poly_s_step_def
  by (simp add: nfoldli_foldl_nres[symmetric])

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

definition check_linear_combi_l_s_dom_err :: \<open>sllist_polynomial \<Rightarrow> nat \<Rightarrow> string nres\<close> where
  \<open>check_linear_combi_l_s_dom_err p r = SPEC (\<lambda>_. True)\<close>

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

fun vars_llist_l where
  \<open>vars_llist_l [] = []\<close> |
  \<open>vars_llist_l (x#xs) = fst x @ vars_llist_l xs\<close>

lemma set_vars_llist_l[simp]: \<open>set(vars_llist_l xs) = vars_llist xs\<close>
  by (induction xs)
    (auto)

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

definition coeff_merge_while :: \<open>(nat,string)shared_vars \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list nres\<close> where
  \<open>coeff_merge_while \<V> = mcmp_merge_while (coeff_cmp \<V>) (coeff_valid \<V>) (coeff_mcmp \<V>)\<close>

definition coeff_pass :: \<open>(nat,string)shared_vars \<Rightarrow> nat list list \<Rightarrow> nat list list nres\<close> where
  \<open>coeff_pass \<V> = mcmp_pass (coeff_cmp \<V>) (coeff_valid \<V>) (coeff_mcmp \<V>)\<close>

definition coeff_run_passes :: \<open>(nat,string)shared_vars \<Rightarrow> nat list list \<Rightarrow> nat list list nres\<close> where
  \<open>coeff_run_passes \<V> = mcmp_run_passes (coeff_cmp \<V>) (coeff_valid \<V>) (coeff_mcmp \<V>)\<close>

lemma term_mcmp_alt_def:
  \<open>term_mcmp \<V> = (\<lambda>(xs, n) (ys, m). doN {
    a \<leftarrow> perfect_shared_term_order_rel_s \<V> xs ys;
    RETURN (a \<noteq> GREATER)
  })\<close>
  unfolding term_mcmp_def COPY_def
  by (auto intro!: ext split: prod.splits)

definition term_merge_while :: \<open>(nat,string)shared_vars \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial nres\<close> where
  \<open>term_merge_while \<V> = mcmp_merge_while (term_cmp \<V>) (term_valid \<V>) (term_mcmp \<V>)\<close>

definition term_pass :: \<open>(nat,string)shared_vars \<Rightarrow> sllist_polynomial list \<Rightarrow> sllist_polynomial list nres\<close> where
  \<open>term_pass \<V> = mcmp_pass (term_cmp \<V>) (term_valid \<V>) (term_mcmp \<V>)\<close>

definition term_run_passes :: \<open>(nat,string)shared_vars \<Rightarrow> sllist_polynomial list \<Rightarrow> sllist_polynomial list nres\<close> where
  \<open>term_run_passes \<V> = mcmp_run_passes (term_cmp \<V>) (term_valid \<V>) (term_mcmp \<V>)\<close>

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

lemma weak_equality_l_s_alt_def:
  \<open>weak_equality_l_s = RETURN oo (\<lambda>p q. p = q)\<close>
  unfolding weak_equality_l_s_def weak_equality_l_s_def by (auto intro!: ext)

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

lemma vars_of_monom_in_s_foldl:
  \<open>foldl (s_fold_inner \<V>) b xs = (b \<and> vars_of_monom_in_s xs \<V>)\<close>
  by (induction xs arbitrary: b) (auto simp: s_fold_inner_def)

definition s_poly_inner :: \<open>(nat, string) shared_vars \<Rightarrow> bool \<Rightarrow> string list \<times> int \<Rightarrow> bool\<close> where
  \<open>s_poly_inner \<V> \<equiv> \<lambda>b (vs, _). b \<and> vars_of_monom_in_s vs \<V>\<close>

lemma vars_of_poly_in_s_foldl:
  \<open>foldl (s_poly_inner \<V>) b xs = (b \<and> vars_of_poly_in_s xs \<V>)\<close>
  apply (induction xs arbitrary: b)
  subgoal by simp
  subgoal for p xs b by (cases p) (auto simp: s_poly_inner_def)
  done

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
        if q = [([], 1)]
        then do {
          pq \<leftarrow> (let r = the (fmlookup A i)
                in add_poly_l_s \<V> (p, r));
          RETURN (pq, xt, CSUCCESS)}
        else do {
          (no_new, q) \<leftarrow> normalize_poly_sharedS \<V> (q);
          let r = the (fmlookup A i);
          q \<leftarrow> mult_poly_full_s \<V> q r;
          pq \<leftarrow> add_poly_l_s \<V> (p, q);
          RETURN (pq, xt, CSUCCESS)
        }
      }
    }) ([], xs, CSUCCESS)
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

section \<open>Error Messages for Shared Polynomials\<close>

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

lemma uminus_poly_s_fref:
  \<open>(uminus_poly_s_nres, RETURN o uminus_poly_s) \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: uminus_poly_s_nres_spec)

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

fun vars_llist_s2 :: \<open>_ \<Rightarrow> _ list\<close> where
  \<open>vars_llist_s2 [] = []\<close> |
  \<open>vars_llist_s2 ((a,_) # xs) = a @ vars_llist_s2 xs\<close>

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

end
