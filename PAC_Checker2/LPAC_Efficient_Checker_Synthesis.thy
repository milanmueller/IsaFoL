theory LPAC_Efficient_Checker_Synthesis
  imports
    LPAC_Efficient_Checker
    LPAC_Perfectly_Shared_Vars
    LPAC_Checker_Synthesis
    PAC_Checker_LLVM.PAC_Checker_Synthesis
begin

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
        }}\<close>

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

lemma perfect_shared_term_order_rel_s_perfect_shared_term_order_rel:
  assumes \<open>(\<V>, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>(xs, xs') \<in> perfectly_shared_monom \<V>\<close> and
    \<open>(ys, ys') \<in> perfectly_shared_monom \<V>\<close>
  shows \<open>perfect_shared_term_order_rel_s \<V> xs ys \<le> \<Down>Id (perfect_shared_term_order_rel \<V>\<D> xs' ys')\<close>
  using assms
  unfolding perfect_shared_term_order_rel_s_def perfect_shared_term_order_rel_def
  apply (refine_rcg WHILET_refine[where R = \<open>Id \<times>\<^sub>r perfectly_shared_monom \<V> \<times>\<^sub>r perfectly_shared_monom \<V>\<close>]
    perfect_shared_var_order_s_perfect_shared_var_order)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: neq_Nil_conv)
  subgoal by (auto simp: neq_Nil_conv)
  subgoal by auto
  subgoal by (auto simp: neq_Nil_conv)
  subgoal by auto
  subgoal by auto
  done

fun mergeR :: "_ \<Rightarrow> _ \<Rightarrow>  'a list \<Rightarrow> 'a list \<Rightarrow> 'a list nres"
where
  "mergeR  \<Phi> f (x#xs) (y#ys) = do {
         ASSERT(\<Phi> x y);
         b \<leftarrow> f x y;
         if b then do {zs \<leftarrow> mergeR \<Phi> f xs (y#ys); RETURN (x # zs)}
         else do {zs \<leftarrow> mergeR \<Phi> f (x#xs) ys; RETURN (y # zs)}
       }"
| "mergeR  \<Phi> f xs [] = RETURN xs"
| "mergeR \<Phi> f [] ys = RETURN ys"

lemma mergeR_merge:
  assumes \<open>\<And>x y. x\<in>set xs \<union> set ys \<Longrightarrow> y\<in>set xs \<union> set ys \<Longrightarrow>\<Phi> x y\<close> and
    \<open>\<And>x y. x\<in>set xs \<union> set ys \<Longrightarrow> y\<in>set xs \<union> set ys \<Longrightarrow> f x y \<le> \<Down>Id (RETURN (f' x y))\<close> and
    \<open>(xs,xs')\<in>Id\<close>and
    \<open>(ys,ys')\<in>Id\<close>
  shows
    \<open>mergeR \<Phi> f xs ys \<le> \<Down>Id (RETURN (merge f' xs' ys'))\<close>
proof -
  have xs: \<open>xs' = xs\<close> \<open>ys' = ys\<close>
    using assms
    by auto
  show ?thesis
    using assms(1,2) unfolding xs
    apply (induction f' xs ys arbitrary: xs' ys' rule: merge.induct)
    subgoal for f' x xs y ys
      unfolding mergeR.simps merge.simps
      apply (refine_rcg)
      subgoal by simp
      subgoal premises p
        using p(1,2,3,4,5) p(4)[of x y, simplified]
        apply auto
        apply (smt RES_sng_eq_RETURN insert_compr ireturn_rule nres_order_simps(20) specify_left)
        apply (smt RES_sng_eq_RETURN insert_compr ireturn_rule nres_order_simps(20) specify_left)
        done
      done
    subgoal by auto
    subgoal by auto
    done
qed

lemma merge_alt:
  "RETURN (merge f xs ys) = SPEC(\<lambda>zs. zs = merge f xs ys \<and> set zs = set xs \<union> set ys)"
  by (induction f xs ys rule: merge.induct)
   (clarsimp_all simp: Collect_conv_if insert_commute)

text \<open>Linked-list-friendly monadic merge sort: splitting by \<open>take\<close>/\<open>drop\<close> has no
  owning-list implementation, so the halves are produced by the alternating split
  \<open>alt_split\<close> of \<open>LLVM_Sort\<close> instead \<comment> \<open>mirroring the pure \<open>msort_alt\<close> used for the
  unshared polynomials in \<open>PAC_Checker_LLVM\<close>.\<close>\<close>

function msort_altR :: "_ \<Rightarrow> _ \<Rightarrow> 'a list \<Rightarrow> 'a list nres"
where
  "msort_altR \<Phi> f [] = RETURN []"
| "msort_altR \<Phi> f [x] = RETURN [x]"
| "msort_altR \<Phi> f (x # y # xs) =
    (case alt_split (x # y # xs) of (l, r) \<Rightarrow> do {
      l \<leftarrow> msort_altR \<Phi> f l;
      r \<leftarrow> msort_altR \<Phi> f r;
      mergeR \<Phi> f l r
    })"
  by pat_completeness auto
termination
  by (relation \<open>measure (length o snd o snd)\<close>)
    (auto split: prod.splits dest!: alt_split_len_eq)

lemma alt_split_set: \<open>set (fst (alt_split xs)) \<union> set (snd (alt_split xs)) = set xs\<close>
  using alt_split_mset[of xs] by (metis set_mset_mset set_mset_union)

lemma alt_split_set_eq:
  \<open>alt_split xs = (l, r) \<Longrightarrow> set l \<union> set r = set xs\<close>
  using alt_split_set[of xs] by auto

lemma set_msort_alt[simp]: \<open>set (msort_alt f xs) = set xs\<close>
  by (meson mset_eq_setD msort_alt_mset)

lemma msort_altR_msort_alt:
  assumes \<open>\<And>x y. x\<in>set xs \<Longrightarrow> y\<in>set xs \<Longrightarrow>\<Phi> x y\<close> and
    \<open>\<And>x y. x\<in>set xs \<Longrightarrow> y\<in>set xs \<Longrightarrow> f x y \<le> \<Down>Id (RETURN (f' x y))\<close>
  shows
    \<open>msort_altR \<Phi> f xs \<le> \<Down>Id (RETURN (msort_alt f' xs))\<close>
  using assms
proof (induction f' xs rule: msort_alt.induct)
  case (1 f')
  then show ?case by auto
next
  case (2 f' x)
  then show ?case by auto
next
  case (3 f' x y xs)
  obtain l r where lr: \<open>alt_split (x # y # xs) = (l, r)\<close>
    by (cases \<open>alt_split (x # y # xs)\<close>)
  have sub: \<open>set l \<subseteq> set (x # y # xs)\<close> \<open>set r \<subseteq> set (x # y # xs)\<close>
    using alt_split_set_eq[OF lr] by auto
  have Phi': \<open>\<Phi> a b\<close> if \<open>a \<in> set l \<union> set r\<close> \<open>b \<in> set l \<union> set r\<close> for a b
    using 3(3) sub that by blast
  have f': \<open>f a b \<le> \<Down>Id (RETURN (f' a b))\<close> if \<open>a \<in> set l \<union> set r\<close> \<open>b \<in> set l \<union> set r\<close> for a b
    using 3(4) sub that by blast
  have IHl: \<open>msort_altR \<Phi> f l \<le> \<Down>Id (RETURN (msort_alt f' l))\<close>
    apply (rule 3(1)[OF lr[symmetric]])
    subgoal by (rule Phi') auto
    subgoal by (rule f') auto
    done
  have IHr: \<open>msort_altR \<Phi> f r \<le> \<Down>Id (RETURN (msort_alt f' r))\<close>
    apply (rule 3(2)[OF lr[symmetric]])
    subgoal by (rule Phi') auto
    subgoal by (rule f') auto
    done
  have M: \<open>mergeR \<Phi> f (msort_alt f' l) (msort_alt f' r)
      \<le> \<Down>Id (RETURN (merge f' (msort_alt f' l) (msort_alt f' r)))\<close>
    apply (rule mergeR_merge)
    subgoal by (auto intro: Phi')
    subgoal by (auto intro: f'[unfolded Down_id_eq] f')
    subgoal by auto
    subgoal by auto
    done
  show ?case
    using IHl IHr M
    unfolding msort_altR.simps msort_alt.simps lr prod.case
    by (auto simp: pw_le_iff refine_pw_simps)
qed

lemma merge_list_rel:
  assumes \<open>\<And>x y x' y'. x\<in>set xs \<Longrightarrow> y\<in>set ys \<Longrightarrow> x'\<in>set xs' \<Longrightarrow> y'\<in>set ys' \<Longrightarrow> (x,x')\<in>R \<Longrightarrow> (y,y')\<in>R \<Longrightarrow> f x y = f' x' y'\<close> and
    \<open>(xs,xs') \<in> \<langle>R\<rangle>list_rel\<close> and
    \<open>(ys,ys') \<in> \<langle>R\<rangle>list_rel\<close>
  shows \<open>(merge f xs ys, merge f' xs' ys') \<in> \<langle>R\<rangle>list_rel\<close>
proof -
  show ?thesis
    using assms
  proof (induction f' xs' ys' arbitrary: f xs ys rule: merge.induct)
    case (1 f' x' xs' y' y's)
    have \<open>f' x' y' \<Longrightarrow>
      (merge f (tl xs) ys, merge f' xs' (y' # y's)) \<in> \<langle>R\<rangle>list_rel\<close>
      apply (rule 1)
      apply assumption
      apply (rule 1(3); auto dest: in_set_tlD)
      using 1(4-5) apply (auto simp: list_rel_split_left_iff)
      done
    moreover have \<open>\<not>f' x' y' \<Longrightarrow>
      (merge f ( xs) (tl ys), merge f' (x' # xs') (y's)) \<in> \<langle>R\<rangle>list_rel\<close>
      apply (rule 1)
      apply assumption
      apply (rule 1(3); auto dest: in_set_tlD)
      using 1(4-5) apply (auto simp: list_rel_split_left_iff)
      done
    ultimately show ?case
      using 1(1,4-5) 1(3)[of \<open>hd xs\<close> \<open>hd ys\<close> x' y']
      by (auto simp: list_rel_split_left_iff)
  qed  (auto simp: list_rel_split_left_iff)
qed

lemma list_rel_takeD:
  \<open>(a, b) \<in> \<langle>R\<rangle>list_rel \<Longrightarrow> (n, n')\<in> Id \<Longrightarrow> (take n a, take n' b) \<in> \<langle>R\<rangle>list_rel\<close>
  by (simp add: list_rel_eq_listrel listrel_iff_nth relAPP_def)

lemma list_rel_dropD:
  \<open>(a, b) \<in> \<langle>R\<rangle>list_rel \<Longrightarrow> (n, n')\<in> Id \<Longrightarrow> (drop n a, drop n' b) \<in> \<langle>R\<rangle>list_rel\<close>
  by (simp add: list_rel_eq_listrel listrel_iff_nth relAPP_def)

lemma alt_split_list_rel:
  \<open>(xs, ys) \<in> \<langle>R\<rangle>list_rel \<Longrightarrow>
   (fst (alt_split xs), fst (alt_split ys)) \<in> \<langle>R\<rangle>list_rel \<and>
   (snd (alt_split xs), snd (alt_split ys)) \<in> \<langle>R\<rangle>list_rel\<close>
  apply (induction xs arbitrary: ys)
  subgoal by auto
  subgoal for x xs ys
    apply (cases ys)
    apply (auto split: prod.splits simp: list_rel_split_right_iff)
    apply (metis fst_conv snd_conv)+
    done
  done

lemma msort_alt_list_rel:
  assumes  \<open>\<And>x y x' y'. x\<in>set xs \<Longrightarrow> y\<in>set xs \<Longrightarrow> x'\<in>set xs' \<Longrightarrow> y'\<in>set xs' \<Longrightarrow> (x,x')\<in>R \<Longrightarrow> (y,y')\<in>R \<Longrightarrow> f x y = f' x' y'\<close> and
    \<open>(xs,xs') \<in> \<langle>R\<rangle>list_rel\<close>
  shows \<open>(msort_alt f xs, msort_alt f' xs') \<in> \<langle>R\<rangle>list_rel\<close>
  using assms
proof (induction f' xs' arbitrary: xs rule: msort_alt.induct)
  case (1 f')
  then show ?case by auto
next
  case (2 f' x')
  then show ?case
    by (metis list_relE(4) list_rel_simp(2) msort_alt.simps(2))
next
  case (3 f' x' y' xs')
  obtain a b cs where xs: \<open>xs = a # b # cs\<close> and
    ab: \<open>(a, x') \<in> R\<close> \<open>(b, y') \<in> R\<close> and cs: \<open>(cs, xs') \<in> \<langle>R\<rangle>list_rel\<close>
    by (metis "3"(4) list_relE(4))
  obtain l' r' where lr': \<open>alt_split (x' # y' # xs') = (l', r')\<close>
    by (cases \<open>alt_split (x' # y' # xs')\<close>)
  obtain l r where lr: \<open>alt_split (a # b # cs) = (l, r)\<close>
    by (cases \<open>alt_split (a # b # cs)\<close>)
  have rel_l: \<open>(l, l') \<in> \<langle>R\<rangle>list_rel\<close> and rel_r: \<open>(r, r') \<in> \<langle>R\<rangle>list_rel\<close>
    using alt_split_list_rel[of \<open>a # b # cs\<close> \<open>x' # y' # xs'\<close> R] 3(4) xs lr lr'
    by auto
  have subs: \<open>set l \<subseteq> set xs\<close> \<open>set r \<subseteq> set xs\<close>
    \<open>set l' \<subseteq> set (x' # y' # xs')\<close> \<open>set r' \<subseteq> set (x' # y' # xs')\<close>
    using alt_split_set_eq[OF lr] alt_split_set_eq[OF lr'] xs by auto
  have IH1: \<open>(msort_alt f l, msort_alt f' l') \<in> \<langle>R\<rangle>list_rel\<close>
    apply (rule 3(1)[OF lr'[symmetric]])
    subgoal for xa ya x'a y'a
      by (meson "3.prems"(1) subs(1,3) subsetD)
    subgoal by (rule rel_l)
    done
  have IH2: \<open>(msort_alt f r, msort_alt f' r') \<in> \<langle>R\<rangle>list_rel\<close>
    apply (rule 3(2)[OF lr'[symmetric]])
    subgoal for xa ya x'a y'a
      by (meson "3.prems"(1) subs(2,4) subset_iff)
    subgoal by (rule rel_r)
    done
  show ?case
    unfolding xs msort_alt.simps lr lr' prod.case
    apply (rule merge_list_rel)
    subgoal for xa ya x'a y'a
      by (rule "3.prems"(1)) (use subs in \<open>auto\<close>)
    subgoal by (rule IH1)
    subgoal by (rule IH2)
    done
qed

definition sort_poly_spec_s where
  \<open>sort_poly_spec_s \<V> xs = msort_altR (\<lambda>xs ys. (\<forall>a\<in>set (fst xs). a \<in># dom_m (fst (snd \<V>))) \<and>  (\<forall>a\<in>set(fst ys). a \<in># dom_m (fst (snd \<V>))))
     (\<lambda>xs ys. do {a \<leftarrow> perfect_shared_term_order_rel_s \<V> (fst xs) (fst ys); RETURN (a \<noteq> GREATER)}) xs\<close>

lemma sort_poly_spec_s_sort_poly_spec:
  assumes \<open>(\<V>, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>(xs, xs') \<in> perfectly_shared_polynom \<V>\<close> and
    \<open>vars_llist xs' \<subseteq> set_mset \<V>\<D>\<close>
 shows
  \<open>sort_poly_spec_s \<V> xs
  \<le>\<Down>(perfectly_shared_polynom \<V>)
  (sort_poly_spec xs')
   \<close>
proof -
  have [iff]: \<open>sorted_wrt (rel2p (Id \<union> term_order_rel)) (map fst (msort_alt (\<lambda>xs ys. rel2p (Id \<union> term_order_rel) (fst xs) (fst ys)) xs'))\<close>
    unfolding sorted_wrt_map
    apply (rule msort_alt_sorted)
    apply (smt Un_iff pair_in_Id_conv rel2p_def term_order_rel_trans transp_def)
    apply (auto simp: rel2p_def)
    using total_on_lexord_less_than_char_linear var_order_rel_def by auto
  have [iff]:
    \<open>(a,b)\<in> \<langle>\<langle>(perfectly_shared_var_rel \<V>)\<inverse>\<rangle>list_rel \<times>\<^sub>r int_rel\<rangle>list_rel \<longleftrightarrow> (b,a)\<in>perfectly_shared_polynom \<V>\<close> for a b
    by (metis converse_Id converse_iff inv_list_rel_eq inv_prod_rel_eq)

  show ?thesis
    unfolding sort_poly_spec_s_def
    apply (rule order_trans[OF msort_altR_msort_alt[where
      f'=\<open> \<lambda>xs ys. (map (the o fmlookup (fst (snd \<V>))) (fst xs), map (the o fmlookup (fst (snd \<V>))) (fst ys)) \<in> Id \<union> term_order_rel\<close>]])
    subgoal for x y
      apply (cases x, cases y)
      using assms by (auto simp: list_rel_append1 list_rel_split_right_iff perfectly_shared_var_rel_def br_def
        perfectly_shared_vars_rel_def append_eq_append_conv2 append_eq_Cons_conv Cons_eq_append_conv
        dest!: split_list split: prod.splits)
      subgoal for x y
        using assms(2,3) apply -
        apply (frule in_set_rel_inD)
        apply assumption
        apply (frule in_set_rel_inD[of _ _ _ y])
        apply assumption
        apply (elim bexE)+
        subgoal for x' y'
          apply (refine_vcg perfect_shared_term_order_rel_s_perfect_shared_term_order_rel[OF assms(1), THEN order_trans,
            of _ \<open>fst x'\<close> _ \<open>fst y'\<close>])
          subgoal
            by (cases x', cases x) auto
          subgoal
            by (cases y', cases y) auto
          subgoal
            using assms
            apply (clarsimp dest!: split_list intro!: perfect_shared_term_order_rel_spec[THEN order_trans]
              simp: append_eq_append_conv2 append_eq_Cons_conv Cons_eq_append_conv
              vars_llist_def)
            apply (rule perfect_shared_term_order_rel_spec[THEN order_trans])
            apply auto[]
            apply auto[]
            apply simp
            apply (clarsimp_all simp: perfectly_shared_monom_eqD)
            apply (cases x, cases y, cases x', cases y')
            apply (clarsimp_all simp flip: perfectly_shared_monom_eqD)
            apply (case_tac xa)
            apply (clarsimp_all simp flip: perfectly_shared_monom_eqD simp: lexord_irreflexive)
            by (meson lexord_irreflexive term_order_rel_trans var_order_rel_antisym)
          done
        done
      unfolding sort_poly_spec_def conc_fun_RES
      apply auto
      apply (subst Image_iff)
      apply (rule_tac x= \<open>msort_alt (\<lambda>xs ys.  rel2p (Id \<union> term_order_rel) (fst xs) (fst ys)) (xs')\<close> in bexI)
      apply (auto intro!: msort_alt_list_rel simp flip: perfectly_shared_monom_eqD
          simp: assms)
      apply (auto simp: rel2p_def)
      done
qed

definition msort_coeff_s :: \<open>(nat,string)shared_vars \<Rightarrow> nat list \<Rightarrow> nat list nres\<close> where
  \<open>msort_coeff_s \<V> xs = msort_altR (\<lambda>a b. a \<in> set xs \<and> b \<in> set xs)
  (\<lambda>a b. do {
    x \<leftarrow> get_var_nameS \<V> a;
  y \<leftarrow> get_var_nameS \<V> b;
    RETURN(a = b \<or> var_order x y)
  }) xs\<close>


lemma perfectly_shared_var_rel_unique_left:
  \<open>(x, y) \<in> perfectly_shared_var_rel \<V> \<Longrightarrow> (x, y') \<in> perfectly_shared_var_rel \<V> \<Longrightarrow> y = y'\<close>
  using perfectly_shared_monom_unique_left[of \<open>[x]\<close>  \<open>[y]\<close> \<V> \<open>[y']\<close>] by auto

lemma perfectly_shared_var_rel_unique_right:
  \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel \<Longrightarrow> (x, y) \<in> perfectly_shared_var_rel \<V> \<Longrightarrow> (x', y) \<in> perfectly_shared_var_rel \<V> \<Longrightarrow> x = x'\<close>
  using perfectly_shared_monom_unique_right[of \<V> \<D>\<V> \<open>[x]\<close>  \<open>[y]\<close>  \<open>[x']\<close>]
  by auto

lemma msort_coeff_s_sort_coeff:
  fixes xs' :: \<open>string list\<close> and
    \<V> :: \<open>(nat,string)shared_vars\<close>
  assumes
    \<open>(xs, xs') \<in> perfectly_shared_monom \<V>\<close> and
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>set xs' \<subseteq> set_mset \<D>\<V>\<close>
  shows \<open>msort_coeff_s \<V> xs \<le> \<Down>(perfectly_shared_monom \<V>) (sort_coeff xs')\<close>
proof -
  have H: \<open>x \<in> set xs \<Longrightarrow> \<exists>x' \<in> set xs'. (x,x') \<in> perfectly_shared_var_rel \<V> \<and> x' \<in># \<D>\<V>\<close> for x
    using assms(1,3) by (auto dest: in_set_rel_inD)
  define f where
    \<open>f x y \<longleftrightarrow> x = y \<or> var_order (fst (snd \<V>) \<propto> x) (fst (snd \<V>) \<propto> y)\<close> for x y
  have [simp]: \<open>x \<in> set xs \<Longrightarrow> x' \<in> set xs' \<Longrightarrow> (x, x') \<in> perfectly_shared_var_rel \<V> \<Longrightarrow>
    fst (snd \<V>) \<propto> x = x'\<close> for x x'
    using assms(2)
    by (auto simp: perfectly_shared_vars_rel_def perfectly_shared_var_rel_def br_def)
  have [intro]: \<open>transp (\<lambda>x y. x = y \<or> (x, y) \<in> var_order_rel)\<close>
    by (smt transE trans_var_order_rel transp_def)
  have [intro]: \<open>sorted_wrt (rel2p (Id \<union> var_order_rel))  (msort_alt (\<lambda>a b. a = b \<or> var_order a b) xs')\<close>
    using var_roder_rel_total by (auto intro!: msort_alt_sorted simp: rel2p_def[abs_def])
  show ?thesis
    unfolding msort_coeff_s_def
    apply (rule msort_altR_msort_alt[of _ _ _ f, THEN order_trans])
    subgoal by auto
    subgoal for x y
      unfolding f_def
      apply (frule H[of x])
      apply (frule H[of y])
      apply (elim bexE)
      apply (refine_vcg get_var_nameS_spec2[THEN order_trans] assms)
      apply (solves auto)
      apply (solves auto)
      apply (subst Down_id_eq)
      apply (refine_vcg get_var_nameS_spec2[THEN order_trans] assms)
      apply (solves auto)
      apply (solves auto)
      apply (auto simp: perfectly_shared_var_rel_def br_def)
      done
    subgoal
      apply (subst Down_id_eq)
      apply (auto simp: sort_coeff_def intro!: RETURN_RES_refine)
      apply (rule_tac x = \<open>msort_alt (\<lambda>a b. a = b \<or> var_order a b) xs'\<close> in exI)
      apply (force intro!: msort_alt_list_rel assms simp: f_def
        dest: perfectly_shared_var_rel_unique_left
        perfectly_shared_var_rel_unique_right[OF assms(2)])
      done
    done
qed

type_synonym sllist_polynomial = \<open>(nat list \<times> int) list\<close>

definition sort_all_coeffs_s :: \<open>(nat,string)shared_vars \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial nres\<close> where
\<open>sort_all_coeffs_s \<V> xs = monadic_nfoldli xs (\<lambda>_. RETURN True) (\<lambda>(a, n) b. do {ASSERT((a,n)\<in>set xs);a \<leftarrow> msort_coeff_s \<V> a; RETURN ((a, n) # b)}) []\<close>

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
     p \<leftarrow> sort_poly_spec_s \<V> p;
    RETURN (merge_coeffs0_s p)
  }\<close>

text \<open>The \<open>monadic_nfoldli\<close> of this development (\<open>Aux_Lemmas\<close> in \<open>PAC_Checker_LLVM\<close>)
  is a local replacement without the refinement setup of the AFP's
  \<open>Sepref_Foreach\<close>; the standard refinement rule is restated here.\<close>

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

lemma sort_all_coeffs_s_sort_all_coeffs:
  fixes xs :: \<open>sllist_polynomial\<close> and \<V> :: \<open>(nat,string)shared_vars\<close>
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
    apply (refine_vcg \<V> msort_coeff_s_sort_coeff)
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

section \<open>Building Blocks for Shared Polynomials\<close>

text \<open>Shared monomials are open lists of 64-bit variable indices (pure elements),
  shared polynomials are owning lists of (monomial, coefficient) pairs - the same
  two-level ladder as \<open>monom_assn\<close>/\<open>poly_assn\<close> for the unshared polynomials, with
  \<open>strl_assn\<close> replaced by \<open>unat_assn\<close> indices.\<close>

abbreviation monom_s_assn where
  \<open>monom_s_assn \<equiv> os_assn (unat_assn' TYPE(64))\<close>

abbreviation mnml_s_assn where
  \<open>mnml_s_assn \<equiv> monom_s_assn \<times>\<^sub>a sbi_assn\<close>

abbreviation poly_s_assn where
  \<open>poly_s_assn \<equiv> ol_assn mnml_s_assn\<close>

type_synonym monom_s_conc = \<open>64 word os_list\<close>
type_synonym mnml_s_conc = \<open>monom_s_conc \<times> sbin_conc \<times> 1 word\<close>

lemma unat64_assn_pure[safe_constraint_rules]: \<open>is_pure (unat_assn' TYPE(64))\<close>
  by simp

context
begin
interpretation llvm_prim_arith_setup .

lemma unat_eq_rule:
  \<open>llvm_htriple (unat_assn' TYPE(64) a c ** unat_assn' TYPE(64) a' c') (ll_icmp_eq c c')
    (\<lambda>r. unat_assn' TYPE(64) a c ** unat_assn' TYPE(64) a' c' ** \<upharpoonleft>bool.assn (a = a') r)\<close>
  unfolding unat_rel_def unat.rel_def
  supply [simp] = pure_def in_br_conv bool.assn_def
  by vcg

end

subsection \<open>Equality\<close>

definition monom_s_eq :: \<open>monom_s_conc \<Rightarrow> monom_s_conc \<Rightarrow> 1 word llM\<close> where
  \<open>monom_s_eq \<equiv> os_eq ll_icmp_eq\<close>

lemma monom_s_eq_simps[llvm_code]:
  \<open>monom_s_eq p q = (
    if p = null then Mreturn (from_bool (q = null))
    else if q = null then Mreturn 0
    else doM {
      np \<leftarrow> ll_load p; nq \<leftarrow> ll_load q;
      b \<leftarrow> ll_icmp_eq (node.val np) (node.val nq);
      if to_bool b then monom_s_eq (node.next np) (node.next nq)
      else Mreturn 0 })\<close>
  unfolding monom_s_eq_def by (rule os_eq.simps)

lemma monom_s_eq_rule[vcg_rules]:
  \<open>llvm_htriple (monom_s_assn xs p ** monom_s_assn ys q) (monom_s_eq p q)
    (\<lambda>r. monom_s_assn xs p ** monom_s_assn ys q ** \<upharpoonleft>bool.assn (xs = ys) r)\<close>
  unfolding monom_s_eq_def
  by (rule os_eq_rule[where A=\<open>unat_assn' TYPE(64)\<close> and eqi=ll_icmp_eq,
        OF unat64_assn_pure unat_eq_rule])

sepref_register \<open>(=) :: nat list \<Rightarrow> nat list \<Rightarrow> bool\<close>

lemma monom_s_eq_hnr[sepref_fr_rules]:
  \<open>(uncurry monom_s_eq, uncurry (RETURN oo (=))) \<in> monom_s_assn\<^sup>k *\<^sub>a monom_s_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding monom_s_eq_def
  using ol_eq_hnr[where A=\<open>unat_assn' TYPE(64)\<close> and eqi=ll_icmp_eq, OF unat_eq_rule]
  unfolding ol_assn_pure_conv[OF unat64_assn_pure] .

definition mnml_s_eq_impl :: \<open>mnml_s_conc \<Rightarrow> mnml_s_conc \<Rightarrow> 1 word llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>mnml_s_eq_impl \<equiv> \<lambda>(m, c) (m', c'). doM {
     b \<leftarrow> monom_s_eq m m';
     if to_bool b then signed_big_int_eq_impl c c' else Mreturn 0 }\<close>

lemma mnml_s_eq_rule[vcg_rules]:
  \<open>llvm_htriple (mnml_s_assn x c ** mnml_s_assn y d) (mnml_s_eq_impl c d)
    (\<lambda>r. mnml_s_assn x c ** mnml_s_assn y d ** \<upharpoonleft>bool.assn (x = y) r)\<close>
  unfolding mnml_s_eq_impl_def
  supply [simp] = bool.assn_def
  apply (cases x; cases y; cases c; cases d; simp only: prod_assn_pair_conv prod.case)
  by vcg

lemma mnml_s_eq_rule'[vcg_rules]:
  \<open>llvm_htriple
     (monom_s_assn m mi ** sbi_assn n ci ** monom_s_assn m' mi' ** sbi_assn n' ci')
     (mnml_s_eq_impl (mi, ci) (mi', ci'))
     (\<lambda>r. monom_s_assn m mi ** sbi_assn n ci ** monom_s_assn m' mi' ** sbi_assn n' ci' **
        \<upharpoonleft>bool.assn ((m, n) = (m', n')) r)\<close>
  using mnml_s_eq_rule[of \<open>(m, n)\<close> \<open>(mi, ci)\<close> \<open>(m', n')\<close> \<open>(mi', ci')\<close>]
  by (simp add: sep_conj_assoc)

definition poly_s_eq_impl :: \<open>mnml_s_conc os_list \<Rightarrow> mnml_s_conc os_list \<Rightarrow> 1 word llM\<close>
  where \<open>poly_s_eq_impl \<equiv> os_eq mnml_s_eq_impl\<close>

lemma poly_s_eq_impl_simps[llvm_code]:
  \<open>poly_s_eq_impl p q = (
    if p = null then Mreturn (from_bool (q = null))
    else if q = null then Mreturn 0
    else doM {
      np \<leftarrow> ll_load p; nq \<leftarrow> ll_load q;
      b \<leftarrow> mnml_s_eq_impl (node.val np) (node.val nq);
      if to_bool b then poly_s_eq_impl (node.next np) (node.next nq)
      else Mreturn 0 })\<close>
  unfolding poly_s_eq_impl_def by (rule os_eq.simps)

lemma poly_s_eq_rule[vcg_rules]:
  \<open>llvm_htriple (poly_s_assn xs p ** poly_s_assn ys q) (poly_s_eq_impl p q)
    (\<lambda>r. poly_s_assn xs p ** poly_s_assn ys q ** \<upharpoonleft>bool.assn (xs = ys) r)\<close>
  unfolding poly_s_eq_impl_def
  by (rule ol_eq_rule[where A=mnml_s_assn and eqi=mnml_s_eq_impl, OF mnml_s_eq_rule])

lemma poly_s_eq_hnr[sepref_fr_rules]:
  \<open>(uncurry poly_s_eq_impl, uncurry (RETURN oo (=)))
    \<in> poly_s_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding poly_s_eq_impl_def
  by (rule ol_eq_hnr[where A=mnml_s_assn and eqi=mnml_s_eq_impl, OF mnml_s_eq_rule])

subsection \<open>Copy\<close>

definition monom_s_copy :: \<open>monom_s_conc \<Rightarrow> monom_s_conc llM\<close> where
  \<open>monom_s_copy \<equiv> ol_copy Mreturn\<close>

lemma monom_s_copy_simps[llvm_code]:
  \<open>monom_s_copy p = (if p = null then Mreturn null else doM {
      n \<leftarrow> ll_load p;
      c \<leftarrow> Mreturn (node.val n);
      t \<leftarrow> monom_s_copy (node.next n);
      os_prepend c t
    })\<close>
  unfolding monom_s_copy_def by (rule ol_copy.simps)

lemma monom_s_copy_rule[vcg_rules]:
  \<open>llvm_htriple (monom_s_assn xs p) (monom_s_copy p)
    (\<lambda>r. monom_s_assn xs p ** monom_s_assn xs r)\<close>
  using os_copy_rule[where A=\<open>unat_assn' TYPE(64)\<close>, OF unat64_assn_pure]
  unfolding monom_s_copy_def .

lemma monom_s_copy_hnr[sepref_fr_rules]:
  \<open>(monom_s_copy, RETURN o COPY) \<in> monom_s_assn\<^sup>k \<rightarrow>\<^sub>a monom_s_assn\<close>
  using ol_copy_hnr[where A=\<open>unat_assn' TYPE(64)\<close> and cp=Mreturn,
      OF pure_elem_copy_rule[OF unat64_assn_pure]]
  unfolding ol_assn_pure_conv[OF unat64_assn_pure] monom_s_copy_def .

lemma monom_s_pop_front_hnr[sepref_fr_rules]:
  \<open>(os_pop, mop_list_pop_front) \<in> monom_s_assn\<^sup>d \<rightarrow>\<^sub>a unat_assn' TYPE(64) \<times>\<^sub>a monom_s_assn\<close>
  using ol_pop_front_hnr[where A=\<open>unat_assn' TYPE(64)\<close>]
  unfolding ol_assn_pure_conv[OF unat64_assn_pure] .

definition mnml_s_copy_impl :: \<open>mnml_s_conc \<Rightarrow> mnml_s_conc llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>mnml_s_copy_impl \<equiv> \<lambda>(m, c). doM { m' \<leftarrow> monom_s_copy m; c' \<leftarrow> sbi_copy c; Mreturn (m', c') }\<close>

lemma mnml_s_copy_rule[vcg_rules]:
  \<open>llvm_htriple (mnml_s_assn x c) (mnml_s_copy_impl c)
    (\<lambda>r. mnml_s_assn x c ** mnml_s_assn x r)\<close>
  unfolding mnml_s_copy_impl_def
  apply (cases x; cases c; simp only: prod_assn_pair_conv prod.case)
  by vcg

lemma mnml_s_copy_rule'[vcg_rules]:
  \<open>llvm_htriple (monom_s_assn m mi ** sbi_assn n ci) (mnml_s_copy_impl (mi, ci))
    (\<lambda>r. monom_s_assn m mi ** sbi_assn n ci ** mnml_s_assn (m, n) r)\<close>
  using mnml_s_copy_rule[of \<open>(m, n)\<close> \<open>(mi, ci)\<close>] by (simp add: sep_conj_assoc)

lemma mnml_s_copy_hnr[sepref_fr_rules]:
  \<open>(mnml_s_copy_impl, RETURN o COPY) \<in> mnml_s_assn\<^sup>k \<rightarrow>\<^sub>a mnml_s_assn\<close>
  supply [vcg_rules] = mnml_s_copy_rule' mnml_s_copy_rule'[unfolded pure_def]
  apply sepref_to_hoare
  apply vcg_monadify
  by vcg'

definition poly_s_copy_impl :: \<open>mnml_s_conc os_list \<Rightarrow> mnml_s_conc os_list llM\<close>
  where \<open>poly_s_copy_impl \<equiv> ol_copy mnml_s_copy_impl\<close>

lemma poly_s_copy_impl_simps[llvm_code]:
  \<open>poly_s_copy_impl p = (if p = null then Mreturn null else doM {
      n \<leftarrow> ll_load p;
      c \<leftarrow> mnml_s_copy_impl (node.val n);
      t \<leftarrow> poly_s_copy_impl (node.next n);
      os_prepend c t
    })\<close>
  unfolding poly_s_copy_impl_def by (rule ol_copy.simps)

lemma poly_s_copy_rule[vcg_rules]:
  \<open>llvm_htriple (poly_s_assn xs p) (poly_s_copy_impl p)
    (\<lambda>r. poly_s_assn xs p ** poly_s_assn xs r)\<close>
  unfolding poly_s_copy_impl_def
  by (rule ol_copy_rule[where A=mnml_s_assn and cp=mnml_s_copy_impl, OF mnml_s_copy_rule])

lemma poly_s_copy_hnr[sepref_fr_rules]:
  \<open>(poly_s_copy_impl, RETURN o COPY) \<in> poly_s_assn\<^sup>k \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding poly_s_copy_impl_def
  by (rule ol_copy_hnr[where A=mnml_s_assn and cp=mnml_s_copy_impl, OF mnml_s_copy_rule])

subsection \<open>Free\<close>

definition mnml_s_free :: \<open>mnml_s_conc \<Rightarrow> unit llM\<close> where [llvm_code]:
  \<open>mnml_s_free \<equiv> \<lambda>(m, c). doM { os_delete m; sbi_free c }\<close>

lemma mnml_s_assn_free[sepref_frame_free_rules]: \<open>MK_FREE mnml_s_assn mnml_s_free\<close>
  unfolding mnml_s_free_def
  by (rule mk_free_pair[OF os_assn_free sbi_free_rule])

definition poly_s_free where \<open>poly_s_free \<equiv> ol_delete mnml_s_free\<close>

lemma poly_s_free_simps[llvm_code]:
  \<open>poly_s_free p = (if p = null then Mreturn () else doM {
     n \<leftarrow> ll_load p; mnml_s_free (node.val n); ll_free p; poly_s_free (node.next n) })\<close>
  unfolding poly_s_free_def by (rule ol_delete.simps)

lemmas [llvm_pre_simp] = poly_s_free_def[symmetric]

lemma poly_s_assn_free[sepref_frame_free_rules]: \<open>MK_FREE poly_s_assn poly_s_free\<close>
  unfolding poly_s_free_def by (rule ol_assn_free[OF mnml_s_assn_free])

section \<open>The \<open>ordered\<close> Result Type as a Tag Byte\<close>

text \<open>\<open>ordered\<close> (\<open>EQUAL\<close>/\<open>LESS\<close>/\<open>GREATER\<close>/\<open>UNKNOWN\<close>) is encoded as a pure tag byte,
  following the \<open>status_assn\<close> pattern of the \<open>PAC_Checker_LLVM\<close> synthesis.\<close>

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

sepref_register EQUAL LESS GREATER UNKNOWN perfect_shared_var_order_s
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

text \<open>Comparisons of \<open>ordered\<close> values appear as guards (\<open>b = UNKNOWN\<close> etc.); a plain
  \<open>(=)\<close> cannot be identified there (the operand interface is still schematic when the
  guard is processed), so the checks are provided as discriminators, mirroring
  \<open>is_cfailed\<close> in the \<open>PAC_Checker_LLVM\<close> synthesis.\<close>

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

text \<open>Fold equations turning \<open>(=)\<close>-tests on \<open>ordered\<close> into the discriminators,
  applied in the synthesis unfoldings.\<close>

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


section \<open>Synthesis of the Shared Polynomial Operations\<close>

sepref_def perfect_shared_var_order_s_impl
  is \<open>uncurry2 perfect_shared_var_order_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a (unat_assn' TYPE(64))\<^sup>k *\<^sub>a (unat_assn' TYPE(64))\<^sup>k \<rightarrow>\<^sub>a ordered_assn\<close>
  unfolding perfect_shared_var_order_s_def perfectly_shared_strings_equal_l_def
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    var_order_rel''
  by sepref

lemmas [sepref_fr_rules] = perfect_shared_var_order_s_impl.refine

text \<open>The walk destroys its lists (\<open>tl\<close> on open lists is destructive), so the keep-mode
  signature copies both monomials at entry - the \<open>add_poly_keep\<close> pattern of the
  \<open>PAC_Checker_LLVM\<close> synthesis.\<close>

lemma perfect_shared_term_order_rel_s_alt_def:
  \<open>perfect_shared_term_order_rel_s \<V> xs ys  = do {
    (b, _, _) \<leftarrow> WHILE\<^sub>T (\<lambda>(b, xs, ys). b = UNKNOWN)
    (\<lambda>(b, xs, ys). do {
       if xs = [] \<and> ys = [] then RETURN (EQUAL, xs, ys)
       else if xs = [] then RETURN (LESS, xs, ys)
       else if ys = [] then RETURN (GREATER, xs, ys)
       else do {
         ASSERT(xs \<noteq> [] \<and> ys \<noteq> []);
         (x, xs) \<leftarrow> mop_list_pop_front xs;
         (y, ys) \<leftarrow> mop_list_pop_front ys;
         eq \<leftarrow> perfect_shared_var_order_s \<V> x y;
         if eq = EQUAL then RETURN (b, xs, ys)
         else RETURN (eq, x # xs, y # ys)
      }
    }) (UNKNOWN, COPY xs, COPY ys);
    RETURN b
  }\<close>
proof -
  have 1: \<open>(\<lambda>(b, xs, ys). do {
       if xs = [] \<and> ys = [] then RETURN (EQUAL, xs, ys)
       else if xs = [] then RETURN (LESS, xs, ys)
       else if ys = [] then RETURN (GREATER, xs, ys)
       else do {
         ASSERT(xs \<noteq> [] \<and> ys \<noteq> []);
         (x, xs) \<leftarrow> mop_list_pop_front xs;
         (y, ys) \<leftarrow> mop_list_pop_front ys;
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
      (auto simp: mop_list_pop_front_def pw_eq_iff refine_pw_simps
        split: prod.splits list.splits)
  show ?thesis
    unfolding perfect_shared_term_order_rel_s_def COPY_def 1 by auto
qed

sepref_def perfect_shared_term_order_rel_s_impl
  is \<open>uncurry2 perfect_shared_term_order_rel_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a monom_s_assn\<^sup>k *\<^sub>a monom_s_assn\<^sup>k \<rightarrow>\<^sub>a ordered_assn\<close>
  supply [[goals_limit=1]]
  unfolding perfect_shared_term_order_rel_s_alt_def
    conv_to_is_Nil fold_is_Nil_is_empty fold_ordered_discriminators
  by sepref

lemmas [sepref_fr_rules] = perfect_shared_term_order_rel_s_impl.refine

subsection \<open>Addition\<close>

text \<open>Pop-front form of \<open>add_poly_l_s\<close>: the only head access available at
  \<open>poly_s_assn\<close> is \<open>mop_list_pop_front\<close> (ownership transfer). The implementation is
  destructive in both polynomials; all call sites pass owned polynomials.\<close>

lemma add_poly_l_s_alt_def:
  \<open>add_poly_l_s \<D> = REC\<^sub>T
  (\<lambda>add_poly_l (p, q).
     if q = [] then RETURN p
     else if p = [] then RETURN q
     else do {
       ((xs, n), p') \<leftarrow> mop_list_pop_front p;
       ((ys, m), q') \<leftarrow> mop_list_pop_front q;
       comp \<leftarrow> perfect_shared_term_order_rel_s \<D> xs ys;
       if comp = EQUAL then
         (if n + m = 0 then add_poly_l (p', q')
          else do {
            pq \<leftarrow> add_poly_l (p', q');
            RETURN ((xs, n + m) # pq)
          })
       else if comp = LESS
       then do {
         pq \<leftarrow> add_poly_l (p', (ys, m) # q');
         RETURN ((xs, n) # pq)
       }
       else do {
         pq \<leftarrow> add_poly_l ((xs, n) # p', q');
         RETURN ((ys, m) # pq)
       }
     })\<close>
  unfolding add_poly_l_s_def
  apply (rule arg_cong[where f = \<open>REC\<^sub>T\<close>])
  apply (intro ext)
  subgoal for f x
    apply (cases x)
    subgoal for p q
      by (cases p; cases q)
        (auto simp: mop_list_pop_front_def pw_eq_iff refine_pw_simps
          split: prod.splits)
    done
  done

sepref_def add_poly_l_prep_impl
  is \<open>uncurry add_poly_l_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a (poly_s_assn \<times>\<^sub>a poly_s_assn)\<^sup>d \<rightarrow>\<^sub>a poly_s_assn\<close>
  supply [[goals_limit=1]]
  unfolding add_poly_l_s_alt_def
    conv_to_is_Nil fold_is_Nil_is_empty fold_ordered_discriminators
  by sepref

subsection \<open>Multiplication\<close>

text \<open>Pop-front form of the monomial product; the keep-mode signature is obtained by
  copying both monomials at entry.\<close>

lemma mult_monoms_s_alt_def:
  \<open>mult_monoms_s \<D> xs ys = do { xs \<leftarrow> RETURN (COPY xs); ys \<leftarrow> RETURN (COPY ys); REC\<^sub>T (\<lambda>f (xs, ys).
 do {
    if xs = [] then RETURN ys
    else if ys = [] then RETURN xs
    else do {
      ASSERT(xs \<noteq> [] \<and> ys \<noteq> []);
      (x, xs) \<leftarrow> mop_list_pop_front xs;
      (y, ys) \<leftarrow> mop_list_pop_front ys;
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
      (x, xs) \<leftarrow> mop_list_pop_front xs;
      (y, ys) \<leftarrow> mop_list_pop_front ys;
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
      (auto simp: mop_list_pop_front_def pw_eq_iff refine_pw_simps
        split: prod.splits list.splits)
  show ?thesis
    unfolding COPY_def nres_monad1 1 mult_monoms_s_def ..
qed

sepref_def mult_monoms_s_impl
  is \<open>uncurry2 mult_monoms_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a monom_s_assn\<^sup>k *\<^sub>a monom_s_assn\<^sup>k \<rightarrow>\<^sub>a monom_s_assn\<close>
  supply [[goals_limit=1]]
  unfolding mult_monoms_s_alt_def
    conv_to_is_Nil fold_is_Nil_is_empty fold_ordered_discriminators
  by sepref

lemmas [sepref_fr_rules] =
  mult_monoms_s_impl.refine

sepref_register mult_monoms_s mult_term_s

text \<open>The folds over polynomials are rephrased as pop-front recursions over a copy
  (there is no \<open>nfoldli\<close> rule at \<open>ol_assn\<close>), cf. \<open>sort_all_coeffs2\<close> in
  \<open>PAC_Checker_LLVM.PAC_Checker_Init\<close>.\<close>

lemma nfoldli_to_pop_RECT:
  fixes body :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'b nres\<close>
  shows \<open>nfoldli qs (\<lambda>_. True) body b = REC\<^sub>T (\<lambda>f (qs, b).
     if qs = [] then RETURN b
     else do {
       (x, qs) \<leftarrow> mop_list_pop_front qs;
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
    apply (simp add: mop_list_pop_front_def nfoldli_simps Cons.IH[symmetric]
      pw_eq_iff refine_pw_simps)
    done
qed

lemma mult_term_s_alt_def:
  \<open>mult_term_s = (\<lambda>\<V> qs (p, m) b. do {
     qs \<leftarrow> RETURN (COPY qs);
     REC\<^sub>T (\<lambda>f (qs, b).
       if qs = [] then RETURN b
       else do {
         ((q, n), qs) \<leftarrow> mop_list_pop_front qs;
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
      apply (auto simp: mop_list_pop_front_def pw_eq_iff refine_pw_simps
          intro!: ext split: prod.splits)
      apply blast
      by blast
    done
qed

sepref_def mult_term_s_impl
  is \<open>uncurry3 mult_term_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k *\<^sub>a mnml_s_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>d \<rightarrow>\<^sub>a poly_s_assn\<close>
  supply [[goals_limit=1]]
  unfolding mult_term_s_alt_def
    conv_to_is_Nil fold_is_Nil_is_empty
  by sepref

lemmas [sepref_fr_rules] =
  mult_term_s_impl.refine

lemma mult_poly_s_alt_def:
  \<open>mult_poly_s \<V> p q = do {
     p \<leftarrow> RETURN (COPY p);
     REC\<^sub>T (\<lambda>f (p, b).
       if p = [] then RETURN b
       else do {
         (pm, p) \<leftarrow> mop_list_pop_front p;
         b \<leftarrow> mult_term_s \<V> q pm b;
         f (p, b)
       }) (p, op_ol_empty)}\<close>
  unfolding mult_poly_s_def COPY_def nres_monad1 op_ol_empty_def op_list_empty_def
  by (subst nfoldli_to_pop_RECT) (rule refl)

sepref_def mult_poly_s_impl
  is \<open>uncurry2 mult_poly_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a poly_s_assn\<close>
  supply [[goals_limit=1]]
  unfolding mult_poly_s_alt_def
    conv_to_is_Nil fold_is_Nil_is_empty
  by sepref

lemmas [sepref_fr_rules] =
  mult_poly_s_impl.refine

subsection \<open>Merging and Sorting\<close>

definition mergeR_vars :: \<open>(nat, string) shared_vars \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial nres\<close> where
  \<open>mergeR_vars \<V> = mergeR
   (\<lambda>xs ys. (\<forall>a\<in>set (fst xs). a \<in># dom_m (fst (snd \<V>))) \<and>  (\<forall>a\<in>set(fst ys). a \<in># dom_m (fst (snd \<V>))))
     (\<lambda>xs ys. do {a \<leftarrow> perfect_shared_term_order_rel_s \<V> (fst xs) (fst ys); RETURN (a \<noteq> GREATER)})\<close>

lemma mergeR_RECT:
  \<open>mergeR \<Phi> f xs ys = REC\<^sub>T (\<lambda>rec (xs, ys).
     if xs = [] then RETURN ys
     else if ys = [] then RETURN xs
     else do {
       (x, xs) \<leftarrow> mop_list_pop_front xs;
       (y, ys) \<leftarrow> mop_list_pop_front ys;
       ASSERT (\<Phi> x y);
       b \<leftarrow> f x y;
       if b then do { zs \<leftarrow> rec (xs, y # ys); RETURN (x # zs) }
       else do { zs \<leftarrow> rec (x # xs, ys); RETURN (y # zs) }
     }) (xs, ys)\<close>
  apply (subst eq_commute)
  apply (induction \<Phi> f xs ys rule: mergeR.induct)
  subgoal premises p for \<Phi> f x xs y ys
    apply (subst RECT_unfold, refine_mono)
    using p
    by (auto simp: mop_list_pop_front_def pw_eq_iff refine_pw_simps)
  subgoal for \<Phi> f xs
    by (subst RECT_unfold, refine_mono) (cases xs; auto)
  subgoal
    by (subst RECT_unfold, refine_mono) auto
  done

lemma mergeR_vars_RECT:
  \<open>mergeR_vars \<V> xs ys = REC\<^sub>T (\<lambda>rec (xs, ys).
     if xs = [] then RETURN ys
     else if ys = [] then RETURN xs
     else do {
       ((xm, xc), xs) \<leftarrow> mop_list_pop_front xs;
       ((ym, yc), ys) \<leftarrow> mop_list_pop_front ys;
       ASSERT ((\<forall>a\<in>set xm. a \<in># dom_m (fst (snd \<V>))) \<and> (\<forall>a\<in>set ym. a \<in># dom_m (fst (snd \<V>))));
       a \<leftarrow> perfect_shared_term_order_rel_s \<V> xm ym;
       if a \<noteq> GREATER then do { zs \<leftarrow> rec (xs, (ym, yc) # ys); RETURN ((xm, xc) # zs) }
       else do { zs \<leftarrow> rec ((xm, xc) # xs, ys); RETURN ((ym, yc) # zs) }
     }) (xs, ys)\<close>
  unfolding mergeR_vars_def
  apply (subst mergeR_RECT)
  apply (rule arg_cong2[where f = \<open>REC\<^sub>T\<close>])
  subgoal
    apply (intro ext)
    subgoal for rec xsys
      by (cases xsys)
        (simp add: split_def nres_monad_laws cong: bind_cong if_cong)
    done
  subgoal by (rule refl)
  done

sepref_def mergeR_vars_impl
  is \<open>uncurry2 mergeR_vars\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>d *\<^sub>a poly_s_assn\<^sup>d \<rightarrow>\<^sub>a poly_s_assn\<close>
  supply [[goals_limit = 1]]
  unfolding mergeR_vars_RECT
    conv_to_is_Nil fold_is_Nil_is_empty fold_ordered_discriminators
  by sepref

lemmas [sepref_fr_rules] =
  mergeR_vars_impl.refine

text \<open>The alternating split at shared polynomials (instance of the generic
  \<open>alt_split\<close> synthesis, cf. \<open>poly_split_impl\<close> in \<open>PAC_Checker_LLVM\<close>).\<close>

sepref_def poly_s_split_impl is \<open>RETURN o alt_split\<close>
  :: \<open>poly_s_assn\<^sup>d \<rightarrow>\<^sub>a poly_s_assn \<times>\<^sub>a poly_s_assn\<close>
  unfolding alt_split_RECT_ol
  by sepref

lemmas [sepref_fr_rules] = poly_s_split_impl.refine

sepref_def monom_s_split_impl is \<open>RETURN o alt_split\<close>
  :: \<open>monom_s_assn\<^sup>d \<rightarrow>\<^sub>a monom_s_assn \<times>\<^sub>a monom_s_assn\<close>
  unfolding alt_split_RECT
  by sepref

lemmas [sepref_fr_rules] = monom_s_split_impl.refine

text \<open>\<open>REC\<^sub>T\<close> form of the monadic merge sort for the synthesis (clone of
  \<open>msort_alt_RECT\<close>).\<close>

lemma msort_altR_RECT:
  \<open>msort_altR \<Phi> f xs = REC\<^sub>T (\<lambda>rec xs.
     if xs = [] then RETURN xs
     else do {
       (x, xs') \<leftarrow> mop_list_pop_front xs;
       if xs' = [] then RETURN (x # xs')
       else do {
         (l, r) \<leftarrow> RETURN (alt_split (x # xs'));
         l \<leftarrow> rec l;
         r \<leftarrow> rec r;
         mergeR \<Phi> f l r
       }
     }) xs\<close>
  apply (subst eq_commute)
  apply (induction \<Phi> f xs rule: msort_altR.induct)
  subgoal by (subst RECT_unfold, refine_mono) auto
  subgoal by (subst RECT_unfold, refine_mono)
      (auto simp: mop_list_pop_front_def pw_eq_iff refine_pw_simps)
  subgoal by (subst RECT_unfold, refine_mono)
      (auto simp: mop_list_pop_front_def pw_eq_iff refine_pw_simps
        split: prod.splits)
  done

abbreviation msortR_vars where
  \<open>msortR_vars \<equiv> sort_poly_spec_s\<close>
lemmas msortR_vars_def = sort_poly_spec_s_def

sepref_register mergeR_vars msortR_vars

sepref_def msortR_vars_impl
  is \<open>uncurry msortR_vars\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>d \<rightarrow>\<^sub>a poly_s_assn\<close>
  supply [[goals_limit = 1]]
  unfolding msortR_vars_def msort_altR_RECT mergeR_vars_def[symmetric]
    conv_to_is_Nil fold_is_Nil_is_empty
  by sepref

lemmas [sepref_fr_rules] =
  msortR_vars_impl.refine

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
  p \<leftarrow> msortR_vars \<V> p;
  RETURN (merge_coeffs_s p)
  }\<close>

lemma normalize_poly_s_normalize_poly_s:
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(xs, xs') \<in> perfectly_shared_polynom \<V>\<close> and
    \<open>vars_llist xs' \<subseteq> set_mset \<D>\<V>\<close>
  shows \<open>normalize_poly_s \<V> xs \<le> \<Down> (perfectly_shared_polynom \<V>) (normalize_poly xs')\<close>
  unfolding normalize_poly_s_def normalize_poly_def
  by (refine_rcg sort_poly_spec_s_sort_poly_spec[unfolded msortR_vars_def[symmetric]] assms
    perfectly_shared_merge_coeffs_merge_coeffs)

definition check_linear_combi_l_s_dom_err :: \<open>sllist_polynomial \<Rightarrow> nat \<Rightarrow> string nres\<close> where
  \<open>check_linear_combi_l_s_dom_err p r = SPEC (\<lambda>_. True)\<close>

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
    subgoal using assms by (auto)
    subgoal using assms by (auto)
    subgoal using assms by (auto)
    subgoal using assms by auto
    subgoal by auto
    subgoal using assms by auto
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
    apply (solves auto) (*one goal with unifucation*)
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
                }})\<close>

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
      sort_poly_spec_s_sort_poly_spec merge_coeffs0_s_merge_coeffs0)
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
    subgoal by (clarsimp intro!: RETURN_RES_refine)
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

subsection \<open>List Reversal\<close>

text \<open>\<open>rev\<close> is needed by the import functions (accumulate-and-reverse walks).
  \<open>os_reverse\<close> relinks the spine only, so a single rule at \<open>ol_assn\<close> covers both the
  owning and (via @{thm ol_assn_pure_conv}) the pure-element open lists.\<close>

lemma list_assn_rev:
  \<open>\<upharpoonleft>(Proto_EOArray.list_assn B) (rev xs) (rev ys)
     = \<upharpoonleft>(Proto_EOArray.list_assn B) xs ys\<close>
proof (cases \<open>length xs = length ys\<close>)
  case True then show ?thesis
    by (induction xs ys rule: list_induct2)
      (auto simp: lo_extract_elem sep_algebra_simps sep_conj_aci)
next
  case False then show ?thesis
    by simp
qed

lemma ol_reverse_rule[vcg_rules]:
  \<open>llvm_htriple (ol_assn A xs p) (os_reverse p) (\<lambda>r. ol_assn A (rev xs) r)\<close>
  unfolding ol_assn_os_conv
  apply (rule htriple_pre_EXS)
  subgoal for xsi
    apply (rule htriple_pure_preI)
    apply vcg
    apply (auto simp: ENTAILS_def sep_algebra_simps pred_lift_extract_simps
      sep_conj_exists vcg_tag_defs)
    apply (auto simp: entails_def list_assn_rev
      intro!: exI[where x = \<open>rev xsi\<close>])
    done
  done

lemma ol_rev_hnr[sepref_fr_rules]:
  \<open>(os_reverse, RETURN o rev) \<in> (ol_assn A)\<^sup>d \<rightarrow>\<^sub>a ol_assn A\<close>
  apply sepref_to_hoare
  by vcg

lemma monom_s_rev_hnr[sepref_fr_rules]:
  \<open>(os_reverse, RETURN o rev) \<in> monom_s_assn\<^sup>d \<rightarrow>\<^sub>a monom_s_assn\<close>
  using ol_rev_hnr[where A = \<open>unat_assn' TYPE(64)\<close>]
  unfolding ol_assn_pure_conv[OF unat64_assn_pure] .

text \<open>The identification phase maps \<open>rev\<close> to the declared interface operation.\<close>

lemmas ol_op_rev_hnr[sepref_fr_rules] = ol_rev_hnr[folded op_list_rev_def]
lemmas monom_s_op_rev_hnr[sepref_fr_rules] = monom_s_rev_hnr[folded op_list_rev_def]

subsection \<open>Sorting the Variables of a Monomial\<close>

definition merge_coeff_s :: \<open>(nat,string)shared_vars \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list nres\<close> where
  \<open>merge_coeff_s \<V> xs = mergeR (\<lambda>a b. a \<in> set xs \<and> b \<in> set xs)
  (\<lambda>a b. do {
    x \<leftarrow> get_var_nameS \<V> a;
  y \<leftarrow> get_var_nameS \<V> b;
    RETURN(a = b \<or> var_order x y)
  })\<close>

lemma merge_coeff_s_RECT:
  \<open>merge_coeff_s \<V> zs xs ys = REC\<^sub>T (\<lambda>rec (xs, ys).
     if xs = [] then RETURN ys
     else if ys = [] then RETURN xs
     else do {
       (x, xs) \<leftarrow> mop_list_pop_front xs;
       (y, ys) \<leftarrow> mop_list_pop_front ys;
       ASSERT (x \<in> set zs \<and> y \<in> set zs);
       x' \<leftarrow> get_var_nameS \<V> x;
       y' \<leftarrow> get_var_nameS \<V> y;
       b \<leftarrow> RETURN (x = y \<or> var_order x' y');
       if b then do { rs \<leftarrow> rec (xs, y # ys); RETURN (x # rs) }
       else do { rs \<leftarrow> rec (x # xs, ys); RETURN (y # rs) }
     }) (xs, ys)\<close>
  unfolding merge_coeff_s_def
  apply (subst mergeR_RECT)
  apply (rule arg_cong2[where f = \<open>REC\<^sub>T\<close>])
  subgoal
    by (intro ext)
      (auto simp: mop_list_pop_front_def nres_monad_laws pw_eq_iff
        refine_pw_simps split: prod.splits if_splits)
  subgoal by (rule refl)
  done

sepref_register merge_coeff_s msort_coeff_s sort_all_coeffs_s

lemma var_order_is_less: \<open>var_order = ((<) :: char list \<Rightarrow> _)\<close>
  by (intro ext) (metis var_order_rel'' var_order_rel_var_order)

sepref_def merge_coeff_s_impl
  is \<open>uncurry3 merge_coeff_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a (monom_s_assn)\<^sup>k *\<^sub>a (monom_s_assn)\<^sup>d *\<^sub>a (monom_s_assn)\<^sup>d \<rightarrow>\<^sub>a monom_s_assn\<close>
  supply [[goals_limit=1]]
  unfolding merge_coeff_s_RECT var_order_is_less
    conv_to_is_Nil fold_is_Nil_is_empty
  by sepref

lemmas [sepref_fr_rules] = merge_coeff_s_impl.refine

lemma msort_coeff_s_RECT:
  \<open>msort_coeff_s \<V> xs = do {
     xsc \<leftarrow> RETURN (COPY xs);
     REC\<^sub>T (\<lambda>rec xsa.
       if xsa = [] then RETURN xsa
       else do {
         (x, xs') \<leftarrow> mop_list_pop_front xsa;
         if xs' = [] then RETURN (x # xs')
         else do {
           (l, r) \<leftarrow> RETURN (alt_split (x # xs'));
           l \<leftarrow> rec l;
           r \<leftarrow> rec r;
           merge_coeff_s \<V> xs l r
         }
       }) xsc}\<close>
  unfolding msort_coeff_s_def COPY_def nres_monad1
  apply (subst msort_altR_RECT)
  unfolding merge_coeff_s_def[symmetric]
  by (metis (no_types, lifting) ext nres_monad_laws(1))

sepref_def msort_coeff_s_impl
  is \<open>uncurry msort_coeff_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a (monom_s_assn)\<^sup>k \<rightarrow>\<^sub>a monom_s_assn\<close>
  supply [[goals_limit=1]]
  unfolding msort_coeff_s_RECT
    conv_to_is_Nil fold_is_Nil_is_empty
  by sepref

lemmas [sepref_fr_rules] = msort_coeff_s_impl.refine

lemma sort_all_coeffs_s_RECT_aux:
  \<open>set ys \<subseteq> set xs \<Longrightarrow>
   monadic_nfoldli ys (\<lambda>_. RETURN True)
     (\<lambda>(a, n) b. do {ASSERT((a,n)\<in>set xs); a \<leftarrow> msort_coeff_s \<V> a; RETURN ((a, n) # b)}) b
   = REC\<^sub>T (\<lambda>f (ys, b).
       if ys = [] then RETURN b
       else do {
         ((a, n), ys) \<leftarrow> mop_list_pop_front ys;
         a \<leftarrow> msort_coeff_s \<V> a;
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
    by (auto simp: x mop_list_pop_front_def Cons.IH[symmetric] pw_eq_iff
      refine_pw_simps)
qed

lemma sort_all_coeffs_s_RECT:
  \<open>sort_all_coeffs_s \<V> xs = REC\<^sub>T (\<lambda>f (ys, b).
       if ys = [] then RETURN b
       else do {
         ((a, n), ys) \<leftarrow> mop_list_pop_front ys;
         a \<leftarrow> msort_coeff_s \<V> a;
         f (ys, ((a, n) # b))
       }) (xs, op_ol_empty)\<close>
  unfolding sort_all_coeffs_s_def op_ol_empty_def op_list_empty_def
  by (rule sort_all_coeffs_s_RECT_aux) auto

sepref_def sort_all_coeffs_s'_impl
  is \<open>uncurry sort_all_coeffs_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>d \<rightarrow>\<^sub>a poly_s_assn\<close>
  supply [[goals_limit=1]]
  unfolding sort_all_coeffs_s_RECT
    conv_to_is_Nil fold_is_Nil_is_empty
  by sepref

lemmas [sepref_fr_rules] = sort_all_coeffs_s'_impl.refine

subsection \<open>Merging Equal Monomials\<close>

sepref_register merge_coeffs0_s merge_coeffs_s

lemma merge_coeffs0_s_RECT:
  \<open>(RETURN o merge_coeffs0_s) p = REC\<^sub>T (\<lambda>f p.
     if p = [] then RETURN p
     else do {
       ((xs, n), p') \<leftarrow> mop_list_pop_front p;
       if p' = [] then (if n = 0 then RETURN p' else RETURN ((xs, n) # p'))
       else do {
         ((ys, m), p'') \<leftarrow> mop_list_pop_front p';
         if xs = ys then
           (if n + m \<noteq> 0 then f ((xs, n + m) # p'') else f p'')
         else if n = 0 then f ((ys, m) # p'')
         else do { r \<leftarrow> f ((ys, m) # p''); RETURN ((xs, n) # r) }
       }
     }) p\<close>
  apply (subst eq_commute)
  apply (induction p rule: merge_coeffs0_s.induct)
  subgoal by (subst RECT_unfold, refine_mono) auto
  subgoal by (subst RECT_unfold, refine_mono)
      (auto simp: mop_list_pop_front_def pw_eq_iff refine_pw_simps)
  subgoal
    apply (subst RECT_unfold, refine_mono)
    by (auto simp: refine_pw_simps)
  done

sepref_def merge_coeffs0_s_impl
  is \<open>RETURN o merge_coeffs0_s\<close>
  :: \<open>poly_s_assn\<^sup>d \<rightarrow>\<^sub>a poly_s_assn\<close>
  supply [[goals_limit=1]]
  unfolding merge_coeffs0_s_RECT
    conv_to_is_Nil fold_is_Nil_is_empty
  by sepref

lemmas [sepref_fr_rules] = merge_coeffs0_s_impl.refine

sepref_register full_normalize_poly_s

sepref_def full_normalize_poly'_impl
  is \<open>uncurry full_normalize_poly_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>d \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding full_normalize_poly_s_def
  by sepref

lemmas [sepref_fr_rules] = full_normalize_poly'_impl.refine

subsection \<open>Weak Equality\<close>

lemma weak_equality_l_s_alt_def:
  \<open>weak_equality_l_s = RETURN oo (\<lambda>p q. p = q)\<close>
  unfolding weak_equality_l_s_def weak_equality_l_s_def by (auto intro!: ext)

text \<open>A bare top-level \<open>(=)\<close> cannot be identified by sepref (the operand interfaces
  are still schematic when the operator is processed); the polynomial equality walk
  \<^emph>\<open>is\<close> the implementation, so the rule is stated directly.\<close>

sepref_register weak_equality_l_s

lemma weak_equality_l_s_hnr[sepref_fr_rules]:
  \<open>(uncurry poly_s_eq_impl, uncurry weak_equality_l_s)
    \<in> poly_s_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  using poly_s_eq_hnr unfolding weak_equality_l_s_alt_def .

abbreviation weak_equality_l_s_impl where
  \<open>weak_equality_l_s_impl \<equiv> poly_s_eq_impl\<close>

section \<open>The Map of Shared Polynomials\<close>

text \<open>The polynomial store maps 64-bit ids to \<^emph>\<open>shared\<close> polynomials: the pam instance
  of \<open>Polys_Assn\<close> with \<open>poly_s_assn\<close> values (\<open>vfree = poly_s_free\<close>,
  \<open>vcopy = poly_s_copy_impl\<close> \<comment> \<open>the-lookup returns a fresh copy\<close>).\<close>

abbreviation polys_s_assn where
  \<open>polys_s_assn \<equiv> pam_fmap_assn (mk_assn poly_s_assn)\<close>

lemmas polys_s_the_lookup_hnr[sepref_fr_rules] =
  pam_the_lookup_hnr[where V = \<open>mk_assn poly_s_assn\<close>, unfolded sel_mk_assn',
    OF poly_s_copy_rule, FCOMP mop_the_lookup_glue, folded pam_fmap_assn_def]

lemmas polys_s_the_lookup_op_hnr[sepref_fr_rules] =
  pam_the_lookup_hnr[where V = \<open>mk_assn poly_s_assn\<close>, unfolded sel_mk_assn',
    OF poly_s_copy_rule, FCOMP op_the_lookup_glue, folded pam_fmap_assn_def]

lemma polys_s_assn_free[sepref_frame_free_rules]:
  \<open>MK_FREE polys_s_assn (pam_free_impl poly_s_free)\<close>
  by (rule pam_fmap_assn_free[OF mk_free_mk_assn[OF poly_s_assn_free]])

subsection \<open>First-order code instances of the bucket walks\<close>

text \<open>The \<open>pam_bucket_\<dots>_impl\<close> walks are higher-order in \<open>vfree\<close>/\<open>vcopy\<close> and thus have
  no code equation of their own; every value instance needs its own first-order
  \<open>[llvm_code]\<close> definition plus a \<open>[llvm_pre_simp]\<close> fold, cf. \<^file>\<open>../PAC_Checker/Polys_Assn.thy\<close>
  (there for \<open>poly_free\<close>/\<open>poly_copy_impl\<close>). Same instances here for the \<^emph>\<open>shared\<close>
  store (\<open>poly_s_free\<close>/\<open>poly_s_copy_impl\<close>) \<emdash> without them the export of
  \<open>run_shared_checker\<close> fails with \<open>No code equation: pam_bucket_update_impl\<close>.\<close>

definition \<open>poly_s_bucket_update \<equiv> pam_bucket_update_impl poly_s_free\<close>

lemma poly_s_bucket_update_simps[llvm_code]:
  \<open>poly_s_bucket_update k v p = (if p = null then os_prepend (k, v) null
     else do\<^sub>M {
       n \<leftarrow> ll_load p;
       eq \<leftarrow> ll_icmp_eq (fst (node.val n)) k;
       if to_bool eq then do\<^sub>M {
                poly_s_free (snd (node.val n));
                ll_store (Node (k, v) (node.next n)) p;
                return\<^sub>M p
              }
       else do\<^sub>M {
        q \<leftarrow> poly_s_bucket_update k v (node.next n);
        ll_store (Node (node.val n) q) p;
        return\<^sub>M p
         }
     })\<close>
  unfolding poly_s_bucket_update_def
  by (rule pam_bucket_update_impl.simps)

lemmas [llvm_pre_simp] = poly_s_bucket_update_def[symmetric]

definition \<open>poly_s_bucket_delete \<equiv> pam_bucket_delete_impl poly_s_free\<close>

lemma poly_s_bucket_delete_simps[llvm_code]:
  \<open>poly_s_bucket_delete k p = (if p = null then Mreturn null
    else doM {
      n \<leftarrow> ll_load p;
      q \<leftarrow> poly_s_bucket_delete k (node.next n);
      eq \<leftarrow> ll_icmp_eq (fst (node.val n)) k;
      if to_bool eq then do\<^sub>M {
          poly_s_free (snd (node.val n));
          ll_free p;
          return\<^sub>M q
        }
      else do\<^sub>M {
      ll_store (Node (node.val n) q) p;
      return\<^sub>M p
      }
    })\<close>
  unfolding poly_s_bucket_delete_def
  using pam_bucket_delete_impl.simps by blast

lemmas [llvm_pre_simp] = poly_s_bucket_delete_def[symmetric]

definition \<open>poly_s_bucket_lookup \<equiv> pam_bucket_lookup_impl poly_s_copy_impl\<close>

lemma poly_s_bucket_lookup_simps[llvm_code]:
  \<open>poly_s_bucket_lookup k p = (if p = null then Mreturn (0, init)
    else do\<^sub>M {
      n \<leftarrow> ll_load p;
      eq \<leftarrow> ll_icmp_eq (fst (node.val n)) k;
      if to_bool eq then do\<^sub>M {
        v' \<leftarrow> poly_s_copy_impl (snd (node.val n));
        return\<^sub>M (1, v')
      }
      else poly_s_bucket_lookup k (node.next n)
    })\<close>
  unfolding poly_s_bucket_lookup_def
  by (rule pam_bucket_lookup_impl.simps)

lemmas [llvm_pre_simp] = poly_s_bucket_lookup_def[symmetric]

definition \<open>poly_s_bucket_free \<equiv> pam_bucket_free_impl poly_s_free\<close>

lemma poly_s_bucket_free_simps[llvm_code]:
  \<open>poly_s_bucket_free p = (if p = null then Mreturn () else do\<^sub>M {
      n \<leftarrow> ll_load p;
      pam_entry_free_impl poly_s_free (node.val n);
      ll_free p;
      poly_s_bucket_free (node.next n)
    })\<close>
  unfolding poly_s_bucket_free_def pam_bucket_free_impl_def
  by (rule ol_delete.simps)

lemmas [llvm_pre_simp] = poly_s_bucket_free_def[symmetric]

section \<open>Importing Polynomials into the Shared Store\<close>

text \<open>The import walks of \<open>LPAC_Perfectly_Shared\<close> read their input with \<open>hd\<close>/\<open>tl\<close>;
  the synthesized forms pop from a copy instead. \<open>import_monomS\<close>/\<open>import_polyS\<close> keep
  the unconsumed remainder in their state on allocation failure, which a pop-based
  walk cannot reproduce; the two-variants below drop it (the remainder is dead at
  loop exit), a plain refinement instead of an equality.\<close>

sepref_register import_monom_no_newS import_poly_no_newS import_monomS import_polyS
  import_variablesS check_linear_combi_l_pre_err normalize_poly_sharedS

lemma import_monom_no_newS_alt_def:
  \<open>import_monom_no_newS \<A> xs0 = do {
     xs \<leftarrow> RETURN (COPY xs0);
     (new, _, ys) \<leftarrow> WHILE\<^sub>T (\<lambda>(new, xs, _). \<not>new \<and> xs \<noteq> [])
       (\<lambda>(_, xs, ys). do {
          ASSERT (xs \<noteq> []);
          (x, xs) \<leftarrow> mop_list_pop_front xs;
          b \<leftarrow> is_new_variableS x \<A>;
          if b then RETURN (True, xs, ys)
          else do { i \<leftarrow> get_var_posS \<A> x; RETURN (False, xs, i # ys) }
       }) (False, xs, []);
     RETURN (new, rev ys)
  }\<close>
proof -
  have B: \<open>(\<lambda>(_, xs, ys). do {
          ASSERT (xs \<noteq> []);
          (x, xs) \<leftarrow> mop_list_pop_front xs;
          b \<leftarrow> is_new_variableS x \<A>;
          if b then RETURN (True, xs, ys)
          else do { i \<leftarrow> get_var_posS \<A> x; RETURN (False, xs, i # ys) }
       }) = (\<lambda>(_, xs, ys). do {
      ASSERT(xs \<noteq> []);
      let x = hd xs;
      b \<leftarrow> is_new_variableS x \<A>;
      if b
      then RETURN (True, tl xs, ys)
      else do {
        x \<leftarrow> get_var_posS \<A> x;
        RETURN (False, tl xs, x # ys)
       }
    })\<close>
    apply (intro ext)
    apply (auto simp: mop_list_pop_front_def pw_eq_iff refine_pw_simps)
    apply (meson pw_bind_nofail)
    apply (meson pw_bind_nofail)
    apply (smt (verit, best) pw_bind_nofail)
    apply (meson pw_bind_inres)
    apply (meson pw_bind_inres)
    sorry
  then show ?thesis
    unfolding import_monom_no_newS_def COPY_def nres_monad1 B
    by auto
qed

sepref_def import_monom_no_newS_impl
  is \<open>uncurry import_monom_no_newS\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a monom_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn \<times>\<^sub>a monom_s_assn\<close>
  supply [[goals_limit=1]]
  unfolding import_monom_no_newS_alt_def
    conv_to_is_Nil fold_is_Nil_is_empty
  by sepref

lemmas [sepref_fr_rules] = import_monom_no_newS_impl.refine

lemma import_poly_no_newS_alt_def:
  \<open>import_poly_no_newS \<A> xs0 = do {
     xs \<leftarrow> RETURN (COPY xs0);
     (new, _, ys) \<leftarrow> WHILE\<^sub>T (\<lambda>(new, xs, _). \<not>new \<and> xs \<noteq> [])
       (\<lambda>(_, xs, ys). do {
          ASSERT (xs \<noteq> []);
          ((x, n), xs) \<leftarrow> mop_list_pop_front xs;
          (b, x) \<leftarrow> import_monom_no_newS \<A> x;
          if b then RETURN (True, xs, ys)
          else RETURN (False, xs, (x, n) # ys)
       }) (False, xs, op_ol_empty);
     RETURN (new, rev ys)
  }\<close>
proof -
  have B: \<open>(\<lambda>(_, xs, ys). do {
          ASSERT (xs \<noteq> []);
          ((x, n), xs) \<leftarrow> mop_list_pop_front xs;
          (b, x) \<leftarrow> import_monom_no_newS \<A> x;
          if b then RETURN (True, xs, ys)
          else RETURN (False, xs, (x, n) # ys)
       }) = (\<lambda>(_, xs, ys). do {
      ASSERT(xs \<noteq> []);
      let (x, n) = hd xs;
      (b, x) \<leftarrow> import_monom_no_newS \<A> x;
      if b
      then RETURN (True, tl xs, ys)
      else do {
        RETURN (False, tl xs, (x, n) # ys)
       }
    })\<close>
    by (intro ext)
      (auto simp: mop_list_pop_front_def pw_eq_iff refine_pw_simps
        split: prod.splits)
  show ?thesis
    unfolding import_poly_no_newS_def COPY_def nres_monad1 B
      op_ol_empty_def op_list_empty_def
    by auto
qed

sepref_def import_poly_no_newS_impl
  is \<open>uncurry (import_poly_no_newS :: (nat,string)shared_vars \<Rightarrow> llist_polynomial \<Rightarrow>( bool \<times> sllist_polynomial) nres)\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn \<times>\<^sub>a poly_s_assn\<close>
  supply [[goals_limit=1]]
  unfolding import_poly_no_newS_alt_def
    conv_to_is_Nil fold_is_Nil_is_empty
  by sepref

lemmas [sepref_fr_rules] =
  import_poly_no_newS_impl.refine

subsection \<open>Imports That Grow the Store\<close>

definition import_monomS2
  :: \<open>(nat, string) shared_vars \<Rightarrow> string list \<Rightarrow> (memory_allocation \<times> nat list \<times> (nat, string) shared_vars) nres\<close>
where
  \<open>import_monomS2 \<A> xs0 = do {
     xs \<leftarrow> RETURN (COPY xs0);
     (mem, _, ys, \<A>) \<leftarrow> WHILE\<^sub>T (\<lambda>(mem, xs, _, _). \<not>alloc_failed mem \<and> xs \<noteq> [])
       (\<lambda>(_, xs, ys, \<A>). do {
          ASSERT (xs \<noteq> []);
          (x, xs) \<leftarrow> mop_list_pop_front xs;
          b \<leftarrow> is_new_variableS x \<A>;
          if b then do {
            (mem, \<A>, i) \<leftarrow> import_variableS x \<A>;
            if alloc_failed mem
            then RETURN (mem, xs, ys, \<A>)
            else RETURN (mem, xs, i # ys, \<A>)
          }
          else do { i \<leftarrow> get_var_posS \<A> x; RETURN (Allocated, xs, i # ys, \<A>) }
       }) (Allocated, xs, [], \<A>);
     RETURN (mem, rev ys, \<A>)
  }\<close>

lemma import_monomS2_import_monomS:
  \<open>(uncurry import_monomS2, uncurry import_monomS)
    \<in> Id \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
proof -
  have H: \<open>import_monomS2 \<A> xs \<le> \<Down>Id (import_monomS \<A> xs)\<close> for \<A> xs
    unfolding import_monomS2_def import_monomS_def COPY_def nres_monad1
    apply (refine_rcg WHILET_refine[where
      R = \<open>{((m, xs, ys, \<A>), (m', xs', ys', \<A>')). m = m' \<and> ys = ys' \<and> \<A> = \<A>' \<and>
            (\<not>alloc_failed m \<longrightarrow> xs = xs')}\<close>])
    subgoal by auto
    subgoal by auto
    subgoal
      by (auto simp: mop_list_pop_front_def pw_le_iff refine_pw_simps
        split: prod.splits)
    subgoal
      sorry
    sorry
  show ?thesis
    by (intro frefI nres_relI) (use H in \<open>auto simp: uncurry_def\<close>)
qed

sepref_def import_monomS2_impl
  is \<open>uncurry import_monomS2\<close>
  :: \<open>shared_vars_assn\<^sup>d *\<^sub>a monom_assn\<^sup>k \<rightarrow>\<^sub>a memory_allocation_assn \<times>\<^sub>a monom_s_assn \<times>\<^sub>a shared_vars_assn\<close>
  supply [[goals_limit=1]]
  unfolding import_monomS2_def
    conv_to_is_Nil fold_is_Nil_is_empty
  by sepref

text \<open>The strings are consumed by \<open>import_variableS\<close> but kept by the enclosing walk,
  so the popped element is copied before the import.\<close>

lemma import_monomS_hnr[sepref_fr_rules]:
  \<open>(uncurry import_monomS2_impl, uncurry import_monomS)
    \<in> shared_vars_assn\<^sup>d *\<^sub>a monom_assn\<^sup>k \<rightarrow>\<^sub>a
      memory_allocation_assn \<times>\<^sub>a monom_s_assn \<times>\<^sub>a shared_vars_assn\<close>
  using import_monomS2_impl.refine[FCOMP import_monomS2_import_monomS]
  by simp

definition import_polyS2
  :: \<open>(nat, string) shared_vars \<Rightarrow> llist_polynomial \<Rightarrow> (memory_allocation \<times> sllist_polynomial \<times> (nat, string) shared_vars) nres\<close>
where
  \<open>import_polyS2 \<A> xs0 = do {
     xs \<leftarrow> RETURN (COPY xs0);
     (mem, _, ys, \<A>) \<leftarrow> WHILE\<^sub>T (\<lambda>(mem, xs, _, _). \<not>alloc_failed mem \<and> xs \<noteq> [])
       (\<lambda>(_, xs, ys, \<A>). do {
          ASSERT (xs \<noteq> []);
          ((x, n), xs) \<leftarrow> mop_list_pop_front xs;
          (mem, x, \<A>) \<leftarrow> import_monomS \<A> x;
          if alloc_failed mem
          then RETURN (mem, xs, ys, \<A>)
          else RETURN (mem, xs, (x, n) # ys, \<A>)
       }) (Allocated, xs, op_ol_empty, \<A>);
     RETURN (mem, rev ys, \<A>)
  }\<close>

lemma import_polyS2_import_polyS:
  \<open>(uncurry import_polyS2, uncurry import_polyS)
    \<in> Id \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
proof -
  have H: \<open>import_polyS2 \<A> xs \<le> \<Down>Id (import_polyS \<A> xs)\<close> for \<A> xs
    unfolding import_polyS2_def import_polyS_def COPY_def nres_monad1
      op_ol_empty_def op_list_empty_def
    apply (refine_rcg WHILET_refine[where
      R = \<open>{((m, xs, ys, \<A>), (m', xs', ys', \<A>')). m = m' \<and> ys = ys' \<and> \<A> = \<A>' \<and>
            (\<not>alloc_failed m \<longrightarrow> xs = xs')}\<close>])
    subgoal by auto
    subgoal by auto
    sorry
  show ?thesis
    by (intro frefI nres_relI) (use H in \<open>auto simp: uncurry_def\<close>)
qed

sepref_def import_polyS2_impl
  is \<open>uncurry import_polyS2\<close>
  :: \<open>shared_vars_assn\<^sup>d *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a memory_allocation_assn \<times>\<^sub>a poly_s_assn \<times>\<^sub>a shared_vars_assn\<close>
  supply [[goals_limit=1]]
  unfolding import_polyS2_def
    conv_to_is_Nil fold_is_Nil_is_empty
  by sepref

lemma import_polyS_hnr[sepref_fr_rules]:
  \<open>(uncurry import_polyS2_impl, uncurry import_polyS)
    \<in> shared_vars_assn\<^sup>d *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a
      memory_allocation_assn \<times>\<^sub>a poly_s_assn \<times>\<^sub>a shared_vars_assn\<close>
  using import_polyS2_impl.refine[FCOMP import_polyS2_import_polyS]
  by simp

lemma import_variablesS_alt_def:
  \<open>import_variablesS vs0 \<V> = do {
     vs \<leftarrow> RETURN (COPY vs0);
     (mem, \<V>, _) \<leftarrow> WHILE\<^sub>T (\<lambda>(mem, \<V>, vs). \<not>alloc_failed mem \<and> vs \<noteq> [])
       (\<lambda>(_, \<V>, vs). do {
          ASSERT (vs \<noteq> []);
          (v, vs) \<leftarrow> mop_list_pop_front vs;
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
  have B: \<open>(\<lambda>(_, \<V>, vs). do {
          ASSERT (vs \<noteq> []);
          (v, vs) \<leftarrow> mop_list_pop_front vs;
          a \<leftarrow> is_new_variableS v \<V>;
          if \<not>a then RETURN (Allocated, \<V>, vs)
          else do {
            (mem, \<V>, _) \<leftarrow> import_variableS v \<V>;
            RETURN (mem, \<V>, vs)
          }
       }) = (\<lambda>(_, \<V>, vs). do {
    ASSERT(vs \<noteq> []);
    let v = hd vs;
    a \<leftarrow> is_new_variableS v \<V>;
    if \<not>a then RETURN (Allocated ,\<V>, tl vs)
    else do {
      (mem, \<V>, _) \<leftarrow> import_variableS v \<V>;
      RETURN(mem, \<V>, tl vs)
    }
    })\<close>
    apply (intro ext)
    apply (auto simp: refine_pw_simps pw_eq_iff mop_list_pop_front_def)
    apply (meson pw_bind_nofail)
    apply (meson pw_bind_nofail)
    apply (smt (verit, del_insts) pw_bind_nofail)
    apply (meson pw_bind_inres)
    apply (meson pw_bind_inres)
    sorry
  show ?thesis
    unfolding import_variablesS_def COPY_def nres_monad1 B
    by auto
qed

sepref_def import_variablesS_impl
  is \<open>uncurry import_variablesS\<close>
  :: \<open>monom_assn\<^sup>k *\<^sub>a shared_vars_assn\<^sup>d \<rightarrow>\<^sub>a memory_allocation_assn \<times>\<^sub>a shared_vars_assn\<close>
  supply [[goals_limit=1]]
  unfolding import_variablesS_alt_def
    conv_to_is_Nil fold_is_Nil_is_empty
  by sepref

lemmas [sepref_fr_rules] = import_variablesS_impl.refine

section \<open>Error Messages\<close>

text \<open>Error-message texts are erased for the LLVM backend (\<open>raw_string_assn\<close>), cf.
  the \<open>PAC_Checker_LLVM\<close> synthesis; the \<open>check_linear_combi_l_pre_err\<close> rule is
  inherited from \<open>LPAC_Checker_Synthesis\<close>.\<close>

sepref_register check_linear_combi_l_s_dom_err check_linear_combi_l_s_mult_err
  check_extension_l_s_new_var_multiple_err check_extension_l_s_side_cond_err

lemma check_linear_combi_l_s_dom_err_hnr[sepref_fr_rules]:
  \<open>(uncurry (\<lambda>_ _. Mreturn 0), uncurry check_linear_combi_l_s_dom_err)
    \<in> poly_s_assn\<^sup>k *\<^sub>a (unat_assn' TYPE(64))\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
  unfolding check_linear_combi_l_s_dom_err_def
  apply sepref_to_hoare
  by (vcg; auto simp: status_pure_reassembly)

lemma check_linear_combi_l_s_mult_err_hnr[sepref_fr_rules]:
  \<open>(uncurry (\<lambda>_ _. Mreturn 0), uncurry check_linear_combi_l_s_mult_err)
    \<in> poly_s_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
  unfolding check_linear_combi_l_s_mult_err_def
  apply sepref_to_hoare
  by (vcg; auto simp: status_pure_reassembly)

lemma check_extension_l_s_new_var_multiple_err_hnr[sepref_fr_rules]:
  \<open>(uncurry (\<lambda>_ _. Mreturn 0), uncurry check_extension_l_s_new_var_multiple_err)
    \<in> strl_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
  unfolding check_extension_l_s_new_var_multiple_err_def
  apply sepref_to_hoare
  by (vcg; auto simp: status_pure_reassembly)

lemma check_extension_l_s_side_cond_err_hnr[sepref_fr_rules]:
  \<open>(uncurry3 (\<lambda>_ _ _ _. Mreturn 0), uncurry3 check_extension_l_s_side_cond_err)
    \<in> strl_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
  unfolding check_extension_l_s_side_cond_err_def
  apply sepref_to_hoare
  by (vcg; auto simp: status_pure_reassembly)

section \<open>Variable Membership Test\<close>

sepref_register vars_llist_in_s

definition vars_of_monom_in_s :: \<open>string list \<Rightarrow> (nat, string) shared_vars \<Rightarrow> bool nres\<close> where
  \<open>vars_of_monom_in_s m \<V> = REC\<^sub>T (\<lambda>g m.
     if m = [] then do { mop_free m; RETURN True }
     else do {
       (x, m) \<leftarrow> mop_list_pop_front m;
       b \<leftarrow> is_new_variableS x \<V>;
       if b then do { mop_free m; RETURN False } else g m
     }) m\<close>

lemma vars_of_monom_in_s_spec:
  \<open>vars_of_monom_in_s m \<V> = RETURN (set m \<subseteq> set_mset (dom_m (snd (snd \<V>))))\<close>
proof -
  obtain \<D> \<V>m \<A> where V: \<open>\<V> = (\<D>, \<V>m, \<A>)\<close> by (cases \<V>)
  show ?thesis
    unfolding vars_of_monom_in_s_def
  proof (induction m)
    case Nil
    show ?case by (subst RECT_unfold, refine_mono) (auto simp: mop_free_def)
  next
    case (Cons x m)
    show ?case
      apply (subst RECT_unfold, refine_mono)
      by (auto simp: mop_list_pop_front_def Cons.IH is_new_variableS_def V
        mop_free_def pw_eq_iff refine_pw_simps)
  qed
qed

sepref_register vars_of_monom_in_s

sepref_def vars_of_monom_in_s_impl
  is \<open>uncurry vars_of_monom_in_s\<close>
  :: \<open>monom_assn\<^sup>d *\<^sub>a shared_vars_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [[goals_limit=1]]
  unfolding vars_of_monom_in_s_def
    conv_to_is_Nil fold_is_Nil_is_empty
  by sepref

lemmas [sepref_fr_rules] = vars_of_monom_in_s_impl.refine

definition vars_of_poly_in_s :: \<open>llist_polynomial \<Rightarrow> (nat, string) shared_vars \<Rightarrow> bool nres\<close> where
  \<open>vars_of_poly_in_s p \<V> = REC\<^sub>T (\<lambda>f xs.
     if xs = [] then do { mop_free xs; RETURN True }
     else do {
       ((m, c), xs) \<leftarrow> mop_list_pop_front xs;
       b \<leftarrow> vars_of_monom_in_s m \<V>;
       if b then f xs else do { mop_free xs; RETURN False }
     }) p\<close>

lemma vars_of_poly_in_s_spec:
  \<open>vars_of_poly_in_s xs \<V> = RETURN (vars_llist xs \<subseteq> set_mset (dom_m (snd (snd \<V>))))\<close>
  unfolding vars_of_poly_in_s_def
proof (induction xs)
  case Nil
  show ?case
    by (subst RECT_unfold, refine_mono) (auto simp: vars_llist_def mop_free_def)
next
  case (Cons p xs)
  show ?case
    apply (subst RECT_unfold, refine_mono)
    by (auto simp: mop_list_pop_front_def vars_of_monom_in_s_spec Cons.IH
      vars_llist_def mop_free_def pw_eq_iff refine_pw_simps split: prod.splits)
qed

sepref_register vars_of_poly_in_s

sepref_def vars_of_poly_in_s_impl
  is \<open>uncurry vars_of_poly_in_s\<close>
  :: \<open>poly_assn\<^sup>d *\<^sub>a shared_vars_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [[goals_limit=1]]
  unfolding vars_of_poly_in_s_def
    conv_to_is_Nil fold_is_Nil_is_empty
  by sepref

lemmas [sepref_fr_rules] = vars_of_poly_in_s_impl.refine

lemma vars_llist_in_s_alt:
  \<open>(RETURN oo vars_llist_in_s) \<V> xs = do {
     xsc \<leftarrow> RETURN (COPY xs);
     vars_of_poly_in_s xsc \<V>
   }\<close>
  unfolding COPY_def nres_monad1 vars_of_poly_in_s_spec
  by (cases \<V>) (auto simp: vars_llist_in_s_def)

sepref_def vars_llist_in_s_impl
  is \<open>uncurry (RETURN oo vars_llist_in_s)\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [[goals_limit=1]]
  unfolding vars_llist_in_s_alt
  by sepref

lemmas [sepref_fr_rules] = vars_llist_in_s_impl.refine

section \<open>Normalization of Shared Polynomials\<close>

sepref_register mult_poly_s normalize_poly_s mult_poly_full_s add_poly_l_s

sepref_def normalize_poly_sharedS_impl
  is \<open>uncurry normalize_poly_sharedS\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_assn\<^sup>d \<rightarrow>\<^sub>a bool1_assn \<times>\<^sub>a poly_s_assn\<close>
  unfolding normalize_poly_sharedS_def
  by sepref

lemmas [sepref_fr_rules] = normalize_poly_sharedS_impl.refine

lemma merge_coeffs_s_RECT:
  \<open>(RETURN o merge_coeffs_s) p = REC\<^sub>T (\<lambda>f p.
     if p = [] then RETURN p
     else do {
       ((xs, n), p') \<leftarrow> mop_list_pop_front p;
       if p' = [] then RETURN ((xs, n) # p')
       else do {
         ((ys, m), p'') \<leftarrow> mop_list_pop_front p';
         if xs = ys then
           (if n + m \<noteq> 0 then f ((xs, n + m) # p'') else f p'')
         else do { r \<leftarrow> f ((ys, m) # p''); RETURN ((xs, n) # r) }
       }
     }) p\<close>
  apply (subst eq_commute)
  apply (induction p rule: merge_coeffs_s.induct)
  subgoal by (subst RECT_unfold, refine_mono) auto
  subgoal by (subst RECT_unfold, refine_mono)
      (auto simp: mop_list_pop_front_def pw_eq_iff refine_pw_simps)
  subgoal by (subst RECT_unfold, refine_mono)
      (auto simp: mop_list_pop_front_def pw_eq_iff refine_pw_simps)
  done

sepref_def merge_coeffs_s_impl
  is \<open>(RETURN o merge_coeffs_s)\<close>
  :: \<open>poly_s_assn\<^sup>d \<rightarrow>\<^sub>a poly_s_assn\<close>
  supply [[goals_limit=1]]
  unfolding merge_coeffs_s_RECT
    conv_to_is_Nil fold_is_Nil_is_empty
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
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding mult_poly_full_s_def
  by sepref

lemmas [sepref_fr_rules] = mult_poly_full_s_impl.refine
  add_poly_l_prep_impl.refine

section \<open>The Checker Functions\<close>

subsection \<open>Linear Combinations\<close>

text \<open>Pop-front form of the linear-combination walk; the error branch re-prepends the
  popped entry (abstractly \<open>hd xs # tl xs = xs\<close>), cf. \<open>linear_combi_l2\<close> in
  \<open>LPAC_Checker_Synthesis\<close>. Like there, the walk is INLINED into the check function
  below (a registered call strands the id phase on the owning result triple).\<close>

lemma linear_combi_l_prep_s_alt_def:
  \<open>linear_combi_l_prep_s i A \<V> xs = do {
  WHILE\<^sub>T
    (\<lambda>(p, xs, err). xs \<noteq> [] \<and> \<not>is_cfailed err)
    (\<lambda>(p, xs, _). do {
      ASSERT(xs \<noteq> []);
      ((q, j), xs) \<leftarrow> mop_list_pop_front xs;
      if (j \<notin># dom_m A \<or> \<not>(vars_llist_in_s \<V> q))
      then do {
        err \<leftarrow> check_linear_combi_l_s_dom_err p j;
        RETURN (p, (q, j) # xs, error_msg j err)
      } else do {
        ASSERT(fmlookup A j \<noteq> None);
        let r = the (fmlookup A j);
        if q = [([], 1)]
        then do {
          pq \<leftarrow> add_poly_l_s \<V> (p, r);
          RETURN (pq, xs, CSUCCESS)}
        else do {
          (no_new, q) \<leftarrow> normalize_poly_sharedS \<V> (q);
          q \<leftarrow> mult_poly_full_s \<V> q r;
          pq \<leftarrow> add_poly_l_s \<V> (p, q);
          RETURN (pq, xs, CSUCCESS)
        }
        }
        })
        (op_ol_empty, xs, CSUCCESS)
          }\<close>
proof -
  have B: \<open>(\<lambda>(p, xs, _). do {
      ASSERT(xs \<noteq> []);
      ((q, j), xs) \<leftarrow> mop_list_pop_front xs;
      if (j \<notin># dom_m A \<or> \<not>(vars_llist_in_s \<V> q))
      then do {
        err \<leftarrow> check_linear_combi_l_s_dom_err p j;
        RETURN (p, (q, j) # xs, error_msg j err)
      } else do {
        ASSERT(fmlookup A j \<noteq> None);
        let r = the (fmlookup A j);
        if q = [([], 1)]
        then do {
          pq \<leftarrow> add_poly_l_s \<V> (p, r);
          RETURN (pq, xs, CSUCCESS)}
        else do {
          (no_new, q) \<leftarrow> normalize_poly_sharedS \<V> (q);
          q \<leftarrow> mult_poly_full_s \<V> q r;
          pq \<leftarrow> add_poly_l_s \<V> (p, q);
          RETURN (pq, xs, CSUCCESS)
        }
        }
        }) = (\<lambda>(p, xs, _). do {
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
        })\<close>
    (* TODO: the pointwise proof \<open>by (intro ext) (auto simp: mop_list_pop_front_def
       pw_eq_iff refine_pw_simps split: prod.splits list.splits)\<close> explodes in
       batch mode; needs a structured bind_cong decomposition. *)
    sorry
  show ?thesis
    unfolding linear_combi_l_prep_s_def B op_ol_empty_def op_list_empty_def ..
qed

subsection \<open>Checking Linear Combinations\<close>

sepref_register
  check_linear_combi_l_s :: \<open>sllist_polynomial \<Rightarrow> (nat, sllist_polynomial) f_map
    \<Rightarrow> (nat, string) shared_vars \<Rightarrow> nat \<Rightarrow> (llist_polynomial \<times> nat) list
    \<Rightarrow> llist_polynomial \<Rightarrow> (string code_status \<times> sllist_polynomial) nres\<close>

sepref_def check_linear_combi_l_s_impl
  is \<open>uncurry5 check_linear_combi_l_s\<close>
  :: \<open>poly_s_assn\<^sup>k *\<^sub>a polys_s_assn\<^sup>k *\<^sub>a shared_vars_assn\<^sup>k *\<^sub>a (unat_assn' TYPE(64))\<^sup>k *\<^sub>a
  lincomb_assn\<^sup>d *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a status_assn raw_string_assn \<times>\<^sub>a poly_s_assn
  \<close>
  supply [[goals_limit=1]]
  unfolding check_linear_combi_l_s_def linear_combi_l_prep_s_alt_def
    fmlookup'_def[symmetric]
    conv_to_is_Nil fold_is_Nil_is_empty
  unfolding fold_ol_empty
  by sepref

lemmas [sepref_fr_rules] = check_linear_combi_l_s_impl.refine

subsection \<open>Checking Extensions\<close>

text \<open>Negation of a polynomial as an order-preserving structural recursion
  (\<open>map\<close> has no rule at owning lists).\<close>

definition uminus_poly_s :: \<open>sllist_polynomial \<Rightarrow> sllist_polynomial nres\<close> where
  \<open>uminus_poly_s = REC\<^sub>T (\<lambda>f p.
     if p = [] then RETURN p
     else do {
       ((a, b), p) \<leftarrow> mop_list_pop_front p;
       r \<leftarrow> f p;
       RETURN ((a, - b) # r)
     })\<close>

lemma uminus_poly_s_spec:
  \<open>uminus_poly_s p = RETURN (map (\<lambda>(a, b). (a, - b)) p)\<close>
  unfolding uminus_poly_s_def
proof (induction p)
  case Nil
  show ?case by (subst RECT_unfold, refine_mono) auto
next
  case (Cons x p)
  show ?case
    apply (subst RECT_unfold, refine_mono)
    by (auto simp: mop_list_pop_front_def Cons.IH pw_eq_iff refine_pw_simps
      split: prod.splits)
qed

sepref_register uminus_poly_s

sepref_def uminus_poly_s_impl
  is \<open>uminus_poly_s\<close>
  :: \<open>poly_s_assn\<^sup>d \<rightarrow>\<^sub>a poly_s_assn\<close>
  supply [[goals_limit=1]]
  unfolding uminus_poly_s_def
    conv_to_is_Nil fold_is_Nil_is_empty
  by sepref

lemmas [sepref_fr_rules] = uminus_poly_s_impl.refine

lemma check_extension_l2_s_alt_def:
  \<open>check_extension_l2_s spec A \<V> i v p = do {
  n \<leftarrow> is_new_variableS v \<V>;
  pre \<leftarrow> RETURN (i \<notin># dom_m A \<and> n);
  nonew \<leftarrow> RETURN (vars_llist_in_s \<V> p);
  (mem, p, \<V>) \<leftarrow> import_polyS \<V> p;
  pre \<leftarrow> RETURN (pre \<and> \<not>alloc_failed mem);
  if \<not>pre
  then do {
    c \<leftarrow> check_extension_l_dom_err i;
    RETURN (error_msg i c, op_ol_empty, \<V>, 0)
  } else do {
      if \<not>nonew
      then do {
        c \<leftarrow> check_extension_l_s_new_var_multiple_err v p;
        RETURN (error_msg i c, op_ol_empty, \<V>, 0)
      }
      else do {
        (mem', \<V>, v') \<leftarrow> import_variableS (COPY v) \<V>;
        if alloc_failed mem'
        then do {
          c \<leftarrow> check_extension_l_dom_err i;
          RETURN (error_msg i c, op_ol_empty, \<V>, 0)
        } else
        do {
         p2 \<leftarrow> mult_poly_full_s \<V> p p;
         p'' \<leftarrow> uminus_poly_s (COPY p);
         q \<leftarrow> add_poly_l_s \<V> (p2, p'');
         eq \<leftarrow> RETURN (q = []);
         if eq then do {
           RETURN (CSUCCESS, p, \<V>, v')
         } else do {
          c \<leftarrow> check_extension_l_s_side_cond_err v p q q;
          RETURN (error_msg i c, op_ol_empty, \<V>, v')
        }
      }
     }
  }
  }\<close>
proof -
  have [simp]: \<open>check_extension_l_s_side_cond_err v p q q' = SPEC (\<lambda>_. True)\<close>
    for v p q q'
    by (auto simp: check_extension_l_s_side_cond_err_def)
  show ?thesis
    unfolding check_extension_l2_s_def uminus_poly_s_spec COPY_def Let_def
      weak_equality_l_s_def op_ol_empty_def op_list_empty_def mop_free_def
    (* TODO: the pointwise proof \<open>by (auto simp: pw_eq_iff refine_pw_simps)\<close>
       explodes in batch mode; needs a structured bind_cong decomposition. *)
    sorry
qed

sepref_register
  check_extension_l2_s :: \<open>'a \<Rightarrow> (nat, 'b) f_map
    \<Rightarrow> (nat, string) shared_vars \<Rightarrow> nat \<Rightarrow> string \<Rightarrow> llist_polynomial
    \<Rightarrow> (string code_status \<times> sllist_polynomial \<times> (nat, string) shared_vars \<times> nat) nres\<close>

sepref_def check_extension_l_s_impl
  is \<open>uncurry5 check_extension_l2_s\<close>
    :: \<open>poly_s_assn\<^sup>k *\<^sub>a polys_s_assn\<^sup>k *\<^sub>a shared_vars_assn\<^sup>d *\<^sub>a (unat_assn' TYPE(64))\<^sup>k *\<^sub>a
    strl_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a status_assn raw_string_assn \<times>\<^sub>a poly_s_assn \<times>\<^sub>a shared_vars_assn \<times>\<^sub>a unat_assn' TYPE(64)
  \<close>
  supply [[goals_limit=1]]
  unfolding check_extension_l2_s_alt_def
    conv_to_is_Nil fold_is_Nil_is_empty
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

lemmas [sepref_fr_rules] = check_extension_l_s_impl.refine

subsection \<open>Checking Deletions\<close>

sepref_def check_del_l_s_impl
  is \<open>uncurry2 check_del_l\<close>
  :: \<open>poly_s_assn\<^sup>k *\<^sub>a polys_s_assn\<^sup>k *\<^sub>a (unat_assn' TYPE(64))\<^sup>k \<rightarrow>\<^sub>a status_assn raw_string_assn\<close>
  unfolding check_del_l_def
  by sepref

lemmas [sepref_fr_rules] = check_del_l_s_impl.refine

section \<open>The Checker Step\<close>

text \<open>Synthesis-level variant of \<open>PAC_checker_l_step_s\<close>: the \<open>case\<close> is replaced by
  discriminator tests plus the one-shot destructors of \<open>LPAC_Step_Assn\<close>, exactly as
  in \<open>PAC_checker_l_step2\<close> of \<open>LPAC_Checker_Synthesis\<close>.\<close>

definition PAC_checker_l_step_s2
  :: \<open>sllist_polynomial \<Rightarrow> string code_status \<times> (nat,string)shared_vars \<times> _ \<Rightarrow> (llist_polynomial, string, nat) pac_step \<Rightarrow> _\<close>
where
  \<open>PAC_checker_l_step_s2 = (\<lambda>spec (st', \<V>, A) st. do {
    ASSERT (\<not>is_cfailed st');
    if is_CL st
    then do {
      (lincomb, i, r\<^sub>0) \<leftarrow> mop_dest_CL st;
      r \<leftarrow> full_normalize_poly r\<^sub>0;
      (eq, r) \<leftarrow> check_linear_combi_l_s spec A \<V> i lincomb r;
      let _ = eq;
      if \<not>is_cfailed eq
      then RETURN (merge_cstatus st' eq, \<V>, fmupd i r A)
      else RETURN (eq, \<V>, A)
    }
    else if is_Del st
    then do {
      i \<leftarrow> mop_dest_Del st;
      eq \<leftarrow> check_del_l spec A i;
      let _ = eq;
      if \<not>is_cfailed eq
      then RETURN (merge_cstatus st' eq, \<V>, fmdrop i A)
      else RETURN (eq, \<V>, A)
    }
    else do {
      (i, v, r\<^sub>0) \<leftarrow> mop_dest_Extension st;
      r \<leftarrow> full_normalize_poly r\<^sub>0;
      (eq, r, \<V>, v') \<leftarrow> check_extension_l2_s spec A \<V> i v r;
      if \<not>is_cfailed eq
      then do {
        r \<leftarrow> add_poly_l_s \<V> ((([v'], -1)) # op_ol_empty, r);
        RETURN (st', \<V>, fmupd i r A)
      }
      else RETURN (eq, \<V>, A)
    }
  })\<close>

lemma PAC_checker_l_step_s2_PAC_checker_l_step_s:
  \<open>PAC_checker_l_step_s = PAC_checker_l_step_s2\<close>
  apply (intro ext)
  subgoal for spec stVA st
    by (cases st; cases stVA)
      (auto simp: PAC_checker_l_step_s_def PAC_checker_l_step_s2_def
        mop_dest_CL_def mop_dest_Extension_def mop_dest_Del_def
        op_ol_empty_def op_list_empty_def
        Let_def pw_eq_iff refine_pw_simps)
  done

definition PAC_checker_l_step_s'
  :: \<open>sllist_polynomial \<Rightarrow> string code_status \<Rightarrow> (nat,string)shared_vars
     \<Rightarrow> (nat, sllist_polynomial) fmap \<Rightarrow> (llist_polynomial, string, nat) pac_step \<Rightarrow> _\<close>
where
  \<open>PAC_checker_l_step_s' spec st' \<V> A st = PAC_checker_l_step_s spec (st', \<V>, A) st\<close>

sepref_register
  PAC_checker_l_step_s' :: \<open>sllist_polynomial \<Rightarrow> string code_status
    \<Rightarrow> (nat, string) shared_vars \<Rightarrow> (nat, sllist_polynomial) f_map
    \<Rightarrow> (llist_polynomial, string, nat) i_pac_step
    \<Rightarrow> (string code_status \<times> (nat, string) shared_vars \<times> (nat, sllist_polynomial) f_map) nres\<close>

sepref_def check_step_s_impl
  is \<open>uncurry4 PAC_checker_l_step_s'\<close>
  :: \<open>poly_s_assn\<^sup>k *\<^sub>a (status_assn raw_string_assn)\<^sup>d *\<^sub>a shared_vars_assn\<^sup>d *\<^sub>a polys_s_assn\<^sup>d
      *\<^sub>a (pac_step_assn poly_assn strl_assn)\<^sup>d \<rightarrow>\<^sub>a
         status_assn raw_string_assn \<times>\<^sub>a shared_vars_assn \<times>\<^sub>a polys_s_assn\<close>
  supply [[goals_limit=1]]
  unfolding PAC_checker_l_step_s'_def
  unfolding PAC_checker_l_step_s2_PAC_checker_l_step_s
    PAC_checker_l_step_s2_def
  unfolding Let_def
  by sepref

declare check_step_s_impl.refine[sepref_fr_rules]

section \<open>The Checker Loop\<close>

definition PAC_checker_l_s' where
  \<open>PAC_checker_l_s' p \<V> A status steps = PAC_checker_l_s p (\<V>, A) status steps\<close>

lemma PAC_checker_l_s_alt_def:
  \<open>PAC_checker_l_s p \<V>A status steps =
    (let (\<V>, A) = \<V>A in PAC_checker_l_s' p \<V> A status steps)\<close>
  unfolding PAC_checker_l_s'_def by auto

lemma PAC_checker_l_s_alt:
  \<open>PAC_checker_l_s spec A b st = do {
  (S, _) \<leftarrow> WHILE\<^sub>T
    (\<lambda>((b, A), n). \<not>is_cfailed b \<and> n \<noteq> [])
    (\<lambda>((bA), n). do {
      (hd, tl) \<leftarrow> mop_list_pop_front n;
      ASSERT(n \<noteq> []);
      S \<leftarrow> PAC_checker_l_step_s spec bA hd;
      RETURN (S, tl)
    })
    ((b, A), st);
  RETURN S
  }\<close>
proof -
  have H: \<open>(\<lambda>((bA), n). do {
      (hd, tl) \<leftarrow> mop_list_pop_front n;
      ASSERT(n \<noteq> []);
      S \<leftarrow> PAC_checker_l_step_s spec bA hd;
      RETURN (S, tl)
    }) = (\<lambda>((bA), n). do {
      ASSERT(n \<noteq> []);
      S \<leftarrow> PAC_checker_l_step_s spec bA (hd n);
      RETURN (S, tl n)
    })\<close>
    by (intro ext)
      (auto simp: mop_list_pop_front_def pw_eq_iff refine_pw_simps
        split: prod.splits)
  show ?thesis
    unfolding PAC_checker_l_s_def H
    by (rule refl)
qed

lemma PAC_checker_l_step_s_alt_def':
  \<open>PAC_checker_l_step_s spec bA st =
    (let (b, \<V>, A) = bA in PAC_checker_l_step_s' spec b \<V> A st)\<close>
  unfolding PAC_checker_l_step_s'_def by auto

sepref_def PAC_checker_l_s_impl
  is \<open>uncurry4 PAC_checker_l_s'\<close>
  :: \<open>poly_s_assn\<^sup>k *\<^sub>a shared_vars_assn\<^sup>d *\<^sub>a polys_s_assn\<^sup>d *\<^sub>a (status_assn raw_string_assn)\<^sup>d *\<^sub>a
       (ol_assn (pac_step_assn poly_assn strl_assn))\<^sup>d \<rightarrow>\<^sub>a
     status_assn raw_string_assn \<times>\<^sub>a shared_vars_assn \<times>\<^sub>a polys_s_assn\<close>
  supply [[goals_limit=1]]
  unfolding PAC_checker_l_s'_def PAC_checker_l_s_alt
    PAC_checker_l_step_s_alt_def'
    nres_bind_let_law[symmetric]
    conv_to_is_Nil fold_is_Nil_is_empty
  apply (subst nres_bind_let_law)
  by sepref

declare PAC_checker_l_s_impl.refine[sepref_fr_rules]

sepref_register
  PAC_checker_l_s' :: \<open>sllist_polynomial \<Rightarrow> (nat, string) shared_vars
    \<Rightarrow> (nat, sllist_polynomial) f_map \<Rightarrow> string code_status
    \<Rightarrow> (llist_polynomial, string, nat) i_pac_step list
    \<Rightarrow> (string code_status \<times> (nat, string) shared_vars \<times> (nat, sllist_polynomial) f_map) nres\<close>

section \<open>Initialisation\<close>

definition memory_out_msg :: \<open>string\<close> where
  \<open>memory_out_msg = ''memory out''\<close>

sepref_register memory_out_msg

lemma [sepref_fr_rules]: \<open>(uncurry0 (Mreturn 0), uncurry0 (RETURN memory_out_msg)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
  unfolding memory_out_msg_def
  apply sepref_to_hoare
  by vcg

fun vars_llist_s2 :: \<open>_ \<Rightarrow> _ list\<close> where
  \<open>vars_llist_s2 [] = []\<close> |
  \<open>vars_llist_s2 ((a,_) # xs) = a @ vars_llist_s2 xs\<close>

lemma set_vars_llist_s2 [simp]: \<open>set (vars_llist_s2 b) = vars_llist b\<close>
  by (induction b)
    (auto simp: vars_llist_def)

definition (in -) remap_polys_l2_with_err_s :: \<open>llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> (nat, llist_polynomial) fmap \<Rightarrow> (nat, string) shared_vars \<Rightarrow>
   (string code_status \<times> (nat, string) shared_vars \<times> (nat, sllist_polynomial) fmap \<times> sllist_polynomial) nres\<close> where
  \<open>remap_polys_l2_with_err_s spec spec0 A (\<V> :: (nat, string) shared_vars) =  do{
   ASSERT(vars_llist spec \<subseteq> vars_llist spec0);
    n \<leftarrow> upper_bound_on_dom A;
   (mem, \<V>) \<leftarrow> import_variablesS (vars_llist_s2 spec0) \<V>;
   (mem', spec, \<V>) \<leftarrow> if \<not>alloc_failed mem then import_polyS \<V> spec else RETURN (mem, [], \<V>);
   failed \<leftarrow> RETURN (alloc_failed mem \<or> alloc_failed mem' \<or> n \<ge> 2^64);
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

text \<open>Importing all variables of a polynomial, monomial by monomial (the flat list
  \<open>vars_llist_s2 spec0\<close> of the abstract program has no owning-list producer).\<close>

definition import_poly_varsS
  :: \<open>(nat, string) shared_vars \<Rightarrow> llist_polynomial \<Rightarrow> (memory_allocation \<times> (nat, string) shared_vars) nres\<close>
where
  \<open>import_poly_varsS \<V> p = do {
     p \<leftarrow> RETURN (COPY p);
     (mem, \<V>, _) \<leftarrow> WHILE\<^sub>T (\<lambda>(mem, \<V>, p). \<not>alloc_failed mem \<and> p \<noteq> [])
       (\<lambda>(_, \<V>, p). do {
          ASSERT (p \<noteq> []);
          ((m, c), p) \<leftarrow> mop_list_pop_front p;
          (mem, \<V>) \<leftarrow> import_variablesS m \<V>;
          RETURN (mem, \<V>, p)
       }) (Allocated, \<V>, p);
     RETURN (mem, \<V>)
  }\<close>

sepref_register import_poly_varsS

sepref_def import_poly_varsS_impl
  is \<open>uncurry import_poly_varsS\<close>
  :: \<open>shared_vars_assn\<^sup>d *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a memory_allocation_assn \<times>\<^sub>a shared_vars_assn\<close>
  supply [[goals_limit=1]]
  unfolding import_poly_varsS_def
    conv_to_is_Nil fold_is_Nil_is_empty
  by sepref

lemmas [sepref_fr_rules] = import_poly_varsS_impl.refine

text \<open>The synthesized initialisation takes the input polynomials as an association
  list (no parser produces an \<open>fmap\<close>), mirroring \<open>remap_polys_l4\<close> in
  \<open>LPAC_Checker_Synthesis\<close>.\<close>

definition remap_polys_s4
  :: \<open>llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> (nat \<times> llist_polynomial) list \<Rightarrow> (nat, string) shared_vars \<Rightarrow>
     (string code_status \<times> (nat, string) shared_vars \<times> (nat, sllist_polynomial) fmap \<times> sllist_polynomial) nres\<close>
where
  \<open>remap_polys_s4 spec spec0 xs \<V> = do {
   (mem, \<V>) \<leftarrow> import_poly_varsS \<V> spec0;
   (mem', spec, \<V>) \<leftarrow> if \<not>alloc_failed mem then import_polyS \<V> spec else RETURN (mem, op_ol_empty, \<V>);
   failed \<leftarrow> RETURN (alloc_failed mem \<or> alloc_failed mem');
   if failed
   then do {
     c \<leftarrow> remap_polys_l_dom_err;
     RETURN (error_msg (0::nat) c, \<V>, fmempty, spec)
   }
   else do {
     (_, err, \<V>, A) \<leftarrow> WHILE\<^sub>T (\<lambda>(xs, err, \<V>, A). xs \<noteq> [] \<and> \<not>is_cfailed err)
       (\<lambda>(xs, err, \<V>, A). do {
          ASSERT (xs \<noteq> []);
          ((i, p\<^sub>0), xs) \<leftarrow> mop_list_pop_front xs;
          if i \<in># dom_m A then do {
            c \<leftarrow> remap_polys_l_dom_err;
            RETURN (xs, error_msg (0::nat) c, \<V>, A)
          } else do {
            (err', p, \<V>) \<leftarrow> import_polyS \<V> p\<^sub>0;
            if alloc_failed err' then do {
              c \<leftarrow> RETURN memory_out_msg;
              RETURN (xs, error_msg (0::nat) c, \<V>, A)
            }
            else do {
              p \<leftarrow> full_normalize_poly_s \<V> p;
              eq \<leftarrow> weak_equality_l_s p spec;
              RETURN (xs, (if eq then CFOUND else CSUCCESS), \<V>, fmupd i p A)
            }
          }
       }) (xs, CSUCCESS, \<V>, fmempty);
     RETURN (err, \<V>, A, spec)
  }}\<close>

sepref_register remap_polys_s4
  :: \<open>llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> (nat \<times> llist_polynomial) list
    \<Rightarrow> (nat, string) shared_vars
    \<Rightarrow> (string code_status \<times> (nat, string) shared_vars \<times> (nat, sllist_polynomial) f_map \<times> sllist_polynomial) nres\<close>

sepref_def remap_polys_s4_impl
  is \<open>uncurry3 remap_polys_s4\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a inputs_assn\<^sup>d *\<^sub>a shared_vars_assn\<^sup>d \<rightarrow>\<^sub>a
  status_assn raw_string_assn \<times>\<^sub>a shared_vars_assn \<times>\<^sub>a polys_s_assn \<times>\<^sub>a poly_s_assn\<close>
  supply [[goals_limit=1]]
  unfolding remap_polys_s4_def
    conv_to_is_Nil fold_is_Nil_is_empty
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

lemmas [sepref_fr_rules] = remap_polys_s4_impl.refine

definition full_checker_l_s2
  :: \<open>llist_polynomial \<Rightarrow> (nat, llist_polynomial) fmap \<Rightarrow> (_, string, nat) pac_step list \<Rightarrow>
    (string code_status \<times> _) nres\<close>
where
  \<open>full_checker_l_s2 spec A st = do {
    spec' \<leftarrow> full_normalize_poly spec;
    (b, \<V>, A, spec') \<leftarrow> remap_polys_l2_with_err_s spec' spec A ({#}, fmempty, fmempty);
    if is_cfailed b
    then RETURN (b, \<V>, A)
    else do {
      PAC_checker_l_s spec' (\<V>, A) b st
     }
   }\<close>

definition full_checker_l_s3
  :: \<open>llist_polynomial \<Rightarrow> (nat \<times> llist_polynomial) list \<Rightarrow> (_, string, nat) pac_step list \<Rightarrow>
    (string code_status \<times> _) nres\<close>
where
  \<open>full_checker_l_s3 spec xs st = do {
    spec' \<leftarrow> full_normalize_poly (COPY spec);
    (b, \<V>, A, spec'') \<leftarrow> remap_polys_s4 spec' spec xs empty_shared_vars;
    if is_cfailed b
    then RETURN (b, \<V>, A)
    else do {
      PAC_checker_l_s spec'' (\<V>, A) b st
     }
   }\<close>

text \<open>TODO: the refinement of the association-list initialisation towards
  \<open>full_checker_l_s2\<close> (clone of \<open>remap_polys_l4_remap_polys_l\<close> in
  \<open>LPAC_Checker_Synthesis\<close>) is still open.\<close>

lemma full_checker_l_s3_full_checker_l_s2:
  \<open>full_checker_l_s3 spec xs st \<le> \<Down>Id (full_checker_l_s2 spec (fmap_of_list xs) st)\<close>
  sorry

sepref_def full_checker_l_s3_impl
  is \<open>uncurry2 full_checker_l_s3\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a inputs_assn\<^sup>d *\<^sub>a (ol_assn (pac_step_assn poly_assn strl_assn))\<^sup>d \<rightarrow>\<^sub>a
  status_assn raw_string_assn \<times>\<^sub>a shared_vars_assn \<times>\<^sub>a polys_s_assn\<close>
  supply [[goals_limit=1]]
  unfolding full_checker_l_s3_def
    PAC_checker_l_s_alt_def
  by sepref

section \<open>Correctness theorem\<close>

context poly_embed
begin

text \<open>TODO (LLVM port): restate the composed step-list assertion over
  \<open>pac_step_assn\<close> (cf. \<open>LPAC_Step_Assn\<close>); the Imperative-HOL version was:\<close>
(* definition fully_epac_assn where
  \<open>fully_epac_assn = (list_assn
        (hr_comp (pac_step_rel_assn uint64_nat_assn poly_assn string_assn)
          (p2rel
            (\<langle>nat_rel, 
             fully_unsorted_poly_rel O
             mset_poly_rel, var_rel\<rangle>pac_step_rel_raw))))\<close> *)


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
  \<open>(uncurry2 full_checker_l_s2, uncurry2 full_checker_l_s) \<in> (Id \<times>\<^sub>r Id) \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
proof -
  have id: \<open>f=g \<Longrightarrow> f \<le>\<Down>Id g\<close> for f g
    by auto
  show ?thesis
    apply (intro frefI nres_relI)
    unfolding uncurry_def
    apply clarify
    unfolding full_checker_l_s2_def
      full_checker_l_s_def
    apply (refine_rcg remap_polys_l2_with_err_s_remap_polys_s_with_err)
    apply (rule id)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule id)
    subgoal by auto
    done
qed

text \<open>TODO (LLVM port): the composed input assertion was stated over the
  Imperative-HOL \<open>polys_assn_input\<close>; the association-list input of
  \<open>full_checker_l_s3\<close> needs a new statement.\<close>
(* lemma full_poly_input_assn_alt_def:
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
qed *)

(* lemma PAC_full_correctness: (\* \htmllink{PAC-full-correctness} *\)
 *   \<open>(uncurry2 full_checker_l_s2_impl,
 *     uncurry2 (\<lambda>spec A _. PAC_checker_specification spec A))
 *   \<in> full_poly_assn\<^sup>k *\<^sub>a full_poly_input_assn\<^sup>k *\<^sub>a fully_epac_assn\<^sup>k
 *     \<rightarrow>\<^sub>a hr_comp (status_assn raw_string_assn \<times>\<^sub>a shared_vars_assn \<times>\<^sub>a polys_s_assn)
 *        {((err, _), err', _). (err, err') \<in> code_status_status_rel}\<close>
 * proof -
 *   have 1: \<open>(uncurry2 full_checker_l_s2, uncurry2 (\<lambda>spec A _. PAC_checker_specification spec A))
 *     \<in> (\<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r int_rel\<rangle>list_rel O fully_unsorted_poly_rel O mset_poly_rel \<times>\<^sub>r
 *     (\<langle>nat_rel, Id\<rangle>fmap_rel O \<langle>nat_rel, fully_unsorted_poly_rel O mset_poly_rel\<rangle>fmap_rel) O
 *     polys_rel) \<times>\<^sub>r
 *     \<langle>p2rel
 *     (\<langle>nat_rel, fully_unsorted_poly_rel O mset_poly_rel,
 *     var_rel\<rangle>LPAC_Checker.pac_step_rel_raw)\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>(({((err, _), err', _).
 *     (err, err') \<in> Id} O
 *     {((b, A, st), b', A', st').
 *     (\<not> is_cfailed b \<longrightarrow> (A, A') \<in> {(x, y). y = set_mset x} \<and> (st, st') \<in> Id) \<and>
 *     (b, b') \<in> Id}) O
 *     {((err, \<V>, A), err', \<V>', A').
 *     ((err, \<V>, A), err', \<V>', A')
 *     \<in> code_status_status_rel \<times>\<^sub>r
 *     vars_rel2 err \<times>\<^sub>r
 *     {(xs, ys).
 *     \<not> is_cfailed err \<longrightarrow>
 *     (xs, ys) \<in> \<langle>nat_rel, sorted_poly_rel O mset_poly_rel\<rangle>fmap_rel \<and>
 *     (\<forall>i\<in>#dom_m xs. vars_llist (xs \<propto> i) \<subseteq> \<V>)}}) O
 *     {((st, G), st', G').
 *     (st, st') \<in> status_rel \<and> (st \<noteq> FAILED \<longrightarrow> (G, G') \<in> Id \<times>\<^sub>r polys_rel)}\<rangle>nres_rel\<close>
 *     using full_checker_l_s2_full_checker_l_s[
 *       FCOMP full_checker_l_s_full_checker_l_prep',
 *       FCOMP full_checker_l_prep_full_checker_l2',
 *       FCOMP full_checker_l_full_checker',
 *       FCOMP full_checker_spec',
 *       unfolded full_poly_assn_def[symmetric]
 *       full_poly_input_assn_def[symmetric]
 *       fully_epac_assn_def[symmetric]
 *       code_status_assn_def[symmetric]
 *       full_vars_assn_def[symmetric]
 *       polys_rel_full_polys_rel
 *       hr_comp_prod_conv
 *       full_polys_assn_def[symmetric]
 *       full_poly_input_assn_alt_def[symmetric]] by auto
 *   have 2: \<open>A \<subseteq> B \<Longrightarrow> \<langle>A\<rangle>nres_rel \<subseteq> \<langle>B\<rangle>nres_rel\<close> for A B
 *     by (auto simp: nres_rel_def conc_fun_R_mono conc_trans_additional(6))
 * 
 *   have 3: \<open>(uncurry2 full_checker_l_s2, uncurry2 (\<lambda>spec A _. PAC_checker_specification spec A))
 *     \<in> (\<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r int_rel\<rangle>list_rel O fully_unsorted_poly_rel O mset_poly_rel \<times>\<^sub>r
 *     (\<langle>nat_rel, Id\<rangle>fmap_rel O \<langle>nat_rel, fully_unsorted_poly_rel O mset_poly_rel\<rangle>fmap_rel) O
 *     polys_rel) \<times>\<^sub>r
 *     \<langle>p2rel
 *     (\<langle>nat_rel, fully_unsorted_poly_rel O mset_poly_rel,
 *     var_rel\<rangle>LPAC_Checker.pac_step_rel_raw)\<rangle>list_rel \<rightarrow>\<^sub>f
 *     \<langle>{((err, _), err', _). (err, err') \<in> code_status_status_rel}\<rangle>nres_rel\<close>
 *     apply (rule set_mp[OF _ 1])
 *     unfolding fref_param1[symmetric]
 *     apply (rule fun_rel_mono)
 *     apply auto[]
 *     apply (rule 2)
 *     apply auto
 *     done
 * 
 *   have 4: \<open>\<langle>nat_rel, Id\<rangle>fmap_rel = Id\<close>
 *     apply (auto simp: fmap_rel_def)
 *     by (metis (no_types, opaque_lifting) fmap_ext_fmdom fmlookup_dom_iff fset_eqI option.sel)
 *   have H: \<open>full_poly_assn = (hr_comp poly_assn
 *     (\<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r int_rel\<rangle>list_rel O fully_unsorted_poly_rel O mset_poly_rel))\<close>
 *     \<open>full_poly_input_assn = hr_comp polys_assn_input
 *    ((Id O \<langle>nat_rel, fully_unsorted_poly_rel O mset_poly_rel\<rangle>fmap_rel) O polys_rel)\<close>
 *     unfolding full_poly_assn_def fully_epac_assn_def full_poly_input_assn_def
 *       hr_comp_assoc O_assoc
 *     by auto
 *   show ?thesis
 *     using full_checker_l_s2_impl.refine[FCOMP 3]
 *     unfolding full_poly_assn_def[symmetric]
 *       full_poly_input_assn_def[symmetric]
 *       fully_epac_assn_def[symmetric]
 *       code_status_assn_def[symmetric]
 *       full_vars_assn_def[symmetric]
 *       polys_rel_full_polys_rel
 *       hr_comp_prod_conv
 *       full_polys_assn_def[symmetric]
 *       full_poly_input_assn_alt_def[symmetric]
 *       4 H[symmetric]
 *     by auto
 * qed *)

end
end
