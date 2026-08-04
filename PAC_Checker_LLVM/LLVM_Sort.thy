section \<open>Generic Merge Sort for Sepref\<close>
theory LLVM_Sort
  imports IICF_Copying_List
begin

subsection \<open>Merge Sort\<close>

text \<open>The previous merge sort implementation translates poorly to LLVM, so we reimplement
  merge sort, tailored to our custom IICF_Copying_List.\<close>

fun merge :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
  \<open>merge cmp (x#xs) (y#ys) =
     (if cmp x y then x # merge cmp xs (y#ys) else y # merge cmp (x#xs) ys)\<close>
| \<open>merge cmp xs [] = xs\<close>
| \<open>merge cmp [] ys = ys\<close>

lemma mset_merge [simp]:
  \<open>mset (merge cmp xs ys) = mset xs + mset ys\<close>
  by (induct cmp xs ys rule: merge.induct) (simp_all add: ac_simps)

lemma set_merge [simp]:
  \<open>set (merge cmp xs ys) = set xs \<union> set ys\<close>
  by (induct cmp xs ys rule: merge.induct) auto

lemma sorted_merge:
  \<open>transp f \<Longrightarrow> (\<And>x y. f x y \<or> f y x) \<Longrightarrow>
   sorted_wrt f (merge f xs ys) \<longleftrightarrow> sorted_wrt f xs \<and> sorted_wrt f ys\<close>
  apply (induct f xs ys rule: merge.induct)
  apply (auto simp add: ball_Un not_le less_le dest: transpD)
  apply blast
  apply (blast dest: transpD)
  done

fun msort :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
  \<open>msort f [] = []\<close>
| \<open>msort f [x] = [x]\<close>
| \<open>msort f xs = merge f (msort f (take (size xs div 2) xs))
                        (msort f (drop (size xs div 2) xs))\<close>

fun alt_split :: \<open>'a list \<Rightarrow> 'a list \<times> 'a list\<close> where
  \<open>alt_split [] = ([], [])\<close>
| \<open>alt_split (x # xs) = (case alt_split xs of (l, r) \<Rightarrow> (x # r, l))\<close>

lemma alt_split_mset[simp]:
  \<open>mset (fst (alt_split xs)) + mset (snd (alt_split xs)) = mset xs\<close>
  by (induction xs) (auto simp: ac_simps split: prod.splits)

lemma alt_split_len:
  \<open>length (fst (alt_split xs)) + length (snd (alt_split xs)) = length xs \<and>
   length (snd (alt_split xs)) \<le> length (fst (alt_split xs)) \<and>
   length (fst (alt_split xs)) \<le> Suc (length (snd (alt_split xs)))\<close>
  by (induction xs) (auto split: prod.splits)

lemma alt_split_len_eq:
  \<open>alt_split xs = (l, r) \<Longrightarrow>
     length l + length r = length xs \<and> length r \<le> length l \<and> length l \<le> Suc (length r)\<close>
  using alt_split_len[of xs] by auto

function msort_alt :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
  \<open>msort_alt f [] = []\<close>
| \<open>msort_alt f [x] = [x]\<close>
| \<open>msort_alt f (x # y # xs) =
     (case alt_split (x # y # xs) of (l, r) \<Rightarrow> merge f (msort_alt f l) (msort_alt f r))\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (length o snd)\<close>)
     (auto split: prod.splits dest!: alt_split_len_eq)

lemma msort_alt_mset[simp]: \<open>mset (msort_alt f xs) = mset xs\<close>
  apply (induction f xs rule: msort_alt.induct)
  subgoal by simp
  subgoal by simp
  subgoal for f x y xs
    by (auto split: prod.splits)
      (metis alt_split_mset fst_conv snd_conv union_assoc)
  done

lemma msort_alt_sorted:
  \<open>transp f \<Longrightarrow> (\<And>x y. f x y \<or> f y x) \<Longrightarrow> sorted_wrt f (msort_alt f xs)\<close>
  apply (induction f xs rule: msort_alt.induct)
  subgoal by simp
  subgoal by simp
  subgoal by (auto split: prod.splits simp: sorted_merge)
  done

subsubsection \<open>Synthesis\<close>

lemma merge_RECT:
  \<open>(RETURN oo merge f) xs ys = REC\<^sub>T (\<lambda>rec (xs, ys).
     if xs = [] then RETURN ys
     else if ys = [] then RETURN xs
     else doN {
       (x, xs) \<leftarrow> mop_list_pop_hd xs;
       (y, ys) \<leftarrow> mop_list_pop_hd ys;
       if f x y then doN { zs \<leftarrow> rec (xs, y # ys); RETURN (x # zs) }
       else doN { zs \<leftarrow> rec (x # xs, ys); RETURN (y # zs) }
     }) (xs, ys)\<close>
  apply (subst eq_commute)
  apply (induction f xs ys rule: merge.induct)
  subgoal by (subst RECT_unfold, refine_mono) (auto)
  subgoal by (subst RECT_unfold, refine_mono) (auto)
  subgoal by (subst RECT_unfold, refine_mono) (auto)
  done

lemma alt_split_RECT:
  \<open>(RETURN o alt_split) xs = REC\<^sub>T (\<lambda>rec xs.
     if xs = [] then RETURN ([], [])
     else doN {
       (x, xs) \<leftarrow> mop_list_pop_hd xs;
       (l, r) \<leftarrow> rec xs;
       RETURN (x # r, l)
     }) xs\<close>
  apply (subst eq_commute)
  apply (induction xs)
  subgoal by (subst RECT_unfold, refine_mono) auto
  subgoal by (subst RECT_unfold, refine_mono) (auto split: prod.splits)
  done

lemma alt_split_RECT_ol:
  \<open>(RETURN o alt_split) xs = REC\<^sub>T (\<lambda>rec xs.
     if xs = [] then RETURN (op_list_empty, op_list_empty)
     else doN {
       (x, xs) \<leftarrow> mop_list_pop_hd xs;
       (l, r) \<leftarrow> rec xs;
       RETURN (x # r, l)
     }) xs\<close>
  unfolding op_list_empty_def op_list_empty_def
  by (rule alt_split_RECT)

lemma msort_alt_RECT:
  \<open>(RETURN o msort_alt f) xs = REC\<^sub>T (\<lambda>rec xs.
     if xs = [] then RETURN xs
     else doN {
       (x, xs') \<leftarrow> mop_list_pop_hd xs;
       if xs' = [] then RETURN (x # xs')
       else doN {
         (l, r) \<leftarrow> RETURN (alt_split (x # xs'));
         l \<leftarrow> rec l;
         r \<leftarrow> rec r;
         RETURN (merge f l r)
       }
     }) xs\<close>
  apply (subst eq_commute)
  apply (induction f xs rule: msort_alt.induct)
  subgoal by (subst RECT_unfold, refine_mono) auto
  subgoal by (subst RECT_unfold, refine_mono) (auto)
  subgoal by (subst RECT_unfold, refine_mono) (auto split: prod.splits)
  done

sepref_register alt_split

section \<open>While-based sorting\<close>
definition mergew_body :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<times> 'a list \<times> 'a list \<Rightarrow>
  ('a list \<times> 'a list \<times> 'a list) nres\<close> where
  \<open>mergew_body cmp = (\<lambda>(r, xs, ys). doN {
        (x, xs) \<leftarrow> mop_list_pop_hd xs;
        (y, ys) \<leftarrow> mop_list_pop_hd ys;
        if cmp x y then
          RETURN (x # r, xs, y # ys)
        else
          RETURN (y # r, x # xs, ys)
      })\<close>

definition mergew_inner :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow>
  ('a list \<times> 'a list \<times> 'a list) nres\<close> where
  \<open>mergew_inner cmp xs\<^sub>0 ys\<^sub>0 \<equiv> WHILE\<^sub>T
      (\<lambda>(r, xs, ys). xs\<noteq>[] \<and> ys\<noteq>[])
      (mergew_body cmp) ([], xs\<^sub>0, ys\<^sub>0)\<close>

lemma WHILET_exit: \<open>\<not> c s \<Longrightarrow> WHILE\<^sub>T c f s = RETURN s\<close>
  by (subst WHILET_unfold) simp

text \<open>\<open>rev r @ ys\<close> expressed with pop/prepend only: concretely this is in-place
  reversal of \<open>r\<close> onto \<open>ys\<close>, so no dedicated \<open>op_list_rev\<close> implementation is needed.\<close>

definition rev_app_body :: \<open>'a list \<times> 'a list \<Rightarrow> ('a list \<times> 'a list) nres\<close> where
  \<open>rev_app_body = (\<lambda>(r, ys). doN {
      (x, r) \<leftarrow> mop_list_pop_hd r;
      RETURN (r, x # ys)
    })\<close>

definition rev_app :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> 'a list nres\<close> where
  \<open>rev_app r ys \<equiv> doN {
     (_, ys) \<leftarrow> WHILE\<^sub>T (\<lambda>(r, ys). r \<noteq> []) rev_app_body (r, ys);
     RETURN ys
   }\<close>

lemma rev_app_loop:
  \<open>WHILE\<^sub>T (\<lambda>(r, ys). r \<noteq> []) rev_app_body (r, ys) = RETURN ([], rev r @ ys)\<close>
  apply (induction r arbitrary: ys)
  subgoal by (simp add: WHILET_exit)
  subgoal by (subst WHILET_unfold) (auto simp: rev_app_body_def)
  done

lemma rev_app_correct: \<open>rev_app r ys = RETURN (rev r @ ys)\<close>
  unfolding rev_app_def by (simp add: rev_app_loop)

definition mergew :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list nres\<close> where
  \<open>mergew cmp xs ys \<equiv> doN {
    (r, xs, ys) \<leftarrow> mergew_inner cmp xs ys;
    if xs = [] then rev_app r ys
    else doN {
      ASSERT (ys = []);
      rev_app r xs
    }
  }\<close>

fun merge_pref :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<times> 'a list \<times> 'a list\<close> where
  \<open>merge_pref cmp (x#xs) (y#ys) =
     (if cmp x y then let (r, xs', ys') = merge_pref cmp xs (y#ys) in (x#r, xs', ys')
      else let (r, xs', ys') = merge_pref cmp (x#xs) ys in (y#r, xs', ys'))\<close>
| \<open>merge_pref cmp xs [] = ([], xs, [])\<close>
| \<open>merge_pref cmp [] ys = ([], [], ys)\<close>

lemma merge_pref_merge:
  \<open>case merge_pref cmp xs ys of (r, xs', ys') \<Rightarrow>
     r @ (if xs' = [] then ys' else xs') = merge cmp xs ys\<close>
  by (induction cmp xs ys rule: merge_pref.induct) (auto split: prod.splits)

lemma merge_pref_one_empty:
  \<open>case merge_pref cmp xs ys of (r, xs', ys') \<Rightarrow> xs' = [] \<or> ys' = []\<close>
  by (induction cmp xs ys rule: merge_pref.induct) (auto split: prod.splits)

lemma mergew_loop:
  \<open>WHILE\<^sub>T (\<lambda>(r, xs, ys). xs \<noteq> [] \<and> ys \<noteq> []) (mergew_body cmp) (r, xs, ys) =
     (let (s, xs', ys') = merge_pref cmp xs ys in RETURN (rev s @ r, xs', ys'))\<close>
  apply (induction cmp xs ys arbitrary: r rule: merge_pref.induct)
  subgoal
    apply (subst WHILET_unfold)
    apply (auto simp: mergew_body_def split: prod.splits)
    done
  subgoal by (simp add: WHILET_exit)
  subgoal by (simp add: WHILET_exit)
  done

lemma mergew_merge: \<open>mergew cmp xs ys = RETURN (merge cmp xs ys)\<close>
  unfolding mergew_def mergew_inner_def
  using merge_pref_merge[of cmp xs ys] merge_pref_one_empty[of cmp xs ys]
  by (auto simp: mergew_loop rev_app_correct split: prod.splits)

subsection \<open>Exploding into singleton runs\<close>

definition explode_body where
  \<open>explode_body = (\<lambda>(r, xs). doN {
      (x, xs) \<leftarrow> mop_list_pop_hd xs;
      RETURN ([x] # r, xs)
    })\<close>

definition explode :: \<open>'a list \<Rightarrow> 'a list list nres\<close> where
  \<open>explode xs \<equiv> doN{
    (r, _) \<leftarrow> WHILE\<^sub>T
    (\<lambda>(r, xs). xs \<noteq> [])
    explode_body ([], xs);
    RETURN r
  }\<close>

lemma explode_loop:
  \<open>WHILE\<^sub>T (\<lambda>(r, xs). xs \<noteq> []) explode_body (r, xs) =
     RETURN (rev (map (\<lambda>x. [x]) xs) @ r, [])\<close>
  apply (induction xs arbitrary: r)
  subgoal by (simp add: WHILET_exit)
  subgoal
    apply (subst WHILET_unfold)
    apply (auto simp: explode_body_def)
    done
  done

lemma explode_correct: \<open>explode xs = RETURN (rev (map (\<lambda>x. [x]) xs))\<close>
  unfolding explode_def
  by (simp add: explode_loop)

lemma concat_rev_singletons: \<open>concat (rev (map (\<lambda>x. [x]) xs)) = rev xs\<close>
  by (induction xs) auto

lemma mset_concat_rev[simp]: \<open>mset (concat (rev xss)) = mset (concat xss)\<close>
  by (induction xss) auto

lemma explode_spec:
  \<open>explode xs \<le> SPEC (\<lambda>rs.
     mset (concat rs) = mset xs \<and> (\<forall>r \<in> set rs. sorted_wrt cmp r))\<close>
  by (auto simp: explode_correct concat_rev_singletons)

subsection \<open>One bottom-up pass\<close>

definition pass_body where
  \<open>pass_body cmp = (\<lambda>(acc, rs). doN {
      (a, rs) \<leftarrow> mop_list_pop_hd rs;
      if rs = [] then RETURN (a # acc, rs)
      else doN {
        (b, rs) \<leftarrow> mop_list_pop_hd rs;
        m \<leftarrow> mergew cmp a b;
        RETURN (m # acc, rs)
      }
    })\<close>

definition pass :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list list \<Rightarrow> 'a list list nres\<close> where
  \<open>pass cmp rs \<equiv> doN {
     (acc, _) \<leftarrow> WHILE\<^sub>T (\<lambda>(acc, rs). rs \<noteq> []) (pass_body cmp) ([], rs);
     RETURN acc
   }\<close>

fun pass_f :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list list \<Rightarrow> 'a list list\<close> where
  \<open>pass_f cmp [] = []\<close>
| \<open>pass_f cmp [a] = [a]\<close>
| \<open>pass_f cmp (a # b # rs) = merge cmp a b # pass_f cmp rs\<close>

lemma pass_loop:
  \<open>WHILE\<^sub>T (\<lambda>(acc, rs). rs \<noteq> []) (pass_body cmp) (acc, rs) =
     RETURN (rev (pass_f cmp rs) @ acc, [])\<close>
  apply (induction cmp rs arbitrary: acc rule: pass_f.induct)
  subgoal by (simp add: WHILET_exit)
  subgoal
    apply (subst WHILET_unfold)
    apply (auto simp: pass_body_def WHILET_exit)
    done
  subgoal
    apply (subst WHILET_unfold)
    apply (auto simp: pass_body_def mergew_merge)
    done
  done

lemma pass_correct: \<open>pass cmp rs = RETURN (rev (pass_f cmp rs))\<close>
  unfolding pass_def by (simp add: pass_loop)

lemma mset_concat_pass_f:
  \<open>mset (concat (pass_f cmp rs)) = mset (concat rs)\<close>
  by (induction cmp rs rule: pass_f.induct) auto

lemma sorted_pass_f:
  \<open>transp cmp \<Longrightarrow> (\<And>x y. cmp x y \<or> cmp y x) \<Longrightarrow> \<forall>r \<in> set rs. sorted_wrt cmp r \<Longrightarrow>
     \<forall>r \<in> set (pass_f cmp rs). sorted_wrt cmp r\<close>
  by (induction cmp rs rule: pass_f.induct) (auto simp: sorted_merge)

lemma length_pass_f: \<open>length (pass_f cmp rs) = (length rs + 1) div 2\<close>
  by (induction cmp rs rule: pass_f.induct) auto

subsection \<open>Bottom-up merge sort\<close>

definition msortw_body where
  \<open>msortw_body cmp = (\<lambda>(a, rs). doN {
      rs \<leftarrow> pass cmp (a # rs);
      mop_list_pop_hd rs
    })\<close>

definition msortw :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list nres\<close> where
  \<open>msortw cmp xs \<equiv> doN {
     rs \<leftarrow> explode xs;
     if rs = [] then RETURN []
     else doN {
       (a, rs) \<leftarrow> mop_list_pop_hd rs;
       (a, _) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(a, rs). mset (concat (a # rs)) = mset xs \<and>
                              (\<forall>r \<in> set (a # rs). sorted_wrt cmp r)\<^esup>
          (\<lambda>(a, rs). rs \<noteq> []) (msortw_body cmp) (a, rs);
       RETURN a
     }
   }\<close>

lemma not_cons_conv: \<open>\<forall>y ys. l \<noteq> y # ys \<Longrightarrow> l = []\<close>
  by (cases l) auto

lemma msortw_correct:
  assumes T: \<open>transp cmp\<close>
    and TOT: \<open>\<And>x y. cmp x y \<or> cmp y x\<close>
  shows \<open>msortw cmp xs \<le> SPEC (\<lambda>r. mset r = mset xs \<and> sorted_wrt cmp r)\<close>
proof -
  have pass_f_nonempty[simp]: \<open>pass_f cmp (a # rs) \<noteq> []\<close> for a rs
    using length_pass_f[of cmp \<open>a # rs\<close>] by (cases \<open>pass_f cmp (a # rs)\<close>) auto
  have pop_app_mset[simp]:
    \<open>mset (hd (l @ [x])) + mset (concat (tl (l @ [x]))) = mset x + mset (concat l)\<close>
    for l :: \<open>'a list list\<close> and x
    by (cases l) (auto simp: ac_simps)
  have sorted_pop_app_hd:
    \<open>sorted_wrt cmp x \<Longrightarrow> \<forall>r \<in> set l. sorted_wrt cmp r \<Longrightarrow> sorted_wrt cmp (hd (l @ [x]))\<close>
    and sorted_pop_app_tl:
    \<open>y \<in> set (tl (l @ [x])) \<Longrightarrow> sorted_wrt cmp x \<Longrightarrow> \<forall>r \<in> set l. sorted_wrt cmp r \<Longrightarrow>
       sorted_wrt cmp y\<close>
    for l :: \<open>'a list list\<close> and x y
    by (cases l; auto)+
  show ?thesis
    unfolding msortw_def msortw_body_def
    apply (simp add: explode_correct pass_correct)
    apply (refine_vcg
        WHILEIT_rule[where R = \<open>measure (\<lambda>(a, rs). length rs)\<close>])
    apply (auto simp: concat_rev_singletons mset_concat_pass_f length_pass_f
        neq_Nil_conv ac_simps
        dest!: not_cons_conv)
    subgoal by (rule sorted_pop_app_hd) auto
    subgoal by (auto dest!: sorted_pop_app_tl)
    subgoal
      by (rule sorted_pop_app_hd)
        (auto simp: sorted_merge[OF T TOT] intro!: sorted_pass_f[OF T TOT])
    subgoal
      by (auto simp: sorted_merge[OF T TOT] dest!: sorted_pop_app_tl
          intro!: sorted_pass_f[OF T TOT]
          dest: sorted_pass_f[OF T TOT, THEN bspec, rotated])
    done
qed

end
