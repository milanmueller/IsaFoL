section \<open>Generic Merge Sort for Sepref\<close>
theory LLVM_Sort
  imports IICF_Copying_List
begin

subsection \<open>Merge Sort\<close>

text \<open>The previous merge sort implementation translates poorly to LLVM, so we reimplement
  merge sort, tailored to our custom @{theory IICF_Copying_List}.\<close>

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

text \<open>\<open>msort\<close> (halving by \<open>take\<close>/\<open>drop\<close>) is kept for compatibility with the existing
  implementation in @{theory PAC_Checker_Init}.\<close>

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

text \<open>Correctness of the abstract algorithm \<emdash> these two lemmas are what downstream
  users compose against specifications like \<open>sort_poly_spec\<close>.\<close>

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

end
