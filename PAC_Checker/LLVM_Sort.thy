section \<open>Generic Merge Sort for Sepref\<close>
theory LLVM_Sort
  imports IICF_Owning_List
begin

text \<open>Generic merge sort, prepared for refinement by sepref over any list implementation
  that provides \<open>mop_list_pop_front\<close>, \<open>op_list_prepend\<close> and \<open>op_list_is_empty\<close>.
  In this development: owning lists (\<open>ol_assn\<close>, impure elements) and open lists with pure
  elements (\<open>os_assn\<close>). Instances: characters within a string (\<open>String_Assn\<close>),
  variables within a monomial (\<open>Monom_Assn\<close>), monomials within a polynomial
  (\<open>PAC_Checker_Relation\<close>).\<close>

subsection \<open>Merge Sort\<close>

text \<open>Merge sort, implemented the idiomatic sepref way: the algorithms are written as
  high-level programs over abstract lists and synthesized to LLVM \<emdash> no hand-written
  \<open>llM\<close> code, no vcg proofs. The phrasing avoids the borrowing problem entirely: heads
  are POPPED (ownership moves out of the list), compared in keep-mode, and pushed back
  where needed \<emdash> using only operations the owning list implements
  (\<open>mop_list_pop_front\<close>, \<open>op_list_prepend\<close>, \<open>op_list_is_empty\<close>); cf. the \<open>nest_test'\<close>
  regression test in \<open>IICF_Owning_List\<close> for the pattern. The split alternates elements
  (swap-accumulator), so no length computation, no word arithmetic, no \<open>max_snat\<close>
  precondition anywhere.

  The abstract functions live HERE (upstream of \<open>PAC_Checker_Init\<close>) so the refinement
  theorems can be stated against them; \<open>PAC_Checker_Init\<close> must use these constants
  instead of local duplicates (a same-named local \<open>fun\<close> would shadow them).
  Cost note: pop/prepend churn means one node free + alloc per element per level
  (constant factor over a destructive relinking merge); acceptable for the
  normalization phase.\<close>

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

text \<open>\<open>msort\<close> (halving by \<open>take\<close>/\<open>drop\<close>) is kept for compatibility with the legacy
  material in \<open>PAC_Checker_Init\<close> (\<open>msort2\<close>, \<open>merge_sort_poly\<close>, \<open>msort_poly_impl\<close>);
  the implementation below uses the list-friendly \<open>alt_split\<close> variant instead.\<close>

fun msort :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
  \<open>msort f [] = []\<close>
| \<open>msort f [x] = [x]\<close>
| \<open>msort f xs = merge f (msort f (take (size xs div 2) xs))
                        (msort f (drop (size xs div 2) xs))\<close>

text \<open>Alternating split (swap-accumulator): distributes the elements of \<open>xs\<close> onto the
  two result lists without any arithmetic \<emdash> the natural split for linked lists.\<close>

fun alt_split :: \<open>'a list \<Rightarrow> 'a list \<times> 'a list\<close> where
  \<open>alt_split [] = ([], [])\<close>
| \<open>alt_split (x # xs) = (case alt_split xs of (l, r) \<Rightarrow> (x # r, l))\<close>

lemma alt_split_mset[simp]:
  \<open>mset (fst (alt_split xs)) + mset (snd (alt_split xs)) = mset xs\<close>
  by (induction xs) (auto simp: ac_simps split: prod.splits)

text \<open>Length facts, phrased division-free (sum + balancedness) so that everything stays
  in linear arithmetic.\<close>

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

subsubsection \<open>Recursion Equations for Synthesis\<close>

text \<open>\<open>REC\<^sub>T\<close> forms of the three functions, phrased with the owning-list vocabulary
  (\<open>mop_list_pop_front\<close> instead of \<open>hd\<close>/\<open>tl\<close>, prepend to put values back). These are
  the \<open>unfolding\<close>s for the \<open>sepref_def\<close>s below, exactly like \<open>lexord_eq_alt_def2\<close> in
  \<open>PAC_Checker_Init\<close>. Proofs: one \<open>RECT_unfold\<close> per induction case, the induction
  hypothesis closes the recursive occurrence.\<close>

lemma merge_RECT:
  \<open>(RETURN oo merge f) xs ys = REC\<^sub>T (\<lambda>rec (xs, ys).
     if xs = [] then RETURN ys
     else if ys = [] then RETURN xs
     else doN {
       (x, xs) \<leftarrow> mop_list_pop_front xs;
       (y, ys) \<leftarrow> mop_list_pop_front ys;
       if f x y then doN { zs \<leftarrow> rec (xs, y # ys); RETURN (x # zs) }
       else doN { zs \<leftarrow> rec (x # xs, ys); RETURN (y # zs) }
     }) (xs, ys)\<close>
  apply (subst eq_commute)
  apply (induction f xs ys rule: merge.induct)
  subgoal by (subst RECT_unfold, refine_mono) (auto simp: refine_pw_simps)
  subgoal by (subst RECT_unfold, refine_mono) (auto simp: refine_pw_simps)
  subgoal by (subst RECT_unfold, refine_mono) (auto simp: refine_pw_simps)
  done

lemma alt_split_RECT:
  \<open>(RETURN o alt_split) xs = REC\<^sub>T (\<lambda>rec xs.
     if xs = [] then RETURN ([], [])
     else doN {
       (x, xs) \<leftarrow> mop_list_pop_front xs;
       (l, r) \<leftarrow> rec xs;
       RETURN (x # r, l)
     }) xs\<close>
  apply (subst eq_commute)
  apply (induction xs)
  subgoal by (subst RECT_unfold, refine_mono) auto
  subgoal by (subst RECT_unfold, refine_mono)
      (auto simp: refine_pw_simps split: prod.splits)
  done

text \<open>Variant for owning-list targets: their empty producer is the custom
  \<open>op_ol_empty\<close> (cf. the producer-op note in \<open>IICF_Owning_List\<close>); pure-element
  \<open>os_assn\<close> targets use the plain \<open>[]\<close> version above (registered against the generic
  \<open>op_list_empty\<close>).\<close>

lemma alt_split_RECT_ol:
  \<open>(RETURN o alt_split) xs = REC\<^sub>T (\<lambda>rec xs.
     if xs = [] then RETURN (op_ol_empty, op_ol_empty)
     else doN {
       (x, xs) \<leftarrow> mop_list_pop_front xs;
       (l, r) \<leftarrow> rec xs;
       RETURN (x # r, l)
     }) xs\<close>
  unfolding op_ol_empty_def op_list_empty_def
  by (rule alt_split_RECT)

lemma msort_alt_RECT:
  \<open>(RETURN o msort_alt f) xs = REC\<^sub>T (\<lambda>rec xs.
     if xs = [] then RETURN xs
     else doN {
       (x, xs') \<leftarrow> mop_list_pop_front xs;
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
  subgoal by (subst RECT_unfold, refine_mono) (auto simp: refine_pw_simps)
  subgoal by (subst RECT_unfold, refine_mono)
      (auto simp: refine_pw_simps split: prod.splits)
  done

text \<open>The split is registered here once (a generic operation); the comparator-specialized
  \<open>merge\<close>/\<open>msort_alt\<close> instances are registered at their instantiation sites (sepref
  rejects partial applications like \<open>merge (\<le>)\<close> as operation heads).\<close>

sepref_register alt_split

end
