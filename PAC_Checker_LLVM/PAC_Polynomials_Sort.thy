theory PAC_Polynomials_Sort
  imports IICF_Copying_List
begin
(* TODO: This theory should be named Copying_List_Sort or something *)

text \<open>This theory defines a bottom-up merge sort using WHILE loops
  instead of recursion. It is designed to work with only the operations
  supported in \<open>IICF_Copying_List.thy\<close> (which in particular does not
  hold the length of the list).
  
  We define each function once recursively, then with a loop, proving
  equivalence for each version.\<close>

fun explode :: \<open>'a list \<Rightarrow> 'a list list\<close>
  where \<open>explode xs = map (\<lambda>x. [x]) xs\<close>

definition explode_while :: \<open>'a list \<Rightarrow> 'a list list nres\<close> where
  \<open>explode_while xs \<equiv> doN {
    (r, _) \<leftarrow> WHILET
      (\<lambda>(r, xs). xs\<noteq>[])
      (\<lambda>(r, xs). doN {
        (x, xs) \<leftarrow> mop_list_pop_hd xs;
        RETURN ([x] # r, xs) 
      }) ([], xs);
    RETURN r
  }\<close>

lemma explode_while_aux:
  \<open>doN {
    (r, _) \<leftarrow> WHILET
      (\<lambda>(r, xs). xs\<noteq>[])
      (\<lambda>(r, xs). doN {
        (x, xs) \<leftarrow> mop_list_pop_hd xs;
        RETURN ([x] # r, xs)
      }) (r\<^sub>0, xs);
    RETURN r
  } = RETURN (rev (map (\<lambda>x. [x]) xs) @ r\<^sub>0)\<close>
proof (induction xs arbitrary: r\<^sub>0)
  case Nil
  then show ?case by (subst WHILET_unfold) simp
next
  case (Cons a xs)
  then show ?case by (subst WHILET_unfold) (simp add: Cons.IH)
qed

lemma explode_equiv: \<open>explode_while xs \<equiv> (RETURN o rev o explode) xs\<close>
  unfolding explode_while_def
  by (rule eq_reflection) (subst explode_while_aux, simp)

lemma explode_sorted: \<open>\<forall>x \<in> set (explode xs). sorted_wrt cmp x\<close>
  by simp

lemma explode_while_spec: \<open>explode_while xs \<le> SPEC (\<lambda>rs. (\<forall>r\<in>set rs. sorted_wrt cmp r) \<and> rs = rev (explode xs))\<close>
proof -
  have \<open>explode_while xs \<le> SPEC (\<lambda>rs. rs = rev (explode xs))\<close>
    using explode_equiv by (metis RETURN_SPEC_conv comp_apply order_mono_setup.refl) 
  then show ?thesis
    using explode_sorted by (simp add: explode_equiv)
qed

locale cmp_env =
  fixes cmp :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes cmp_trans: \<open>(cmp x y) \<and> (cmp y z) \<Longrightarrow> (cmp x z)\<close>
  assumes total: \<open>\<And>x y. cmp x y \<or> cmp y x\<close>
begin

lemma cmp_transD: \<open>cmp x y \<Longrightarrow> cmp y z \<Longrightarrow> cmp x z\<close>
  using cmp_trans by blast

lemma cmp_total_notD: \<open>\<not> cmp x y \<Longrightarrow> cmp y x\<close>
  using total by blast

lemma no_consD: \<open>\<forall>y ys. l \<noteq> y # ys \<Longrightarrow> l = []\<close>
  by (cases l) auto

definition \<open>merge_while_inner \<equiv> \<lambda>xs\<^sub>0 ys\<^sub>0 r\<^sub>0. WHILEIT
    (\<lambda>(r,xs,ys).
      sorted_wrt cmp xs \<and> sorted_wrt cmp ys \<and> sorted_wrt cmp (rev r) \<and>
      (\<forall>a\<in>set r. \<forall>b\<in>set xs \<union> set ys. cmp a b) \<and>
      mset r + mset xs + mset ys = mset r\<^sub>0 + mset xs\<^sub>0 + mset ys\<^sub>0)
    (\<lambda>(r,xs,ys). xs\<noteq>[] \<and> ys\<noteq>[])
    (\<lambda>(r,xs,ys). doN {
      (x,xs) \<leftarrow> mop_list_pop_hd xs;
      (y,ys) \<leftarrow> mop_list_pop_hd ys;
      if cmp x y then RETURN (x#r,xs,y#ys)
      else RETURN (y#r,x#xs,ys)
    }) (r\<^sub>0,xs\<^sub>0,ys\<^sub>0)\<close>

lemma merge_while_inner_spec:
  assumes \<open>sorted_wrt cmp xs\<^sub>0\<close> \<open>sorted_wrt cmp ys\<^sub>0\<close>
    and \<open>sorted_wrt cmp (rev r\<^sub>0)\<close>
    and \<open>\<forall>a\<in>set r\<^sub>0. \<forall>b\<in>set xs\<^sub>0 \<union> set ys\<^sub>0. cmp a b\<close>
  shows \<open>merge_while_inner xs\<^sub>0 ys\<^sub>0 r\<^sub>0 \<le> SPEC (\<lambda>(r,xs,ys).
      (xs = [] \<or> ys = []) \<and>
      sorted_wrt cmp (rev r @ xs @ ys) \<and>
      mset r + mset xs + mset ys = mset r\<^sub>0 + mset xs\<^sub>0 + mset ys\<^sub>0)\<close>
  unfolding merge_while_inner_def
  apply (refine_vcg WHILEIT_rule[where R=\<open>measure (\<lambda>(_,xs,ys). length xs + length ys)\<close>])
  using assms
  apply (auto simp: sorted_wrt_append neq_Nil_conv add_mset_commute
              dest!: no_consD dest: cmp_transD cmp_total_notD)
  by (meson cmp_transD cmp_total_notD)+

definition \<open>merge_while \<equiv> \<lambda>xs ys. doN{
    (r, xs, ys) \<leftarrow> merge_while_inner xs ys [];
    RETURN (rev r @ xs @ ys)
  }\<close>

lemma merge_while_spec:
  assumes \<open>sorted_wrt cmp xs\<close> \<open>sorted_wrt cmp ys\<close>
  shows \<open>merge_while xs ys \<le>
    SPEC (\<lambda>r. sorted_wrt cmp r \<and> mset r = mset xs + mset ys)\<close>
  unfolding merge_while_def
  by (refine_vcg merge_while_inner_spec; auto simp: assms)

definition pass :: \<open>'a list list \<Rightarrow> 'a list list nres\<close> where
  \<open>pass xss\<^sub>0 \<equiv> doN {
    (r, _) \<leftarrow> WHILEIT
      (\<lambda>(r,xss).
        (\<forall>xs\<in>set r \<union> set xss. sorted_wrt cmp xs) \<and>
        mset (concat r) + mset (concat xss) = mset (concat xss\<^sub>0) \<and>
        2 * length r + length xss \<le> length xss\<^sub>0 + (if xss = [] then 1 else 0) \<and>
        (r = [] \<longrightarrow> xss = xss\<^sub>0))
      (\<lambda>(r,xss). xss\<noteq>[])
      (\<lambda>(r,xss). doN{
        (xs,xss) \<leftarrow> mop_list_pop_hd xss;
        if xss=[] then RETURN (xs#r,xss)
        else doN {
          (ys,xss) \<leftarrow> mop_list_pop_hd xss;
          ms \<leftarrow> merge_while xs ys;
          RETURN (ms#r, xss)
        }
      }) ([], xss\<^sub>0);
    RETURN r
  }\<close>

lemma pass_spec:
  assumes \<open>\<forall>xs\<in>set xss\<^sub>0. sorted_wrt cmp xs\<close>
  shows \<open>pass xss\<^sub>0 \<le> SPEC (\<lambda>r.
      (\<forall>xs\<in>set r. sorted_wrt cmp xs) \<and>
      mset (concat r) = mset (concat xss\<^sub>0) \<and>
      length r \<le> (length xss\<^sub>0 + 1) div 2 \<and>
      (xss\<^sub>0 \<noteq> [] \<longrightarrow> r \<noteq> []))\<close>
  unfolding pass_def
  apply (refine_vcg WHILEIT_rule[where R=\<open>measure (\<lambda>(_,xss). length xss)\<close>] merge_while_spec)
  using assms
  apply (auto simp: neq_Nil_conv ac_simps split: if_splits)
  subgoal for r by (cases r) auto
  done

definition run_passes :: \<open>'a list list \<Rightarrow> 'a list list nres\<close> where
  \<open>run_passes xss\<^sub>0 \<equiv> doN {
    ASSERT (xss\<^sub>0\<noteq>[]);
    (xss, _) \<leftarrow> WHILEIT
      (\<lambda>(xss,done).
        (\<forall>xs\<in>set xss. sorted_wrt cmp xs) \<and>
        mset (concat xss) = mset (concat xss\<^sub>0) \<and>
        xss \<noteq> [] \<and>
        (done \<longrightarrow> length xss = 1))
      (\<lambda>(xss,done). \<not>done)
      (\<lambda>(xss,done). doN {
        (xs,xss) \<leftarrow> mop_list_pop_hd xss;
        if xss = [] then RETURN (xs#xss,True)
        else doN {
          xss' \<leftarrow> pass (xs#xss);
          RETURN (xss',False)
        }
      }) (xss\<^sub>0, False);
    RETURN xss
  }\<close>

lemma run_passes_spec:
  assumes \<open>\<forall>xs\<in>set xss\<^sub>0. sorted_wrt cmp xs\<close>
      and \<open>xss\<^sub>0 \<noteq> []\<close>
    shows \<open>run_passes xss\<^sub>0 \<le> SPEC (\<lambda>r. \<exists>xs.
      r = [xs] \<and> sorted_wrt cmp xs \<and> mset xs = mset (concat xss\<^sub>0))\<close>
  unfolding run_passes_def
  apply (refine_vcg WHILEIT_rule[where
      R=\<open>measure (\<lambda>(xss,done). 2 * length xss + (if done then 0 else 1))\<close>] pass_spec)
  using assms
  apply (auto simp: neq_Nil_conv length_Suc_conv dest!: no_consD split: if_splits)
  done

definition msort :: \<open>'a list \<Rightarrow> 'a list nres\<close> where
  \<open>msort xs \<equiv> doN {
    if xs = [] then RETURN xs
    else doN {
      xss \<leftarrow> explode_while xs;
      xss' \<leftarrow> run_passes xss;
      xs \<leftarrow> mop_list_hd xss';
      RETURN (xs)
    }
  }\<close>

lemma msort_spec: \<open>msort xs \<le> SPEC (\<lambda>r. mset xs = mset r \<and> sorted_wrt cmp r)\<close>
  unfolding msort_def
  apply (refine_vcg explode_while_spec run_passes_spec)
  apply simp_all
  subgoal by blast
  subgoal by (auto simp: rev_map)
  subgoal by fastforce
  done

end

locale cmp_env_impl = cmp_env + freeable_assn +
  fixes cmp_impl :: \<open>'c::llvm_rep \<Rightarrow> 'c \<Rightarrow> 1 word llM\<close>
  assumes cmp_hnr[sepref_fr_rules]:
    \<open>(uncurry cmp_impl,uncurry (RETURN oo cmp)) \<in> A\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
begin

lemma ls_emp: \<open>xs\<noteq>[] \<equiv> \<not>(op_list_is_empty xs)\<close> by simp

sepref_def explode_impl is \<open>explode_while\<close>
  :: \<open>(cl_assn' A)\<^sup>d \<rightarrow>\<^sub>a cl_assn' (cl_assn' A)\<close>
  unfolding explode_while_def ls_emp
  by sepref

sepref_register cmp
sepref_def merge_impl is \<open>uncurry (PR_CONST merge_while)\<close>
  :: \<open>(cl_assn' A)\<^sup>d *\<^sub>a (cl_assn' A)\<^sup>d \<rightarrow>\<^sub>a cl_assn' A\<close>
  unfolding merge_while_def merge_while_inner_def ls_emp PR_CONST_def
  by sepref

interpretation nested: freeable_assn \<open>cl_assn' A\<close> cl_free
  by unfold_locales (rule cl_assn_free)

sepref_register merge_while
sepref_def pass_impl is \<open>PR_CONST pass\<close>
  :: \<open>(cl_assn' (cl_assn' A))\<^sup>d \<rightarrow>\<^sub>a cl_assn' (cl_assn' A)\<close>
  unfolding pass_def ls_emp PR_CONST_def
  by sepref

sepref_register pass
sepref_def run_passes_impl is \<open>PR_CONST run_passes\<close>
  :: \<open>(cl_assn' (cl_assn' A))\<^sup>d \<rightarrow>\<^sub>a cl_assn' (cl_assn' A)\<close>
  unfolding run_passes_def ls_emp PR_CONST_def
  by sepref

sepref_register run_passes
sepref_def msort_impl is \<open>PR_CONST msort\<close>
  :: \<open>(cl_assn' A)\<^sup>d \<rightarrow>\<^sub>a cl_assn' A\<close>
  unfolding msort_def PR_CONST_def
  by sepref

end

end
