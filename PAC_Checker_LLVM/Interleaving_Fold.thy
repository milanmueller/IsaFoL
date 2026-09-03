theory Interleaving_Fold
  imports IICF_Copying_List
begin

text \<open>This theory defines a generalization of the
  @{term foldl} function that allows traversal through two lists.
  In Isabelle_LLVM, using the Copying List implementation,
  this allows us to walk two lists simultaneously without
  destroying the original lists, as long as the inner functions
  keep their arguments intact.\<close>

text \<open>When traversing two lists, direction defines which list to
  recurse into\<close>
datatype direction = LEFT | RIGHT | BOTH | STOP

fun ifoldl :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> direction \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> direction)
  \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'c \<Rightarrow> 'a)
  \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> 'a\<close> where
  \<open>ifoldl _ _   _  _  acc [] []             = acc\<close>
| \<open>ifoldl _ _   f1 _  acc xs []             = foldl f1 acc xs\<close>
| \<open>ifoldl _ _   _  f2 acc [] ys             = foldl f2 acc ys\<close>
| \<open>ifoldl f dec f1 f2 acc (x # xs) (y # ys) = (
    case dec x y of
      STOP  \<Rightarrow> (f acc x y STOP)
    | LEFT  \<Rightarrow> ifoldl f dec f1 f2 (f acc x y LEFT)  xs (y # ys)
    | RIGHT \<Rightarrow> ifoldl f dec f1 f2 (f acc x y RIGHT) (x # xs) ys
    | BOTH  \<Rightarrow> ifoldl f dec f1 f2 (f acc x y BOTH)  xs ys
  )\<close>

definition foldl_nres :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'a nres) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a nres\<close> where
  \<open>foldl_nres f acc xs \<equiv> REC\<^sub>T (\<lambda>fr (acc, xs). doN {
    if xs = [] then RETURN acc 
    else doN {
      (x,xs) \<leftarrow> mop_list_pop_hd xs;
      acc \<leftarrow> f acc x;
      fr (acc, xs) 
    } 
  }) (acc, xs)\<close>

definition ifoldl_nres :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> direction \<Rightarrow> 'a nres) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> direction nres)
  \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'a nres) \<Rightarrow> ('a \<Rightarrow> 'c \<Rightarrow> 'a nres)
  \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> 'a nres\<close> where
  \<open>ifoldl_nres f dec f1 f2 acc xs ys \<equiv> doN {
    (acc, xs, ys, stop) \<leftarrow> WHILEIT
      (\<lambda>_. True)
      (\<lambda>(acc, xs, ys, stop). xs \<noteq> [] \<and> ys \<noteq> [] \<and> \<not>stop)
      (\<lambda>(acc, xs, ys, stop). doN {
        ASSERT (xs \<noteq> [] \<and> ys \<noteq> []);
        (x,xs) \<leftarrow> mop_list_pop_hd xs;
        (y,ys) \<leftarrow> mop_list_pop_hd ys;
        dir \<leftarrow> dec x y;
        acc \<leftarrow> f acc x y dir;
        if dir = STOP then RETURN (acc, xs, ys, True)
        else if dir = LEFT then RETURN (acc, xs, y # ys, False)
        else if dir = RIGHT then RETURN (acc, x # xs, ys, False)
        else RETURN (acc, xs, ys, False)
      })
      (acc, xs, ys, False);
    if stop then RETURN acc
    else if ys = [] then foldl_nres f1 acc xs
    else if xs = [] then foldl_nres f2 acc ys
    else RETURN acc
  }\<close>

lemma WHILEIT_true_rule:
  assumes WF: \<open>wf R\<close>
    and I0: \<open>I s\<close>
    and IS: \<open>\<And>s. \<lbrakk>I s; b s\<rbrakk> \<Longrightarrow> f s \<le> SPEC (\<lambda>s'. I s' \<and> (s', s) \<in> R)\<close>
    and PHI: \<open>\<And>s. \<lbrakk>I s; \<not>b s\<rbrakk> \<Longrightarrow> \<Phi> s\<close>
  shows \<open>WHILEIT (\<lambda>_. True) b f s \<le> SPEC \<Phi>\<close>
  using WHILET_rule[OF assms] unfolding WHILET_def .

lemma foldl_nres_unfold:
  \<open>foldl_nres f acc xs = doN {
    if xs = [] then RETURN acc
    else doN {
      (x, xs) \<leftarrow> mop_list_pop_hd xs;
      acc \<leftarrow> f acc x;
      foldl_nres f acc xs
    }
  }\<close>
  unfolding foldl_nres_def
  apply (subst RECT_unfold)
  subgoal by refine_mono
  subgoal by simp
  done

lemma foldl_nres_refine:
  assumes f: \<open>\<And>acc x. fn acc x \<le> SPEC (\<lambda>r. r = f acc x)\<close>
  shows \<open>foldl_nres fn acc xs \<le> SPEC (\<lambda>r. r = foldl f acc xs)\<close>
proof (induction xs arbitrary: acc)
  case Nil
  show ?case by (subst foldl_nres_unfold) simp
next
  case (Cons x xs acc)
  show ?case
    apply (subst foldl_nres_unfold)
    apply (use Cons.IH[of \<open>f acc x\<close>] f[of acc x] in
        \<open>auto simp: pw_le_iff refine_pw_simps mop_list_pop_hd_def\<close>)
    done
qed

lemma ifoldl_Nil2: \<open>ifoldl f dec f1 f2 acc xs [] = foldl f1 acc xs\<close>
  by (cases xs) auto

lemma ifoldl_Nil1: \<open>ifoldl f dec f1 f2 acc [] ys = foldl f2 acc ys\<close>
  by (cases ys) auto

lemma ifoldl_nres_refine:
  assumes f: \<open>\<And>acc x y dir. fn acc x y dir \<le> SPEC (\<lambda>r. r = f acc x y dir)\<close>
      and dec: \<open>\<And>x y. decn x y \<le> SPEC (\<lambda>r. r = dec x y)\<close>
      and f1: \<open>\<And>acc x. f1n acc x \<le> SPEC (\<lambda>r. r = f1 acc x)\<close>
      and f2: \<open>\<And>acc y. f2n acc y \<le> SPEC (\<lambda>r. r = f2 acc y)\<close>
    shows \<open>ifoldl_nres fn decn f1n f2n acc xs ys \<le> SPEC (\<lambda>r. r = ifoldl f dec f1 f2 acc xs ys)\<close>
  unfolding ifoldl_nres_def
  apply (rule bind_rule)
  apply (rule WHILEIT_true_rule[where
        I = \<open>\<lambda>(acc', xs', ys', stop).
              (if stop then acc' else ifoldl f dec f1 f2 acc' xs' ys')
                = ifoldl f dec f1 f2 acc xs ys\<close>
        and R = \<open>measure (\<lambda>(acc', xs', ys', stop).
              (if stop then 0 else length xs' + length ys' + 1))\<close>])
  subgoal by simp
  subgoal by simp
  subgoal for s
    apply (cases s rule: prod_cases4)
    apply (simp only: prod.case)
    apply (elim conjE)
    apply (cases \<open>fst (snd s)\<close>; cases \<open>fst (snd (snd s))\<close>)
    apply (simp_all add: mop_list_pop_hd_def)
    apply (rule bind_rule)
    apply (rule order_trans[OF dec])
    apply (rule SPEC_rule)
    apply (rule bind_rule)
    apply (rule order_trans[OF f])
    apply (rule SPEC_rule)
    apply (auto split: direction.splits)
    done
  subgoal for s
    apply (cases s rule: prod_cases4)
    apply (auto simp: ifoldl_Nil1 ifoldl_Nil2
        intro: order_trans[OF foldl_nres_refine[OF f1]]
               order_trans[OF foldl_nres_refine[OF f2]])
    done
  done

subsection \<open>Unfolding equations for @{term ifoldl_nres}\<close>

lemma foldl_nres_Nil[simp]: \<open>foldl_nres f acc [] = RETURN acc\<close>
  by (subst foldl_nres_unfold) simp

lemma foldl_nres_Cons:
  \<open>foldl_nres f acc (x # xs) = doN {acc \<leftarrow> f acc x; foldl_nres f acc xs}\<close>
  by (subst foldl_nres_unfold) (simp add: mop_list_pop_hd_def)

lemma ifoldl_nres_Nil2: \<open>ifoldl_nres fn decn f1n f2n acc xs [] = foldl_nres f1n acc xs\<close>
  unfolding ifoldl_nres_def by (subst WHILEIT_unfold) simp

lemma ifoldl_nres_Nil1: \<open>ifoldl_nres fn decn f1n f2n acc [] ys = foldl_nres f2n acc ys\<close>
  unfolding ifoldl_nres_def by (subst WHILEIT_unfold) (cases ys; simp)

lemma ifoldl_nres_Cons:
  \<open>ifoldl_nres fn decn f1n f2n acc (x # xs) (y # ys) = doN {
    dir \<leftarrow> decn x y;
    acc \<leftarrow> fn acc x y dir;
    case dir of
      STOP \<Rightarrow> RETURN acc
    | LEFT \<Rightarrow> ifoldl_nres fn decn f1n f2n acc xs (y # ys)
    | RIGHT \<Rightarrow> ifoldl_nres fn decn f1n f2n acc (x # xs) ys
    | BOTH \<Rightarrow> ifoldl_nres fn decn f1n f2n acc xs ys
  }\<close>
  unfolding ifoldl_nres_def
  apply (subst WHILEIT_unfold)
  apply (simp add: mop_list_pop_hd_def)
  apply (intro bind_cong[OF refl] ext)
  apply (auto split: direction.splits)
  text \<open>Remaining: the \<open>STOP\<close> case, where the loop exits at once.\<close>
  apply (subst WHILEIT_unfold)
  apply simp
  done

section \<open>Implementation for Copying Lists\<close>

definition[llvm_code]: \<open>cl_foldl_monadic' f \<equiv> MMonad.REC (\<lambda>ff (acc, p).
  if p = null then Mreturn acc
  else doM {
    n \<leftarrow> ll_load p;
    acc \<leftarrow> f acc (node.val n);
    ff (acc, node.next n)
  })\<close>

lemmas cl_foldl_monadic'_unfold = REC_unfold_extr[OF cl_foldl_monadic'_def, discharge_monos]

lemma cl_fold_monadic'_rule:
  assumes F: \<open>\<And>a ai b bi. llvm_htriple (A a ai ** B b bi) (fi ai bi) (\<lambda>r. A (f a b) r ** B b bi)\<close>
  shows \<open>llvm_htriple
    (A a ai ** cl_assn' B bs bsi)
    (cl_foldl_monadic' fi (ai, bsi))
    (\<lambda>r. A (foldl f a bs) r ** cl_assn' B bs bsi)\<close>
proof (induction bs arbitrary: a ai bsi)
  case Nil
  show ?case
    supply [simp] = cl_assn_simps
    apply (subst cl_foldl_monadic'_unfold)
    by vcg
next
  case (Cons b bs)
  note [vcg_rules] = Cons.IH F
  show ?case
    supply [simp] = cl_assn_simps
    apply (subst cl_foldl_monadic'_unfold)
    by vcg
qed

lemma cl_fold_hfref:
  assumes F: \<open>(uncurry fi, uncurry (RETURN oo f)) \<in> A\<^sup>d *\<^sub>a B\<^sup>k \<rightarrow>\<^sub>a A\<close>
  shows \<open>(cl_foldl_monadic' fi, uncurry (RETURN oo foldl f))
        \<in> A\<^sup>d *\<^sub>a (cl_assn' B)\<^sup>k \<rightarrow>\<^sub>a A\<close>
proof -
  have BODY: \<open>llvm_htriple (A a ai ** B b bi) (fi ai bi)
                (\<lambda>r. A (f a b) r ** B b bi)\<close> for a ai b bi
    apply (rule htriple_ent_post[OF _ hfref_htriple_d1_k2[OF F]])
    by (simp add: sep_conj_aci)
  show ?thesis
    supply [vcg_rules] = cl_fold_monadic'_rule[where A=A and B=B and fi=fi and f=f, OF BODY]
    by (sepref_to_hoare; vcg)
qed

text \<open>Refinement of the monadic fold @{term foldl_nres}: the step function is an
  \<open>nres\<close> program, so its rule carries a \<open>nofail\<close> premise and a refinement
  postcondition (the shape of @{thm hn_refineD}).\<close>
lemma cl_fold_monadic'_nres_rule:
  assumes F: \<open>\<And>a ai b bi. nofail (f a b) \<Longrightarrow> llvm_htriple
    (A a ai ** B b bi) (fi ai bi)
    (\<lambda>r. B b bi ** (EXS x. A x r ** \<up>(RETURN x \<le> f a b)))\<close>
  assumes NF: \<open>nofail (foldl_nres f a bs)\<close>
  shows \<open>llvm_htriple
    (A a ai ** cl_assn' B bs bsi)
    (cl_foldl_monadic' fi (ai, bsi))
    (\<lambda>r. cl_assn' B bs bsi ** (EXS x. A x r ** \<up>(RETURN x \<le> foldl_nres f a bs)))\<close>
  using NF
proof (induction bs arbitrary: a ai bsi)
  case Nil
  show ?case
    supply [simp] = cl_assn_simps
    apply (subst cl_foldl_monadic'_unfold)
    apply (subst foldl_nres_unfold)
    by vcg
next
  case (Cons b bs)
  note [vcg_rules] = F Cons.IH
  show ?case
    using Cons.prems
    supply [simp] = cl_assn_simps refine_pw_simps pw_le_iff mop_list_pop_hd_def
    apply (subst (asm) foldl_nres_unfold)
    apply (subst cl_foldl_monadic'_unfold)
    apply (subst foldl_nres_unfold)
    by vcg
qed

text \<open>Variant with the \<open>nofail\<close> condition in the precondition. As a rule premise
  it is checked before the pure parts of the current state are extracted, which
  loses facts such as \<open>drop j cs = []\<close> obtained from \<open>cl_assn' C (drop j cs) null\<close>.\<close>
lemma cl_fold_monadic'_nres_rule':
  assumes F: \<open>\<And>a ai b bi. nofail (f a b) \<Longrightarrow> llvm_htriple
    (A a ai ** B b bi) (fi ai bi)
    (\<lambda>r. B b bi ** (EXS x. A x r ** \<up>(RETURN x \<le> f a b)))\<close>
  shows \<open>llvm_htriple
    (A a ai ** cl_assn' B bs bsi ** \<up>(nofail (foldl_nres f a bs)))
    (cl_foldl_monadic' fi (ai, bsi))
    (\<lambda>r. cl_assn' B bs bsi ** (EXS x. A x r ** \<up>(RETURN x \<le> foldl_nres f a bs)))\<close>
proof (rule htriple_pure_preI)
  assume \<open>pure_part (A a ai ** cl_assn' B bs bsi ** \<up>(nofail (foldl_nres f a bs)))\<close>
  then have NF: \<open>nofail (foldl_nres f a bs)\<close>
    by (auto dest!: pure_part_split_conj)
  show \<open>llvm_htriple
    (A a ai ** cl_assn' B bs bsi ** \<up>(nofail (foldl_nres f a bs)))
    (cl_foldl_monadic' fi (ai, bsi))
    (\<lambda>r. cl_assn' B bs bsi ** (EXS x. A x r ** \<up>(RETURN x \<le> foldl_nres f a bs)))\<close>
    apply (rule htriple_ent_pre[OF _ cl_fold_monadic'_nres_rule[OF F NF]])
    by (auto simp: entails_def sep_algebra_simps pred_lift_extract_simps)
qed

lemma cl_fold_monadic'_hfref:
  assumes F: \<open>(uncurry fi, uncurry f) \<in> A\<^sup>d *\<^sub>a B\<^sup>k \<rightarrow>\<^sub>a A\<close>
  shows \<open>(cl_foldl_monadic' fi, uncurry (foldl_nres f))
        \<in> A\<^sup>d *\<^sub>a (cl_assn' B)\<^sup>k \<rightarrow>\<^sub>a A\<close>
proof -
  note HT = F[to_hnr, unfolded autoref_tag_defs, THEN hn_refineD]
  have BODY: \<open>llvm_htriple (A a ai ** B b bi) (fi ai bi)
      (\<lambda>r. B b bi ** (EXS x. A x r ** \<up>(RETURN x \<le> f a b)))\<close>
    if NF: \<open>nofail (f a b)\<close> for a ai b bi
    apply (rule htriple_ent_pre[OF _ htriple_ent_post[OF _ HT[OF NF]]])
    unfolding hn_ctxt_def
    subgoal by (rule entails_refl)
    subgoal
      by (auto simp: entails_def sep_algebra_simps sep_conj_exists invalid_assn_def
          pred_lift_extract_simps)
    done
  show ?thesis
    supply [vcg_rules] = cl_fold_monadic'_nres_rule[where A=A and B=B and fi=fi and f=f, OF BODY]
    by (sepref_to_hoare; vcg)
qed

definition cl_ifoldl_guard
  :: \<open>'a::llvm_rep \<times> 'b::llvm_rep cl_list \<times> 'c::llvm_rep cl_list \<times> 1 word \<Rightarrow> 1 word llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>cl_ifoldl_guard \<equiv> \<lambda>(acc, xp, yp, stop). doM {
      if to_bool stop then Mreturn 0
      else if xp = null then Mreturn 0
      else if yp = null then Mreturn 0
      else Mreturn 1}\<close>

definition cl_ifoldl ::
  \<open>('a::llvm_rep \<Rightarrow> 'b::llvm_rep \<Rightarrow> 'c::llvm_rep \<Rightarrow> 8 word \<Rightarrow> 'a llM)
    \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 8 word llM)
    \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'a llM) \<Rightarrow> ('a \<Rightarrow> 'c \<Rightarrow> 'a llM)
    \<Rightarrow> 'a \<Rightarrow> 'b cl_list \<Rightarrow> 'c cl_list \<Rightarrow> 'a llM\<close>
  where [llvm_code]:
  \<open>cl_ifoldl f dec f1 f2 acc xp yp \<equiv> doM {
    (acc, xp, yp, stop) \<leftarrow> llc_while cl_ifoldl_guard
    (\<lambda>(acc, xp, yp, stop). doM {
      xn \<leftarrow> ll_load xp;
      yn \<leftarrow> ll_load yp;
      let x = node.val xn;
      let y = node.val yn;
      dir \<leftarrow> dec x y;
      acc \<leftarrow> f acc x y dir;
      if dir = 0 then
        Mreturn (acc, node.next xn, node.next yn, 1)
      else if dir = 1 then
        Mreturn (acc, node.next xn, yp, 0)
      else if dir = 2 then
        Mreturn (acc, xp, node.next yn, 0)
      else
        Mreturn (acc, node.next xn, node.next yn, 0)
    }) (acc, xp, yp, 0 :: 1 word);
    if to_bool stop then
      Mreturn acc
    else if yp = null then
      cl_foldl_monadic' f1 (acc, xp)
    else if xp = null then
      cl_foldl_monadic' f2 (acc, yp)
    else
      Mreturn acc
  }\<close>

subsection \<open>Direction encoding\<close>

definition dir_enc :: \<open>direction \<Rightarrow> 8 word\<close> where
  \<open>dir_enc d \<equiv> case d of STOP \<Rightarrow> 0 | LEFT \<Rightarrow> 1 | RIGHT \<Rightarrow> 2 | BOTH \<Rightarrow> 3\<close>

lemma dir_enc_simps[simp]:
  \<open>dir_enc STOP = 0\<close> \<open>dir_enc LEFT = 1\<close> \<open>dir_enc RIGHT = 2\<close> \<open>dir_enc BOTH = 3\<close>
  by (simp_all add: dir_enc_def)

lemma dir_enc_eq_iff[simp]:
  \<open>dir_enc d = 0 \<longleftrightarrow> d = STOP\<close>
  \<open>dir_enc d = 1 \<longleftrightarrow> d = LEFT\<close>
  \<open>dir_enc d = 2 \<longleftrightarrow> d = RIGHT\<close>
  \<open>dir_enc d = 3 \<longleftrightarrow> d = BOTH\<close>
  by (cases d; simp)+

definition dir_rel :: \<open>(8 word \<times> direction) set\<close> where
  \<open>dir_rel \<equiv> {(w, d). w = dir_enc d}\<close>

definition dir_assn :: \<open>direction \<Rightarrow> 8 word \<Rightarrow> assn\<close> where
  \<open>dir_assn \<equiv> pure dir_rel\<close>

lemma dir_assn_simp[simp]: \<open>dir_assn d w = \<up>(w = dir_enc d)\<close>
  unfolding dir_assn_def dir_rel_def by (simp add: pure_app_eq)

context begin
interpretation llvm_prim_arith_setup .

lemma ll_ptrcmp_eq_null_simp:
  \<open>ll_ptrcmp_eq a null = doM { Mreturn (from_bool (a = null))}\<close>
  by (vcg_normalize; simp add: eq_commute[of null])

lemma ll_ptrcmp_eq_null_rule[vcg_rules]:
  \<open>llvm_htriple \<box> (ll_ptrcmp_eq a null) (\<lambda>r. \<up>(to_bool r \<longleftrightarrow> a = null))\<close>
  unfolding ll_ptrcmp_eq_null_simp
  by vcg

lemma ll_icmp_eq_bool_rule:
  \<open>llvm_htriple \<box> (ll_icmp_eq (a::'l::len word) b) (\<lambda>r. \<up>(to_bool r \<longleftrightarrow> a = b))\<close>
  by vcg

end

subsection \<open>Hoare rule for @{term cl_ifoldl}\<close>
lemma cl_ifoldl_guard_rule[vcg_rules]:
  \<open>llvm_htriple \<box> (cl_ifoldl_guard (acci, xp, yp, stop))
    (\<lambda>r. \<upharpoonleft>bool.assn (stop = 0 \<and> xp \<noteq> null \<and> yp \<noteq> null) r)\<close>
proof -
  interpret llvm_prim_ctrl_setup .
  show ?thesis
    unfolding cl_ifoldl_guard_def
    supply [simp] = bool.assn_def
    by vcg
qed

lemma cl_assn'_load_rule:
  \<open>llvm_htriple (cl_assn' A xs p ** \<up>(p \<noteq> null)) (ll_load p)
    (\<lambda>r. EXS c q. \<up>(r = Node c q \<and> xs \<noteq> []) ** \<upharpoonleft>ll_bpto (Node c q) p
        ** A (hd xs) c ** cl_assn' A (tl xs) q)\<close>
proof (cases xs)
  case Nil
  then show ?thesis by (simp add: cl_assn_simps) vcg
next
  case (Cons x xs')
  then show ?thesis by (simp add: cl_assn_simps) vcg
qed

lemma olseg_snoc_red:
  \<open>PRECOND (SOLVE_AUTO (i < length xs)) \<Longrightarrow>
    is_sep_red \<box> (\<upharpoonleft>ll_bpto (Node c r) q ** A (xs ! i) c)
      (olseg A (take i xs) p q) (olseg A (take (Suc i) xs) p r)\<close>
  unfolding vcg_tag_defs
proof (rule is_sep_redI)
  fix Ps Qs
  assume I: \<open>i < length xs\<close>
    and H: \<open>\<box> ** Ps \<turnstile> (\<upharpoonleft>ll_bpto (Node c r) q ** A (xs ! i) c) ** Qs\<close>
  have H': \<open>Ps \<turnstile> \<upharpoonleft>ll_bpto (Node c r) q ** A (xs ! i) c ** Qs\<close>
    using H by simp
  have 1: \<open>olseg A (take i xs) p q ** Ps
      \<turnstile> (olseg A (take i xs) p q ** \<upharpoonleft>ll_bpto (Node c r) q ** A (xs ! i) c) ** Qs\<close>
    using conj_entails_mono[OF entails_refl H'] unfolding sep_conj_assoc .
  have 2: \<open>(olseg A (take i xs) p q ** \<upharpoonleft>ll_bpto (Node c r) q ** A (xs ! i) c) ** Qs
      \<turnstile> olseg A (take (Suc i) xs) p r ** Qs\<close>
    using conj_entails_mono[OF olseg_snoc entails_refl, of A \<open>take i xs\<close> p q c r \<open>xs ! i\<close> Qs]
    by (simp add: take_Suc_conv_app_nth[OF I])
  show \<open>olseg A (take i xs) p q ** Ps \<turnstile> olseg A (take (Suc i) xs) p r ** Qs\<close>
    by (rule entails_trans[OF 1 2])
qed

lemma olseg_cl_reassemble_red:
  \<open>is_sep_red \<box> (cl_assn' A (drop i xs) q) (olseg A (take i xs) p q) (cl_assn' A xs p)\<close>
proof (rule is_sep_redI)
  fix Ps Qs
  assume H: \<open>\<box> ** Ps \<turnstile> cl_assn' A (drop i xs) q ** Qs\<close>
  have H': \<open>Ps \<turnstile> olseg A (drop i xs) q null ** Qs\<close>
    using H by (simp add: cl_assn_olseg)
  have 1: \<open>olseg A (take i xs) p q ** Ps
      \<turnstile> (olseg A (take i xs) p q ** olseg A (drop i xs) q null) ** Qs\<close>
    using conj_entails_mono[OF entails_refl H'] unfolding sep_conj_assoc .
  have 2: \<open>(olseg A (take i xs) p q ** olseg A (drop i xs) q null) ** Qs
      \<turnstile> cl_assn' A xs p ** Qs\<close>
    using conj_entails_mono[OF olseg_append entails_refl, of A \<open>take i xs\<close> p q \<open>drop i xs\<close> null Qs]
    by (simp add: cl_assn_olseg)
  show \<open>olseg A (take i xs) p q ** Ps \<turnstile> cl_assn' A xs p ** Qs\<close>
    by (rule entails_trans[OF 1 2])
qed

lemma cl_assn'_cons_red:
  \<open>PRECOND (SOLVE_AUTO (i < length xs)) \<Longrightarrow>
    is_sep_red \<box> (A (xs ! i) c ** cl_assn' A (drop (Suc i) xs) q)
      (\<upharpoonleft>ll_bpto (Node c q) p) (cl_assn' A (drop i xs) p)\<close>
  unfolding vcg_tag_defs
proof (rule is_sep_redI)
  fix Ps Qs
  assume I: \<open>i < length xs\<close>
    and H: \<open>\<box> ** Ps \<turnstile> (A (xs ! i) c ** cl_assn' A (drop (Suc i) xs) q) ** Qs\<close>
  have H': \<open>Ps \<turnstile> A (xs ! i) c ** cl_assn' A (drop (Suc i) xs) q ** Qs\<close>
    using H by simp
  have E: \<open>cl_assn' A (drop i xs) p
      = (EXS c q. \<upharpoonleft>ll_bpto (Node c q) p ** A (xs ! i) c ** cl_assn' A (drop (Suc i) xs) q)\<close>
    by (subst Cons_nth_drop_Suc[OF I, symmetric]) (simp add: cl_assn_simps)
  have 1: \<open>\<upharpoonleft>ll_bpto (Node c q) p ** Ps
      \<turnstile> (\<upharpoonleft>ll_bpto (Node c q) p ** A (xs ! i) c ** cl_assn' A (drop (Suc i) xs) q) ** Qs\<close>
    using conj_entails_mono[OF entails_refl H'] unfolding sep_conj_assoc .
  have 2: \<open>\<upharpoonleft>ll_bpto (Node c q) p ** A (xs ! i) c ** cl_assn' A (drop (Suc i) xs) q
      \<turnstile> cl_assn' A (drop i xs) p\<close>
    unfolding E
    by (rule entails_exI[where x=c], rule entails_exI[where x=q], rule entails_refl)
  show \<open>\<upharpoonleft>ll_bpto (Node c q) p ** Ps \<turnstile> cl_assn' A (drop i xs) p ** Qs\<close>
    by (rule entails_trans[OF 1 conj_entails_mono[OF 2 entails_refl]])
qed

context begin

private lemma cl_assn'_cong_fri:
  \<open>PRECOND (SOLVE_AUTO (a = a')) \<Longrightarrow> cl_assn' A a c \<turnstile> cl_assn' A a' c\<close>
  unfolding vcg_tag_defs by simp

private lemma olseg_empty_fri:
  \<open>PRECOND (SOLVE_AUTO (ys = [] \<and> p = q)) \<Longrightarrow> \<box> \<turnstile> olseg A ys p q\<close>
  unfolding vcg_tag_defs by (simp add: olseg_nil sep_algebra_simps)

private lemma olseg_cl_fri:
  \<open>PRECOND (SOLVE_AUTO (ys = xs)) \<Longrightarrow> olseg A ys p null \<turnstile> cl_assn' A xs p\<close>
  unfolding vcg_tag_defs by (simp add: cl_assn_olseg)

private lemma drop_head:
  \<open>i < length xs \<Longrightarrow> drop i xs = xs ! i # drop (Suc i) xs\<close>
  by (simp add: Cons_nth_drop_Suc)

lemma cl_ifoldl_rule:
  assumes F: \<open>\<And>a ai b bi c ci d di. llvm_htriple
    (A a ai ** B b bi ** C c ci ** dir_assn d di)
    (fi ai bi ci di)
    (\<lambda>r. A (f a b c d) r ** B b bi ** C c ci)\<close>
    and DEC: \<open>\<And>b bi c ci. llvm_htriple
    (B b bi ** C c ci)
    (deci bi ci)
    (\<lambda>r. dir_assn (dec b c) r ** B b bi ** C c ci)\<close>
    and F1: \<open>\<And>a ai b bi. llvm_htriple
    (A a ai ** B b bi)
    (f1i ai bi)
    (\<lambda>r. A (f1 a b) r ** B b bi)\<close>
    and F2: \<open>\<And>a ai c ci. llvm_htriple
    (A a ai ** C c ci)
    (f2i ai ci)
    (\<lambda>r. A (f2 a c) r ** C c ci)\<close>
  shows \<open>llvm_htriple
    (A acc acci ** cl_assn' B bs bsi ** cl_assn' C cs csi)
    (cl_ifoldl fi deci f1i f2i acci bsi csi)
    (\<lambda>r. A (ifoldl f dec f1 f2 acc bs cs) r ** cl_assn' B bs bsi ** cl_assn' C cs csi)\<close>
proof -
  interpret llvm_prim_ctrl_setup .
  show ?thesis
  unfolding cl_ifoldl_def
  apply (rewrite annotate_llc_while [where
    I = \<open>\<lambda>(acci', xp, yp, stop) t. EXS i j acc'.
        A acc' acci'
        ** olseg B (take i bs) bsi xp ** olseg C (take j cs) csi yp
        ** cl_assn' B (drop i bs) xp ** cl_assn' C (drop j cs) yp
        ** \<up>((if stop = 0
               then ifoldl f dec f1 f2 acc' (drop i bs) (drop j cs)
               else acc')
              = ifoldl f dec f1 f2 acc bs cs)
        ** \<up>\<^sub>!(t = (if stop = 0 then Suc (length bs - i + (length cs - j)) else 0))\<close>
    and R = \<open>measure id\<close>])
  supply [vcg_rules] = F DEC ll_icmp_eq_bool_rule cl_assn'_load_rule
    cl_fold_monadic'_rule[where A=A and B=B and fi=f1i and f=f1, OF F1]
    cl_fold_monadic'_rule[where A=A and B=C and fi=f2i and f=f2, OF F2]
  supply [simp] = cl_assn_simps olseg_nil sep_conj_exists drop_head
    hd_drop_conv_nth drop_Suc[symmetric] ifoldl_Nil1 ifoldl_Nil2
  supply [fri_rules] = cl_assn'_cong_fri olseg_empty_fri olseg_cl_fri
  supply [fri_red_rules] = olseg_snoc_red olseg_cl_reassemble_red cl_assn'_cons_red
  apply vcg_monadify
  apply vcg'
  subgoal for aa ab x xa
    by (cases \<open>dec (bs ! x) (cs ! xa)\<close>) auto
  done
qed


subsection \<open>Refinement rule for @{term cl_ifoldl} against @{term ifoldl_nres}\<close>
lemma cl_ifoldl_nres_rule:
  assumes F: \<open>\<And>a ai b bi c ci d di. nofail (fn a b c d) \<Longrightarrow> llvm_htriple
    (A a ai ** B b bi ** C c ci ** dir_assn d di)
    (fi ai bi ci di)
    (\<lambda>r. B b bi ** C c ci ** (EXS x. A x r ** \<up>(RETURN x \<le> fn a b c d)))\<close>
    and DEC: \<open>\<And>b bi c ci. nofail (decn b c) \<Longrightarrow> llvm_htriple
    (B b bi ** C c ci)
    (deci bi ci)
    (\<lambda>r. B b bi ** C c ci ** (EXS d. dir_assn d r ** \<up>(RETURN d \<le> decn b c)))\<close>
    and F1: \<open>\<And>a ai b bi. nofail (f1n a b) \<Longrightarrow> llvm_htriple
    (A a ai ** B b bi)
    (f1i ai bi)
    (\<lambda>r. B b bi ** (EXS x. A x r ** \<up>(RETURN x \<le> f1n a b)))\<close>
    and F2: \<open>\<And>a ai c ci. nofail (f2n a c) \<Longrightarrow> llvm_htriple
    (A a ai ** C c ci)
    (f2i ai ci)
    (\<lambda>r. C c ci ** (EXS x. A x r ** \<up>(RETURN x \<le> f2n a c)))\<close>
    and NF: \<open>nofail (ifoldl_nres fn decn f1n f2n acc bs cs)\<close>
  shows \<open>llvm_htriple
    (A acc acci ** cl_assn' B bs bsi ** cl_assn' C cs csi)
    (cl_ifoldl fi deci f1i f2i acci bsi csi)
    (\<lambda>r. cl_assn' B bs bsi ** cl_assn' C cs csi
      ** (EXS x. A x r ** \<up>(RETURN x \<le> ifoldl_nres fn decn f1n f2n acc bs cs)))\<close>
proof -
  interpret llvm_prim_ctrl_setup .
  show ?thesis
  using NF
  unfolding cl_ifoldl_def
  apply (rewrite annotate_llc_while [where
    I = \<open>\<lambda>(acci', xp, yp, stop) t. EXS i j acc'.
        A acc' acci'
        ** olseg B (take i bs) bsi xp ** olseg C (take j cs) csi yp
        ** cl_assn' B (drop i bs) xp ** cl_assn' C (drop j cs) yp
        ** \<up>((if stop = 0
               then ifoldl_nres fn decn f1n f2n acc' (drop i bs) (drop j cs)
               else RETURN acc')
              \<le> ifoldl_nres fn decn f1n f2n acc bs cs)
        ** \<up>\<^sub>!(t = (if stop = 0 then Suc (length bs - i + (length cs - j)) else 0))\<close>
    and R = \<open>measure id\<close>])
  supply [vcg_rules] = F DEC ll_icmp_eq_bool_rule cl_assn'_load_rule
    cl_fold_monadic'_nres_rule'[where A=A and B=B and fi=f1i and f=f1n, OF F1]
    cl_fold_monadic'_nres_rule'[where A=A and B=C and fi=f2i and f=f2n, OF F2]
  supply [simp] = cl_assn_simps olseg_nil sep_conj_exists drop_head
    hd_drop_conv_nth drop_Suc[symmetric] ifoldl_nres_Nil1 ifoldl_nres_Nil2 ifoldl_nres_Cons
    pw_le_iff refine_pw_simps
  supply [fri_rules] = cl_assn'_cong_fri olseg_empty_fri olseg_cl_fri
  supply [fri_red_rules] = olseg_snoc_red olseg_cl_reassemble_red cl_assn'_cons_red
  apply vcg_monadify
  apply vcg'
  apply (auto split: direction.splits)
  subgoal by blast
  subgoal by blast
  subgoal by blast
  subgoal by (meson direction.exhaust)
  subgoal by metis
  done
qed

end

subsection \<open>hfref forms\<close>

lemma hfref_nres_htriple_d1_k2_k3_k4:
  assumes R: \<open>(uncurry3 fi, uncurry3 fn) \<in> A\<^sup>d *\<^sub>a B\<^sup>k *\<^sub>a C\<^sup>k *\<^sub>a dir_assn\<^sup>k \<rightarrow>\<^sub>a A\<close>
    and NF: \<open>nofail (fn a b c d)\<close>
  shows \<open>llvm_htriple (A a ai ** B b bi ** C c ci ** dir_assn d di) (fi ai bi ci di)
    (\<lambda>r. B b bi ** C c ci ** (EXS x. A x r ** \<up>(RETURN x \<le> fn a b c d)))\<close>
proof -
  note HT = R[to_hnr, unfolded autoref_tag_defs, THEN hn_refineD, OF NF]
  show ?thesis
    apply (rule htriple_ent_pre[OF _ htriple_ent_post[OF _ HT]])
    unfolding hn_ctxt_def
    subgoal by (rule entails_refl)
    subgoal
      by (auto simp: entails_def sep_algebra_simps sep_conj_exists invalid_assn_def
          pred_lift_extract_simps)
    done
qed

lemma hfref_nres_htriple_k1_k2:
  assumes R: \<open>(uncurry fi, uncurry fn) \<in> B\<^sup>k *\<^sub>a C\<^sup>k \<rightarrow>\<^sub>a D\<close>
    and NF: \<open>nofail (fn b c)\<close>
  shows \<open>llvm_htriple (B b bi ** C c ci) (fi bi ci)
    (\<lambda>r. B b bi ** C c ci ** (EXS x. D x r ** \<up>(RETURN x \<le> fn b c)))\<close>
proof -
  note HT = R[to_hnr, unfolded autoref_tag_defs, THEN hn_refineD, OF NF]
  show ?thesis
    apply (rule htriple_ent_pre[OF _ htriple_ent_post[OF _ HT]])
    unfolding hn_ctxt_def
    subgoal by (rule entails_refl)
    subgoal
      by (auto simp: entails_def sep_algebra_simps sep_conj_exists
          pred_lift_extract_simps)
    done
qed

lemma hfref_nres_htriple_d1_k2:
  assumes R: \<open>(uncurry fi, uncurry fn) \<in> A\<^sup>d *\<^sub>a B\<^sup>k \<rightarrow>\<^sub>a A\<close>
    and NF: \<open>nofail (fn a b)\<close>
  shows \<open>llvm_htriple (A a ai ** B b bi) (fi ai bi)
    (\<lambda>r. B b bi ** (EXS x. A x r ** \<up>(RETURN x \<le> fn a b)))\<close>
proof -
  note HT = R[to_hnr, unfolded autoref_tag_defs, THEN hn_refineD, OF NF]
  show ?thesis
    apply (rule htriple_ent_pre[OF _ htriple_ent_post[OF _ HT]])
    unfolding hn_ctxt_def
    subgoal by (rule entails_refl)
    subgoal
      by (auto simp: entails_def sep_algebra_simps sep_conj_exists invalid_assn_def
          pred_lift_extract_simps)
    done
qed

lemma cl_ifoldl_nres_hfref:
  assumes F: \<open>(uncurry3 fi, uncurry3 fn) \<in> A\<^sup>d *\<^sub>a B\<^sup>k *\<^sub>a C\<^sup>k *\<^sub>a dir_assn\<^sup>k \<rightarrow>\<^sub>a A\<close>
    and DEC: \<open>(uncurry deci, uncurry decn) \<in> B\<^sup>k *\<^sub>a C\<^sup>k \<rightarrow>\<^sub>a dir_assn\<close>
    and F1: \<open>(uncurry f1i, uncurry f1n) \<in> A\<^sup>d *\<^sub>a B\<^sup>k \<rightarrow>\<^sub>a A\<close>
    and F2: \<open>(uncurry f2i, uncurry f2n) \<in> A\<^sup>d *\<^sub>a C\<^sup>k \<rightarrow>\<^sub>a A\<close>
  shows \<open>(uncurry2 (cl_ifoldl fi deci f1i f2i), uncurry2 (ifoldl_nres fn decn f1n f2n))
    \<in> A\<^sup>d *\<^sub>a (cl_assn' B)\<^sup>k *\<^sub>a (cl_assn' C)\<^sup>k \<rightarrow>\<^sub>a A\<close>
  supply [vcg_rules] = cl_ifoldl_nres_rule[where A=A and B=B and C=C
      and fi=fi and deci=deci and f1i=f1i and f2i=f2i
      and fn=fn and decn=decn and f1n=f1n and f2n=f2n,
      OF hfref_nres_htriple_d1_k2_k3_k4[OF F] hfref_nres_htriple_k1_k2[OF DEC]
         hfref_nres_htriple_d1_k2[OF F1] hfref_nres_htriple_d1_k2[OF F2]]
  by (sepref_to_hoare; vcg)

text \<open>The functional variant follows by monotonicity of \<open>hfref\<close> in the
  abstract program, via @{thm ifoldl_nres_refine}.\<close>
lemma cl_ifoldl_hfref:
  assumes F: \<open>(uncurry3 fi, uncurry3 (RETURN oooo f))
      \<in> A\<^sup>d *\<^sub>a B\<^sup>k *\<^sub>a C\<^sup>k *\<^sub>a dir_assn\<^sup>k \<rightarrow>\<^sub>a A\<close>
    and DEC: \<open>(uncurry deci, uncurry (RETURN oo dec)) \<in> B\<^sup>k *\<^sub>a C\<^sup>k \<rightarrow>\<^sub>a dir_assn\<close>
    and F1: \<open>(uncurry f1i, uncurry (RETURN oo f1)) \<in> A\<^sup>d *\<^sub>a B\<^sup>k \<rightarrow>\<^sub>a A\<close>
    and F2: \<open>(uncurry f2i, uncurry (RETURN oo f2)) \<in> A\<^sup>d *\<^sub>a C\<^sup>k \<rightarrow>\<^sub>a A\<close>
  shows \<open>(uncurry2 (cl_ifoldl fi deci f1i f2i), uncurry2 (RETURN ooo ifoldl f dec f1 f2))
    \<in> A\<^sup>d *\<^sub>a (cl_assn' B)\<^sup>k *\<^sub>a (cl_assn' C)\<^sup>k \<rightarrow>\<^sub>a A\<close>
proof -
  note M = cl_ifoldl_nres_hfref[OF F DEC F1 F2]
  have LE: \<open>ifoldl_nres (RETURN oooo f) (RETURN oo dec) (RETURN oo f1) (RETURN oo f2)
      acc bs cs \<le> RETURN (ifoldl f dec f1 f2 acc bs cs)\<close> for acc bs cs
    by (rule order_trans[OF ifoldl_nres_refine]) (simp_all add: pw_le_iff refine_pw_simps)
  show ?thesis
    apply (rule hfrefI)
    apply (rule hn_refine_ref[OF _ hfrefD[OF M]])
    by (auto simp: LE)
qed

subsection \<open>Sepref setup for @{typ direction}\<close>

lemma dir_enc_inj[simp]: \<open>dir_enc d = dir_enc d' \<longleftrightarrow> d = d'\<close>
  by (cases d; cases d'; simp)

lemma dir_assn_is_pure[safe_constraint_rules]: \<open>is_pure dir_assn\<close>
  unfolding dir_assn_def by simp

lemma dir_assn_free[sepref_frame_free_rules]: \<open>MK_FREE dir_assn (\<lambda>_. Mreturn ())\<close>
  unfolding dir_assn_def by (rule mk_free_pure)

sepref_register STOP LEFT RIGHT BOTH
sepref_register eq_dir: \<open>(=) :: direction \<Rightarrow> _\<close> :: \<open>direction \<Rightarrow> direction \<Rightarrow> bool\<close>

lemma dir_const_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn (0 :: 8 word)), uncurry0 (RETURN STOP)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a dir_assn\<close>
  \<open>(uncurry0 (Mreturn (1 :: 8 word)), uncurry0 (RETURN LEFT)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a dir_assn\<close>
  \<open>(uncurry0 (Mreturn (2 :: 8 word)), uncurry0 (RETURN RIGHT)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a dir_assn\<close>
  \<open>(uncurry0 (Mreturn (3 :: 8 word)), uncurry0 (RETURN BOTH)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a dir_assn\<close>
  by (sepref_to_hoare; vcg)+

lemma dir_eq_hnr[sepref_fr_rules]:
  \<open>(uncurry ll_icmp_eq, uncurry (RETURN oo (=))) \<in> dir_assn\<^sup>k *\<^sub>a dir_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [vcg_rules] = ll_icmp_eq_bool_rule
  supply [simp] = pure_def bool1_rel_def bool.rel_def in_br_conv
  by (sepref_to_hoare; vcg)

experiment
begin

text \<open>Non-monadic test refinement\<close>
abbreviation \<open>u8_assn \<equiv> unat_assn' TYPE(8)\<close>
definition \<open>ftest a b c dir \<equiv>
  if dir = STOP then a
  else if dir = LEFT then c # b # a
  else if dir = RIGHT then b # c # a
  else b # a
\<close>
sepref_def ftest_impl is \<open>uncurry3 (RETURN oooo ftest)\<close>
  :: \<open>(cl_assn' u8_assn)\<^sup>d *\<^sub>a u8_assn\<^sup>k *\<^sub>a u8_assn\<^sup>k *\<^sub>a dir_assn\<^sup>k \<rightarrow>\<^sub>a (cl_assn' u8_assn)\<close>
  unfolding ftest_def
  by sepref

definition \<open>dirtest a b \<equiv>
  if a = b then BOTH
  else if a < b then LEFT
  else RIGHT
\<close>
sepref_def dirtest_impl is \<open>uncurry (RETURN oo dirtest)\<close>
  :: \<open>u8_assn\<^sup>k *\<^sub>a u8_assn\<^sup>k \<rightarrow>\<^sub>a dir_assn\<close>
  unfolding dirtest_def
  by sepref

definition \<open>f1test a b = b # a\<close>
sepref_def f1test_impl is \<open>uncurry (RETURN oo f1test)\<close>
  :: \<open>(cl_assn' u8_assn)\<^sup>d *\<^sub>a u8_assn\<^sup>k \<rightarrow>\<^sub>a cl_assn' u8_assn\<close>
  unfolding f1test_def
  by sepref

definition \<open>f2test a c = c # a\<close>
sepref_def f2test_impl is \<open>uncurry (RETURN oo f2test)\<close>
  :: \<open>(cl_assn' u8_assn)\<^sup>d *\<^sub>a u8_assn\<^sup>k \<rightarrow>\<^sub>a cl_assn' u8_assn\<close>
  unfolding f2test_def
  by sepref

definition \<open>test_ifoldl \<equiv> ifoldl ftest dirtest f1test f2test\<close>
sepref_register test_ifoldl

lemmas test_ifoldl_hnr[sepref_fr_rules] =
  cl_ifoldl_hfref[OF ftest_impl.refine dirtest_impl.refine f1test_impl.refine f2test_impl.refine,
    folded test_ifoldl_def]

definition \<open>test \<equiv> ifoldl ftest dirtest f1test f2test []\<close>

sepref_def test_impl is \<open>uncurry (RETURN oo test)\<close>
  :: \<open>(cl_assn' u8_assn)\<^sup>k *\<^sub>a (cl_assn' u8_assn)\<^sup>k \<rightarrow>\<^sub>a cl_assn' u8_assn\<close>
  unfolding test_def test_ifoldl_def[symmetric]
  by sepref

end

end
