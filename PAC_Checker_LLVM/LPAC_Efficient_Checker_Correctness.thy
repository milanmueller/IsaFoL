theory LPAC_Efficient_Checker_Correctness
  imports
    LPAC_Efficient_Checker_Synthesis
begin

text \<open>Final correctness theorem of the efficient LPAC checker, combining the
  refinement chain of \<open>LPAC_Efficient_Checker_Refinement\<close> with the synthesis
  of \<open>LPAC_Efficient_Checker_Synthesis\<close>.\<close>

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
