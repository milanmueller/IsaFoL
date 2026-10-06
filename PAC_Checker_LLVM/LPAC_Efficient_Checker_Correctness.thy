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

text \<open>The assertions of the three inputs relate the LLVM data structures directly to the
  abstract objects of the specification: the specification polynomial, the map of input
  polynomials, and the list of proof steps.\<close>

definition full_poly_assn where
  \<open>full_poly_assn = hr_comp polynomiala_assn (fully_unsorted_poly_rel O mset_poly_rel)\<close>

definition full_poly_input_assn where
  \<open>full_poly_input_assn = hr_comp polysa_assn (unsorted_fmap_polys_rel O polys_rel)\<close>

definition fully_epac_assn where
  \<open>fully_epac_assn = hr_comp (cl_assn' lpac_stepa_assn) (\<langle>epac_step_rel\<rangle>list_rel)\<close>

text \<open>

Below is the full correctness theorems. It basically states that:
  \<^enum> assuming that the input polynomials have no duplicate variables

The theorem has no precondition on the identifiers of the proof steps. Identifiers are stored
in signed 64-bit words; a step that introduces an identifier \<ge> 2^63-1 is rejected at runtime
with \<^term>\<open>CFAILED\<close> (see \<^term>\<open>step_id_overflow\<close>). This is new, compared to the SML backend.

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
  define c :: \<open>memory_allocation \<times> (nat, string) shared_vars \<times> string list \<Rightarrow> bool\<close> where
    \<open>c = (\<lambda>(mem, \<V>, vs). \<not>alloc_failed mem \<and> vs \<noteq> [])\<close>
  define b :: \<open>memory_allocation \<times> (nat, string) shared_vars \<times> string list \<Rightarrow> _\<close> where
    \<open>b = (\<lambda>(_, \<V>, vs). do {
      ASSERT(vs \<noteq> []);
      let v = hd vs;
      a \<leftarrow> is_new_variableS v \<V>;
      if \<not>a then RETURN (Allocated ,\<V>, tl vs)
      else do {
        (mem, \<V>, _) \<leftarrow> import_variableS v \<V>;
        RETURN(mem, \<V>, tl vs)
      }
    })\<close>
  have def: \<open>import_variablesS vs \<V> = do {
      (mem, \<V>, _) \<leftarrow> WHILE\<^sub>T c b (Allocated, \<V>, vs); RETURN (mem, \<V>)}\<close> for vs \<V>
    unfolding import_variablesS_def c_def b_def ..
  have exit: \<open>WHILE\<^sub>T c b (Mem_Out, \<V>0, vs0) = RETURN (Mem_Out, \<V>0, vs0)\<close> for \<V>0 vs0
    by (subst WHILET_unfold) (auto simp: c_def)
  have step: \<open>WHILE\<^sub>T c b (Allocated, \<V>, v # vs) = b (Allocated, \<V>, v # vs) \<bind> WHILE\<^sub>T c b\<close>
    by (subst WHILET_unfold) (auto simp: c_def)
  have tail: \<open>WHILE\<^sub>T c b (mem, \<V>', vs) \<bind> (\<lambda>(mem, \<V>, _). RETURN (mem, \<V>)) =
      (if alloc_failed mem then RETURN (mem, \<V>') else import_variablesS vs \<V>')\<close> for mem \<V>'
    by (cases mem) (auto simp: exit def)
  have body: \<open>b (Allocated, \<V>, v # vs) = do {
      a \<leftarrow> is_new_variableS v \<V>;
      if \<not>a then RETURN (Allocated, \<V>, vs)
      else do {
        (mem, \<V>, _) \<leftarrow> import_variableS v \<V>;
        RETURN (mem, \<V>, vs)
      }}\<close>
    by (auto simp: b_def intro!: bind_cong[OF refl])
  show ?thesis
    unfolding def[of \<open>v # vs\<close>] step body
    by (cases \<V>)
      (auto simp: is_new_variableS_def tail intro!: bind_cong[OF refl])
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

lemma import_poly_varsS_Cons:
  \<open>import_poly_varsS \<V> ((m, c) # p) = do {
     (mem, \<V>) \<leftarrow> import_variablesS m \<V>;
     if alloc_failed mem then RETURN (mem, \<V>) else import_poly_varsS \<V> p
  }\<close>
proof -
  define cnd :: \<open>memory_allocation \<times> (nat, string) shared_vars \<times> llist_polynomial \<Rightarrow> bool\<close> where
    \<open>cnd = (\<lambda>(mem, \<V>, p). \<not>alloc_failed mem \<and> p \<noteq> [])\<close>
  define bdy :: \<open>memory_allocation \<times> (nat, string) shared_vars \<times> llist_polynomial \<Rightarrow> _\<close> where
    \<open>bdy = (\<lambda>(_, \<V>, p). do {
       ((m, c), p) \<leftarrow> mop_list_pop_hd p;
       (mem, \<V>) \<leftarrow> import_variablesS m \<V>;
       RETURN (mem, \<V>, p)
     })\<close>
  have def: \<open>import_poly_varsS \<V> p = do {
      (mem, \<V>, _) \<leftarrow> WHILE\<^sub>T cnd bdy (Allocated, \<V>, p); RETURN (mem, \<V>)}\<close> for \<V> p
    unfolding import_poly_varsS_def COPY_def id_apply nres_monad1 cnd_def bdy_def ..
  have exit: \<open>WHILE\<^sub>T cnd bdy (Mem_Out, \<V>0, p0) = RETURN (Mem_Out, \<V>0, p0)\<close> for \<V>0 p0
    by (subst WHILET_unfold) (auto simp: cnd_def)
  have step: \<open>WHILE\<^sub>T cnd bdy (Allocated, \<V>, (m, c) # p) =
      bdy (Allocated, \<V>, (m, c) # p) \<bind> WHILE\<^sub>T cnd bdy\<close>
    by (subst WHILET_unfold) (auto simp: cnd_def)
  have tail: \<open>WHILE\<^sub>T cnd bdy (mem, \<V>', p) \<bind> (\<lambda>(mem, \<V>, _). RETURN (mem, \<V>)) =
      (if alloc_failed mem then RETURN (mem, \<V>') else import_poly_varsS \<V>' p)\<close> for mem \<V>'
    by (cases mem) (auto simp: exit def)
  have body: \<open>bdy (Allocated, \<V>, (m, c) # p) = do {
      (mem, \<V>) \<leftarrow> import_variablesS m \<V>;
      RETURN (mem, \<V>, p)}\<close>
    by (auto simp: bdy_def mop_list_pop_hd_def intro!: bind_cong[OF refl])
  show ?thesis
    unfolding def[of _ \<open>(m, c) # p\<close>] step body
    by (auto simp: tail intro!: bind_cong[OF refl])
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
    \<in> (Id \<times>\<^sub>r Id) \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
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
    apply (rule id)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule id)
    subgoal by auto
    done
qed

lemmas full_checker_l_s2_spec_chain = full_checker_l_s2_full_checker_l_s[
      FCOMP full_checker_l_s_full_checker_l_prep',
      FCOMP full_checker_l_prep_full_checker_l2',
      FCOMP full_checker_l_full_checker',
      FCOMP full_checker_spec']

lemma full_checker_l_s2_spec:
  \<open>(uncurry2 full_checker_l_s2, uncurry2 (\<lambda>spec A _. PAC_checker_specification spec A))
    \<in> ((fully_unsorted_poly_rel O mset_poly_rel) \<times>\<^sub>r (unsorted_fmap_polys_rel O polys_rel)) \<times>\<^sub>r
       \<langle>epac_step_rel\<rangle>list_rel \<rightarrow>\<^sub>f
    \<langle>{((err, _), err', _). (err, err') \<in> code_status_status_rel}\<rangle>nres_rel\<close>
proof -
  have 2: \<open>A \<subseteq> B \<Longrightarrow> \<langle>A\<rangle>nres_rel \<subseteq> \<langle>B\<rangle>nres_rel\<close> for A B
    by (auto simp: nres_rel_def conc_fun_R_mono conc_trans_additional(6))
  have 4: \<open>\<langle>nat_rel, Id\<rangle>fmap_rel = Id\<close>
    apply (auto simp: fmap_rel_def)
    by (metis (no_types, opaque_lifting) fmap_ext_fmdom fmlookup_dom_iff fset_eqI option.sel)
  show ?thesis
    apply (rule set_mp[OF _ full_checker_l_s2_spec_chain])
    unfolding fref_param1[symmetric]
    apply (rule fun_rel_mono)
    subgoal by (auto simp: 4)
    apply (rule 2)
    apply auto
    done
qed

theorem PAC_full_correctness: (* \htmllink{PAC-full-correctness} *)
  \<open>(uncurry2 full_checker_l_s2_impl,
     uncurry2 (\<lambda>spec A _. PAC_checker_specification spec A))
  \<in> full_poly_assn\<^sup>k *\<^sub>a full_poly_input_assn\<^sup>k *\<^sub>a fully_epac_assn\<^sup>d \<rightarrow>\<^sub>a
    hr_comp (status_assn \<times>\<^sub>a shared_vars_assn \<times>\<^sub>a polys_s_assn)
      {((err, _), err', _). (err, err') \<in> code_status_status_rel}\<close>
  using full_checker_l_s2_impl.refine[FCOMP full_checker_l_s2_spec]
  unfolding full_poly_assn_def[symmetric] full_poly_input_assn_def[symmetric]
    fully_epac_assn_def[symmetric]
  .

end

end
