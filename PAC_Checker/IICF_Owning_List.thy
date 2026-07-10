section \<open>Owning Open Lists \<emdash> Design Sketch\<close>
theory IICF_Owning_List
  imports IICF_Open_List Isabelle_LLVM.Proto_IICF_EOArray
begin

text \<open>An open list whose elements may themselves own heap (in particular: nested lists),
  complementing \<open>os_assn\<close> from \<open>IICF_Open_List\<close>, which is restricted to pure element
  assertions.\<close>

subsection \<open>The Owning List Assertion\<close>

text \<open>Owning list segment: a spine of nodes holding concrete values \<open>xsi\<close>, plus element-wise
  ownership \<open>A\<close> between the abstract list \<open>xs\<close> and \<open>xsi\<close>. We reuse
  \<^const>\<open>Proto_EOArray.list_assn\<close> (element-wise big-star) for the second part, so all its
  cons/append/extract lemmas apply.\<close>

definition ol_seg :: \<open>('a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn) \<Rightarrow> 'a list \<Rightarrow> 'c os_list \<Rightarrow> 'c os_list \<Rightarrow> assn\<close>
  where \<open>ol_seg A xs p s \<equiv> EXS xsi. lseg xsi p s ** \<upharpoonleft>(Proto_EOArray.list_assn (mk_assn A)) xs xsi\<close>

definition ol_list_assn :: \<open>('a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn) \<Rightarrow> ('a list, 'c os_list) dr_assn\<close>
  where \<open>ol_list_assn A \<equiv> mk_assn (\<lambda>xs p. ol_seg A xs p null)\<close>

definition ol_assn :: \<open>('a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn) \<Rightarrow> 'a list \<Rightarrow> 'c os_list \<Rightarrow> assn\<close>
  where \<open>ol_assn A \<equiv> \<upharpoonleft>(ol_list_assn A)\<close>

lemma ol_assn_conv: \<open>ol_assn A xs p = ol_seg A xs p null\<close>
  unfolding ol_assn_def ol_list_assn_def by simp

text \<open>The key lemma for all raw-rule proofs below: an owning list is a plain open list of
  concrete values plus element-wise ownership. Rewriting a triple with this exposes
  \<open>\<upharpoonleft>os_list_assn\<close>, so the \<^emph>\<open>existing\<close> vcg rules from \<open>LLVM_DS_Open_List\<close>/\<open>IICF_Open_List\<close>
  (including the while-loop rules) apply verbatim, no loop proof is ever redone.\<close>

lemma ol_assn_os_conv:
  \<open>ol_assn A xs p
    = (EXS xsi. \<up>(length xsi = length xs) ** \<upharpoonleft>os_list_assn xsi p
        ** \<upharpoonleft>(Proto_EOArray.list_assn (mk_assn A)) xs xsi)\<close>
  unfolding ol_assn_conv ol_seg_def os_list_assn_def Proto_EOArray.list_assn_def
  by (auto simp: sep_algebra_simps pred_lift_extract_simps fun_eq_iff)

text \<open>Hoisting an existential out of a Hoare-triple precondition (no library rule exists;
  vcg does this internally via @{thm STATE_extract}, but for hand-composed proofs we need
  it as an explicit rule).\<close>

lemma htriple_pre_EXS:
  assumes \<open>\<And>x. llvm_htriple (P x) c Q\<close>
  shows \<open>llvm_htriple (EXS x. P x) c Q\<close>
  apply (rule htripleI)
  apply (clarsimp simp only: STATE_extract(3))
  by (rule htripleD[OF assms])

text \<open>Structural characterization, mirroring \<open>os_list_assn_simps\<close> and \<open>list_assn_cc_simp\<close>.\<close>

lemma ol_seg_empty[simp]: \<open>ol_seg A [] p s = \<up>(p = s)\<close>
  unfolding ol_seg_def
  by (auto simp: sep_algebra_simps fun_eq_iff)

text \<open>NOTE (hard-won): equalities that both eliminate a pure equation (\<open>\<up>(xsi = c # cs)\<close>)
  and reorder \<open>**\<close>-atoms MUST be proven in two stages. The AC simps (\<open>sep_conj_c\<close>/\<open>aci\<close>)
  and the \<open>\<up>\<close>-fronting simps inside \<open>sep_algebra_simps\<close> are both commutation rule sets and
  ping-pong into a stack overflow (\<open>Interrupt_Breakdown\<close>) when active together on a term
  containing \<open>\<up>\<close>. Stage 1 eliminates the pures (extraction simps, NO AC), stage 2
  AC-aligns the then pure-free bodies (\<open>sep_conj_c\<close> is safe there).\<close>

lemma ol_seg_cons:
  \<open>ol_seg A (x # xs) p s = (EXS c q. \<upharpoonleft>ll_bpto (Node c q) p ** A x c ** ol_seg A xs q s)\<close>
proof -
  have \<open>ol_seg A (x # xs) p s
      = (EXS c cs. lseg (c # cs) p s ** A x c ** \<upharpoonleft>(Proto_EOArray.list_assn (mk_assn A)) xs cs)\<close>
    unfolding ol_seg_def
    by (auto simp: list_assn_cons1_conv sep_algebra_simps fun_eq_iff)
  also have \<open>\<dots> = (EXS c q. \<upharpoonleft>ll_bpto (Node c q) p ** A x c ** ol_seg A xs q s)\<close>
    unfolding ol_seg_def
    by (auto simp: sep_algebra_simps fun_eq_iff sep_conj_c)
  finally show ?thesis .
qed

lemma ol_seg_cons_null[simp]: \<open>ol_seg A (x # xs) null s = sep_false\<close>
  unfolding ol_seg_def
  by (auto simp: list_assn_cons1_conv sep_algebra_simps fun_eq_iff)

lemma ol_seg_append:
  \<open>ol_seg A (xs @ ys) p s = (EXS q. ol_seg A xs p q ** ol_seg A ys q s)\<close>
proof (induction xs arbitrary: p)
  case Nil
  show ?case
    by (auto simp: sep_algebra_simps)
next
  case (Cons z zs)
  show ?case
    by (auto simp: ol_seg_cons Cons.IH sep_algebra_simps fun_eq_iff sep_conj_c)
qed

lemma ol_seg_pure_partD: \<open>pure_part (ol_seg A xs p s) \<Longrightarrow> xs = [] \<longrightarrow> p = s\<close>
  by (cases xs) auto

text \<open>Sanity check: for pure elements the owning list degenerates to \<open>os_assn\<close>, so nothing
  is lost by switching a use site from \<open>os_assn\<close> to \<open>ol_assn\<close>. Proof via
  @{thm Proto_IICF_EOArray.pure_list_assn_to_rel_conv} (the analog for arrays is
  @{thm Proto_IICF_EOArray.pure_woarray_assn_conv}).\<close>

lemma ol_assn_pure_conv: \<open>is_pure A \<Longrightarrow> ol_assn A = os_assn A\<close>
  apply (intro ext)
  unfolding ol_assn_conv ol_seg_def os_assn_def hr_comp_def os_list_assn_def
  by (auto simp: pure_list_assn_to_rel_conv sep_algebra_simps)

subsection \<open>Deep Deallocation\<close>

text \<open>Freeing an owning list must free the elements, too. The free function is parameterized
  by an element free function \<open>fc\<close>, and the \<open>MK_FREE\<close> rule is \<^emph>\<open>conditional\<close> \<emdash> exactly the
  format the frame infrastructure supports (cf. \<open>mk_free_pair\<close>).

  CAVEAT (code generation): \<open>ol_delete\<close> is higher-order in \<open>fc\<close>; the LLVM code generator
  only handles first-order code. Each concrete instantiation (e.g.
  \<open>ol_delete os_delete\<close> for lists of lists) must be specialized into its own first-order
  \<open>[llvm_code]\<close> definition before export think of \<open>ol_delete\<close> as a template.\<close>

partial_function (M) ol_delete :: \<open>('c::llvm_rep \<Rightarrow> unit llM) \<Rightarrow> 'c os_list \<Rightarrow> unit llM\<close>
  where
  \<open>ol_delete fc p = (if p = null then Mreturn () else doM {
      n \<leftarrow> ll_load p;
      fc (node.val n);
      ll_free p;
      ol_delete fc (node.next n)
    })\<close>

lemma ol_delete_rule:
  assumes A: \<open>MK_FREE A fc\<close>
  shows \<open>llvm_htriple (ol_seg A xs p null) (ol_delete fc p) (\<lambda>_. \<box>)\<close>
proof (induction xs arbitrary: p)
  case Nil
  show ?case
    apply (subst ol_delete.simps)
    by vcg
next
  case (Cons x xs)
  interpret llvm_prim_ctrl_setup .
  note [vcg_rules] = Cons.IH MK_FREED[OF A]
  note [simp] = ol_seg_cons
  show ?case
    apply (subst ol_delete.simps)
    by vcg
qed

lemma ol_assn_free[sepref_frame_free_rules]:
  assumes \<open>MK_FREE A fc\<close>
  shows \<open>MK_FREE (ol_assn A) (ol_delete fc)\<close>
  apply (rule MK_FREEI)
  unfolding ol_assn_conv
  by (rule ol_delete_rule[OF assms])

subsection \<open>Structural Operations\<close>

text \<open>All implementations are the unchanged raw ops from \<open>LLVM_DS_Open_List\<close> /
  \<open>IICF_Open_List\<close>. Two systematic differences to the \<open>os_assn\<close> interface:

  \<^item> \<^emph>\<open>No parametricity composition.\<close> For \<open>os_assn\<close> we proved raw rules with \<open>id_assn\<close>
    elements and let \<open>sepref_decl_impl\<close> compose them with the operation's parametricity
    theorem. That shortcut requires pure \<open>A\<close>. Here the rules are stated (and must be
    proven) directly at the \<open>ol_assn A\<close> level for arbitrary \<open>A\<close>, and are declared
    \<open>[sepref_fr_rules]\<close> by hand; \<open>mop\<close>- and plain-op forms need separate statements.\<close>

text \<open>Front-pop as an interface operation (the owning replacement for \<open>hd\<close>+\<open>tl\<close>;
  analogous to the existing \<^const>\<open>op_list_pop_last\<close>). Implemented by the existing raw
  \<^const>\<open>os_pop\<close> in a single node visit, no traversal.\<close>

context notes [simp] = List.null_iff[symmetric] and [simp del] = List.null_iff begin
  sepref_decl_op list_pop_front: \<open>\<lambda>l. (hd l, tl l)\<close>
    :: \<open>[\<lambda>l. l \<noteq> []]\<^sub>f \<langle>A\<rangle>list_rel \<rightarrow> A \<times>\<^sub>r \<langle>A\<rangle>list_rel\<close> .
end

text \<open>IMPORTANT (found the hard way, see the regression test below): \<open>empty\<close> must NOT be
  registered against the generic \<open>op_list_empty\<close>. A producer op has no argument that pins
  down the result assertion, so a rule \<open>\<dots> \<rightarrow>\<^sub>a ol_assn ?A\<close> matches \<^emph>\<open>every\<close> \<open>[]\<close> in every
  synthesis (it is tried before the \<open>os_assn\<close> rule, being declared later) and leaves an
  uninstantiated \<open>ol_assn ?A\<close> that a later consumer (e.g. \<open>prepend\<close> into an \<open>os_assn\<close> list)
  can never unify away \<emdash> sepref does not backtrack across committed operator steps.
  Consumer rules are unaffected: their argument's \<open>hn_ctxt\<close> disambiguates by unification.
  Solution: the \<open>list_custom_empty\<close> idiom from \<open>IICF_List\<close> \<emdash> a per-implementation name
  \<open>op_ol_empty\<close>, folded in at use sites via @{text fold_ol_empty}.\<close>

definition op_ol_empty :: \<open>'a list\<close> where [simp]: \<open>op_ol_empty \<equiv> op_list_empty\<close>
sepref_register op_ol_empty

lemma fold_ol_empty:
  \<open>[] = op_ol_empty\<close>
  \<open>op_list_empty = op_ol_empty\<close>
  \<open>mop_list_empty = RETURN op_ol_empty\<close>
  by simp_all

subsubsection \<open>Raw Rules\<close>

text \<open>One-node operations get direct proofs mirroring their \<open>os_list_assn\<close> counterparts,
  with \<open>ol_seg_cons\<close> in place of the \<open>os_list_assn\<close> simps. Loop operations (\<open>length\<close>) are
  NOT re-proven: rewriting with @{thm ol_assn_os_conv} exposes \<open>\<upharpoonleft>os_list_assn\<close>, the
  existing while-loop rule fires on the spine, and the element ownership rides along in
  the frame.\<close>

lemma ol_empty_rule[vcg_rules]: \<open>llvm_htriple \<box> os_empty (\<lambda>r. ol_assn A [] r)\<close>
  unfolding os_empty_def
  supply [simp] = ol_assn_conv
  by vcg

lemma ol_is_empty_rule[vcg_rules]:
  \<open>llvm_htriple (ol_assn A xs p) (os_is_empty p)
    (\<lambda>r. ol_assn A xs p ** \<up>(r = from_bool (xs = [])))\<close>
  unfolding os_is_empty_def
  supply [simp] = ol_assn_conv ol_seg_cons sep_conj_exists
  apply (cases \<open>p = null\<close>; cases xs; simp)
  by vcg

lemma ol_prepend_rule[vcg_rules]:
  \<open>llvm_htriple (A x c ** ol_assn A xs p) (os_prepend c p) (\<lambda>r. ol_assn A (x # xs) r)\<close>
  unfolding os_prepend_def
  supply [simp] = ol_assn_conv
  supply [named_ss fri_prepare_simps] = ol_seg_cons
  by vcg

lemma ol_pop_rule[vcg_rules]:
  \<open>xs \<noteq> [] \<Longrightarrow> llvm_htriple (ol_assn A xs p) (os_pop p)
    (\<lambda>(ci, r). A (hd xs) ci ** ol_assn A (tl xs) r)\<close>
  supply [simp] = ol_assn_conv ol_seg_cons sep_conj_exists
  apply (cases xs; simp)
  unfolding os_pop_def
  by vcg

lemma ol_reverse_aux_rule:
  \<open>llvm_htriple (ol_seg A xs p null ** ol_seg A ys q null) (os_reverse_aux q p)
    (\<lambda>r. ol_seg A (rev xs @ ys) r null)\<close>
proof (induct xs arbitrary: p q ys)
  case Nil
  then show ?case by vcg
next
  case (Cons x xs)
  note [vcg_rules] = Cons.hyps[where ys = \<open>x # ys\<close>]
  note [simp, named_ss fri_prepare_simps] = ol_seg_cons
  show ?case
    apply (cases \<open>p \<noteq> null\<close>; simp)
    by vcg
qed

lemma ol_reverse_rule[vcg_rules]:
  \<open>llvm_htriple (ol_assn A xs p) (os_reverse p) (\<lambda>r. ol_assn A (rev xs) r)\<close>
  unfolding os_reverse_def ol_assn_conv
  supply [vcg_rules] = ol_reverse_aux_rule[where ys = \<open>[]\<close>, simplified]
  by vcg

context begin

private lemma ol_length_aux:
  assumes B: \<open>length xs < max_snat LENGTH('l)\<close> and L: \<open>length xsi = length xs\<close>
  shows \<open>llvm_htriple
    (\<up>(length xsi = length xs) ** \<upharpoonleft>os_list_assn xsi p
      ** \<upharpoonleft>(Proto_EOArray.list_assn (mk_assn A)) xs xsi)
    (os_list_length p :: 'l::len2 word llM)
    (\<lambda>n. \<upharpoonleft>snat.assn (length xs) n ** (EXS xsi'. \<up>(length xsi' = length xs)
      ** \<upharpoonleft>os_list_assn xsi' p ** \<upharpoonleft>(Proto_EOArray.list_assn (mk_assn A)) xs xsi'))\<close>
proof -
  have B': \<open>length xsi < max_snat LENGTH('l)\<close> using B L by simp
  note H = frame_rule[OF os_list_length_rule[OF B'],
    where F = \<open>\<upharpoonleft>(Proto_EOArray.list_assn (mk_assn A)) xs xsi\<close>]
  show ?thesis
    apply (rule htriple_ent_pre[OF _ htriple_ent_post[OF _ H]])
    subgoal
      by (auto simp: entails_def sep_algebra_simps)
    subgoal for n
      apply (simp add: sep_conj_exists)
      apply (rule entails_exI[where x = xsi])
      by (auto simp: entails_def sep_algebra_simps L)
    done
qed

lemma ol_length_rule[vcg_rules]:
  \<open>length xs < max_snat LENGTH('l) \<Longrightarrow> llvm_htriple
    (ol_assn A xs p)
    (os_list_length p :: 'l::len2 word llM)
    (\<lambda>n. \<upharpoonleft>snat.assn (length xs) n ** ol_assn A xs p)\<close>
  unfolding ol_assn_os_conv
  apply (rule htriple_pre_EXS)
  subgoal for xsi
    apply (rule htriple_pure_preI)
    apply (rule ol_length_aux)
     apply assumption
    by (auto dest!: pure_part_split_conj)
  done

end

subsubsection \<open>Element-wise Equality\<close>

text \<open>The generic template \<open>os_eq\<close> from \<open>IICF_Open_List\<close> decides abstract list equality,
  given an element comparison \<open>eqi\<close> that decides abstract \<^emph>\<open>element\<close> equality. No purity
  or uniqueness of the element relation appears at this level \<emdash> those conditions only
  arise when discharging the premise for concrete word-like elements (\<open>ll_icmp_eq\<close> is a
  correct \<open>eqi\<close> iff the word relation is bi-unique). Equality only reads (\<open>\<^sup>k\<close>
  everywhere), so impure elements \<emdash> e.g. nested lists \<emdash> are fine; instantiating the rule
  with itself one level down gives equality of lists of lists.

  Proof technique for the recursive \<open>partial_function\<close>: never \<open>unfolding os_eq.simps\<close>
  (simp loops on the recursive occurrence); instead ONE unfold per induction case via
  \<open>subst os_eq.simps\<close>, with the induction hypothesis (and the element rule) as
  \<open>vcg_rules\<close> for the recursive call \<emdash> mirroring \<open>os_delete_rule\<close>/\<open>os_rem_rule\<close>.\<close>

lemma ol_eq_rule:
  assumes EQ: \<open>\<And>a c a' c'. llvm_htriple (A a c ** A a' c') (eqi c c')
    (\<lambda>r. A a c ** A a' c' ** \<upharpoonleft>bool.assn (a = a') r)\<close>
  shows \<open>llvm_htriple (ol_assn A xs p ** ol_assn A ys q) (os_eq eqi p q)
    (\<lambda>r. ol_assn A xs p ** ol_assn A ys q ** \<upharpoonleft>bool.assn (xs = ys) r)\<close>
  unfolding ol_assn_conv
proof (induction xs arbitrary: ys p q)
  case Nil
  show ?case
    supply [simp] = bool.assn_def
    apply (subst os_eq.simps)
    apply (cases ys; cases \<open>q = null\<close>; simp)
    by vcg
next
  case (Cons x xs)
  interpret llvm_prim_ctrl_setup .
  note [vcg_rules] = Cons.IH EQ
  show ?case
    supply [simp, named_ss fri_prepare_simps] = ol_seg_cons
    supply [simp] = bool.assn_def sep_conj_exists
    apply (subst os_eq.simps)
    apply (cases \<open>p = null\<close>; cases \<open>q = null\<close>; cases ys; simp)
    by vcg
qed

lemma os_eq_rule:
  assumes P: \<open>is_pure A\<close>
  and EQ: \<open>\<And>a c a' c'. llvm_htriple (A a c ** A a' c') (eqi c c')
    (\<lambda>r. A a c ** A a' c' ** \<upharpoonleft>bool.assn (a = a') r)\<close>
  shows \<open>llvm_htriple (os_assn A xs p ** os_assn A ys q) (os_eq eqi p q)
    (\<lambda>r. os_assn A xs p ** os_assn A ys q ** \<upharpoonleft>bool.assn (xs = ys) r)\<close>
  using ol_eq_rule[where A=A and eqi=eqi, OF EQ] unfolding ol_assn_pure_conv[OF P] .

lemma ol_eq_hnr:
  assumes EQ: \<open>\<And>a c a' c'. llvm_htriple (A a c ** A a' c') (eqi c c')
    (\<lambda>r. A a c ** A a' c' ** \<upharpoonleft>bool.assn (a = a') r)\<close>
  shows \<open>(uncurry (os_eq eqi), uncurry (RETURN oo (=)))
    \<in> (ol_assn A)\<^sup>k *\<^sub>a (ol_assn A)\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding bool1_rel_def bool.assn_is_rel[symmetric]
  supply [vcg_rules] = ol_eq_rule[OF EQ]
  apply sepref_to_hoare
  apply vcg_monadify
  by vcg'

subsubsection \<open>Interface Rules\<close>

context
  notes [simp] = refine_pw_simps prod_assn_pair_conv
begin

private method ol_ref =
  ((unfold snat_rel_def snat.assn_is_rel[symmetric] bool1_rel_def bool.assn_is_rel[symmetric])?,
    sepref_to_hoare, vcg_monadify, vcg')

lemma ol_empty_hnr[sepref_fr_rules]:
  \<open>(uncurry0 os_empty, uncurry0 (RETURN op_ol_empty)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a ol_assn A\<close>
  unfolding op_ol_empty_def
  by ol_ref

lemma ol_is_empty_hnr[sepref_fr_rules]:
  \<open>(os_is_empty, RETURN o op_list_is_empty) \<in> (ol_assn A)\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding bool1_rel_def bool.assn_is_rel[symmetric]
  apply sepref_to_hoare
  apply vcg_monadify
  apply vcg'
  subgoal
    by (auto simp: ENTAILS_def entails_def bool.assn_def from_bool_def
      sep_algebra_simps pred_lift_extract_simps split: bool.splits)
  by (tactic \<open>Defer_Slot.remove_slot_tac\<close>)

lemma ol_prepend_hnr[sepref_fr_rules]:
  \<open>(uncurry os_prepend, uncurry (RETURN oo op_list_prepend)) \<in> A\<^sup>d *\<^sub>a (ol_assn A)\<^sup>d \<rightarrow>\<^sub>a ol_assn A\<close>
  by ol_ref

lemma ol_pop_front_hnr[sepref_fr_rules]:
  \<open>(os_pop, mop_list_pop_front) \<in> (ol_assn A)\<^sup>d \<rightarrow>\<^sub>a A \<times>\<^sub>a ol_assn A\<close>
  by ol_ref

lemma ol_pop_front_hnr_op[sepref_fr_rules]:
  \<open>(os_pop, RETURN o op_list_pop_front) \<in> [\<lambda>xs. xs \<noteq> []]\<^sub>a (ol_assn A)\<^sup>d \<rightarrow> A \<times>\<^sub>a ol_assn A\<close>
  by ol_ref

lemma ol_rev_hnr[sepref_fr_rules]:
  \<open>(os_reverse, RETURN o op_list_rev) \<in> (ol_assn A)\<^sup>d \<rightarrow>\<^sub>a ol_assn A\<close>
  by ol_ref

context
  fixes l_dummy :: \<open>'l::len2 itself\<close>
  and L defines [simp]: \<open>L \<equiv> LENGTH('l)\<close>
begin

lemma ol_length_hnr[sepref_fr_rules]:
  \<open>(os_list_length, RETURN o op_list_length)
    \<in> [\<lambda>xs. length xs < max_snat L]\<^sub>a (ol_assn A)\<^sup>k \<rightarrow> snat_assn' TYPE('l)\<close>
  by ol_ref

end

end

text \<open>Also structural, hence directly liftable once needed (raw code partially still to be
  written): destructive \<open>take\<close>/\<open>drop\<close>/\<open>op_split_list\<close> (sever one link, free resp. keep the
  suffix \<emdash> \<open>drop\<close>/\<open>split\<close> need no element access at all, destructive \<open>take\<close> frees the
  dropped suffix and therefore takes a \<open>MK_FREE A\<close> assumption), and destructive
  concatenation (\<open>op_join_list\<close>, walk to the last node and patch its next pointer).
  The copying variants of \<open>take\<close>/\<open>drop\<close> are NOT liftable for impure \<open>A\<close> without a
  deep-copy operation on \<open>A\<close> as an extra parameter; full-list deep copy is provided
  below (\<open>ol_copy\<close>).\<close>

subsection \<open>Deep Copy\<close>

text \<open>Deep copy of an owning list, parameterized by an element copy \<open>cp\<close>,  the dual of
  \<open>ol_delete\<close>. A borrowing (zero-copy) keep-mode read of an element is impossible: the
  postcondition \<open>ol_assn A xs p ** A (xs!i) r\<close> with \<open>r\<close> aliasing the node payload would
  claim the same heap cells in both \<open>**\<close>-conjuncts. With a \<^emph>\<open>fresh\<close> copy the same
  postcondition is honestly satisfiable, so keep-mode operations returning elements
  become derivable at the price of duplication.

  The sepref-facing form is \<open>(cp, RETURN o COPY) \<in> A\<^sup>k \<rightarrow>\<^sub>a A\<close>: sepref's monadify phase
  inserts \<open>COPY\<close> automatically whenever abstract code violates linearity (an owned value
  used twice), and resolves it against such rules (cf. \<open>hnr_pure_COPY\<close> for pure \<open>A\<close>, and
  \<open>is_copy\<close>/\<open>sort_impl_copy_context\<close> in the sorting library for the same idiom).

  CAVEAT (code generation): like \<open>ol_delete\<close>, the template is higher-order in \<open>cp\<close>;
  instances must be specialized first-order for export (cf. \<open>strl_copy\<close> in
  \<open>String_Assn\<close>, \<open>monom_copy_impl\<close> in \<open>Monom_Assn\<close>).\<close>

partial_function (M) ol_copy :: \<open>('c::llvm_rep \<Rightarrow> 'c llM) \<Rightarrow> 'c os_list \<Rightarrow> 'c os_list llM\<close>
  where
  \<open>ol_copy cp p = (if p = null then Mreturn null else doM {
      n \<leftarrow> ll_load p;
      c \<leftarrow> cp (node.val n);
      t \<leftarrow> ol_copy cp (node.next n);
      os_prepend c t
    })\<close>

lemma ol_copy_rule:
  assumes CP: \<open>\<And>a c. llvm_htriple (A a c) (cp c) (\<lambda>r. A a c ** A a r)\<close>
  shows \<open>llvm_htriple (ol_assn A xs p) (ol_copy cp p) (\<lambda>r. ol_assn A xs p ** ol_assn A xs r)\<close>
  unfolding ol_assn_conv
proof (induction xs arbitrary: p)
  case Nil
  show ?case
    apply (subst ol_copy.simps)
    by vcg
next
  case (Cons x xs)
  interpret llvm_prim_ctrl_setup .
  note [vcg_rules] = Cons.IH CP ol_prepend_rule[unfolded ol_assn_conv]
  show ?case
    supply [simp, named_ss fri_prepare_simps] = ol_seg_cons
    supply [simp] = sep_conj_exists
    apply (subst ol_copy.simps)
    apply (cases \<open>p = null\<close>; simp)
    by vcg
qed

text \<open>For pure element assertions the trivial element copy \<open>Mreturn\<close> works: duplicating
  a pure assertion costs nothing (\<open>\<up>\<Phi> ** \<up>\<Phi> = \<up>\<Phi>\<close>).\<close>

lemma pure_elem_copy_rule:
  assumes \<open>is_pure A\<close>
  shows \<open>llvm_htriple (A a c) (Mreturn c) (\<lambda>r. A a c ** A a r)\<close>
proof -
  from assms obtain \<Phi> where P: \<open>\<And>x x'. A x x' = \<up>(\<Phi> x x')\<close>
    by (auto simp: is_pure_def)
  show ?thesis
    unfolding P
    by vcg
qed

lemma os_copy_rule:
  assumes P: \<open>is_pure A\<close>
  shows \<open>llvm_htriple (os_assn A xs p) (ol_copy Mreturn p)
    (\<lambda>r. os_assn A xs p ** os_assn A xs r)\<close>
  using ol_copy_rule[where A=A and cp=Mreturn, OF pure_elem_copy_rule[OF P]]
  unfolding ol_assn_pure_conv[OF P] .

lemma ol_copy_hnr:
  assumes CP: \<open>\<And>a c. llvm_htriple (A a c) (cp c) (\<lambda>r. A a c ** A a r)\<close>
  shows \<open>(ol_copy cp, RETURN o COPY) \<in> (ol_assn A)\<^sup>k \<rightarrow>\<^sub>a ol_assn A\<close>
  supply [vcg_rules] = ol_copy_rule[OF CP]
  apply sepref_to_hoare
  apply vcg_monadify
  by vcg'

subsection \<open>Reading Without Consuming - the Borrowing Problem\<close>

text \<open>Sepref has no borrowing: a rule result either owns (\<open>\<^sup>d\<close> input consumed) or the input
  is kept whole (\<open>\<^sup>k\<close>). Reading the head of an owning list for inspection (e.g. the
  comparisons in \<open>msort\<close>'s merge) therefore needs one of:

  \<^enum> \<^emph>\<open>Pop / re-prepend\<close> at the nres level: rewrite the abstract program to
    \<open>doN { (x, xs') \<leftarrow> mop_list_pop_front xs; \<dots> use x \<dots>; RETURN (x # xs') }\<close>.
    Works today with the rules above; costs a node free + re-allocation per peek.

  \<^enum> \<^emph>\<open>Fused special-purpose ops\<close>: register a combined operation, e.g.
    \<open>mop_list_hd2_cmp le xs ys \<equiv> doN {ASSERT (\<dots>); RETURN (le (hd xs) (hd ys))}\<close>,
    implemented by two \<open>ll_load\<close>s under both list assertions and proven directly.
    Pragmatic and efficient; this is likely what \<open>msort\<close>'s merge wants, with the
    comparator specialized (as planned anyway for the monomial order).

  \<^enum> \<^emph>\<open>Systematic borrowing\<close>: \<^theory>\<open>Isabelle_LLVM.Proto_Sepref_Borrow\<close> resp. a
    \<open>WITH_SPLIT\<close>-style combinator (\<open>WITH_HD xs (\<lambda>x. m x)\<close> lending \<open>A\<close>-ownership of the
    head to a subcomputation that must return it unchanged). Heaviest machinery,
    only worth it if peeking is pervasive.

  \<^enum> \<^emph>\<open>Deep copy\<close> (\<open>ol_copy\<close> above): keep-mode access by duplication. Sepref inserts
    \<open>COPY\<close> automatically on linearity violations and resolves it via the registered
    copy rules (\<open>strl_copy_hnr\<close>/\<open>monom_copy_hnr\<close>). Ergonomic fallback for cold code;
    a full traversal + allocation per read, so wrong for hot loops.\<close>

subsection \<open>Explicit-Ownership View (optional)\<close>

text \<open>For in-place indexed element access (the array sorting algorithms use this heavily),
  Proto_EOArray refines \<open>'a option list\<close>, where \<open>None\<close> marks an ownership hole
  (\<open>mop_eo_extract\<close> takes an element out, \<open>mop_eo_set\<close> puts one back). The owning list
  gets this view for free by instantiating \<open>ol_assn\<close> with \<^const>\<open>oelem_assn\<close>; the ops are
  \<open>O(i)\<close> pointer walks (reusing \<open>os_list_get\<close>'s loop).\<close>

abbreviation ol_eo_assn :: \<open>('a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn) \<Rightarrow> 'a option list \<Rightarrow> 'c os_list \<Rightarrow> assn\<close>
  where \<open>ol_eo_assn A \<equiv> ol_assn (\<upharpoonleft>(oelem_assn (mk_assn A)))\<close>

lemma mk_assn_inv: \<open>mk_assn (\<upharpoonleft>B) = B\<close>
  unfolding mk_assn_def dr_assn_prefix_def by simp

lemma list_assn_map_some:
  \<open>\<upharpoonleft>(Proto_EOArray.list_assn (oelem_assn (mk_assn A))) (map Some xs) xsi
    = \<upharpoonleft>(Proto_EOArray.list_assn (mk_assn A)) xs xsi\<close>
proof (cases \<open>length xs = length xsi\<close>)
  case True then show ?thesis
    by (induction xs xsi rule: list_induct2) (auto simp: sep_algebra_simps)
next
  case False then show ?thesis by simp
qed

lemma ol_eo_assn_map_some: \<open>ol_eo_assn A (map Some xs) p = ol_assn A xs p\<close>
  unfolding ol_assn_conv ol_seg_def
  by (simp add: mk_assn_inv list_assn_map_some)

lemma ol_assn_eo_conv: \<open>ol_assn A = hr_comp (ol_eo_assn A) (\<langle>some_rel\<rangle>list_rel)\<close>
  apply (intro ext)
  unfolding hr_comp_def
  by (auto simp: some_list_rel_conv ol_eo_assn_map_some sep_algebra_simps fun_eq_iff)

lemma ol_to_eo_conv_hnr[sepref_fr_rules]:
  \<open>(Mreturn, mop_to_eo_conv) \<in> (ol_assn A)\<^sup>d \<rightarrow>\<^sub>a ol_eo_assn A\<close>
  supply [simp] = refine_pw_simps
  apply sepref_to_hoare
  apply vcg_monadify
  apply vcg'
  unfolding ENTAILS_def
  apply (simp add: sep_algebra_simps ol_eo_assn_map_some)
  by (tactic \<open>Defer_Slot.remove_slot_tac\<close>)

lemma ol_to_wo_conv_hnr[sepref_fr_rules]:
  \<open>(Mreturn, mop_to_wo_conv) \<in> (ol_eo_assn A)\<^sup>d \<rightarrow>\<^sub>a ol_assn A\<close>
  supply [simp] = ol_eo_assn_map_some
  apply sepref_to_hoare
  apply (auto simp: refine_pw_simps sep_algebra_simps elim!: None_not_in_set_conv)
  by vcg

definition ol_eo_extract :: \<open>'c::llvm_rep os_list \<Rightarrow> 'b::len2 word \<Rightarrow> ('c \<times> 'c os_list) llM\<close>
  where [llvm_code]: \<open>ol_eo_extract p i \<equiv> doM { v \<leftarrow> os_list_get p i; Mreturn (v, p) }\<close>

context begin

text \<open>The auxiliary rule fixes the concrete spine \<open>xsi\<close> and carries the facts fri will
  need as pure conjuncts of the precondition \<emdash> conditional-vcg-rule side conditions must
  be derivable from state-extracted premises, or they end up as unsolvable
  \<open>SOLVE_AUTO_DEFER\<close> leftovers. Its postcondition is stated with the existential hoisted
  to lambda-top, which is the normal form \<open>simp only: sep_conj_exists\<close> produces in the
  public rule's goal (rule composition needs the posts to unify verbatim).\<close>

private lemma ol_eo_extract_aux:
  assumes I: \<open>i < length xs\<close> and S: \<open>xs ! i = Some x\<close> and L: \<open>length xsi = length xs\<close>
  shows \<open>llvm_htriple
    (\<upharpoonleft>snat.assn i ii ** \<up>(i < length xsi \<and> length xsi = length xs) ** \<upharpoonleft>os_list_assn xsi p
      ** \<upharpoonleft>(Proto_EOArray.list_assn (oelem_assn (mk_assn A))) xs xsi)
    (ol_eo_extract p ii)
    (\<lambda>(ci, r). EXS xsi'. A (the (xs ! i)) ci ** \<upharpoonleft>snat.assn i ii
      ** \<up>(length xsi' = length (xs[i := None])) ** \<upharpoonleft>os_list_assn xsi' r
      ** \<upharpoonleft>(Proto_EOArray.list_assn (oelem_assn (mk_assn A))) (xs[i := None]) xsi')\<close>
proof -
  note E = lo_extract_elem[OF I S, of \<open>mk_assn A\<close> xsi]
  show ?thesis
    unfolding ol_eo_extract_def
    supply [simp] = E S length_list_update
    by vcg 
qed

lemma ol_eo_extract_rule[vcg_rules]:
  assumes I: \<open>i < length xs\<close> and N: \<open>xs ! i \<noteq> None\<close>
  shows \<open>llvm_htriple
    (\<upharpoonleft>snat.assn i ii ** ol_eo_assn A xs p)
    (ol_eo_extract p ii)
    (\<lambda>(ci, r). A (the (xs ! i)) ci ** \<upharpoonleft>snat.assn i ii ** ol_eo_assn A (xs[i := None]) r)\<close>
proof -
  from N obtain x where S: \<open>xs ! i = Some x\<close> by (cases \<open>xs ! i\<close>) auto
  show ?thesis
    unfolding ol_assn_os_conv
    apply (simp only: mk_assn_inv sep_conj_exists)
    apply (rule htriple_pre_EXS)
    apply (rule htriple_pure_preI)
    subgoal premises PP for xsi
    proof -
      have L: \<open>length xsi = length xs\<close>
        using PP by (auto dest!: pure_part_split_conj)
      show ?thesis
        apply (rule htriple_ent_pre[OF _ ol_eo_extract_aux[OF I S L]])
        using I L
        by (auto simp: entails_def sep_algebra_simps)
    qed
    done
qed

end

lemma ol_eo_extract_hnr[sepref_fr_rules]:
  \<open>(uncurry ol_eo_extract, uncurry mop_eo_extract)
    \<in> (ol_eo_assn A)\<^sup>d *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a A \<times>\<^sub>a ol_eo_assn A\<close>
  supply [simp] = refine_pw_simps 
  unfolding snat_rel_def snat.assn_is_rel[symmetric]
  apply sepref_to_hoare
  apply vcg_monadify
  by vcg'

definition ol_eo_set :: \<open>'c::llvm_rep os_list \<Rightarrow> 'b::len2 word \<Rightarrow> 'c \<Rightarrow> 'c os_list llM\<close>
  where [llvm_code]: \<open>ol_eo_set p\<^sub>0 i\<^sub>0 x = doM {
    (p, _) \<leftarrow> llc_while
      (\<lambda>(_, i). ll_cmp (i \<noteq> 0))
      (\<lambda>(p, i). doM {
        n \<leftarrow> ll_load p;
        Mreturn (node.next n, i - signed_nat 1)
      }) (p\<^sub>0, i\<^sub>0);
    n \<leftarrow> ll_load p;
    ll_store (Node x (node.next n)) p;
    Mreturn p\<^sub>0
  }\<close>

context begin

text \<open>The only genuinely new while-loop proof of this theory: the walk is identical to
  \<open>os_list_get\<close>, so invariant and step lemma (\<open>os_get_step_entails\<close>) are reused verbatim
  from \<open>IICF_Open_List\<close>; only the exit differs (store + re-assembly of the updated list
  via \<open>lseg_reassemble\<close> instantiated at \<open>xs[n := c]\<close>).\<close>

private lemma ol_set_exit_entails:
  assumes N: \<open>n < length xs\<close>
  shows \<open>ENTAILS
    (\<upharpoonleft>ll_bpto (Node c s) a ** lseg (drop (Suc n) xs) s null ** lseg (take n xs) p a)
    (lseg (xs[n := c]) p null)\<close>
proof -
  have T1: \<open>take n (xs[n := c]) = take n xs\<close>
    by (metis order_refl take_update_cancel)
  have T1b: \<open>(take n xs)[n := c] = take n xs\<close>
    by (simp add: list_update_beyond)
  have T2: \<open>drop (Suc n) (xs[n := c]) = drop (Suc n) xs\<close>
    by simp
  have T3: \<open>(xs[n := c]) ! n = c\<close> using N by simp
  have L: \<open>n < length (xs[n := c])\<close> using N by simp
  show ?thesis
    unfolding ENTAILS_def
    using lseg_reassemble[OF L, of p a s] by (simp add: T1 T1b T2 T3 sep_conj_aci)
qed

lemma ol_eo_set_raw_rule:
  \<open>llvm_htriple
    (\<upharpoonleft>os_list_assn xs p ** \<upharpoonleft>snat.assn n nn ** \<up>(n < length xs))
    (ol_eo_set p nn c)
    (\<lambda>r. \<up>(r = p) ** \<upharpoonleft>os_list_assn (xs[n := c]) p)\<close>
  unfolding ol_eo_set_def
  apply (rewrite annotate_llc_while [where
    I=\<open>\<lambda>(q, ii) t. EXS i. \<upharpoonleft>snat.assn i ii
                 ** lseg (take (n - i) xs) p q
                 ** lseg (drop (n - i) xs) q null
                 ** \<up>(i \<le> n)
                 ** \<up>\<^sub>!(t = i)\<close>
    and R=\<open>measure id\<close>])
  supply [simp] = os_list_assn_def take_shift_snoc take_shift_snoc' drop_shift
    lseg_append lseg_singleton sep_conj_exists
  apply vcg_monadify
  apply vcg'
  subgoal by (rule os_get_step_entails; assumption)
  subgoal for asf a b t r s
    apply (rule impI)
    apply hypsubst
    supply [simp] = drop_head_exit 
    apply vcg'
    subgoal
      apply (simp add: sep_algebra_simps)
      by (rule ol_set_exit_entails; assumption)
    by (tactic \<open>Defer_Slot.remove_slot_tac\<close>)
  by (tactic \<open>Defer_Slot.remove_slot_tac\<close>)

private lemma ol_eo_set_aux:
  assumes I: \<open>i < length xs\<close> and N: \<open>xs ! i = None\<close> and L: \<open>length xsi = length xs\<close>
  shows \<open>llvm_htriple
    (A x c ** \<upharpoonleft>snat.assn i ii ** \<up>(i < length xsi \<and> length xsi = length xs)
      ** \<upharpoonleft>os_list_assn xsi p
      ** \<upharpoonleft>(Proto_EOArray.list_assn (oelem_assn (mk_assn A))) xs xsi)
    (ol_eo_set p ii c)
    (\<lambda>r. EXS xsi'. \<up>(r = p) ** \<up>(length xsi' = length (xs[i := Some x]))
      ** \<upharpoonleft>os_list_assn xsi' r
      ** \<upharpoonleft>(Proto_EOArray.list_assn (oelem_assn (mk_assn A))) (xs[i := Some x]) xsi')\<close>
proof -
  have I': \<open>i < length xsi\<close> using I L by simp
  note E = lo_insert_elem[OF I N, of \<open>mk_assn A\<close> x xsi c]
  note H = frame_rule[OF ol_eo_set_raw_rule[of xsi p i ii c],
    where F = \<open>A x c ** \<upharpoonleft>(Proto_EOArray.list_assn (oelem_assn (mk_assn A))) xs xsi\<close>]
  show ?thesis
    apply (rule htriple_ent_pre[OF _ htriple_ent_post[OF _ H]])
    subgoal
      apply (simp add: sep_algebra_simps)
      by (auto simp: entails_def sep_conj_c I' L)
    subgoal for r
      unfolding entails_def
      apply (clarsimp simp: sep_algebra_simps)
      apply (rule exI[where x = \<open>xsi[i := c]\<close>])
      apply (intro conjI)
      subgoal by (simp add: L)
      by (simp add: E sep_conj_aci)
    done
qed

lemma ol_eo_set_rule[vcg_rules]:
  assumes I: \<open>i < length xs\<close> and N: \<open>xs ! i = None\<close>
  shows \<open>llvm_htriple
    (A x c ** \<upharpoonleft>snat.assn i ii ** ol_eo_assn A xs p)
    (ol_eo_set p ii c)
    (\<lambda>r. \<up>(r = p) ** ol_eo_assn A (xs[i := Some x]) r)\<close>
  unfolding ol_assn_os_conv
  apply (simp only: mk_assn_inv sep_conj_exists)
  apply (rule htriple_pre_EXS)
  apply (rule htriple_pure_preI)
  subgoal premises PP for xsi
  proof -
    have L: \<open>length xsi = length xs\<close>
      using PP by (auto dest!: pure_part_split_conj)
    show ?thesis
      apply (rule htriple_ent_pre[OF _ ol_eo_set_aux[OF I N L]])
      using I L
      by (auto simp: entails_def sep_algebra_simps)
  qed
  done

end

lemma ol_eo_set_hnr[sepref_fr_rules]:
  \<open>(uncurry2 ol_eo_set, uncurry2 mop_eo_set)
    \<in> (ol_eo_assn A)\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a A\<^sup>d \<rightarrow>\<^sub>a ol_eo_assn A\<close>
  supply [simp] = refine_pw_simps 
  unfolding snat_rel_def snat.assn_is_rel[symmetric]
  apply sepref_to_hoare
  apply vcg_monadify
  by vcg'

experiment
begin

  abbreviation w8ss_assn :: \<open>8 word list list \<Rightarrow> 8 word os_list os_list \<Rightarrow> assn\<close> where
    \<open>w8ss_assn \<equiv> ol_assn (os_assn id_assn)\<close>

  text \<open>Deep free composes: the conditional \<open>MK_FREE\<close> rule instantiated with the inner
    lists' free function.\<close>
  lemma w8ss_assn_free: \<open>MK_FREE w8ss_assn (ol_delete os_delete)\<close>
    by (rule ol_assn_free[OF os_assn_free])

  text \<open>End-to-end synthesis on a nested list: prepend a fresh empty inner list.
    Exercises \<open>ol_prepend_hnr\<close> with the impure element assertion \<open>os_assn id_assn\<close>
    (element in \<open>\<^sup>d\<close> mode) and the inner \<open>os_empty\<close> rule from \<open>IICF_Open_List\<close>.\<close>
  definition nest_cons_empty :: \<open>8 word list list \<Rightarrow> 8 word list list\<close> where
    \<open>nest_cons_empty xss = op_list_empty # xss\<close>

  sepref_def nest_cons_empty_impl is \<open>RETURN o nest_cons_empty\<close>
    :: \<open>w8ss_assn\<^sup>d \<rightarrow>\<^sub>a w8ss_assn\<close>
    unfolding nest_cons_empty_def by sepref

  text \<open>Producing a fresh (outer) owning list via the custom empty op.\<close>
  definition nest_new :: \<open>8 word list list\<close> where
    \<open>nest_new = op_ol_empty\<close>

  sepref_def nest_new_impl is \<open>uncurry0 (RETURN nest_new)\<close>
    :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a w8ss_assn\<close>
    unfolding nest_new_def by sepref

  text \<open>Destructive traversal: pop the first inner list and return it, freeing nothing.\<close>
  definition nest_pop :: \<open>8 word list list \<Rightarrow> (8 word list \<times> 8 word list list) nres\<close> where
    \<open>nest_pop xss = mop_list_pop_front xss\<close>

  sepref_def nest_pop_impl is \<open>nest_pop\<close>
    :: \<open>w8ss_assn\<^sup>d \<rightarrow>\<^sub>a os_assn id_assn \<times>\<^sub>a w8ss_assn\<close>
    unfolding nest_pop_def by sepref

  definition \<open>nest_test xss \<equiv> case xss of [] \<Rightarrow> [] | (xs # xss) \<Rightarrow> (case xs of [] \<Rightarrow> xss | (x # xs) \<Rightarrow> [x]#xss)\<close>

  text \<open>FAILS \<emdash> but not because something is destroyed; the opposite: after
    @{thm list.case_eq_if} the branches read the head via \<open>hd xss\<close>/\<open>tl xss\<close> while \<open>xss\<close>
    stays alive. For \<open>ol_assn\<close> there are deliberately NO \<open>hd\<close>/\<open>tl\<close> rules: \<open>hd\<close> in \<open>\<^sup>k\<close>
    mode would \<^emph>\<open>duplicate\<close> ownership of the inner list (the same pointer would carry a
    full \<open>os_assn\<close> both as the returned value and inside \<open>xss\<close>'s element ownership \<emdash>
    unexpressible in separation logic), and \<open>tl\<close> would have to free the head element.
    Sepref therefore falls back to the only registered \<open>hd\<close> rule \<emdash> the pure-element
    \<open>os_assn\<close> one \<emdash> and the translation dies on the unprovable frame goal
    \<open>hn_ctxt (ol_assn (os_assn word_assn)) xss p \<turnstile> hn_ctxt (os_assn ?R) xss p\<close>
    (plus an unsatisfiable \<open>CONSTRAINT is_pure ?R\<close>). Reading the head of an owning list
    must transfer ownership, i.e. go through the destructive \<open>mop_list_pop_front\<close>;
    see the working variant below.\<close>
  sepref_def nest_test_impl is \<open>RETURN o nest_test\<close>
    :: \<open>w8ss_assn\<^sup>d \<rightarrow>\<^sub>a w8ss_assn\<close>
    unfolding nest_test_def list.case_eq_if
    apply sepref_dbg_keep
    oops

  text \<open>The same function with the case distinctions expressed by \<open>pop\<close> instead of
    \<open>hd\<close>/\<open>tl\<close> \<emdash> ownership of the popped inner list moves out of \<open>xss\<close>, is consumed by
    the inner pop resp. dropped (sepref inserts the deep free via the conditional
    \<open>MK_FREE\<close> rules), and the rebuilt element is consumed by the outer prepend.\<close>
  text \<open>The same function with the OUTER case distinction expressed by \<open>pop\<close> \<emdash>
    ownership of the popped inner list \<open>xs\<close> moves out of \<open>xss\<close>. The INNER list has pure
    elements, so \<open>hd\<close> in \<open>\<^sup>k\<close> mode is legal there. (An inner \<open>mop_list_pop_front\<close> would
    NOT translate: the new op has only an \<open>ol_assn\<close> implementation so far; an \<open>os_assn\<close>
    one could be added via \<open>sepref_decl_impl (ismop)\<close> over \<open>os_pop\<close>.) The popped \<open>xs\<close> is
    dropped in both branches after use; sepref inserts the frees automatically via the
    registered \<open>MK_FREE\<close> rules.\<close>
  definition nest_test' :: \<open>8 word list list \<Rightarrow> 8 word list list nres\<close> where
    \<open>nest_test' xss = (
      if xss = [] then RETURN xss
      else doN {
        (xs, xss') \<leftarrow> mop_list_pop_front xss;
        if xs = [] then RETURN xss'
        else doN {
          x \<leftarrow> mop_list_hd xs;
          RETURN ((x # op_list_empty) # xss')
        }
      })\<close>

  lemma nest_test'_correct: \<open>nest_test' xss = RETURN (nest_test xss)\<close>
    unfolding nest_test'_def nest_test_def
    by (cases xss; cases \<open>hd xss\<close>) (auto simp: refine_pw_simps)

  sepref_def nest_test_impl' is \<open>nest_test'\<close>
    :: \<open>w8ss_assn\<^sup>d \<rightarrow>\<^sub>a w8ss_assn\<close>
    unfolding nest_test'_def by sepref

end

subsection \<open>Proof Architecture Notes\<close>

text \<open>How the sorry-free state was reached \<emdash> the load-bearing ideas:

  \<^enum> \<^emph>\<open>Reuse over re-proving\<close>: @{thm ol_assn_os_conv} decomposes an owning list into a
    plain \<open>\<upharpoonleft>os_list_assn\<close> spine plus element-wise \<open>list_assn\<close> ownership. Every rule whose
    code only touches the spine (\<open>length\<close>, eo \<open>extract\<close>/\<open>set\<close> walks) is composed manually
    from the \<^emph>\<open>existing\<close> spine rule via \<open>htriple_pre_EXS\<close> + \<open>htriple_pure_preI\<close> +
    \<open>frame_rule\<close> + \<open>htriple_ent_pre\<close>/\<open>_post\<close> \<emdash> plain \<open>vcg\<close> on such decomposed triples
    reliably diverges (\<open>Interrupt_Breakdown\<close>). One-node ops (\<open>prepend\<close>, \<open>pop\<close>, \<open>is_empty\<close>,
    \<open>reverse\<close>, \<open>delete\<close>) instead get direct vcg proofs with \<open>ol_seg_cons\<close> as simp,
    mirroring their \<open>LLVM_DS_Open_List\<close> counterparts.
  \<^enum> \<^emph>\<open>Two-stage AC discipline\<close> for assertion equalities (see the note at
    \<open>ol_seg_cons\<close>): pure elimination first (no AC), atom reordering second (no pures).
  \<^enum> \<^emph>\<open>Fri-friendly auxiliary statements\<close>: side conditions of conditional vcg rules must
    be state-derivable (carried as \<open>\<up>\<close>-conjuncts of the aux precondition), and aux
    postconditions must be stated with existentials hoisted to lambda-top \<emdash> the form
    \<open>simp only: sep_conj_exists\<close> produces \<emdash> or rule composition fails to unify.
  \<^enum> The single genuinely new loop proof (\<open>ol_eo_set_raw_rule\<close>) reuses the invariant and
    step lemma of \<open>os_list_get_rule\<close> verbatim; only the exit entailment is new.

  Open design points:
  \<^item> Code export for the \<open>ol_delete\<close>/\<open>ol_copy\<close> templates: needs first-order per-instance
    specializations (\<open>[llvm_code]\<close> can't take the higher-order template).
  \<^item> Whether \<open>msort\<close> on owning lists uses pop/prepend-based merge (option 1 above) or a
    fused head-comparison op (option 2); option 2 is recommended once the comparator is
    specialized anyway.
  \<^item> Rule-set hygiene: \<^emph>\<open>consumer\<close> rules (pop, prepend, is_empty, \<dots>) are disambiguated
    from their \<open>os_assn\<close> counterparts by unification against the argument's \<open>hn_ctxt\<close>,
    so global registration is safe. \<^emph>\<open>Producer\<close> rules (empty, and later replicate/copy)
    are NOT \<emdash> their result assertion is unconstrained at rule-application time and sepref
    commits without backtracking; they need per-implementation op names
    (\<open>op_ol_empty\<close> + \<open>fold_ol_empty\<close>, the \<open>list_custom_empty\<close> idiom). The same latent
    issue exists between \<open>os_empty\<close> (registered for generic \<open>op_list_empty\<close> in
    \<open>IICF_Open_List\<close>) and the array-list empty rules \<emdash> whichever is declared last wins.\<close>

end
