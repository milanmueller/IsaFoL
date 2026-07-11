section \<open>Implementation of Lists by Open Singly Linked Lists\<close>
theory IICF_Open_List
  imports Isabelle_LLVM.IICF Isabelle_LLVM.LLVM_DS_Open_List
begin

text \<open>Implementation of (parts of) the IICF list interface by open singly linked lists
  (\<open>LLVM_DS_Open_List\<close>), following the structure of \<open>IICF_Array_List\<close>.\<close>

subsection \<open>Additional Operations on Open Lists\<close>

text \<open>Operations on open lists which are not provided by \<open>LLVM_DS_Open_List\<close>.\<close>

definition os_hd :: \<open>'a::llvm_rep os_list \<Rightarrow> 'a llM\<close> where[llvm_code]:
  \<open>os_hd p = doM { v \<leftarrow> ll_load p; Mreturn (node.val v)}\<close>

lemma os_hd_rule[vcg_rules]:
  \<open>xs \<noteq> [] \<Longrightarrow> llvm_htriple (\<upharpoonleft>os_list_assn xs r) (os_hd r) (\<lambda>x. \<up>(x=hd xs) ** \<upharpoonleft>os_list_assn xs r)\<close>
  apply (cases xs; simp)
  unfolding os_hd_def os_list_assn_def
  by vcg

definition os_tl :: \<open>'a::llvm_rep os_list \<Rightarrow> 'a os_list llM\<close> where[llvm_code]:
  \<open>os_tl p = doM {
    n \<leftarrow> ll_load p;
    ll_free p;
    Mreturn (node.next n)
  }\<close>

lemma os_tl_rule[vcg_rules]:
  \<open>xs \<noteq> [] \<Longrightarrow> llvm_htriple (\<upharpoonleft>os_list_assn xs r) (os_tl r) (\<lambda>x. \<upharpoonleft>os_list_assn (tl xs) x)\<close>
  apply (cases xs; simp)
  unfolding os_tl_def os_list_assn_def
  by vcg

text \<open>Auxiliary lemmas for list segments: splitting off and re-attaching single nodes.\<close>

lemma lseg_singleton: \<open>lseg [x] p q = \<upharpoonleft>ll_bpto (Node x q) p\<close>
  by (simp add: sep_algebra_simps)

lemma lseg_snoc: \<open>lseg ys p q ** \<upharpoonleft>ll_bpto (Node x r) q \<turnstile> lseg (ys@[x]) p r\<close>
  by (metis lseg_fuse lseg_singleton)

lemma lseg_pure_partD:
  \<open>pure_part (lseg l p s) \<Longrightarrow> l = [] \<longrightarrow> p = s\<close>
  by (cases l) auto

lemma lseg_reassemble:
  assumes \<open>n < length xs\<close>
  shows \<open>lseg (take n xs) p q ** \<upharpoonleft>ll_bpto (Node (xs ! n) r) q ** lseg (drop (Suc n) xs) r null
          \<turnstile> lseg xs p null\<close>
proof -
  have 1: \<open>take n xs @ [xs ! n] = take (Suc n) xs\<close>
    using assms by (simp add: take_Suc_conv_app_nth)
  have \<open>lseg (take n xs) p q ** \<upharpoonleft>ll_bpto (Node (xs ! n) r) q \<turnstile> lseg (take (Suc n) xs) p r\<close>
    using lseg_snoc[of \<open>take n xs\<close> p q \<open>xs ! n\<close> r] unfolding 1 .
  hence \<open>(lseg (take n xs) p q ** \<upharpoonleft>ll_bpto (Node (xs ! n) r) q) ** lseg (drop (Suc n) xs) r null
    \<turnstile> lseg (take (Suc n) xs) p r ** lseg (drop (Suc n) xs) r null\<close>
    by (rule conj_entails_mono[OF _ entails_refl])
  also have \<open>lseg (take (Suc n) xs) p r ** lseg (drop (Suc n) xs) r null \<turnstile> lseg xs p null\<close>
    using lseg_fuse[of \<open>take (Suc n) xs\<close> p r \<open>drop (Suc n) xs\<close> null] by simp
  finally have R: \<open>(lseg (take n xs) p q ** \<upharpoonleft>ll_bpto (Node (xs ! n) r) q) ** lseg (drop (Suc n) xs) r null
    \<turnstile> lseg xs p null\<close> .
  show ?thesis using R by (simp add: sep_conj_assoc)
qed

definition os_list_get :: \<open>'a::llvm_rep os_list \<Rightarrow> 'b::len2 word \<Rightarrow> 'a llM\<close> where [llvm_code]:
  \<open>os_list_get p\<^sub>0 i\<^sub>0 = doM {
    (p, _) \<leftarrow> llc_while
      (\<lambda>(_, i). ll_cmp (i \<noteq> 0))
      (\<lambda>(p, i). doM {
        n \<leftarrow> ll_load p;
        Mreturn (node.next n, i - signed_nat 1)
      }) (p\<^sub>0, i\<^sub>0);
    n \<leftarrow> ll_load p;
    Mreturn (node.val n)
  }\<close>

context begin

lemma take_shift_snoc:
  assumes \<open>0 < i\<close> \<open>i \<le> n\<close> \<open>n < length xs\<close>
  shows \<open>take (n - (i - 1)) xs = take (n - i) xs @ [xs ! (n - i)]\<close>
proof -
  from assms have A: \<open>n - (i - 1) = Suc (n - i)\<close> by auto
  from assms have B: \<open>n - i < length xs\<close> by auto
  show ?thesis unfolding A by (rule take_Suc_conv_app_nth[OF B])
qed

lemma take_shift_snoc':
  assumes \<open>0 < i\<close> \<open>i \<le> n\<close> \<open>n < length xs\<close>
  shows \<open>take (Suc n - i) xs = take (n - i) xs @ [xs ! (n - i)]\<close>
proof -
  from assms have A: \<open>Suc n - i = Suc (n - i)\<close> by auto
  from assms have B: \<open>n - i < length xs\<close> by auto
  show ?thesis unfolding A by (rule take_Suc_conv_app_nth[OF B])
qed

lemma drop_shift:
  assumes \<open>0 < i\<close> \<open>i \<le> n\<close> \<open>n < length xs\<close>
  shows \<open>drop (n - i) xs = xs ! (n - i) # drop (n - (i - 1)) xs\<close>
proof -
  from assms have A: \<open>n - (i - 1) = Suc (n - i)\<close> by auto
  from assms have B: \<open>n - i < length xs\<close> by auto
  show ?thesis unfolding A by (rule Cons_nth_drop_Suc[OF B, symmetric])
qed

lemma drop_head_exit:
  assumes \<open>n < length xs\<close>
  shows \<open>drop n xs = xs ! n # drop (Suc n) xs\<close>
  by (rule Cons_nth_drop_Suc[OF assms, symmetric])

text \<open>Invariant preservation for the loop step of \<open>os_list_get\<close>: the traversed
  prefix grows by the node just visited.\<close>
lemma os_get_step_entails:
  assumes \<open>0 < t\<close> \<open>t \<le> n\<close> \<open>n < length xs\<close> \<open>\<flat>\<^sub>psnat.assn (t - Suc 0) rb\<close>
  shows \<open>ENTAILS
    (\<upharpoonleft>ll_bpto (Node (xs ! (n - t)) s) a ** lseg (drop (Suc n - t) xs) s null
      ** lseg (take (n - t) xs) p a)
    (EXS x. (EXS xa. \<upharpoonleft>snat.assn xa rb ** lseg (take (n - xa) xs) p s
      ** lseg (drop (n - xa) xs) s null ** \<up>(xa \<le> n) ** \<up>\<^sub>!(x = xa))
      ** \<up>\<^sub>d((x, t) \<in> measure id) ** \<box>)\<close>
proof -
  have A: \<open>n - (t - Suc 0) = Suc n - t\<close> using assms(1,2) by auto
  have B: \<open>t - Suc 0 \<le> n\<close> using assms(2) by simp
  have R: \<open>(\<upharpoonleft>ll_bpto (Node (xs ! (n - t)) s) a ** lseg (drop (Suc n - t) xs) s null
      ** lseg (take (n - t) xs) p a)
    = ((lseg (take (n - t) xs) p a ** \<upharpoonleft>ll_bpto (Node (xs ! (n - t)) s) a)
      ** lseg (drop (Suc n - t) xs) s null)\<close>
    by (simp add: sep_conj_aci)
  have S: \<open>lseg (take (n - t) xs) p a ** \<upharpoonleft>ll_bpto (Node (xs ! (n - t)) s) a
      \<turnstile> lseg (take (Suc n - t) xs) p s\<close>
    using lseg_snoc[of \<open>take (n - t) xs\<close> p a \<open>xs ! (n - t)\<close> s]
    by (simp add: take_shift_snoc'[OF assms(1,2,3)])
  have SP: \<open>\<upharpoonleft>ll_bpto (Node (xs ! (n - t)) s) a ** lseg (drop (Suc n - t) xs) s null
      ** lseg (take (n - t) xs) p a
    \<turnstile> lseg (take (Suc n - t) xs) p s ** lseg (drop (Suc n - t) xs) s null\<close>
    unfolding R by (rule conj_entails_mono[OF S entails_refl])
  show ?thesis
    unfolding ENTAILS_def
    apply (rule entails_trans[OF SP])
    apply (simp add: sep_conj_exists sep_algebra_simps)
    apply (rule entails_exI[where x=\<open>t - Suc 0\<close>])
    apply (rule entails_exI[where x=\<open>t - Suc 0\<close>])
    using assms B by (simp add: A vcg_tag_defs extract_pure_assn snat.assn_pure sep_algebra_simps)
qed

text \<open>At loop exit the value node is read; re-assemble the full list.\<close>
private lemma os_get_exit_entails:
  assumes \<open>n < length xs\<close>
  shows \<open>ENTAILS
    (\<upharpoonleft>ll_bpto (Node (xs ! n) s) a ** lseg (drop (Suc n) xs) s null ** lseg (take n xs) p a)
    (lseg xs p null)\<close>
  unfolding ENTAILS_def
  using lseg_reassemble[OF assms, of p a s] by (simp add: sep_conj_aci)

lemma os_list_get_rule[vcg_rules]:
  \<open>llvm_htriple
    (\<upharpoonleft>os_list_assn xs p ** \<upharpoonleft>snat.assn n nn ** \<up>(n < length xs))
    (os_list_get p nn)
    (\<lambda>v. \<up>(v = xs ! n) ** \<upharpoonleft>os_list_assn xs p)\<close>
  unfolding os_list_get_def
  apply (rewrite annotate_llc_while [where
    I="\<lambda>(q, ii) t. EXS i. \<upharpoonleft>snat.assn i ii
                 ** lseg (take (n - i) xs) p q
                 ** lseg (drop (n - i) xs) q null
                 ** \<up>(i \<le> n)
                 ** \<up>\<^sub>!(t = i)"
    and R="measure id"])
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
      by (rule os_get_exit_entails; assumption)
    by (tactic \<open>Defer_Slot.remove_slot_tac\<close>)
  by (tactic \<open>Defer_Slot.remove_slot_tac\<close>)

end

definition os_list_length :: \<open>'a::llvm_rep os_list \<Rightarrow> 'b::len2 word llM\<close> where [llvm_code]:
  \<open>os_list_length p\<^sub>0 \<equiv> doM {
    (_, i) \<leftarrow> llc_while
      (\<lambda>(p, _). ll_cmp (p \<noteq> null))
      (\<lambda>(p, i). doM {
        nd \<leftarrow> ll_load p;
        i \<leftarrow> ll_add i (signed_nat 1);
        Mreturn (node.next nd, i)
      }) (p\<^sub>0, signed_nat 0);
    Mreturn i
  }\<close>

lemma to_bool_from_bool[simp]: \<open>to_bool (from_bool \<phi> :: 1 word) = \<phi>\<close>
  by (cases \<phi>) (auto simp: from_bool_def)

text \<open>The library's \<open>ll_ptrcmp\<close> null-comparison support is commented out
  (TODO in @{theory Isabelle_LLVM.LLVM_Shallow_RS}); we derive the rule needed for null-check loop guards.\<close>
context begin
interpretation llvm_prim_arith_setup .

lemma ll_ptrcmp_ne_null_simp:
  \<open>ll_ptrcmp_ne a null = doM { Mreturn (from_bool (a \<noteq> null))}\<close>
  by (vcg_normalize; simp add: eq_commute[of null])

lemma ll_ptrcmp_ne_null_rule[vcg_rules]:
  \<open>llvm_htriple \<box> (ll_ptrcmp_ne a null) (\<lambda>r. \<upharpoonleft>bool.assn (a \<noteq> null) r)\<close>
  unfolding ll_ptrcmp_ne_null_simp
  supply [simp] = bool.assn_def
  by vcg

end

text \<open>NOTE: without the bound \<open>length xs < max_snat LENGTH('b)\<close> the counter may
  overflow, so the rule is stated with this precondition, which also allows a
  \<open>snat.assn\<close> result. The invariant tracks the traversed prefix \<open>take i xs\<close>; the
  disjunct \<open>i < length xs \<or> p' = null\<close> makes the non-emptiness of the remaining
  suffix available purely in the loop step (the guard is on the pointer, so this
  is otherwise spatial knowledge, cf. \<open>lseg_pure_partD\<close>).\<close>
context begin

private lemma take_snoc:
  \<open>i < length xs \<Longrightarrow> take (Suc i) xs = take i xs @ [xs ! i]\<close>
  by (rule take_Suc_conv_app_nth)

private lemma take_snoc':
  \<open>i < length xs \<Longrightarrow> take (i + 1) xs = take i xs @ [xs ! i]\<close>
  by (simp add: take_Suc_conv_app_nth)

private lemma drop_plus1: \<open>drop (i + 1) xs = drop (Suc i) xs\<close>
  by simp

private lemma drop_head:
  \<open>i < length xs \<Longrightarrow> drop i xs = xs ! i # drop (Suc i) xs\<close>
  by (simp add: Cons_nth_drop_Suc)

private lemma os_length_step_entails:
  assumes \<open>x < length xs\<close> \<open>\<flat>\<^sub>psnat.assn (Suc x) rc\<close>
  shows \<open>ENTAILS
    (\<upharpoonleft>ll_bpto (Node (xs ! x) xa) a ** lseg (drop (Suc x) xs) xa null ** lseg (take x xs) p a)
    (EXS xb. (EXS x'. \<upharpoonleft>snat.assn x' rc ** lseg (take x' xs) p xa ** lseg (drop x' xs) xa null
        ** \<up>(x' \<le> length xs \<and> (x' < length xs \<or> xa = null)) ** \<up>\<^sub>!(xb = length xs - x'))
      ** \<up>\<^sub>d((xb, length xs - x) \<in> measure id) ** \<box>)\<close>
proof -
  have R: \<open>(\<upharpoonleft>ll_bpto (Node (xs ! x) xa) a ** lseg (drop (Suc x) xs) xa null
      ** lseg (take x xs) p a)
    = ((lseg (take x xs) p a ** \<upharpoonleft>ll_bpto (Node (xs ! x) xa) a)
      ** lseg (drop (Suc x) xs) xa null)\<close>
    by (simp add: sep_conj_aci)
  have S: \<open>lseg (take x xs) p a ** \<upharpoonleft>ll_bpto (Node (xs ! x) xa) a
      \<turnstile> lseg (take (Suc x) xs) p xa\<close>
    using lseg_snoc[of \<open>take x xs\<close> p a \<open>xs ! x\<close> xa]
    by (simp add: take_snoc[OF assms(1)])
  have SP: \<open>\<upharpoonleft>ll_bpto (Node (xs ! x) xa) a ** lseg (drop (Suc x) xs) xa null
      ** lseg (take x xs) p a
    \<turnstile> lseg (take (Suc x) xs) p xa ** lseg (drop (Suc x) xs) xa null\<close>
    unfolding R by (rule conj_entails_mono[OF S entails_refl])
  show ?thesis
    unfolding ENTAILS_def
    apply (rule entails_pureI)
    apply (rule entails_trans[OF SP])
    apply (simp add: sep_conj_exists sep_algebra_simps)
    apply (rule entails_exI[where x=\<open>length xs - Suc x\<close>])
    apply (rule entails_exI[where x=\<open>Suc x\<close>])
    using assms
    by (auto simp: vcg_tag_defs extract_pure_assn snat.assn_pure
      sep_algebra_simps pred_lift_extract_simps entails_def
      dest!: pure_part_split_conj dest: lseg_pure_partD)
qed

lemma os_list_length_rule[vcg_rules]:
  \<open>length xs < max_snat LENGTH('b) \<Longrightarrow> llvm_htriple
    (\<upharpoonleft>os_list_assn xs p)
    (os_list_length p :: 'b::len2 word llM)
    (\<lambda>n. \<upharpoonleft>snat.assn (length xs) n ** \<upharpoonleft>os_list_assn xs p)\<close>
  unfolding os_list_length_def
  apply (rewrite annotate_llc_while [where
    I = \<open>\<lambda>(p', ii) t. EXS i. \<upharpoonleft>snat.assn i ii
                 ** lseg (take i xs) p p'
                 ** lseg (drop i xs) p' null
                 ** \<up>(i \<le> length xs \<and> (i < length xs \<or> p' = null))
                 ** \<up>\<^sub>!(t = length xs - i)\<close>
    and R = \<open>measure id\<close>])
  supply [simp] = os_list_assn_def drop_head take_snoc take_snoc' drop_plus1
    lseg_append lseg_singleton sep_conj_exists
  apply vcg_monadify
  apply vcg'
  subgoal by (rule os_length_step_entails; assumption)
  subgoal for asf r a b x ra sa
    apply (rule impI)
    apply hypsubst
    apply vcg'
    done
  by (tactic \<open>Defer_Slot.remove_slot_tac\<close>)

end

subsubsection \<open>Generic Element-wise Equality\<close>

text \<open>Template, parameterized by an element comparison \<open>eqi\<close>. The rule is proven in
  \<open>IICF_Owning_List\<close> (\<open>ol_eq_rule\<close>) since it is stated against \<open>ol_assn\<close> \<emdash> note that
  \<open>ol_assn\<close> is NOT in scope here, so stating the rule in this theory would silently turn
  it into a free variable. NOTE: \<open>os_eq\<close> is higher-order in \<open>eqi\<close>, so no \<open>[llvm_code]\<close>
  on the template \<emdash> instances must be specialized first-order for code export
  (cf. \<open>ol_delete\<close> in \<open>IICF_Owning_List\<close>).\<close>

partial_function (M) os_eq :: \<open>('c::llvm_rep \<Rightarrow> 'c \<Rightarrow> 1 word llM) \<Rightarrow> 'c os_list \<Rightarrow> 'c os_list \<Rightarrow> 1 word llM\<close> where
  \<open>os_eq eqi p q = (
    if p = null then Mreturn (from_bool (q = null))
    else if q = null then Mreturn 0
    else doM {
      np \<leftarrow> ll_load p; nq \<leftarrow> ll_load q;
      b \<leftarrow> eqi (node.val np) (node.val nq);
      if to_bool b then os_eq eqi (node.next np) (node.next nq)
      else Mreturn 0 })\<close>

subsubsection \<open>Copying a list\<close>

partial_function (M) os_copy :: \<open>'c::llvm_rep os_list \<Rightarrow> 'c os_list llM\<close> where [llvm_code]:
  \<open>os_copy p = (if p = null then Mreturn null else doM {
    n \<leftarrow> ll_load p;
    t \<leftarrow> os_copy (node.next n);
    os_prepend (node.val n) t
  })\<close> 


subsection \<open>List Interface Implementation\<close>

abbreviation (input) \<open>raw_os_assn \<equiv> \<upharpoonleft>os_list_assn\<close>

definition os_assn where \<open>os_assn A \<equiv> hr_comp raw_os_assn (\<langle>the_pure A\<rangle>list_rel)\<close>

thm lseg.simps

lemma os_copy_rule:
  \<open>llvm_htriple (raw_os_assn xs p) (os_copy p) (\<lambda>r. raw_os_assn xs p ** raw_os_assn xs r)\<close>
proof (induction xs arbitrary: p)
  case Nil
  then show ?case
    apply (subst os_copy.simps)
    unfolding os_list_assn_def
    by vcg
next
  case (Cons x xs)
  note [vcg_rules] = Cons.IH
  show ?case
    supply [simp, named_ss fri_prepare_simps] = os_list_assn_simps
    supply [simp] = sep_conj_exists
    apply (subst os_copy.simps)
    apply (cases \<open>p = null\<close>; simp)
    by vcg
qed

lemma raw_os_assn_free[sepref_frame_free_rules]: \<open>MK_FREE raw_os_assn os_delete\<close>
  apply rule by vcg

lemma os_assn_free[sepref_frame_free_rules]: \<open>MK_FREE (os_assn A) os_delete\<close>
  unfolding os_assn_def by (rule sepref_frame_free_rules)+

text \<open>\<open>os_delete\<close> appears in synthesized code (sepref inserts it as the free function
  for dropped open lists); the library declares no code equations for it, so export
  needs them here. First-order, so the recursion equations export directly.\<close>
lemmas [llvm_code] = os_delete.simps

context
  notes [simp] = refine_pw_simps
begin

private lemma n_unf: \<open>hr_comp raw_os_assn (\<langle>the_pure A\<rangle>list_rel) = os_assn A\<close>
  unfolding os_assn_def ..

context
  notes [fcomp_norm_unfold] = n_unf
begin

private method m_ref =
  ((unfold snat_rel_def snat.assn_is_rel[symmetric] bool1_rel_def bool.assn_is_rel[symmetric])?,
    sepref_to_hoare, vcg_monadify, vcg')

lemma os_empty_hnr_aux:
  \<open>(uncurry0 os_empty, uncurry0 (RETURN op_list_empty)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a raw_os_assn\<close>
  by m_ref
sepref_decl_impl os_empty: os_empty_hnr_aux .

lemma os_is_empty_hnr_aux:
  \<open>(os_is_empty, RETURN o op_list_is_empty) \<in> raw_os_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding bool1_rel_def bool.assn_is_rel[symmetric]
  apply sepref_to_hoare
  apply vcg_monadify
  apply vcg'
  subgoal
    by (auto simp: ENTAILS_def entails_def bool.assn_def from_bool_def
      sep_algebra_simps pred_lift_extract_simps split: bool.splits)
  by (tactic \<open>Defer_Slot.remove_slot_tac\<close>)
sepref_decl_impl os_is_empty: os_is_empty_hnr_aux .

lemma os_hd_hnr_aux:
  \<open>(os_hd, mop_list_hd) \<in> raw_os_assn\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
  by m_ref
sepref_decl_impl (ismop) os_hd: os_hd_hnr_aux .

lemma os_tl_hnr_aux:
  \<open>(os_tl, mop_list_tl) \<in> raw_os_assn\<^sup>d \<rightarrow>\<^sub>a raw_os_assn\<close>
  by m_ref
sepref_decl_impl (ismop) os_tl: os_tl_hnr_aux .

lemma os_prepend_hnr_aux:
  \<open>(uncurry os_prepend, uncurry (RETURN oo op_list_prepend)) \<in> id_assn\<^sup>k *\<^sub>a raw_os_assn\<^sup>d \<rightarrow>\<^sub>a raw_os_assn\<close>
  by m_ref
sepref_decl_impl os_prepend: os_prepend_hnr_aux .

lemma os_get_hnr_aux:
  \<open>(uncurry os_list_get, uncurry mop_list_get) \<in> raw_os_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
  by m_ref
sepref_decl_impl (ismop) os_get: os_get_hnr_aux .

context
  fixes l_dummy :: \<open>'l::len2 itself\<close>
  and L defines [simp]: \<open>L \<equiv> LENGTH('l)\<close>
begin

lemma os_length_hnr_aux:
  \<open>(os_list_length, RETURN o op_list_length)
    \<in> [\<lambda>xs. length xs < max_snat L]\<^sub>a raw_os_assn\<^sup>k \<rightarrow> snat_assn' TYPE('l)\<close>
  by m_ref
sepref_decl_impl os_length: os_length_hnr_aux
  by (auto simp: fun_rel_def dest: list_rel_imp_same_length)

end

lemma os_copy_hnr: \<open>(os_copy, RETURN o COPY) \<in> raw_os_assn\<^sup>k \<rightarrow>\<^sub>a raw_os_assn\<close>
  supply [vcg_rules] = os_copy_rule
  by m_ref

end


end

subsection \<open>Interface Coverage\<close>

text \<open>Status of the IICF list interface (\<open>sepref_decl_op\<close>s in \<open>IICF_List\<close>) for \<open>os_assn\<close>:

  Implemented:
    \<^item> \<open>op_list_empty\<close>      (\<open>os_empty\<close>)
    \<^item> \<open>op_list_is_empty\<close>   (\<open>os_is_empty\<close>)
    \<^item> \<open>op_list_hd\<close>         (\<open>os_hd\<close>)
    \<^item> \<open>op_list_tl\<close>         (\<open>os_tl\<close>)
    \<^item> \<open>op_list_prepend\<close>    (\<open>os_prepend\<close>)
    \<^item> \<open>op_list_get\<close>        (\<open>os_list_get\<close>)
    \<^item> \<open>op_list_length\<close>     (\<open>os_list_length\<close>, requires \<open>length xs < max_snat\<close>)

  Still missing:
    \<^item> \<open>op_list_replicate\<close>
    \<^item> \<open>op_list_copy\<close>
    \<^item> \<open>op_list_append\<close>     (append at the back, O(n) on a singly linked list)
    \<^item> \<open>op_list_concat\<close>
    \<^item> \<open>op_list_take\<close>       (plan: BOTH a copying (\<open>xs\<^sup>k\<close>) and a destructive (\<open>xs\<^sup>d\<close>, sever link +
                            free suffix) rule against the same op; sepref picks by liveness.
                            Needed for \<open>msort\<close>, which uses \<open>xs\<close> twice: copying \<open>take\<close> first,
                            destructive \<open>drop\<close> for the last use. Copying can be implemented as
                            prepend-copy + \<open>os_reverse\<close> (raw op with vcg rule already exists).)
    \<^item> \<open>op_list_drop\<close>       (same plan: copying + destructive (walk + free prefix, O(n), no
                            allocation) variants)
    \<^item> \<open>op_list_set\<close>
    \<^item> \<open>op_list_last\<close>
    \<^item> \<open>op_list_butlast\<close>
    \<^item> \<open>op_list_pop_last\<close>
    \<^item> \<open>op_list_contains\<close>
    \<^item> \<open>op_list_swap\<close>
    \<^item> \<open>op_list_rotate1\<close>
    \<^item> \<open>op_list_rev\<close>        (raw op \<open>os_reverse\<close> with vcg rule already exists in \<open>LLVM_DS_Open_List\<close>;
                            only the \<open>hnr\<close> interface binding is missing)
    \<^item> \<open>op_list_index\<close>
    \<^item> \<open>op_split_list\<close>      (destructive split \<open>xs\<^sup>d \<rightarrow> take/drop pair\<close>: walk n nodes, sever the
                            link \<emdash> zero-allocation alternative to \<open>take\<close>+\<open>drop\<close> for \<open>msort\<close>,
                            but requires the abstract program to bind both halves at once)
    \<^item> \<open>op_join_list\<close>

  Further raw operations available in \<open>LLVM_DS_Open_List\<close> without an interface counterpart:
  \<open>os_pop\<close> (destructive \<open>hd\<close>+\<open>tl\<close> in one traversal-free step) and \<open>os_rem\<close> (\<open>removeAll\<close>,
  which is not part of the IICF list interface).\<close>

subsection \<open>Ad-Hoc Regression Tests\<close>

text \<open>Small survey of what synthesizes against \<open>os_assn\<close>: simple functions on
  8-bit-word elements, functions on lists of tuples, and pattern matching.

  Summary of the findings:
    \<^item> if/is-empty/hd/prepend/ASSERT-guarded length and get all synthesize directly,
      including bare word literals (test 2) and pair elements via
      \<open>id_assn \<times>\<^sub>a id_assn\<close> (tests 9, 10).
    \<^item> Pattern matching on \<^emph>\<open>tuples\<close> (\<open>case p of (a, b) \<Rightarrow> \<dots>\<close>) works out of the box.
    \<^item> Pattern matching on \<^emph>\<open>lists\<close> does NOT work directly: there are no sepref rules
      for the \<open>case_list\<close> combinator, so translation fails immediately
      (tests 5, 7, 11). Rewriting the case expression with @{thm list.case_eq_if}
      (\<open>case xs of [] \<Rightarrow> a | y # ys \<Rightarrow> f y ys  \<leadsto>  if xs = [] then a else f (hd xs) (tl xs)\<close>)
      makes all of them go through (tests 6, 8, 12) \<emdash> including the destructive
      destructure-and-rebuild (test 8) and a pair pattern nested inside the list
      pattern (test 12).\<close>

experiment
begin

  text \<open>Elements: raw 8-bit words (chars), refined by \<open>id_assn\<close>.\<close>

  abbreviation w8s_assn :: \<open>8 word list \<Rightarrow> 8 word os_list \<Rightarrow> assn\<close> where
    \<open>w8s_assn \<equiv> os_assn id_assn\<close>

  abbreviation w8w64s_assn :: \<open>(8 word \<times> 64 word) list \<Rightarrow> (8 word \<times> 64 word) os_list \<Rightarrow> assn\<close> where
    \<open>w8w64s_assn \<equiv> os_assn (id_assn \<times>\<^sub>a id_assn)\<close>

  text \<open>(1) if / is-empty / hd, default passed as parameter \<emdash> works\<close>
  definition hd_dflt :: \<open>8 word \<Rightarrow> 8 word list \<Rightarrow> 8 word\<close> where
    \<open>hd_dflt d xs = (if xs = [] then d else hd xs)\<close>

  sepref_def hd_dflt_impl is \<open>uncurry (RETURN oo hd_dflt)\<close>
    :: \<open>id_assn\<^sup>k *\<^sub>a w8s_assn\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
    unfolding hd_dflt_def by sepref

  text \<open>(2) prepending a word literal \<emdash> works\<close>
  definition cons_zero :: \<open>8 word list \<Rightarrow> 8 word list\<close> where
    \<open>cons_zero xs = 0 # xs\<close>

  sepref_def cons_zero_impl is \<open>RETURN o cons_zero\<close>
    :: \<open>w8s_assn\<^sup>d \<rightarrow>\<^sub>a w8s_assn\<close>
    unfolding cons_zero_def by sepref

  text \<open>(3) length, bound supplied via ASSERT \<emdash> works\<close>
  definition len_test :: \<open>8 word list \<Rightarrow> nat nres\<close> where
    \<open>len_test xs = doN { ASSERT (length xs < max_snat 64); RETURN (length xs) }\<close>

  sepref_def len_test_impl is \<open>len_test\<close>
    :: \<open>w8s_assn\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(64)\<close>
    unfolding len_test_def by sepref

  text \<open>(4) indexed access, bound supplied via ASSERT \<emdash> works\<close>
  definition get_test :: \<open>8 word list \<Rightarrow> nat \<Rightarrow> 8 word nres\<close> where
    \<open>get_test xs i = doN { ASSERT (i < length xs); RETURN (xs ! i) }\<close>

  sepref_def get_test_impl is \<open>uncurry get_test\<close>
    :: \<open>w8s_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(64))\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
    unfolding get_test_def by sepref

  text \<open>(5) pattern matching on the list, direct\<close>
  definition case_hd :: \<open>8 word \<Rightarrow> 8 word list \<Rightarrow> 8 word\<close> where
    \<open>case_hd d xs = (case xs of [] \<Rightarrow> d | y # _ \<Rightarrow> y)\<close>

  text \<open>FAILS: there are no sepref rules for the \<open>case_list\<close> combinator; translation
    does not even start ("Failed to apply initial proof method").
    Rewrite the case expression with @{thm list.case_eq_if} first, see next test.\<close>
  sepref_def case_hd_impl is \<open>uncurry (RETURN oo case_hd)\<close>
    :: \<open>id_assn\<^sup>k *\<^sub>a w8s_assn\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
    unfolding case_hd_def
    apply sepref_dbg_keep
    apply sepref_dbg_trans_keep
    apply sepref_dbg_trans_step_keep
    apply sepref_dbg_side_unfold
    oops

  text \<open>(6) same function, case expression rewritten via @{thm list.case_eq_if} \<emdash> works\<close>
  sepref_def case_hd_impl' is \<open>uncurry (RETURN oo case_hd)\<close>
    :: \<open>id_assn\<^sup>k *\<^sub>a w8s_assn\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
    unfolding case_hd_def list.case_eq_if
    by sepref

  text \<open>(7) destructure and rebuild, direct\<close>
  definition uncons_recons :: \<open>8 word list \<Rightarrow> 8 word list\<close> where
    \<open>uncons_recons xs = (case xs of [] \<Rightarrow> xs | y # ys \<Rightarrow> y # ys)\<close>

  text \<open>FAILS: same \<open>case_list\<close> problem as above.\<close>
  sepref_def uncons_recons_impl is \<open>RETURN o uncons_recons\<close>
    :: \<open>w8s_assn\<^sup>d \<rightarrow>\<^sub>a w8s_assn\<close>
    unfolding uncons_recons_def
    apply sepref_dbg_keep
    oops

  text \<open>(8) destructure and rebuild via @{thm list.case_eq_if} \<emdash> works
    (destructive \<open>hd\<close>/\<open>tl\<close>/prepend on the owned list)\<close>
  sepref_def uncons_recons_impl' is \<open>RETURN o uncons_recons\<close>
    :: \<open>w8s_assn\<^sup>d \<rightarrow>\<^sub>a w8s_assn\<close>
    unfolding uncons_recons_def list.case_eq_if
    by sepref

  text \<open>(9) tuples: second component of the head \<emdash> works
    (pattern matching on pairs is unproblematic)\<close>
  definition snd_hd :: \<open>64 word \<Rightarrow> (8 word \<times> 64 word) list \<Rightarrow> 64 word\<close> where
    \<open>snd_hd d xs = (if xs = [] then d else (case hd xs of (a, b) \<Rightarrow> b))\<close>

  sepref_def snd_hd_impl is \<open>uncurry (RETURN oo snd_hd)\<close>
    :: \<open>id_assn\<^sup>k *\<^sub>a w8w64s_assn\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
    unfolding snd_hd_def by sepref

  text \<open>(10) tuples: building and prepending a pair \<emdash> works\<close>
  definition cons_pair :: \<open>(8 word \<times> 64 word) list \<Rightarrow> 8 word \<Rightarrow> 64 word \<Rightarrow> (8 word \<times> 64 word) list\<close> where
    \<open>cons_pair xs a b = (a, b) # xs\<close>

  sepref_def cons_pair_impl is \<open>uncurry2 (RETURN ooo cons_pair)\<close>
    :: \<open>w8w64s_assn\<^sup>d *\<^sub>a id_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a w8w64s_assn\<close>
    unfolding cons_pair_def by sepref

  text \<open>(11) nested pattern: pair pattern under list pattern, direct\<close>
  definition nested_case :: \<open>64 word \<Rightarrow> (8 word \<times> 64 word) list \<Rightarrow> 64 word\<close> where
    \<open>nested_case d xs = (case xs of [] \<Rightarrow> d | (a, b) # _ \<Rightarrow> b)\<close>

  text \<open>FAILS: the outer \<open>case_list\<close> is the problem again (the inner pair pattern is fine).\<close>
  sepref_def nested_case_impl is \<open>uncurry (RETURN oo nested_case)\<close>
    :: \<open>id_assn\<^sup>k *\<^sub>a w8w64s_assn\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
    unfolding nested_case_def
    apply sepref_dbg_keep
    oops

  text \<open>(12) nested pattern via @{thm list.case_eq_if} \<emdash> works\<close>
  sepref_def nested_case_impl' is \<open>uncurry (RETURN oo nested_case)\<close>
    :: \<open>id_assn\<^sup>k *\<^sub>a w8w64s_assn\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
    unfolding nested_case_def list.case_eq_if by sepref

end

end
