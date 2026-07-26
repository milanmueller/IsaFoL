theory IICF_Copying_List
  imports Isabelle_LLVM.IICF
    Isabelle_LLVM.Proto_EOArray
    Isabelle_LLVM.LLVM_DS_Open_List
begin

text \<open>This Theory defines a "copying list".
  By copying list we mean that the list can hold impure objects,
  for operations that take ownership of an object (i.e. @{term hd}),
  we implement a destructive variant (that will destroy the list)
  and a non-destructive variant that will copy the element and keep
  the list intact. Container elements need to have an implementation of copy.
  It is mostly based on/inspired by @{theory Isabelle_LLVM.LLVM_DS_Open_List}.\<close>

text \<open>TODO list \<emdash> coverage of the @{theory Isabelle_LLVM.IICF_List} interface
  Done:
    \<^item> [x] \<open>op_list_empty\<close>     (\<open>cl_empty_hnr\<close>)
    \<^item> [x] \<open>op_list_prepend\<close>   (\<open>cl_prepend_hnr\<close>; takes ownership of the element)
    \<^item> [x] \<open>op_list_length\<close>    (\<open>cl_length_hnr\<close>)
    \<^item> [x] \<open>COPY\<close>              (\<open>cl_copy_hnr\<close>/\<open>cl_copy_is_copy\<close>)
    \<^item> [x] \<open>op_list_hd\<close>        (\<open>cl_hd\<^sub>k\<close>); will copy the first element and leave list intact
    \<^item> [x] \<open>op_list_pop_hd\<close>    (\<open>os_pop\<close>); (See interface extension below) will move the \<open>hd\<close>
                                          out and also return the \<open>tl\<close> of the list.

  Infrastructure (not interface ops):
    \<^item> [x] \<open>MK_FREE\<close> deep free  (\<open>cl_assn_free\<close>, in \<open>copy_free_context\<close>)

  Missing \<emdash> need destructive + copying variants (element leaves the list):
    \<^item> [ ] \<open>op_list_get\<close>
    \<^item> [ ] \<open>op_list_last\<close>
    \<^item> [ ] \<open>op_list_pop_last\<close>

  Missing \<emdash> structural (no element extracted, single variant suffices):
    \<^item> [ ] \<open>op_list_is_empty\<close>
    \<^item> [ ] \<open>op_list_replicate\<close> (needs element copy for n > 1)
    \<^item> [ ] \<open>op_list_append\<close>    (snoc; O(n) without a tail pointer)
    \<^item> [ ] \<open>op_list_concat\<close> / \<open>op_join_list\<close>
    \<^item> [ ] \<open>op_list_take\<close>      (must free the dropped suffix)
    \<^item> [ ] \<open>op_list_drop\<close>      (must free the dropped prefix)
    \<^item> [ ] \<open>op_list_set\<close>       (must free the overwritten element)
    \<^item> [ ] \<open>op_list_tl\<close>        (must free the head element)
    \<^item> [ ] \<open>op_list_butlast\<close>   (must free the last element)
    \<^item> [ ] \<open>op_list_swap\<close>
    \<^item> [ ] \<open>op_list_rotate1\<close>
    \<^item> [ ] \<open>op_list_rev\<close>
    \<^item> [ ] \<open>op_split_list\<close>
    \<^item> [ ] \<open>op_list_contains\<close>  (needs an element-equality parameter)
    \<^item> [ ] \<open>op_list_index\<close>     (needs an element-equality parameter)\<close>

section \<open>Extending List Interface\<close>

text \<open>The list interface (see above) does not define a `pop_first` operation.
  In addition to our copying `hd` implementation, we might want a destructive
  variant for efficiency, so we define `list_pop_hd` here.\<close>
term op_list_pop_last
context notes [simp] = List.null_iff[symmetric] and [simp del] = List.null_iff begin
  sepref_decl_op list_pop_hd: \<open>\<lambda>l. (hd l, tl l)\<close> :: \<open>[\<lambda>l. l \<noteq> []]\<^sub>f \<langle>A\<rangle>list_rel \<rightarrow> A \<times>\<^sub>r \<langle>A\<rangle>list_rel\<close> .
end

section \<open>Basic Setup\<close>
text \<open>Based on @{theory \<open>Isabelle_LLVM.LLVM_DS_Open_List\<close>}\<close>

type_synonym 'a cl_list = \<open>'a node ptr\<close>

(* Owning list segment *)
definition \<open>olseg A xs p s \<equiv> EXS xsi. lseg xsi p s ** \<upharpoonleft>(list_assn (mk_assn A)) xs xsi\<close> 

(* Owning list assertion *)
definition \<open>cl_assn A \<equiv> mk_assn (\<lambda>xs p. olseg A xs p null)\<close>
definition \<open>cl_assn' A \<equiv> \<upharpoonleft>(cl_assn A)\<close>
 
lemma cl_assn_simps:
  \<open>cl_assn' A [] p = \<up>(p=null)\<close>
  \<open>cl_assn' A xs null = \<up>(xs=[])\<close>
  \<open>cl_assn' A (x#xs) p = (EXS c q. \<upharpoonleft>ll_bpto (Node c q) p ** A x c ** cl_assn' A xs q)\<close>
  unfolding cl_assn'_def cl_assn_def olseg_def
  subgoal by (auto simp: sep_algebra_simps)
  subgoal by (auto simp: sep_algebra_simps)
  subgoal
    apply (auto simp: sep_algebra_simps list_assn_cons1_conv)
    (* Sledgehammer finds this - TODO: make nicer *)
    proof -
    { fix bb :: 'b and pp :: "'b node ptr" and bbs :: "'b list" and aa :: llvm_amemory and bba :: 'b and ppa :: "'b node ptr" and bbsa :: "'b list"
      have "\<not> (\<upharpoonleft>ll_bpto (Node bb pp) p \<and>* A x bb \<and>* lseg bbs pp null \<and>* \<upharpoonleft>(list_assn (mk_assn A)) xs bbs) aa \<and> \<not> (\<upharpoonleft>ll_bpto (Node bba ppa) p \<and>* lseg bbsa ppa null \<and>* A x bba \<and>* \<upharpoonleft>(list_assn (mk_assn A)) xs bbsa) aa \<or> (\<exists>b pa bs ba pb bsa. (\<upharpoonleft>ll_bpto (Node b pa) p \<and>* A x b \<and>* lseg bs pa null \<and>* \<upharpoonleft>(list_assn (mk_assn A)) xs bs) aa \<and> (\<upharpoonleft>ll_bpto (Node ba pb) p \<and>* lseg bsa pb null \<and>* A x ba \<and>* \<upharpoonleft>(list_assn (mk_assn A)) xs bsa) aa)"
     by (smt (verit) sep.mult.left_commute) }
    then show "(\<lambda>a. \<exists>b bs pa. (\<upharpoonleft>ll_bpto (Node b pa) p \<and>* lseg bs pa null \<and>* A x b \<and>* \<upharpoonleft>(list_assn (mk_assn A)) xs bs) a) = (\<lambda>a. \<exists>b pa bs. (\<upharpoonleft>ll_bpto (Node b pa) p \<and>* A x b \<and>* lseg bs pa null \<and>* \<upharpoonleft>(list_assn (mk_assn A)) xs bs) a)"
      by meson
    qed
  done 

section \<open>non-destructive, non-copying operations\<close>
text \<open>The following operations can be defined without having to decide
  between a destructive and a non-destructive variant\<close>

definition cl_empty :: \<open>_ cl_list llM\<close> where [llvm_code, llvm_inline]:
  \<open>cl_empty \<equiv> Mreturn null\<close>

lemma os_empty_rule[vcg_rules]: \<open>llvm_htriple \<box> cl_empty (\<lambda>r. cl_assn' A [] r)\<close>
  unfolding cl_empty_def cl_assn'_def cl_assn_def olseg_def
  by vcg

lemma cl_empty_hnr[sepref_fr_rules]:
  \<open>(uncurry0 cl_empty, uncurry0 (RETURN op_list_empty)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a (cl_assn' A)\<close>
  by (sepref_to_hoare; vcg)

text \<open>Note that our prepend implementation implicitly destroys/takes ownership of the
  given object, so caller must (optionally) opt in to copy the object instead.\<close>
definition cl_prepend :: \<open>'a::llvm_rep \<Rightarrow> 'a cl_list \<Rightarrow> 'a cl_list llM\<close> where [llvm_code, llvm_inline]:
  \<open>cl_prepend x p = ll_ref (Node x p)\<close>

lemma cl_prepend_rule[vcg_rules]:
  \<open>llvm_htriple (cl_assn' A xs p ** A x xi) (cl_prepend xi p) (\<lambda>r. cl_assn' A (x # xs) r)\<close>
  unfolding cl_prepend_def
  supply [simp] = cl_assn_simps
  by vcg

lemma cl_prepend_hnr[sepref_fr_rules]:
  \<open>(uncurry cl_prepend, uncurry (RETURN oo op_list_prepend))
  \<in> A\<^sup>d *\<^sub>a (cl_assn' A)\<^sup>d \<rightarrow>\<^sub>a (cl_assn' A) \<close>
  by (sepref_to_hoare; vcg)

text \<open>Implementing `op_list_length` is surprisingly tricky. The Correctnes proof here
  was found by Anthropic's Fable 5 model.\<close>
definition cl_length :: \<open>'a::llvm_rep cl_list \<Rightarrow> 'b::len2 word llM\<close> where [llvm_code]:
  \<open>cl_length p \<equiv> doM{
    (_, i) \<leftarrow> llc_while
      (\<lambda>(p, _). ll_cmp (p \<noteq> null))
      (\<lambda>(p, i). doM {
        n \<leftarrow> ll_load p;
        i \<leftarrow> ll_add i (signed_nat 1);
        Mreturn (node.next n, i) 
      }) (p, signed_nat 0);
    Mreturn i 
  }\<close>

lemma to_bool_from_bool[simp]: \<open>to_bool (from_bool \<phi> :: 1 word) = \<phi>\<close>
  by (cases \<phi>) (auto simp: from_bool_def)

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

lemma lseg_singleton: \<open>lseg [x] p q = \<upharpoonleft>ll_bpto (Node x q) p\<close>
  by (simp add: sep_algebra_simps)

lemma lseg_snoc: \<open>lseg ys p q ** \<upharpoonleft>ll_bpto (Node x r) q \<turnstile> lseg (ys@[x]) p r\<close>
  by (metis lseg_fuse lseg_singleton)

lemma lseg_pure_partD:
  \<open>pure_part (lseg l p s) \<Longrightarrow> l = [] \<longrightarrow> p = s\<close>
  by (cases l) auto

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

private lemma cl_length_step_entails:
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

lemma cl_length_spine_rule[vcg_rules]:
  \<open>length xs < max_snat LENGTH('l) \<Longrightarrow> llvm_htriple
    (\<upharpoonleft>os_list_assn xs p)
    (cl_length p :: 'l::len2 word llM)
    (\<lambda>n. \<upharpoonleft>snat.assn (length xs) n ** \<upharpoonleft>os_list_assn xs p)\<close>
  unfolding cl_length_def
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
  subgoal by (rule cl_length_step_entails; assumption)
  subgoal for asf r a b x ra sa
    apply (rule impI)
    apply hypsubst
    apply vcg'
    done
  by (tactic \<open>Defer_Slot.remove_slot_tac\<close>)

end

lemma cl_assn'_os_conv:
  \<open>cl_assn' A xs p
    = (EXS xsi. \<up>(length xsi = length xs) ** \<upharpoonleft>os_list_assn xsi p
        ** \<upharpoonleft>(list_assn (mk_assn A)) xs xsi)\<close>
  unfolding cl_assn'_def cl_assn_def olseg_def os_list_assn_def Proto_EOArray.list_assn_def
  by (auto simp: sep_algebra_simps pred_lift_extract_simps fun_eq_iff)

lemma htriple_pre_EXS:
  assumes \<open>\<And>x. llvm_htriple (P x) c Q\<close>
  shows \<open>llvm_htriple (EXS x. P x) c Q\<close>
  apply (rule htripleI)
  apply (clarsimp simp only: STATE_extract(3))
  by (rule htripleD[OF assms])

context begin

private lemma cl_length_aux:
  assumes B: \<open>length xs < max_snat LENGTH('l)\<close> and L: \<open>length xsi = length xs\<close>
  shows \<open>llvm_htriple
    (\<up>(length xsi = length xs) ** \<upharpoonleft>os_list_assn xsi p
      ** \<upharpoonleft>(list_assn (mk_assn A)) xs xsi)
    (cl_length p :: 'l::len2 word llM)
    (\<lambda>n. \<upharpoonleft>snat.assn (length xs) n ** (EXS xsi'. \<up>(length xsi' = length xs)
      ** \<upharpoonleft>os_list_assn xsi' p ** \<upharpoonleft>(list_assn (mk_assn A)) xs xsi'))\<close>
proof -
  have B': \<open>length xsi < max_snat LENGTH('l)\<close> using B L by simp
  note H = frame_rule[OF cl_length_spine_rule[OF B'],
    where F = \<open>\<upharpoonleft>(list_assn (mk_assn A)) xs xsi\<close>]
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

lemma cl_length_rule[vcg_rules]:
  \<open>length xs < max_snat LENGTH('l) \<Longrightarrow> llvm_htriple
    (cl_assn' A xs p)
    (cl_length p :: 'l::len2 word llM)
    (\<lambda>n. \<upharpoonleft>snat.assn (length xs) n ** cl_assn' A xs p)\<close>
  unfolding cl_assn'_os_conv
  apply (rule htriple_pre_EXS)
  subgoal for xsi
    apply (rule htriple_pure_preI)
    apply (rule cl_length_aux)
     apply assumption
    by (auto dest!: pure_part_split_conj)
  done

lemma cl_length_hnr[sepref_fr_rules]:
  \<open>(cl_length, RETURN o op_list_length)
  \<in> [\<lambda>xs. length xs < max_snat LENGTH('l::len2)]\<^sub>a (cl_assn' A)\<^sup>k \<rightarrow> (snat_assn' TYPE('l))\<close>
  unfolding snat_rel_def snat.assn_is_rel[symmetric]
  by (sepref_to_hoare; vcg)

end

text \<open>We define a generic list implementation and require the objects in our
  list to implement a copy and a free function.
  This copying setup is taken from
  `isabelle_llvm/thys/examples/sorting/Sorting_Setup.thy`\<close>

definition "is_copy A cp \<equiv> (cp, RETURN o COPY) \<in> A\<^sup>k \<rightarrow>\<^sub>a A"

lemma is_copy_hnr[sepref_fr_rules]:
  "GEN_ALGO cp (is_copy A) \<Longrightarrow> (cp, RETURN o COPY) \<in> A\<^sup>k \<rightarrow>\<^sub>a A"
  unfolding is_copy_def GEN_ALGO_def by auto

lemma is_copy_pure_gen_algo: "CONSTRAINT is_pure A \<Longrightarrow> GEN_ALGO (Mreturn) (is_copy A)"  
  unfolding is_copy_def GEN_ALGO_def
  by (rule hnr_pure_COPY)

locale copy_free_context =
  fixes A :: \<open>'a \<Rightarrow> 'b::llvm_rep \<Rightarrow> assn\<close>
    and afree_impl :: \<open>'b \<Rightarrow> unit llM\<close>
    and acopy_impl :: \<open>'b \<Rightarrow> 'b llM\<close>
  assumes a_assn_free[sepref_frame_free_rules]: \<open>MK_FREE A afree_impl\<close>
  assumes a_assn_copy[sepref_gen_algo_rules]: \<open>GEN_ALGO acopy_impl (is_copy A)\<close>
begin

lemma acopy_rule[vcg_rules]: \<open>llvm_htriple (A x c) (acopy_impl c) (\<lambda>r. A x c ** A x r)\<close>
proof -
  note HNR = a_assn_copy[unfolded GEN_ALGO_def is_copy_def, to_hnr, unfolded autoref_tag_defs]
  note HT = HNR[THEN hn_refineD]
  show ?thesis
    apply (rule htriple_ent_pre[OF _ htriple_ent_post[OF _ HT]])
    unfolding hn_ctxt_def apply (rule entails_refl)
    subgoal by (auto simp: entails_def sep_algebra_simps)
    subgoal by simp
    done
qed

definition cl_copy :: \<open>'b cl_list \<Rightarrow> 'b cl_list llM\<close> where [llvm_code]:
  \<open>cl_copy \<equiv> MMonad.REC (\<lambda>cl_copy p.
    if p = null then Mreturn null else doM {
      n \<leftarrow> ll_load p;
      cpy \<leftarrow> acopy_impl (node.val n);
      tl \<leftarrow> cl_copy (node.next n);
      cl_prepend cpy tl
    })\<close>

(* Apparently, vcg does not support unfolding for `MMonad.REC`, so we do unfolding manually. *)
lemmas cl_copy_unfold = REC_unfold_extr[OF cl_copy_def, discharge_monos]

lemma cl_copy_rule[vcg_rules]:
  \<open>llvm_htriple
    (cl_assn' A xs xi)
    (cl_copy xi)
    (\<lambda>r. cl_assn' A xs xi ** cl_assn' A xs r)\<close>
proof (induction xs arbitrary: xi)
  case Nil
  then show ?case
    apply (rewrite cl_copy_unfold)
    supply [simp] = cl_assn_simps 
    by vcg
next
  case (Cons a xs)
  note [vcg_rules] = Cons.IH
  then show ?case
    apply (rewrite cl_copy_unfold)
    supply [simp] = cl_assn_simps sep_conj_exists
    by vcg
qed

lemma cl_copy_hnr[sepref_fr_rules]:
  \<open>(cl_copy, RETURN o COPY) \<in> (cl_assn' A)\<^sup>k \<rightarrow>\<^sub>a (cl_assn' A)\<close>
  by (sepref_to_hoare; vcg)

lemma cl_copy_is_copy[sepref_gen_algo_rules]:
  \<open>GEN_ALGO cl_copy (is_copy (cl_assn' A))\<close>
  unfolding GEN_ALGO_def is_copy_def
  by (rule cl_copy_hnr)

text \<open>A deep free: frees the spine and every element. Together with @{thm cl_copy_is_copy}
  this is what allows a copying list to be an *element* of another copying list
  (cf. the nesting experiment below).\<close>
definition cl_free :: \<open>'b cl_list \<Rightarrow> unit llM\<close> where [llvm_code]:
  \<open>cl_free \<equiv> MMonad.REC (\<lambda>cl_free p.
    if p = null then Mreturn () else doM {
      n \<leftarrow> ll_load p;
      ll_free p;
      afree_impl (node.val n);
      cl_free (node.next n)
    })\<close>

lemmas cl_free_unfold = REC_unfold_extr[OF cl_free_def, discharge_monos]

lemma cl_assn_free[sepref_frame_free_rules]: \<open>MK_FREE (cl_assn' A) cl_free\<close>
proof (rule MK_FREEI)
  fix xs p
  show \<open>llvm_htriple (cl_assn' A xs p) (cl_free p) (\<lambda>_. \<box>)\<close>
  proof (induction xs arbitrary: p)
    case Nil
    then show ?case
      apply (rewrite cl_free_unfold)
      supply [simp] = cl_assn_simps
      by vcg
  next
    case (Cons a xs)
    note [vcg_rules] = Cons.IH MK_FREED[OF a_assn_free]
    show ?case
      apply (rewrite cl_free_unfold)
      supply [simp] = cl_assn_simps sep_conj_exists
      by vcg
  qed
qed

definition cl_hd\<^sub>k :: \<open>'b cl_list \<Rightarrow> 'b llM\<close> where [llvm_code]:
  \<open>cl_hd\<^sub>k p \<equiv> doM {
    n \<leftarrow> ll_load p;
    cpy \<leftarrow> acopy_impl (node.val n);
    Mreturn cpy
  }\<close>

lemma cl_hd\<^sub>k_rule[vcg_rules]:
  assumes \<open>xs \<noteq> []\<close>
  shows \<open>llvm_htriple
    (cl_assn' A xs xi)
    (cl_hd\<^sub>k xi)
    (\<lambda>r. cl_assn' A xs xi ** A (hd xs) r)\<close>
  unfolding cl_hd\<^sub>k_def
  apply (cases xs)
  subgoal using assms by simp
  supply [simp] = cl_assn_simps sep_conj_exists
  by vcg

lemma cl_hd\<^sub>k_hnr[sepref_fr_rules]:
  \<open>(cl_hd\<^sub>k, RETURN o op_list_hd) \<in> [\<lambda>xs. xs \<noteq> []]\<^sub>a (cl_assn' A)\<^sup>k \<rightarrow> A\<close>
  by (sepref_to_hoare; vcg)

(* A destructive variant of `hd` is `pop`, which is already implemented for open lists. *)
lemma cl_pop_rule[vcg_rules]:
  assumes \<open>xs \<noteq> []\<close>
  shows \<open>llvm_htriple
    (cl_assn' A xs xi)
    (os_pop xi)
    (\<lambda>(r, xi'). A (hd xs) r ** cl_assn' A (tl xs) xi')\<close>
  unfolding os_pop_def
  apply (cases xs)
  subgoal using assms by simp
  supply [simp] = cl_assn_simps sep_conj_exists
  by vcg

lemma cl_pop_hnr_mop[sepref_fr_rules]:
  \<open>(os_pop, mop_list_pop_hd) \<in> (cl_assn' A)\<^sup>d \<rightarrow>\<^sub>a A \<times>\<^sub>a cl_assn' A\<close>
  supply [simp] = refine_pw_simps 
  by (sepref_to_hoare; vcg)

lemma cl_pop_hnr_op[sepref_fr_rules]:
  \<open>(os_pop, RETURN o op_list_pop_hd) \<in> [\<lambda>xs. xs \<noteq> []]\<^sub>a (cl_assn' A)\<^sup>d \<rightarrow> A \<times>\<^sub>a cl_assn' A\<close>
  supply [simp] = refine_pw_simps 
  by (sepref_to_hoare; vcg)
end

experiment begin

text \<open>Inner lists hold pure elements (64-bit snat numbers), so their copy is @{term Mreturn}
  and their free is a no-op. The outer instantiation then uses the inner list's
  \<open>P.cl_copy\<close>/\<open>P.cl_free\<close> as element copy/free.\<close>

interpretation P: copy_free_context \<open>snat_assn' TYPE(64)\<close> \<open>\<lambda>_. Mreturn ()\<close> Mreturn
  apply unfold_locales
  subgoal by (rule mk_free_pure)
  subgoal by (rule is_copy_pure_gen_algo) simp
  done

interpretation PP: copy_free_context \<open>cl_assn' (snat_assn' TYPE(64))\<close> P.cl_free P.cl_copy
  apply unfold_locales
  subgoal by (rule P.cl_assn_free)
  subgoal by (rule P.cl_copy_is_copy)
  done

definition test_nested :: \<open>(nat list list \<times> nat list list) nres\<close> where
  \<open>test_nested = doN {
    let l1 = [1, 2];
    let l2 = COPY l1;
    let xss = [l1, l2];
    let yss = COPY xss;
    RETURN (xss, yss) 
  }\<close>

sepref_definition test_nested_impl is \<open>uncurry0 test_nested\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a (cl_assn' (cl_assn' (snat_assn' TYPE(64)))) \<times>\<^sub>a (cl_assn' (cl_assn' (snat_assn' TYPE(64))))\<close>
  unfolding test_nested_def
  apply (annot_snat_const "TYPE(64)")
  by sepref

sepref_definition test_nested2_impls is \<open>uncurry0 (RETURN ([[(1::nat),2],[3,4]]))\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a (cl_assn' (cl_assn' (snat_assn' TYPE(64))))\<close>
  apply (annot_snat_const "TYPE(64)")
  by sepref

end

end
