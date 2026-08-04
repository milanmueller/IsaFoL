theory IICF_Copying_List
  imports Isabelle_LLVM.IICF
    Isabelle_LLVM.Proto_EOArray
    Isabelle_LLVM.LLVM_DS_Open_List
begin

text \<open>This Theory defines a "copying list".
  By copying list we mean that the list can hold impure objects.
  For operations that take ownership of an object (i.e. @{term hd}),
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
    \<^item> [x] \<open>op_list_is_empty\<close>  (\<open>os_is_empty\<close>)
    \<^item> [x] \<open>op_list_concat\<close>    (\<open>cl_concat_hnr\<close>; destructively links both lists)
    \<^item> [x] \<open>op_list_append\<close>    (\<open>cl_append_hnr\<close>; snoc, O(n), takes ownership of the element)
    \<^item> [x] \<open>op_list_rev\<close>       (\<open>cl_rev_hnr\<close>; destructive in-place reversal, O(n))

  Infrastructure (not interface ops):
    \<^item> [x] \<open>MK_FREE\<close> deep free  (\<open>cl_assn_free\<close>, in \<open>copy_free_context\<close>)

  Missing, need destructive + copying variants (element leaves the list):
    \<^item> [ ] \<open>op_list_get\<close>
    \<^item> [ ] \<open>op_list_last\<close>
    \<^item> [ ] \<open>op_list_pop_last\<close>

  Missing, structural (no element extracted, single variant suffices):
    \<^item> [ ] \<open>op_list_replicate\<close> (needs element copy for n > 1)
    \<^item> [ ] \<open>op_join_list\<close>
    \<^item> [ ] \<open>op_list_take\<close>      (must free the dropped suffix)
    \<^item> [ ] \<open>op_list_drop\<close>      (must free the dropped prefix)
    \<^item> [ ] \<open>op_list_set\<close>       (must free the overwritten element)
    \<^item> [ ] \<open>op_list_tl\<close>        (must free the head element)
    \<^item> [ ] \<open>op_list_butlast\<close>   (must free the last element)
    \<^item> [ ] \<open>op_list_swap\<close>
    \<^item> [ ] \<open>op_list_rotate1\<close>
    \<^item> [ ] \<open>op_split_list\<close>
    \<^item> [ ] \<open>op_list_contains\<close>  (needs an element-equality parameter)
    \<^item> [ ] \<open>op_list_index\<close>     (needs an element-equality parameter)
\<close>


section \<open>Extending List Interface\<close>

text \<open>The list interface (see above) does not define a `pop_first` operation.
  In addition to our copying `hd` implementation, we might want a destructive
  variant for efficiency, so we define `list_pop_hd` here.\<close>
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
    (* Sledgehammer finds this - TODO: find nicer proof *)
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

subsection \<open>@{term op_list_empty}\<close>

definition cl_empty :: \<open>_ cl_list llM\<close> where [llvm_code, llvm_inline]:
  \<open>cl_empty \<equiv> Mreturn null\<close>

lemma os_empty_rule[vcg_rules]: \<open>llvm_htriple \<box> cl_empty (\<lambda>r. cl_assn' A [] r)\<close>
  unfolding cl_empty_def cl_assn'_def cl_assn_def olseg_def
  by vcg

lemma cl_empty_hnr[sepref_fr_rules]:
  \<open>(uncurry0 cl_empty, uncurry0 (RETURN op_list_empty)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a (cl_assn' A)\<close>
  by (sepref_to_hoare; vcg)

subsection \<open>@{term op_list_is_empty}\<close>
text \<open>For Emptiness check, we can simply reuse the implementation in
  @{theory Isabelle_LLVM.LLVM_DS_Open_List}, c.f. @{term os_is_empty}\<close>

lemma cl_is_empty_rule[vcg_rules]:
  \<open>llvm_htriple 
     (cl_assn' A xs xi)
     (os_is_empty xi)
     (\<lambda>r. cl_assn' A xs xi ** \<up>(r = (if xs = [] then 1 else 0)))\<close>
  unfolding os_is_empty_def
  supply [simp] = cl_assn_simps
  by vcg

lemma cl_is_empty_hnr[sepref_fr_rules]:
  \<open>(os_is_empty, RETURN o op_list_is_empty) \<in> (cl_assn' A)\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  apply sepref_to_hoare
  supply [simp] = bool1_rel_def bool.rel_def in_br_conv
  by vcg

subsection \<open>@{term op_list_prepend}\<close>

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

subsection \<open>@{term op_list_length}\<close>
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
    apply (simp add: sep_algebra_simps)
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

section \<open>Destructive/Copying Operations\<close>

subsection \<open>@{term op_list_pop_hd}\<close>
text \<open>Custom destructive @{term hd} operation defined at the top of the theory,
  c.f. @{term op_list_pop_hd}.\<close>

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




locale free_copying_list =
  fixes A :: \<open>'a \<Rightarrow> 'b::llvm_rep \<Rightarrow> assn\<close>
    and afree_impl :: \<open>'b \<Rightarrow> unit llM\<close>
  assumes a_assn_free[sepref_frame_free_rules]: \<open>MK_FREE A afree_impl\<close>
begin

subsection \<open>@{term op_list_free}\<close>

definition cl_free :: \<open>'b cl_list \<Rightarrow> unit llM\<close> where [llvm_code]:
  \<open>cl_free \<equiv> MMonad.REC (\<lambda>cl_free p.
    if p = null then Mreturn () else doM {
      n \<leftarrow> ll_load p;
      ll_free p;
      afree_impl (node.val n);
      cl_free (node.next n)
    })\<close>

lemmas cl_free_unfold = REC_unfold_extr[OF cl_free_def, discharge_monos]

lemma cl_free_rule[vcg_rules]:
  \<open>llvm_htriple (cl_assn' A xs p) (cl_free p) (\<lambda>_. \<box>)\<close>
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

lemma cl_assn_free[sepref_frame_free_rules]: \<open>MK_FREE (cl_assn' A) cl_free\<close>
  apply (rule MK_FREEI)
  by vcg

subsection \<open>@{term op_list_hd}, destructively\<close>
definition \<open>cl_hd\<^sub>d \<equiv> \<lambda>p. doM {(hd,tl) \<leftarrow> os_pop p; cl_free tl; Mreturn hd}\<close>

lemma cl_hd\<^sub>d_rule[vcg_rules]:
  assumes \<open>xs \<noteq> []\<close>
  shows \<open>llvm_htriple
    (cl_assn' A xs xi)
    (cl_hd\<^sub>d xi)
    (\<lambda>r. A (hd xs) r)\<close>
  unfolding cl_hd\<^sub>d_def
  apply (cases xs)
  subgoal using assms by simp
  by vcg

lemma cl_hd\<^sub>d_hnr_mop[sepref_fr_rules]:
  \<open>(cl_hd\<^sub>d, mop_list_hd) \<in> (cl_assn' A)\<^sup>d \<rightarrow>\<^sub>a A\<close>
  supply [simp] = refine_pw_simps
  by (sepref_to_hoare; vcg)

lemma cl_hd\<^sub>d_hnr_op[sepref_fr_rules]:
  \<open>(cl_hd\<^sub>d, RETURN o op_list_hd) \<in> [\<lambda>xs. xs\<noteq>[]]\<^sub>a (cl_assn' A)\<^sup>d \<rightarrow> A\<close>
  supply [simp] = refine_pw_simps
  by (sepref_to_hoare; vcg)

end

text \<open>We define a generic list implementation and require the objects in our
  list to implement a copy and a free function. This copying setup is copied from
  `isabelle_llvm/thys/examples/sorting/Sorting_Setup.thy`\<close>

definition "is_copy A cp \<equiv> (cp, RETURN o COPY) \<in> A\<^sup>k \<rightarrow>\<^sub>a A"

lemma is_copy_hnr[sepref_fr_rules]:
  "GEN_ALGO cp (is_copy A) \<Longrightarrow> (cp, RETURN o COPY) \<in> A\<^sup>k \<rightarrow>\<^sub>a A"
  unfolding is_copy_def GEN_ALGO_def by auto

lemma is_copy_pure_gen_algo: "CONSTRAINT is_pure A \<Longrightarrow> GEN_ALGO (Mreturn) (is_copy A)"  
  unfolding is_copy_def GEN_ALGO_def
  by (rule hnr_pure_COPY)

(* TODO: rename to copy_free_copying_list or something *)
locale copy_free_context = free_copying_list +
  fixes acopy_impl :: \<open>'b::llvm_rep \<Rightarrow> 'b llM\<close>
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

subsection \<open>@{term op_list_copy}\<close>

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


subsection \<open>@{term op_list_hd}\<close>

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

end


subsection \<open>@{term op_list_concat}\<close>

definition cl_concat_impl :: \<open>'a::llvm_rep cl_list \<times> 'a cl_list \<Rightarrow> 'a cl_list llM\<close>
  where [llvm_code]:
  \<open>cl_concat_impl \<equiv> MMonad.REC (\<lambda>cl_concat_impl (xp, yp).
    if xp = null then Mreturn yp
    else doM {
      n \<leftarrow> ll_load xp;
      tl \<leftarrow> cl_concat_impl (node.next n, yp);
      ll_store (Node (node.val n) tl) xp;
      Mreturn xp
    })\<close>

lemmas cl_concat_impl_unfold = REC_unfold_extr[OF cl_concat_impl_def, discharge_monos]

definition cl_concat :: \<open>'a::llvm_rep cl_list \<Rightarrow> 'a cl_list \<Rightarrow> 'a cl_list llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>cl_concat xp yp \<equiv> cl_concat_impl (xp, yp)\<close>

lemma cl_concat_rule[vcg_rules]:
  \<open>llvm_htriple
    (cl_assn' A xs xi ** cl_assn' A ys yi)
    (cl_concat xi yi)
    (\<lambda>r. cl_assn' A (xs @ ys) r)\<close>
  unfolding cl_concat_def
proof (induction xs arbitrary: xi)
  case Nil
  show ?case
    apply (rewrite cl_concat_impl_unfold)
    supply [simp] = cl_assn_simps
    by vcg
next
  case (Cons x xs)
  note [vcg_rules] = Cons.IH
  show ?case
    apply (rewrite cl_concat_impl_unfold)
    supply [simp] = cl_assn_simps sep_conj_exists
    by vcg
qed

lemma cl_concat_hnr[sepref_fr_rules]:
  \<open>(uncurry cl_concat, uncurry (RETURN oo op_list_concat))
    \<in> (cl_assn' A)\<^sup>d *\<^sub>a (cl_assn' A)\<^sup>d \<rightarrow>\<^sub>a (cl_assn' A)\<close>
  by (sepref_to_hoare; vcg)

subsection \<open>@{term op_list_append}\<close>
definition cl_append :: \<open>'a::llvm_rep cl_list \<Rightarrow> 'a \<Rightarrow> 'a cl_list llM\<close> where[llvm_code]:
  \<open>cl_append ai a \<equiv> doM {
    ap \<leftarrow> ll_ref (Node a null);
    cl_concat_impl (ai, ap)
  }\<close>

lemma cl_append_rule[vcg_rules]: \<open>llvm_htriple
  (cl_assn' A xs xi ** A a ai)
  (cl_append xi ai)
  (\<lambda>r. cl_assn' A (xs @ [a]) r)\<close>
  unfolding cl_append_def
  supply [vcg_rules] = cl_concat_rule[unfolded cl_concat_def, where ys=\<open>[a]\<close>]
  supply [simp, named_ss fri_prepare_simps] = cl_assn_simps
  by vcg

lemma cl_append_hnr[sepref_fr_rules]:
  \<open>(uncurry cl_append, uncurry (RETURN oo op_list_append))
    \<in> (cl_assn' A)\<^sup>d *\<^sub>a A\<^sup>d \<rightarrow>\<^sub>a (cl_assn' A)\<close>
  by (sepref_to_hoare; vcg)

subsection \<open>@{term op_list_rev}\<close>

text \<open>Destructive in-place reversal: walk the list once, re-linking each node
  onto an accumulator list.\<close>
definition cl_rev_impl :: \<open>'a::llvm_rep cl_list \<times> 'a cl_list \<Rightarrow> 'a cl_list llM\<close>
  where [llvm_code]:
  \<open>cl_rev_impl \<equiv> MMonad.REC (\<lambda>cl_rev_impl (xp, acc).
    if xp = null then Mreturn acc
    else doM {
      n \<leftarrow> ll_load xp;
      ll_store (Node (node.val n) acc) xp;
      cl_rev_impl (node.next n, xp)
    })\<close>

lemmas cl_rev_impl_unfold = REC_unfold_extr[OF cl_rev_impl_def, discharge_monos]

definition cl_rev :: \<open>'a::llvm_rep cl_list \<Rightarrow> 'a cl_list llM\<close> where [llvm_code, llvm_inline]:
  \<open>cl_rev xp \<equiv> cl_rev_impl (xp, null)\<close>

lemma cl_rev_impl_rule:
  \<open>llvm_htriple
    (cl_assn' A xs xi ** cl_assn' A ys yi)
    (cl_rev_impl (xi, yi))
    (\<lambda>r. cl_assn' A (rev xs @ ys) r)\<close>
proof (induction xs arbitrary: xi ys yi)
  case Nil
  show ?case
    apply (rewrite cl_rev_impl_unfold)
    supply [simp] = cl_assn_simps
    by vcg
next
  case (Cons x xs)
  note [vcg_rules] = Cons.IH[where ys=\<open>x # ys\<close>]
  show ?case
    apply (rewrite cl_rev_impl_unfold)
    supply [simp, named_ss fri_prepare_simps] = cl_assn_simps
    supply [simp] = sep_conj_exists
    by vcg
qed

lemma cl_rev_rule[vcg_rules]:
  \<open>llvm_htriple (cl_assn' A xs xi) (cl_rev xi) (\<lambda>r. cl_assn' A (rev xs) r)\<close>
  unfolding cl_rev_def
  supply [vcg_rules] = cl_rev_impl_rule[where ys=\<open>[]\<close> and yi=null]
  supply [simp, named_ss fri_prepare_simps] = cl_assn_simps
  by vcg

lemma cl_rev_hnr[sepref_fr_rules]:
  \<open>(cl_rev, RETURN o op_list_rev) \<in> (cl_assn' A)\<^sup>d \<rightarrow>\<^sub>a (cl_assn' A)\<close>
  by (sepref_to_hoare; vcg)

locale eq_copying_list =
  fixes A :: \<open>'a \<Rightarrow> 'b::llvm_rep \<Rightarrow> assn\<close>
    and aeq_impl :: \<open>'b \<Rightarrow> 'b \<Rightarrow> 1 word llM\<close> 
  assumes Aeq: \<open>(uncurry aeq_impl, uncurry (RETURN oo (=))) \<in> A\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close> 
begin

lemma aeq_impl_rule[vcg_rules]:
  \<open>llvm_htriple (A a ai ** A a' ai') (aeq_impl ai ai') (\<lambda>r. A a ai ** A a' ai' ** bool1_assn (a = a') r)\<close>
proof -
  note HNR = Aeq[to_hnr, unfolded autoref_tag_defs]
  note HT = HNR[THEN hn_refineD]
  show ?thesis
    apply (rule htriple_ent_pre[OF _ htriple_ent_post[OF _ HT]])
    unfolding hn_ctxt_def apply (rule entails_refl)
    subgoal by (auto simp: entails_def sep_algebra_simps pred_lift_extract_simps
      sep_conj_exists pw_le_iff refine_pw_simps)
    subgoal by simp
    done
qed

definition cl_eq_impl :: \<open>'b cl_list \<times> 'b cl_list \<Rightarrow> 1 word llM\<close> where[llvm_code, llvm_inline]:
  \<open>cl_eq_impl \<equiv> MMonad.REC (\<lambda>cl_eq_impl (ai, bi). doM {
    empa \<leftarrow> os_is_empty ai;
    llc_if empa (doM {
      empb \<leftarrow> os_is_empty bi;
      llc_if empb (Mreturn 1) (Mreturn 0) 
    }) (doM {
      empb \<leftarrow> os_is_empty bi;
      llc_if empb (Mreturn 0) (doM{
        aip \<leftarrow> ll_load ai;
        bip \<leftarrow> ll_load bi;
        eq \<leftarrow> aeq_impl (node.val aip) (node.val bip);
        llc_if eq (cl_eq_impl (node.next aip, node.next bip)) (Mreturn 0)
      })
    })
  })\<close>

lemmas cl_eq_impl_unfold = REC_unfold_extr[OF cl_eq_impl_def, discharge_monos]

definition \<open>cl_eq ai bi \<equiv> cl_eq_impl (ai, bi)\<close>

context begin
interpretation llvm_prim_ctrl_setup .

lemma cl_eq_rule[vcg_rules]:
  \<open>llvm_htriple
    (cl_assn' A xs xi ** cl_assn' A ys yi)
    (cl_eq xi yi)
    (\<lambda>r. cl_assn' A xs xi ** cl_assn' A ys yi ** bool1_assn (xs = ys) r)\<close>
  unfolding cl_eq_def
proof (induction xs arbitrary: xi ys yi)
  case Nil
  show ?case
    apply (rewrite cl_eq_impl_unfold)
    apply (unfold os_is_empty_def)
    supply [simp] = cl_assn_simps sep_conj_exists pure_def bool1_rel_def bool.rel_def in_br_conv
    apply (cases ys; simp)
    apply vcg
    done
next
  case (Cons x xs)
  note [vcg_rules] = Cons.IH
  show ?case
    apply (rewrite cl_eq_impl_unfold)
    apply (unfold os_is_empty_def)
    supply [simp] = cl_assn_simps sep_conj_exists pure_def bool1_rel_def bool.rel_def in_br_conv
    apply (cases ys; simp)
    apply vcg
    done
qed

end

lemma cl_eq_hnr[sepref_fr_rules]:
  \<open>(uncurry cl_eq, uncurry (RETURN oo (=)))
    \<in> (cl_assn' A)\<^sup>k *\<^sub>a (cl_assn' A)\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [simp] = pure_def
  by (sepref_to_hoare; vcg)

end

section \<open>Lexicographic Order\<close>

definition list_lt :: \<open>'a::linorder list \<Rightarrow> 'a list \<Rightarrow> bool\<close> where
  \<open>list_lt xs ys \<equiv> lexordp (<) xs ys\<close>

definition list_le :: \<open>'a::linorder list \<Rightarrow> 'a list \<Rightarrow> bool\<close> where
  \<open>list_le xs ys \<equiv> lexordp_eq xs ys\<close>

sepref_register list_lt list_le

instantiation list :: (linorder) linorder
begin
  definition less_list where  "less_list = lexordp (<)"
  definition less_eq_list where "less_eq_list = lexordp_eq"
instance
proof standard
  have [dest]: \<open>\<And>x y :: 'a :: linorder list. (x, y) \<in> lexord {(x, y). x < y} \<Longrightarrow>
           lexordp_eq y x \<Longrightarrow> False\<close>
    by (metis lexordp_antisym lexordp_conv_lexord lexordp_eq_conv_lexord)
  have [simp]: \<open>\<And>x y :: 'a :: linorder list. lexordp_eq x y \<Longrightarrow>
           \<not> lexordp_eq y x \<Longrightarrow>
           (x, y) \<in> lexord {(x, y). x < y}\<close>
    using lexordp_conv_lexord lexordp_conv_lexordp_eq by blast
  show
   \<open>(x < y) = (x \<le> y \<and> \<not> y \<le> x)\<close>
   \<open>x \<le> x\<close>
   \<open>x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z\<close>
   \<open>x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y\<close>
   \<open>x \<le> y \<or> y \<le> x\<close>
   for x y z :: \<open>'a :: linorder list\<close>
    by (auto simp: less_list_def less_eq_list_def List.lexordp_def
    lexordp_conv_lexord lexordp_into_lexordp_eq lexordp_antisym
    antisym_def lexordp_eq_refl lexordp_eq_linear intro: lexordp_eq_trans
    dest: lexordp_eq_antisym)
qed

end

lemma list_lt_less: \<open>list_lt = ((<) :: 'a::linorder list \<Rightarrow> _)\<close>
  by (intro ext) (simp add: list_lt_def less_list_def)

lemma list_le_less_eq: \<open>list_le = ((\<le>) :: 'a::linorder list \<Rightarrow> _)\<close>
  by (intro ext) (simp add: list_le_def less_eq_list_def)

lemma list_less_Nil_left: \<open>(([]::'a::linorder list) < ys) = (ys \<noteq> [])\<close>
  by (cases ys) (auto simp: less_list_def lexordp_def)

lemma list_less_Nil_right: \<open>(xs < ([]::'a::linorder list)) = False\<close>
  by (auto simp: less_list_def lexordp_def)

lemma list_less_Cons: \<open>((x # xs) < (y # ys)) = (x < y \<or> (x = y \<and> xs < ys))\<close>
  for x :: \<open>'a::linorder\<close>
  by (auto simp: less_list_def lexordp_def)

locale linord_copying_list = eq_copying_list A aeq_impl
  for A :: \<open>'a::linorder \<Rightarrow> 'b::llvm_rep \<Rightarrow> assn\<close>
  and aeq_impl :: \<open>'b \<Rightarrow> 'b \<Rightarrow> 1 word llM\<close> +
  fixes alt_impl :: \<open>'b \<Rightarrow> 'b \<Rightarrow> 1 word llM\<close>
  assumes Alt: \<open>(uncurry alt_impl, uncurry (RETURN oo (<))) \<in> A\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
begin

lemma alt_impl_rule[vcg_rules]:
  \<open>llvm_htriple (A a ai ** A a' ai') (alt_impl ai ai') (\<lambda>r. A a ai ** A a' ai' ** bool1_assn (a < a') r)\<close>
proof -
  note HNR = Alt[to_hnr, unfolded autoref_tag_defs]
  note HT = HNR[THEN hn_refineD]
  show ?thesis
    apply (rule htriple_ent_pre[OF _ htriple_ent_post[OF _ HT]])
    unfolding hn_ctxt_def apply (rule entails_refl)
    subgoal by (auto simp: entails_def sep_algebra_simps pred_lift_extract_simps
      sep_conj_exists pw_le_iff refine_pw_simps)
    subgoal by simp
    done
qed

subsection \<open>Strict Order\<close>

lemma lexordp_simps':
  \<open>lexordp r xs [] = False\<close>
  \<open>lexordp r [] (y # ys) = True\<close>
  \<open>lexordp r (x # xs) (y # ys) = (r x y \<or> (x = y \<and> lexordp r xs ys))\<close>
  by (simp_all add: lexordp_def)

definition cl_less_impl :: \<open>'b cl_list \<times> 'b cl_list \<Rightarrow> 1 word llM\<close> where [llvm_code, llvm_inline]:
  \<open>cl_less_impl \<equiv> MMonad.REC (\<lambda>cl_less_impl (ai, bi). doM {
    empb \<leftarrow> os_is_empty bi;
    llc_if empb (Mreturn 0) (doM {
      empa \<leftarrow> os_is_empty ai;
      llc_if empa (Mreturn 1) (doM {
        aip \<leftarrow> ll_load ai;
        bip \<leftarrow> ll_load bi;
        lt \<leftarrow> alt_impl (node.val aip) (node.val bip);
        llc_if lt (Mreturn 1) (doM {
          eq \<leftarrow> aeq_impl (node.val aip) (node.val bip);
          llc_if eq (cl_less_impl (node.next aip, node.next bip)) (Mreturn 0)
        })
      })
    })
  })\<close>

lemmas cl_less_impl_unfold = REC_unfold_extr[OF cl_less_impl_def, discharge_monos]

definition \<open>cl_less ai bi \<equiv> cl_less_impl (ai, bi)\<close>

context begin
interpretation llvm_prim_ctrl_setup .

lemma cl_less_rule[vcg_rules]:
  \<open>llvm_htriple
    (cl_assn' A xs xi ** cl_assn' A ys yi)
    (cl_less xi yi)
    (\<lambda>r. cl_assn' A xs xi ** cl_assn' A ys yi ** bool1_assn (list_lt xs ys) r)\<close>
  unfolding cl_less_def list_lt_def
proof (induction xs arbitrary: xi ys yi)
  case Nil
  show ?case
    apply (rewrite cl_less_impl_unfold)
    apply (unfold os_is_empty_def)
    supply [simp] = cl_assn_simps sep_conj_exists pure_def bool1_rel_def bool.rel_def in_br_conv
      lexordp_simps'
    apply (cases ys; simp)
    apply vcg
    done
next
  case (Cons x xs)
  note [vcg_rules] = Cons.IH
  show ?case
    apply (rewrite cl_less_impl_unfold)
    apply (unfold os_is_empty_def)
    supply [simp] = cl_assn_simps sep_conj_exists pure_def bool1_rel_def bool.rel_def in_br_conv
      lexordp_simps'
    apply (cases ys; simp)
    apply vcg
    done
qed

end

lemma cl_less_hnr[sepref_fr_rules]:
  \<open>(uncurry cl_less, uncurry (RETURN oo list_lt))
    \<in> (cl_assn' A)\<^sup>k *\<^sub>a (cl_assn' A)\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [simp] = pure_def
  by (sepref_to_hoare; vcg)

subsection \<open>Non-Strict Order\<close>

lemma lexordp_eq_conv_not_lexordp:
  \<open>lexordp_eq xs (ys :: 'a list) \<longleftrightarrow> \<not> lexordp (<) ys xs\<close>
  by (metis lexordp_conv_lexord lexordp_conv_lexordp_eq lexordp_def
      lexordp_eq_conv_lexord lexordp_linear)

definition cl_le :: \<open>'b cl_list \<Rightarrow> 'b cl_list \<Rightarrow> 1 word llM\<close> where [llvm_code, llvm_inline]:
  \<open>cl_le ai bi \<equiv> doM {
    lt \<leftarrow> cl_less_impl (bi, ai);
    llc_if lt (Mreturn 0) (Mreturn 1)
  }\<close>

context begin
interpretation llvm_prim_ctrl_setup .

lemma cl_le_rule[vcg_rules]:
  \<open>llvm_htriple
    (cl_assn' A xs xi ** cl_assn' A ys yi)
    (cl_le xi yi)
    (\<lambda>r. cl_assn' A xs xi ** cl_assn' A ys yi ** bool1_assn (list_le xs ys) r)\<close>
  unfolding cl_le_def list_le_def
  supply [vcg_rules] = cl_less_rule[unfolded cl_less_def list_lt_def]
  supply [simp] = pure_def bool1_rel_def bool.rel_def in_br_conv
    lexordp_eq_conv_not_lexordp
  by vcg

end

lemma cl_le_hnr[sepref_fr_rules]:
  \<open>(uncurry cl_le, uncurry (RETURN oo list_le))
    \<in> (cl_assn' A)\<^sup>k *\<^sub>a (cl_assn' A)\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [simp] = pure_def
  by (sepref_to_hoare; vcg)

end

section \<open>Regression Tests\<close>

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

text \<open>The order locale instantiated with 64-bit numbers as elements.\<close>

interpretation N: linord_copying_list \<open>snat_assn' TYPE(64)\<close> ll_icmp_eq ll_icmp_slt
  apply unfold_locales
  subgoal by (rule hn_snat_ops(7))
  subgoal by (rule hn_snat_ops(10))
  done

sepref_definition test_lt_impl is \<open>uncurry (RETURN oo list_lt)\<close>
  :: \<open>(cl_assn' (snat_assn' TYPE(64)))\<^sup>k *\<^sub>a (cl_assn' (snat_assn' TYPE(64)))\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

sepref_definition test_le_impl is \<open>uncurry (RETURN oo list_le)\<close>
  :: \<open>(cl_assn' (snat_assn' TYPE(64)))\<^sup>k *\<^sub>a (cl_assn' (snat_assn' TYPE(64)))\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

sepref_definition test_concat_impl is \<open>uncurry (RETURN oo (@))\<close>
  :: \<open>(cl_assn' (snat_assn' TYPE(64)))\<^sup>d *\<^sub>a (cl_assn' (snat_assn' TYPE(64)))\<^sup>d
    \<rightarrow>\<^sub>a (cl_assn' (snat_assn' TYPE(64)))\<close>
  by sepref

sepref_definition test_rev_impl is \<open>RETURN o rev\<close>
  :: \<open>(cl_assn' (snat_assn' TYPE(64)))\<^sup>d \<rightarrow>\<^sub>a (cl_assn' (snat_assn' TYPE(64)))\<close>
  by sepref

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
