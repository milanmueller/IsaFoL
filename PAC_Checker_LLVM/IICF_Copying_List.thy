theory IICF_Copying_List
  imports Assn_Env
    Isabelle_LLVM.Proto_EOArray
    Isabelle_LLVM.LLVM_DS_Open_List
begin

text \<open>This Theory defines a "copying list".
  By copying we mean that it's possible to get, e.g. the head of the list
  without destroying the list (which would be the case for lists holding
  impure objects without copying or some kind of borrow machinery).
  It is mostly based on/inspired by @{theory Isabelle_LLVM.LLVM_DS_Open_List}.\<close>

text \<open>coverage of the @{theory Isabelle_LLVM.IICF_List} interface
  Done:
    \<^item> [x] \<open>op_list_empty\<close>     (\<open>cl_empty_hnr\<close>)
    \<^item> [x] \<open>op_list_prepend\<close>   (\<open>cl_prepend_hnr\<close>; takes ownership of the element)
    \<^item> [x] \<open>op_list_length\<close>    (\<open>cl_length_hnr\<close>)
    \<^item> [x] \<open>COPY\<close>              (\<open>cl_copy_hnr\<close>/\<open>cl_copy_is_copy\<close>)
    \<^item> [x] \<open>op_list_hd\<close>        (\<open>cl_hd\<^sub>k\<close>); will copy the first element and leave list intact
                                          This operation is the main reason this theory exists.
    \<^item> [x] \<open>op_list_pop_hd\<close>    (\<open>os_pop\<close>); (See interface extension below) will move the \<open>hd\<close>
                                          out and also return the \<open>tl\<close> of the list.
    \<^item> [x] \<open>op_list_is_empty\<close>  (\<open>os_is_empty\<close>)
    \<^item> [x] \<open>op_list_concat\<close>    (\<open>cl_concat_hnr\<close>; destructively links both lists)
    \<^item> [x] \<open>op_list_append\<close>    (\<open>cl_append_hnr\<close>; snoc, O(n), takes ownership of the element;
                                          O(1) on the tail-pointer builder \<open>clt_assn\<close>,
                                          see \<open>clt_snoc_hnr\<close>)
    \<^item> [x] \<open>op_list_rev\<close>       (\<open>cl_rev_hnr\<close>; destructive in-place reversal, O(n))

  Infrastructure (not interface ops):
    \<^item> [x] \<open>MK_FREE\<close> deep free  (\<open>cl_assn_free\<close>, in the \<open>freeable_assn\<close> context)
    \<^item> [ ] \<open>cl_fold\<close> - read only walk parameterized over an inner function that keeps list elements intact

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
    \<^item> [x] \<open>op_list_contains\<close>  (\<open>cl_contains_hnr\<close>, in the \<open>eq_assn\<close> context)
    \<^item> [ ] \<open>op_list_index\<close>     (needs an element-equality parameter)
  
  Maybe a kind of split operation (where both halves are returned 
  might be interesting for merge sort...
\<close>

(* TODO:
  We might want to explore the feasibility of a read-only generic fold implementation
  in such a fold, we could deliberately only copy the inner elements where needed,
  which might even compose. With the function we currently have, List walks can
  only be done by also destroying the list. Providing a fold operation parameterized
  over the inner function might avoid that.

  c.f. The String hashing stuff for where this might actually help quite a bit...
*)

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
      { fix bb :: 'b and pp :: "'b node ptr" and bbs :: "'b list" 
        and aa :: llvm_amemory and bba :: 'b and ppa :: "'b node ptr" 
        and bbsa :: "'b list"
      have "\<not> (\<upharpoonleft>ll_bpto (Node bb pp) p 
                \<and>* A x bb \<and>* lseg bbs pp null 
                \<and>* \<upharpoonleft>(list_assn (mk_assn A)) xs bbs) aa 
         \<and> \<not> (\<upharpoonleft>ll_bpto (Node bba ppa) p 
                \<and>* lseg bbsa ppa null 
                \<and>* A x bba \<and>* \<upharpoonleft>(list_assn (mk_assn A)) xs bbsa) aa 
           \<or> (\<exists>b pa bs ba pb bsa. (\<upharpoonleft>ll_bpto (Node b pa) p 
                                    \<and>* A x b \<and>* lseg bs pa null 
                                    \<and>* \<upharpoonleft>(list_assn (mk_assn A)) xs bs) aa 
                                 \<and> (\<upharpoonleft>ll_bpto (Node ba pb) p \<and>* lseg bsa pb null 
                                    \<and>* A x ba \<and>* \<upharpoonleft>(list_assn (mk_assn A)) xs bsa) aa)"
     by (smt (verit) sep.mult.left_commute) }
  then show "(\<lambda>a. \<exists>b bs pa. (\<upharpoonleft>ll_bpto (Node b pa) p 
                              \<and>* lseg bs pa null \<and>* A x b 
                              \<and>* \<upharpoonleft>(list_assn (mk_assn A)) xs bs) a) = (\<lambda>a. \<exists>b pa bs. (\<upharpoonleft>ll_bpto (Node b pa) p 
                              \<and>* A x b \<and>* lseg bs pa null 
                              \<and>* \<upharpoonleft>(list_assn (mk_assn A)) xs bs) a)"
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

section \<open>Custom Fold implementation\<close>
text \<open>Using our other functions like @{term op_list_hd} or @{term op_list_pop_hd}
  either destroys the list, or copies elements.
  There are, however, cases, where we want a read only walk. For these cases, we
  implement a fold operation, parameterized over an f, that keeps the inner elements intact\<close>

definition cl_fold :: \<open>('a::llvm_rep \<Rightarrow> 'b::llvm_rep \<Rightarrow> 'a llM) \<Rightarrow> ('b cl_list \<times> 'a) \<Rightarrow> 'a llM\<close>
  where [llvm_code]:
  \<open>cl_fold f \<equiv> MMonad.REC (\<lambda>ff (xi, a).
    if xi = null then Mreturn a
    else doM {
      n \<leftarrow> ll_load xi;
      a \<leftarrow> f a (node.val n);
      ff (node.next n, a)
    })\<close>

lemmas cl_fold_unfold = REC_unfold_extr[OF cl_fold_def, discharge_monos]

lemma cl_fold_rule:
  assumes F: \<open>\<And>a ai x xi. llvm_htriple
      (R a ai ** A x xi) (f ai xi) (\<lambda>r. R (fa a x) r ** A x xi)\<close>
  shows \<open>llvm_htriple
    (R a ai ** cl_assn' A xs p)
    (cl_fold f (p, ai))
    (\<lambda>r. R (foldl fa a xs) r ** cl_assn' A xs p)\<close>
proof (induction xs arbitrary: a ai p)
  case Nil
  show ?case
    supply [simp] = cl_assn_simps
    apply (subst cl_fold_unfold)
    by vcg
next
  case (Cons x xs)
  note [vcg_rules] = Cons.IH F
  show ?case
    supply [simp] = cl_assn_simps
    apply (subst cl_fold_unfold)
    by vcg
qed

(* for nicer refinment, we want uncurried version *)
definition [llvm_inline]: \<open>cl_fold' f a xi \<equiv> cl_fold f (xi, a)\<close>

lemma cl_fold'_rule:
  assumes F: \<open>\<And>a ai x xi. llvm_htriple
      (R a ai ** A x xi) (f ai xi) (\<lambda>r. R (fa a x) r ** A x xi)\<close>
  shows \<open>llvm_htriple
    (R a ai ** cl_assn' A xs p)
    (cl_fold' f ai p)
    (\<lambda>r. R (foldl fa a xs) r ** cl_assn' A xs p)\<close>
  unfolding cl_fold'_def
  supply [vcg_rules] = cl_fold_rule[where a="a" and ai="ai" and R="R", OF F]
  by vcg

term cl_fold'
fun mfoldl :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'a nres) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a nres\<close> where
  \<open>mfoldl _ a [] = RETURN a\<close>
| \<open>mfoldl f a (b#bs) = doN {a' \<leftarrow> f a b; mfoldl f a' bs}\<close>

(* Not sure if useful *)
lemma mfoldl_RETURN:
  \<open>mfoldl (\<lambda>a b. RETURN (fa a b)) a bs = RETURN (foldl fa a bs)\<close>
  by (induction bs arbitrary: a) auto

lemma mfoldl_nfoldli:
  \<open>mfoldl f a bs = nfoldli bs (\<lambda>_. True) (\<lambda>b a. f a b) a\<close>
  by (induction bs arbitrary: a) auto

lemma cl_fold_hfref:
  assumes F: \<open>(uncurry fi, uncurry (RETURN oo fa)) \<in> R\<^sup>d *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a R\<close>
  shows \<open>(uncurry (cl_fold' fi), uncurry (RETURN oo foldl fa))
        \<in> R\<^sup>d *\<^sub>a (cl_assn' A)\<^sup>k \<rightarrow>\<^sub>a R\<close>
proof -
  have BODY: \<open>llvm_htriple (R a ai ** A x xi) (fi ai xi)
                (\<lambda>r. R (fa a x) r ** A x xi)\<close> for a ai x xi
    apply (rule htriple_ent_post[OF _ hfref_htriple_d1_k2[OF F]])
    by (simp add: sep_conj_aci)
  show ?thesis
    thm cl_fold'_rule[where R=R and A=A and f=fi and fa=fa, OF BODY]
    supply [vcg_rules] = cl_fold'_rule[where R=R and A=A and f=fi and fa=fa, OF BODY]
    by (sepref_to_hoare; vcg)
qed

text \<open>Additional assertions @{term \<Phi>} survive cl_fold. This is needed when the
  fold's step function captures further (read-only) parameters beyond the
  accumulator and the current element: their assertions ride along in \<open>\<Phi>\<close>.\<close>
lemma cl_fold_rule':
  assumes F: \<open>\<And>a ai x xi. llvm_htriple
      (\<Phi> ** R a ai ** A x xi) (f ai xi) (\<lambda>r. \<Phi> ** R (fa a x) r ** A x xi)\<close>
  shows \<open>llvm_htriple
    (\<Phi> ** R a ai ** cl_assn' A xs p)
    (cl_fold' f ai p)
    (\<lambda>r. \<Phi> ** R (foldl fa a xs) r ** cl_assn' A xs p)\<close>
  unfolding cl_fold'_def
proof (induction xs arbitrary: a ai p)
  case Nil
  show ?case
    supply [simp] = cl_assn_simps
    apply (subst cl_fold_unfold)
    by vcg
next
  case (Cons x xs)
  note [vcg_rules] = Cons.IH F
  show ?case
    supply [simp] = cl_assn_simps
    apply (subst cl_fold_unfold)
    by vcg
qed

text \<open>Parameterized version of @{thm cl_fold_hfref}: the step function takes an
  additional kept parameter \<open>P\<close> (e.g. the fixed operand of an outer loop).\<close>
lemma cl_fold_hfref_param:
  assumes F: \<open>(uncurry2 fi, uncurry2 (RETURN ooo fa)) \<in> P\<^sup>k *\<^sub>a R\<^sup>d *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a R\<close>
  shows \<open>(uncurry2 (\<lambda>pi. cl_fold' (fi pi)), uncurry2 (RETURN ooo (\<lambda>p. foldl (fa p))))
        \<in> P\<^sup>k *\<^sub>a R\<^sup>d *\<^sub>a (cl_assn' A)\<^sup>k \<rightarrow>\<^sub>a R\<close>
proof -
  have BODY: \<open>llvm_htriple (P p pi ** R a ai ** A x xi) (fi pi ai xi)
                (\<lambda>r. P p pi ** R (fa p a x) r ** A x xi)\<close> for p pi a ai x xi
    by (rule hfref_htriple_k1_d2_k3[OF F])
  show ?thesis
    supply [vcg_rules] = cl_fold_rule'[where R=R and A=A, OF BODY]
    by (sepref_to_hoare; vcg)
qed


subsection \<open>Lambda-lifted fold\<close>

text \<open>LLVM cannot compile closures: a fold instance \<open>cl_fold (f e)\<close> whose step
  function captures a runtime parameter \<open>e\<close> fails \<open>export_llvm\<close> with
  "Expected ground term". \<open>cl_fold_env\<close> instead threads the environment through
  the recursion, so the step function of every instance is a ground constant.\<close>

definition cl_fold_env
  :: \<open>('e::llvm_rep \<Rightarrow> 'a::llvm_rep \<Rightarrow> 'b::llvm_rep \<Rightarrow> 'a llM)
      \<Rightarrow> 'e \<times> 'b cl_list \<times> 'a \<Rightarrow> 'a llM\<close>
  where [llvm_code]:
  \<open>cl_fold_env f \<equiv> MMonad.REC (\<lambda>ff (e, xi, a).
    if xi = null then Mreturn a
    else doM {
      n \<leftarrow> ll_load xi;
      a \<leftarrow> f e a (node.val n);
      ff (e, node.next n, a)
    })\<close>

lemmas cl_fold_env_unfold = REC_unfold_extr[OF cl_fold_env_def, discharge_monos]

lemma cl_fold_env_rule:
  assumes F: \<open>\<And>a ai x xi. llvm_htriple
      (P e ei ** R a ai ** A x xi) (f ei ai xi)
      (\<lambda>r. P e ei ** R (fa e a x) r ** A x xi)\<close>
  shows \<open>llvm_htriple
    (P e ei ** R a ai ** cl_assn' A xs p)
    (cl_fold_env f (ei, p, ai))
    (\<lambda>r. P e ei ** R (foldl (fa e) a xs) r ** cl_assn' A xs p)\<close>
proof (induction xs arbitrary: a ai p)
  case Nil
  show ?case
    supply [simp] = cl_assn_simps
    apply (subst cl_fold_env_unfold)
    by vcg
next
  case (Cons x xs)
  note [vcg_rules] = Cons.IH F
  show ?case
    supply [simp] = cl_assn_simps
    apply (subst cl_fold_env_unfold)
    by vcg
qed

text \<open>Lambda-lifted analogue of @{thm cl_fold_hfref_param}.\<close>
lemma cl_fold_env_hfref_param:
  assumes F: \<open>(uncurry2 fi, uncurry2 (RETURN ooo fa)) \<in> P\<^sup>k *\<^sub>a R\<^sup>d *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a R\<close>
  shows \<open>(uncurry2 (\<lambda>pi ai xsi. cl_fold_env fi (pi, xsi, ai)),
          uncurry2 (RETURN ooo (\<lambda>p. foldl (fa p))))
        \<in> P\<^sup>k *\<^sub>a R\<^sup>d *\<^sub>a (cl_assn' A)\<^sup>k \<rightarrow>\<^sub>a R\<close>
proof -
  have BODY: \<open>llvm_htriple (P p pi ** R a ai ** A x xi) (fi pi ai xi)
                (\<lambda>r. P p pi ** R (fa p a x) r ** A x xi)\<close> for p pi a ai x xi
    by (rule hfref_htriple_k1_d2_k3[OF F])
  show ?thesis
    supply [vcg_rules] = cl_fold_env_rule[where P=P and R=R and A=A and f=fi, OF BODY]
    by (sepref_to_hoare; vcg)
qed

text \<open>Guarded variant: the step function's rule only holds for elements
  satisfying \<open>P\<close>; the fold then requires all list elements to satisfy \<open>P\<close>.\<close>
lemma cl_fold_rule_guard:
  assumes F: \<open>\<And>a ai x xi. P x \<Longrightarrow> llvm_htriple
      (R a ai ** A x xi) (f ai xi) (\<lambda>r. R (fa a x) r ** A x xi)\<close>
  assumes ALL: \<open>\<forall>x \<in> set xs. P x\<close>
  shows \<open>llvm_htriple
    (R a ai ** cl_assn' A xs p)
    (cl_fold f (p, ai))
    (\<lambda>r. R (foldl fa a xs) r ** cl_assn' A xs p)\<close>
  using ALL
proof (induction xs arbitrary: a ai p)
  case Nil
  show ?case
    supply [simp] = cl_assn_simps
    apply (subst cl_fold_unfold)
    by vcg
next
  case (Cons x xs)
  from Cons.prems have Px: \<open>P x\<close> and TL: \<open>\<forall>y \<in> set xs. P y\<close> by auto
  note [vcg_rules] = Cons.IH[OF TL] F[OF Px]
  show ?case
    supply [simp] = cl_assn_simps
    apply (subst cl_fold_unfold)
    by vcg
qed

lemma cl_fold'_rule_guard:
  assumes F: \<open>\<And>a ai x xi. P x \<Longrightarrow> llvm_htriple
      (R a ai ** A x xi) (f ai xi) (\<lambda>r. R (fa a x) r ** A x xi)\<close>
  assumes ALL: \<open>\<forall>x \<in> set xs. P x\<close>
  shows \<open>llvm_htriple
    (R a ai ** cl_assn' A xs p)
    (cl_fold' f ai p)
    (\<lambda>r. R (foldl fa a xs) r ** cl_assn' A xs p)\<close>
  unfolding cl_fold'_def
  supply [vcg_rules] = cl_fold_rule_guard[where a=a and ai=ai and R=R, OF F ALL]
  by vcg

lemma cl_fold_hfref_guard:
  assumes F: \<open>(uncurry fi, uncurry (RETURN oo fa)) \<in> [\<lambda>(_, x). P x]\<^sub>a R\<^sup>d *\<^sub>a A\<^sup>k \<rightarrow> R\<close>
  shows \<open>(uncurry (cl_fold' fi), uncurry (RETURN oo foldl fa))
        \<in> [\<lambda>(_, xs). \<forall>x \<in> set xs. P x]\<^sub>a R\<^sup>d *\<^sub>a (cl_assn' A)\<^sup>k \<rightarrow> R\<close>
proof -
  have BODY: \<open>P x \<Longrightarrow> llvm_htriple (R a ai ** A x xi) (fi ai xi)
                (\<lambda>r. R (fa a x) r ** A x xi)\<close> for a ai x xi
    apply (rule htriple_ent_post[OF _ hfref_htriple_d1_k2_guard[OF F]])
    by (simp_all add: sep_conj_aci)
  show ?thesis
    apply sepref_to_hoare
    subgoal premises prems for b bi a ai
      supply [vcg_rules] =
        cl_fold'_rule_guard[where R=R and A=A and f=fi and fa=fa, OF BODY prems(1)]
      by vcg
    done
qed

section \<open>@{term op_list_contains}\<close>

context eq_assn
begin

definition cl_contains :: \<open>'b \<Rightarrow> 'b cl_list \<Rightarrow> 1 word llM\<close> where [llvm_code]:
  \<open>cl_contains xi \<equiv> MMonad.REC (\<lambda>D p.
    if p = null then Mreturn 0
    else doM {
      n \<leftarrow> ll_load p;
      eq \<leftarrow> aeq (node.val n) xi;
      llc_if eq (Mreturn 1) (D (node.next n))
    })\<close>

lemmas cl_contains_unfold = REC_unfold_extr[OF cl_contains_def, discharge_monos]

lemma cl_contains_rule[vcg_rules]:
  \<open>llvm_htriple
    (cl_assn' A xs xsi ** A a ai)
    (cl_contains ai xsi)
    (\<lambda>r. cl_assn' A xs xsi ** A a ai ** \<upharpoonleft>bool.assn (a \<in> set xs) r)\<close>
proof (induction xs arbitrary: xsi)
  case Nil
  show ?case
    supply [simp] = cl_assn_simps bool.assn_def
    apply (subst cl_contains_unfold)
    by vcg
next
  case (Cons e es)
  interpret llvm_prim_ctrl_setup .
  note [vcg_rules] = Cons.IH
  show ?case
    supply [simp] = cl_assn_simps bool.assn_def bool1_rel_def bool.rel_def in_br_conv pure_def
    apply (subst cl_contains_unfold)
    by vcg
qed

lemma cl_contains_hnr[sepref_fr_rules]:
  \<open>(uncurry cl_contains, uncurry (RETURN oo op_list_contains))
    \<in> A\<^sup>k *\<^sub>a (cl_assn' A)\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  apply (sepref_to_hoare; vcg)
  apply (auto simp: ENTAILS_def entails_def sep_algebra_simps
    bool1_rel_def bool.rel_def in_br_conv bool.assn_def)
  apply (metis sep.mult_commute)
  by (metis sep_conj_commuteI)
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

text \<open>Operations that need to free elements live in the \<open>freeable_assn\<close> context
  (see theory \<open>Assn_Env\<close>).\<close>

context freeable_assn
begin

subsection \<open>@{term op_list_free}\<close>

definition cl_free :: \<open>'b cl_list \<Rightarrow> unit llM\<close> where [llvm_code]:
  \<open>cl_free \<equiv> MMonad.REC (\<lambda>cl_free p.
    if p = null then Mreturn () else doM {
      n \<leftarrow> ll_load p;
      ll_free p;
      afree (node.val n);
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
  note [vcg_rules] = Cons.IH
  show ?case
    apply (rewrite cl_free_unfold)
    supply [simp] = cl_assn_simps sep_conj_exists
    by vcg
qed

lemma cl_assn_free[sepref_frame_free_rules]: \<open>MK_FREE (cl_assn' A) cl_free\<close>
  apply (rule MK_FREEI)
  by vcg

subsection \<open>@{term op_list_hd}, destructively\<close>
definition cl_hd\<^sub>d where [llvm_code]: 
  \<open>cl_hd\<^sub>d \<equiv> \<lambda>p. doM {(hd,tl) \<leftarrow> os_pop p; cl_free tl; Mreturn hd}\<close>

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

text \<open>Operations that additionally need to copy elements live in the
  \<open>copyable_assn\<close> context. (The copying setup \<open>is_copy\<close> itself lives in
  theory \<open>Assn_Env\<close>.)\<close>

context copyable_assn
begin

subsection \<open>@{term op_list_hd}\<close>

definition cl_hd\<^sub>k :: \<open>'b cl_list \<Rightarrow> 'b llM\<close> where [llvm_code]:
  \<open>cl_hd\<^sub>k p \<equiv> doM {
    n \<leftarrow> ll_load p;
    cpy \<leftarrow> acopy (node.val n);
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

text \<open>Comparison operations only load elements, so they need neither free nor
  copy; equality needs only \<open>aeq\<close> and lives in the \<open>eq_assn\<close> context (the order
  operations below live in \<open>linorder_assn\<close>).\<close>

context eq_assn
begin

definition cl_eq_impl :: \<open>'b cl_list \<times> 'b cl_list \<Rightarrow> 1 word llM\<close> where[llvm_code]:
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
        eq \<leftarrow> aeq (node.val aip) (node.val bip);
        llc_if eq (cl_eq_impl (node.next aip, node.next bip)) (Mreturn 0)
      })
    })
  })\<close>

lemmas cl_eq_impl_unfold = REC_unfold_extr[OF cl_eq_impl_def, discharge_monos]

definition [llvm_code]: \<open>cl_eq ai bi \<equiv> cl_eq_impl (ai, bi)\<close>

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

context linorder_assn
begin

subsection \<open>Strict Order\<close>

lemma lexordp_simps':
  \<open>lexordp r xs [] = False\<close>
  \<open>lexordp r [] (y # ys) = True\<close>
  \<open>lexordp r (x # xs) (y # ys) = (r x y \<or> (x = y \<and> lexordp r xs ys))\<close>
  by (simp_all add: lexordp_def)

definition cl_less_impl :: \<open>'b cl_list \<times> 'b cl_list \<Rightarrow> 1 word llM\<close> where [llvm_code]:
  \<open>cl_less_impl \<equiv> MMonad.REC (\<lambda>cl_less_impl (ai, bi). doM {
    empb \<leftarrow> os_is_empty bi;
    llc_if empb (Mreturn 0) (doM {
      empa \<leftarrow> os_is_empty ai;
      llc_if empa (Mreturn 1) (doM {
        aip \<leftarrow> ll_load ai;
        bip \<leftarrow> ll_load bi;
        lt \<leftarrow> alt (node.val aip) (node.val bip);
        llc_if lt (Mreturn 1) (doM {
          eq \<leftarrow> aeq (node.val aip) (node.val bip);
          llc_if eq (cl_less_impl (node.next aip, node.next bip)) (Mreturn 0)
        })
      })
    })
  })\<close>

lemmas cl_less_impl_unfold = REC_unfold_extr[OF cl_less_impl_def, discharge_monos]

definition [llvm_code]: \<open>cl_less ai bi \<equiv> cl_less_impl (ai, bi)\<close>

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


section \<open>Tail-Pointer Builder List\<close>

type_synonym 'a clt_list = \<open>'a node ptr \<times> 'a node ptr\<close>

subsection \<open>Auxiliary Lemmas about @{term olseg}\<close>

lemma entails_exE: \<open>(\<And>x. P x \<turnstile> Q) \<Longrightarrow> (EXS x. P x) \<turnstile> Q\<close>
  by (auto simp: entails_def)

lemma olseg_nil: \<open>olseg A [] p q = \<up>(p = q)\<close>
  unfolding olseg_def
  by (auto simp: sep_algebra_simps)

lemma olseg_snoc:
  \<open>olseg A ys p q ** \<upharpoonleft>ll_bpto (Node c r) q ** A y c \<turnstile> olseg A (ys @ [y]) p r\<close>
proof -
  have H: \<open>lseg xsi p q ** \<upharpoonleft>(list_assn (mk_assn A)) ys xsi ** \<upharpoonleft>ll_bpto (Node c r) q ** A y c
      \<turnstile> olseg A (ys @ [y]) p r\<close> for xsi
  proof (rule entails_pureI)
    assume \<open>pure_part (lseg xsi p q ** \<upharpoonleft>(list_assn (mk_assn A)) ys xsi
        ** \<upharpoonleft>ll_bpto (Node c r) q ** A y c)\<close>
    then have L: \<open>length ys = length xsi\<close>
      by (auto dest!: pure_part_split_conj dest: list_assn_pure_part)
    have R: \<open>(lseg xsi p q ** \<upharpoonleft>(list_assn (mk_assn A)) ys xsi
          ** \<upharpoonleft>ll_bpto (Node c r) q ** A y c)
        = ((lseg xsi p q ** \<upharpoonleft>ll_bpto (Node c r) q)
          ** (\<upharpoonleft>(list_assn (mk_assn A)) ys xsi ** A y c))\<close>
      by (simp add: sep_conj_aci)
    have S: \<open>\<upharpoonleft>(list_assn (mk_assn A)) (ys @ [y]) (xsi @ [c])
        = (\<upharpoonleft>(list_assn (mk_assn A)) ys xsi ** A y c)\<close>
      by (simp add: L sep_algebra_simps)
    show \<open>lseg xsi p q ** \<upharpoonleft>(list_assn (mk_assn A)) ys xsi
        ** \<upharpoonleft>ll_bpto (Node c r) q ** A y c \<turnstile> olseg A (ys @ [y]) p r\<close>
      unfolding olseg_def R
      apply (rule entails_exI[where x = \<open>xsi @ [c]\<close>])
      unfolding S
      by (rule conj_entails_mono[OF lseg_snoc entails_refl])
  qed
  have E: \<open>(olseg A ys p q ** \<upharpoonleft>ll_bpto (Node c r) q ** A y c)
      = (EXS xsi. lseg xsi p q ** \<upharpoonleft>(list_assn (mk_assn A)) ys xsi
          ** \<upharpoonleft>ll_bpto (Node c r) q ** A y c)\<close>
    unfolding olseg_def by (simp add: sep_conj_exists)
  show ?thesis
    unfolding E by (rule entails_exE[OF H])
qed

lemma olseg_append: \<open>olseg A xs p q ** olseg A ys q r \<turnstile> olseg A (xs @ ys) p r\<close>
proof -
  have H: \<open>lseg xsi p q ** \<upharpoonleft>(list_assn (mk_assn A)) xs xsi
      ** lseg ysi q r ** \<upharpoonleft>(list_assn (mk_assn A)) ys ysi
      \<turnstile> olseg A (xs @ ys) p r\<close> for xsi ysi
  proof (rule entails_pureI)
    assume \<open>pure_part (lseg xsi p q ** \<upharpoonleft>(list_assn (mk_assn A)) xs xsi
        ** lseg ysi q r ** \<upharpoonleft>(list_assn (mk_assn A)) ys ysi)\<close>
    then have L: \<open>length xs = length xsi\<close>
      by (auto dest!: pure_part_split_conj dest: list_assn_pure_part)
    have R: \<open>(lseg xsi p q ** \<upharpoonleft>(list_assn (mk_assn A)) xs xsi
        ** lseg ysi q r ** \<upharpoonleft>(list_assn (mk_assn A)) ys ysi)
      = ((lseg xsi p q ** lseg ysi q r)
        ** (\<upharpoonleft>(list_assn (mk_assn A)) xs xsi ** \<upharpoonleft>(list_assn (mk_assn A)) ys ysi))\<close>
      by (simp add: sep_conj_aci)
    have S: \<open>\<upharpoonleft>(list_assn (mk_assn A)) (xs @ ys) (xsi @ ysi)
        = (\<upharpoonleft>(list_assn (mk_assn A)) xs xsi ** \<upharpoonleft>(list_assn (mk_assn A)) ys ysi)\<close>
      by (simp add: L sep_algebra_simps)
    show \<open>lseg xsi p q ** \<upharpoonleft>(list_assn (mk_assn A)) xs xsi
        ** lseg ysi q r ** \<upharpoonleft>(list_assn (mk_assn A)) ys ysi
        \<turnstile> olseg A (xs @ ys) p r\<close>
      unfolding olseg_def R
      apply (rule entails_exI[where x = \<open>xsi @ ysi\<close>])
      unfolding S
      by (rule conj_entails_mono[OF lseg_fuse entails_refl])
  qed
  have E: \<open>(olseg A xs p q ** olseg A ys q r)
      = (EXS xsi ysi. lseg xsi p q ** \<upharpoonleft>(list_assn (mk_assn A)) xs xsi
          ** lseg ysi q r ** \<upharpoonleft>(list_assn (mk_assn A)) ys ysi)\<close>
    unfolding olseg_def by (simp add: sep_conj_exists)
  show ?thesis
    unfolding E by (intro entails_exE, rule H)
qed

subsection \<open>Assertion\<close>

definition clt_assn where
  \<open>clt_assn A \<equiv> mk_assn (\<lambda>xs (p, q).
     if xs = [] then \<up>(p = null)
     else EXS c. olseg A (butlast xs) p q ** \<upharpoonleft>ll_bpto (Node c null) q
        ** A (last xs) c ** \<up>(p \<noteq> null))\<close>

definition \<open>clt_assn' A \<equiv> \<upharpoonleft>(clt_assn A)\<close>

lemma clt_assn_conv:
  \<open>clt_assn' A xs (p, q) =
     (if xs = [] then \<up>(p = null)
      else EXS c. olseg A (butlast xs) p q ** \<upharpoonleft>ll_bpto (Node c null) q
        ** A (last xs) c ** \<up>(p \<noteq> null))\<close>
  unfolding clt_assn'_def clt_assn_def by simp

text \<open>Forgetting the tail pointer recovers an ordinary copying list.\<close>

lemma clt_cl_entails: \<open>clt_assn' A xs (p, q) \<turnstile> cl_assn' A xs p\<close>
proof (cases \<open>xs = []\<close>)
  case True
  then show ?thesis
    by (simp add: clt_assn_conv cl_assn_simps)
next
  case False
  then have E: \<open>butlast xs @ [last xs] = xs\<close> by simp
  have H: \<open>olseg A (butlast xs) p q ** \<upharpoonleft>ll_bpto (Node c null) q ** A (last xs) c
      \<turnstile> olseg A xs p null\<close> for c
    using olseg_snoc[of A \<open>butlast xs\<close> p q c null \<open>last xs\<close>] unfolding E .
  show ?thesis
    unfolding clt_assn_conv cl_assn'_def cl_assn_def
    using False
    apply simp
    apply (rule entails_exE)
    subgoal for c
      using H[of c]
      apply (auto simp: entails_def)
      by (metis (no_types, lifting) pred_lift_extract_simps(2) sep.mult_assoc
          sep.mult_commute)
    done
qed

subsection \<open>Operations\<close>

subsubsection \<open>Empty Builder\<close>

definition clt_empty :: \<open>('a::llvm_rep) clt_list llM\<close> where [llvm_code, llvm_inline]:
  \<open>clt_empty \<equiv> Mreturn (null, null)\<close>

lemma clt_empty_rule[vcg_rules]: \<open>llvm_htriple \<box> clt_empty (\<lambda>r. clt_assn' A [] r)\<close>
  unfolding clt_empty_def
  supply [simp] = clt_assn_conv
  by vcg

definition op_clt_empty :: \<open>'a list\<close> where [simp]: \<open>op_clt_empty \<equiv> op_list_empty\<close>
sepref_register op_clt_empty

lemma fold_clt_empty:
  \<open>[] = op_clt_empty\<close>
  \<open>op_list_empty = op_clt_empty\<close>
  \<open>mop_list_empty = RETURN op_clt_empty\<close>
  by simp_all

lemma clt_empty_hnr[sepref_fr_rules]:
  \<open>(uncurry0 clt_empty, uncurry0 (RETURN op_clt_empty)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a clt_assn' A\<close>
  unfolding op_clt_empty_def
  by (sepref_to_hoare; vcg)

subsubsection \<open>Snoc (append at the end, O(1))\<close>

text \<open>Takes ownership of the element, like @{term cl_prepend}. The list argument comes
  first to match @{term op_list_append}.\<close>

definition clt_snoc :: \<open>'a::llvm_rep clt_list \<Rightarrow> 'a \<Rightarrow> 'a clt_list llM\<close> where [llvm_code]:
  \<open>clt_snoc \<equiv> \<lambda>pq x. doM {
    let (p, q) = pq;
    r \<leftarrow> ll_ref (Node x null);
    if p = null then Mreturn (r, r)
    else doM {
      n \<leftarrow> ll_load q;
      ll_store (Node (node.val n) r) q;
      Mreturn (p, r)
    }
  }\<close>

context begin

private lemma clt_snoc_step:
  assumes \<open>xs \<noteq> []\<close> and \<open>p \<noteq> null\<close>
  shows \<open>ENTAILS
    (\<upharpoonleft>ll_bpto (Node c r) q ** A (last xs) c ** A x ci
      ** \<upharpoonleft>ll_bpto (Node ci null) r ** olseg A (butlast xs) p q)
    (clt_assn' A (xs @ [x]) (p, r))\<close>
proof -
  have E: \<open>butlast xs @ [last xs] = xs\<close> using assms by simp
  have H: \<open>olseg A (butlast xs) p q ** \<upharpoonleft>ll_bpto (Node c r) q ** A (last xs) c
      \<turnstile> olseg A xs p r\<close>
    using olseg_snoc[of A \<open>butlast xs\<close> p q c r \<open>last xs\<close>] unfolding E .
  have R: \<open>(\<upharpoonleft>ll_bpto (Node c r) q ** A (last xs) c ** A x ci
      ** \<upharpoonleft>ll_bpto (Node ci null) r ** olseg A (butlast xs) p q)
    = ((olseg A (butlast xs) p q ** \<upharpoonleft>ll_bpto (Node c r) q ** A (last xs) c)
      ** (\<upharpoonleft>ll_bpto (Node ci null) r ** A x ci))\<close>
    by (simp add: sep_conj_aci)
  have SP: \<open>(\<upharpoonleft>ll_bpto (Node c r) q ** A (last xs) c ** A x ci
      ** \<upharpoonleft>ll_bpto (Node ci null) r ** olseg A (butlast xs) p q)
    \<turnstile> olseg A xs p r ** \<upharpoonleft>ll_bpto (Node ci null) r ** A x ci\<close>
    unfolding R by (rule conj_entails_mono[OF H entails_refl])
  show ?thesis
    unfolding ENTAILS_def
    apply (rule entails_trans[OF SP])
    apply (simp add: clt_assn_conv)
    apply (rule entails_exI[where x = ci])
    using assms
    by (simp add: sep_algebra_simps pred_lift_extract_simps)
qed

lemma clt_snoc_rule[vcg_rules]:
  \<open>llvm_htriple (clt_assn' A xs pq ** A x xi) (clt_snoc pq xi)
    (\<lambda>r. clt_assn' A (xs @ [x]) r)\<close>
  unfolding clt_snoc_def
  supply [simp] = clt_assn_conv olseg_nil sep_conj_exists
  apply (cases pq; cases \<open>xs = []\<close>; simp)
  subgoal by vcg
  subgoal
    apply vcg
    apply (rule clt_snoc_step; assumption)
    done
  done

lemma clt_snoc_hnr[sepref_fr_rules]:
  \<open>(uncurry clt_snoc, uncurry (RETURN oo op_list_append))
    \<in> (clt_assn' A)\<^sup>d *\<^sub>a A\<^sup>d \<rightarrow>\<^sub>a clt_assn' A\<close>
  by (sepref_to_hoare; vcg)

end

subsubsection \<open>Concatenation (O(1))\<close>

text \<open>Destructively links the last node of the first list to the head of the
  second list; both arguments are consumed. Unlike @{term cl_concat} this needs
  no list traversal, thanks to the tail pointer.\<close>

definition clt_concat :: \<open>'a::llvm_rep clt_list \<Rightarrow> 'a clt_list \<Rightarrow> 'a clt_list llM\<close>
  where [llvm_code]:
  \<open>clt_concat \<equiv> \<lambda>c1 c2. doM {
    let (p1, q1) = c1;
    let (p2, q2) = c2;
    if p1 = null then Mreturn (p2, q2)
    else if p2 = null then Mreturn (p1, q1)
    else doM {
      n \<leftarrow> ll_load q1;
      ll_store (Node (node.val n) p2) q1;
      Mreturn (p1, q2)
    }
  }\<close>

context begin

private lemma clt_concat_step:
  assumes \<open>xs \<noteq> []\<close> and \<open>ys \<noteq> []\<close> and \<open>p1 \<noteq> null\<close>
  shows \<open>ENTAILS
    (\<upharpoonleft>ll_bpto (Node c1 p2) q1 ** A (last xs) c1 ** olseg A (butlast ys) p2 q2
      ** \<upharpoonleft>ll_bpto (Node c2 null) q2 ** A (last ys) c2 ** olseg A (butlast xs) p1 q1)
    (clt_assn' A (xs @ ys) (p1, q2))\<close>
proof -
  have E: \<open>butlast xs @ [last xs] = xs\<close> using assms by simp
  have H1: \<open>olseg A (butlast xs) p1 q1 ** \<upharpoonleft>ll_bpto (Node c1 p2) q1 ** A (last xs) c1
      \<turnstile> olseg A xs p1 p2\<close>
    using olseg_snoc[of A \<open>butlast xs\<close> p1 q1 c1 p2 \<open>last xs\<close>] unfolding E .
  have R: \<open>(\<upharpoonleft>ll_bpto (Node c1 p2) q1 ** A (last xs) c1 ** olseg A (butlast ys) p2 q2
      ** \<upharpoonleft>ll_bpto (Node c2 null) q2 ** A (last ys) c2 ** olseg A (butlast xs) p1 q1)
    = (((olseg A (butlast xs) p1 q1 ** \<upharpoonleft>ll_bpto (Node c1 p2) q1 ** A (last xs) c1)
        ** olseg A (butlast ys) p2 q2)
      ** (\<upharpoonleft>ll_bpto (Node c2 null) q2 ** A (last ys) c2))\<close>
    by (simp add: sep_conj_aci)
  have SP: \<open>((olseg A (butlast xs) p1 q1 ** \<upharpoonleft>ll_bpto (Node c1 p2) q1 ** A (last xs) c1)
        ** olseg A (butlast ys) p2 q2) ** (\<upharpoonleft>ll_bpto (Node c2 null) q2 ** A (last ys) c2)
      \<turnstile> olseg A (xs @ butlast ys) p1 q2 ** (\<upharpoonleft>ll_bpto (Node c2 null) q2 ** A (last ys) c2)\<close>
    by (rule conj_entails_mono[OF entails_trans[OF
          conj_entails_mono[OF H1 entails_refl] olseg_append] entails_refl])
  show ?thesis
    unfolding ENTAILS_def R
    apply (rule entails_trans[OF SP])
    apply (simp add: clt_assn_conv butlast_append last_append assms)
    apply (rule entails_exI[where x = c2])
    using assms by (simp add: sep_algebra_simps pred_lift_extract_simps)
qed

lemma clt_concat_rule[vcg_rules]:
  \<open>llvm_htriple (clt_assn' A xs pq1 ** clt_assn' A ys pq2)
    (clt_concat pq1 pq2)
    (\<lambda>r. clt_assn' A (xs @ ys) r)\<close>
  unfolding clt_concat_def
  supply [simp] = clt_assn_conv olseg_nil sep_conj_exists
  apply (cases pq1; cases pq2; cases \<open>xs = []\<close>; cases \<open>ys = []\<close>; simp)
  subgoal by vcg
  subgoal by vcg
  subgoal by vcg
  subgoal
    apply vcg
    apply (rule clt_concat_step; assumption)
    done
  done

lemma clt_concat_hnr[sepref_fr_rules]:
  \<open>(uncurry clt_concat, uncurry (RETURN oo op_list_concat))
    \<in> (clt_assn' A)\<^sup>d *\<^sub>a (clt_assn' A)\<^sup>d \<rightarrow>\<^sub>a clt_assn' A\<close>
  by (sepref_to_hoare; vcg)

end

subsubsection \<open>Conversion to @{term cl_assn}\<close>

definition clt_to_cl :: \<open>'a::llvm_rep clt_list \<Rightarrow> 'a cl_list llM\<close> where [llvm_code, llvm_inline]:
  \<open>clt_to_cl \<equiv> \<lambda>(p, q). Mreturn p\<close>

lemma clt_to_cl_rule[vcg_rules]:
  \<open>llvm_htriple (clt_assn' A xs pq) (clt_to_cl pq) (\<lambda>r. cl_assn' A xs r)\<close>
  unfolding clt_to_cl_def
  apply (cases pq; simp)
  subgoal for p q
    apply (rule htriple_ent_pre[OF clt_cl_entails])
    by vcg
  done

definition op_clt_to_cl :: \<open>'a list \<Rightarrow> 'a list\<close> where [simp]: \<open>op_clt_to_cl xs = xs\<close>
sepref_register op_clt_to_cl

lemma clt_to_cl_hnr[sepref_fr_rules]:
  \<open>(clt_to_cl, RETURN o op_clt_to_cl) \<in> (clt_assn' A)\<^sup>d \<rightarrow>\<^sub>a cl_assn' A\<close>
  by (sepref_to_hoare; vcg)

subsubsection \<open>Appending a @{term cl_assn} list (O(1))\<close>

text \<open>Destructively links the last node of the tail-pointer list to the head of an
  ordinary copying list. Like @{term clt_concat} this needs no traversal; unlike it,
  the second operand carries no tail pointer, so the result is only a @{term cl_assn}
  list.\<close>

definition clt_cl_append :: \<open>'a::llvm_rep clt_list \<Rightarrow> 'a cl_list \<Rightarrow> 'a cl_list llM\<close>
  where [llvm_code]:
  \<open>clt_cl_append \<equiv> \<lambda>pq r. doM {
    let (p, q) = pq;
    if p = null then Mreturn r
    else doM {
      n \<leftarrow> ll_load q;
      ll_store (Node (node.val n) r) q;
      Mreturn p
    }
  }\<close>

lemma cl_assn_olseg: \<open>cl_assn' A xs p = olseg A xs p null\<close>
  unfolding cl_assn'_def cl_assn_def by simp

context begin

private lemma clt_cl_append_step:
  assumes \<open>xs \<noteq> []\<close> and \<open>p \<noteq> null\<close>
  shows \<open>ENTAILS
    (\<upharpoonleft>ll_bpto (Node c r) q ** A (last xs) c ** cl_assn' A ys r ** olseg A (butlast xs) p q)
    (cl_assn' A (xs @ ys) p)\<close>
proof -
  have E: \<open>butlast xs @ [last xs] = xs\<close> using assms by simp
  have H1: \<open>olseg A (butlast xs) p q ** \<upharpoonleft>ll_bpto (Node c r) q ** A (last xs) c
      \<turnstile> olseg A xs p r\<close>
    using olseg_snoc[of A \<open>butlast xs\<close> p q c r \<open>last xs\<close>] unfolding E .
  have R: \<open>(\<upharpoonleft>ll_bpto (Node c r) q ** A (last xs) c ** olseg A ys r null
      ** olseg A (butlast xs) p q)
    = ((olseg A (butlast xs) p q ** \<upharpoonleft>ll_bpto (Node c r) q ** A (last xs) c)
      ** olseg A ys r null)\<close>
    by (simp add: sep_conj_aci)
  show ?thesis
    unfolding ENTAILS_def cl_assn_olseg
    unfolding R
    by (rule entails_trans[OF conj_entails_mono[OF H1 entails_refl] olseg_append])
qed

lemma clt_cl_append_rule[vcg_rules]:
  \<open>llvm_htriple (clt_assn' A xs pq ** cl_assn' A ys ri)
    (clt_cl_append pq ri)
    (\<lambda>r. cl_assn' A (xs @ ys) r)\<close>
  unfolding clt_cl_append_def
  supply [simp] = clt_assn_conv olseg_nil sep_conj_exists
  apply (cases pq; cases \<open>xs = []\<close>; simp)
  subgoal by vcg
  subgoal
    apply vcg
    apply (rule clt_cl_append_step; assumption)
    done
  done

definition op_clt_cl_append :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where [simp]:
  \<open>op_clt_cl_append xs ys = xs @ ys\<close>
sepref_register op_clt_cl_append

lemma clt_cl_append_hnr[sepref_fr_rules]:
  \<open>(uncurry clt_cl_append, uncurry (RETURN oo op_clt_cl_append))
    \<in> (clt_assn' A)\<^sup>d *\<^sub>a (cl_assn' A)\<^sup>d \<rightarrow>\<^sub>a cl_assn' A\<close>
  by (sepref_to_hoare; vcg)

end

subsubsection \<open>Concatenation when one operand is empty (O(1))\<close>

text \<open>Guarded variant of @{term op_list_concat}: if one of the two lists is known to
  be empty, the concatenation is just a pointer choice and needs no traversal
  (@{term cl_concat} walks its first argument). The guard must be established by an
  @{term ASSERT} at the call site.\<close>

definition cl_concat0 :: \<open>'a::llvm_rep cl_list \<Rightarrow> 'a cl_list \<Rightarrow> 'a cl_list llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>cl_concat0 \<equiv> \<lambda>p q. if p = null then Mreturn q else Mreturn p\<close>

definition op_cl_concat0 :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where [simp]:
  \<open>op_cl_concat0 xs ys = xs @ ys\<close>
sepref_register op_cl_concat0

lemma cl_concat0_rule[vcg_rules]:
  \<open>llvm_htriple (cl_assn' A xs p ** cl_assn' A ys q ** \<up>(xs = [] \<or> ys = []))
    (cl_concat0 p q)
    (\<lambda>r. cl_assn' A (xs @ ys) r)\<close>
  unfolding cl_concat0_def
  supply [simp] = cl_assn_simps
  apply (cases \<open>xs = []\<close>; cases \<open>p = null\<close>; simp)
  apply (all \<open>vcg\<close>)
  done

lemma cl_concat0_hnr[sepref_fr_rules]:
  \<open>(uncurry cl_concat0, uncurry (RETURN oo op_cl_concat0))
    \<in> [\<lambda>(xs, ys). xs = [] \<or> ys = []]\<^sub>a (cl_assn' A)\<^sup>d *\<^sub>a (cl_assn' A)\<^sup>d \<rightarrow> cl_assn' A\<close>
  by (sepref_to_hoare; vcg)

subsubsection \<open>Free\<close>

context freeable_assn
begin

definition clt_free :: \<open>'b clt_list \<Rightarrow> unit llM\<close> where [llvm_code]:
  \<open>clt_free \<equiv> \<lambda>(p, q). cl_free p\<close>

lemma clt_assn_free[sepref_frame_free_rules]: \<open>MK_FREE (clt_assn' A) clt_free\<close>
proof (rule MK_FREEI)
  fix xs pq
  show \<open>llvm_htriple (clt_assn' A xs pq) (clt_free pq) (\<lambda>_. \<box>)\<close>
    unfolding clt_free_def
    apply (cases pq; simp)
    subgoal for p q
      apply (rule htriple_ent_pre[OF clt_cl_entails])
      by vcg
    done
qed

end

subsubsection \<open>Copyable @{term cl_assn} to @{term clt_assn} (keeps the original list)\<close>

definition cl_to_clt :: \<open>'a list \<Rightarrow> 'a list\<close> where
  \<open>cl_to_clt \<equiv> foldl (\<lambda>acc a. acc @ [a]) []\<close>

definition cl_to_clt_inner :: \<open>'a list \<Rightarrow> 'a \<Rightarrow> 'a list\<close> where
  \<open>cl_to_clt_inner \<equiv> \<lambda>acc a. acc @ [COPY a]\<close>

lemma foldl_snoc: \<open>foldl (\<lambda>acc a. acc @ [a]) a xs = a @ xs\<close>
  by (induction xs arbitrary: a) auto

lemma foldl_cl_to_clt_inner: \<open>foldl cl_to_clt_inner a xs = a @ xs\<close>
  by (induction xs arbitrary: a) (auto simp: cl_to_clt_inner_def)

lemma cl_to_clt_id: \<open>cl_to_clt xs = xs\<close>
  unfolding cl_to_clt_def by (simp add: foldl_snoc)

context copyable_assn
begin

sepref_def cl_to_clt_inner_impl is \<open>uncurry (RETURN oo cl_to_clt_inner)\<close>
  :: \<open>(clt_assn' A)\<^sup>d *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a clt_assn' A\<close>
  unfolding cl_to_clt_inner_def
  by sepref

definition [llvm_code]: \<open>cl_to_clt_impl \<equiv> \<lambda>p. doM {e \<leftarrow> clt_empty; cl_fold' cl_to_clt_inner_impl e p}\<close>

lemma cl_to_clt_rule: \<open>llvm_htriple
  ((cl_assn' A) xs xsi)
  (cl_to_clt_impl xsi)
  (\<lambda>r. (cl_assn' A) xs xsi ** (clt_assn' A) xs r)\<close>
proof -
  have BODY: \<open>llvm_htriple (clt_assn' A a ai ** A x xi) (cl_to_clt_inner_impl ai xi)
      (\<lambda>r. clt_assn' A (cl_to_clt_inner a x) r ** A x xi)\<close> for a ai x xi
    apply (rule htriple_ent_post[OF _ hfref_htriple_d1_k2[OF cl_to_clt_inner_impl.refine]])
    by (simp add: sep_conj_aci)
  show ?thesis
    unfolding cl_to_clt_impl_def
    supply [vcg_rules] = cl_fold'_rule[where R=\<open>clt_assn' A\<close> and A=A
        and f=cl_to_clt_inner_impl and fa=cl_to_clt_inner, OF BODY]
    supply [simp] = foldl_cl_to_clt_inner
    by vcg
qed

lemma cl_to_clt_hnr[sepref_fr_rules]:
  \<open>(cl_to_clt_impl, RETURN o cl_to_clt) \<in> (cl_assn' A)\<^sup>k \<rightarrow>\<^sub>a clt_assn' A\<close>
  supply [vcg_rules] = cl_to_clt_rule
  supply [simp] = cl_to_clt_id
  by (sepref_to_hoare; vcg)

end

section \<open>Copying_List operations, relying on clt\<close>
subsection \<open>@{term op_list_copy}\<close>

context copyable_assn
begin

definition cl_copy' :: \<open>'b cl_list \<Rightarrow> 'b clt_list llM\<close> where [llvm_code]:
  \<open>cl_copy' p \<equiv> doM {
    p' \<leftarrow> clt_empty;
    (_,p') \<leftarrow> llc_while
      (\<lambda>(p,p'). ll_cmp (p \<noteq> null))
      (\<lambda>(p,p'). doM {
        n \<leftarrow> ll_load p;
        v \<leftarrow> acopy (node.val n);
        p' \<leftarrow> clt_snoc p' v;
        let p = node.next n;
        Mreturn (p, p')
      }) (p, p');
    Mreturn p'
  }\<close>

context begin

private lemma cl_assn'_pure_partD:
  \<open>pure_part (cl_assn' A ys p) \<Longrightarrow> ys = [] \<longrightarrow> p = null\<close>
  by (cases ys) (auto simp: cl_assn_simps)

private lemma cl_copy'_step_entails:
  assumes \<open>x < length xs\<close>
  shows \<open>ENTAILS
    (clt_assn' A (take x xs @ [xs ! x]) (aa, b) ** cl_assn' A (drop (Suc x) xs) xb
      ** olseg A (take x xs) xi a ** \<upharpoonleft>ll_bpto (Node xa xb) a ** A (xs ! x) xa)
    (EXS t. (EXS n. clt_assn' A (take n xs) (aa, b) ** cl_assn' A (drop n xs) xb
        ** olseg A (take n xs) xi xb
        ** \<up>(n \<le> length xs \<and> (n < length xs \<or> xb = null))
        ** \<up>\<^sub>!(t = length xs - n))
      ** \<up>\<^sub>d((t, length xs - x) \<in> measure id) ** \<box>)\<close>
proof -
  have E: \<open>take x xs @ [xs ! x] = take (Suc x) xs\<close>
    using assms by (simp add: take_Suc_conv_app_nth)
  have H: \<open>olseg A (take x xs) xi a ** \<upharpoonleft>ll_bpto (Node xa xb) a ** A (xs ! x) xa
      \<turnstile> olseg A (take (Suc x) xs) xi xb\<close>
    using olseg_snoc[of A \<open>take x xs\<close> xi a xa xb \<open>xs ! x\<close>] unfolding E .
  have R: \<open>(clt_assn' A (take x xs @ [xs ! x]) (aa, b) ** cl_assn' A (drop (Suc x) xs) xb
      ** olseg A (take x xs) xi a ** \<upharpoonleft>ll_bpto (Node xa xb) a ** A (xs ! x) xa)
    = ((olseg A (take x xs) xi a ** \<upharpoonleft>ll_bpto (Node xa xb) a ** A (xs ! x) xa)
      ** (clt_assn' A (take (Suc x) xs) (aa, b) ** cl_assn' A (drop (Suc x) xs) xb))\<close>
    unfolding E by (simp add: sep_conj_aci)
  have SP: \<open>clt_assn' A (take x xs @ [xs ! x]) (aa, b) ** cl_assn' A (drop (Suc x) xs) xb
      ** olseg A (take x xs) xi a ** \<upharpoonleft>ll_bpto (Node xa xb) a ** A (xs ! x) xa
    \<turnstile> olseg A (take (Suc x) xs) xi xb ** clt_assn' A (take (Suc x) xs) (aa, b)
      ** cl_assn' A (drop (Suc x) xs) xb\<close>
    unfolding R by (rule conj_entails_mono[OF H entails_refl])
  have L: \<open>Suc x \<le> length xs\<close> and T: \<open>length xs - Suc x < length xs - x\<close>
    using assms by auto
  show ?thesis
    unfolding ENTAILS_def
  proof (rule entails_pureI)
    assume \<open>pure_part (clt_assn' A (take x xs @ [xs ! x]) (aa, b)
      ** cl_assn' A (drop (Suc x) xs) xb ** olseg A (take x xs) xi a
      ** \<upharpoonleft>ll_bpto (Node xa xb) a ** A (xs ! x) xa)\<close>
    then have D: \<open>Suc x < length xs \<or> xb = null\<close>
      using L by (auto dest!: pure_part_split_conj dest: cl_assn'_pure_partD)
    show \<open>clt_assn' A (take x xs @ [xs ! x]) (aa, b) ** cl_assn' A (drop (Suc x) xs) xb
      ** olseg A (take x xs) xi a ** \<upharpoonleft>ll_bpto (Node xa xb) a ** A (xs ! x) xa
      \<turnstile> (EXS t. (EXS n. clt_assn' A (take n xs) (aa, b) ** cl_assn' A (drop n xs) xb
        ** olseg A (take n xs) xi xb
        ** \<up>(n \<le> length xs \<and> (n < length xs \<or> xb = null))
        ** \<up>\<^sub>!(t = length xs - n))
      ** \<up>\<^sub>d((t, length xs - x) \<in> measure id) ** \<box>)\<close>
      apply (rule entails_trans[OF SP])
      apply (simp add: sep_algebra_simps)
      apply (rule entails_exI[where x=\<open>length xs - Suc x\<close>])
      apply (rule entails_exI[where x=\<open>Suc x\<close>])
      apply (simp add: vcg_tag_defs L T D sep_algebra_simps pred_lift_extract_simps)
      by (simp add: sep_conj_aci entails_refl)
  qed
qed

text \<open>Frame-inference helpers for the loop entry: the invariant's index \<open>n\<close> is
  existentially quantified, so nothing in the initial state pins it. These rules
  let the frame solver instantiate \<open>n := 0\<close> via \<open>auto\<close> (cf. @{thm fri_abs_cong_rl}).\<close>

private lemma clt_entry_fri:
  \<open>PRECOND (SOLVE_AUTO ([] = ys)) \<Longrightarrow> clt_assn' A' [] pq \<turnstile> clt_assn' A ys pq\<close>
  unfolding vcg_tag_defs by (cases pq) (simp add: clt_assn_conv)

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

lemma cl_copy'_rule[vcg_rules]:
  \<open>llvm_htriple
    (cl_assn' A xs xi)
    (cl_copy' xi)
    (\<lambda>r. cl_assn' A xs xi ** clt_assn' A xs r)\<close>
  unfolding cl_copy'_def
  apply (rewrite annotate_llc_while [where
    I = \<open>\<lambda>(p,p') t. EXS n. clt_assn' A (take n xs) p'
        ** cl_assn' A (drop n xs) p ** olseg A (take n xs) xi p
        ** \<up>(n \<le> length xs \<and> (n < length xs \<or> p = null)) ** \<up>\<^sub>!(t = length xs - n)\<close>
    and R = \<open>measure id\<close>])
  supply [simp] = cl_assn_simps olseg_nil sep_conj_exists drop_head
  supply [fri_rules] = clt_entry_fri cl_assn'_cong_fri olseg_empty_fri olseg_cl_fri
  apply vcg_monadify
  apply vcg'
  subgoal by (rule cl_copy'_step_entails; assumption)
  subgoal for asf a aa b x r s
    apply (rule impI)
    apply hypsubst
    apply vcg'
    done
  by (tactic \<open>Defer_Slot.remove_slot_tac\<close>)

end

definition[llvm_code]: \<open>cl_copy p \<equiv> doM{ p' \<leftarrow> cl_copy' p; clt_to_cl p' }\<close>

lemma cl_copy_rule[vcg_rules]:
  \<open>llvm_htriple
    (cl_assn' A xs xi)
    (cl_copy xi)
    (\<lambda>r. cl_assn' A xs xi ** cl_assn' A xs r)\<close>
  unfolding cl_copy_def
  by vcg

lemma cl_copy_hnr[sepref_fr_rules]:
  \<open>(cl_copy, RETURN o COPY) \<in> (cl_assn' A)\<^sup>k \<rightarrow>\<^sub>a (cl_assn' A)\<close>
  by (sepref_to_hoare; vcg)

lemma cl_copy_is_copy[sepref_gen_algo_rules]:
  \<open>GEN_ALGO cl_copy (is_copy (cl_assn' A))\<close>
  unfolding GEN_ALGO_def is_copy_def
  by (rule cl_copy_hnr)

end 

section \<open>Regression Tests\<close>

experiment begin

text \<open>Inner lists hold pure elements (64-bit snat numbers), so their copy is @{term Mreturn}
  and their free is a no-op. The outer instantiation then uses the inner list's
  \<open>P.cl_copy\<close>/\<open>P.cl_free\<close> as element copy/free.\<close>

interpretation P: copyable_assn \<open>snat_assn' TYPE(64)\<close> \<open>\<lambda>_. Mreturn ()\<close> Mreturn
  apply unfold_locales
  subgoal by (rule mk_free_pure)
  subgoal by (rule hnr_pure_COPY) simp
  done

interpretation PP: copyable_assn \<open>cl_assn' (snat_assn' TYPE(64))\<close> P.cl_free P.cl_copy
  apply unfold_locales
  subgoal by (rule P.cl_assn_free)
  subgoal by (rule P.cl_copy_hnr)
  done

text \<open>The order locale instantiated with 64-bit numbers as elements.\<close>

interpretation N: linorder_assn \<open>snat_assn' TYPE(64)\<close> ll_icmp_eq ll_icmp_slt
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

section \<open>Extras\<close>
text \<open>Some lemmas which are often helpful for refining functions that work on lists\<close>
lemma ls_emp: \<open>p\<noteq>[] \<equiv> \<not>(op_list_is_empty p)\<close> by simp
lemma ls_emp': \<open>p = [] \<equiv> op_list_is_empty p\<close> by simp

subsection \<open>Regression Tests\<close>

experiment begin

interpretation P: copyable_assn \<open>snat_assn' TYPE(64)\<close> \<open>\<lambda>_. Mreturn ()\<close> Mreturn
  apply unfold_locales
  subgoal by (rule mk_free_pure)
  subgoal by (rule hnr_pure_COPY) simp
  done

definition test_clt :: \<open>nat list nres\<close> where
  \<open>test_clt = doN {
    let xs = op_clt_empty;
    let xs = op_list_append xs 1;
    let xs = op_list_append xs 2;
    RETURN (op_clt_to_cl xs)
  }\<close>

sepref_definition test_clt_impl is \<open>uncurry0 test_clt\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a cl_assn' (snat_assn' TYPE(64))\<close>
  unfolding test_clt_def
  apply (annot_snat_const "TYPE(64)")
  by sepref

definition test_clt_concat :: \<open>nat list nres\<close> where
  \<open>test_clt_concat = doN {
    let xs = op_clt_empty;
    let xs = op_list_append xs 1;
    let ys = op_clt_empty;
    let ys = op_list_append ys 2;
    RETURN (op_clt_to_cl (xs @ ys))
  }\<close>

sepref_definition test_clt_concat_impl is \<open>uncurry0 test_clt_concat\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a cl_assn' (snat_assn' TYPE(64))\<close>
  unfolding test_clt_concat_def
  apply (annot_snat_const "TYPE(64)")
  by sepref

end

end
