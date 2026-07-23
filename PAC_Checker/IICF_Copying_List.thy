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
  the list intact. Container elements need to have an implementation of copy.\<close>

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

text \<open>Composing the spine rule with the element ownership: decompose \<open>cl_assn'\<close> into
  the plain spine plus element-wise \<open>list_assn\<close> ownership (cf. \<open>ol_assn_os_conv\<close> in
  \<open>IICF_Owning_List\<close>), then sandwich the framed spine rule. Plain \<open>vcg\<close> on such
  decomposed triples reliably diverges, hence the manual composition via
  \<open>htriple_pre_EXS\<close>/\<open>htriple_pure_preI\<close>.\<close>

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

lemma is_copy_rule[sepref_fr_rules]:
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

definition cl_copy :: \<open>'b cl_list \<Rightarrow> 'b cl_list llM\<close> where [llvm_code]:
  \<open>cl_copy \<equiv> MMonad.REC (\<lambda>cl_copy p.
    if p = null then Mreturn null else doM {
      n \<leftarrow> ll_load p;
      cpy \<leftarrow> acopy_impl (node.val n);
      tl \<leftarrow> cl_copy (node.next n);
      cl_prepend cpy tl
    })\<close>

end

experiment begin

definition \<open>nesttest xss = doN{
  ASSERT(xss \<noteq> []);
  ASSERT(hd xss \<noteq> []);
  RETURN (hd (hd xss))
}\<close> 

end

end
