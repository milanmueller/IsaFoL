theory String_Assn
  imports Isabelle_LLVM.LLVM_DS_Open_List Char_Assn
begin

text \<open>Implement Chars as Open Lists\<close>

type_synonym str = \<open>char list\<close>

term larray_assn

definition \<open>str_assn \<equiv> hr_comp \<upharpoonleft>os_list_assn (\<langle>the_pure char_assn\<rangle>list_rel)\<close>
lemma str_assn_pure: \<open>is_pure str_assn\<close>
  unfolding str_assn_def os_list_assn_def 
  (* do we have any chance here? I don't think we do... *)
  oops

(* We have to implement some functions for open lists which are not there yet *)
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

lemma op_tl_rule[vcg_rules]:
  \<open>xs \<noteq> [] \<Longrightarrow> llvm_htriple (\<upharpoonleft>os_list_assn xs r) (os_tl r) (\<lambda>x. \<upharpoonleft>os_list_assn (tl xs) x)\<close>
  apply (cases xs; simp)
  unfolding os_tl_def os_list_assn_def
  by vcg

definition os_list_get :: \<open>'a::llvm_rep os_list \<Rightarrow> 'b::len2 word \<Rightarrow> 'a llM\<close> where [llvm_code]:
  \<open>os_list_get p\<^sub>0 i\<^sub>0 = doM {
    (p, _) \<leftarrow> llc_while
      (\<lambda>(_, i). ll_cmp (i \<noteq> 0))
      (\<lambda>(p, i). doM {
        n \<leftarrow> ll_load p; 
        Mreturn (node.next n, i - 1)
      }) (p\<^sub>0, i\<^sub>0);
    n \<leftarrow> ll_load p;
    Mreturn (node.val n)
  }\<close>

lemma os_list_get_rule[vcg_rules]:
  \<open>llvm_htriple
    (\<upharpoonleft>os_list_assn xs p ** \<upharpoonleft>snat.assn n nn ** \<up>(n < length xs))
    (os_list_get p nn)
    (\<lambda>v. \<up>(v = xs ! n) ** \<upharpoonleft>os_list_assn xs p)\<close>
  unfolding os_list_get_def
  apply (rewrite annotate_llc_while [where
    I="\<lambda>(q, ii) t. EXS i. \<upharpoonleft>snat.assn i ii
                 ** lseg (take i xs) p q
                 ** lseg (drop i xs) q null
                 ** \<up>(i \<le> n \<and> 0 \<le> i)
                 ** \<up>\<^sub>!(t = i)"
    and R="measure id"])
  supply [simp] = os_list_assn_def
  apply vcg_monadify
  apply vcg
  sorry

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
lemma os_list_length_rule[vcg_rules]:
  \<open>llvm_htriple
    (\<upharpoonleft>os_list_assn xs p)
    (os_list_length p)
    (\<lambda>n. \<up>(unat n = length xs) ** \<upharpoonleft>os_list_assn xs p)\<close>
  unfolding os_list_length_def
  apply (rewrite annotate_llc_while [where
    I = \<open>\<lambda>(p', ii) t . EXS i. \<upharpoonleft>snat.assn i ii
                          ** (lseg (take i xs) p p')
                          ** (lseg (drop i xs) p' null)
                          ** \<up>(i \<le> length xs \<and> 0 \<le> i)
                          ** \<up>\<^sub>!(t = length xs - i)\<close>
    and R = \<open>measure id\<close>])
  supply [simp] = os_list_assn_def 
  apply vcg_monadify
  apply vcg
  subgoal for asf i0 p' ii s i
    apply (auto simp: STATE_def ABSTRACT_def POSTCOND_def EXTRACT_def)
  sorry

(* Now we specialize open lists to string *)
lemma str_empty_refine[sepref_fr_rules]:
  \<open>(uncurry0 os_empty, uncurry0 (RETURN op_list_empty)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a str_assn\<close>
  unfolding os_empty_def op_list_empty_def
  apply sepref_to_hoare
  apply vcg
  by (auto simp: str_assn_def ENTAILS_def entails_def os_list_assn_def hr_comp_def sep_algebra_simps)
    
lemma str_is_empty_refine[sepref_fr_rules]:
  \<open>(os_is_empty, RETURN o op_list_is_empty) \<in> [\<lambda>_. True]\<^sub>a str_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  unfolding os_is_empty_def str_assn_def op_list_is_empty_def 
  apply sepref_to_hoare
  subgoal for x xi
    apply (cases x; cases \<open>xi=null\<close>; simp)
    subgoal
      apply vcg
      apply (simp add: sep_algebra_simps ENTAILS_def entails_def hr_comp_def os_list_assn_def)
      by (metis bool.rel_def bool1_rel_def brI from_bool_to_bool_iff)
    subgoal
      apply vcg
      by (simp add: sep_algebra_simps ENTAILS_def hr_comp_def os_list_assn_def)
    subgoal
      apply vcg
      by (simp add: sep_algebra_simps ENTAILS_def hr_comp_def os_list_assn_def) 
    subgoal
      apply vcg
      by (auto simp: ENTAILS_def entails_def sep_algebra_simps hr_comp_def
        os_list_assn_def bool1_rel_def bool.rel_def in_br_conv)
    done
  done

lemma str_hd_refine[sepref_fr_rules]:
  \<open>(os_hd, RETURN o op_list_hd) \<in> [\<lambda>xs. xs \<noteq> []]\<^sub>a str_assn\<^sup>k \<rightarrow> char_assn\<close>
  unfolding str_assn_def op_list_hd_def hr_comp_def 
  apply sepref_to_hoare
  apply auto
  apply vcg
  subgoal by auto
  subgoal
    apply (simp add: sep_algebra_simps EXTRACT_def POSTCOND_def STATE_def list_rel_def os_list_assn_def)
    by (metis (no_types, lifting) Sepref_Basic.pure_def char_assn_def
    list.rel_cases list.sel(1) pred_lift_extract_simps(2) sep_conj_commuteI
    the_pure_pure)
  done 

lemma str_tl_refine[sepref_fr_rules]:
  \<open>(os_tl, RETURN o op_list_tl) \<in> [\<lambda>xs. xs \<noteq> []]\<^sub>a str_assn\<^sup>d \<rightarrow> str_assn\<close>
  unfolding str_assn_def op_list_tl_def hr_comp_def
  apply sepref_to_hoare
  apply auto
  apply vcg
  subgoal by auto
  subgoal
    apply (simp add: sep_algebra_simps STATE_def EXTRACT_def POSTCOND_def
            os_list_assn_def list_rel_def)
    using list.rel_sel by blast  
  done

lemma str_prepend_refine[sepref_fr_rules]:
  \<open>(uncurry os_prepend, uncurry (RETURN oo op_list_prepend)) \<in> char_assn\<^sup>k *\<^sub>a str_assn\<^sup>d \<rightarrow>\<^sub>a str_assn\<close>
  unfolding str_assn_def os_prepend_def op_list_prepend_def
  apply sepref_to_hoare
  apply (auto simp: os_list_assn_def hr_comp_def)
  apply vcg
  apply (auto simp: sep_algebra_simps ENTAILS_def entails_def list_rel_def os_list_assn_def
          char_assn_def char_rel_def in_br_conv char_of_word_def br_def)
  by (metis (lifting) list.simps(11) lseg_Cons mem_Collect_eq old.prod.case
    pred_lift_extract_simps(2) pure_app_eq sep_conj_aci(3))

lemma str_assn_mk_free[sepref_frame_free_rules]:
  \<open>MK_FREE str_assn os_delete\<close>
  apply (rule MK_FREEI)
  unfolding str_assn_def hr_comp_def 
  by vcg

lemma str_get_refine[sepref_fr_rules]:
  \<open>(uncurry os_list_get, uncurry (RETURN oo op_list_get)) \<in>
  [\<lambda>(xs,i). i < length xs]\<^sub>a str_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(64))\<^sup>k \<rightarrow> char_assn\<close>
  unfolding op_list_get_def
  apply sepref_to_hoare
  apply (simp add: str_assn_def hr_comp_def os_list_assn_simps)
  apply vcg
  apply (simp add: sep_algebra_simps STATE_def EXTRACT_def POSTCOND_def snat_rel_def snat.rel_def
    os_list_assn_def
    snat_invar_def ll_cmp_def list_rel_def char_assn_def char_rel_def in_br_conv char_of_word_def)
  subgoal by (metis snat_invar_def snat_eq_unat_aux2 list_all2_lengthD)
  subgoal for bi a ai asf x sa
    (* Residual: pick witness \<langle>x\<rangle>, then separation-logic split of the heap
       into \<langle>os_list_assn x ai\<rangle> \<^emph> pure \<langle>char_assn (a!snat bi) (x!unat bi)\<rangle>.
       Pattern in \<langle>str_hd_refine\<rangle> uses \<langle>list.rel_cases\<rangle> on the head; here
       we'd need \<langle>list_all2_conv_all_nth\<rangle> at index \<langle>snat bi = unat bi\<rangle>. *)
    sorry
  done

(* NOTE: lemma as stated is not provable without a precondition like
   \<langle>length xs < 2^(LENGTH('b) - 1)\<rangle> guaranteeing the result fits as snat.
   After existing tactics + this auto, the residual goal is
   \<langle>length x = snat r\<rangle> and \<langle>msb r \<Longrightarrow> False\<rangle>; the second cannot be discharged
   without such a bound. *)
lemma str_len_refine[sepref_fr_rules]:
  \<open>(os_list_length, RETURN o op_list_length) \<in> str_assn\<^sup>k \<rightarrow>\<^sub>a (snat_assn' TYPE(64))\<close>
  apply sepref_to_hoare
  apply (simp add: str_assn_def hr_comp_def os_list_assn_simps)
  apply vcg
  apply (simp add: sep_algebra_simps STATE_def EXTRACT_def POSTCOND_def os_list_assn_def
          list_rel_def char_assn_def char_rel_def in_br_conv char_of_word_def)
  apply (auto simp: ENTAILS_def entails_def snat_rel_def snat.rel_def br_def
          snat_invar_def list_all2_lengthD sep_algebra_simps pred_lift_extract_simps
          snat_eq_unat)
  sorry

experiment begin

  definition test :: \<open>str \<Rightarrow> char\<close> where
    \<open>test cs \<equiv> (if cs = [] then (char_of_word (0::(8 word))) else hd cs)\<close>

  sepref_def test_impl is \<open>RETURN o test\<close>
    :: \<open>str_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
    unfolding test_def 
    by sepref

  (* export_llvm \<open>test_impl\<close> *)

  definition empty_check :: \<open>str \<Rightarrow> bool\<close> where
    \<open>empty_check cs \<equiv> cs = []\<close>

  sepref_def empty_check_impl is \<open>RETURN o empty_check\<close>
    :: \<open>str_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
    unfolding empty_check_def
    by sepref

  (* export_llvm empty_check_impl *)

  definition cons_test :: \<open>str \<Rightarrow> char \<Rightarrow> str\<close> where
    \<open>cons_test cs c = c # cs\<close>

  sepref_def cons_test_impl is \<open>uncurry (RETURN oo cons_test)\<close>
    :: \<open>str_assn\<^sup>d *\<^sub>a char_assn\<^sup>k \<rightarrow>\<^sub>a str_assn\<close>
    unfolding cons_test_def
    by sepref

  definition tail_test :: \<open>str \<Rightarrow> str\<close> where
    \<open>tail_test cs = (if cs = [] then cs else tl cs)\<close>

  sepref_def tail_test_impl is \<open>RETURN o tail_test\<close>
    :: \<open>str_assn\<^sup>d \<rightarrow>\<^sub>a str_assn\<close>
    unfolding tail_test_def
    by sepref

  (* definition swap_test' :: \<open>str \<Rightarrow> str\<close> where
   *   \<open>swap_test' cs = (if cs = [] then cs else
   *     let a = hd cs; bs = tl cs in
   *     a # bs
   *   )\<close> *)

  definition dest_cons_test :: \<open>str \<Rightarrow> str\<close> where
    \<open>dest_cons_test cs = (case cs of
      [] \<Rightarrow> cs
    | (c # cs') \<Rightarrow> c # cs'
    )\<close>

  sepref_def dest_cons_test_impl is \<open>RETURN o dest_cons_test\<close>
    :: \<open>str_assn\<^sup>d \<rightarrow>\<^sub>a str_assn\<close>
    unfolding dest_cons_test_def
    apply sepref_dbg_keep
    apply sepref_dbg_trans_keep
    apply sepref_dbg_trans_step_keep
    apply sepref_dbg_side_unfold
    oops

end

end
