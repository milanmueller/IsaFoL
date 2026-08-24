theory More_EOArray
  imports Isabelle_LLVM.Proto_EOArray
    LLVM_String
begin

text \<open>This theory contains a variation of @{term nao_assn} that stores elements directly
  instead of wrappig them in @{term option}. Also, we store the length and capacity like for
  @{term arl_assn}. Noteworthably, this is an opinionated implementation that will copy elements on retreival.
  \<close>

context copyable_assn
begin

definition oa_assn :: "('a list, ('b, 64) array_list) dr_assn" where
  \<open>oa_assn \<equiv> mk_assn (\<lambda>xs ali. EXS xsi. \<upharpoonleft>arl_assn xsi ali ** \<upharpoonleft>(list_assn (mk_assn A)) xs xsi)\<close>
abbreviation \<open>oa_assn' \<equiv> \<upharpoonleft>oa_assn\<close>

section \<open>nth\<close>

definition oa_nth :: \<open>('b, 64) array_list \<Rightarrow> 64 word \<Rightarrow> 'b llM\<close> where[llvm_code,llvm_inline]:
  \<open>oa_nth ai i \<equiv> doM {xi \<leftarrow> arl_nth ai i; acopy xi}\<close>

lemma list_assn_focus:
  assumes I: \<open>i < length xs\<close>
  shows \<open>\<upharpoonleft>(list_assn (mk_assn A)) xs xsi =
    (A (xs!i) (xsi!i)
     ** \<upharpoonleft>(list_assn (mk_assn A)) (take i xs) (take i xsi)
     ** \<upharpoonleft>(list_assn (mk_assn A)) (drop (Suc i) xs) (drop (Suc i) xsi)
     ** \<up>(length xsi = length xs))\<close>
proof (cases \<open>length xsi = length xs\<close>)
  case True
  obtain xs\<^sub>1 x xs\<^sub>2 where XSF: \<open>xs = xs\<^sub>1 @ x # xs\<^sub>2\<close> and LEN1: \<open>i = length xs\<^sub>1\<close>
    using id_take_nth_drop[OF I] I by fastforce
  obtain ys\<^sub>1 y ys\<^sub>2 where YSF: \<open>xsi = ys\<^sub>1 @ y # ys\<^sub>2\<close> and LEN2: \<open>length ys\<^sub>1 = length xs\<^sub>1\<close>
    and LEN3: \<open>length ys\<^sub>2 = length xs\<^sub>2\<close>
    using split_list_according[OF XSF True] .
  show ?thesis
    unfolding XSF YSF LEN1
    by (simp add: LEN2 LEN3 nth_append sep_algebra_simps sep_conj_c)
qed (simp add: sep_algebra_simps)

lemma list_assn_acopy_nth_rule[vcg_rules]:
  \<open>llvm_htriple
     (\<upharpoonleft>(list_assn (mk_assn A)) xs xsi ** \<up>\<^sub>d(i < length xs))
     (acopy (xsi!i))
     (\<lambda>r. \<upharpoonleft>(list_assn (mk_assn A)) xs xsi ** A (xs!i) r)\<close>
proof (induction xs arbitrary: i xsi)
  case Nil
  then show ?case by vcg
next
  case (Cons x xs')
  note [vcg_rules] = Cons.IH
  show ?case
    apply (cases xsi; cases i; simp)
    by vcg
qed

lemma oa_nth_rule[vcg_rules]:
  \<open>llvm_htriple
    (\<upharpoonleft>oa_assn xs ali ** \<upharpoonleft>snat.assn i ii ** \<up>\<^sub>d(i < length xs))
    (oa_nth ali ii)
    (\<lambda>x. \<upharpoonleft>oa_assn xs ali ** A (xs!i) x)\<close>
  unfolding oa_nth_def oa_assn_def
  by vcg

lemma oa_hnr:
  \<open>(uncurry oa_nth, uncurry (RETURN oo op_list_get))
  \<in> [\<lambda>(xs, i). i < length xs]\<^sub>a oa_assn'\<^sup>k *\<^sub>a (snat_assn' TYPE(64))\<^sup>k \<rightarrow> A\<close>
  unfolding op_list_get_def snat.assn_is_rel[symmetric] snat_rel_def
  apply sepref_to_hoare
  by vcg

section \<open>Update\<close>

text \<open>We reuse the existing @{term arl_upd} implementation and leave
  copying to the caller.\<close>

definition oa_upd :: \<open>('b, 64) array_list \<Rightarrow> 64 word \<Rightarrow> 'b \<Rightarrow> ('b, 64) array_list llM\<close>
  where [llvm_code]:
  \<open>oa_upd ai ii xi \<equiv> doM {
    old \<leftarrow> arl_nth ai ii;
    afree old;
    arl_upd ai ii xi
  }\<close>

lemma list_assn_afree_set_rule[vcg_rules]:
  \<open>llvm_htriple
     (\<upharpoonleft>(list_assn (mk_assn A)) xs xsi ** A x xi ** \<up>\<^sub>d(i < length xs))
     (afree (xsi!i))
     (\<lambda>_. \<upharpoonleft>(list_assn (mk_assn A)) (xs[i:=x]) (xsi[i:=xi]))\<close>
proof (induction xs arbitrary: i xsi)
  case Nil
  then show ?case by vcg
next
  case (Cons y ys)
  note [vcg_rules] = Cons.IH
  show ?case
    apply (cases xsi; cases i; simp)
    by vcg
qed

lemma oa_upd_rule[vcg_rules]:
  \<open>llvm_htriple
    (\<upharpoonleft>oa_assn xs ali ** \<upharpoonleft>snat.assn i ii ** A x xi ** \<up>\<^sub>d(i < length xs))
    (oa_upd ali ii xi)
    (\<lambda>r. \<up>(r = ali) ** \<upharpoonleft>oa_assn (xs[i:=x]) ali)\<close>
  unfolding oa_upd_def oa_assn_def
  by vcg

lemma oa_upd_hnr:
  \<open>(uncurry2 oa_upd, uncurry2 (RETURN ooo op_list_set))
  \<in> [\<lambda>((xs, i), x). i < length xs]\<^sub>a oa_assn'\<^sup>d *\<^sub>a (snat_assn' TYPE(64))\<^sup>k *\<^sub>a A\<^sup>d \<rightarrow> oa_assn'\<close>
  unfolding op_list_set_def snat_rel_def snat.assn_is_rel[symmetric]
  apply sepref_to_hoare
  by vcg

section \<open>Push back\<close>

definition oa_push_back :: \<open>('b, 64) array_list \<Rightarrow> 'b \<Rightarrow> ('b, 64) array_list llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>oa_push_back ai xi \<equiv> arl_push_back ai xi\<close>

lemma oa_push_back_aux:
  \<open>ENTAILS
     (\<upharpoonleft>arl_assn (xsi @ [xi]) ali \<and>* \<upharpoonleft>(list_assn (mk_assn A)) xs xsi \<and>* A x xi)
     (\<lambda>c. \<exists>xsi'. (\<upharpoonleft>arl_assn xsi' ali \<and>* \<upharpoonleft>(list_assn (mk_assn A)) (xs @ [x]) xsi') c)\<close>
  unfolding ENTAILS_def
  apply (rule entails_pureI)
  apply (clarsimp dest!: pure_part_split_conj list_assn_pure_part)
  apply (rule entails_exI[where x=\<open>xsi @ [xi]\<close>])
  by (simp add: sep_algebra_simps sep_conj_aci)

lemma oa_push_back_rule[vcg_rules]:
  \<open>llvm_htriple
    (\<upharpoonleft>oa_assn xs ali ** A x xi ** \<up>\<^sub>d(length xs + 1 < max_snat 64))
    (oa_push_back ali xi)
    (\<lambda>ali'. \<upharpoonleft>oa_assn (xs @ [x]) ali')\<close>
  unfolding oa_push_back_def oa_assn_def
  apply vcg
  by (rule oa_push_back_aux)

lemma oa_push_back_hnr:
  \<open>(uncurry oa_push_back, uncurry (RETURN oo op_list_append))
  \<in> [\<lambda>(xs, _). length xs + 1 < max_snat 64]\<^sub>a oa_assn'\<^sup>d *\<^sub>a A\<^sup>d \<rightarrow> oa_assn'\<close>
  unfolding op_list_append_def
  apply sepref_to_hoare
  by vcg

section \<open>Length\<close>

definition oa_len :: \<open>('b, 64) array_list \<Rightarrow> 64 word llM\<close> where [llvm_code, llvm_inline]:
  \<open>oa_len ai \<equiv> arl_len ai\<close>

lemma oa_len_aux:
  assumes L: \<open>\<flat>\<^sub>psnat.assn (length xsi) li\<close>
  shows \<open>ENTAILS
     (\<upharpoonleft>arl_assn xsi ali \<and>* \<upharpoonleft>(list_assn (mk_assn A)) xs xsi)
     ((\<lambda>a. \<exists>xsi'. (\<upharpoonleft>arl_assn xsi' ali \<and>* \<upharpoonleft>(list_assn (mk_assn A)) xs xsi') a)
       \<and>* \<upharpoonleft>snat.assn (length xs) li)\<close>
  unfolding ENTAILS_def
  apply (rule entails_pureI)
  apply (clarsimp dest!: pure_part_split_conj list_assn_pure_part)
  apply (simp add: snat.assn_pure[THEN extract_pure_assn] L sep_algebra_simps
    pred_lift_extract_simps)
  apply (rule entails_exI[where x=xsi])
  by (rule entails_refl)

lemma oa_len_rule[vcg_rules]:
  \<open>llvm_htriple (\<upharpoonleft>oa_assn xs ali) (oa_len ali)
    (\<lambda>li. \<upharpoonleft>oa_assn xs ali ** \<upharpoonleft>snat.assn (length xs) li)\<close>
  unfolding oa_len_def oa_assn_def
  apply vcg
  by (rule oa_len_aux)

lemma oa_len_hnr:
  \<open>(oa_len, RETURN o op_list_length) \<in> oa_assn'\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(64)\<close>
  unfolding op_list_length_def snat_rel_def snat.assn_is_rel[symmetric]
  apply sepref_to_hoare
  by vcg

section \<open>Empty\<close>

lemma oa_empty_rule[vcg_rules]:
  \<open>llvm_htriple \<box> (arl_new TYPE('b) TYPE(64)) (\<lambda>ali. \<upharpoonleft>oa_assn [] ali)\<close>
  unfolding oa_assn_def
  by vcg

definition oa_empty :: \<open>('b, 64) array_list llM\<close> where [llvm_code, llvm_inline]:
  \<open>oa_empty \<equiv> arl_new TYPE('b) TYPE(64)\<close>

lemma oa_empty_hnr:
  \<open>(uncurry0 oa_empty, uncurry0 (RETURN op_list_empty)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a oa_assn'\<close>
  unfolding oa_empty_def op_list_empty_def
  apply sepref_to_hoare
  by vcg

section \<open>Free\<close>
text \<open>We need to also free the inner elements.\<close>

definition oa_free :: \<open>('b, 64) array_list \<Rightarrow> unit llM\<close> where [llvm_code]:
  \<open>oa_free ai \<equiv> doM {
  llc_while
    (\<lambda>i. doM{ l \<leftarrow> oa_len ai; ll_icmp_ult i l })
    (\<lambda>i. doM {
      xi \<leftarrow> arl_nth ai i;
      afree xi;
      i \<leftarrow> ll_add i (signed_nat 1);
      Mreturn i
    }) (signed_nat 0);
    arl_free ai
  }\<close>

lemma oa_free_aux_rule:
  \<open>llvm_htriple
    (\<upharpoonleft>arl_assn xsi ali ** \<upharpoonleft>(list_assn (mk_assn A)) xs xsi)
    (oa_free ali)
    (\<lambda>_. \<box>)\<close>
  unfolding oa_free_def oa_len_def
  apply (rewrite annotate_llc_while[where
    I=\<open>\<lambda>ii t. EXS i. \<upharpoonleft>snat.assn i ii ** \<upharpoonleft>arl_assn xsi ali
        ** \<upharpoonleft>(list_assn (mk_assn A)) (drop i xs) (drop i xsi)
        ** \<up>\<^sub>!(i \<le> length xs \<and> length xsi = length xs \<and> t = length xs - i)\<close>
    and R=\<open>less_than\<close>])
  supply [simp] = Cons_nth_drop_Suc[symmetric]
  apply vcg_monadify
  apply vcg'
  done

lemma oa_free_rule[vcg_rules]:
  \<open>llvm_htriple (\<upharpoonleft>oa_assn xs ali) (oa_free ali) (\<lambda>_. \<box>)\<close>
  unfolding oa_assn_def
  supply [vcg_rules] = oa_free_aux_rule
  by vcg

lemma oa_free_mk_free[sepref_frame_free_rules]: \<open>MK_FREE oa_assn' oa_free\<close>
  by (rule MK_FREEI) (rule oa_free_rule)

end

section \<open>Instantiation for string tables\<close>

interpretation strls: copyable_assn strl_assn' strl.cl_free strl.cl_copy
  apply unfold_locales
  subgoal by (rule strl.cl_assn_free)
  subgoal by (rule strl.cl_copy_hnr)
  done

abbreviation \<open>strls_assn \<equiv> \<upharpoonleft>strls.oa_assn\<close>

end
