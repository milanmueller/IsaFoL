theory LLVM_String
  imports Char_Assn IICF_Copying_List Isabelle_LLVM.IICF
    PAC_Polynomials_Sort
begin

text \<open>Here, we provide two implementations of strings:
  \<^item> One using our custom copying list @{term cl_assn}
  \<^item> One using @{term larray_assn}\<close>

section \<open>String by List\<close>
abbreviation \<open>strl_assn \<equiv> cl_assn char_assn\<close>
abbreviation \<open>strl_assn' \<equiv> cl_assn' char_assn\<close>

interpretation strl: copy_free_context char_assn \<open>\<lambda>_. Mreturn ()\<close> Mreturn
  apply unfold_locales
  subgoal by (rule char_assn_mk_free)
  subgoal by (rule is_copy_pure_gen_algo) (simp add: char_assn_pure)
  done

interpretation strl: linord_copying_list char_assn ll_icmp_eq ll_icmp_ult
  apply unfold_locales
  subgoal by (rule char_eq_hnr)
  subgoal by (rule char_lt_hnr)
  done

interpretation strl: cmp_env_impl
  \<open>(\<le>)\<close> \<open>char_assn\<close>  \<open>\<lambda>_. Mreturn ()\<close> \<open>char_le_impl\<close>
  apply unfold_locales
  subgoal by auto
  subgoal by auto
  subgoal by (rule char_le_impl.refine)
  done

sepref_register \<open>(=) :: char list \<Rightarrow> char list \<Rightarrow> bool\<close>
sepref_register \<open>(<) :: char list \<Rightarrow> char list \<Rightarrow> bool\<close>
sepref_register \<open>(\<le>) :: char list \<Rightarrow> char list \<Rightarrow> bool\<close>

lemmas strl_less_hnr[sepref_fr_rules] = strl.cl_less_hnr[unfolded list_lt_less]
lemmas strl_le_hnr[sepref_fr_rules] = strl.cl_le_hnr[unfolded list_le_less_eq]

experiment
begin

definition \<open>tststr \<equiv> ''aba''\<close>

sepref_definition tststr_impl is \<open>uncurry0 (RETURN tststr)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a strl_assn'\<close>
  unfolding tststr_def
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply sepref_dbg_side_unfold
  oops

sepref_definition strl_lt_test is \<open>uncurry (RETURN oo list_lt)\<close>
  :: \<open>strl_assn'\<^sup>k *\<^sub>a strl_assn'\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

sepref_definition strl_le_test is \<open>uncurry (RETURN oo list_le)\<close>
  :: \<open>strl_assn'\<^sup>k *\<^sub>a strl_assn'\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

sepref_register \<open>(=) :: char list \<Rightarrow> char list \<Rightarrow> bool\<close>

sepref_definition strl_eq_test is \<open>uncurry (RETURN oo (=))\<close>
  :: \<open>strl_assn'\<^sup>k *\<^sub>a strl_assn'\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

sepref_definition strl_copy_test is \<open>RETURN o COPY\<close>
  :: \<open>strl_assn'\<^sup>k \<rightarrow>\<^sub>a strl_assn'\<close>
  by sepref

definition prependtest :: \<open>char \<Rightarrow> char list \<Rightarrow> char list\<close> where
  \<open>prependtest c ss = c # ss\<close>

sepref_definition prependtest_impl is \<open>uncurry (RETURN oo prependtest)\<close>
  :: \<open>char_assn\<^sup>k *\<^sub>a strl_assn'\<^sup>d \<rightarrow>\<^sub>a strl_assn'\<close>
  unfolding prependtest_def 
  by sepref

end

section \<open>String by Array\<close>
definition \<open>stra_assn \<equiv> larray_assn char_assn\<close>
(* Deferred for now *)

(* This is copied from copying list... *)
(* TODO: Should probably live in it's own theory?
 * Monoms might want this stuff aswell... *)
locale copy_free_larray =
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
end

experiment
begin

definition \<open>tststr \<equiv> ''aba''\<close>

sepref_definition tststr_impl is \<open>uncurry0 (RETURN tststr)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a stra_assn'\<close>
  unfolding tststr_def
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply sepref_dbg_side_unfold
  oops

sepref_definition strl_lt_test is \<open>uncurry (RETURN oo list_lt)\<close>
  :: \<open>stra_assn\<^sup>k *\<^sub>a stra_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  apply sepref_dbg_keep
  oops

sepref_definition strl_le_test is \<open>uncurry (RETURN oo list_le)\<close>
  :: \<open>stra_assn\<^sup>k *\<^sub>a stra_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  apply sepref_dbg_keep
  oops

sepref_register \<open>(=) :: char list \<Rightarrow> char list \<Rightarrow> bool\<close>

sepref_definition strl_eq_test is \<open>uncurry (RETURN oo (=))\<close>
  :: \<open>stra_assn\<^sup>k *\<^sub>a stra_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  apply sepref_dbg_keep
  oops

sepref_definition strl_copy_test is \<open>RETURN o COPY\<close>
  :: \<open>stra_assn\<^sup>k \<rightarrow>\<^sub>a stra_assn\<close>
  apply sepref_dbg_keep
  oops

end

end
