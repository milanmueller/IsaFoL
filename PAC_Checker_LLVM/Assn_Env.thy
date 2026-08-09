theory Assn_Env
  imports Isabelle_LLVM.IICF
begin

text \<open>This theory defines a hierarchy of locales on refinement assertions
  to avoid code duplication.\<close>

section \<open>Generic bridge from \<open>hfref\<close> rules to Hoare triples\<close>

text \<open>The locale assumptions below are refinement rules (\<open>hfref\<close>). 
  \<open>vgc\<close>, however, works with Hoare triples. Therefore we might want
  a translation of _hnr rules to vcg_rules\<close>

lemma hfref_htriple_k1:
  assumes R: \<open>(f, RETURN o g) \<in> A\<^sup>k \<rightarrow>\<^sub>a B\<close>
  shows \<open>llvm_htriple (A a ai) (f ai) (\<lambda>r. A a ai ** B (g a) r)\<close>
proof -
  note HNR = R[to_hnr, unfolded autoref_tag_defs]
  note HT = HNR[THEN hn_refineD]
  show ?thesis
    apply (rule htriple_ent_pre[OF _ htriple_ent_post[OF _ HT]])
    unfolding hn_ctxt_def
    apply (rule entails_refl)
    subgoal by (auto simp: entails_def sep_algebra_simps)
    subgoal by simp
    done
qed

lemma hfref_htriple_k2:
  assumes R: \<open>(uncurry f, uncurry (RETURN oo g)) \<in> A\<^sup>k *\<^sub>a B\<^sup>k \<rightarrow>\<^sub>a C\<close>
  shows \<open>llvm_htriple (A a ai ** B b bi) (f ai bi) (\<lambda>r. A a ai ** B b bi ** C (g a b) r)\<close>
proof -
  note HNR = R[to_hnr, unfolded autoref_tag_defs]
  note HT = HNR[THEN hn_refineD]
  show ?thesis
    apply (rule htriple_ent_pre[OF _ htriple_ent_post[OF _ HT]])
    unfolding hn_ctxt_def
    apply (rule entails_refl)
    subgoal by (auto simp: entails_def sep_algebra_simps)
    subgoal by simp
    done
qed

lemma hfref_htriple_k3:
  assumes R: \<open>(uncurry2 f, uncurry2 (RETURN ooo g)) \<in> A\<^sup>k *\<^sub>a B\<^sup>k *\<^sub>a C\<^sup>k \<rightarrow>\<^sub>a D\<close>
  shows \<open>llvm_htriple (A a ai ** B b bi ** C c ci) (f ai bi ci)
           (\<lambda>r. A a ai ** B b bi ** C c ci ** D (g a b c) r)\<close>
proof -
  note HNR = R[to_hnr, unfolded autoref_tag_defs]
  note HT = HNR[THEN hn_refineD]
  show ?thesis
    apply (rule htriple_ent_pre[OF _ htriple_ent_post[OF _ HT]])
    unfolding hn_ctxt_def
    apply (rule entails_refl)
    subgoal by (auto simp: entails_def sep_algebra_simps pred_lift_extract_simps
      sep_conj_exists pw_le_iff refine_pw_simps)
    subgoal by simp
    done
qed

lemma hfref_htriple_d1_k2:
  assumes R: \<open>(uncurry f, uncurry (RETURN oo g)) \<in> A\<^sup>d *\<^sub>a B\<^sup>k \<rightarrow>\<^sub>a C\<close>
  shows \<open>llvm_htriple (A a ai ** B b bi) (f ai bi) (\<lambda>r. B b bi ** C (g a b) r)\<close>
proof -
  note HNR = R[to_hnr, unfolded autoref_tag_defs]
  note HT = HNR[THEN hn_refineD]
  show ?thesis
    apply (rule htriple_ent_pre[OF _ htriple_ent_post[OF _ HT]])
    unfolding hn_ctxt_def
    apply (rule entails_refl)
    subgoal
      apply (auto simp: entails_def sep_algebra_simps)
      by (simp add: invalid_assn_def pred_lift_extract_simps(2))
    subgoal by simp
    done
qed

lemma hfref_htriple_k1_d2_k3:
  assumes R: \<open>(uncurry2 f, uncurry2 (RETURN ooo g)) \<in> A\<^sup>k *\<^sub>a B\<^sup>d *\<^sub>a C\<^sup>k \<rightarrow>\<^sub>a D\<close>
  shows \<open>llvm_htriple (A a ai ** B b bi ** C c ci) (f ai bi ci)
           (\<lambda>r. A a ai ** D (g a b c) r ** C c ci)\<close>
proof -
  note HNR = R[to_hnr, unfolded autoref_tag_defs]
  note HT = HNR[THEN hn_refineD]
  show ?thesis
    apply (rule htriple_ent_pre[OF _ htriple_ent_post[OF _ HT]])
    unfolding hn_ctxt_def
    apply (rule entails_refl)
    subgoal
      apply (auto simp: entails_def sep_algebra_simps pred_lift_extract_simps
        sep_conj_exists pw_le_iff refine_pw_simps)
      by (simp add: invalid_assn_def pred_lift_extract_simps(2) sep_algebra_simps
        sep_conj_aci)
    subgoal by simp
    done
qed

section \<open>Copying\<close>

(* Copying setup is taken from the sorting examples in Isabelle-LLVM *)

definition \<open>is_copy A cp \<equiv> (cp, RETURN o COPY) \<in> A\<^sup>k \<rightarrow>\<^sub>a A\<close>

lemma is_copy_hnr[sepref_fr_rules]:
  \<open>GEN_ALGO cp (is_copy A) \<Longrightarrow> (cp, RETURN o COPY) \<in> A\<^sup>k \<rightarrow>\<^sub>a A\<close>
  unfolding is_copy_def GEN_ALGO_def by auto

lemma is_copy_pure_gen_algo: \<open>CONSTRAINT is_pure A \<Longrightarrow> GEN_ALGO Mreturn (is_copy A)\<close>
  unfolding is_copy_def GEN_ALGO_def
  by (rule hnr_pure_COPY)

section \<open>The locale hierarchy\<close>

subsection \<open>Freeable assertions\<close>

locale freeable_assn =
  fixes A :: \<open>'a \<Rightarrow> 'b::llvm_rep \<Rightarrow> assn\<close>
    and afree :: \<open>'b \<Rightarrow> unit llM\<close>
  assumes afree_free[sepref_frame_free_rules]: \<open>MK_FREE A afree\<close>
begin

lemma afree_rule[vcg_rules]: \<open>llvm_htriple (A a c) (afree c) (\<lambda>_. \<box>)\<close>
  by (rule MK_FREED[OF afree_free])

end

subsection \<open>Copyable assertions\<close>

locale copyable_assn = freeable_assn +
  fixes acopy :: \<open>'b::llvm_rep \<Rightarrow> 'b llM\<close>
  assumes acopy_hnr[sepref_fr_rules]: \<open>(acopy, RETURN o COPY) \<in> A\<^sup>k \<rightarrow>\<^sub>a A\<close>
begin

lemma acopy_is_copy: \<open>is_copy A acopy\<close>
  unfolding is_copy_def by (rule acopy_hnr)

lemma acopy_gen_algo[sepref_gen_algo_rules]: \<open>GEN_ALGO acopy (is_copy A)\<close>
  unfolding GEN_ALGO_def by (rule acopy_is_copy)

lemma acopy_rule[vcg_rules]: \<open>llvm_htriple (A a c) (acopy c) (\<lambda>r. A a c ** A a r)\<close>
  using hfref_htriple_k1[OF acopy_hnr] by simp

end

subsection \<open>Assertions with an equality test\<close>

locale eq_assn =
  fixes A :: \<open>'a \<Rightarrow> 'b::llvm_rep \<Rightarrow> assn\<close>
    and aeq :: \<open>'b \<Rightarrow> 'b \<Rightarrow> 1 word llM\<close>
  assumes aeq_hnr[sepref_fr_rules]:
      \<open>(uncurry aeq, uncurry (RETURN oo (=))) \<in> A\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
begin

lemma aeq_rule[vcg_rules]:
  \<open>llvm_htriple (A a ai ** A b bi) (aeq ai bi) (\<lambda>r. A a ai ** A b bi ** bool1_assn (a = b) r)\<close>
  by (rule hfref_htriple_k2[OF aeq_hnr])

end

subsection \<open>Linearly ordered assertions\<close>

locale linorder_assn = eq_assn A aeq
  for A :: \<open>'a::linorder \<Rightarrow> 'b::llvm_rep \<Rightarrow> assn\<close>
  and aeq :: \<open>'b \<Rightarrow> 'b \<Rightarrow> 1 word llM\<close> +
  fixes alt :: \<open>'b \<Rightarrow> 'b \<Rightarrow> 1 word llM\<close>
  assumes alt_hnr[sepref_fr_rules]:
      \<open>(uncurry alt, uncurry (RETURN oo (<))) \<in> A\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
begin

lemma alt_rule[vcg_rules]:
  \<open>llvm_htriple (A a ai ** A b bi) (alt ai bi) (\<lambda>r. A a ai ** A b bi ** bool1_assn (a < b) r)\<close>
  by (rule hfref_htriple_k2[OF alt_hnr])

end

subsection \<open>Combination: copyable and linearly ordered\<close>

locale linorder_copyable_assn =
  copyable_assn A afree acopy + linorder_assn A aeq alt
  for A :: \<open>'a::linorder \<Rightarrow> 'b::llvm_rep \<Rightarrow> assn\<close>
  and afree :: \<open>'b \<Rightarrow> unit llM\<close>
  and acopy :: \<open>'b \<Rightarrow> 'b llM\<close>
  and aeq alt :: \<open>'b \<Rightarrow> 'b \<Rightarrow> 1 word llM\<close>

subsection \<open>Hashable assertions\<close>

locale hashable_assn =
  fixes A :: \<open>'a \<Rightarrow> 'b::llvm_rep \<Rightarrow> assn\<close>
    and ahash :: \<open>'a \<Rightarrow> 64 word\<close>
    and ahash_impl :: \<open>'b \<Rightarrow> 64 word llM\<close>
  assumes Ahash_hnr[sepref_fr_rules]:
    \<open>(ahash_impl, RETURN o ahash) \<in> A\<^sup>k \<rightarrow>\<^sub>a word_assn' TYPE(64)\<close>
begin

lemma Ahash_rule[vcg_rules]:
  \<open>llvm_htriple (A a ai) (ahash_impl ai) (\<lambda>r. A a ai ** word_assn' TYPE(64) (ahash a) r)\<close>
  by (rule hfref_htriple_k1[OF Ahash_hnr])

end

section \<open>Regression tests\<close>

text \<open>Instantiate the hierarchy with 64-bit \<open>snat\<close> numbers (a pure assertion, so
  free is a no-op and copy is \<open>Mreturn\<close>) to validate that the assumptions are
  dischargeable and that the diamond in \<open>linorder_copyable_assn\<close> merges.\<close>

experiment
begin

interpretation P: copyable_assn \<open>snat_assn' TYPE(64)\<close> \<open>\<lambda>_. Mreturn ()\<close> Mreturn
  apply unfold_locales
  subgoal by (rule mk_free_pure)
  subgoal by (rule hnr_pure_COPY) simp
  done

interpretation N: linorder_assn \<open>snat_assn' TYPE(64)\<close> ll_icmp_eq ll_icmp_slt
  apply unfold_locales
  subgoal by (rule hn_snat_ops(7))
  subgoal by (rule hn_snat_ops(10))
  done

end

text \<open>The combined locale, interpreted in a fresh context (with \<open>copyable_assn\<close> or
  \<open>linorder_assn\<close> already interpreted at the same parameters, \<open>interpretation\<close> only
  generates obligations for the parts that are new).\<close>

experiment
begin

interpretation NP: linorder_copyable_assn
  \<open>snat_assn' TYPE(64)\<close> \<open>\<lambda>_. Mreturn ()\<close> Mreturn ll_icmp_eq ll_icmp_slt
  apply unfold_locales
  subgoal by (rule mk_free_pure)
  subgoal by (rule hnr_pure_COPY) simp
  subgoal by (rule hn_snat_ops(7))
  subgoal by (rule hn_snat_ops(10))
  done

end

experiment
begin

interpretation E: eq_assn \<open>snat_assn' TYPE(64)\<close> ll_icmp_eq
  by unfold_locales (rule hn_snat_ops(7))

interpretation L: linorder_assn \<open>snat_assn' TYPE(64)\<close> ll_icmp_eq ll_icmp_slt
  by unfold_locales (rule hn_snat_ops(10))

end

end
