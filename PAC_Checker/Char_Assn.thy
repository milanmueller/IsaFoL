theory Char_Assn 
  imports Isabelle_LLVM.IICF PAC_Polynomials_Term
begin

text \<open>We need to tell sepref how to relate @{typ \<open>char\<close>} and @{typ \<open>8 word\<close>}\<close>

definition char_of_word :: \<open>8 word \<Rightarrow> char\<close> where
  \<open>char_of_word \<equiv> char_of \<circ> unat\<close>

definition char_rel :: \<open>(8 word \<times> char) set\<close> where
  \<open>char_rel \<equiv> br char_of_word (\<lambda>_. True)\<close>

definition \<open>char_assn \<equiv> pure char_rel\<close>
lemma char_assn_pure: \<open>is_pure char_assn\<close> unfolding char_assn_def by simp (* nice to know *)

interpretation char_word: standard_opr_abstraction
  "char_of_word :: 8 word \<Rightarrow> char"
  "(\<lambda>_. True)"
  "(\<lambda>_ _ _. True)"
  "(\<lambda>_ _ _ _. True)"
  "(\<lambda>_ _. True)"
  by standard simp

lemma unat_of_char_mod: \<open>unat (a :: 8 word) mod 256 = unat a\<close>
proof -
  have \<open>unat a < 256\<close>
    by (rule less_le_trans[OF unat_lt2p]) simp
  then show ?thesis
    by simp
qed

lemma char_eq_is_cmp_op: "char_word.is_cmp_op ll_icmp_eq (=) (=)"
  apply (rule char_word.is_cmp_opI)
  unfolding ll_icmp_eq_def op_lift_cmp_def char_of_word_def
  apply (simp add: from_bool_lint_conv word_to_lint_eq)
  using unat_of_char_mod by auto

lemma char_ne_is_cmp_op: \<open>char_word.is_cmp_op ll_icmp_ne (\<noteq>) (\<noteq>)\<close>
  apply (rule char_word.is_cmp_opI)
  unfolding ll_icmp_ne_def op_lift_cmp_def char_of_word_def
  apply (simp add: from_bool_lint_conv word_to_lint_eq)
  using unat_of_char_mod by auto

instantiation char :: linorder
begin
  definition less_char where [symmetric, simp]: "less_char = PAC_Polynomials_Term.less_char"
  definition less_eq_char where [symmetric, simp]: "less_eq_char = PAC_Polynomials_Term.less_eq_char"
instance
  apply standard
  using char.linorder_axioms
  by (auto simp: class.linorder_def class.order_def class.preorder_def
       less_eq_char_def less_than_char_def class.order_axioms_def
       class.linorder_axioms_def p2rel_def less_char_def)
end

lemma char_lt_is_cmp_op: "char_word.is_cmp_op ll_icmp_ult (<) (<)"
  apply (rule char_word.is_cmp_opI)
  unfolding ll_icmp_ult_def op_lift_cmp_def char_of_word_def
  apply (simp add: from_bool_lint_conv word_to_lint_ult)
  using unat_of_char_mod
  by (auto simp: word_less_nat_alt PAC_Polynomials_Term.less_char_def 
           simp flip: less_char_def) 

lemma char_le_is_cmp_op: "char_word.is_cmp_op ll_icmp_ule (\<le>) (\<le>)"
  apply (rule char_word.is_cmp_opI)
  unfolding ll_icmp_ule_def op_lift_cmp_def char_of_word_def
  apply (simp add: from_bool_lint_conv word_to_lint_ule)
  using unat_of_char_mod 
  by (auto simp: word_le_nat_alt PAC_Polynomials_Term.less_eq_char_def 
           simp flip: less_eq_char_def)

sepref_register
  "(=) :: char \<Rightarrow> _"
  "(<) :: char \<Rightarrow> _"
  "(\<le>) :: char \<Rightarrow> _"

sepref_register op_neq_char: "op_neq :: char \<Rightarrow> _"

lemmas char_eq_hnr[sepref_fr_rules] =
  char_eq_is_cmp_op[THEN char_word.hn_cmp_op,
    unfolded char_word.assn_is_rel bool.assn_is_rel char_word.rel_def,
    folded bool1_rel_def char_rel_def char_assn_def]

lemmas char_ne_hnr[sepref_fr_rules] =
  char_ne_is_cmp_op[THEN char_word.hn_cmp_op,
    unfolded char_word.assn_is_rel bool.assn_is_rel char_word.rel_def,
    folded bool1_rel_def op_neq_def char_rel_def char_assn_def]

lemmas char_lt_hnr[sepref_fr_rules] =
  char_lt_is_cmp_op[THEN char_word.hn_cmp_op,
    unfolded char_word.assn_is_rel bool.assn_is_rel char_word.rel_def,
    folded bool1_rel_def char_rel_def char_assn_def char_rel_def]

lemmas char_le_hnr[sepref_fr_rules] =
  char_le_is_cmp_op[THEN char_word.hn_cmp_op,
    unfolded char_word.assn_is_rel bool.assn_is_rel char_word.rel_def,
    folded bool1_rel_def char_rel_def char_assn_def]

lemma char_of_word_hnr[sepref_fr_rules]:
  \<open>(Mreturn, RETURN o char_of_word) \<in> (hn_val word_rel)\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  unfolding char_assn_def 
  apply (intro hfrefI hn_refineI; vcg)
  apply (auto simp: in_br_conv ENTAILS_def entails_def char_rel_def char_of_word_def sep_algebra_simps br_def)
  by (smt (verit, best) Misc.IdD case_prodI fri_basic_extract_simps(1) import_param_3(2) mem_Collect_eq pure_app_eq)

lemma char_assn_mk_free[sepref_frame_free_rules]:
  \<open>MK_FREE char_assn (\<lambda>_. Mreturn ())\<close>
  unfolding char_assn_def
  by (rule mk_free_pure)

(* This is essentially just testing *)
sepref_definition char_eq_impl is \<open>uncurry (RETURN oo (=))\<close> 
  :: \<open>char_assn\<^sup>k *\<^sub>a char_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

sepref_definition char_ne_impl is \<open>uncurry (RETURN oo (\<noteq>))\<close> 
  :: \<open>char_assn\<^sup>k *\<^sub>a char_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

sepref_definition char_lt_impl is \<open>uncurry (RETURN oo (<))\<close> 
  :: \<open>char_assn\<^sup>k *\<^sub>a char_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

sepref_definition char_le_impl is \<open>uncurry (RETURN oo (\<le>))\<close> 
  :: \<open>char_assn\<^sup>k *\<^sub>a char_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

(*
definition ls_eq_nres :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> bool nres\<close> where
  \<open>ls_eq_nres xs ys = doN {
    if length xs \<noteq> length ys then RETURN False
    else doN {
      (_, eq) \<leftarrow> WHILEIT
        (\<lambda>(i, eq). i \<le> length xs \<and> (eq \<longleftrightarrow> (\<forall>j < i. xs ! j = ys ! j)))
        (\<lambda>(i, eq). eq \<and> i < length xs)
        (\<lambda>(i, _). doN {
          ASSERT (i < length xs);
          let x = xs!i;
          let y = ys!i;
          RETURN (i + 1, x = y)
        })
        (0, True);
      RETURN eq
    }
  }\<close>

lemma ls_eq_nres_correct: \<open>ls_eq_nres xs ys \<le> SPEC (\<lambda>r. r \<longleftrightarrow> xs = ys)\<close>
  unfolding ls_eq_nres_def
  apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(i,_). length xs - i)\<close>])
  apply clarsimp_all
  (* finish remaining subgoals *)
  sorry

definition str_eq_nres :: \<open>char list \<Rightarrow> char list \<Rightarrow> bool nres\<close> where
  \<open>str_eq_nres = ls_eq_nres\<close>

sepref_definition str_eq_impl is \<open>uncurry str_eq_nres\<close>
  :: \<open>string_assn\<^sup>k *\<^sub>a string_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding str_eq_nres_def ls_eq_nres_def
  apply (annot_snat_const size_t)
  by sepref

export_llvm str_eq_nres

definition lss_eq_nres :: \<open>'a list list \<Rightarrow> 'a list list \<Rightarrow> bool nres\<close> where
  \<open>lss_eq_nres xss yss = doN {
    if length xss \<noteq> length yss then RETURN False
    else if length xss = 0 then RETURN True
    else doN {
      xs0 \<leftarrow> mop_list_get xss 0;
      ys0 \<leftarrow> mop_list_get yss 0;
      (_, _, _, _, eq) \<leftarrow> WHILEIT
        (\<lambda>(i, j, xs, ys, eq). i \<le> length xss \<and>
            (i < length xss \<longrightarrow> xs = xss!i \<and> ys = yss!i \<and> j \<le> length xs \<and>
            (eq \<longleftrightarrow> length xs = length ys \<and> (\<forall>h < j. xs!h = ys!h))) \<and>
            (\<forall>k < i. xss!k = yss!k) \<and> (i = length xss \<longrightarrow> eq))
        (\<lambda>(i, _, _, _, eq). eq \<and> i < length xss)
        (\<lambda>(i, j, xs, ys, _). doN {
          if j < length xs then doN {
            ASSERT (j < length ys);
            RETURN (i, j + 1, xs, ys, xs!j = ys!j)
          } else doN {
            ASSERT (i < length xss);
            let i' = i + 1;
            if i' < length xss then doN {
              xs' \<leftarrow> mop_list_get xss i';
              ys' \<leftarrow> mop_list_get yss i';
              RETURN (i', 0, xs', ys', length xs' = length ys')
            } else RETURN (i', 0, xs, ys, True)
          }
        })
        (0, 0, xs0, ys0, length xs0 = length ys0);
      RETURN eq
    }
  }\<close>

lemma lss_eq_nres_correct: \<open>lss_eq_nres xss yss \<le> SPEC (\<lambda>r. r \<longleftrightarrow> xss = yss)\<close>
  unfolding lss_eq_nres_def
  apply (refine_vcg WHILEIT_rule[where R = \<open>inv_image (less_than <*lex*> less_than)
    (\<lambda>(i, j, xs :: 'a list, _, _). (length xss - i, length xs - j))\<close>])
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (auto; metis less_Suc_eq)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal
    apply (auto simp: less_Suc_eq)
    subgoal by (rule nth_equalityI; auto)
    subgoal by (rule nth_equalityI; auto)
    done
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal
    apply (auto simp: less_Suc_eq)
    by (rule nth_equalityI; auto)
  subgoal by auto
  subgoal by auto
  subgoal
    apply auto
    subgoal by (rule nth_equalityI; auto)
    subgoal by (rule nth_equalityI; auto)
    done
  done

definition strs_eq_nres :: \<open>char list list \<Rightarrow> char list list \<Rightarrow> bool nres\<close> where
  \<open>strs_eq_nres = lss_eq_nres\<close>

sepref_definition strs_eq_impl is \<open>uncurry strs_eq_nres\<close>
  :: \<open>monom_assn\<^sup>k *\<^sub>a monom_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding strs_eq_nres_def lss_eq_nres_def
  apply (annot_snat_const size_t)
  (*apply sepref_dbg_keep*)
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  oops (* `larray` will never be pure i think? *)
*)

end
