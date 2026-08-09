theory LLVM_ASCII_String
  imports LLVM_String BigInt_LLVM.LLVM_CodeGen_Signed
begin

text \<open>This theory defines the relation between ascii strings in LLVM (lists of 8-bit words)
  and numbers (natural numbers and integers).\<close>

section \<open>High-Level ASCII Semantics\<close>

text \<open>Note that correctness of the sbi \<rightarrow> string and string \<rightarrow> sbi conversion is relative
  to the string \<leftrightarrow> int relation established here.\<close>

subsection \<open>@{typ nat} by @{typ string}}\<close>

definition is_ascii_unum :: \<open>char \<Rightarrow> bool\<close> where
  \<open>is_ascii_unum c \<equiv> 48 \<le> (of_char :: char \<Rightarrow> nat) c \<and> (of_char :: char \<Rightarrow> nat) c \<le> 57\<close>

definition char_uval :: \<open>char \<Rightarrow> nat\<close> where
  \<open>char_uval c = (of_char c) - 48\<close>

definition \<open>ascii_char_nat_rel \<equiv> br char_uval is_ascii_unum\<close>

definition is_ascii_unum_str :: \<open>string \<Rightarrow> bool\<close> where
  \<open>is_ascii_unum_str ss \<equiv> ss \<noteq> [] \<and> foldl (\<lambda>acc d. acc \<and> is_ascii_unum d) True ss\<close>

definition str_uval :: \<open>string \<Rightarrow> nat\<close> where
  \<open>str_uval cs \<equiv> foldl (\<lambda>acc c. 10 * acc + char_uval c) 0 cs\<close>

definition \<open>ascii_str_nat_rel \<equiv> br str_uval is_ascii_unum_str\<close>

subsection \<open>@{typ int} by @{typ string}}\<close>

definition \<open>ascii_hyphen \<equiv> (hd ''-'')\<close>

definition is_ascii_snum_str :: \<open>string \<Rightarrow> bool\<close> where
  \<open>is_ascii_snum_str cs \<equiv> is_ascii_unum_str cs \<or> hd cs = ascii_hyphen \<and> is_ascii_unum_str (tl cs)\<close>

definition str_sval :: \<open>string \<Rightarrow> int\<close> where
  \<open>str_sval cs \<equiv> if hd cs = ascii_hyphen then - int (str_uval (tl cs)) else int (str_uval cs)\<close>

definition \<open>ascii_str_int_rel \<equiv> br str_sval is_ascii_snum_str\<close>

section \<open>Conversion from @{typ string} to @{typ int}\<close>

subsection \<open>The constant 10 at \<open>sbi_assn\<close>\<close>

definition int10 :: int where \<open>int10 \<equiv> 10\<close>

definition signed_big_int10 :: signed_big_int where
  \<open>signed_big_int10 \<equiv> ([10], False)\<close>

lemma signed_big_int10_\<alpha>: \<open>signed_big_int_to_int ([10], False) = 10\<close>
  by eval

lemma signed_big_int10_refine: \<open>(signed_big_int10, int10) \<in> signed_big_int_rel\<close>
  by (auto simp: signed_big_int10_def int10_def signed_big_int_rel_def in_br_conv
      signed_big_int10_\<alpha> signed_big_int_invar_def \<sigma>_def limbs_of_def)

lemma signed_big_int10_alt: \<open>signed_big_int10 = (op_al_empty TYPE(size_t) @ [10], False)\<close>
  by (simp add: signed_big_int10_def)

sepref_def signed_big_int10_impl is \<open>uncurry0 (RETURN signed_big_int10)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a sbi_aux_assn\<close>
  unfolding signed_big_int10_alt
  by sepref

sepref_register int10

context notes [fcomp_norm_unfold] = sbi_assn_def[symmetric] begin
lemmas signed_big_int10_hnr[sepref_fr_rules] =
  signed_big_int10_impl.refine[FCOMP signed_big_int10_refine]
end

subsection \<open>Full Refinement\<close>
text \<open>We don't implment conversion into nat, since for @{term bi_assn}, multiplication is not registered.\<close>

text \<open>Using our fold implementation of copying lists, refinement is straight forward.\<close>

definition str_uvals_inner :: \<open>int \<Rightarrow> char \<Rightarrow> int\<close> where
  \<open>str_uvals_inner \<equiv> \<lambda>acc c. 10 * acc + int (char_uval c)\<close>

definition str_uvals_outer :: \<open>int \<Rightarrow> string \<Rightarrow> int\<close> where
  \<open>str_uvals_outer \<equiv> foldl str_uvals_inner\<close>

definition str_uvals_outer' :: \<open>string \<Rightarrow> int\<close> where
  \<open>str_uvals_outer' \<equiv> str_uvals_outer 0\<close>

lemma foldl_uval_int_nat:
  \<open>foldl (\<lambda>acc c. 10 * acc + int (char_uval c)) (int n) cs
     = int (foldl (\<lambda>acc c. 10 * acc + char_uval c) n cs)\<close>
  apply (induction cs arbitrary: n; auto)
  by (metis (lifting) Abs_fnat_hom_add int_ops(3) of_nat_mult)

lemma str_uvals_correct: \<open>str_uvals_outer' cs = int (str_uval cs)\<close>
  unfolding str_uval_def str_uvals_outer'_def str_uvals_outer_def str_uvals_inner_def
  by (metis foldl_uval_int_nat int_ops(1))

context begin
interpretation llvm_prim_arith_setup .
lemma ll_sub8_rule: \<open>llvm_htriple \<box> (ll_sub (a::8 word) b) (\<lambda>r. \<up>(r = a - b))\<close>
  by vcg
lemma ll_zext_8_64_rule:
  \<open>llvm_htriple \<box> (ll_zext (c::8 word) TYPE(64 word)) (\<lambda>r. \<up>(r = UCAST(8 \<rightarrow> 64) c))\<close>
  supply [simp] = is_up'
  by vcg
end

definition char_uval_impl :: \<open>8 word \<Rightarrow> 64 word llM\<close> where
  \<open>char_uval_impl xi \<equiv> doM { d \<leftarrow> ll_sub xi 0x30; ll_zext d TYPE(64 word) }\<close>

lemma char_uval_snat_aux:
  assumes \<open>48 \<le> unat (xi::8 word)\<close>
  shows \<open>(UCAST(8 \<rightarrow> 64) (xi - 0x30), unat xi - 48) \<in> snat_rel' TYPE(64)\<close>
proof -
  have [simp]: \<open>unat (UCAST(8 \<rightarrow> 64) (xi - 0x30)) = unat (xi - 0x30)\<close>
    by (simp add: unat_ucast_upcast is_up')
  have inv: \<open>snat_invar (UCAST(8 \<rightarrow> 64) (xi - 0x30))\<close>
    using unat_lt2p[of \<open>xi - 0x30\<close>]
    by (simp add: snat_invar_def msb_unat_big)
  have val: \<open>unat (xi - 0x30) = unat xi - 48\<close>
    using assms by (simp add: unat_sub word_le_nat_alt)
  show ?thesis
    using inv val
    by (simp add: snat_rel_def snat.rel_def in_br_conv snat_eq_unat_aux2)
qed

sepref_register char_uval
lemma char_uval_hnr[sepref_fr_rules]:
  \<open>(char_uval_impl, RETURN \<circ> char_uval)
     \<in> [is_ascii_unum]\<^sub>a char_assn\<^sup>k \<rightarrow> snat_assn' TYPE(64)\<close>
  unfolding char_uval_impl_def char_uval_def
  apply sepref_to_hoare
  supply [vcg_rules] = ll_sub8_rule ll_zext_8_64_rule
  apply vcg
  by (auto simp: is_ascii_unum_def sep_algebra_simps  in_br_conv
      char_rel_def char_assn_def char_of_word_def
      pure_def ENTAILS_def entails_def unat_of_char_mod
      intro: char_uval_snat_aux)

sepref_def str_uvals_inner_impl is \<open>uncurry (RETURN oo str_uvals_inner)\<close>
  :: \<open>[\<lambda>(_, c). is_ascii_unum c]\<^sub>a sbi_assn\<^sup>k *\<^sub>a char_assn\<^sup>k \<rightarrow> sbi_assn\<close>
  unfolding str_uvals_inner_def int10_def[symmetric]
  by sepref

definition str_uvals_inner_dimpl where
  \<open>str_uvals_inner_dimpl ai ci \<equiv> doM { r \<leftarrow> str_uvals_inner_impl ai ci; sbi_free ai; Mreturn r }\<close>

lemma str_uvals_inner_dimpl_refine:
  \<open>(uncurry str_uvals_inner_dimpl, uncurry (RETURN oo str_uvals_inner))
     \<in> [\<lambda>(_, c). is_ascii_unum c]\<^sub>a sbi_assn\<^sup>d *\<^sub>a char_assn\<^sup>k \<rightarrow> sbi_assn\<close>
  unfolding str_uvals_inner_dimpl_def
  apply sepref_to_hoare
  supply [vcg_rules] = hfref_htriple_k1_k2_guard[OF str_uvals_inner_impl.refine]
    sbi_free_rule[THEN MK_FREED]
  apply vcg
  done

lemmas str_uvals_fold_hnr = cl_fold_hfref_guard[OF str_uvals_inner_dimpl_refine]

definition str_uvals_outer_impl where
  \<open>str_uvals_outer_impl \<equiv> cl_fold' str_uvals_inner_dimpl\<close>

sepref_register str_uvals_outer

lemma str_uvals_outer_hnr[sepref_fr_rules]:
  \<open>(uncurry str_uvals_outer_impl, uncurry (RETURN oo str_uvals_outer))
     \<in> [\<lambda>(_, cs). \<forall>c\<in>set cs. is_ascii_unum c]\<^sub>a sbi_assn\<^sup>d *\<^sub>a strl_assn'\<^sup>k \<rightarrow> sbi_assn\<close>
  using str_uvals_fold_hnr
  unfolding str_uvals_outer_def str_uvals_outer_impl_def .

sepref_def str_uvals_outer'_impl is \<open>RETURN o str_uvals_outer'\<close>
  :: \<open>[\<lambda>cs. \<forall>c\<in>set cs. is_ascii_unum c]\<^sub>a strl_assn'\<^sup>k \<rightarrow> sbi_assn\<close>
  unfolding str_uvals_outer'_def
  by sepref

subsection \<open>Predicate bridge lemmas\<close>

lemma foldl_conj_Ball: \<open>foldl (\<lambda>acc d. acc \<and> P d) b xs \<longleftrightarrow> b \<and> (\<forall>x\<in>set xs. P x)\<close>
  by (induction xs arbitrary: b) auto

lemma is_ascii_unum_str_alt:
  \<open>is_ascii_unum_str cs \<longleftrightarrow> cs \<noteq> [] \<and> (\<forall>c\<in>set cs. is_ascii_unum c)\<close>
  by (auto simp: is_ascii_unum_str_def foldl_conj_Ball)

lemma is_ascii_unum_hyphen[simp]: \<open>\<not> is_ascii_unum ascii_hyphen\<close>
  by (simp add: is_ascii_unum_def ascii_hyphen_def)

lemma is_ascii_snum_str_nempty: \<open>is_ascii_snum_str cs \<Longrightarrow> cs \<noteq> []\<close>
  by (auto simp: is_ascii_snum_str_def is_ascii_unum_str_alt)

lemma is_ascii_snum_str_hyphen:
  \<open>is_ascii_snum_str cs \<Longrightarrow> hd cs = ascii_hyphen \<Longrightarrow> \<forall>c\<in>set (tl cs). is_ascii_unum c\<close>
  by (cases cs) (auto simp: is_ascii_snum_str_def is_ascii_unum_str_alt)

lemma is_ascii_snum_str_no_hyphen:
  \<open>is_ascii_snum_str cs \<Longrightarrow> hd cs \<noteq> ascii_hyphen \<Longrightarrow> \<forall>c\<in>set cs. is_ascii_unum c\<close>
  by (auto simp: is_ascii_snum_str_def is_ascii_unum_str_alt)

subsection \<open>The signed conversion\<close>

definition str_sval_nres :: \<open>string \<Rightarrow> int nres\<close> where
  \<open>str_sval_nres cs \<equiv> doN {
    ASSERT (cs\<noteq>[]);
    (c,cs) \<leftarrow> mop_list_pop_hd cs;
    if c=ascii_hyphen then doN {
      ASSERT (\<forall>x\<in>set cs. is_ascii_unum x);
      let v = str_uvals_outer' cs;
      RETURN (-v)
    } else doN {
      cs \<leftarrow> RETURN (c#cs);
      ASSERT (\<forall>x\<in>set cs. is_ascii_unum x);
      let v = str_uvals_outer' cs;
      RETURN v
    }
  }\<close>

lemma str_sval_nres_correct:
  \<open>is_ascii_snum_str cs \<Longrightarrow> str_sval_nres cs \<le> RETURN (str_sval cs)\<close>
  unfolding str_sval_nres_def
  apply refine_vcg
  apply (auto simp: str_sval_def str_uvals_correct is_ascii_snum_str_nempty
      dest: is_ascii_snum_str_hyphen is_ascii_snum_str_no_hyphen)
  apply (auto simp: is_ascii_snum_str_def is_ascii_unum_str_alt neq_Nil_conv)
  done

lemma ascii_hyphen_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 45), uncurry0 (RETURN ascii_hyphen))
  \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  unfolding ascii_hyphen_def hd_def
  apply sepref_to_hoare
  apply vcg
  by (auto simp: sep_algebra_simps ENTAILS_def entails_def char_assn_def pure_def
    char_rel_def in_br_conv char_of_word_def char_of_def bit_Suc_0_iff)

sepref_register str_uvals_outer'

sepref_def str_sval_impl is \<open>str_sval_nres\<close>
  :: \<open>[is_ascii_snum_str]\<^sub>a strl_assn'\<^sup>d \<rightarrow> sbi_assn\<close>
  unfolding str_sval_nres_def
  by sepref

subsection \<open>Composition with the high-level conversion\<close>

lemma str_sval_nres_refine:
  \<open>(str_sval_nres, RETURN o str_sval)
     \<in> [is_ascii_snum_str]\<^sub>f \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>int_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: str_sval_nres_correct)

lemmas str_sval_hnr = str_sval_impl.refine[FCOMP str_sval_nres_refine]

definition str_int_assn where
  \<open>str_int_assn \<equiv> hr_comp strl_assn' ascii_str_int_rel\<close>

lemma str_sval_id_refine:
  \<open>(RETURN o str_sval, RETURN o id) \<in> [\<lambda>_. True]\<^sub>f ascii_str_int_rel \<rightarrow> \<langle>int_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: ascii_str_int_rel_def in_br_conv)

lemma ascii_str_int_relD[fcomp_prenorm_simps]:
  \<open>(cs, n) \<in> ascii_str_int_rel \<Longrightarrow> is_ascii_snum_str cs\<close>
  by (simp add: ascii_str_int_rel_def in_br_conv)

text \<open>This is overall correctness lemma for our string \<rightarrow> sbi converstion,
  allowing for (partially) verified parsing.\<close>
context notes [fcomp_norm_unfold] = str_int_assn_def[symmetric] begin
lemmas str_int_conv_hnr = str_sval_hnr[FCOMP str_sval_id_refine]
end

end
