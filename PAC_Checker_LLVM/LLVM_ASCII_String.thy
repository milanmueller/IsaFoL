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

lemma ascii_char_nat_rel_sanity_check:
  \<open>(hd ''0'',0) \<in> ascii_char_nat_rel\<close> \<open>(hd ''1'',1) \<in> ascii_char_nat_rel\<close>
  \<open>(hd ''2'',2) \<in> ascii_char_nat_rel\<close> \<open>(hd ''3'',3) \<in> ascii_char_nat_rel\<close>
  \<open>(hd ''4'',4) \<in> ascii_char_nat_rel\<close> \<open>(hd ''5'',5) \<in> ascii_char_nat_rel\<close>
  \<open>(hd ''6'',6) \<in> ascii_char_nat_rel\<close> \<open>(hd ''7'',7) \<in> ascii_char_nat_rel\<close>
  \<open>(hd ''8'',8) \<in> ascii_char_nat_rel\<close> \<open>(hd ''9'',9) \<in> ascii_char_nat_rel\<close>
  unfolding ascii_char_nat_rel_def char_uval_def is_ascii_unum_def in_br_conv by auto

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
      char_rel_def char_of_word_def char_of_word_in_char_rel
      pure_def ENTAILS_def entails_def unat_of_char_mod char_nat_rel_def
      char_of_nat_invar_def char_of_nat_def unat_rel_def unat.rel_def
      intro: char_uval_snat_aux)

sepref_def str_uvals_inner_impl is \<open>uncurry (RETURN oo str_uvals_inner)\<close>
  :: \<open>[\<lambda>(_, c). is_ascii_unum c]\<^sub>a sbi_assn\<^sup>k *\<^sub>a char_assn\<^sup>k \<rightarrow> sbi_assn\<close>
  unfolding str_uvals_inner_def int10_def[symmetric]
  by sepref

definition str_uvals_inner_dimpl where
  \<open>str_uvals_inner_dimpl ai ci \<equiv> doM { r \<leftarrow> str_uvals_inner_impl ai ci; sbi_free ai; Mreturn r }\<close>

lemma str_uvals_inner_impl_rule:
  assumes \<open>(bi, b) \<in> char_rel\<close> and \<open>is_ascii_unum b\<close>
  shows \<open>llvm_htriple (sbi_assn a ai) (str_uvals_inner_impl ai bi)
           (\<lambda>r. sbi_assn a ai ** sbi_assn (str_uvals_inner a b) r)\<close>
proof -
  have PRE: \<open>(\<lambda>(_, c). is_ascii_unum c) (a, b)\<close> using assms by simp
  note HT = hfref_htriple_k1_k2_guard[OF str_uvals_inner_impl.refine PRE]
  show ?thesis
    using HT[of ai bi] assms
    by (simp add: pure_app_eq pure_true_conv sep_algebra_simps)
qed

lemma str_uvals_inner_dimpl_refine:
  \<open>(uncurry str_uvals_inner_dimpl, uncurry (RETURN oo str_uvals_inner))
     \<in> [\<lambda>(_, c). is_ascii_unum c]\<^sub>a sbi_assn\<^sup>d *\<^sub>a char_assn\<^sup>k \<rightarrow> sbi_assn\<close>
  unfolding str_uvals_inner_dimpl_def
  apply sepref_to_hoare
  supply [vcg_rules] = str_uvals_inner_impl_rule
    sbi_free_rule[THEN MK_FREED]
  apply vcg
  apply assumption
  apply assumption
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

sepref_def ascii_hyphen_impl is \<open>uncurry0 (RETURN ascii_hyphen)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  unfolding ascii_hyphen_def
  by sepref

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
lemmas str_int_conv_hnr = str_sval_hnr[FCOMP str_sval_id_refine]

section \<open>Conversion from @{typ int} to @{typ string}\<close>

text \<open>Converting an nat to a string is done by simply collecting digits\<close>

fun digits_of_nat :: \<open>nat \<Rightarrow> nat list\<close> where
  \<open>digits_of_nat n = (if n < 10 then [n] else digits_of_nat (n div 10) @ [n mod 10])\<close>

lemma digits_of_nat_correct: \<open>n = foldl (\<lambda>acc d. 10 * acc + d) 0 (digits_of_nat n)\<close>
  apply (induction n rule: digits_of_nat.induct)
  apply (subst digits_of_nat.simps)
  apply (simp del: digits_of_nat.simps)
  done

text \<open>The relation between digit and nat is the inverse of @{term char_uval}}\<close>

definition char_of_digit :: \<open>nat \<Rightarrow> char\<close> where
  \<open>char_of_digit n = char_of (n + 48)\<close>

definition is_digit :: \<open>nat \<Rightarrow> bool\<close> where
  \<open>is_digit n \<equiv> n < 10\<close>

definition \<open>nat_ascii_char_rel \<equiv> br char_of_digit is_digit\<close>

lemma is_ascii_unum_char_of_digit: \<open>is_digit d \<Longrightarrow> is_ascii_unum (char_of_digit d)\<close>
  by (auto simp: is_digit_def is_ascii_unum_def char_of_digit_def)

lemma char_uval_char_of_digit: \<open>is_digit d \<Longrightarrow> char_uval (char_of_digit d) = d\<close>
  by (auto simp: is_digit_def char_uval_def char_of_digit_def)

lemma nat_ascii_char_rel_ascii_char_nat_rel_inv:
  \<open>nat_ascii_char_rel O ascii_char_nat_rel = Id_on {n. is_digit n}\<close> (is ?A)
  \<open>ascii_char_nat_rel O nat_ascii_char_rel = Id_on {c. is_ascii_unum c}\<close> (is ?B)
proof -
  show ?A
    unfolding nat_ascii_char_rel_def ascii_char_nat_rel_def
    by (auto simp: in_br_conv char_of_digit_def is_digit_def char_uval_def is_ascii_unum_def)
  show ?B
    unfolding nat_ascii_char_rel_def ascii_char_nat_rel_def
    by (auto simp: in_br_conv char_of_digit_def is_digit_def char_uval_def is_ascii_unum_def)
qed

fun chars_of_nat :: \<open>nat \<Rightarrow> string\<close> where
  \<open>chars_of_nat n = 
    (if n < 10 then [char_of_digit n] 
     else chars_of_nat (n div 10) @ [char_of_digit (n mod 10)])\<close>

definition \<open>nat_ascii_str_rel \<equiv> br chars_of_nat (\<lambda>_. True)\<close>

lemma chars_of_nat_neq_Nil[simp]: \<open>chars_of_nat n \<noteq> []\<close>
  by (subst chars_of_nat.simps) (auto simp del: chars_of_nat.simps)

lemma chars_of_nat_unum[simp]: \<open>\<forall>c \<in> set (chars_of_nat n). is_ascii_unum c\<close>
  apply (induction n rule: chars_of_nat.induct)
  apply (subst chars_of_nat.simps)
  apply (auto simp del: chars_of_nat.simps simp add: is_digit_def
      intro: is_ascii_unum_char_of_digit)
  done

lemma str_uval_chars_of_nat[simp]: \<open>str_uval (chars_of_nat n) = n\<close>
  unfolding str_uval_def
  apply (induction n rule: chars_of_nat.induct)
  apply (subst chars_of_nat.simps)
  apply (auto simp del: chars_of_nat.simps simp add: char_uval_char_of_digit is_digit_def)
  done

lemma hd_chars_of_nat_not_hyphen[simp]: \<open>hd (chars_of_nat n) \<noteq> ascii_hyphen\<close>
  by (metis chars_of_nat_neq_Nil chars_of_nat_unum hd_in_set is_ascii_unum_hyphen)

lemma nat_ascii_str_rel_ascii_str_nat_rel_inv:
  \<open>nat_ascii_str_rel O ascii_str_nat_rel = Id\<close>
  unfolding nat_ascii_str_rel_def ascii_str_nat_rel_def
  apply (auto simp: relcomp_unfold is_ascii_unum_str_alt)
  apply (metis in_br_conv str_uval_chars_of_nat)
  by (metis chars_of_nat_neq_Nil chars_of_nat_unum in_br_conv 
            is_ascii_unum_str_alt str_uval_chars_of_nat)

subsubsection \<open>Extending to Integers\<close>

definition chars_of_int :: \<open>int \<Rightarrow> string\<close> where
  \<open>chars_of_int i \<equiv> 
    if 0 \<le> i then chars_of_nat (nat i) else ascii_hyphen # chars_of_nat (nat (-i))\<close>

definition \<open>int_ascii_str_rel \<equiv> br chars_of_int (\<lambda>_. True)\<close>

lemma str_sval_chars_of_int[simp]: \<open>str_sval (chars_of_int i) = i\<close>
  using chars_of_int_def hd_chars_of_nat_not_hyphen str_sval_def str_uval_chars_of_nat 
  by auto

lemma is_ascii_snum_str_chars_of_int[simp]: \<open>is_ascii_snum_str (chars_of_int i)\<close>
  by (metis chars_of_int_def chars_of_nat_neq_Nil chars_of_nat_unum 
            is_ascii_snum_str_def is_ascii_unum_str_alt list.sel(1,3))

corollary int_ascii_str_rel_ascii_str_int_rel_inv:
  \<open>int_ascii_str_rel O ascii_str_int_rel = Id\<close>
  unfolding int_ascii_str_rel_def ascii_str_int_rel_def
  apply (auto simp: relcomp_unfold)
  apply (metis in_br_conv str_sval_chars_of_int)
  by (metis in_br_conv is_ascii_snum_str_chars_of_int str_sval_chars_of_int)

subsection \<open>Refinement\<close>

subsubsection \<open>divmod for bigint\<close>

(* this whole subsection essentially just refines the following definition: *)
definition \<open>divmod_nat \<equiv> \<lambda>(a::nat) (b::nat). (a div b, a mod b)\<close>

definition divmod2by1 :: \<open>limb \<Rightarrow> limb \<Rightarrow> limb \<Rightarrow> (limb \<times> limb) nres\<close> where
  \<open>divmod2by1 hi lo d \<equiv> doN {
    ASSERT (0 < unat d \<and> unat hi < unat d);
    let cur = unat hi * limb_sz + unat lo;
    RETURN (nat_limb (cur div unat d), nat_limb (cur mod unat d))
  }\<close>

lemma divmod2by1_spec:
  assumes \<open>0 < unat d\<close> and \<open>unat hi < unat d\<close>
  shows \<open>divmod2by1 hi lo d \<le> SPEC (\<lambda>(q, r).
      unat q = (unat hi * limb_sz + unat lo) div unat d
    \<and> unat r = (unat hi * limb_sz + unat lo) mod unat d
    \<and> unat r < unat d)\<close>
proof -
  let ?cur = \<open>unat hi * limb_sz + unat lo\<close>
  have lo_lt: \<open>unat lo < limb_sz\<close> using limb_nat_lt[of lo] unfolding limb_nat_def by simp
  have d_lt: \<open>unat d < limb_sz\<close> using limb_nat_lt[of d] unfolding limb_nat_def by simp
  have cur_lt: \<open>?cur < unat d * limb_sz\<close>
  proof -
    have \<open>?cur \<le> (unat d - 1) * limb_sz + (limb_sz - 1)\<close>
      using assms(2) lo_lt by (intro add_mono mult_le_mono) auto
    also have \<open>\<dots> < unat d * limb_sz\<close>
      using assms(1) limb_sz_gt(1) by (cases \<open>unat d\<close>) (auto simp: algebra_simps)
    finally show ?thesis .
  qed
  have q_lt: \<open>?cur div unat d < limb_sz\<close>
    using cur_lt by (simp add: less_mult_imp_div_less mult.commute)
  have r_lt: \<open>?cur mod unat d < limb_sz\<close>
    using assms(1) d_lt by (meson mod_less_divisor order_less_trans)
  show ?thesis
    unfolding divmod2by1_def
    apply (refine_vcg)
    using assms apply simp
    apply (metis assms(2))
    using limb_nat_def nat_limb_mod q_lt apply force
    apply (metis nat_limb_def prod.sel(2) uno_simps(1))
    by (simp add: nat_limb_def uno_simps(1))
qed

definition bi_div_by_w64 :: \<open>big_int \<Rightarrow> limb \<Rightarrow> (big_int \<times> limb) nres\<close> where
  \<open>bi_div_by_w64 bi l \<equiv> doN {
    ASSERT (0 < unat l);
    (q, r, _) \<leftarrow> WHILEIT
      (\<lambda>(q, r, i).
          i \<le> length bi
        \<and> length q = length bi
        \<and> unat r < unat l
        \<and> unat r = big_int_\<alpha> (drop i bi) mod unat l
        \<and> big_int_\<alpha> (drop i q) = big_int_\<alpha> (drop i bi) div unat l)
      (\<lambda>(_, _, i). 0 < i)
      (\<lambda>(q, r, i). doN {
        ASSERT (0 < i \<and> i \<le> length bi);
        (d, r') \<leftarrow> divmod2by1 r (bi ! (i - 1)) l;
        RETURN (q[i - 1 := d], r', i - 1)
      })
      (replicate (length bi) 0, 0, length bi);
    q \<leftarrow> big_int_trim q;
    RETURN (q, r)
  }\<close>

lemma div_step_mod:
  fixes H d0 l :: nat
  shows \<open>(d0 + limb_sz * H) mod l = ((H mod l) * limb_sz + d0) mod l\<close>
  by (metis (no_types, lifting) add.commute mod_add_left_eq mod_mult_right_eq mult.commute)

lemma div_step_div:
  fixes H d0 l :: nat
  shows \<open>(d0 + limb_sz * H) div l = (limb_sz * (H div l)) + ((H mod l) * limb_sz + d0) div l\<close>
proof -
  have \<open>d0 + limb_sz * H = limb_sz * (H div l) * l + ((H mod l) * limb_sz + d0)\<close>
    by (metis (full_types) add.commute distrib_left div_mod_decomp
    group_cancel.add1 mult.commute mult.left_commute)
  thus ?thesis
    by (metis Euclidean_Rings.div_eq_0_iff div_mult_self3 mult_0_right
    nat_arith.rule0)
qed

lemma div_digit_step:
  fixes q bi :: big_int and ab :: limb and i l :: nat
  assumes i_pos: \<open>0 < i\<close> and i_le: \<open>i \<le> length bi\<close> and len_q: \<open>length q = length bi\<close>
    and inv_q: \<open>big_int_\<alpha> (drop i q) = big_int_\<alpha> (drop i bi) div l\<close>
    and dig: \<open>unat ab = (big_int_\<alpha> (drop i bi) mod l * limb_sz + unat (bi ! (i - 1))) div l\<close>
  shows \<open>big_int_\<alpha> (drop (i - 1) (q[i - 1 := ab])) = big_int_\<alpha> (drop (i - 1) bi) div l\<close>
proof -
  let ?j = \<open>i - 1\<close>
  let ?H = \<open>big_int_\<alpha> (drop i bi)\<close>
  have j_lt_q: \<open>?j < length q\<close> using i_pos i_le len_q by simp
  have j_lt_bi: \<open>?j < length bi\<close> using i_pos i_le by simp
  have suc: \<open>Suc ?j = i\<close> using i_pos by simp
  have drop_q: \<open>drop ?j (q[?j := ab]) = ab # drop i q\<close>
    using j_lt_q suc
    by (metis Cons_nth_drop_Suc drop_update_cancel lessI length_list_update
        nth_list_update_eq)
  have drop_bi: \<open>drop ?j bi = bi ! ?j # drop i bi\<close>
    using j_lt_bi suc by (metis Cons_nth_drop_Suc)
  have \<open>big_int_\<alpha> (drop ?j (q[?j := ab])) = unat ab + limb_sz * (?H div l)\<close>
    unfolding drop_q using inv_q by (simp add: limb_nat_def)
  also have \<open>\<dots> = (unat (bi ! ?j) + limb_sz * ?H) div l\<close>
    using dig by (simp add: div_step_div)
  also have \<open>\<dots> = big_int_\<alpha> (drop ?j bi) div l\<close>
    unfolding drop_bi by (simp add: limb_nat_def)
  finally show ?thesis .
qed

lemma bi_div_by_w64_correct_aux:
  assumes bi: \<open>(bi, a::nat) \<in> big_int_rel\<close> and l: \<open>(l, lnn::nat) \<in> unat_rel\<close> and lpos: \<open>0 < lnn\<close>
  shows \<open>bi_div_by_w64 bi l \<le> \<Down>(big_int_rel \<times>\<^sub>r unat_rel) (RETURN (a div lnn, a mod lnn))\<close>
proof -
  have a_eq: \<open>big_int_\<alpha> bi = a\<close> using bi unfolding big_int_rel_def in_br_conv by simp
  have l_eq: \<open>unat l = lnn\<close>
    using l unfolding unat_rel_def unat.rel_def in_br_conv by simp
  show ?thesis
    unfolding bi_div_by_w64_def
    apply (refine_vcg
        WHILEIT_rule[where R=\<open>measure (\<lambda>(_, _, i). i)\<close>
          and I=\<open>\<lambda>(q, r, i).
              i \<le> length bi
            \<and> length q = length bi
            \<and> unat r < unat l
            \<and> unat r = big_int_\<alpha> (drop i bi) mod unat l
            \<and> big_int_\<alpha> (drop i q) = big_int_\<alpha> (drop i bi) div unat l\<close>]
        divmod2by1_spec
        big_int_trim_correct)
    apply simp_all
    subgoal by (metis lpos l_eq) 
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal
      by (metis Cons_nth_drop_Suc Suc_pred big_int_to_nat.simps(2) div_step_mod
                limb_nat_def nz_le_conv_less)
    subgoal
      apply (clarsimp simp only: One_nat_def[symmetric])
      apply (rule div_digit_step; assumption)
      done
    subgoal
      by (simp add: a_eq big_int_rel_def brI l_eq unat.rel_def unat_rel_def)
    done
qed

lemma bi_div_by_w64_correct:
  \<open>(uncurry bi_div_by_w64, uncurry (RETURN oo divmod_nat))
  \<in> [\<lambda>(_, ln). 0 < ln]\<^sub>f big_int_rel \<times>\<^sub>r unat_rel \<rightarrow> \<langle>big_int_rel \<times>\<^sub>r unat_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (clarsimp simp: divmod_nat_def)
  apply (rule bi_div_by_w64_correct_aux; assumption)
  done

subsubsection \<open>The 128-bit divide-two-by-one primitive\<close>

definition divmod2by1_word :: \<open>limb \<Rightarrow> limb \<Rightarrow> limb \<Rightarrow> (limb \<times> limb)\<close> where
  \<open>divmod2by1_word hi lo d \<equiv>
     let cur = (extend hi << limb_wd) + extend lo; dd = extend d
     in (cutoff (cur div dd), cutoff (cur mod dd))\<close>

lemma extend_unat[simp]: \<open>unat (extend x) = unat x\<close>
proof -
  have b: \<open>unat x < 2 ^ LENGTH(double\<^sub>w)\<close>
    by (rule order_less_le_trans[OF unat_lt2p]) simp
  show ?thesis
    by (metis Word.of_nat_unat b unat_of_nat_eq)
qed

lemma limb_wd_lt_double: \<open>limb_wd < LENGTH(double\<^sub>w)\<close>
  by (simp add: limb_wd_unfold)

lemma len_double_eq: \<open>(2::nat) ^ LENGTH(double\<^sub>w) = limb_sz * limb_sz\<close>
  by (metis len_bit0 power_even_eq limb_sz_unfold power2_eq_square)

lemma unat_combine:
  \<open>unat ((extend hi << limb_wd) + extend lo) = unat hi * limb_sz + unat lo\<close>
proof -
  have hi_lt: \<open>unat hi < limb_sz\<close> using limb_nat_lt[of hi] unfolding limb_nat_def by simp
  have lo_lt: \<open>unat lo < limb_sz\<close> using limb_nat_lt[of lo] unfolding limb_nat_def by simp
  have sz: \<open>limb_sz = 2 ^ limb_wd\<close> by (simp add: limb_sz_def)
  have sh: \<open>unat (extend hi << limb_wd) = unat hi * limb_sz\<close>
  proof -
    have \<open>unat (extend hi << limb_wd) = (2 ^ limb_wd * unat hi) mod (limb_sz * limb_sz)\<close>
      by (metis Abs_fnat_hom_mult Word.unat_of_nat len_double_eq shiftl_t2n ucast_nat_def word_unat_power)
    also have \<open>\<dots> = (unat hi * limb_sz) mod (limb_sz * limb_sz)\<close>
      by (simp add: sz mult.commute)
    also have \<open>\<dots> = unat hi * limb_sz\<close>
      using hi_lt by (simp add: mult_strict_right_mono)
    finally show ?thesis .
  qed
  have sum_lt: \<open>unat hi * limb_sz + unat lo < 2 ^ LENGTH(double\<^sub>w)\<close>
    using hi_lt lo_lt unfolding len_double_eq
    by (metis hi_lt lo_lt mlex_bound)
  show ?thesis
    using sum_lt sh unat_add_lem[of \<open>extend hi << limb_wd\<close> \<open>extend lo\<close>]
    by simp
qed

lemma divmod2by1_word_eq:
  \<open>divmod2by1_word hi lo d =
     (nat_limb ((unat hi * limb_sz + unat lo) div unat d),
      nat_limb ((unat hi * limb_sz + unat lo) mod unat d))\<close>
  unfolding divmod2by1_word_def Let_def cutoff_limb
  by (simp add: unat_div unat_mod unat_combine)

lemma divmod2by1_word_refine:
  \<open>(uncurry2 (RETURN ooo divmod2by1_word), uncurry2 divmod2by1)
   \<in> (Id \<times>\<^sub>r Id) \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI; clarsimp simp: divmod2by1_def)
  apply refine_vcg
  apply (simp add: divmod2by1_word_eq)
  by (meson order_mono_setup.refl)

sepref_register divmod2by1

lemma extend_neq_zero[simp]: \<open>extend d \<noteq> 0 \<longleftrightarrow> d \<noteq> 0\<close>
  by (metis extend_unat unat_eq_zero)

sepref_def divmod2by1_impl is \<open>uncurry2 (RETURN ooo divmod2by1_word)\<close>
  :: \<open>[\<lambda>((hi, lo), d). d \<noteq> 0]\<^sub>a limb_assn\<^sup>k *\<^sub>a limb_assn\<^sup>k *\<^sub>a limb_assn\<^sup>k \<rightarrow> limb_assn \<times>\<^sub>a limb_assn\<close>
  unfolding divmod2by1_word_def
  supply [simp] = is_upcast limb_wd_unfold
  apply (rewrite at "_ << \<hole>" annot_snat_snat_upcast[where 'l="double\<^sub>w"])
  by sepref

lemmas divmod2by1_hnr[sepref_fr_rules] = divmod2by1_impl.refine[FCOMP divmod2by1_word_refine]

subsubsection \<open>The long-division loop\<close>

sepref_register bi_div_by_w64

sepref_def bi_div_by_w64_impl is \<open>uncurry bi_div_by_w64\<close>
  :: \<open>bi_aux_assn\<^sup>k *\<^sub>a limb_assn\<^sup>k \<rightarrow>\<^sub>a bi_aux_assn \<times>\<^sub>a limb_assn\<close>
  unfolding bi_div_by_w64_def
  apply (annot_snat_const size_t)
  apply (rewrite al_fold_custom_replicate)
  by sepref

context notes [fcomp_norm_unfold] = bi_assn_def[symmetric]
begin
lemmas bi_div_by_w64_hnr[sepref_fr_rules] =
  bi_div_by_w64_impl.refine[FCOMP bi_div_by_w64_correct]
end

subsubsection \<open>Unsigned Bigint to nat\<close>

text \<open>We can define @{term chars_of_nat} imperatively, using nat.\<close>

definition chars_of_nat_nres :: \<open>nat \<Rightarrow> string nres\<close> where
  \<open>chars_of_nat_nres n \<equiv> doN {
    (cs,r) \<leftarrow> WHILEIT
      (\<lambda>(cs,m). chars_of_nat n = chars_of_nat m @ cs)
      (\<lambda>(cs,n). 9 < n)
      (\<lambda>(cs,n). doN {
        let (q,r) = divmod_nat n 10;
        ASSERT(r < 10);
        RETURN ((char_of_digit r)#cs,q)
      }) ([], n);
    ASSERT (r < 10);
    RETURN ((char_of_digit r)#cs)
  }\<close>

lemma chars_of_nat_base: \<open>m < 10 \<Longrightarrow> chars_of_nat m = [char_of_digit m]\<close>
  by (subst chars_of_nat.simps) simp

lemma chars_of_nat_step:
  \<open>\<not> m < 10 \<Longrightarrow> chars_of_nat m = chars_of_nat (m div 10) @ [char_of_digit (m mod 10)]\<close>
  by (subst chars_of_nat.simps) simp

lemma char_of_nat_refine: \<open>chars_of_nat_nres n \<le> SPEC (\<lambda>cs. cs = (chars_of_nat n))\<close>
  unfolding chars_of_nat_nres_def divmod_nat_def
  apply (refine_vcg WHILEIT_rule[where R=\<open>measure (\<lambda>(_, m). m)\<close>])
  apply (auto simp del: chars_of_nat.simps simp add: chars_of_nat_base chars_of_nat_step)
  done

lemma char_of_nat_href_spec:
  \<open>(chars_of_nat_nres, RETURN o chars_of_nat) 
    \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  by (smt (verit, del_insts) Id_refine char_of_nat_refine inres_simps(2) mem_Collect_eq 
    nofail_simps(2) nres_order_simps(21) pair_in_Id_conv push_in_let_conv(2) pw_le_iff)

definition char_of_digit_sbi :: \<open>big_int \<Rightarrow> char\<close> where
  \<open>char_of_digit_sbi sbi \<equiv> char_of (unat (get_or_zero sbi 0) + 48)\<close>

lemma char_of_digit_sbi_spec:
  \<open>(char_of_digit_sbi, char_of_digit) \<in> [is_digit]\<^sub>f big_int_rel \<rightarrow> Id\<close>
proof (intro frefI)
  fix sbi :: big_int and n :: nat
  assume dig: \<open>is_digit n\<close> and rel: \<open>(sbi, n) \<in> big_int_rel\<close>
  have inv: \<open>big_int_invar sbi\<close> and n_eq: \<open>n = big_int_\<alpha> sbi\<close>
    using rel by (auto simp: big_int_rel_def in_br_conv)
  have \<open>char_of_digit_sbi sbi = char_of_digit n\<close>
  proof (cases sbi)
    case Nil
    then show ?thesis
      using n_eq by (simp add: char_of_digit_sbi_def char_of_digit_def get_or_zero_def)
  next
    case (Cons x xs)
    have \<open>big_int_\<alpha> xs = 0\<close>
    proof (rule ccontr)
      assume \<open>big_int_\<alpha> xs \<noteq> 0\<close>
      hence \<open>limb_sz \<le> limb_sz * big_int_\<alpha> xs\<close>
        using mult_le_mono2[of 1 \<open>big_int_\<alpha> xs\<close> limb_sz] by simp
      moreover have \<open>limb_sz * big_int_\<alpha> xs \<le> n\<close>
        using n_eq Cons by simp
      moreover have \<open>(10::nat) \<le> limb_sz\<close>
        by (simp add: limb_sz_unfold)
      ultimately show False
        using dig
        by (meson is_digit_def le_trans linorder_not_le)
    qed
    then obtain k where k: \<open>xs = replicate k 0\<close>
      using big_int_to_nat_0 by auto
    have \<open>xs = []\<close>
    proof (rule ccontr)
      assume ne: \<open>xs \<noteq> []\<close>
      hence \<open>last xs = 0\<close>
        using k by (metis in_set_replicate last_in_set)
      moreover have \<open>last (x # xs) \<noteq> 0\<close>
        using inv Cons by (simp add: big_int_invar_def)
      ultimately show False
        using ne by simp
    qed
    then show ?thesis
      using n_eq Cons
      by (simp add: char_of_digit_sbi_def char_of_digit_def get_or_zero_def limb_nat_def)
  qed
  thus \<open>(char_of_digit_sbi sbi, char_of_digit n) \<in> Id\<close> by simp
qed

subsubsection \<open>LLVM implementation of the digit-to-char conversion\<close>

definition cutoff8 :: \<open>limb \<Rightarrow> 8 word\<close> where
  \<open>cutoff8 w \<equiv> UCAST(limb\<^sub>w \<rightarrow> 8) w\<close>

sepref_register cutoff8

context begin
interpretation llvm_prim_arith_setup .
lemma cutoff8_hnr[sepref_fr_rules]:
  \<open>(\<lambda>w. ll_trunc w TYPE(8 word), RETURN o cutoff8) \<in> limb_assn\<^sup>k \<rightarrow>\<^sub>a word_assn' TYPE(8)\<close>
  unfolding cutoff8_def
  supply [simp] = is_down'
  apply sepref_to_hoare
  by vcg
end

definition char_of_digit_limb :: \<open>limb \<Rightarrow> char\<close> where
  \<open>char_of_digit_limb x \<equiv> char_of (unat x + 48)\<close>

lemma char_of_digit_limb_alt:
  \<open>char_of_digit_limb x = char_of_word (cutoff8 (x + 48))\<close>
proof -
  have dvd1: \<open>(2::nat) ^ 8 dvd 2 ^ 64\<close>
    by (rule le_imp_power_dvd) simp
  hence dvd2: \<open>(256::nat) dvd 2 ^ 64\<close>
    by simp
  have dvd3: \<open>(256::nat) dvd 18446744073709551616\<close>
    by eval
  show ?thesis
    unfolding char_of_digit_limb_def char_of_word_def cutoff8_def
    by (simp add: unat_ucast unat_word_ariths
        mod_mod_cancel[OF dvd1] mod_mod_cancel[OF dvd2] mod_mod_cancel[OF dvd3])
qed

sepref_register char_of_digit_limb

sepref_def char_of_digit_limb_impl [llvm_inline] is \<open>RETURN o char_of_digit_limb\<close>
  :: \<open>limb_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  unfolding char_of_digit_limb_alt
  by sepref

definition char_of_digit_sbi_nres :: \<open>big_int \<Rightarrow> char nres\<close> where
  \<open>char_of_digit_sbi_nres sbi \<equiv> doN {
     if length sbi = 0 then RETURN (char_of_digit_limb 0)
     else doN { x \<leftarrow> mop_list_get sbi 0; RETURN (char_of_digit_limb x) }
   }\<close>

lemma char_of_digit_sbi_nres_correct:
  assumes dig: \<open>is_digit n\<close> and rel: \<open>(sbi, n) \<in> big_int_rel\<close>
  shows \<open>char_of_digit_sbi_nres sbi \<le> RETURN (char_of_digit n)\<close>
proof -
  have eq: \<open>char_of_digit_sbi sbi = char_of_digit n\<close>
    using char_of_digit_sbi_spec dig rel by (auto simp: fref_def)
  show ?thesis
    using eq
    by (auto simp: char_of_digit_sbi_nres_def char_of_digit_sbi_def char_of_digit_limb_def
        get_or_zero_def pw_le_iff refine_pw_simps)
qed

lemma char_of_digit_sbi_nres_spec:
  \<open>(char_of_digit_sbi_nres, RETURN o char_of_digit) \<in> [is_digit]\<^sub>f big_int_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: char_of_digit_sbi_nres_correct)

context notes [fcomp_norm_unfold] = bi_assn_def[symmetric] begin

sepref_def char_of_digit_sbi_impl is \<open>char_of_digit_sbi_nres\<close>
  :: \<open>bi_aux_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  unfolding char_of_digit_sbi_nres_def
  apply (annot_snat_const size_t)
  by sepref

lemmas char_of_digit_hnr[sepref_fr_rules] =
  char_of_digit_sbi_impl.refine[FCOMP char_of_digit_sbi_nres_spec]

definition \<open>gt_nine \<equiv> \<lambda>(n::nat). 9 < n\<close>

lemma gt_nine_fold: \<open>(9 < n) = gt_nine n\<close>
  by (simp add: gt_nine_def)

sepref_register gt_nine

definition gt_nine_bi_nres :: \<open>big_int \<Rightarrow> bool nres\<close> where
  \<open>gt_nine_bi_nres bi \<equiv> doN {
     if 1 < length bi then RETURN True
     else if length bi = 0 then RETURN False
     else doN { x \<leftarrow> mop_list_get bi 0; RETURN ((9::limb) < x) }
   }\<close>

lemma gt_nine_bi_nres_correct:
  assumes rel: \<open>(bi, n) \<in> big_int_rel\<close>
  shows \<open>gt_nine_bi_nres bi \<le> RETURN (gt_nine n)\<close>
proof -
  have inv: \<open>big_int_invar bi\<close> and n_eq: \<open>n = big_int_\<alpha> bi\<close>
    using rel by (auto simp: big_int_rel_def in_br_conv)
  show ?thesis
  proof (cases bi)
    case Nil
    then show ?thesis
      using n_eq by (simp add: gt_nine_bi_nres_def gt_nine_def)
  next
    case bi_cons: (Cons x xs)
    show ?thesis
    proof (cases xs)
      case Nil
      hence bi_eq: \<open>bi = [x]\<close>
        using bi_cons by simp
      hence n_val: \<open>n = unat x\<close>
        using n_eq by (simp add: limb_nat_def)
      show ?thesis
        by (auto simp: gt_nine_bi_nres_def gt_nine_def bi_eq n_val word_less_nat_alt
            pw_le_iff refine_pw_simps)
    next
      case cons2: (Cons y ys)
      hence len: \<open>1 < length bi\<close>
        using bi_cons by simp
      have \<open>n \<noteq> 0\<close>
      proof
        assume \<open>n = 0\<close>
        then obtain k where k: \<open>bi = replicate k 0\<close>
          using n_eq big_int_to_nat_0 by auto
        have ne: \<open>bi \<noteq> []\<close>
          using len by auto
        hence \<open>last bi \<noteq> 0\<close>
          using inv by (simp add: big_int_invar_def)
        moreover have \<open>last bi = 0\<close>
          using k ne by (metis in_set_replicate last_in_set)
        ultimately show False by simp
      qed
      hence lb: \<open>limb_sz ^ (length bi - 1) \<le> n\<close>
        using big_int_rel_bounds(2)[OF rel] by simp
      have \<open>limb_sz ^ 1 \<le> limb_sz ^ (length bi - 1)\<close>
        by (rule power_increasing) (use len limb_sz_gt(1) in auto)
      hence \<open>limb_sz \<le> limb_sz ^ (length bi - 1)\<close>
        by simp
      moreover have \<open>(9::nat) < limb_sz\<close>
        by (simp add: limb_sz_unfold)
      ultimately have \<open>gt_nine n\<close>
        using lb unfolding gt_nine_def by linarith
      then show ?thesis
        using len by (simp add: gt_nine_bi_nres_def)
    qed
  qed
qed

lemma gt_nine_bi_nres_spec:
  \<open>(gt_nine_bi_nres, RETURN o gt_nine) \<in> big_int_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: gt_nine_bi_nres_correct)

sepref_def gt_nine_bi_impl is \<open>gt_nine_bi_nres\<close>
  :: \<open>bi_aux_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding gt_nine_bi_nres_def
  apply (annot_snat_const size_t)
  by sepref

lemmas gt_nine_hnr[sepref_fr_rules] =
  gt_nine_bi_impl.refine[FCOMP gt_nine_bi_nres_spec]

lemma char_of_digit_limb_unat_refine:
  \<open>(RETURN o char_of_digit_limb, RETURN o char_of_digit) \<in> unat_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: char_of_digit_limb_def char_of_digit_def unat_rel_def unat.rel_def
       in_br_conv)

lemmas char_of_digit_unat_hnr[sepref_fr_rules] =
  char_of_digit_limb_impl.refine[FCOMP char_of_digit_limb_unat_refine]

sepref_register char_of_digit
sepref_def char_of_nat_impl is \<open>chars_of_nat_nres\<close>
  :: \<open>bi_assn\<^sup>d \<rightarrow>\<^sub>a strl_assn'\<close>
  unfolding chars_of_nat_nres_def gt_nine_fold
  supply [simp] = is_digit_def
  apply (annot_unat_const size_t)
  by sepref

lemmas char_of_nat_hnr[sepref_fr_rules] = 
  char_of_nat_impl.refine[FCOMP char_of_nat_href_spec]

subsubsection \<open>Extending to signed big integers\<close>

definition \<open>int_sign \<equiv> \<lambda>(i::int). if i < 0 then True else False\<close>

lemma int_sign_impl[sepref_fr_rules]:
  \<open>(\<lambda>(sbi,s). Mreturn s, RETURN o int_sign)
  \<in> sbi_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding int_sign_def
  apply sepref_to_hoare
  apply vcg
  apply (auto simp: ENTAILS_def entails_def sep_algebra_simps
    bool1_rel_def bool.rel_def in_br_conv sbi_assn_def pure_def
    hr_comp_def signed_big_int_rel_def signed_big_int_to_int_def
    signed_big_int_invar_def \<sigma>_def)
  using big_int_to_nat_not0 apply blast
  using big_int_to_nat_not0 apply blast
  using big_int_to_nat_not0 by blast

definition \<open>int_abs_nat \<equiv> nat o abs\<close>

lemma limbs_of_sbi_impl[sepref_fr_rules]:
  \<open>(\<lambda>(sbi,s).Mreturn sbi, RETURN o int_abs_nat)
  \<in> sbi_assn\<^sup>d \<rightarrow>\<^sub>a bi_assn\<close>
  unfolding int_abs_nat_def
  apply (sepref_to_hoare; vcg)
  apply (auto simp: ENTAILS_def entails_def sep_algebra_simps
  sbi_assn_def bi_assn_def hr_comp_def bool1_rel_def pure_def
  bool.rel_def in_br_conv signed_big_int_rel_def 
  signed_big_int_to_int_def signed_big_int_invar_def big_int_rel_def)
  using limbs_of_def apply force
  using big_int_invar_def limbs_of_def apply auto[1]
  apply (metis big_int_invar_def fst_conv limbs_of_def)
  using big_int_to_nat_not0 by blast

definition chars_of_int_nres :: \<open>int \<Rightarrow> string nres\<close> where
  \<open>chars_of_int_nres i \<equiv> doN {
    let \<sigma> = int_sign i;
    if \<sigma> then doN {
      let n = int_abs_nat i;
      let csn = chars_of_nat n;
      RETURN (ascii_hyphen#csn)
    } else doN {
      let n = int_abs_nat i;
      let csn = chars_of_nat n;
      RETURN (csn)
    }
  }\<close>

lemma char_of_int_spec:
  \<open>(chars_of_int_nres, RETURN o chars_of_int)
  \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding chars_of_int_nres_def chars_of_int_def
    int_sign_def int_abs_nat_def
  by (smt (verit, del_insts) Id_refine comp_apply pair_in_Id_conv)
  
sepref_def chars_of_int_impl is \<open>chars_of_int_nres\<close>
  :: \<open>sbi_assn\<^sup>d \<rightarrow>\<^sub>a strl_assn'\<close>
  unfolding chars_of_int_nres_def
  by sepref

lemmas chars_of_int_hnr[sepref_fr_rules] =
  chars_of_int_impl.refine[FCOMP char_of_int_spec]

text \<open>We can compose with the high level ascii semantics like we did 
  for string \<rightarrow> int\<close>

definition sbi_str_assn where
  \<open>sbi_str_assn \<equiv> hr_comp sbi_assn int_ascii_str_rel\<close>

lemma chars_of_int_id_refine:
  \<open>(RETURN o chars_of_int, RETURN o id)
  \<in> int_ascii_str_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: int_ascii_str_rel_def in_br_conv)

text \<open>This is overall correctness lemma for our sbi \<rightarrow> string converstion\<close>
lemmas int_str_conv_hnr = chars_of_int_hnr[FCOMP chars_of_int_id_refine]

end

end
