theory Printing_Setup
  imports Char_Assn
begin

text \<open>Constant-table synthesis for character literals.

  A literal \<open>CHR ''-''\<close> is notation for the ground constructor application
  @{term \<open>Char True False True True False True False False\<close>}, and \<open>Char\<close> is a
  \<open>sepref_register\<close>ed 8-ary operation (@{thm asciichar_of_holchar_hnr}); each literal
  therefore synthesizes into eight boolean constants plus the inlined
  \<open>asciichar_of_holchar\<close> zext/shl/or chain (~23 LLVM instructions per literal).
  Clang constant-folds that chain, but the generated \<open>.ll\<close> is bloated and every
  literal costs sepref nine rule applications.

  Here we instead fold each literal into a dedicated nullary operation via
  \<open>def_pat_rules\<close> \<^emph>\<open>in the ID phase\<close>, i.e. before monadify flattens the \<open>Char\<close>
  application, and give that operation a one-instruction implementation
  \<open>Mreturn <code>\<close>. Characters outside the table (non-printable, non-newline)
  still take the generic constructor route.\<close>

section \<open>Generic constant rule\<close>

text \<open>@{term char_assn} is pure (@{thm char_assn_pure}), so any word literal
  refines the corresponding abstract character.\<close>

lemma char_const_hnr:
  assumes \<open>char_of_word w = c\<close>
  shows \<open>(uncurry0 (Mreturn w), uncurry0 (RETURN c)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  unfolding char_assn_def
  apply (intro hfrefI hn_refineI; vcg)
  apply (auto simp: assms[symmetric] in_br_conv ENTAILS_def entails_def char_rel_def
      sep_algebra_simps pure_def pred_lift_extract_simps)
  done

section \<open>The character table\<close>

definition op_char_10 :: char where [simp]: \<open>op_char_10 = CHR 0x0A\<close> (* newline *)
sepref_register op_char_10
lemma [def_pat_rules]: \<open>Char$False$True$False$True$False$False$False$False \<equiv> op_char_10\<close> by simp
lemma op_char_10_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x0A), uncurry0 (RETURN op_char_10)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_32 :: char where [simp]: \<open>op_char_32 = CHR 0x20\<close> (* space *)
sepref_register op_char_32
lemma [def_pat_rules]: \<open>Char$False$False$False$False$False$True$False$False \<equiv> op_char_32\<close> by simp
lemma op_char_32_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x20), uncurry0 (RETURN op_char_32)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_33 :: char where [simp]: \<open>op_char_33 = CHR 0x21\<close> (* ! *)
sepref_register op_char_33
lemma [def_pat_rules]: \<open>Char$True$False$False$False$False$True$False$False \<equiv> op_char_33\<close> by simp
lemma op_char_33_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x21), uncurry0 (RETURN op_char_33)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_34 :: char where [simp]: \<open>op_char_34 = CHR 0x22\<close> (* " *)
sepref_register op_char_34
lemma [def_pat_rules]: \<open>Char$False$True$False$False$False$True$False$False \<equiv> op_char_34\<close> by simp
lemma op_char_34_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x22), uncurry0 (RETURN op_char_34)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_35 :: char where [simp]: \<open>op_char_35 = CHR 0x23\<close> (* # *)
sepref_register op_char_35
lemma [def_pat_rules]: \<open>Char$True$True$False$False$False$True$False$False \<equiv> op_char_35\<close> by simp
lemma op_char_35_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x23), uncurry0 (RETURN op_char_35)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_36 :: char where [simp]: \<open>op_char_36 = CHR 0x24\<close> (* $ *)
sepref_register op_char_36
lemma [def_pat_rules]: \<open>Char$False$False$True$False$False$True$False$False \<equiv> op_char_36\<close> by simp
lemma op_char_36_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x24), uncurry0 (RETURN op_char_36)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_37 :: char where [simp]: \<open>op_char_37 = CHR 0x25\<close> (* % *)
sepref_register op_char_37
lemma [def_pat_rules]: \<open>Char$True$False$True$False$False$True$False$False \<equiv> op_char_37\<close> by simp
lemma op_char_37_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x25), uncurry0 (RETURN op_char_37)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_38 :: char where [simp]: \<open>op_char_38 = CHR 0x26\<close> (* & *)
sepref_register op_char_38
lemma [def_pat_rules]: \<open>Char$False$True$True$False$False$True$False$False \<equiv> op_char_38\<close> by simp
lemma op_char_38_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x26), uncurry0 (RETURN op_char_38)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_39 :: char where [simp]: \<open>op_char_39 = CHR 0x27\<close> (* ' *)
sepref_register op_char_39
lemma [def_pat_rules]: \<open>Char$True$True$True$False$False$True$False$False \<equiv> op_char_39\<close> by simp
lemma op_char_39_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x27), uncurry0 (RETURN op_char_39)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_40 :: char where [simp]: \<open>op_char_40 = CHR 0x28\<close> (* ( *)
sepref_register op_char_40
lemma [def_pat_rules]: \<open>Char$False$False$False$True$False$True$False$False \<equiv> op_char_40\<close> by simp
lemma op_char_40_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x28), uncurry0 (RETURN op_char_40)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_41 :: char where [simp]: \<open>op_char_41 = CHR 0x29\<close> (* ) *)
sepref_register op_char_41
lemma [def_pat_rules]: \<open>Char$True$False$False$True$False$True$False$False \<equiv> op_char_41\<close> by simp
lemma op_char_41_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x29), uncurry0 (RETURN op_char_41)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_42 :: char where [simp]: \<open>op_char_42 = CHR 0x2A\<close> (* * *)
sepref_register op_char_42
lemma [def_pat_rules]: \<open>Char$False$True$False$True$False$True$False$False \<equiv> op_char_42\<close> by simp
lemma op_char_42_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x2A), uncurry0 (RETURN op_char_42)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_43 :: char where [simp]: \<open>op_char_43 = CHR 0x2B\<close> (* + *)
sepref_register op_char_43
lemma [def_pat_rules]: \<open>Char$True$True$False$True$False$True$False$False \<equiv> op_char_43\<close> by simp
lemma op_char_43_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x2B), uncurry0 (RETURN op_char_43)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_44 :: char where [simp]: \<open>op_char_44 = CHR 0x2C\<close> (* , *)
sepref_register op_char_44
lemma [def_pat_rules]: \<open>Char$False$False$True$True$False$True$False$False \<equiv> op_char_44\<close> by simp
lemma op_char_44_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x2C), uncurry0 (RETURN op_char_44)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_45 :: char where [simp]: \<open>op_char_45 = CHR 0x2D\<close> (* - *)
sepref_register op_char_45
lemma [def_pat_rules]: \<open>Char$True$False$True$True$False$True$False$False \<equiv> op_char_45\<close> by simp
lemma op_char_45_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x2D), uncurry0 (RETURN op_char_45)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_46 :: char where [simp]: \<open>op_char_46 = CHR 0x2E\<close> (* . *)
sepref_register op_char_46
lemma [def_pat_rules]: \<open>Char$False$True$True$True$False$True$False$False \<equiv> op_char_46\<close> by simp
lemma op_char_46_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x2E), uncurry0 (RETURN op_char_46)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_47 :: char where [simp]: \<open>op_char_47 = CHR 0x2F\<close> (* / *)
sepref_register op_char_47
lemma [def_pat_rules]: \<open>Char$True$True$True$True$False$True$False$False \<equiv> op_char_47\<close> by simp
lemma op_char_47_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x2F), uncurry0 (RETURN op_char_47)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_48 :: char where [simp]: \<open>op_char_48 = CHR 0x30\<close> (* 0 *)
sepref_register op_char_48
lemma [def_pat_rules]: \<open>Char$False$False$False$False$True$True$False$False \<equiv> op_char_48\<close> by simp
lemma op_char_48_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x30), uncurry0 (RETURN op_char_48)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_49 :: char where [simp]: \<open>op_char_49 = CHR 0x31\<close> (* 1 *)
sepref_register op_char_49
lemma [def_pat_rules]: \<open>Char$True$False$False$False$True$True$False$False \<equiv> op_char_49\<close> by simp
lemma op_char_49_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x31), uncurry0 (RETURN op_char_49)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_50 :: char where [simp]: \<open>op_char_50 = CHR 0x32\<close> (* 2 *)
sepref_register op_char_50
lemma [def_pat_rules]: \<open>Char$False$True$False$False$True$True$False$False \<equiv> op_char_50\<close> by simp
lemma op_char_50_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x32), uncurry0 (RETURN op_char_50)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_51 :: char where [simp]: \<open>op_char_51 = CHR 0x33\<close> (* 3 *)
sepref_register op_char_51
lemma [def_pat_rules]: \<open>Char$True$True$False$False$True$True$False$False \<equiv> op_char_51\<close> by simp
lemma op_char_51_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x33), uncurry0 (RETURN op_char_51)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_52 :: char where [simp]: \<open>op_char_52 = CHR 0x34\<close> (* 4 *)
sepref_register op_char_52
lemma [def_pat_rules]: \<open>Char$False$False$True$False$True$True$False$False \<equiv> op_char_52\<close> by simp
lemma op_char_52_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x34), uncurry0 (RETURN op_char_52)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_53 :: char where [simp]: \<open>op_char_53 = CHR 0x35\<close> (* 5 *)
sepref_register op_char_53
lemma [def_pat_rules]: \<open>Char$True$False$True$False$True$True$False$False \<equiv> op_char_53\<close> by simp
lemma op_char_53_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x35), uncurry0 (RETURN op_char_53)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_54 :: char where [simp]: \<open>op_char_54 = CHR 0x36\<close> (* 6 *)
sepref_register op_char_54
lemma [def_pat_rules]: \<open>Char$False$True$True$False$True$True$False$False \<equiv> op_char_54\<close> by simp
lemma op_char_54_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x36), uncurry0 (RETURN op_char_54)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_55 :: char where [simp]: \<open>op_char_55 = CHR 0x37\<close> (* 7 *)
sepref_register op_char_55
lemma [def_pat_rules]: \<open>Char$True$True$True$False$True$True$False$False \<equiv> op_char_55\<close> by simp
lemma op_char_55_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x37), uncurry0 (RETURN op_char_55)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_56 :: char where [simp]: \<open>op_char_56 = CHR 0x38\<close> (* 8 *)
sepref_register op_char_56
lemma [def_pat_rules]: \<open>Char$False$False$False$True$True$True$False$False \<equiv> op_char_56\<close> by simp
lemma op_char_56_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x38), uncurry0 (RETURN op_char_56)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_57 :: char where [simp]: \<open>op_char_57 = CHR 0x39\<close> (* 9 *)
sepref_register op_char_57
lemma [def_pat_rules]: \<open>Char$True$False$False$True$True$True$False$False \<equiv> op_char_57\<close> by simp
lemma op_char_57_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x39), uncurry0 (RETURN op_char_57)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_58 :: char where [simp]: \<open>op_char_58 = CHR 0x3A\<close> (* : *)
sepref_register op_char_58
lemma [def_pat_rules]: \<open>Char$False$True$False$True$True$True$False$False \<equiv> op_char_58\<close> by simp
lemma op_char_58_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x3A), uncurry0 (RETURN op_char_58)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_59 :: char where [simp]: \<open>op_char_59 = CHR 0x3B\<close> (* ; *)
sepref_register op_char_59
lemma [def_pat_rules]: \<open>Char$True$True$False$True$True$True$False$False \<equiv> op_char_59\<close> by simp
lemma op_char_59_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x3B), uncurry0 (RETURN op_char_59)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_60 :: char where [simp]: \<open>op_char_60 = CHR 0x3C\<close> (* < *)
sepref_register op_char_60
lemma [def_pat_rules]: \<open>Char$False$False$True$True$True$True$False$False \<equiv> op_char_60\<close> by simp
lemma op_char_60_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x3C), uncurry0 (RETURN op_char_60)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_61 :: char where [simp]: \<open>op_char_61 = CHR 0x3D\<close> (* = *)
sepref_register op_char_61
lemma [def_pat_rules]: \<open>Char$True$False$True$True$True$True$False$False \<equiv> op_char_61\<close> by simp
lemma op_char_61_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x3D), uncurry0 (RETURN op_char_61)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_62 :: char where [simp]: \<open>op_char_62 = CHR 0x3E\<close> (* > *)
sepref_register op_char_62
lemma [def_pat_rules]: \<open>Char$False$True$True$True$True$True$False$False \<equiv> op_char_62\<close> by simp
lemma op_char_62_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x3E), uncurry0 (RETURN op_char_62)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_63 :: char where [simp]: \<open>op_char_63 = CHR 0x3F\<close> (* ? *)
sepref_register op_char_63
lemma [def_pat_rules]: \<open>Char$True$True$True$True$True$True$False$False \<equiv> op_char_63\<close> by simp
lemma op_char_63_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x3F), uncurry0 (RETURN op_char_63)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_64 :: char where [simp]: \<open>op_char_64 = CHR 0x40\<close> (* @ *)
sepref_register op_char_64
lemma [def_pat_rules]: \<open>Char$False$False$False$False$False$False$True$False \<equiv> op_char_64\<close> by simp
lemma op_char_64_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x40), uncurry0 (RETURN op_char_64)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_65 :: char where [simp]: \<open>op_char_65 = CHR 0x41\<close> (* A *)
sepref_register op_char_65
lemma [def_pat_rules]: \<open>Char$True$False$False$False$False$False$True$False \<equiv> op_char_65\<close> by simp
lemma op_char_65_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x41), uncurry0 (RETURN op_char_65)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_66 :: char where [simp]: \<open>op_char_66 = CHR 0x42\<close> (* B *)
sepref_register op_char_66
lemma [def_pat_rules]: \<open>Char$False$True$False$False$False$False$True$False \<equiv> op_char_66\<close> by simp
lemma op_char_66_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x42), uncurry0 (RETURN op_char_66)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_67 :: char where [simp]: \<open>op_char_67 = CHR 0x43\<close> (* C *)
sepref_register op_char_67
lemma [def_pat_rules]: \<open>Char$True$True$False$False$False$False$True$False \<equiv> op_char_67\<close> by simp
lemma op_char_67_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x43), uncurry0 (RETURN op_char_67)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_68 :: char where [simp]: \<open>op_char_68 = CHR 0x44\<close> (* D *)
sepref_register op_char_68
lemma [def_pat_rules]: \<open>Char$False$False$True$False$False$False$True$False \<equiv> op_char_68\<close> by simp
lemma op_char_68_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x44), uncurry0 (RETURN op_char_68)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_69 :: char where [simp]: \<open>op_char_69 = CHR 0x45\<close> (* E *)
sepref_register op_char_69
lemma [def_pat_rules]: \<open>Char$True$False$True$False$False$False$True$False \<equiv> op_char_69\<close> by simp
lemma op_char_69_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x45), uncurry0 (RETURN op_char_69)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_70 :: char where [simp]: \<open>op_char_70 = CHR 0x46\<close> (* F *)
sepref_register op_char_70
lemma [def_pat_rules]: \<open>Char$False$True$True$False$False$False$True$False \<equiv> op_char_70\<close> by simp
lemma op_char_70_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x46), uncurry0 (RETURN op_char_70)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_71 :: char where [simp]: \<open>op_char_71 = CHR 0x47\<close> (* G *)
sepref_register op_char_71
lemma [def_pat_rules]: \<open>Char$True$True$True$False$False$False$True$False \<equiv> op_char_71\<close> by simp
lemma op_char_71_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x47), uncurry0 (RETURN op_char_71)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_72 :: char where [simp]: \<open>op_char_72 = CHR 0x48\<close> (* H *)
sepref_register op_char_72
lemma [def_pat_rules]: \<open>Char$False$False$False$True$False$False$True$False \<equiv> op_char_72\<close> by simp
lemma op_char_72_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x48), uncurry0 (RETURN op_char_72)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_73 :: char where [simp]: \<open>op_char_73 = CHR 0x49\<close> (* I *)
sepref_register op_char_73
lemma [def_pat_rules]: \<open>Char$True$False$False$True$False$False$True$False \<equiv> op_char_73\<close> by simp
lemma op_char_73_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x49), uncurry0 (RETURN op_char_73)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_74 :: char where [simp]: \<open>op_char_74 = CHR 0x4A\<close> (* J *)
sepref_register op_char_74
lemma [def_pat_rules]: \<open>Char$False$True$False$True$False$False$True$False \<equiv> op_char_74\<close> by simp
lemma op_char_74_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x4A), uncurry0 (RETURN op_char_74)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_75 :: char where [simp]: \<open>op_char_75 = CHR 0x4B\<close> (* K *)
sepref_register op_char_75
lemma [def_pat_rules]: \<open>Char$True$True$False$True$False$False$True$False \<equiv> op_char_75\<close> by simp
lemma op_char_75_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x4B), uncurry0 (RETURN op_char_75)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_76 :: char where [simp]: \<open>op_char_76 = CHR 0x4C\<close> (* L *)
sepref_register op_char_76
lemma [def_pat_rules]: \<open>Char$False$False$True$True$False$False$True$False \<equiv> op_char_76\<close> by simp
lemma op_char_76_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x4C), uncurry0 (RETURN op_char_76)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_77 :: char where [simp]: \<open>op_char_77 = CHR 0x4D\<close> (* M *)
sepref_register op_char_77
lemma [def_pat_rules]: \<open>Char$True$False$True$True$False$False$True$False \<equiv> op_char_77\<close> by simp
lemma op_char_77_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x4D), uncurry0 (RETURN op_char_77)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_78 :: char where [simp]: \<open>op_char_78 = CHR 0x4E\<close> (* N *)
sepref_register op_char_78
lemma [def_pat_rules]: \<open>Char$False$True$True$True$False$False$True$False \<equiv> op_char_78\<close> by simp
lemma op_char_78_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x4E), uncurry0 (RETURN op_char_78)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_79 :: char where [simp]: \<open>op_char_79 = CHR 0x4F\<close> (* O *)
sepref_register op_char_79
lemma [def_pat_rules]: \<open>Char$True$True$True$True$False$False$True$False \<equiv> op_char_79\<close> by simp
lemma op_char_79_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x4F), uncurry0 (RETURN op_char_79)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_80 :: char where [simp]: \<open>op_char_80 = CHR 0x50\<close> (* P *)
sepref_register op_char_80
lemma [def_pat_rules]: \<open>Char$False$False$False$False$True$False$True$False \<equiv> op_char_80\<close> by simp
lemma op_char_80_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x50), uncurry0 (RETURN op_char_80)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_81 :: char where [simp]: \<open>op_char_81 = CHR 0x51\<close> (* Q *)
sepref_register op_char_81
lemma [def_pat_rules]: \<open>Char$True$False$False$False$True$False$True$False \<equiv> op_char_81\<close> by simp
lemma op_char_81_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x51), uncurry0 (RETURN op_char_81)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_82 :: char where [simp]: \<open>op_char_82 = CHR 0x52\<close> (* R *)
sepref_register op_char_82
lemma [def_pat_rules]: \<open>Char$False$True$False$False$True$False$True$False \<equiv> op_char_82\<close> by simp
lemma op_char_82_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x52), uncurry0 (RETURN op_char_82)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_83 :: char where [simp]: \<open>op_char_83 = CHR 0x53\<close> (* S *)
sepref_register op_char_83
lemma [def_pat_rules]: \<open>Char$True$True$False$False$True$False$True$False \<equiv> op_char_83\<close> by simp
lemma op_char_83_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x53), uncurry0 (RETURN op_char_83)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_84 :: char where [simp]: \<open>op_char_84 = CHR 0x54\<close> (* T *)
sepref_register op_char_84
lemma [def_pat_rules]: \<open>Char$False$False$True$False$True$False$True$False \<equiv> op_char_84\<close> by simp
lemma op_char_84_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x54), uncurry0 (RETURN op_char_84)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_85 :: char where [simp]: \<open>op_char_85 = CHR 0x55\<close> (* U *)
sepref_register op_char_85
lemma [def_pat_rules]: \<open>Char$True$False$True$False$True$False$True$False \<equiv> op_char_85\<close> by simp
lemma op_char_85_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x55), uncurry0 (RETURN op_char_85)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_86 :: char where [simp]: \<open>op_char_86 = CHR 0x56\<close> (* V *)
sepref_register op_char_86
lemma [def_pat_rules]: \<open>Char$False$True$True$False$True$False$True$False \<equiv> op_char_86\<close> by simp
lemma op_char_86_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x56), uncurry0 (RETURN op_char_86)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_87 :: char where [simp]: \<open>op_char_87 = CHR 0x57\<close> (* W *)
sepref_register op_char_87
lemma [def_pat_rules]: \<open>Char$True$True$True$False$True$False$True$False \<equiv> op_char_87\<close> by simp
lemma op_char_87_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x57), uncurry0 (RETURN op_char_87)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_88 :: char where [simp]: \<open>op_char_88 = CHR 0x58\<close> (* X *)
sepref_register op_char_88
lemma [def_pat_rules]: \<open>Char$False$False$False$True$True$False$True$False \<equiv> op_char_88\<close> by simp
lemma op_char_88_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x58), uncurry0 (RETURN op_char_88)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_89 :: char where [simp]: \<open>op_char_89 = CHR 0x59\<close> (* Y *)
sepref_register op_char_89
lemma [def_pat_rules]: \<open>Char$True$False$False$True$True$False$True$False \<equiv> op_char_89\<close> by simp
lemma op_char_89_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x59), uncurry0 (RETURN op_char_89)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_90 :: char where [simp]: \<open>op_char_90 = CHR 0x5A\<close> (* Z *)
sepref_register op_char_90
lemma [def_pat_rules]: \<open>Char$False$True$False$True$True$False$True$False \<equiv> op_char_90\<close> by simp
lemma op_char_90_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x5A), uncurry0 (RETURN op_char_90)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_91 :: char where [simp]: \<open>op_char_91 = CHR 0x5B\<close> (* [ *)
sepref_register op_char_91
lemma [def_pat_rules]: \<open>Char$True$True$False$True$True$False$True$False \<equiv> op_char_91\<close> by simp
lemma op_char_91_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x5B), uncurry0 (RETURN op_char_91)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_92 :: char where [simp]: \<open>op_char_92 = CHR 0x5C\<close> (* \ *)
sepref_register op_char_92
lemma [def_pat_rules]: \<open>Char$False$False$True$True$True$False$True$False \<equiv> op_char_92\<close> by simp
lemma op_char_92_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x5C), uncurry0 (RETURN op_char_92)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_93 :: char where [simp]: \<open>op_char_93 = CHR 0x5D\<close> (* ] *)
sepref_register op_char_93
lemma [def_pat_rules]: \<open>Char$True$False$True$True$True$False$True$False \<equiv> op_char_93\<close> by simp
lemma op_char_93_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x5D), uncurry0 (RETURN op_char_93)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_94 :: char where [simp]: \<open>op_char_94 = CHR 0x5E\<close> (* ^ *)
sepref_register op_char_94
lemma [def_pat_rules]: \<open>Char$False$True$True$True$True$False$True$False \<equiv> op_char_94\<close> by simp
lemma op_char_94_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x5E), uncurry0 (RETURN op_char_94)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_95 :: char where [simp]: \<open>op_char_95 = CHR 0x5F\<close> (* _ *)
sepref_register op_char_95
lemma [def_pat_rules]: \<open>Char$True$True$True$True$True$False$True$False \<equiv> op_char_95\<close> by simp
lemma op_char_95_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x5F), uncurry0 (RETURN op_char_95)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_96 :: char where [simp]: \<open>op_char_96 = CHR 0x60\<close> (* ` *)
sepref_register op_char_96
lemma [def_pat_rules]: \<open>Char$False$False$False$False$False$True$True$False \<equiv> op_char_96\<close> by simp
lemma op_char_96_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x60), uncurry0 (RETURN op_char_96)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_97 :: char where [simp]: \<open>op_char_97 = CHR 0x61\<close> (* a *)
sepref_register op_char_97
lemma [def_pat_rules]: \<open>Char$True$False$False$False$False$True$True$False \<equiv> op_char_97\<close> by simp
lemma op_char_97_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x61), uncurry0 (RETURN op_char_97)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_98 :: char where [simp]: \<open>op_char_98 = CHR 0x62\<close> (* b *)
sepref_register op_char_98
lemma [def_pat_rules]: \<open>Char$False$True$False$False$False$True$True$False \<equiv> op_char_98\<close> by simp
lemma op_char_98_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x62), uncurry0 (RETURN op_char_98)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_99 :: char where [simp]: \<open>op_char_99 = CHR 0x63\<close> (* c *)
sepref_register op_char_99
lemma [def_pat_rules]: \<open>Char$True$True$False$False$False$True$True$False \<equiv> op_char_99\<close> by simp
lemma op_char_99_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x63), uncurry0 (RETURN op_char_99)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_100 :: char where [simp]: \<open>op_char_100 = CHR 0x64\<close> (* d *)
sepref_register op_char_100
lemma [def_pat_rules]: \<open>Char$False$False$True$False$False$True$True$False \<equiv> op_char_100\<close> by simp
lemma op_char_100_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x64), uncurry0 (RETURN op_char_100)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_101 :: char where [simp]: \<open>op_char_101 = CHR 0x65\<close> (* e *)
sepref_register op_char_101
lemma [def_pat_rules]: \<open>Char$True$False$True$False$False$True$True$False \<equiv> op_char_101\<close> by simp
lemma op_char_101_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x65), uncurry0 (RETURN op_char_101)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_102 :: char where [simp]: \<open>op_char_102 = CHR 0x66\<close> (* f *)
sepref_register op_char_102
lemma [def_pat_rules]: \<open>Char$False$True$True$False$False$True$True$False \<equiv> op_char_102\<close> by simp
lemma op_char_102_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x66), uncurry0 (RETURN op_char_102)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_103 :: char where [simp]: \<open>op_char_103 = CHR 0x67\<close> (* g *)
sepref_register op_char_103
lemma [def_pat_rules]: \<open>Char$True$True$True$False$False$True$True$False \<equiv> op_char_103\<close> by simp
lemma op_char_103_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x67), uncurry0 (RETURN op_char_103)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_104 :: char where [simp]: \<open>op_char_104 = CHR 0x68\<close> (* h *)
sepref_register op_char_104
lemma [def_pat_rules]: \<open>Char$False$False$False$True$False$True$True$False \<equiv> op_char_104\<close> by simp
lemma op_char_104_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x68), uncurry0 (RETURN op_char_104)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_105 :: char where [simp]: \<open>op_char_105 = CHR 0x69\<close> (* i *)
sepref_register op_char_105
lemma [def_pat_rules]: \<open>Char$True$False$False$True$False$True$True$False \<equiv> op_char_105\<close> by simp
lemma op_char_105_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x69), uncurry0 (RETURN op_char_105)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_106 :: char where [simp]: \<open>op_char_106 = CHR 0x6A\<close> (* j *)
sepref_register op_char_106
lemma [def_pat_rules]: \<open>Char$False$True$False$True$False$True$True$False \<equiv> op_char_106\<close> by simp
lemma op_char_106_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x6A), uncurry0 (RETURN op_char_106)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_107 :: char where [simp]: \<open>op_char_107 = CHR 0x6B\<close> (* k *)
sepref_register op_char_107
lemma [def_pat_rules]: \<open>Char$True$True$False$True$False$True$True$False \<equiv> op_char_107\<close> by simp
lemma op_char_107_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x6B), uncurry0 (RETURN op_char_107)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_108 :: char where [simp]: \<open>op_char_108 = CHR 0x6C\<close> (* l *)
sepref_register op_char_108
lemma [def_pat_rules]: \<open>Char$False$False$True$True$False$True$True$False \<equiv> op_char_108\<close> by simp
lemma op_char_108_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x6C), uncurry0 (RETURN op_char_108)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_109 :: char where [simp]: \<open>op_char_109 = CHR 0x6D\<close> (* m *)
sepref_register op_char_109
lemma [def_pat_rules]: \<open>Char$True$False$True$True$False$True$True$False \<equiv> op_char_109\<close> by simp
lemma op_char_109_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x6D), uncurry0 (RETURN op_char_109)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_110 :: char where [simp]: \<open>op_char_110 = CHR 0x6E\<close> (* n *)
sepref_register op_char_110
lemma [def_pat_rules]: \<open>Char$False$True$True$True$False$True$True$False \<equiv> op_char_110\<close> by simp
lemma op_char_110_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x6E), uncurry0 (RETURN op_char_110)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_111 :: char where [simp]: \<open>op_char_111 = CHR 0x6F\<close> (* o *)
sepref_register op_char_111
lemma [def_pat_rules]: \<open>Char$True$True$True$True$False$True$True$False \<equiv> op_char_111\<close> by simp
lemma op_char_111_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x6F), uncurry0 (RETURN op_char_111)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_112 :: char where [simp]: \<open>op_char_112 = CHR 0x70\<close> (* p *)
sepref_register op_char_112
lemma [def_pat_rules]: \<open>Char$False$False$False$False$True$True$True$False \<equiv> op_char_112\<close> by simp
lemma op_char_112_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x70), uncurry0 (RETURN op_char_112)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_113 :: char where [simp]: \<open>op_char_113 = CHR 0x71\<close> (* q *)
sepref_register op_char_113
lemma [def_pat_rules]: \<open>Char$True$False$False$False$True$True$True$False \<equiv> op_char_113\<close> by simp
lemma op_char_113_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x71), uncurry0 (RETURN op_char_113)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_114 :: char where [simp]: \<open>op_char_114 = CHR 0x72\<close> (* r *)
sepref_register op_char_114
lemma [def_pat_rules]: \<open>Char$False$True$False$False$True$True$True$False \<equiv> op_char_114\<close> by simp
lemma op_char_114_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x72), uncurry0 (RETURN op_char_114)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_115 :: char where [simp]: \<open>op_char_115 = CHR 0x73\<close> (* s *)
sepref_register op_char_115
lemma [def_pat_rules]: \<open>Char$True$True$False$False$True$True$True$False \<equiv> op_char_115\<close> by simp
lemma op_char_115_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x73), uncurry0 (RETURN op_char_115)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_116 :: char where [simp]: \<open>op_char_116 = CHR 0x74\<close> (* t *)
sepref_register op_char_116
lemma [def_pat_rules]: \<open>Char$False$False$True$False$True$True$True$False \<equiv> op_char_116\<close> by simp
lemma op_char_116_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x74), uncurry0 (RETURN op_char_116)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_117 :: char where [simp]: \<open>op_char_117 = CHR 0x75\<close> (* u *)
sepref_register op_char_117
lemma [def_pat_rules]: \<open>Char$True$False$True$False$True$True$True$False \<equiv> op_char_117\<close> by simp
lemma op_char_117_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x75), uncurry0 (RETURN op_char_117)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_118 :: char where [simp]: \<open>op_char_118 = CHR 0x76\<close> (* v *)
sepref_register op_char_118
lemma [def_pat_rules]: \<open>Char$False$True$True$False$True$True$True$False \<equiv> op_char_118\<close> by simp
lemma op_char_118_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x76), uncurry0 (RETURN op_char_118)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_119 :: char where [simp]: \<open>op_char_119 = CHR 0x77\<close> (* w *)
sepref_register op_char_119
lemma [def_pat_rules]: \<open>Char$True$True$True$False$True$True$True$False \<equiv> op_char_119\<close> by simp
lemma op_char_119_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x77), uncurry0 (RETURN op_char_119)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_120 :: char where [simp]: \<open>op_char_120 = CHR 0x78\<close> (* x *)
sepref_register op_char_120
lemma [def_pat_rules]: \<open>Char$False$False$False$True$True$True$True$False \<equiv> op_char_120\<close> by simp
lemma op_char_120_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x78), uncurry0 (RETURN op_char_120)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_121 :: char where [simp]: \<open>op_char_121 = CHR 0x79\<close> (* y *)
sepref_register op_char_121
lemma [def_pat_rules]: \<open>Char$True$False$False$True$True$True$True$False \<equiv> op_char_121\<close> by simp
lemma op_char_121_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x79), uncurry0 (RETURN op_char_121)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_122 :: char where [simp]: \<open>op_char_122 = CHR 0x7A\<close> (* z *)
sepref_register op_char_122
lemma [def_pat_rules]: \<open>Char$False$True$False$True$True$True$True$False \<equiv> op_char_122\<close> by simp
lemma op_char_122_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x7A), uncurry0 (RETURN op_char_122)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_123 :: char where [simp]: \<open>op_char_123 = CHR 0x7B\<close> (* { *)
sepref_register op_char_123
lemma [def_pat_rules]: \<open>Char$True$True$False$True$True$True$True$False \<equiv> op_char_123\<close> by simp
lemma op_char_123_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x7B), uncurry0 (RETURN op_char_123)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_124 :: char where [simp]: \<open>op_char_124 = CHR 0x7C\<close> (* | *)
sepref_register op_char_124
lemma [def_pat_rules]: \<open>Char$False$False$True$True$True$True$True$False \<equiv> op_char_124\<close> by simp
lemma op_char_124_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x7C), uncurry0 (RETURN op_char_124)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_125 :: char where [simp]: \<open>op_char_125 = CHR 0x7D\<close> (* } *)
sepref_register op_char_125
lemma [def_pat_rules]: \<open>Char$True$False$True$True$True$True$True$False \<equiv> op_char_125\<close> by simp
lemma op_char_125_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x7D), uncurry0 (RETURN op_char_125)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

definition op_char_126 :: char where [simp]: \<open>op_char_126 = CHR 0x7E\<close> (* ~ *)
sepref_register op_char_126
lemma [def_pat_rules]: \<open>Char$False$True$True$True$True$True$True$False \<equiv> op_char_126\<close> by simp
lemma op_char_126_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0x7E), uncurry0 (RETURN op_char_126)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by (rule char_const_hnr) eval

section \<open>Tests\<close>

experiment
begin

text \<open>The table route must carry a literal on its own: with the bit-blasting
  constructor rule removed, synthesis still succeeds.\<close>

context
  notes [sepref_fr_rules del] = asciichar_of_holchar_hnr
begin

sepref_definition char_tab_test is \<open>uncurry0 (RETURN (CHR ''-''))\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by sepref

sepref_definition char_tab_test_nl is \<open>uncurry0 (RETURN (CHR 0x0A))\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by sepref

end

text \<open>A character outside the table still synthesizes via the constructor route.\<close>

sepref_definition char_nontab_test is \<open>uncurry0 (RETURN (CHR 0xC8))\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by sepref

end

end
