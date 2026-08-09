theory Char_Assn 
  imports Isabelle_LLVM.IICF 
begin

text \<open>We need to tell sepref how to relate @{typ \<open>char\<close>} and @{typ \<open>8 word\<close>}\<close>

definition char_of_word :: \<open>8 word \<Rightarrow> char\<close> where
  \<open>char_of_word \<equiv> char_of \<circ> unat\<close>

definition char_rel :: \<open>(8 word \<times> char) set\<close> where
  \<open>char_rel \<equiv> br char_of_word (\<lambda>_. True)\<close>

definition \<open>char_assn \<equiv> pure char_rel\<close>

lemma char_assn_pure[safe_constraint_rules]: \<open>is_pure char_assn\<close>
  unfolding char_assn_def by simp

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

definition less_eq_char :: \<open>char \<Rightarrow> char \<Rightarrow> bool\<close> where
  \<open>less_eq_char c d = (((of_char c) :: nat) \<le> of_char d)\<close>

definition less_char :: \<open>char \<Rightarrow> char \<Rightarrow> bool\<close> where
  \<open>less_char c d = (((of_char c) :: nat) < of_char d)\<close>

global_interpretation char: linorder less_eq_char less_char
  using linorder_char
  unfolding linorder_class_def class.linorder_def
    less_eq_char_def[symmetric] less_char_def[symmetric]
    class.order_def order_class_def
    class.preorder_def preorder_class_def
    ord_class_def
  apply auto
  done

instantiation char :: linorder
begin
definition less_eq_char_inst: \<open>(c :: char) \<le> d \<longleftrightarrow> less_eq_char c d\<close>
definition less_char_inst: \<open>(c :: char) < d \<longleftrightarrow> less_char c d\<close>
instance
  by standard
    (auto simp: less_eq_char_inst less_char_inst less_eq_char_def less_char_def)
end

lemma char_lt_is_cmp_op: "char_word.is_cmp_op ll_icmp_ult (<) (<)"
  apply (rule char_word.is_cmp_opI)
  unfolding ll_icmp_ult_def op_lift_cmp_def char_of_word_def
  apply (simp add: from_bool_lint_conv word_to_lint_ult)
  using unat_of_char_mod
  by (metis comp_eq_dest_lhs less_char_def less_char_inst of_char_of word_less_nat_alt)

lemma char_le_is_cmp_op: "char_word.is_cmp_op ll_icmp_ule (\<le>) (\<le>)"
  apply (rule char_word.is_cmp_opI)
  unfolding ll_icmp_ule_def op_lift_cmp_def char_of_word_def
  apply (simp add: from_bool_lint_conv word_to_lint_ule)
  using unat_of_char_mod 
  by (metis comp_eq_dest_lhs less_char_def less_char_inst linorder_not_le of_char_of word_less_eq_iff_unsigned)


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

lemma char_of_word_inj: \<open>char_of_word a = char_of_word b \<longleftrightarrow> a = b\<close>
proof
  assume \<open>char_of_word a = char_of_word b\<close>
  hence \<open>(of_char (char_of_word a) :: nat) = of_char (char_of_word b)\<close> by simp
  hence \<open>unat a = unat b\<close>
    unfolding char_of_word_def by (simp add: of_char_of unat_of_char_mod)
  thus \<open>a = b\<close> by (simp add: word_unat_eq_iff)
qed simp

lemma char_of_word_less: \<open>char_of_word c < char_of_word c' \<longleftrightarrow> c < c'\<close>
  using unat_of_char_mod
  by (meson char_lt_is_cmp_op char_word.is_cmp_op_def)

context begin
interpretation llvm_prim_arith_setup .

lemma char_eq_rule:
  \<open>llvm_htriple (char_assn a c ** char_assn a' c') (ll_icmp_eq c c')
    (\<lambda>r. char_assn a c ** char_assn a' c' ** \<upharpoonleft>bool.assn (a = a') r)\<close>
  unfolding char_assn_def char_rel_def
  supply [simp] = pure_def in_br_conv bool.assn_def char_of_word_inj
  by vcg

lemma char_lt_rule:
  \<open>llvm_htriple (char_assn a c ** char_assn a' c') (ll_icmp_ult c c')
    (\<lambda>r. char_assn a c ** char_assn a' c' ** \<upharpoonleft>bool.assn (a < a') r)\<close>
  unfolding char_assn_def char_rel_def
  supply [simp] = pure_def in_br_conv bool.assn_def char_of_word_less
  by vcg

end

sepref_register \<open>(=) :: char \<Rightarrow> char \<Rightarrow> bool\<close>
sepref_register \<open>(<) :: char \<Rightarrow> char \<Rightarrow> bool\<close>
sepref_register \<open>(\<le>) :: char \<Rightarrow> char \<Rightarrow> bool\<close>
sepref_register op_neq_char: "op_neq :: char \<Rightarrow> _"

section \<open>Producing Chars (HOL \<open>Char\<close> Constructor)\<close>

text \<open>String literals elaborate into @{term \<open>Char b0 b1 b2 b3 b4 b5 b6 b7\<close>} constructor
  applications over eight booleans (least significant bit first). To let sepref synthesize
  them, we implement the constructor generically: zero-extend each 1-bit word to 8 bits,
  shift it into position, and or everything together. At literal call sites the arguments
  are constants, so LLVM constant-folds the chain into a single \<open>i8\<close> constant.\<close>

definition asciichar_of_holchar ::
  \<open>1 word \<Rightarrow> 1 word \<Rightarrow> 1 word \<Rightarrow> 1 word \<Rightarrow> 1 word \<Rightarrow> 1 word \<Rightarrow> 1 word \<Rightarrow> 1 word \<Rightarrow> 8 word llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>asciichar_of_holchar b0 b1 b2 b3 b4 b5 b6 b7 \<equiv> doM {
    x0 \<leftarrow> ll_zext b0 TYPE(8 word);
    x1 \<leftarrow> ll_zext b1 TYPE(8 word);
    x2 \<leftarrow> ll_zext b2 TYPE(8 word);
    x3 \<leftarrow> ll_zext b3 TYPE(8 word);
    x4 \<leftarrow> ll_zext b4 TYPE(8 word);
    x5 \<leftarrow> ll_zext b5 TYPE(8 word);
    x6 \<leftarrow> ll_zext b6 TYPE(8 word);
    x7 \<leftarrow> ll_zext b7 TYPE(8 word);
    x1 \<leftarrow> ll_shl x1 1;
    x2 \<leftarrow> ll_shl x2 2;
    x3 \<leftarrow> ll_shl x3 3;
    x4 \<leftarrow> ll_shl x4 4;
    x5 \<leftarrow> ll_shl x5 5;
    x6 \<leftarrow> ll_shl x6 6;
    x7 \<leftarrow> ll_shl x7 7;
    r \<leftarrow> ll_or x0 x1;
    r \<leftarrow> ll_or r x2;
    r \<leftarrow> ll_or r x3;
    r \<leftarrow> ll_or r x4;
    r \<leftarrow> ll_or r x5;
    r \<leftarrow> ll_or r x6;
    r \<leftarrow> ll_or r x7;
    Mreturn r
  }\<close>

lemma word1_exhaust: \<open>b = 0 \<or> b = 1\<close> for b :: \<open>1 word\<close>
proof -
  have \<open>unat b < 2\<close>
    using unat_lt2p[of b] by simp
  then have \<open>unat b = 0 \<or> unat b = 1\<close>
    by linarith
  then show ?thesis
    by (metis unsigned_0 unsigned_1 word_unat_eq_iff)
qed

lemma bit_word1_iff: \<open>bit (b :: 1 word) n \<longleftrightarrow> n = 0 \<and> b \<noteq> 0\<close>
  using word1_exhaust[of b] by (cases n) (auto simp: bit_0 dest: bit_imp_le_length)

text \<open>The ambient simpset rewrites \<open><< 1\<close> to \<open>* 2\<close>, so this operand needs its own bit rule.
  Proved by exhausting the two values of the 1-word (simp re-normalizes \<open>push_bit\<close> back
  to \<open>* 2\<close>, so the bit-algebraic route is not available here).\<close>
lemma bit_ucast18_double: \<open>bit (UCAST(1 \<rightarrow> 8) (b :: 1 word) * 2) n \<longleftrightarrow> n = 1 \<and> b \<noteq> 0\<close>
proof (cases \<open>b = 0\<close>)
  case True
  then show ?thesis by simp
next
  case False
  with word1_exhaust[of b] have b1: \<open>b = 1\<close> by simp
  have \<open>bit (2 :: 8 word) n \<longleftrightarrow> n = 1\<close>
    by (cases n) (auto simp: bit_0 bit_Suc bit_1_iff)
  with b1 show ?thesis by simp
qed

lemma bit_ucast18: \<open>bit (UCAST(1 \<rightarrow> 8) (b :: 1 word)) n \<longleftrightarrow> n = 0 \<and> b \<noteq> 0\<close>
  by (auto simp: bit_ucast_iff bit_word1_iff)

lemma word1_lsb: \<open>lsb (b :: 1 word) \<longleftrightarrow> b \<noteq> 0\<close>
  using word1_exhaust[of b] by auto

lemma bit_ucast18_shiftl: \<open>bit (UCAST(1 \<rightarrow> 8) (b :: 1 word) << k) n \<longleftrightarrow> n = k \<and> k < 8 \<and> b \<noteq> 0\<close>
  by (auto simp: bit_shiftl_word_iff bit_ucast18)

text \<open>The assembled byte has exactly the constructor's booleans as bits. The statement
  is normalized to the shape the ambient simpset leaves in the vcg goal: left-nested
  or-chain, \<open><< 1\<close> already rewritten to \<open>* 2\<close>, and \<open>to_bool\<close> unfolded to \<open>\<noteq> 0\<close>.
  The proof must not unfold to \<open>push_bit\<close> (the ambient simpset normalizes it back,
  overflowing the simplifier); only atom-level \<open>bit\<close> rules are used.\<close>
lemma asciichar_of_holchar_correct:
  fixes b0 b1 b2 b3 b4 b5 b6 b7 :: \<open>1 word\<close>
  shows \<open>char_of_word
      (((((((UCAST(1 \<rightarrow> 8) b0 OR UCAST(1 \<rightarrow> 8) b1 * 2) OR (UCAST(1 \<rightarrow> 8) b2 << 2))
        OR (UCAST(1 \<rightarrow> 8) b3 << 3)) OR (UCAST(1 \<rightarrow> 8) b4 << 4)) OR (UCAST(1 \<rightarrow> 8) b5 << 5))
        OR (UCAST(1 \<rightarrow> 8) b6 << 6)) OR (UCAST(1 \<rightarrow> 8) b7 << 7))
    = Char (b0 \<noteq> 0) (b1 \<noteq> 0) (b2 \<noteq> 0) (b3 \<noteq> 0) (b4 \<noteq> 0) (b5 \<noteq> 0) (b6 \<noteq> 0) (b7 \<noteq> 0)\<close>
  unfolding char_of_word_def comp_apply char_of_def
  by (simp add: bit_unsigned_iff bit_or_iff bit_ucast18 bit_ucast18_double bit_ucast18_shiftl
      bit_word1_iff word1_lsb)

sepref_register Char

text \<open>The library's @{thm norm_RETURN_o} (in \<open>to_hnr_post\<close>) only normalizes
  \<open>(RETURN o\<dots>o f)$x$\<dots>\<close> heads up to arity 5; the 8-ary constructor needs its own rule,
  otherwise the \<open>sepref_fr_rules\<close> attribute rejects the rule with "Invalid abstract head".\<close>
lemma norm_RETURN_o8[to_hnr_post]:
  \<open>\<And>f. (\<lambda>x y z a b. RETURN ooo f x y z a b)$x$y$z$a$b$c$d$e = (RETURN$(f$x$y$z$a$b$c$d$e))\<close>
  by auto

context begin
interpretation llvm_prim_arith_setup .

lemma asciichar_of_holchar_hnr[sepref_fr_rules]:
  \<open>(uncurry7 asciichar_of_holchar, uncurry7 (RETURN oooooooo Char))
    \<in> bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a
      bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  unfolding asciichar_of_holchar_def char_assn_def
  supply [simp] = is_up' pure_def in_br_conv char_rel_def bool1_rel_def bool.rel_def
  apply sepref_to_hoare
  apply vcg (* very slow *)
  by (simp add: asciichar_of_holchar_correct ENTAILS_def entails_def
      sep_algebra_simps sep_conj_exists pred_lift_extract_simps)

end

experiment
begin

sepref_definition char_lit_test is \<open>uncurry0 (RETURN (CHR ''a''))\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by sepref

end

section \<open>Hashing of Chars\<close>
(* As desribed in https://en.wikipedia.org/wiki/Fowler%E2%80%93Noll%E2%80%93Vo_hash_function *)
abbreviation \<open>fnv_offset \<equiv> (0xcbf29ce484222325 :: 64 word)\<close>
abbreviation \<open>fnv_prime \<equiv> (0x00000100000001b3 :: 64 word)\<close>

text \<open>Upcast from a character to the 64-bit hash domain.\<close>

definition w64_of_char :: \<open>char \<Rightarrow> 64 word\<close> where
  \<open>w64_of_char c \<equiv> of_nat (of_char c)\<close>

sepref_register w64_of_char

lemma w64_of_char_ucast: \<open>w64_of_char (char_of_word c) = UCAST(8 \<rightarrow> 64) c\<close>
proof -
  have \<open>UCAST(8 \<rightarrow> 64) c = of_nat (unat c)\<close>
    by simp
  then show ?thesis
    unfolding w64_of_char_def char_of_word_def
    by (simp add: of_char_of unat_of_char_mod)
qed

context begin
interpretation llvm_prim_arith_setup .

lemma w64_of_char_hnr[sepref_fr_rules]:
  \<open>(\<lambda>c. ll_zext c TYPE(64 word), RETURN o w64_of_char)
    \<in> char_assn\<^sup>k \<rightarrow>\<^sub>a word_assn' TYPE(64)\<close>
  supply [simp] = is_up' char_assn_def char_rel_def in_br_conv pure_def
    w64_of_char_ucast
  apply sepref_to_hoare
  by vcg

end

definition \<open>fnv1a_of_char c \<equiv> (fnv_offset XOR w64_of_char c) * fnv_prime\<close>

sepref_def fnv1a_of_char_impl is \<open>RETURN o fnv1a_of_char\<close>
  :: \<open>char_assn\<^sup>k \<rightarrow>\<^sub>a (word_assn' TYPE(64))\<close>
  unfolding fnv1a_of_char_def
  by sepref_dbg_keep  

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

end
