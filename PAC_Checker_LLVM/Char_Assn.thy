theory Char_Assn 
  imports Isabelle_LLVM.IICF 
begin

text \<open>We need to tell sepref how to relate @{typ \<open>char\<close>} and @{typ \<open>8 word\<close>}\<close>

definition char_of_nat :: \<open>nat \<Rightarrow> char\<close> where \<open>char_of_nat = char_of\<close>
definition char_of_nat_invar :: \<open>nat \<Rightarrow> bool\<close> where \<open>char_of_nat_invar n = (n < 256)\<close>
definition \<open>char_nat_rel = br char_of_nat char_of_nat_invar\<close>
abbreviation \<open>w8_assn \<equiv> unat_assn' TYPE(8)\<close>

definition char_rel :: \<open>(8 word \<times> char) set\<close> where
  \<open>char_rel = unat_rel O char_nat_rel\<close>

abbreviation char_assn :: \<open>char \<Rightarrow> 8 word \<Rightarrow> assn\<close> where
  \<open>char_assn \<equiv> pure char_rel\<close>

lemmas char_rel_norm[fcomp_norm_unfold] = char_rel_def[symmetric]

lemma char_assn_alt: \<open>hr_comp w8_assn char_nat_rel = char_assn\<close>
  by (simp add: char_rel_def hr_comp_pure)

lemma char_assn_pure[safe_constraint_rules]: \<open>is_pure char_assn\<close>
  by simp
  
definition char_of_word :: \<open>8 word \<Rightarrow> char\<close> where
  \<open>char_of_word \<equiv> (char_of :: nat \<Rightarrow> char) \<circ> (unat :: 8 word \<Rightarrow> nat)\<close>

lemma unat_of_char_mod: \<open>unat (a :: 8 word) mod 256 = unat a\<close>
proof -
  have \<open>unat a < 256\<close>
    by (rule less_le_trans[OF unat_lt2p]) simp
  then show ?thesis
    by simp
qed

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

sepref_def char_eq_impl is \<open>uncurry (RETURN oo ((=) :: nat \<Rightarrow> nat \<Rightarrow> bool))\<close>
  :: \<open>(unat_assn' TYPE(8))\<^sup>k *\<^sub>a (unat_assn' TYPE(8))\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

lemma char_eq_fref: 
  \<open>(uncurry (RETURN oo (=)), uncurry (RETURN oo (=)))
  \<in> char_nat_rel \<times>\<^sub>r char_nat_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) 
     (auto simp: char_nat_rel_def in_br_conv
                 char_of_nat_def char_of_nat_invar_def)

lemmas char_eq_hnr[sepref_fr_rules] =
  char_eq_impl.refine[FCOMP char_eq_fref]

lemma of_char_char_of_nat:
  \<open>char_of_nat_invar n \<Longrightarrow> (of_char (char_of_nat n) :: nat) = n\<close>
  by (simp add: char_of_nat_def char_of_nat_invar_def)

lemma char_of_nat_inj:
  \<open>char_of_nat_invar a \<Longrightarrow> char_of_nat_invar b \<Longrightarrow>
    (char_of_nat a = char_of_nat b) \<longleftrightarrow> a = b\<close>
  by (metis of_char_char_of_nat)

lemmas char_nat_rel_simps =
  char_nat_rel_def in_br_conv of_char_char_of_nat char_of_nat_inj
  less_char_inst less_eq_char_inst less_char_def less_eq_char_def

sepref_def char_ne_impl is \<open>uncurry (RETURN oo (op_neq :: nat \<Rightarrow> nat \<Rightarrow> bool))\<close>
  :: \<open>w8_assn\<^sup>k *\<^sub>a w8_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

sepref_def char_lt_impl is \<open>uncurry (RETURN oo ((<) :: nat \<Rightarrow> nat \<Rightarrow> bool))\<close>
  :: \<open>w8_assn\<^sup>k *\<^sub>a w8_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

sepref_def char_le_impl is \<open>uncurry (RETURN oo ((\<le>) :: nat \<Rightarrow> nat \<Rightarrow> bool))\<close>
  :: \<open>w8_assn\<^sup>k *\<^sub>a w8_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

lemma char_ne_fref:
  \<open>(uncurry (RETURN oo op_neq), uncurry (RETURN oo op_neq))
  \<in> char_nat_rel \<times>\<^sub>r char_nat_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: char_nat_rel_simps)

lemma char_lt_fref:
  \<open>(uncurry (RETURN oo (<)), uncurry (RETURN oo (<)))
  \<in> char_nat_rel \<times>\<^sub>r char_nat_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: char_nat_rel_simps)

lemma char_le_fref:
  \<open>(uncurry (RETURN oo (\<le>)), uncurry (RETURN oo (\<le>)))
  \<in> char_nat_rel \<times>\<^sub>r char_nat_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: char_nat_rel_simps)

lemmas char_ne_hnr[sepref_fr_rules] = char_ne_impl.refine[FCOMP char_ne_fref]
lemmas char_lt_hnr[sepref_fr_rules] = char_lt_impl.refine[FCOMP char_lt_fref]
lemmas char_le_hnr[sepref_fr_rules] = char_le_impl.refine[FCOMP char_le_fref]

lemma char_assn_mk_free[sepref_frame_free_rules]:
  \<open>MK_FREE char_assn (\<lambda>_. Mreturn ())\<close>
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
  by (metis char_of_word_def comp_apply less_char_def less_char_inst of_char_of word_less_iff_unsigned)

context begin
interpretation llvm_prim_arith_setup .

lemma char_eq_rule:
  \<open>llvm_htriple (char_assn a c ** char_assn a' c') (ll_icmp_eq c c')
    (\<lambda>r. char_assn a c ** char_assn a' c' ** \<upharpoonleft>bool.assn (a = a') r)\<close>
  unfolding char_rel_def
  supply [simp] = pure_def in_br_conv bool.assn_def char_of_word_inj
                  char_nat_rel_def char_of_nat_def char_of_nat_invar_def
  apply vcg
  apply (auto simp: ENTAILS_def entails_def sep_algebra_simps)
  apply (metis in_br_conv unat.rel_def unat_rel_def word_unat.Rep_inverse)
  apply (metis in_br_conv unat.rel_def unat_rel_def)
  done
  

lemma char_lt_rule:
  \<open>llvm_htriple (char_assn a c ** char_assn a' c') (ll_icmp_ult c c')
    (\<lambda>r. char_assn a c ** char_assn a' c' ** \<upharpoonleft>bool.assn (a < a') r)\<close>
  unfolding char_rel_def
  supply [simp] = pure_def in_br_conv bool.assn_def char_of_word_less
                  char_nat_rel_def char_of_nat_def char_of_nat_invar_def
  apply vcg
  apply (auto simp: ENTAILS_def entails_def sep_algebra_simps)
  apply (simp add: less_char_def less_char_inst unat.rel_def unat_arith_simps(2) unat_rel_def)
  apply (simp add: less_char_def less_char_inst unat.rel_def unat_arith_simps(2) unat_rel_def)
  done

end

sepref_register \<open>(=) :: char \<Rightarrow> char \<Rightarrow> bool\<close>
sepref_register \<open>(<) :: char \<Rightarrow> char \<Rightarrow> bool\<close>
sepref_register \<open>(\<le>) :: char \<Rightarrow> char \<Rightarrow> bool\<close>
sepref_register op_neq_char: "op_neq :: char \<Rightarrow> _"

section \<open>Producing Chars (HOL \<open>Char\<close> Constructor)\<close>

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

lemma char_of_word_in_char_rel_raw:
  \<open>(w, char_of_word w) \<in> br unat (\<lambda>_. True) O br char_of char_of_nat_invar\<close>
proof -
  have \<open>unat w < 256\<close>
    by (rule less_le_trans[OF unat_lt2p]) simp
  then show ?thesis
    by (auto simp: in_br_conv char_of_word_def char_of_nat_invar_def
      intro!: relcompI[of w \<open>unat w\<close>])
qed

lemma char_of_word_in_char_rel:
  \<open>(w, char_of_word w) \<in> char_rel\<close>
  unfolding char_rel_def
  by (simp add: Char_Assn.char_of_nat_def char_nat_rel_def char_of_word_in_char_rel_raw unat.rel_def unat_rel_def)

sepref_register Char

lemma norm_RETURN_o8[to_hnr_post]:
  \<open>\<And>f. (\<lambda>x y z a b. RETURN ooo f x y z a b)$x$y$z$a$b$c$d$e = (RETURN$(f$x$y$z$a$b$c$d$e))\<close>
  by auto

context begin
interpretation llvm_prim_arith_setup .

lemma asciichar_of_holchar_hnr[sepref_fr_rules]:
  \<open>(uncurry7 asciichar_of_holchar, uncurry7 (RETURN oooooooo Char))
    \<in> bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a
      bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  unfolding asciichar_of_holchar_def
  supply [simp] = is_up' pure_def in_br_conv char_rel_def bool1_rel_def bool.rel_def
  apply sepref_to_hoare
  apply vcg (* very slow *)
  apply (simp add: asciichar_of_holchar_correct ENTAILS_def entails_def
        sep_algebra_simps sep_conj_exists pred_lift_extract_simps char_nat_rel_def
        in_br_conv char_of_nat_def char_of_nat_invar_def unat_rel_def unat.rel_def)
  apply (simp add: asciichar_of_holchar_correct[symmetric] char_of_word_in_char_rel_raw)
  done
  
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

lemma char_of_word_hnr[sepref_fr_rules]:
  \<open>(Mreturn, RETURN o char_of_word) \<in> word_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  apply (sepref_to_hoare; vcg)
  apply (auto simp: sep_algebra_simps ENTAILS_def entails_def char_rel_def)
  using char_of_word_in_char_rel char_rel_def by fastforce
  
context begin
interpretation llvm_prim_arith_setup .

lemma w64_of_char_hnr[sepref_fr_rules]:
  \<open>(\<lambda>c. ll_zext c TYPE(64 word), RETURN o w64_of_char)
    \<in> char_assn\<^sup>k \<rightarrow>\<^sub>a word_assn' TYPE(64)\<close>
  supply [simp] = is_up' char_rel_def in_br_conv pure_def
    w64_of_char_ucast char_of_word_in_char_rel_raw char_nat_rel_def
  apply (sepref_to_hoare; vcg)
  apply (auto simp: sep_algebra_simps ENTAILS_def entails_def
          char_of_nat_def)
  by (simp add: char_of_nat_invar_def unat.rel_def unat_rel_def w64_of_char_def)

end

definition \<open>fnv1a_of_char c \<equiv> (fnv_offset XOR w64_of_char c) * fnv_prime\<close>

sepref_def fnv1a_of_char_impl is \<open>RETURN o fnv1a_of_char\<close>
  :: \<open>char_assn\<^sup>k \<rightarrow>\<^sub>a (word_assn' TYPE(64))\<close>
  unfolding fnv1a_of_char_def
  by sepref_dbg_keep

experiment
begin

sepref_definition char_lit_test is \<open>uncurry0 (RETURN (CHR ''a''))\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
  by sepref

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

end
