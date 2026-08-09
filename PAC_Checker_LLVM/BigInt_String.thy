theory BigInt_String
  imports
    BigInt_LLVM.LLVM_CodeGen_Signed
    PAC_Checker_LLVM_old.IICF_Open_List
begin

text \<open>In this theory we implement conversions from and to strings\<close>

section \<open>Basic High-Level Relations\<close>
type_synonym str = \<open>char list\<close>

text \<open>First we fix define the semantics/values of characters. 
  We assume ASCII encoded characters. We only accept characters 0-9, all other characters
  have no defined value.\<close>

text \<open>ASCII numerals have values 48-57 (assuming unsigned 8 words)\<close>
definition is_ascii_num :: \<open>char \<Rightarrow> bool\<close> where
  \<open>is_ascii_num c \<equiv> 48 \<le> (of_char :: char \<Rightarrow> nat) c \<and> (of_char :: char \<Rightarrow> nat) c \<le> 57\<close>

definition char_val :: \<open>char \<Rightarrow> nat\<close> where
  \<open>char_val c = (of_char c) - 48\<close>

definition \<open>ascii_char_nat_rel \<equiv> br char_val is_ascii_num\<close>

definition is_ascii_num_str :: \<open>str \<Rightarrow> bool\<close> where
  \<open>is_ascii_num_str ss \<equiv> ss \<noteq> [] \<and> foldl (\<lambda>acc d. acc \<and> is_ascii_num d) True ss\<close>

text \<open>Note that for strings, other than for big integers, we use a big endian encoding\<close>
definition str_val :: \<open>str \<Rightarrow> nat\<close> where
  \<open>str_val ss \<equiv>
    let exps = map nat (rev [0 .. int (length ss-1)]) in
    foldl (\<lambda>acc (exp, c). acc + 10^exp * char_val c) 0 (zip exps ss)\<close>

definition \<open>ascii_str_nat_rel \<equiv> br str_val is_ascii_num_str\<close>

lemma ascii_num_str_nempty:
  assumes \<open>is_ascii_num_str ss\<close>
    shows \<open>ss \<noteq> []\<close>
  unfolding is_ascii_num_str_def using assms is_ascii_num_str_def by blast

section \<open>Base 10 Conversion\<close>
text \<open>Our limbs are given as 64-bit numbers, we now want to convert that to base 10
  lists of characters. For now, we don't do a generic conversion, but a specialized
  one for base 10 specifically.\<close>

text \<open>First, we have to implement division by 10 for our limbs.
  TODO: Mihai Spinei is also working on division I think, we might at some point
  want to merge efforts...\<close>

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

(* I don't know how to instanciate divmod to nat... *)
definition \<open>divmod_nat \<equiv> \<lambda>(a::nat) (b::nat). (a div b, a mod b)\<close>

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

section \<open>LLVM Synthesis\<close>

subsection \<open>The 128-bit divide-two-by-one primitive\<close>

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
  \<comment> \<open>the shifted high limb, using \<open>unat (push_bit n w) = (2^n * unat w) mod 2^len\<close>\<close>
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


subsection \<open>The long-division loop\<close>

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

section \<open>Big Int to String conversion\<close>

text \<open>On the HOL side, we want to reason on @{term char}, but
  on the LLVM side we work with @{term \<open>8 word\<close>}, so we first
  need to define a bijective mapping between the two.\<close>

definition \<open>char_of_word (w :: 8 word) \<equiv> char_of (unat w)\<close>
definition \<open>word_of_char (c :: char) \<equiv> (of_char :: char \<Rightarrow> 8 word) c\<close>
definition \<open>char_word_rel = br word_of_char (\<lambda>_. True)\<close>
definition \<open>word_char_rel = br char_of_word (\<lambda>_. True)\<close>

lemma unat_of_char_8word: \<open>unat (of_char c :: 8 word) = (of_char c :: nat) mod 256\<close>
proof -
  have \<open>(of_char c :: 8 word) = of_nat (of_char c :: nat)\<close>
    by (simp add: of_nat_of_char)
  then have \<open>unat (of_char c :: 8 word) = unat (of_nat (of_char c :: nat) :: 8 word)\<close>
    by simp
  also have \<open>\<dots> = (of_char c :: nat) mod 2 ^ LENGTH(8)\<close>
    by (simp add: unat_of_nat)
  finally show ?thesis by simp
qed

lemma char_of_word_word_of_char: \<open>char_of_word (word_of_char c) = c\<close>
  unfolding char_of_word_def word_of_char_def
  by (simp add: unat_of_char_8word)

lemma word_of_char_char_of_word: \<open>word_of_char (char_of_word w) = w\<close>
  unfolding char_of_word_def word_of_char_def
proof -
  have wlt: \<open>unat w < 256\<close> using unsigned_less[of w] by simp
  have \<open>unat (of_char (char_of (unat w)) :: 8 word) = unat w\<close>
    using wlt by (simp add: unat_of_char_8word)
  then show \<open>(of_char (char_of (unat w)) :: 8 word) = w\<close>
    by (rule unsigned_word_eqI)
qed

lemma char_of_8word_id:
  shows \<open>char_of_word o word_of_char = id\<close>
    and \<open>word_of_char o char_of_word = id\<close>
  by (simp_all add: fun_eq_iff char_of_word_word_of_char word_of_char_char_of_word)

definition dec_val :: \<open>64 word list \<Rightarrow> nat\<close> where
  \<open>dec_val ds = foldl (\<lambda>acc d. acc * 10 + unat d) 0 ds\<close>

lemma dec_val_Nil[simp]: \<open>dec_val [] = 0\<close>
  by (simp add: dec_val_def)

lemma foldl_dec_shift:
  fixes init :: nat and ds :: \<open>64 word list\<close>
  shows \<open>foldl (\<lambda>acc d. acc * 10 + unat d) init ds
     = init * 10 ^ length ds + foldl (\<lambda>acc d. acc * 10 + unat d) 0 ds\<close>
proof (induction ds arbitrary: init)
  case Nil then show ?case by simp
next
  case (Cons d ds)
  have L: \<open>foldl (\<lambda>acc d. acc * 10 + unat d) init (d # ds)
      = (init * 10 + unat d) * 10 ^ length ds + foldl (\<lambda>acc d. acc * 10 + unat d) 0 ds\<close>
    using Cons.IH[of \<open>init * 10 + unat d\<close>] by simp
  have R: \<open>foldl (\<lambda>acc d. acc * 10 + unat d) 0 (d # ds)
      = unat d * 10 ^ length ds + foldl (\<lambda>acc d. acc * 10 + unat d) 0 ds\<close>
    using Cons.IH[of \<open>unat d\<close>] by simp
  show ?case using L R by (simp add: algebra_simps)
qed

lemma dec_val_Cons: \<open>dec_val (r # res) = unat r * 10 ^ length res + dec_val res\<close>
  unfolding dec_val_def using foldl_dec_shift[of \<open>unat r\<close> res] by simp

lemma dec_step_value:
  fixes n :: nat
  shows \<open>(n div 10) * 10 ^ Suc len + (n mod 10) * 10 ^ len = n * 10 ^ len\<close>
proof -
  have expand: \<open>(n div 10) * 10 ^ Suc len + (n mod 10) * 10 ^ len
      = (n div 10 * 10 + n mod 10) * 10 ^ len\<close>
    by (metis add_mult_distrib mult.assoc power_Suc)
  show ?thesis
    unfolding expand by (simp only: div_mult_mod_eq)
qed

lemma big_int_pos_of_nonempty:
  \<open>big_int_invar xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> 0 < big_int_\<alpha> xs\<close>
  using big_int_to_nat_not0[of xs] by (auto simp: big_int_invar_def)

lemma bi_div_by_w64_div10:
  assumes \<open>big_int_invar q\<close>
  shows \<open>bi_div_by_w64 q 10 \<le> SPEC (\<lambda>(q', r).
      big_int_invar q' \<and> big_int_\<alpha> q' = big_int_\<alpha> q div 10 \<and> unat r = big_int_\<alpha> q mod 10)\<close>
proof -
  have r1: \<open>(q, big_int_\<alpha> q) \<in> big_int_rel\<close>
    using assms by (simp add: big_int_rel_def in_br_conv)
  have r2: \<open>((10::limb), (10::nat)) \<in> unat_rel\<close>
    by (simp add: unat_rel_def unat.rel_def in_br_conv)
  have \<open>bi_div_by_w64 q 10
      \<le> \<Down> (big_int_rel \<times>\<^sub>r unat_rel) (RETURN (big_int_\<alpha> q div 10, big_int_\<alpha> q mod 10))\<close>
    using bi_div_by_w64_correct_aux[OF r1 r2] by simp
  also have \<open>\<dots> \<le> SPEC (\<lambda>(q', r).
      big_int_invar q' \<and> big_int_\<alpha> q' = big_int_\<alpha> q div 10 \<and> unat r = big_int_\<alpha> q mod 10)\<close>
    by (auto simp: pw_le_iff refine_pw_simps
        big_int_rel_def unat_rel_def unat.rel_def prod_rel_def in_br_conv)
  finally show ?thesis .
qed

definition dec_of_big_int :: \<open>big_int \<Rightarrow> big_int nres\<close> where
  \<open>dec_of_big_int bi \<equiv> doN {
    ASSERT (big_int_invar bi);
    if big_int_length bi = 0 then RETURN [0]
    else doN {
      (_, res) \<leftarrow> WHILEIT
        (\<lambda>(q, res).
            big_int_invar q
          \<and> (\<forall>d \<in> set res. unat d < 10)
          \<and> big_int_\<alpha> q * 10 ^ length res + dec_val res = big_int_\<alpha> bi)
        (\<lambda>(q, _). 0 < big_int_length q)
        (\<lambda>(q, res). doN {
          (q', r) \<leftarrow> bi_div_by_w64 q 10;
          RETURN (q', r # res)
        })
        (bi, []);
      RETURN res
    }
  }\<close>

lemma dec_of_big_int_correct:
  assumes \<open>big_int_invar bi\<close>
  shows \<open>dec_of_big_int bi \<le> SPEC (\<lambda>ds.
      dec_val ds = big_int_\<alpha> bi \<and> (\<forall>d \<in> set ds. unat d < 10) \<and> ds \<noteq> [])\<close>
  unfolding dec_of_big_int_def big_int_length_def
  apply (refine_vcg
      WHILEIT_rule[where R = \<open>measure (\<lambda>(q, res). big_int_\<alpha> q)\<close>]
      bi_div_by_w64_div10)
  apply simp_all
  subgoal using assms by simp
  subgoal by (simp add: dec_val_Cons)
  subgoal
    by (metis (no_types, lifting) dec_val_Cons div_mod_decomp
    left_add_mult_distrib mult.assoc)
  subgoal
    by (metis big_int_pos_of_nonempty div_less_dividend numeral_One
    numeral_less_iff semiring_norm(76))
  subgoal
    using big_int_to_nat_unique by force
  done

abbreviation \<open>digits_assn \<equiv> os_assn (word_assn' size_t)\<close>

sepref_def dec_of_big_int_impl is \<open>dec_of_big_int\<close>
  :: \<open>bi_aux_assn\<^sup>d \<rightarrow>\<^sub>a digits_assn\<close>
  unfolding dec_of_big_int_def
  apply (annot_snat_const size_t)
  by sepref

section \<open>Digits to ASCII characters\<close>

definition ascii_of_digit :: \<open>64 word \<Rightarrow> 8 word\<close> where
  \<open>ascii_of_digit d = UCAST(64 \<rightarrow> 8) (d + 48)\<close>

lemma of_char_char_of_word: \<open>(of_char (char_of_word w) :: nat) = unat w\<close>
proof -
  have \<open>unat w < 256\<close> using unsigned_less[of w] by simp
  then show ?thesis
    unfolding char_of_word_def by (simp add: of_char_of)
qed

lemma unat_ascii_of_digit:
  assumes \<open>unat d < 10\<close>
  shows \<open>unat (ascii_of_digit d) = unat d + 48\<close>
proof -
  have add: \<open>unat (d + 48) = unat d + 48\<close>
    using assms unat_add_lem[of d 48] by simp
  have \<open>unat (ascii_of_digit d) = (unat d + 48) mod 256\<close>
    unfolding ascii_of_digit_def by (simp add: unat_ucast add)
  also have \<open>\<dots> = unat d + 48\<close> using assms by simp
  finally show ?thesis .
qed

lemma char_of_digit_rel:
  assumes \<open>unat d < 10\<close>
  shows \<open>(char_of_word (ascii_of_digit d), unat d) \<in> ascii_char_nat_rel\<close>
proof -
  have \<open>of_char (char_of_word (ascii_of_digit d)) = unat d + 48\<close>
    using of_char_char_of_word[of \<open>ascii_of_digit d\<close>] unat_ascii_of_digit[OF assms] by simp
  then show ?thesis
    using assms by (auto simp: ascii_char_nat_rel_def in_br_conv char_val_def is_ascii_num_def)
qed

corollary is_ascii_num_char_of_digit:
  \<open>unat d < 10 \<Longrightarrow> is_ascii_num (char_of_word (ascii_of_digit d))\<close>
  using char_of_digit_rel[of d] by (simp add: ascii_char_nat_rel_def in_br_conv)

definition ascii_of_digits :: \<open>64 word list \<Rightarrow> 8 word list\<close> where
  \<open>ascii_of_digits ds = map ascii_of_digit ds\<close>

lemma ascii_of_digits_rel:
  assumes \<open>\<forall>d \<in> set ds. unat d < 10\<close>
  shows \<open>(map char_of_word (ascii_of_digits ds), map unat ds) \<in> \<langle>ascii_char_nat_rel\<rangle>list_rel\<close>
  using assms unfolding ascii_of_digits_def
  by (induction ds) (auto simp: char_of_digit_rel list_rel_def)

lemma foldl_conj_is_ascii_num:
  \<open>foldl (\<lambda>acc d. acc \<and> is_ascii_num d) b ss = (b \<and> (\<forall>c \<in> set ss. is_ascii_num c))\<close>
  by (induction ss arbitrary: b) auto

lemma is_ascii_num_str_ascii_of_digits:
  assumes \<open>\<forall>d \<in> set ds. unat d < 10\<close> and \<open>ds \<noteq> []\<close>
  shows \<open>is_ascii_num_str (map char_of_word (ascii_of_digits ds))\<close>
  using assms unfolding is_ascii_num_str_def ascii_of_digits_def
  by (auto simp: foldl_conj_is_ascii_num is_ascii_num_char_of_digit)

lemma foldl_wval_shift:
  fixes a :: nat
  shows \<open>foldl (\<lambda>acc (e, ch). acc + 10 ^ e * char_val ch) a xs
       = a + foldl (\<lambda>acc (e, ch). acc + 10 ^ e * char_val ch) 0 xs\<close>
proof (induction xs arbitrary: a)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  obtain e ch where x: \<open>x = (e, ch)\<close> by (cases x)
  have L: \<open>foldl (\<lambda>acc (e, ch). acc + 10 ^ e * char_val ch) a (x # xs)
      = (a + 10 ^ e * char_val ch) + foldl (\<lambda>acc (e, ch). acc + 10 ^ e * char_val ch) 0 xs\<close>
    unfolding x using Cons.IH[of \<open>a + 10 ^ e * char_val ch\<close>] by simp
  have R: \<open>foldl (\<lambda>acc (e, ch). acc + 10 ^ e * char_val ch) 0 (x # xs)
      = 10 ^ e * char_val ch + foldl (\<lambda>acc (e, ch). acc + 10 ^ e * char_val ch) 0 xs\<close>
    unfolding x using Cons.IH[of \<open>10 ^ e * char_val ch\<close>] by simp
  show ?case using L R by (simp add: add.assoc)
qed

lemma str_val_Cons:
  \<open>str_val (c # ss) = 10 ^ length ss * char_val c + str_val ss\<close>
proof -
  let ?rest = \<open>map nat (rev [0..int (length ss) - 1])\<close>
  have exps: \<open>map nat (rev [0..int (length ss)]) = length ss # ?rest\<close>
  proof -
    have \<open>[0..int (length ss)] = [0..int (length ss) - 1] @ [int (length ss)]\<close>
      by (rule upto_rec2) simp
    then show ?thesis by simp
  qed
  have rest_eq: \<open>foldl (\<lambda>acc (e, ch). acc + 10 ^ e * char_val ch) 0 (zip ?rest ss) = str_val ss\<close>
  proof (cases \<open>ss = []\<close>)
    case True then show ?thesis by (simp add: str_val_def)
  next
    case False
    then have \<open>1 \<le> length ss\<close> by (cases ss) auto
    then have \<open>?rest = map nat (rev [0..int (length ss - 1)])\<close> by (simp add: of_nat_diff)
    then show ?thesis by (simp add: str_val_def Let_def)
  qed
  have \<open>str_val (c # ss)
      = foldl (\<lambda>acc (e, ch). acc + 10 ^ e * char_val ch) 0 (zip (length ss # ?rest) (c # ss))\<close>
    by (simp add: str_val_def Let_def exps)
  also have \<open>\<dots> = foldl (\<lambda>acc (e, ch). acc + 10 ^ e * char_val ch)
                    (10 ^ length ss * char_val c) (zip ?rest ss)\<close>
    by simp
  also have \<open>\<dots> = 10 ^ length ss * char_val c
                  + foldl (\<lambda>acc (e, ch). acc + 10 ^ e * char_val ch) 0 (zip ?rest ss)\<close>
    by (rule foldl_wval_shift)
  also have \<open>\<dots> = 10 ^ length ss * char_val c + str_val ss\<close>
    by (simp add: rest_eq)
  finally show ?thesis .
qed

lemma str_val_ascii_of_digits:
  assumes \<open>\<forall>d \<in> set ds. unat d < 10\<close>
  shows \<open>str_val (map char_of_word (ascii_of_digits ds)) = dec_val ds\<close>
  using assms
proof (induction ds)
  case Nil then show ?case by (simp add: str_val_def ascii_of_digits_def)
next
  case (Cons d ds)
  have cv: \<open>char_val (char_of_word (ascii_of_digit d)) = unat d\<close>
    using char_of_digit_rel[of d] Cons.prems by (simp add: ascii_char_nat_rel_def in_br_conv)
  show ?case
    using Cons.IH Cons.prems
    by (simp add: ascii_of_digits_def str_val_Cons dec_val_Cons cv)
qed

section \<open>Putting it all together\<close>

definition \<open>print_bi_ascii bi \<equiv> doN{ d \<leftarrow> dec_of_big_int bi; RETURN (ascii_of_digits d) }\<close>

lemma print_bi_ascii_correct:
  assumes \<open>(bi, b) \<in> big_int_rel\<close>
  shows \<open>print_bi_ascii bi \<le> SPEC (\<lambda>bytes. (map char_of_word bytes, b) \<in> ascii_str_nat_rel)\<close>
proof -
  have inv: \<open>big_int_invar bi\<close> and val: \<open>big_int_\<alpha> bi = b\<close>
    using assms by (auto simp: big_int_rel_def in_br_conv)
  show ?thesis
    unfolding print_bi_ascii_def
    apply (refine_vcg dec_of_big_int_correct[OF inv])
    subgoal for ds
      using val by (auto simp: ascii_str_nat_rel_def in_br_conv
          str_val_ascii_of_digits is_ascii_num_str_ascii_of_digits)
    done
qed

abbreviation \<open>ascii_strl_assn \<equiv> os_assn (word_assn' TYPE(8))\<close>

subsection \<open>Fused variant: convert to ASCII inside the division loop\<close>

text \<open>There is no refinment target for @{term \<open>map\<close>}.
  Therefore we do the ascii conversion in the loop body.\<close>
definition print_bi_ascii' :: \<open>big_int \<Rightarrow> 8 word list nres\<close> where
  \<open>print_bi_ascii' bi \<equiv> doN {
    ASSERT (big_int_invar bi);
    if big_int_length bi = 0 then RETURN [ascii_of_digit 0]
    else doN {
      (_, res) \<leftarrow> WHILEIT
        (\<lambda>_. True)
        (\<lambda>(q, _). 0 < big_int_length q)
        (\<lambda>(q, res). doN {
          (q', r) \<leftarrow> bi_div_by_w64 q 10;
          RETURN (q', ascii_of_digit r # res)
        })
        (bi, []);
      RETURN res
    }
  }\<close>

definition \<open>ascii_list_rel \<equiv> {(bytes, digits). bytes = map ascii_of_digit digits}\<close>

lemma print_bi_ascii'_refine_dec:
  \<open>print_bi_ascii' bi \<le> \<Down> ascii_list_rel (dec_of_big_int bi)\<close>
  unfolding print_bi_ascii'_def dec_of_big_int_def
  apply (refine_rcg WHILEIT_refine[where R = \<open>Id \<times>\<^sub>r ascii_list_rel\<close>])
  apply refine_dref_type
  by (auto simp: ascii_list_rel_def conc_Id)

text \<open>For this (functional) relation, dropping down to \<^const>\<open>ascii_list_rel\<close> coincides with mapping
  the conversion over the result.\<close>
lemma conc_ascii_le:
  \<open>\<Down> ascii_list_rel m \<le> m \<bind> (\<lambda>d. RETURN (map ascii_of_digit d))\<close>
  by (auto simp: pw_le_iff refine_pw_simps pw_conc_inres pw_conc_nofail ascii_list_rel_def)

lemma print_bi_ascii'_refine:
  \<open>print_bi_ascii' bi \<le> print_bi_ascii bi\<close>
proof -
  have \<open>print_bi_ascii' bi \<le> \<Down> ascii_list_rel (dec_of_big_int bi)\<close>
    by (rule print_bi_ascii'_refine_dec)
  also have \<open>\<Down> ascii_list_rel (dec_of_big_int bi) \<le> print_bi_ascii bi\<close>
    unfolding print_bi_ascii_def ascii_of_digits_def by (rule conc_ascii_le)
  finally show ?thesis .
qed

lemma print_bi_ascii'_correct:
  assumes \<open>(bi, b) \<in> big_int_rel\<close>
  shows \<open>print_bi_ascii' bi \<le> SPEC (\<lambda>bytes. (map char_of_word bytes, b) \<in> ascii_str_nat_rel)\<close>
  using print_bi_ascii'_refine[of bi] print_bi_ascii_correct[OF assms]
  by (rule order_trans)

subsection \<open>LLVM synthesis\<close>

lemma is_downcast_64_8: \<open>is_down' UCAST(64 \<rightarrow> 8)\<close>
  by (auto simp: is_down')

sepref_register ascii_of_digit

context
begin
  interpretation llvm_prim_arith_setup .
  lemma ascii_of_digit_hnr[sepref_fr_rules]:
    \<open>(\<lambda>w. doM { s \<leftarrow> ll_add w 48; ll_trunc s TYPE(8 word) }, RETURN o ascii_of_digit)
      \<in> limb_assn\<^sup>k \<rightarrow>\<^sub>a word_assn' TYPE(8)\<close>
    supply [simp] = is_downcast_64_8
    unfolding ascii_of_digit_def
    apply sepref_to_hoare
    by vcg
end

sepref_def print_bi_ascii_impl is \<open>print_bi_ascii'\<close>
  :: \<open>bi_aux_assn\<^sup>d \<rightarrow>\<^sub>a ascii_strl_assn\<close>
  unfolding print_bi_ascii'_def
  apply (annot_snat_const size_t)
  by sepref


lemma word_char_list_rel_map:
  \<open>(bytes, map char_of_word bytes) \<in> \<langle>word_char_rel\<rangle>list_rel\<close>
  by (simp add: word_char_rel_def list_rel_def in_br_conv list_all2_map2 list_all2_same)

lemma print_bi_ascii_refine:
  assumes \<open>(bi, b) \<in> big_int_rel\<close>
  shows \<open>print_bi_ascii bi \<le> \<Down> (\<langle>word_char_rel\<rangle>list_rel O ascii_str_nat_rel) (RETURN b)\<close>
proof -
  have \<open>print_bi_ascii bi \<le> SPEC (\<lambda>bytes. (map char_of_word bytes, b) \<in> ascii_str_nat_rel)\<close>
    using assms by (rule print_bi_ascii_correct)
  also have \<open>\<dots> \<le> \<Down> (\<langle>word_char_rel\<rangle>list_rel O ascii_str_nat_rel) (RETURN b)\<close>
    by (auto simp: pw_le_iff refine_pw_simps intro: word_char_list_rel_map)
  finally show ?thesis .
qed

section \<open>Extending to Signed Big Integers\<close>

text \<open>Since printing is implemented destructively, extending to signed version is a fairly simple
  extension...\<close>

abbreviation \<open>ascii_hyphen \<equiv> (45 :: nat)\<close>
abbreviation \<open>char_hyphen \<equiv> (char_of :: nat \<Rightarrow> char) ascii_hyphen\<close>
abbreviation \<open>word_hyphen \<equiv> (of_nat ascii_hyphen) :: 8 word\<close>

lemma word_hyphen_val: \<open>word_hyphen = 0x2D\<close> by auto

lemma word_hyphen_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 45), uncurry0 (RETURN word_hyphen)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a (word_assn' TYPE(8))\<close>
  apply sepref_dbg_keep
  oops

definition int_of_str :: \<open>str \<Rightarrow> int\<close> where
  \<open>int_of_str ss \<equiv> case ss of
    [] \<Rightarrow> undefined
  | (c # cs) \<Rightarrow> (if c = char_hyphen then -int (str_val cs) else int (str_val ss))
  \<close>
definition is_ascii_int :: \<open>str \<Rightarrow> bool\<close> where
  \<open>is_ascii_int ss \<equiv> case ss of
    [] \<Rightarrow> False
  | (c # cs) \<Rightarrow> c = char_hyphen \<and> is_ascii_num_str cs \<and> 0 < str_val cs \<or> is_ascii_num_str ss
\<close>
definition \<open>ascii_str_int_rel \<equiv> br int_of_str is_ascii_int\<close>

lemma of_char_hyphen: \<open>(of_char char_hyphen :: nat) = ascii_hyphen\<close>
  by (simp add: of_char_of)

lemma is_ascii_num_not_hyphen: \<open>is_ascii_num c \<Longrightarrow> c \<noteq> char_hyphen\<close>
  unfolding is_ascii_num_def using of_char_hyphen by auto

lemma ascii_prefix_sign:
  assumes \<open>(ss, i) \<in> ascii_str_int_rel\<close>
  shows \<open>hd ss = char_hyphen \<longleftrightarrow> i < 0\<close>
proof -
  have i_def: \<open>i = int_of_str ss\<close> and inv: \<open>is_ascii_int ss\<close>
    using assms by (auto simp: ascii_str_int_rel_def in_br_conv)
  obtain c cs where ss_eq: \<open>ss = c # cs\<close>
    using inv by (cases ss) (auto simp: is_ascii_int_def)
  show ?thesis
  proof
    assume \<open>hd ss = char_hyphen\<close>
    then have c_hyphen: \<open>c = char_hyphen\<close> by (simp add: ss_eq)
    then have \<open>\<not> is_ascii_num_str ss\<close>
      unfolding is_ascii_num_str_def ss_eq
      by (auto simp: foldl_conj_is_ascii_num dest: is_ascii_num_not_hyphen)
    then have \<open>0 < str_val cs\<close>
      using inv c_hyphen by (auto simp: is_ascii_int_def ss_eq)
    then show \<open>i < 0\<close>
      by (simp add: i_def int_of_str_def ss_eq c_hyphen)
  next
    assume \<open>i < 0\<close>
    then have \<open>c = char_hyphen\<close>
      using i_def by (auto simp: int_of_str_def ss_eq split: if_splits)
    then show \<open>hd ss = char_hyphen\<close> by (simp add: ss_eq)
  qed
qed

lemma int_of_pos_str:
  assumes \<open>i \<ge> 0\<close>
      and \<open>(ss, i) \<in> ascii_str_int_rel\<close>
  shows \<open>int_of_str ss = int (str_val ss)\<close>
proof -
  have \<open>is_ascii_int ss\<close>
    using assms is_ascii_int_def
      by (metis assms(2) ascii_str_int_rel_def in_br_conv)
  then have \<open>ss \<noteq> []\<close>
    using is_ascii_int_def by force
  then obtain s ss' where ss_dest: \<open>ss = s # ss'\<close>
    by (metis \<open>ss \<noteq> []\<close> list.exhaust)
  then have val: \<open>int_of_str ss = (if s = char_hyphen then -int (str_val ss') else int (str_val ss))\<close>
    unfolding int_of_str_def by simp
  have \<open>\<not>(s = char_hyphen)\<close>
    using assms(1) assms(2) ss_dest ascii_prefix_sign
    by force 
  then show ?thesis
    using val by presburger
qed

text \<open>Lifting the unsigned string relation to the signed one: a valid digit string denotes its
  (non-negative) value, and prefixing a hyphen negates a positive value.\<close>

lemma ascii_str_nat_int_pos:
  assumes \<open>(ss, n) \<in> ascii_str_nat_rel\<close>
  shows \<open>(ss, int n) \<in> ascii_str_int_rel\<close>
proof -
  have sv: \<open>str_val ss = n\<close> and num: \<open>is_ascii_num_str ss\<close>
    using assms by (auto simp: ascii_str_nat_rel_def in_br_conv)
  obtain c cs where ss_eq: \<open>ss = c # cs\<close>
    using ascii_num_str_nempty[OF num] by (cases ss) auto
  have \<open>is_ascii_num c\<close>
    using num by (simp add: is_ascii_num_str_def ss_eq foldl_conj_is_ascii_num)
  then have \<open>c \<noteq> char_hyphen\<close> by (rule is_ascii_num_not_hyphen)
  then show ?thesis
    using sv num
    by (simp add: ascii_str_int_rel_def in_br_conv int_of_str_def is_ascii_int_def ss_eq)
qed

lemma ascii_str_nat_int_neg:
  assumes \<open>(ss, n) \<in> ascii_str_nat_rel\<close> and \<open>0 < n\<close>
  shows \<open>(char_hyphen # ss, - int n) \<in> ascii_str_int_rel\<close>
  using assms
  by (simp add: ascii_str_nat_rel_def ascii_str_int_rel_def in_br_conv
      int_of_str_def is_ascii_int_def)

lemma char_of_word_hyphen[simp]: \<open>char_of_word word_hyphen = char_hyphen\<close>
  by (simp add: char_of_word_def unat_of_nat)


definition copy_extr_\<sigma>_impl :: \<open>(64 word \<times> 64 word \<times> 64 word ptr) \<times> 1 word \<Rightarrow> 1 word llM\<close>
  where [llvm_inline]: \<open>copy_extr_\<sigma>_impl \<equiv> \<lambda>(bi, \<sigma>). Mreturn \<sigma>\<close>

(* Note that this little function could have saved a lot of trouble in the signed integer
 * arithmetics. Maybe it's worth to rework some of them... *)
lemma copy_extr_\<sigma>_hnr[sepref_fr_rules]:
  \<open>(copy_extr_\<sigma>_impl, RETURN o \<sigma>) \<in> sbi_aux_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding \<sigma>_def copy_extr_\<sigma>_impl_def
  apply sepref_to_hoare
  by vcg

definition dest_extr_bi :: \<open>signed_big_int \<Rightarrow> big_int nres\<close> where
  \<open>dest_extr_bi sbi \<equiv> (\<lambda>(bi, sign). RETURN bi) sbi\<close>

definition dest_extr_bi_impl
  :: \<open>(64 word \<times> 64 word \<times> 64 word ptr) \<times> 1 word \<Rightarrow> (64 word \<times> 64 word \<times> 64 word ptr) llM\<close>
  where [llvm_inline]: \<open>dest_extr_bi_impl \<equiv> \<lambda>(bi, sign). Mreturn bi\<close>

lemma dest_extr_bi_impl_hnr[sepref_fr_rules]:
  \<open>(dest_extr_bi_impl, dest_extr_bi) \<in> sbi_aux_assn\<^sup>d \<rightarrow>\<^sub>a bi_aux_assn\<close>
  unfolding dest_extr_bi_impl_def dest_extr_bi_def
  apply sepref_to_hoare
  by vcg

definition print_sbi_ascii :: \<open>signed_big_int \<Rightarrow> 8 word list nres\<close> where
  \<open>print_sbi_ascii sbi \<equiv> doN {
    let \<sigma>_in = \<sigma> sbi;
    bi \<leftarrow> dest_extr_bi sbi;
    abs_str \<leftarrow> print_bi_ascii' bi;
    if \<sigma>_in then RETURN (word_hyphen # abs_str) else RETURN abs_str
  }\<close>

sepref_def print_sbi_ascii_impl is \<open>print_sbi_ascii\<close>
  :: \<open>sbi_aux_assn\<^sup>d \<rightarrow>\<^sub>a ascii_strl_assn\<close>
  unfolding print_sbi_ascii_def word_hyphen_val
  by sepref

lemma print_sbi_ascii_correct:
  assumes \<open>(sbi, i) \<in> signed_big_int_rel\<close>
  shows \<open>print_sbi_ascii sbi \<le>
         SPEC (\<lambda>bytes. (map char_of_word bytes, i) \<in> ascii_str_int_rel)\<close>
proof -
  obtain bia sg where sbi_eq: \<open>sbi = (bia, sg)\<close> by (cases sbi)
  have bir: \<open>(bia, nat \<bar>i\<bar>) \<in> big_int_rel\<close>
    using abs_rel[OF assms] by (simp add: sbi_eq limbs_of_def)
  have sg_iff: \<open>sg \<longleftrightarrow> i < 0\<close>
    using signs_rel(2)[OF assms] by (simp add: sbi_eq \<sigma>_def)
  have unf: \<open>print_sbi_ascii sbi = doN {
      abs_str \<leftarrow> print_bi_ascii' bia;
      if sg then RETURN (word_hyphen # abs_str) else RETURN abs_str }\<close>
    unfolding print_sbi_ascii_def dest_extr_bi_def sbi_eq
    by (simp add: \<sigma>_def Let_def)
  show ?thesis
    unfolding unf
  proof (rule specify_left[OF print_bi_ascii'_correct[OF bir]])
    fix bytes
    assume rel: \<open>(map char_of_word bytes, nat \<bar>i\<bar>) \<in> ascii_str_nat_rel\<close>
    show \<open>(if sg then RETURN (word_hyphen # bytes) else RETURN bytes)
          \<le> SPEC (\<lambda>bytes. (map char_of_word bytes, i) \<in> ascii_str_int_rel)\<close>
    proof (cases sg)
      case True
      then have neg: \<open>i < 0\<close> using sg_iff by simp
      then have \<open>(char_hyphen # map char_of_word bytes, i) \<in> ascii_str_int_rel\<close>
        using ascii_str_nat_int_neg[OF rel] by (auto simp: abs_if)
      then show ?thesis
        using True char_of_word_hyphen by force
    next
      case False
      then have \<open>0 \<le> i\<close> using sg_iff by simp
      then have \<open>(map char_of_word bytes, i) \<in> ascii_str_int_rel\<close>
        using ascii_str_nat_int_pos[OF rel] by (auto simp: abs_if)
      then show ?thesis
        using False by (simp add: pw_le_iff refine_pw_simps)
    qed
  qed
qed

term sbi_assn
term sbi_aux_assn
term ascii_strl_assn

section \<open>Decimal Byte Strings to Integers\<close>

text \<open>With bigint \<rightarrow> String in place, we now want to go the other direction of string \<rightarrow> big_int\<close>

definition byte_val :: \<open>8 word \<Rightarrow> nat\<close> where
  \<open>byte_val b \<equiv> unat b - 48\<close>

definition bytes_dec_val :: \<open>8 word list \<Rightarrow> nat\<close> where
  \<open>bytes_dec_val bs \<equiv> foldl (\<lambda>acc b. 10 * acc + byte_val b) 0 bs\<close>

lemma bytes_dec_val_Nil: \<open>bytes_dec_val [] = 0\<close>
  by (simp add: bytes_dec_val_def)

lemma bytes_dec_val_snoc: \<open>bytes_dec_val (xs @ [b]) = 10 * bytes_dec_val xs + byte_val b\<close>
  by (simp add: bytes_dec_val_def)

subsection \<open>Abstract Parser\<close>


definition int_of_bytes :: \<open>8 word list \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> int nres\<close> where
  \<open>int_of_bytes bs i\<^sub>0 neg = doN {
     ASSERT (length bs < max_snat 64);
     (_, acc) \<leftarrow> WHILE\<^sub>T
       (\<lambda>(i, acc). i < length bs)
       (\<lambda>(i, acc). do {
          ASSERT (i < length bs);
          ASSERT (48 \<le> unat (bs ! i));
          RETURN (i + 1, acc * of_nat 10 + of_nat (byte_val (bs ! i)))
        }) (i\<^sub>0, 0);
     RETURN (if neg then - acc else acc)
   }\<close>

lemma int_of_bytes_correct:
  assumes D: \<open>\<forall>b \<in> set bs. 48 \<le> unat b\<close> and L: \<open>length bs < max_snat 64\<close> and I\<^sub>0: \<open>i\<^sub>0 < length bs\<close>
  shows \<open>int_of_bytes bs i\<^sub>0 neg \<le> RETURN ((if neg then -1 else 1) * int (bytes_dec_val (drop i\<^sub>0 bs)))\<close>
proof -
  have step: \<open>bytes_dec_val (take (Suc j) cs) = 10 * bytes_dec_val (take j cs) + byte_val (cs ! j)\<close>
    if \<open>j < length cs\<close> for j and cs :: \<open>8 word list\<close>
    using that by (simp add: take_Suc_conv_app_nth bytes_dec_val_snoc)
  have dstep: \<open>int (bytes_dec_val (take (Suc i - i⇩0) (drop i⇩0 bs)))
                = 10 * int (bytes_dec_val (take (i - i⇩0) (drop i⇩0 bs))) + int (byte_val (bs ! i))\<close>
    if ii: \<open>i⇩0 \<le> i\<close> and il: \<open>i < length bs\<close> for i
  proof -
    have jl: \<open>i - i⇩0 < length (drop i⇩0 bs)\<close> using ii il by simp
    have \<open>bytes_dec_val (take (Suc (i - i⇩0)) (drop i⇩0 bs))
           = 10 * bytes_dec_val (take (i - i⇩0) (drop i⇩0 bs)) + byte_val (bs ! i)\<close>
      using step[OF jl] ii il by simp
    then show ?thesis
      using ii by (simp add: Suc_diff_le)
  qed  
  show ?thesis

    unfolding int_of_bytes_def
      apply (refine_vcg WHILET_rule[where
        I = \<open>\<lambda>(i, acc). i⇩0 \<le> i \<and> i \<le> length bs
                         \<and> acc = int (bytes_dec_val (take (i - i⇩0) (drop i⇩0 bs)))\<close> and
        R = \<open>measure (\<lambda>(i, _). length bs - i)\<close>])
      using I\<^sub>0
      apply (auto simp: L D[THEN bspec] dstep bytes_dec_val_Nil algebra_simps)
      done
qed

definition byte_digit_impl :: \<open>8 word \<Rightarrow> 64 word llM\<close> where [llvm_code]:
  \<open>byte_digit_impl b \<equiv> doM { w \<leftarrow> ll_zext b TYPE(64 word); ll_sub w 48 }\<close>

context begin
interpretation llvm_prim_arith_setup .
lemma byte_digit_impl_rule:
  \<open>llvm_htriple \<box> (byte_digit_impl b) (\<lambda>r. \<up>(r = UCAST(8 \<rightarrow> 64) b - 48))\<close>
  unfolding byte_digit_impl_def
  supply [simp] = is_up'
  by vcg
end

lemma byte_val_hnr[sepref_fr_rules]:
  \<open>(byte_digit_impl, RETURN o byte_val) \<in> [\<lambda>b. 48 \<le> unat b]\<^sub>a id_assn\<^sup>k \<rightarrow> snat_assn' TYPE(64)\<close>
proof -
  have U: \<open>unat (UCAST(8 \<rightarrow> 64) b - 48) = unat b - 48\<close> if \<open>48 \<le> unat b\<close> for b :: \<open>8 word\<close>
  proof -
    have E: \<open>unat (UCAST(8 \<rightarrow> 64) b) = unat b\<close>
      by (simp add: is_up' unat_ucast_upcast)
    have \<open>(48 :: 64 word) \<le> UCAST(8 \<rightarrow> 64) b\<close>
      using that by (simp add: word_le_nat_alt E)
    then show ?thesis
      by (simp add: unat_sub E)
  qed
  have I: \<open>snat_invar (UCAST(8 \<rightarrow> 64) b - 48)\<close> if \<open>48 \<le> unat b\<close> for b :: \<open>8 word\<close>
  proof -
    have \<open>unat (UCAST(8 \<rightarrow> 64) b - 48) = unat b - 48\<close>
      using that by (rule U)
    also have \<open>unat b - 48 < 2 ^ 63\<close>
      using unat_lt2p[of b] by simp
    finally show ?thesis
      by (simp add: snat_invar_alt)
  qed
  show ?thesis
    apply sepref_to_hoare
    supply [vcg_rules] = byte_digit_impl_rule
    apply vcg
    apply (auto simp: snat_rel_def snat.rel_def in_br_conv snat.assn_is_rel[symmetric]
      pure_def byte_val_def U I sep_algebra_simps pred_lift_extract_simps)
    apply (simp add: ENTAILS_def I U sep_empty_I snat_eq_unat_aux2)
    done
qed

(* TODO: We name this `str_to_int` only because `int_of_str` is already defined - fix naming *)
definition str_to_int :: \<open>8 word list \<Rightarrow> int nres\<close> where
  \<open>str_to_int s \<equiv> doN {
    ASSERT (s \<noteq> []);
    if s!0 = word_hyphen
      then int_of_bytes s 1 True
      else int_of_bytes s 0 False
  }\<close>

sepref_def str_to_int_impl is \<open>str_to_int\<close>
  :: \<open>(larray_assn' TYPE(64) id_assn)\<^sup>k \<rightarrow>\<^sub>a sbi_assn\<close>
  unfolding str_to_int_def word_hyphen_val int_of_bytes_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

(* TODO: Full correctness proof of `str_to_int_impl` w.r.t. to the relations defined at the top
 * of the theory. Then we want to show that the two directions can be composed to get identity *)

end
