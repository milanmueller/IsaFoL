theory String_Hash_Map
  imports String_Assn BigInt_LLVM.LLVM_CodeGen_Auxiliary

begin

section \<open>Hash function for strings\<close>

text \<open>Define basic hashing algorithm for strings. Note that @{typ "char"} is implemented by @{typ "8 word"}
      and @{typ "string"} is implemented by @{typ "64 word \<times> 8 word ptr"} (i.e. an array of characters).\<close>

definition uc8_64 :: \<open>8 word \<Rightarrow> 64 word\<close> where \<open>uc8_64 \<equiv> UCAST(8 \<rightarrow> 64)\<close>
(* Weird setup stuff taken from BigInt *)
lemma is_upcast_uc8_64: \<open>is_up' uc8_64\<close>
  by (auto simp: is_up')
context
begin  
  interpretation llvm_prim_arith_setup .
    lemma uc8_64_hnr[sepref_fr_rules]: \<open>(\<lambda>w. ll_zext w TYPE (64 word), RETURN o uc8_64) \<in> (word_assn' TYPE(8))\<^sup>k \<rightarrow>\<^sub>a (word_assn' TYPE(64))\<close>
    unfolding uc8_64_def
    supply [simp] = is_up'
    apply sepref_to_hoare
    by vcg
end

(* Values taken from https://en.wikipedia.org/wiki/Fowler%E2%80%93Noll%E2%80%93Vo_hash_function *)
definition \<open>fnv_prime = (1099511628211 :: 64 word)\<close>
definition \<open>fnv_offset_basis = (14695981039346656037 :: 64 word)\<close>

definition fnv_1a_of_str :: \<open>char list \<Rightarrow> 64 word\<close> where
  \<open>fnv_1a_of_str = foldl (\<lambda>acc x. (acc XOR (uc8_64 (of_char x))) * fnv_prime) fnv_offset_basis\<close>

definition fnv_1a_of_str_imp :: \<open>char list \<Rightarrow> 64 word nres\<close> where
  \<open>fnv_1a_of_str_imp cs \<equiv> doN {
    ASSERT (length cs < max_snat 64);
    (_, res) \<leftarrow> WHILEIT
      (\<lambda>(i, res). i \<le> length cs)
      (\<lambda>(i, _). i < length cs)
      (\<lambda>(i, res). doN{
        ASSERT (i < length cs);
        RETURN (i + 1, (res XOR (uc8_64 (of_char (cs!i)))) * fnv_prime)
      })
    (0, fnv_offset_basis);
    RETURN res 
  }\<close>

(* Need some setup for sepref to know that of_char can be ignored (since char is implemented by 8 word already) *)
lemma of_char_word_id: \<open>x = of_char (char_of (unat (x :: 8 word)))\<close>
  by (metis of_char_of of_nat_of_char unat_of_char_mod word_unat.Rep_inverse)

lemma of_char_hnr [sepref_fr_rules]:
  \<open>(Mreturn, RETURN o of_char) \<in> char_assn\<^sup>k \<rightarrow>\<^sub>a word_assn' TYPE(8)\<close>
  apply sepref_to_hoare
  apply vcg
  apply (clarsimp simp: ENTAILS_def entails_def sep_algebra_simps br_def)
  by (metis (full_types, lifting) char_assn_def char_of_word_def char_rel_def
    char_word.assn_def char_word.assn_is_rel char_word.rel_def comp_def
    of_char_word_id pred_lift_extract_simps(1) sel_mk_pure_assn(1))

sepref_def fnv_1a_of_str_impl is \<open>fnv_1a_of_str_imp\<close>
  :: \<open>(str_assn)\<^sup>k \<rightarrow>\<^sub>a (word_assn' TYPE(size_t))\<close>
  unfolding fnv_1a_of_str_imp_def fnv_prime_def fnv_offset_basis_def
  apply (annot_snat_const "TYPE(size_t)") (* TODO: check if this will give the correct constants *)
  by sepref

section \<open>Hashmap implementation\<close>

text \<open>We implement (a subset of) the Hash Map interface from @{theory "Isabelle_LLVM.IICF_Map"} for strings\<close>

end
