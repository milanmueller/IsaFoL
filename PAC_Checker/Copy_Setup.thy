theory Copy_Setup
  imports Isabelle_LLVM.IICF
begin

text \<open>Copy Setup taken from Isabelle_LLVM/sorting/Sorting_Setup.thy (which is not in ROOTS)
  thus we copy paste it here\<close>

definition "is_copy A cp \<equiv> (cp,RETURN o COPY) \<in> A\<^sup>k \<rightarrow>\<^sub>a A"

lemma is_copy_rule[sepref_fr_rules]:
  "GEN_ALGO cp (is_copy A) \<Longrightarrow> (cp,RETURN o COPY) \<in> A\<^sup>k \<rightarrow>\<^sub>a A"
  unfolding is_copy_def GEN_ALGO_def by auto

definition arl_copy :: "('a::llvm_rep,'l::len2) array_list \<Rightarrow> ('a,'l) array_list llM"
  where [llvm_code]: "arl_copy al \<equiv> doM {
    let (l,c,a) = al;
    a' \<leftarrow> narray_new TYPE('a) l;  \<comment> \<open>Compacts the new array\<close>
    arraycpy a' a l;
    Mreturn (l,l,a')
  }"

lemma arl_copy_rule[vcg_rules]: "llvm_htriple
  (\<upharpoonleft>arl_assn xs xsi) (arl_copy xsi) (\<lambda>r. \<upharpoonleft>arl_assn xs xsi ** \<upharpoonleft>arl_assn xs r)"
  unfolding arl_copy_def arl_assn_def arl_assn'_def
  by vcg

lemma al_copy_hnr: "(arl_copy, RETURN o op_list_copy) \<in> (al_assn A)\<^sup>k \<rightarrow>\<^sub>a al_assn A"
  unfolding al_assn_def hr_comp_def
  apply sepref_to_hoare
  by vcg

sepref_decl_impl al_copy_hnr uses op_list_copy.fref[of Id, simplified] .

lemma al_copy_gen_algo[sepref_gen_algo_rules]: "GEN_ALGO arl_copy (is_copy (al_assn A))"
  using al_copy_hnr
  unfolding GEN_ALGO_def is_copy_def COPY_def op_list_copy_def .

end
