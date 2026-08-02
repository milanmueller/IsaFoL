theory Aux_Lemmas
  imports Main Isabelle_LLVM.IICF
begin

text \<open>Lemmas and Definitions that are not available in Isabelle LLVM, but where
(possibly indirectly) available in Refine_Imperative HOL\<close>

text \<open>From Separation_Logic_Imperative_HOL.Hash_Map\<close>
lemma take_set: "set (take n l) = { l!i | i. i<n \<and> i<length l }"
  apply (auto simp add: set_conv_nth)
  apply (rule_tac x=i in exI)
  apply auto
  done

text \<open>From Refine_Imperative_HOL.IICF_List_Mset\<close>
definition "list_mset_rel \<equiv> br mset (\<lambda>_. True)"

text \<open>From Refine_Imperative_HOL.Sepref_Foreach\<close>
definition "monadic_nfoldli l c f s \<equiv> RECT (\<lambda>D (l,s). case l of 
    [] \<Rightarrow> RETURN s
  | x#ls \<Rightarrow> do {
      b \<leftarrow> c s;
      if b then do { s'\<leftarrow>f x s; D (ls,s')} else RETURN s
    }
  ) (l,s)"

lemma monadic_nfoldli_eq:
  "monadic_nfoldli l c f s = (
    case l of 
      [] \<Rightarrow> RETURN s 
    | x#ls \<Rightarrow> do {
        b\<leftarrow>c s; 
        if b then f x s \<bind> monadic_nfoldli ls c f else RETURN s
      }
  )"
  apply (subst monadic_nfoldli_def)
  apply (subst RECT_unfold)
  apply (tagged_solver)
  apply (subst monadic_nfoldli_def[symmetric])
  apply simp
  done

lemma monadic_nfoldli_simp[simp]:
  "monadic_nfoldli [] c f s = RETURN s"
  "monadic_nfoldli (x#ls) c f s = do {
    b\<leftarrow>c s;
    if b then f x s \<bind> monadic_nfoldli ls c f else RETURN s
  }"
  apply (subst monadic_nfoldli_eq, simp)
  apply (subst monadic_nfoldli_eq, simp)
  done

end
