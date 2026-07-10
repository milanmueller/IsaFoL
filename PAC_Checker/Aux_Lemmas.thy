theory Aux_Lemmas
  imports Main Isabelle_LLVM.IICF
begin

(* TODO: Move and properly implement.
   Placeholder until Isabelle LLVM gains a hashmap implementation.
   The concrete representation is fixed to \<^typ>\<open>unit\<close> and the body to
   \<^const>\<open>sep_false\<close> so the definition type-checks but admits no concrete
   value (no synthesis rules should fire on this yet). *)
definition hm_assn ::
  \<open>('k \<Rightarrow> 'ck \<Rightarrow> assn) \<Rightarrow>
   ('v \<Rightarrow> 'cv \<Rightarrow> assn) \<Rightarrow>
   ('k \<Rightarrow> 'v option) \<Rightarrow> unit \<Rightarrow> assn\<close> where
  \<open>hm_assn K V \<equiv> \<lambda>_ _. sep_false\<close>

(* TODO: Move and properly implement.
   Placeholder until Isabelle LLVM gains a hashset implementation.
   Mirrors \<^const>\<open>hm_assn\<close>: the concrete representation is fixed to \<^typ>\<open>unit\<close>
   and the body to \<^const>\<open>sep_false\<close> so the definition type-checks but admits
   no concrete value (no synthesis rules should fire on this yet).
   In Refine_Imperative_HOL this was the \<open>hs.assn\<close> of the \<open>bind_set\<close> locale,
   with \<open>hs.assn A \<equiv> hr_comp is_set (\<langle>the_pure A\<rangle>set_rel)\<close> of type
   \<open>('a \<Rightarrow> 'ai \<Rightarrow> assn) \<Rightarrow> 'a set \<Rightarrow> 'm \<Rightarrow> assn\<close>. *)
definition hs_assn ::
  \<open>('a \<Rightarrow> 'ca \<Rightarrow> assn) \<Rightarrow>
   'a set \<Rightarrow> unit \<Rightarrow> assn\<close> where
  \<open>hs_assn A \<equiv> \<lambda>_ _. sep_false\<close>

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

text \<open>Does not exist. Note that we have to properly implement Hashmaps\<close>

(* type of hm.assn (with refine imperative)
\<open>"('c \<Rightarrow> 'a \<Rightarrow> assn) \<Rightarrow> ('d \<Rightarrow> 'b \<Rightarrow> assn) \<Rightarrow> ('c \<Rightarrow> 'd option) \<Rightarrow> ('a, 'b) hashtable \<Rightarrow> assn"\<close>
*)

(* type of hr_comp (with refine imperative)
"hr_comp"
:: "('a \<Rightarrow> 'b \<Rightarrow> assn) \<Rightarrow> ('a \<times> 'c) set \<Rightarrow> 'c \<Rightarrow> 'b \<Rightarrow> assn"
*)

(* type of hr_comp (with isabelle llvm backend)
"hr_comp"
  :: "('a \<Rightarrow> 'b \<Rightarrow> llvm_amemory \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'c) set \<Rightarrow> 'c \<Rightarrow> 'b \<Rightarrow> llvm_amemory \<Rightarrow> bool"
*)
(* Note assn = (llvm_amemory \<Rightarrow> bool) ind isabelle llvm*)

(* So hm_assn (for isabelle llvm backend) should have type
... llvm_amemory \<Rightarrow> bool
*)

end