theory IICF_Sepl_Binding
  imports 
  Separation_Logic_Imperative_HOL.Imp_Map_Spec
  Separation_Logic_Imperative_HOL.Imp_Set_Spec
  Separation_Logic_Imperative_HOL.Imp_List_Spec

  Separation_Logic_Imperative_HOL.Hash_Map_Impl
  Separation_Logic_Imperative_HOL.Array_Map_Impl

  Separation_Logic_Imperative_HOL.To_List_GA
  Separation_Logic_Imperative_HOL.Hash_Set_Impl
  Separation_Logic_Imperative_HOL.Array_Set_Impl

  Separation_Logic_Imperative_HOL.Open_List
  Separation_Logic_Imperative_HOL.Circ_List

  Isabelle_LLVM.IICF

  Collections.Locale_Code
begin
  subsubsection \<open>Map\<close>

  locale bind_map = imp_map is_map for is_map :: "('ki \<rightharpoonup> 'vi) \<Rightarrow> 'm \<Rightarrow> assn"
  begin
    definition "assn K V \<equiv> hr_comp is_map (\<langle>the_pure K,the_pure V\<rangle>map_rel)"
    lemmas [fcomp_norm_unfold] = assn_def[symmetric]
    lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure "assn K V" for K V]

  end

  locale bind_map_empty = imp_map_empty + bind_map
  begin
    lemma empty_hnr_aux: "(uncurry0 empty,uncurry0 (RETURN op_map_empty)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a is_map"
      by solve_sepl_binding

    sepref_decl_impl (no_register) empty: empty_hnr_aux .
  end  


  locale bind_map_is_empty = imp_map_is_empty + bind_map
  begin
    lemma is_empty_hnr_aux: "(is_empty,RETURN o op_map_is_empty) \<in> is_map\<^sup>k \<rightarrow>\<^sub>a bool_assn"
      by solve_sepl_binding
      
    sepref_decl_impl is_empty: is_empty_hnr_aux .
  end
  

  locale bind_map_update = imp_map_update + bind_map
  begin
    lemma update_hnr_aux: "(uncurry2 update,uncurry2 (RETURN ooo op_map_update)) \<in> id_assn\<^sup>k *\<^sub>a id_assn\<^sup>k *\<^sub>a is_map\<^sup>d \<rightarrow>\<^sub>a is_map"
      by solve_sepl_binding

    sepref_decl_impl update: update_hnr_aux .
  end


  locale bind_map_delete = imp_map_delete + bind_map
  begin
    lemma delete_hnr_aux: "(uncurry delete,uncurry (RETURN oo op_map_delete)) \<in> id_assn\<^sup>k *\<^sub>a is_map\<^sup>d \<rightarrow>\<^sub>a is_map"
      by solve_sepl_binding

    sepref_decl_impl delete: delete_hnr_aux .
  end


  locale bind_map_lookup = imp_map_lookup + bind_map
  begin
    lemma lookup_hnr_aux: "(uncurry lookup,uncurry (RETURN oo op_map_lookup)) \<in> id_assn\<^sup>k *\<^sub>a is_map\<^sup>k \<rightarrow>\<^sub>a id_assn"
      by solve_sepl_binding

    sepref_decl_impl lookup: lookup_hnr_aux .
  end

  locale bind_map_contains_key = imp_map_contains_key + bind_map
  begin
    lemma contains_key_hnr_aux: "(uncurry contains_key,uncurry (RETURN oo op_map_contains_key)) \<in> id_assn\<^sup>k *\<^sub>a is_map\<^sup>k \<rightarrow>\<^sub>a bool_assn"
      by solve_sepl_binding

    sepref_decl_impl contains_key: contains_key_hnr_aux .
  end

  subsection \<open>Hash Map (hm)\<close>
  interpretation hm: bind_map_empty is_hashmap hm_new
    by unfold_locales

  definition "op_hm_empty \<equiv> IICF_Map.op_map_empty"  
  interpretation hm: map_custom_empty op_hm_empty
    by unfold_locales (simp add: op_hm_empty_def)
  lemmas [sepref_fr_rules] = hm.empty_hnr[folded op_hm_empty_def]

  interpretation hm: bind_map_is_empty is_hashmap Hash_Map.hm_isEmpty
    by unfold_locales

  interpretation hm: bind_map_update is_hashmap Hash_Map.hm_update
    by unfold_locales

  interpretation hm: bind_map_delete is_hashmap Hash_Map.hm_delete
    by unfold_locales

  interpretation hm: bind_map_lookup is_hashmap Hash_Map.hm_lookup
    by unfold_locales

  setup Locale_Code.open_block
  interpretation hm: gen_contains_key_by_lookup is_hashmap Hash_Map.hm_lookup
    by unfold_locales
  setup Locale_Code.close_block

  interpretation hm: bind_map_contains_key is_hashmap hm.contains_key
    by unfold_locales
end
