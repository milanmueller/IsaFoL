(*
  File:         PAC_Step_Assn.thy
  Authors:      Milan Müller, Anthropic Opus 4.8
*)
theory LPAC_Step_Assn
  imports
    PAC_Checker_LLVM.IICF_Owning_List
    LPAC_Checker_Specification
begin

section \<open>Concrete Representation and Refinement Assertion\<close>

text \<open>For the concrete data, we use a tag (8 word) to select the constructor.
  Then, we have a field for every possible inner value.
  For every constructors, some fields will be emtpy (e.g. Del holds no poly)\<close>

text \<open>We fix ids to 64 bit words - maybe it could be \<open>'l::len\<close> aswell...\<close>
type_synonym ('pi, 'vi) pac_step_impl =
  \<open>8 word \<times> 64 word \<times> 'pi \<times> ('pi \<times> 64 word) os_list \<times> 'vi\<close>
  (*  tag \<times> new_id  \<times> res \<times> srcs                    \<times> var *)

definition pac_step_assn ::
  \<open>('a \<Rightarrow> 'pi::llvm_rep \<Rightarrow> assn) \<Rightarrow> ('b \<Rightarrow> 'vi::llvm_rep \<Rightarrow> assn)
    \<Rightarrow> ('a, 'b, nat) pac_step \<Rightarrow> ('pi, 'vi) pac_step_impl \<Rightarrow> assn\<close> where
  \<open>pac_step_assn Rp Rv step \<equiv> (\<lambda>(tag, idc, res, srcs, var). case step of
      CL p i r \<Rightarrow>
        \<up>(tag = 0) ** unat_assn' TYPE(64) i idc
        ** ol_assn (Rp \<times>\<^sub>a unat_assn' TYPE(64)) p srcs ** Rp r res
    | Extension i x r \<Rightarrow>
        \<up>(tag = 1) ** unat_assn' TYPE(64) i idc ** Rv x var ** Rp r res
    | Del i \<Rightarrow>
        \<up>(tag = 2) ** unat_assn' TYPE(64) i idc)\<close>

lemma pac_step_assn_CL[simp]:
  \<open>pac_step_assn Rp Rv (CL p i r) (tag, idc, res, srcs, nvar) =
    (\<up>(tag = 0) ** unat_assn' TYPE(64) i idc
      ** ol_assn (Rp \<times>\<^sub>a unat_assn' TYPE(64)) p srcs ** Rp r res)\<close>
  unfolding pac_step_assn_def by simp

lemma pac_step_assn_Extension[simp]:
  \<open>pac_step_assn Rp Rv (Extension i x r) (tag, idc, res, srcs, nvar) =
    (\<up>(tag = 1) ** unat_assn' TYPE(64) i idc ** Rv x nvar ** Rp r res)\<close>
  unfolding pac_step_assn_def by simp

lemma pac_step_assn_Del[simp]:
  \<open>pac_step_assn Rp Rv (Del i) (tag, idc, res, srcs, nvar) =
    (\<up>(tag = 2) ** unat_assn' TYPE(64) i idc)\<close>
  unfolding pac_step_assn_def by simp

section \<open>Raw word comparison and reassembly bundle\<close>

text \<open>The tag is a raw \<^typ>\<open>8 word\<close>; \<open>ll_icmp_eq\<close> on it has no snat/unat abstraction, so we
  prove the comparison rule once in a throwaway interpreted context and supply it locally
  (never globally \<open>[vcg_rules]\<close>, cf. the same recipe in \<open>PAC_Checker_Synthesis\<close>).\<close>

context begin
interpretation llvm_prim_arith_setup .

lemma ll_icmp_eq_word_rule:
  \<open>llvm_htriple \<box> (ll_icmp_eq (a::'l::len word) b) (\<lambda>r. \<upharpoonleft>bool.assn (a = b) r)\<close>
  supply [simp] = bool.assn_def by vcg

end

lemmas step_pure_reassembly =
  ENTAILS_def entails_def sep_algebra_simps pred_lift_extract_simps sep_conj_exists
  pure_app_eq pure_def vcg_tag_defs

text \<open>Guard-lifting bundle for free proofs: like \<open>step_pure_reassembly\<close> but WITHOUT \<open>pure_def\<close>,
  so the \<open>unat_assn'\<close> inside the owning-list element parameter stays folded and the
  \<open>ol_assn_free\<close> rule still matches. (Unfolding it there breaks the free-rule unification.)\<close>

lemmas step_free_prep =
  sep_algebra_simps pred_lift_extract_simps sep_conj_exists pure_app_eq vcg_tag_defs


section \<open>Discriminators (read the tag, keep the step)\<close>

definition is_CL_impl :: \<open>('pi::llvm_rep, 'vi::llvm_rep) pac_step_impl \<Rightarrow> 1 word llM\<close>
  where [llvm_code, llvm_inline]: \<open>is_CL_impl \<equiv> \<lambda>(t, _, _, _, _). ll_icmp_eq t 0\<close>

definition is_Extension_impl :: \<open>('pi::llvm_rep, 'vi::llvm_rep) pac_step_impl \<Rightarrow> 1 word llM\<close>
  where [llvm_code, llvm_inline]: \<open>is_Extension_impl \<equiv> \<lambda>(t, _, _, _, _). ll_icmp_eq t 1\<close>

definition is_Del_impl :: \<open>('pi::llvm_rep, 'vi::llvm_rep) pac_step_impl \<Rightarrow> 1 word llM\<close>
  where [llvm_code, llvm_inline]: \<open>is_Del_impl \<equiv> \<lambda>(t, _, _, _, _). ll_icmp_eq t 2\<close>

lemma is_CL_hnr[sepref_fr_rules]:
  \<open>(is_CL_impl, RETURN o is_CL) \<in> (pac_step_assn Rp Rv)\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding bool1_rel_def bool.assn_is_rel[symmetric] is_CL_impl_def
  supply [vcg_rules] = ll_icmp_eq_word_rule
  supply [simp] = bool.assn_def
  apply sepref_to_hoare
  subgoal for step c
    by (cases step; cases c) (vcg; auto simp: step_pure_reassembly)+
  done

lemma is_Extension_hnr[sepref_fr_rules]:
  \<open>(is_Extension_impl, RETURN o is_Extension) \<in> (pac_step_assn Rp Rv)\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding bool1_rel_def bool.assn_is_rel[symmetric] is_Extension_impl_def
  supply [vcg_rules] = ll_icmp_eq_word_rule
  supply [simp] = bool.assn_def
  apply sepref_to_hoare
  subgoal for step c
    by (cases step; cases c) (vcg; auto simp: step_pure_reassembly)+
  done

lemma is_Del_hnr[sepref_fr_rules]:
  \<open>(is_Del_impl, RETURN o is_Del) \<in> (pac_step_assn Rp Rv)\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding bool1_rel_def bool.assn_is_rel[symmetric] is_Del_impl_def
  supply [vcg_rules] = ll_icmp_eq_word_rule
  supply [simp] = bool.assn_def
  apply sepref_to_hoare
  subgoal for step c
    by (cases step; cases c) (vcg; auto simp: step_pure_reassembly)+
  done


section \<open>Pure reader for the id/label field (present in every constructor)\<close>

definition read_id_impl :: \<open>('pi::llvm_rep, 'vi::llvm_rep) pac_step_impl \<Rightarrow> 64 word llM\<close>
  where [llvm_code, llvm_inline]: \<open>read_id_impl \<equiv> \<lambda>(_, idc, _, _, _). Mreturn idc\<close>

lemma read_new_id_hnr[sepref_fr_rules]:
  \<open>(read_id_impl, RETURN o new_id) \<in> [\<lambda>x. \<not>is_Del x]\<^sub>a (pac_step_assn Rp Rv)\<^sup>k \<rightarrow> unat_assn' TYPE(64)\<close>
  unfolding read_id_impl_def
  apply sepref_to_hoare
  subgoal for step c
    by (cases step; cases c) (vcg; auto simp: step_pure_reassembly)+
  done

lemma read_pac_src1_hnr[sepref_fr_rules]:
  \<open>(read_id_impl, RETURN o pac_src1) \<in> [\<lambda>x. is_Del x]\<^sub>a (pac_step_assn Rp Rv)\<^sup>k \<rightarrow> unat_assn' TYPE(64)\<close>
  unfolding read_id_impl_def
  apply sepref_to_hoare
  subgoal for step c
    by (cases step; cases c) (vcg; auto simp: step_pure_reassembly)+
  done


section \<open>Destructors: consume the step, transfer ownership of its fields out\<close>

text \<open>Each destructor is a pure tuple projection. Because \<^type>\<open>pac_step_impl\<close> is passed by
  value (no heap cell of its own), projecting the pointer fields out of the consumed (\<open>\<^sup>d\<close>)
  step transfers their ownership to the caller; the unused slot is dropped (never owned).\<close>

definition mop_dest_CL where
  \<open>mop_dest_CL s = do { ASSERT(is_CL s); RETURN (pac_srcs s, new_id s, pac_res s) }\<close>

definition dest_CL_impl ::
  \<open>('pi::llvm_rep, 'vi::llvm_rep) pac_step_impl
    \<Rightarrow> (('pi \<times> 64 word) os_list \<times> 64 word \<times> 'pi) llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>dest_CL_impl \<equiv> \<lambda>(t, idc, res, srcs, var). Mreturn (srcs, idc, res)\<close>

lemma dest_CL_hnr[sepref_fr_rules]:
  \<open>(dest_CL_impl, mop_dest_CL) \<in> (pac_step_assn Rp Rv)\<^sup>d \<rightarrow>\<^sub>a
     ol_assn (Rp \<times>\<^sub>a unat_assn' TYPE(64)) \<times>\<^sub>a unat_assn' TYPE(64) \<times>\<^sub>a Rp\<close>
  unfolding dest_CL_impl_def mop_dest_CL_def
  supply [simp] = refine_pw_simps
  apply sepref_to_hoare
  subgoal for step c
    apply (cases step; cases c)
    apply (simp_all add: refine_pw_simps)
    apply (vcg; auto simp: step_pure_reassembly prod_assn_def)
    done
  done

definition mop_dest_Extension where
  \<open>mop_dest_Extension s = do { ASSERT(is_Extension s); RETURN (new_id s, new_var s, pac_res s) }\<close>

definition dest_Extension_impl ::
  \<open>('pi::llvm_rep, 'vi::llvm_rep) pac_step_impl \<Rightarrow> (64 word \<times> 'vi \<times> 'pi) llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>dest_Extension_impl \<equiv> \<lambda>(t, idc, res, srcs, var). Mreturn (idc, var, res)\<close>

lemma dest_Extension_hnr[sepref_fr_rules]:
  \<open>(dest_Extension_impl, mop_dest_Extension) \<in> (pac_step_assn Rp Rv)\<^sup>d \<rightarrow>\<^sub>a
     unat_assn' TYPE(64) \<times>\<^sub>a Rv \<times>\<^sub>a Rp\<close>
  unfolding dest_Extension_impl_def mop_dest_Extension_def
  supply [simp] = refine_pw_simps
  apply sepref_to_hoare
  subgoal for step c
    apply (cases step; cases c)
    apply (simp_all add: refine_pw_simps)
    apply (vcg; auto simp: step_pure_reassembly prod_assn_def)
    done
  done

definition mop_dest_Del where
  \<open>mop_dest_Del s = do { ASSERT(is_Del s); RETURN (pac_src1 s) }\<close>

definition dest_Del_impl ::
  \<open>('pi::llvm_rep, 'vi::llvm_rep) pac_step_impl \<Rightarrow> 64 word llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>dest_Del_impl \<equiv> \<lambda>(t, idc, res, srcs, var). Mreturn idc\<close>

lemma dest_Del_hnr[sepref_fr_rules]:
  \<open>(dest_Del_impl, mop_dest_Del) \<in> (pac_step_assn Rp Rv)\<^sup>d \<rightarrow>\<^sub>a unat_assn' TYPE(64)\<close>
  unfolding dest_Del_impl_def mop_dest_Del_def
  supply [simp] = refine_pw_simps
  apply sepref_to_hoare
  subgoal for step c
    apply (cases step; cases c)
    apply (simp_all add: refine_pw_simps)
    apply (vcg; auto simp: step_pure_reassembly prod_assn_def)
    done
  done


section \<open>Deep free: dispatch on the tag, free only the owned slots\<close>

text \<open>A CL step owns the sources list and the result poly; an Extension owns the variable and
  the result poly; a Del owns nothing but the (pure) id. The unused slots are filled with
  \<open>init\<close> and never owned, so freeing skips them. The sources entry \<open>(poly, id)\<close> frees only the
  poly (the id is pure).\<close>

definition src_entry_free_impl ::
  \<open>('pi::llvm_rep \<Rightarrow> unit llM) \<Rightarrow> ('pi \<times> 64 word) \<Rightarrow> unit llM\<close>
  where [llvm_code]: \<open>src_entry_free_impl pfree \<equiv> \<lambda>(p, _). pfree p\<close>

lemma src_entry_assn_free:
  assumes \<open>MK_FREE Rp pfree\<close>
  shows \<open>MK_FREE (Rp \<times>\<^sub>a unat_assn' TYPE(64)) (src_entry_free_impl pfree)\<close>
  supply [vcg_rules] = MK_FREED[OF assms]
  apply (rule MK_FREEI)
  unfolding src_entry_free_impl_def prod_assn_def
  subgoal for a c
    apply (cases a; cases c; simp)
    by (vcg; auto simp: step_pure_reassembly)
  done

definition pac_step_free_impl ::
  \<open>('pi::llvm_rep \<Rightarrow> unit llM) \<Rightarrow> ('vi::llvm_rep \<Rightarrow> unit llM)
    \<Rightarrow> ('pi, 'vi) pac_step_impl \<Rightarrow> unit llM\<close>
  where [llvm_code]:
  \<open>pac_step_free_impl pfree vfree \<equiv> \<lambda>(t, idc, res, srcs, var).
     if t = 0 then doM { ol_delete (src_entry_free_impl pfree) srcs; pfree res }
     else if t = 1 then doM { vfree var; pfree res }
     else Mreturn ()\<close>

lemma pac_step_assn_free[sepref_frame_free_rules]:
  assumes P: \<open>MK_FREE Rp pfree\<close> and V: \<open>MK_FREE Rv vfree\<close>
  shows \<open>MK_FREE (pac_step_assn Rp Rv) (pac_step_free_impl pfree vfree)\<close>
  supply [vcg_rules] = MK_FREED[OF P] MK_FREED[OF V]
    MK_FREED[OF ol_assn_free[OF src_entry_assn_free[OF P]]]
  apply (rule MK_FREEI)
  unfolding pac_step_free_impl_def
  subgoal for a c
    apply (cases a; cases c)
    subgoal by (simp add: step_free_prep split: if_splits; vcg; auto simp: step_pure_reassembly)
    subgoal by (simp add: step_free_prep split: if_splits; vcg; auto simp: step_pure_reassembly)
    subgoal by (simp add: step_free_prep split: if_splits; vcg; auto simp: step_pure_reassembly)
    done
  done


section \<open>Constructors (producers): pack the fields into the tagged tuple\<close>

text \<open>Each constructor writes its tag, moves its owning fields into their slots, and fills the
  unused slots with \<open>init\<close> (never owned). These are producers: their result assertion is
  unconstrained at rule-application time, so we do NOT register them globally
  \<open>[sepref_fr_rules]\<close> (they would shadow other syntheses without backtracking); instead they
  are \<open>supply\<close>-ed locally where needed (cf. the \<open>list_custom_empty\<close> discipline).\<close>

definition CL_impl ::
  \<open>('pi \<times> 64 word) os_list \<Rightarrow> 64 word \<Rightarrow> 'pi \<Rightarrow> ('pi::llvm_rep, 'vi::llvm_rep) pac_step_impl llM\<close>
  where [llvm_code, llvm_inline]: \<open>CL_impl srcs idc res \<equiv> Mreturn (0, idc, res, srcs, init)\<close>

definition Extension_impl ::
  \<open>64 word \<Rightarrow> 'vi \<Rightarrow> 'pi \<Rightarrow> ('pi::llvm_rep, 'vi::llvm_rep) pac_step_impl llM\<close>
  where [llvm_code, llvm_inline]: \<open>Extension_impl idc nvar res \<equiv> Mreturn (1, idc, res, init, nvar)\<close>

definition Del_impl ::
  \<open>64 word \<Rightarrow> ('pi::llvm_rep, 'vi::llvm_rep) pac_step_impl llM\<close>
  where [llvm_code, llvm_inline]: \<open>Del_impl idc \<equiv> Mreturn (2, idc, init, init, init)\<close>

lemma CL_impl_hnr:
  \<open>(uncurry2 CL_impl, uncurry2 (RETURN ooo CL))
    \<in> (ol_assn (Rp \<times>\<^sub>a unat_assn' TYPE(64)))\<^sup>d *\<^sub>a (unat_assn :: nat \<Rightarrow> 64 word \<Rightarrow> _)\<^sup>k *\<^sub>a Rp\<^sup>d
      \<rightarrow>\<^sub>a pac_step_assn Rp Rv\<close>
  unfolding CL_impl_def
  apply sepref_to_hoare
  subgoal for res idc srcs resi idci srcsi
    by (vcg; auto simp: step_pure_reassembly prod_assn_def)
  done

lemma Extension_impl_hnr:
  \<open>(uncurry2 Extension_impl, uncurry2 (RETURN ooo Extension))
    \<in> (unat_assn :: nat \<Rightarrow> 64 word \<Rightarrow> _)\<^sup>k *\<^sub>a Rv\<^sup>d *\<^sub>a Rp\<^sup>d \<rightarrow>\<^sub>a pac_step_assn Rp Rv\<close>
  unfolding Extension_impl_def
  apply sepref_to_hoare
  subgoal for res var idc resi vari idci
    by (vcg; auto simp: step_pure_reassembly prod_assn_def)
  done

lemma Del_impl_hnr:
  \<open>(Del_impl, RETURN o Del) \<in> (unat_assn :: nat \<Rightarrow> 64 word \<Rightarrow> _)\<^sup>k \<rightarrow>\<^sub>a pac_step_assn Rp Rv\<close>
  unfolding Del_impl_def
  apply sepref_to_hoare
  subgoal for i ii
    by (vcg; auto simp: step_pure_reassembly prod_assn_def)
  done

text \<open>Interface type for \<open>pac_step\<close> and the \<open>intf_of_assn\<close> bridge (mirrors the map/set
  assertions): without it the id phase cannot assign a \<open>pac_step\<close>-typed operation an interface
  and rejects it with \<open>Invalid abstract head\<close>. The label is always \<^typ>\<open>nat\<close> (refined by
  \<open>unat_assn\<close>), so the interface's label slot is fixed to \<^typ>\<open>nat\<close>.\<close>

sepref_decl_intf ('k, 'b, 'lbl) i_pac_step is "('k, 'b, 'lbl) pac_step"

lemma pac_step_assn_intf[intf_of_assn]:
  \<open>intf_of_assn Rp TYPE('ip) \<Longrightarrow> intf_of_assn Rv TYPE('iv)
    \<Longrightarrow> intf_of_assn (pac_step_assn Rp Rv) TYPE(('ip, 'iv, nat) i_pac_step)\<close>
  by simp

sepref_register CL Extension Del is_CL is_Extension is_Del new_id pac_src1
  mop_dest_CL mop_dest_Extension mop_dest_Del


section \<open>Experiments / smoke tests\<close>

experiment begin

text \<open>T1 \<emdash> pure elements (\<open>Rp = Rv = unat_assn\<close>): build a \<open>Del\<close> step and read its tag back.
  Exercises the producer reassembly, the discriminator, and the tag logic end-to-end.\<close>

sepref_definition t1_impl is \<open>\<lambda>i. do { s \<leftarrow> RETURN (Del i); RETURN (is_Del s) }\<close>
  :: \<open>(unat_assn :: nat \<Rightarrow> 64 word \<Rightarrow> _)\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [sepref_fr_rules] = Del_impl_hnr
  by sepref

text \<open>Owning poly stand-in: an owning list of ids (\<open>pstub_assn\<close>, abstract \<^typ>\<open>nat list\<close>) plays
  the role of the heap-owning polynomial \<open>Rp\<close>, so the following tests actually move heap
  ownership through the step. The abbreviations carry EXPLICIT type signatures (cf. \<open>w8ss_assn\<close>
  in \<open>IICF_Owning_List\<close>).\<close>

abbreviation id64_assn :: \<open>nat \<Rightarrow> 64 word \<Rightarrow> assn\<close> where
  \<open>id64_assn \<equiv> unat_assn\<close>

abbreviation pstub_assn :: \<open>nat list \<Rightarrow> 64 word os_list \<Rightarrow> assn\<close> where
  \<open>pstub_assn \<equiv> ol_assn unat_assn\<close>

abbreviation src_assn :: \<open>(nat list \<times> nat) list \<Rightarrow> (64 word os_list \<times> 64 word) os_list \<Rightarrow> assn\<close>
  where \<open>src_assn \<equiv> ol_assn (pstub_assn \<times>\<^sub>a id64_assn)\<close>

text \<open>Sanity: the owning stand-in assertions themselves move (\<open>\<^sup>d\<close> identity) through \<open>sepref\<close> \<emdash>
  the nested \<open>ol_assn\<close>-of-\<open>ol_assn\<close> representation and the composed free machinery are sound.\<close>

sepref_definition pd_test is \<open>RETURN o (\<lambda>x::nat list. x)\<close> :: \<open>pstub_assn\<^sup>d \<rightarrow>\<^sub>a pstub_assn\<close>
  by sepref

sepref_definition sd_test is \<open>RETURN o (\<lambda>x::(nat list \<times> nat) list. x)\<close> :: \<open>src_assn\<^sup>d \<rightarrow>\<^sub>a src_assn\<close>
  by sepref

text \<open>T2 \<emdash> owning roundtrip: build a \<open>CL\<close> step from an owning sources list and an owning result
  poly, destructure it, return only \<open>(id, res)\<close>. The sources list is dropped, so \<open>sepref\<close> must
  synthesize its deep free (the composed \<open>ol_assn\<close>/entry free chain).

  NB the \<open>:: (nat list, nat, nat) pac_step\<close> ascription: \<open>CL\<close>/\<open>Del\<close> leave the variable-type slot
  \<open>'b\<close> free (only \<open>Extension\<close> constrains it), so without it the interface \<open>i_pac_step\<close>'s var slot
  stays schematic and the sepref \<open>::\<close> annotation fails to unify (a stray \<open>_ itself\<close>). Fixing the
  \<open>'b\<close> makes the interface concrete. Real code that also uses \<open>Extension\<close> will not need this.\<close>

definition t2 :: \<open>(nat list \<times> nat) list \<times> nat \<times> nat list \<Rightarrow> (nat \<times> nat list) nres\<close> where
  \<open>t2 = (\<lambda>(srcs, i, r). do {
     (srcs', i', r') \<leftarrow> mop_dest_CL (CL srcs i r :: (nat list, nat, nat) pac_step);
     RETURN (i', r') })\<close>

sepref_definition t2_impl is \<open>t2\<close>
  :: \<open>(src_assn \<times>\<^sub>a id64_assn \<times>\<^sub>a pstub_assn)\<^sup>d \<rightarrow>\<^sub>a id64_assn \<times>\<^sub>a pstub_assn\<close>
  unfolding t2_def
  supply [sepref_fr_rules] = CL_impl_hnr
  by sepref

text \<open>T3 \<emdash> free acid-test: build a full step and drop it unused (return only the separate id).
  \<open>sepref\<close> must synthesize the tag-dispatching deep free for the dead step.\<close>

definition t3 :: \<open>(nat list \<times> nat) list \<times> nat \<times> nat list \<Rightarrow> nat nres\<close> where
  \<open>t3 = (\<lambda>(srcs, i, r). do {
     let s = (CL srcs i r :: (nat list, nat, nat) pac_step); RETURN (new_id s) })\<close>

sepref_definition t3_impl is \<open>t3\<close>
  :: \<open>(src_assn \<times>\<^sub>a id64_assn \<times>\<^sub>a pstub_assn)\<^sup>d \<rightarrow>\<^sub>a id64_assn\<close>
  unfolding t3_def
  supply [sepref_fr_rules] = CL_impl_hnr
  by sepref

end

end
