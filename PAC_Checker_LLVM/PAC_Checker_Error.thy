(*
  File:         PAC_Checker_Error.thy
  Author:       Mathias Fleury, Daniela Kaufmann, JKU
  Maintainer:   Mathias Fleury, JKU
*)
theory PAC_Checker_Error
  imports PAC_Checker IICF_HashSet PAC_Step_Assn
    PAC_Checker_Init More_Loops LLVM_String
    IICF_PartialMap PAC_Checker_Relation
begin

section \<open>Synthesis of the Error Messages\<close>

text \<open>Refinement of errors is really slow (because hard coded strings
  amount to pushing all characters in a list).
  Therefore it lives in it's own theory.\<close>

term stra_assn
type_synonym stra_conc = \<open>64 word \<times> 8 word ptr\<close>
type_synonym status_conc = \<open>8 word \<times> stra_conc\<close>

definition msg_assn :: \<open>string \<Rightarrow> stra_conc \<Rightarrow> assn\<close> where
  \<open>msg_assn s si \<equiv> stra_assn (capped s) si\<close>

lemma msg_assn_capped[simp]: \<open>msg_assn (capped s) = msg_assn s\<close>
  unfolding msg_assn_def by simp

lemma msg_assn_mk_free[sepref_frame_free_rules]: \<open>MK_FREE msg_assn la_free_impl\<close>
  apply (rule MK_FREEI)
  unfolding msg_assn_def
  by (rule MK_FREED[OF larray_mk_free])

definition status_assn :: \<open>string code_status \<Rightarrow> status_conc \<Rightarrow> assn\<close> where
  \<open>status_assn c \<equiv> \<lambda>(tag,msgi). case c of
    CSUCCESS    \<Rightarrow> \<up>(tag = 0) ** \<box>
  | CFOUND      \<Rightarrow> \<up>(tag = 1) ** \<box>
  | CFAILED msg \<Rightarrow> \<up>(tag = 2) ** msg_assn msg msgi
  \<close>

lemma status_assn_csuccess_conv[simp]:
  \<open>status_assn CSUCCESS (tag, msgi) \<equiv> \<up>(tag = 0) ** \<box>\<close>
  unfolding status_assn_def by simp

lemma status_assn_cfound_conv[simp]:
  \<open>status_assn CFOUND (tag, msgi) \<equiv> \<up>(tag = 1) ** \<box>\<close>
  unfolding status_assn_def by simp

lemma status_assn_cfailed_conv[simp]:
  \<open>status_assn (CFAILED msg) (tag, msgi) \<equiv> \<up>(tag = 2) ** msg_assn msg msgi\<close>
  unfolding status_assn_def by simp

lemma status_assn_capped[simp]: \<open>status_assn (CFAILED (capped msg)) = status_assn (CFAILED msg)\<close>
  by (intro ext) (auto simp: status_assn_def split: prod.splits)

lemma status_assn_tagD:
  assumes \<open>status_assn c (tag, msgi) s\<close>
  shows \<open>tag = (if is_cfailed c then 2 else if is_cfound c then 1 else 0)\<close>
proof -
  have \<open>pure_part (status_assn c (tag, msgi))\<close>
    using assms by (rule pure_partI)
  then show ?thesis
    by (cases c)
      (auto simp: status_assn_def dest!: pure_part_split_conj pure_part_pureD)
qed

definition mk_csuccess_impl :: \<open>status_conc llM\<close> where [llvm_code,llvm_inline]:
  \<open>mk_csuccess_impl \<equiv> Mreturn (0, init)\<close>

definition mk_cfound_impl :: \<open>status_conc llM\<close> where [llvm_code,llvm_inline]:
  \<open>mk_cfound_impl \<equiv> Mreturn (1, init)\<close>

definition mk_cfailed_impl :: \<open>strl_conc \<Rightarrow> status_conc llM\<close> where [llvm_code,llvm_inline]:
  \<open>mk_cfailed_impl msg \<equiv> doM { msg' \<leftarrow> stra_of_strl_impl msg; Mreturn (2, msg') }\<close>
  
lemma SUCCESS_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (mk_csuccess_impl), uncurry0 (RETURN CSUCCESS))
  \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a status_assn\<close>
  unfolding mk_csuccess_impl_def
  apply (sepref_to_hoare)
  apply vcg
  by (auto simp: sep_algebra_simps ENTAILS_def entails_def)

lemma FOUND_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (mk_cfound_impl), uncurry0 (RETURN CFOUND))
  \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a status_assn\<close>
  unfolding mk_cfound_impl_def
  apply (sepref_to_hoare)
  apply vcg
  by (auto simp: sep_algebra_simps ENTAILS_def entails_def)

lemma FAILED_hnr[sepref_fr_rules]:
  \<open>(mk_cfailed_impl, RETURN o CFAILED) \<in> strl_assn'\<^sup>d \<rightarrow>\<^sub>a status_assn\<close>
  unfolding mk_cfailed_impl_def
  apply sepref_to_hoare
  apply vcg
  by (auto simp: sep_algebra_simps ENTAILS_def entails_def msg_assn_def
    invalid_assn_def pure_def)

(* definition is_csuccess_impl :: \<open>status_conc \<Rightarrow> 1 word llM\<close> where[llvm_code,llvm_inline]:
 *   \<open>is_csuccess_impl \<equiv> \<lambda>(tag,msg). ll_icmp_eq tag 0\<close> *)
definition is_cfound_impl :: \<open>status_conc \<Rightarrow> 1 word llM\<close> where[llvm_code,llvm_inline]:
  \<open>is_cfound_impl \<equiv> \<lambda>(tag,msg). ll_icmp_eq tag 1\<close>
definition is_cfailed_impl :: \<open>status_conc \<Rightarrow> 1 word llM\<close> where[llvm_code,llvm_inline]:
  \<open>is_cfailed_impl \<equiv> \<lambda>(tag,msg). ll_icmp_eq tag 2\<close>

context begin
interpretation llvm_prim_arith_setup + llvm_prim_ctrl_setup .

lemma is_success_hnr[sepref_fr_rules]:
  \<open>(is_cfound_impl, (RETURN o is_cfound))
  \<in> status_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding is_cfound_impl_def
  apply (sepref_to_hoare; vcg)
  by (auto simp: sep_algebra_simps ENTAILS_def entails_def
    bool1_rel_def bool.rel_def in_br_conv pred_lift_extract_simps
    dest!: status_assn_tagD split: if_splits)

lemma is_cfailed_hnr[sepref_fr_rules]:
  \<open>(is_cfailed_impl, (RETURN o is_cfailed))
  \<in> status_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding is_cfailed_impl_def
  apply (sepref_to_hoare; vcg)
  by (auto simp: sep_algebra_simps ENTAILS_def entails_def
    bool1_rel_def bool.rel_def in_br_conv pred_lift_extract_simps
    dest!: status_assn_tagD split: if_splits)

definition merge_cstatus_impl :: \<open>status_conc \<Rightarrow> status_conc \<Rightarrow> status_conc llM\<close>
  where[llvm_code]: \<open>merge_cstatus_impl \<equiv> \<lambda>s1 s2. doM {
    let (t1,msg1) = s1;
    let (t2,msg2) = s2;
    failed1 \<leftarrow> is_cfailed_impl (t1,msg1);
    llc_if failed1
      (doM {
        failed2 \<leftarrow> is_cfailed_impl (t2,msg2);
        llc_if failed2
          (doM { la_free_impl msg2; Mreturn (t1,msg1) })
          (Mreturn (t1,msg1))
      })
      (doM {
        failed2 \<leftarrow> is_cfailed_impl (t2,msg2);
        llc_if failed2
          (Mreturn (t2,msg2))
          (doM {
            found1 \<leftarrow> is_cfound_impl (t1,msg1);
              llc_if found1
                (Mreturn (t1,msg1))
                (doM {
                  found2 \<leftarrow> is_cfound_impl (t2,msg2);
                  llc_if found2
                    (Mreturn (t2,msg2))
                    (Mreturn (0,init))
                })
          })
      })
  }\<close>

lemma merge_cstatus_hnr[sepref_fr_rules]:
  \<open>(uncurry merge_cstatus_impl, uncurry (RETURN oo merge_cstatus)) \<in>
    status_assn\<^sup>d *\<^sub>a  status_assn\<^sup>d \<rightarrow>\<^sub>a status_assn\<close>
  supply [vcg_rules] = msg_assn_mk_free[THEN MK_FREED]
  unfolding merge_cstatus_impl_def is_cfailed_impl_def is_cfound_impl_def
  apply sepref_to_hoare
  subgoal for y x yi xi
    apply (cases x; cases y; cases xi; cases yi; simp)
    apply (all \<open>vcg\<close>)
    apply (auto simp: ENTAILS_def entails_def sep_algebra_simps
      pred_lift_extract_simps sep_conj_exists)
    done
  done

definition status_free_impl :: \<open>status_conc \<Rightarrow> unit llM\<close> where [llvm_code, llvm_inline]:
  \<open>status_free_impl \<equiv> \<lambda>(tag, msgi). doM {
    failed \<leftarrow> is_cfailed_impl (tag, msgi);
    llc_if failed (la_free_impl msgi) (Mreturn ())
  }\<close>

lemma status_assn_mk_free[sepref_frame_free_rules]: \<open>MK_FREE status_assn status_free_impl\<close>
  supply [vcg_rules] = msg_assn_mk_free[THEN MK_FREED]
  apply (rule MK_FREEI)
  subgoal for a c
    unfolding status_free_impl_def is_cfailed_impl_def
    by (cases a; cases c; simp; vcg)
  done

end

subsection \<open>Error Messages on Polynomials\<close>

abbreviation \<open>raw_string_assn \<equiv> stra_assn\<close>

definition error_msg_not_equal_dom_nres where
  \<open>error_msg_not_equal_dom_nres p q pq r \<equiv> doN {
    let ps = poly_print p;
    let qs = poly_print q;
    let pqs = poly_print pq;
    let rs = poly_print r;
    let res = ps @ cl_to_clt '' + '' @
              qs @ cl_to_clt '' = '' @
              pqs @ cl_to_clt '' not equal'' @
              rs;
    RETURN res
  }\<close> 

term raw_string_assn
term stra_assn

sepref_register stra_of_strl
sepref_def error_msg_not_equal_dom_impl is \<open>uncurry3 (error_msg_not_equal_dom_nres)\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding error_msg_not_equal_dom_nres_def
  by sepref

lemma error_msg_not_equal_dom_nres_refine:
  \<open>(uncurry3 error_msg_not_equal_dom_nres, uncurry3 check_not_equal_dom_err)
  \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  by (auto simp: check_not_equal_dom_err_def error_msg_not_equal_dom_nres_def Let_def)

lemmas error_msg_not_equal_dom_hnr[sepref_fr_rules] =
  error_msg_not_equal_dom_impl.refine[FCOMP error_msg_not_equal_dom_nres_refine]

subsection \<open>Printing of Numbers\<close>

(* TODO cleanup this section *)
definition \<open>show_nres \<equiv> cl_to_clt o chars_of_int o COPY\<close>

sepref_def show_impl is \<open>RETURN o show_nres\<close>
  :: \<open>sbi_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding show_nres_def
  by sepref 

lemma char_of_eq_iff2: \<open>c = char_of n \<longleftrightarrow> of_char c = take_bit 8 (n::nat)\<close>
  by (metis char_of_eq_iff)

lemma string_of_digit_single:
  \<open>n < 10 \<Longrightarrow> string_of_digit n = [char_of_digit n]\<close>
  apply (subgoal_tac \<open>n = 0 \<or> n = 1 \<or> n = 2 \<or> n = 3 \<or> n = 4 \<or> n = 5 \<or>
      n = 6 \<or> n = 7 \<or> n = 8 \<or> n = 9\<close>)
  subgoal
    unfolding string_of_digit_def char_of_digit_def
    by (elim disjE; simp add: char_of_eq_iff char_of_eq_iff2)
  subgoal by auto
  done

lemma showsp_nat_chars_of_nat: \<open>showsp_nat p n s = chars_of_nat n @ s\<close>
  apply (induction n arbitrary: s rule: chars_of_nat.induct)
  apply (subst showsp_nat.simps)
  apply (subst chars_of_nat.simps)
  apply (auto simp del: chars_of_nat.simps
      simp add: shows_string_def string_of_digit_single)
  done

lemma chars_of_int_show: \<open>chars_of_int i = show i\<close>
  by (auto simp: chars_of_int_def shows_prec_int_def showsp_int_def
      showsp_nat_chars_of_nat shows_string_def ascii_hyphen_def)

lemma cl_to_clt_id: \<open>cl_to_clt = id\<close>
  unfolding cl_to_clt_def
  by (metis (mono_tags, lifting) append.simps(1) eq_id_iff foldl_snoc)
    
lemma show_nres_spec: \<open>(RETURN o show_nres, RETURN o show)
  \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  unfolding show_nres_def cl_to_clt_id id_def
  apply (intro frefI nres_relI)
  using chars_of_int_show by auto

definition show_int :: \<open>int \<Rightarrow> string\<close> where
  \<open>show_int i = show i\<close>

lemma show_nres_int_spec: \<open>(RETURN o show_nres, RETURN o show_int)
  \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  unfolding show_nres_def show_int_def cl_to_clt_id
  apply (intro frefI nres_relI)
  apply (auto simp: chars_of_int_show)
  done

lemmas show_nres_hnr[sepref_fr_rules] =
  show_impl.refine[FCOMP show_nres_int_spec]

lemma show_nat_show_int_of_nat: \<open>show (n :: nat) = show_int (of_nat n)\<close>
  unfolding show_int_def chars_of_int_show[symmetric] chars_of_int_def
  by (simp add: shows_prec_nat_def showsp_nat_chars_of_nat)

definition show_nat :: \<open>nat \<Rightarrow> string\<close> where \<open>show_nat \<equiv> show\<close>

sepref_def show_nat_impl is \<open>RETURN o show_nat\<close>
  :: \<open>si64_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding show_nat_def show_nat_show_int_of_nat
  by sepref

subsection \<open>Error Messages with Line Numbers\<close>

sepref_register \<open>error_msg_notin_dom :: nat \<Rightarrow> string\<close>
  \<open>error_msg_reused_dom :: nat \<Rightarrow> string\<close>
  \<open>error_msg :: nat \<Rightarrow> string \<Rightarrow> string code_status\<close>
  \<open>CFAILED :: string \<Rightarrow> string code_status\<close>

lemma error_msg_notin_dom_alt:
  \<open>error_msg_notin_dom i = show_nat i @ cl_to_clt '' notin domain''\<close>
  by (simp add: error_msg_notin_dom_def error_msg_notin_dom_err_def show_nat_show_int_of_nat cl_to_clt_def
    show_nat_def)

sepref_def error_msg_notin_dom_impl is \<open>RETURN o error_msg_notin_dom\<close>
  :: \<open>si64_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding error_msg_notin_dom_alt
  by sepref

lemma error_msg_reused_dom_alt:
  \<open>error_msg_reused_dom (i :: nat) = show_nat i @ cl_to_clt '' already in domain''\<close>
  by (simp add: error_msg_reused_dom_def show_nat_def cl_to_clt_id)

sepref_def error_msg_reused_dom_impl is \<open>RETURN o error_msg_reused_dom\<close>
  :: \<open>si64_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding error_msg_reused_dom_alt[abs_def]
  by sepref

definition error_msg_alt where
  \<open>error_msg_alt (i :: nat) msg =
    CFAILED (op_clt_to_cl (cl_to_clt ''s CHECKING failed at line '' @ show_nat i
                         @ cl_to_clt '' with error '' @ msg))\<close>

lemma error_msg_correct: \<open>error_msg_alt = error_msg\<close>
  unfolding error_msg_alt_def error_msg_def
  by (simp add: error_msg_def cl_to_clt_id show_nat_def show_nat_show_int_of_nat)

term \<open>uncurry (RETURN oo error_msg_alt)\<close>
term \<open>uncurry (RETURN oo error_msg)\<close>
lemma error_msg_alt_refine:
  \<open>(uncurry (RETURN oo error_msg_alt), uncurry (RETURN oo error_msg))
  \<in> nat_rel \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  using error_msg_correct apply simp
  done

sepref_def error_msg_impl is \<open>uncurry (RETURN oo error_msg_alt)\<close>
  :: \<open>si64_assn\<^sup>k *\<^sub>a strlt_assn\<^sup>d \<rightarrow>\<^sub>a status_assn\<close>
  unfolding error_msg_alt_def
  by sepref

lemmas error_msg_hnr[sepref_fr_rules] = 
  error_msg_impl.refine[FCOMP error_msg_alt_refine]

subsection \<open>Error Messages of the Multiplication\<close>

sepref_register check_mult_l_dom_err

thm show_nat_show_int_of_nat
definition check_mult_l_dom_err_imp where
  \<open>check_mult_l_dom_err_imp pd p ia i =
    (if pd then (cl_to_clt ''The polynomial with id '')
                 @ show_nat p
                 @ (cl_to_clt '' was not found'') else op_clt_empty) @
    (if ia then (cl_to_clt ''The id of the resulting id '')
                 @ show_nat i
                 @ (cl_to_clt '' was already given'') else op_clt_empty)\<close>

sepref_def check_mult_l_dom_err_impl is \<open>uncurry3 (RETURN oooo check_mult_l_dom_err_imp)\<close>
  :: \<open>bool1_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding check_mult_l_dom_err_imp_def 
  by sepref

lemma check_mult_l_dom_err_imp_spec:
  \<open>(uncurry3 (RETURN oooo check_mult_l_dom_err_imp),
  uncurry3 check_mult_l_dom_err)
  \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding check_mult_l_dom_err_imp_def
    check_mult_l_dom_err_def
  by auto

lemmas check_mult_l_dom_err_impl_hnr[sepref_fr_rules] =
  check_mult_l_dom_err_impl.refine[FCOMP check_mult_l_dom_err_imp_spec]

thm poly_print_hnr
definition check_mult_l_mult_err_imp where
  \<open>check_mult_l_mult_err_imp p q pq r =
  cl_to_clt ''Multiplying '' @ poly_print p @ cl_to_clt '' by '' @ poly_print q @
  cl_to_clt '' gives '' @ poly_print pq @ cl_to_clt '' and not '' @ poly_print r\<close>

sepref_def check_mult_l_mult_err_impl is
  \<open>uncurry3 (RETURN oooo check_mult_l_mult_err_imp)\<close> ::
  \<open>polynomial_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k
  \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding check_mult_l_mult_err_imp_def
  by sepref

lemma check_mult_l_mult_err_imp_spec:
  \<open>(uncurry3 (RETURN oooo check_mult_l_mult_err_imp),
  uncurry3 check_mult_l_mult_err) \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding check_mult_l_mult_err_imp_def
    cl_to_clt_id check_mult_l_mult_err_def
  by auto 

lemmas check_mult_l_mult_err_hnr[sepref_fr_rules] = 
  check_mult_l_mult_err_impl.refine[FCOMP check_mult_l_mult_err_imp_spec]

sepref_register check_mult_l_mult_err

subsection \<open>Error Messages of the Extensions\<close>

definition check_ext_l_dom_err_imp :: \<open>nat \<Rightarrow> _\<close>  where
  \<open>check_ext_l_dom_err_imp p =
    cl_to_clt ''There is already a polynomial with index '' @ show_nat p\<close>

sepref_def check_ext_l_dom_err_impl is \<open>RETURN o check_ext_l_dom_err_imp\<close>
  :: \<open>si64_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding check_ext_l_dom_err_imp_def
  by sepref

lemma check_ext_l_dom_err_spec: 
  \<open>(RETURN o check_ext_l_dom_err_imp, check_extension_l_dom_err)
  \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding check_ext_l_dom_err_imp_def check_extension_l_dom_err_def
  by auto 

lemmas check_ext_l_dom_err_hnr[sepref_fr_rules] =
  check_ext_l_dom_err_impl.refine[FCOMP check_ext_l_dom_err_spec]

definition check_extension_l_no_new_var_err_imp :: \<open>llist_polynomial \<Rightarrow> string\<close>  where
  \<open>check_extension_l_no_new_var_err_imp p =
    cl_to_clt ''No new variable could be found in polynomial '' @ poly_print p\<close>

sepref_def check_extension_l_no_new_var_err_impl is \<open>RETURN o check_extension_l_no_new_var_err_imp\<close> 
  :: \<open>polynomial_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding check_extension_l_no_new_var_err_imp_def
  by sepref

lemma check_extension_l_no_new_var_err_spec:
  \<open>(RETURN o check_extension_l_no_new_var_err_imp,
    check_extension_l_no_new_var_err) \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding check_extension_l_no_new_var_err_imp_def
    check_extension_l_no_new_var_err_def
  by auto

lemmas check_extension_l_no_new_var_err_hnr[sepref_fr_rules] =
  check_extension_l_no_new_var_err_impl.refine[FCOMP check_extension_l_no_new_var_err_spec]

definition check_extension_l_side_cond_err_imp :: \<open>_ \<Rightarrow> _\<close>  where
  \<open>check_extension_l_side_cond_err_imp v p r s =
    cl_to_clt ''Error while checking side conditions of extensions polynow, var is '' @ cl_to_clt v @
    cl_to_clt '' polynomial is '' @ poly_print p @
    cl_to_clt ''side condition p*p - p = '' @ poly_print s @ cl_to_clt '' and should be 0''\<close>

sepref_def check_extension_l_side_cond_err_impl is
  \<open>uncurry3 (RETURN oooo check_extension_l_side_cond_err_imp)\<close>
  :: \<open>strl_assn'\<^sup>k *\<^sub>a polynomial_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding check_extension_l_side_cond_err_imp_def
  by sepref

lemma check_extension_l_side_cond_err_spec:
  \<open>(uncurry3 (RETURN oooo check_extension_l_side_cond_err_imp),
    uncurry3 check_extension_l_side_cond_err) \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding check_extension_l_side_cond_err_imp_def
    check_extension_l_side_cond_err_def
  by auto

lemmas check_extension_l_side_cond_err_hnr[sepref_fr_rules] =
  check_extension_l_side_cond_err_impl.refine[FCOMP check_extension_l_side_cond_err_spec]

definition check_extension_l_new_var_multiple_err_imp :: \<open>_ \<Rightarrow> _\<close>  where
  \<open>check_extension_l_new_var_multiple_err_imp v p =
    cl_to_clt ''Error while checking side conditions of extensions polynow, var is '' @ cl_to_clt v @
    cl_to_clt '' but it either appears at least once in the polynomial or another new variable is created '' @
    poly_print p @ cl_to_clt '' but should not.''\<close>

sepref_def check_extension_l_new_var_multiple_err_impl is
  \<open>uncurry (RETURN oo check_extension_l_new_var_multiple_err_imp)\<close>
  :: \<open>strl_assn'\<^sup>k *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding check_extension_l_new_var_multiple_err_imp_def
  by sepref

lemma check_extension_l_new_var_multiple_err_spec:
  \<open>(uncurry (RETURN oo check_extension_l_new_var_multiple_err_imp),
    uncurry check_extension_l_new_var_multiple_err) \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding check_extension_l_new_var_multiple_err_imp_def
    check_extension_l_new_var_multiple_err_def
  by auto

lemmas check_extension_l_new_var_multiple_err_hnr[sepref_fr_rules] =
  check_extension_l_new_var_multiple_err_impl.refine[FCOMP check_extension_l_new_var_multiple_err_spec]


subsection \<open>Error Messages of the Initialisation\<close>

definition remap_polys_l_dom_err_imp :: \<open>_\<close>  where
  \<open>remap_polys_l_dom_err_imp =
    cl_to_clt ''Error during initialisation. Too many polynomials where provided. If this happens, please report the example to the authors.''\<close>

sepref_def remap_polys_l_dom_err_impl is \<open>uncurry0 (RETURN remap_polys_l_dom_err_imp)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding remap_polys_l_dom_err_imp_def
  by sepref

lemma remap_polys_l_dom_err_fref:
  \<open>(uncurry0 (RETURN remap_polys_l_dom_err_imp), uncurry0 remap_polys_l_dom_err)
  \<in> unit_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding remap_polys_l_dom_err_imp_def remap_polys_l_dom_err_def cl_to_clt_id
  by auto

lemmas remap_polys_l_dom_err_hnr[sepref_fr_rules] =
  remap_polys_l_dom_err_impl.refine[FCOMP remap_polys_l_dom_err_fref]

end
