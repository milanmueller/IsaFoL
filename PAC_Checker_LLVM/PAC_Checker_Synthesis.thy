(*
  File:         PAC_Checker_Synthesis.thy
  Author:       Mathias Fleury, Daniela Kaufmann, JKU
  Maintainer:   Mathias Fleury, JKU
*)
theory PAC_Checker_Synthesis
  imports PAC_Checker IICF_HashSet PAC_Step_Assn
    PAC_Checker_Init More_Loops LLVM_String
    IICF_PartialMap PAC_Checker_Relation
begin

section \<open>Code Synthesis of the Complete Checker\<close>

text \<open>We here combine refine the full checker, using the initialisation provided in another file and
adding more efficient data structures (mostly replacing the set of variables by a more efficient
hash map).\<close>

interpretation strl: hashset_env
  \<open>strl_assn'\<close> \<open>strl.cl_free\<close> \<open>strl.cl_copy\<close> \<open>strl.cl_eq\<close>
  \<open>fnv1a_of_strl\<close> \<open>fnv1a_of_strl_impl\<close>
  apply unfold_locales
  by (rule fnv1a_of_strl_hnr)

abbreviation vars_assn where
  \<open>vars_assn \<equiv> strl.hs_assn'\<close>

fun vars_of_monom_in where
  \<open>vars_of_monom_in [] _ = True\<close> |
  \<open>vars_of_monom_in (x # xs) \<V> \<longleftrightarrow> x \<in> \<V> \<and> vars_of_monom_in xs \<V>\<close>

fun vars_of_poly_in where
  \<open>vars_of_poly_in [] _ = True\<close> |
  \<open>vars_of_poly_in ((x, _) # xs) \<V> \<longleftrightarrow> vars_of_monom_in x \<V> \<and> vars_of_poly_in xs \<V>\<close>

lemma vars_of_monom_in_alt_def:
  \<open>vars_of_monom_in xs \<V> \<longleftrightarrow> set xs \<subseteq> \<V>\<close>
  by (induction xs)
   auto

lemma vars_llist_alt_def:
  \<open>vars_llist xs \<subseteq> \<V> \<longleftrightarrow> vars_of_poly_in xs \<V>\<close>
  by (induction xs)
   (auto simp: vars_llist_def vars_of_monom_in_alt_def)

lemma vars_of_monom_in_alt_def2:
  \<open>vars_of_monom_in xs \<V> \<longleftrightarrow> fold (\<lambda>x b. b \<and> x \<in> \<V>) xs True\<close>
  apply (subst foldr_fold[symmetric])
  subgoal by auto
  subgoal by (induction xs) auto
  done

text \<open>We use our custom read only fold for copying lists (to avoid copying)\<close>
definition \<open>fold_inner \<V> \<equiv> \<lambda>b x. b \<and> x \<in> \<V>\<close>
sepref_def fold_inner_impl is \<open>uncurry2 (RETURN ooo fold_inner)\<close>
  :: \<open>vars_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a strl_assn'\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding fold_inner_def
  by sepref
    
definition \<open>vars_of_monom_in_impl xs \<V> \<equiv> cl_fold (fold_inner_impl \<V>) (xs, 1)\<close>

lemma fold_inner_step_rule:
  \<open>llvm_htriple
    ((bool1_assn b bi ** vars_assn \<V> vi) ** strl_assn' x xi)
    (fold_inner_impl vi bi xi)
    (\<lambda>r. (bool1_assn (fold_inner \<V> b x) r ** vars_assn \<V> vi) ** strl_assn' x xi)\<close>
  supply [vcg_rules] = hfref_htriple_k3[OF fold_inner_impl.refine]
  apply vcg
  unfolding ENTAILS_def
  by (auto simp: entails_def pure_def sep_algebra_simps)

lemmas vars_of_monom_walk_rule =
  cl_fold_rule[where R = \<open>\<lambda>b r. bool1_assn b r ** vars_assn \<V> vi\<close>
    and fa = \<open>fold_inner \<V>\<close> and A = strl_assn' for \<V> vi,
    OF fold_inner_step_rule]

lemma vars_of_monom_in_foldl:
  \<open>foldl (fold_inner \<V>) b xs = (b \<and> vars_of_monom_in xs \<V>)\<close>
  by (induction xs arbitrary: b) (auto simp: fold_inner_def)

lemma vars_of_monom_in_impl_hnr[sepref_fr_rules]:
  \<open>(uncurry vars_of_monom_in_impl, uncurry (RETURN oo vars_of_monom_in))
  \<in> monom_assn\<^sup>k *\<^sub>a vars_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding vars_of_monom_in_impl_def
  apply sepref_to_hoare
  supply [vcg_rules] = vars_of_monom_walk_rule
  supply [simp] = vars_of_monom_in_foldl bool1_rel_def bool.rel_def in_br_conv
    pure_def
  by vcg

lemma vars_of_poly_in_alt_def2:
  \<open>vars_of_poly_in xs \<V> \<longleftrightarrow> fold (\<lambda>(x, _) b. b \<and> vars_of_monom_in x \<V>) xs True\<close>
  apply (subst foldr_fold[symmetric])
  subgoal by auto
  subgoal by (induction xs) auto
  done

text \<open>Again, we can use our readonly cl_fold; the step of the outer walk is the
  monom walk (on the pair's first component), synthesized by sepref from the
  registered monom rule.\<close>
definition \<open>vars_of_poly_in_inner \<V> \<equiv> \<lambda>b (vs, _). b \<and> vars_of_monom_in vs \<V>\<close>

sepref_def vars_of_poly_in_inner_impl is \<open>uncurry2 (RETURN ooo vars_of_poly_in_inner)\<close>
  :: \<open>vars_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a monomial_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding vars_of_poly_in_inner_def
  by sepref

definition \<open>vars_of_poly_in_impl xs \<V> \<equiv> cl_fold (vars_of_poly_in_inner_impl \<V>) (xs, 1)\<close>

lemma vars_of_poly_in_inner_step_rule:
  \<open>llvm_htriple
    ((bool1_assn b bi ** vars_assn \<V> vi) ** monomial_assn x xi)
    (vars_of_poly_in_inner_impl vi bi xi)
    (\<lambda>r. (bool1_assn (vars_of_poly_in_inner \<V> b x) r ** vars_assn \<V> vi) ** monomial_assn x xi)\<close>
  supply [vcg_rules] = hfref_htriple_k3[OF vars_of_poly_in_inner_impl.refine]
  apply vcg
  unfolding ENTAILS_def
  by (auto simp: entails_def pure_def sep_algebra_simps)

lemmas vars_of_poly_walk_rule =
  cl_fold_rule[where R = \<open>\<lambda>b r. bool1_assn b r ** vars_assn \<V> vi\<close>
    and fa = \<open>vars_of_poly_in_inner \<V>\<close> and A = monomial_assn for \<V> vi,
    OF vars_of_poly_in_inner_step_rule]

lemma vars_of_poly_in_foldl:
  \<open>foldl (vars_of_poly_in_inner \<V>) b xs = (b \<and> vars_of_poly_in xs \<V>)\<close>
  apply (induction xs arbitrary: b)
  subgoal by simp
  subgoal for p xs b by (cases p) (auto simp: vars_of_poly_in_inner_def)
  done

lemma vars_of_poly_in_impl_hnr[sepref_fr_rules]:
  \<open>(uncurry vars_of_poly_in_impl, uncurry (RETURN oo vars_of_poly_in))
  \<in> polynomial_assn\<^sup>k *\<^sub>a vars_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding vars_of_poly_in_impl_def
  apply sepref_to_hoare
  supply [vcg_rules] = vars_of_poly_walk_rule
  supply [simp] = vars_of_poly_in_foldl bool1_rel_def bool.rel_def in_br_conv
    pure_def
  by vcg

definition union_vars_monom :: \<open>string list \<Rightarrow> string set \<Rightarrow> string set\<close> where
\<open>union_vars_monom xs \<V> = fold insert xs \<V>\<close>

definition \<open>insert' \<equiv> \<lambda>\<V> x. insert (COPY x) \<V>\<close>

sepref_def insert'_impl is \<open>uncurry (RETURN oo insert')\<close>
  :: \<open>vars_assn\<^sup>d *\<^sub>a strl_assn'\<^sup>k \<rightarrow>\<^sub>a vars_assn\<close>
  unfolding insert'_def
  by sepref
  
lemma union_vars_monom_alt: \<open>union_vars_monom xs \<V> = foldl insert' \<V> xs\<close>
  unfolding union_vars_monom_def insert'_def COPY_def
  by (auto simp: foldl_conv_fold)

definition \<open>union_vars_monom_impl xs \<V> \<equiv> cl_fold insert'_impl (xs, \<V>)\<close>

lemma insert'_step_rule: \<open>llvm_htriple
    (vars_assn \<V> \<V>i ** strl_assn' x xi)
    (insert'_impl \<V>i xi)
    (\<lambda>r. vars_assn (insert' \<V> x) r ** strl_assn' x xi)\<close>
  supply [vcg_rules] = hfref_htriple_d1_k2[OF insert'_impl.refine]
  by vcg

lemma union_vars_monom_impl_hnr[sepref_fr_rules]:
  \<open>(uncurry union_vars_monom_impl, uncurry (RETURN oo union_vars_monom))
  \<in> monom_assn\<^sup>k *\<^sub>a vars_assn\<^sup>d \<rightarrow>\<^sub>a vars_assn\<close>
  unfolding union_vars_monom_alt union_vars_monom_impl_def
  apply sepref_to_hoare
  supply [vcg_rules] = cl_fold_rule[where
    R = \<open>vars_assn\<close> and A = \<open>strl_assn'\<close>
    and f = \<open>insert'_impl\<close>
    and fa = \<open>insert'\<close>,
    OF insert'_step_rule]
  by vcg

definition union_vars_poly :: \<open>llist_polynomial \<Rightarrow> string set \<Rightarrow> string set\<close> where
\<open>union_vars_poly xs \<V> = fold (\<lambda>(xs, _) \<V>. union_vars_monom xs \<V>) xs \<V>\<close>

definition \<open>union_vars_poly_inner \<equiv> \<lambda>\<V> (xs,_). union_vars_monom xs \<V>\<close>

sepref_register union_vars_monom
sepref_def union_vars_poly_inner_impl is \<open>uncurry (RETURN oo union_vars_poly_inner)\<close>
  :: \<open>vars_assn\<^sup>d *\<^sub>a monomial_assn\<^sup>k \<rightarrow>\<^sub>a vars_assn\<close>
  unfolding union_vars_poly_inner_def
  by sepref

lemma union_vars_poly_comp: \<open>union_vars_poly xs \<V> = foldl union_vars_poly_inner \<V> xs\<close>
  unfolding union_vars_poly_def union_vars_poly_inner_def
  by (simp add: foldl_conv_fold split_def)

definition \<open>union_vars_poly_impl xsi \<V>i \<equiv> cl_fold (union_vars_poly_inner_impl) (xsi, \<V>i)\<close>

lemma union_vars_poly_inner_step_rule: \<open>llvm_htriple
    (vars_assn \<V> \<V>i ** monomial_assn m mi)
    (union_vars_poly_inner_impl \<V>i mi)
    (\<lambda>r. vars_assn (union_vars_poly_inner \<V> m) r ** monomial_assn m mi)\<close>
  supply [vcg_rules] = hfref_htriple_d1_k2[OF union_vars_poly_inner_impl.refine]
  by vcg

lemma union_vars_poly_impl_hnr[sepref_fr_rules]:
  \<open>(uncurry union_vars_poly_impl, uncurry (RETURN oo union_vars_poly))
  \<in> polynomial_assn\<^sup>k *\<^sub>a vars_assn\<^sup>d \<rightarrow>\<^sub>a vars_assn\<close>
  unfolding union_vars_poly_comp union_vars_poly_impl_def
  apply sepref_to_hoare
  supply [vcg_rules] = cl_fold_rule[where
    R = \<open>vars_assn\<close> and A = \<open>monomial_assn\<close>
    and f = \<open>union_vars_poly_inner_impl\<close>
    and fa = \<open>union_vars_poly_inner\<close>,
    OF union_vars_poly_inner_step_rule]
  by vcg

lemma union_vars_monom_alt_def:
  \<open>union_vars_monom xs \<V> = \<V> \<union> set xs\<close>
  unfolding union_vars_monom_def
  apply (subst foldr_fold[symmetric])
  subgoal for x y
    by (cases x; cases y) auto
  subgoal
    by (induction xs) auto
  done

lemma union_vars_poly_alt_def:
  \<open>union_vars_poly xs \<V> = \<V> \<union> vars_llist xs\<close>
  unfolding union_vars_poly_def
  apply (subst foldr_fold[symmetric])
  subgoal for x y
    by (cases x; cases y)
      (auto simp: union_vars_monom_alt_def)
  subgoal
    by (induction xs)
     (auto simp: vars_llist_def union_vars_monom_alt_def)
   done

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

text \<open>The tag is determined by the discriminators. Stating this once keeps the discriminator
  implementations free of a case split on @{typ \<open>string code_status\<close>}: unfolding
  @{thm status_assn_def} in those proofs leaves a @{term case_code_status} applied to a state,
  which the simplifier will not split.\<close>
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
    invalid_assn_def)

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
  where[llvm_code]: \<open>merge_cstatus_impl \<equiv> \<lambda>(t1,msg1) (t2,msg2). doM {
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

end

sepref_def add_poly_l_impl is \<open>uncurry add_poly_l\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a polynomial_assn\<close>
  unfolding add_poly_l_def add_poly_l1_def add_poly_l2_def
    apl_cond_def apl_body_def apl2_body_def ls_emp term_order_rel_by_lt
  by sepref

lemma var_order_rel_alt: \<open>(x,y) \<in> var_order_rel \<equiv> x < y\<close>
  unfolding var_order_rel_def less_char_def p2rel_def
  by (simp add: List.lexordp_def less_char_def less_char_inst
    less_list_def)

definition \<open>mult_monoms_inner p\<^sub>0 q\<^sub>0 \<equiv> WHILEIT
    (\<lambda>(r,p,q). mult_monoms p\<^sub>0 q\<^sub>0 = r @ mult_monoms p q)
    (\<lambda>(r,p,q). p\<noteq>[] \<and> q\<noteq>[])
    (\<lambda>(r,p,q). doN {
      (x,p) \<leftarrow> mop_list_pop_hd p;
      (y,q) \<leftarrow> mop_list_pop_hd q;
      if x = y then
        RETURN (op_list_append r x, p, q)
      else if (x,y) \<in> var_order_rel then
        RETURN (op_list_append r x, p, y#q)
      else 
        RETURN  (op_list_append r y, x#p, q)
    }) ([], p\<^sub>0, q\<^sub>0)\<close>

abbreviation \<open>monom_assn_tail \<equiv> clt_assn' strl_assn'\<close>

sepref_def mult_monoms_inner_impl is \<open>uncurry mult_monoms_inner\<close>
  :: \<open>monom_assn\<^sup>d *\<^sub>a monom_assn\<^sup>d \<rightarrow>\<^sub>a (monom_assn_tail \<times>\<^sub>a monom_assn \<times>\<^sub>a monom_assn)\<close>
  unfolding mult_monoms_inner_def ls_emp var_order_rel_alt
  unfolding fold_clt_empty 
  by sepref

lemma mult_monoms_inner_refine:
  \<open>mult_monoms_inner p\<^sub>0 q\<^sub>0 \<le> SPEC (\<lambda>(r,p,q). mult_monoms p\<^sub>0 q\<^sub>0 = r @ mult_monoms p q \<and> (p = [] \<or> q = []))\<close>
  unfolding mult_monoms_inner_def
  apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>(r,p,q). length p + length q)"])
  apply clarsimp_all
  apply (metis list.exhaust_sel mult_monoms.simps(3))+
  done

definition \<open>mult_monoms_alt \<equiv> \<lambda>p q. doN { 
    (r,p',q') \<leftarrow> mult_monoms_inner (COPY p) (COPY q);
    let rcl = op_clt_to_cl r;
    RETURN (rcl @ p' @ q')
  }\<close>

lemma mult_monoms_Nil_right[simp]: \<open>mult_monoms p [] = p\<close>
  by (cases p) auto

lemma mult_monoms_Nil_left[simp]: \<open>mult_monoms [] q = q\<close>
  by (cases q) auto

lemma mult_monoms_alt_spec:
  \<open>mult_monoms_alt p q \<le> SPEC (\<lambda>r. r = mult_monoms p q)\<close>
  unfolding mult_monoms_alt_def op_clt_to_cl_def COPY_def
  by (refine_vcg mult_monoms_inner_refine[THEN order_trans]) auto

lemma mult_monoms_alt_refine:
  \<open>(uncurry mult_monoms_alt, uncurry (RETURN oo mult_monoms))
  \<in> Id \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (auto simp: RETURN_SPEC_conv)
  using mult_monoms_alt_spec by auto

sepref_register mult_monoms_inner
sepref_def mult_monoms_impl is \<open>uncurry mult_monoms_alt\<close>
  :: \<open>monom_assn\<^sup>k *\<^sub>a monom_assn\<^sup>k \<rightarrow>\<^sub>a monom_assn\<close>
  unfolding mult_monoms_alt_def
  by sepref

lemmas mult_monoms_hnr[sepref_fr_rules] =
  mult_monoms_impl.refine[FCOMP mult_monoms_alt_refine]

sepref_def mult_monomials_impl
  is \<open>uncurry (RETURN oo mult_monomials)\<close>
  :: \<open>monomial_assn\<^sup>k *\<^sub>a monomial_assn\<^sup>k \<rightarrow>\<^sub>a monomial_assn\<close>
  unfolding mult_monomials_def
  by sepref

type_synonym monomial_abs = \<open>(term_poly_list \<times> int)\<close>
abbreviation \<open>polynomial_assn_tail \<equiv> clt_assn' monomial_assn\<close>

definition mult_poly_raw_inner :: \<open>monomial_abs \<Rightarrow> llist_polynomial \<Rightarrow> monomial_abs \<Rightarrow> llist_polynomial\<close>
  where \<open>mult_poly_raw_inner pm b qm \<equiv> b @ [(mult_monomials pm qm)]\<close>

sepref_register mult_monomials
sepref_def mult_poly_raw_inner_impl is \<open>uncurry2 (RETURN ooo mult_poly_raw_inner)\<close>
  :: \<open>monomial_assn\<^sup>k *\<^sub>a polynomial_assn_tail\<^sup>d *\<^sub>a monomial_assn\<^sup>k \<rightarrow>\<^sub>a polynomial_assn_tail\<close>
  unfolding mult_poly_raw_inner_def
  by sepref

definition poly_row_fold :: \<open>monomial_abs \<Rightarrow> llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> llist_polynomial\<close>
  where \<open>poly_row_fold pm \<equiv> foldl (mult_poly_raw_inner pm)\<close>

sepref_register poly_row_fold
lemma poly_row_fold_hnr[sepref_fr_rules]:
  \<open>(uncurry2 (\<lambda>pmi. cl_fold' (mult_poly_raw_inner_impl pmi)),
    uncurry2 (RETURN ooo poly_row_fold))
    \<in> monomial_assn\<^sup>k *\<^sub>a polynomial_assn_tail\<^sup>d *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a polynomial_assn_tail\<close>
  unfolding poly_row_fold_def[abs_def]
  by (rule cl_fold_hfref_param[OF mult_poly_raw_inner_impl.refine])

definition mult_poly_raw_inner2 :: \<open>monomial_abs \<Rightarrow> llist_polynomial \<Rightarrow> llist_polynomial\<close>
  where \<open>mult_poly_raw_inner2 pm q \<equiv> poly_row_fold pm [] q\<close>

sepref_register mult_poly_raw_inner2
sepref_def mult_poly_raw_inner2_impl is \<open>uncurry (RETURN oo mult_poly_raw_inner2)\<close>
  :: \<open>monomial_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a polynomial_assn_tail\<close>
  unfolding mult_poly_raw_inner2_def
  unfolding fold_clt_empty
  by sepref

definition mult_poly_raw_outer :: \<open>llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> monomial_abs \<Rightarrow> llist_polynomial\<close>
  where \<open>mult_poly_raw_outer q b pm \<equiv> mult_poly_raw_inner2 pm q @ b\<close>

sepref_def mult_poly_raw_outer_impl is \<open>uncurry2 (RETURN ooo mult_poly_raw_outer)\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a polynomial_assn_tail\<^sup>d *\<^sub>a monomial_assn\<^sup>k \<rightarrow>\<^sub>a polynomial_assn_tail\<close>
  unfolding mult_poly_raw_outer_def
  by sepref

definition poly_mult_fold :: \<open>llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> llist_polynomial\<close>
  where \<open>poly_mult_fold q \<equiv> foldl (mult_poly_raw_outer q)\<close>

sepref_register poly_mult_fold
lemma poly_mult_fold_hnr[sepref_fr_rules]:
  \<open>(uncurry2 (\<lambda>qi. cl_fold' (mult_poly_raw_outer_impl qi)),
    uncurry2 (RETURN ooo poly_mult_fold))
    \<in> polynomial_assn\<^sup>k *\<^sub>a polynomial_assn_tail\<^sup>d *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a polynomial_assn_tail\<close>
  unfolding poly_mult_fold_def[abs_def]
  by (rule cl_fold_hfref_param[OF mult_poly_raw_outer_impl.refine])

lemma foldl_snoc_conv_map: \<open>foldl (\<lambda>b x. b @ [g x]) b\<^sub>0 xs = b\<^sub>0 @ map g xs\<close>
  by (induction xs arbitrary: b\<^sub>0) auto

lemma mult_poly_raw_inner2_map: \<open>mult_poly_raw_inner2 pm q = map (mult_monomials pm) q\<close>
  unfolding mult_poly_raw_inner2_def poly_row_fold_def mult_poly_raw_inner_def[abs_def]
  by (simp add: foldl_snoc_conv_map)

lemma mult_poly_raw_alt:
  \<open>mult_poly_raw p q = op_clt_to_cl (poly_mult_fold q [] p)\<close>
  unfolding mult_poly_raw_def poly_mult_fold_def mult_poly_raw_outer_def[abs_def]
    op_clt_to_cl_def
  by (simp add: mult_poly_raw_inner2_map)

sepref_def mult_poly_raw_impl
  is \<open>uncurry (RETURN oo mult_poly_raw)\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a polynomial_assn\<close>
  unfolding mult_poly_raw_alt
  unfolding fold_clt_empty
  by sepref

definition merge_coeffs_inner :: \<open>llist_polynomial \<Rightarrow> (llist_polynomial \<times> llist_polynomial) nres\<close> where
  \<open>merge_coeffs_inner p\<^sub>0 \<equiv> WHILEIT
  (\<lambda>(r,p). merge_coeffs p\<^sub>0 = r @ merge_coeffs p)
  (\<lambda>(r,p). p\<noteq>[])
  (\<lambda>(r,p). doN {
    ((xs,n),p) \<leftarrow> mop_list_pop_hd p;
    if p=[] then RETURN (op_list_append r (xs,n), p)
    else doN {
      ((ys,m),p) \<leftarrow> mop_list_pop_hd p;
      if xs = ys then doN {
        let s = n + m;
        if s = 0 then RETURN (r,p)
        else RETURN (r, (xs, s)#p)
      }
      else
        RETURN (op_list_append r (xs,n), (ys,m)#p)
    }
  }) ([], p\<^sub>0)\<close>

lemma merge_coeffs_inner_refine:
  \<open>merge_coeffs_inner p\<^sub>0 \<le> SPEC (\<lambda>(r,p). r = merge_coeffs p\<^sub>0 \<and> p = [])\<close>
  unfolding merge_coeffs_inner_def
  apply (refine_vcg WHILEIT_rule[where R=\<open>measure (\<lambda>(r,p). length p)\<close>])
  apply clarsimp_all
  apply (metis list.exhaust_sel merge_coeffs.simps(2) merge_coeffs.simps(3))+
  done

definition merge_coeffs_alt :: \<open>llist_polynomial \<Rightarrow> llist_polynomial nres\<close> where
  \<open>merge_coeffs_alt p \<equiv> doN {
    (r, p') \<leftarrow> merge_coeffs_inner p;
    let rcl = op_clt_to_cl r;
    RETURN (rcl @ p')
  }\<close>

lemma merge_coeffs_alt_spec:
  \<open>merge_coeffs_alt p \<le> SPEC (\<lambda>r. r = merge_coeffs p)\<close>
  unfolding merge_coeffs_alt_def op_clt_to_cl_def
  by (refine_vcg merge_coeffs_inner_refine[THEN order_trans]) auto

lemma merge_coeffs_alt_refine:
  \<open>(merge_coeffs_alt, RETURN o merge_coeffs) \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (auto simp: RETURN_SPEC_conv)
  using merge_coeffs_alt_spec by auto

sepref_register merge_coeffs_inner
sepref_def merge_coeffs_inner_impl is \<open>merge_coeffs_inner\<close>
  :: \<open>polynomial_assn\<^sup>d \<rightarrow>\<^sub>a (polynomial_assn_tail \<times>\<^sub>a polynomial_assn)\<close>
  unfolding merge_coeffs_inner_def ls_emp ls_emp'
  unfolding fold_clt_empty
  by sepref

sepref_def merge_coeffs_impl is \<open>merge_coeffs_alt\<close>
  :: \<open>polynomial_assn\<^sup>d \<rightarrow>\<^sub>a polynomial_assn\<close>
  unfolding merge_coeffs_alt_def
  by sepref

lemmas merge_coeffs_hnr[sepref_fr_rules] =
  merge_coeffs_impl.refine[FCOMP merge_coeffs_alt_refine]

sepref_def mult_poly_impl
  is \<open>uncurry mult_poly_full\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a polynomial_assn\<close>
  unfolding mult_poly_full_def normalize_poly_def
  by sepref

declare mult_poly_impl.refine[sepref_fr_rules]

sepref_register \<open>(=) :: llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> bool\<close>
sepref_def weak_equality_l_impl
  is \<open>uncurry weak_equality_l\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding weak_equality_l_def
  by sepref
    
declare weak_equality_l_impl.refine[sepref_fr_rules]

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

text \<open>No \<open>nres\<close> detour and no \<open>fref\<close> is needed: the program stays the exact abstract
  @{term error_msg}, and the conversion to the array representation (including its
  truncation) happens inside @{thm FAILED_hnr}.\<close>
lemma error_msg_alt:
  \<open>error_msg (i :: nat) msg =
    CFAILED (op_clt_to_cl (cl_to_clt ''s CHECKING failed at line '' @ show_nat i
                         @ cl_to_clt '' with error '' @ msg))\<close>
  by (simp add: error_msg_def cl_to_clt_id show_nat_def show_nat_show_int_of_nat)

sepref_def error_msg_impl is \<open>uncurry (RETURN oo error_msg)\<close>
  :: \<open>si64_assn\<^sup>k *\<^sub>a strlt_assn\<^sup>d \<rightarrow>\<^sub>a status_assn\<close>
  unfolding error_msg_alt[abs_def]
  by sepref

interpretation polys: boxed_copying_pmap
  \<open>polynomial_assn\<close> \<open>poly.cl_free\<close> \<open>poly.cl_copy\<close>
  apply unfold_locales
  subgoal by (rule poly.cl_assn_free)
  subgoal by (rule poly.cl_copy_hnr)
  done

abbreviation polys_assn where
  \<open>polys_assn \<equiv> hr_comp (hr_comp polys.bx.pmap_assn' opt_list_map_rel) map_fmap_rel\<close>

lemma polys_assn_intf[intf_of_assn]:
  \<open>intf_of_assn polys_assn TYPE((nat, (char list list \<times> int) list) f_map)\<close>
  by simp

(* These lemmas used to exist similarly in PAC_Map_Rel.thy *)
lemmas fmap_empty_hnr[sepref_fr_rules] =
  polys.bx.pmap_empty_hnr2[FCOMP fmempty_empty]

lemmas fmap_delete_hnr[sepref_fr_rules] =
  polys.bx.pmap_delete_hnr2[FCOMP fmdrop_set_None]

lemmas fmap_update_hnr[sepref_fr_rules] =
  polys.bx.pmap_update_hnr2[FCOMP map_upd_fmupd]

lemmas fmap_lookup_hnr[sepref_fr_rules] =
  polys.bx.cpmap_lookup_hnr2[FCOMP op_map_lookup_fmlookup]

sepref_register fmlookup' :: \<open>'k \<Rightarrow> ('k, 'v) f_map \<Rightarrow> 'v option\<close>

lemma map_fmap_contains_key:
  \<open>(uncurry (RETURN oo op_map_contains_key), uncurry (RETURN oo op_fmap_contains_key))
     \<in> Id \<times>\<^sub>r map_fmap_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: op_map_contains_key_def op_fmap_contains_key_def map_fmap_rel_def
      br_def in_fdom_alt fmap.Abs_fmap_inverse split: option.splits)

lemmas fmap_contains_key_hnr[sepref_fr_rules] =
  polys.bx.pmap_contains_key_hnr2[FCOMP map_fmap_contains_key]

lemma in_dom_by_contains: \<open>k\<in># dom_m A = op_fmap_contains_key k A\<close>
  unfolding op_fmap_contains_key_def by simp

sepref_decl_op fmap_the_lookup: \<open>\<lambda>k m. the (fmlookup' k m)\<close>
  :: \<open>[\<lambda>(k, m). k \<in># dom_m m]\<^sub>f K \<times>\<^sub>r \<langle>K,V\<rangle>fmap_rel \<rightarrow> V\<close>
  using fmap_rel_in_dom_iff by fastforce

(* lemma the_lookup_alt:
 *   \<open>the (fmlookup' k m) = UNBOX (op_fmap_the_lookup k m)\<close>
 *   by simp *)

lemma op_the_lookup_refine:
  \<open>(uncurry (RETURN oo op_map_the_lookup), uncurry (RETURN oo op_fmap_the_lookup))
     \<in> [\<lambda>(k, m). k \<in># dom_m m]\<^sub>f Id \<times>\<^sub>r map_fmap_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  by (auto simp: map_fmap_rel_def br_def in_fdom_alt fmap.Abs_fmap_inverse)

lemma map_fmap_rel_dom_iff[fcomp_prenorm_simps]:
  \<open>(m, fm) \<in> map_fmap_rel \<Longrightarrow> (\<exists>y. m k = Some y) \<longleftrightarrow> k \<in># dom_m fm\<close>
  by (auto simp: map_fmap_rel_def br_def in_fdom_alt fmap.Abs_fmap_inverse)

lemmas fmap_the_lookup_hnr[sepref_fr_rules] =
  polys.bx.cpmap_the_lookup_hnr2[FCOMP op_the_lookup_refine]

lemma pat_fmap_the_lookup[def_pat_rules]:
  \<open>the$(fmlookup'$k$m) \<equiv> UNBOX$(op_fmap_the_lookup$k$m)\<close>
  by (simp add: UNBOX_def)

term error_msg
sepref_def check_addition_l_impl
  is \<open>uncurry6 check_addition_l\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a vars_assn\<^sup>k *\<^sub>a
  si64_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k
  \<rightarrow>\<^sub>a status_assn\<close>
  supply [[goals_limit=1]]
  unfolding
    check_addition_l_def
    mult_poly_full_def
    vars_llist_alt_def
    fmlookup'_def[symmetric]
    in_dom_by_contains
    fold_clt_empty
  by sepref

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
sepref_def check_mult_l_impl
  is \<open>uncurry6 check_mult_l\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a vars_assn\<^sup>k *\<^sub>a
  si64_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>k  \<rightarrow>\<^sub>a status_assn\<close>
  supply [[goals_limit=1]]
  unfolding check_mult_l_def
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    in_dom_by_contains
    fmlookup'_def[symmetric]
    vars_llist_alt_def
  by sepref


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

definition uminus_poly :: \<open>llist_polynomial \<Rightarrow> llist_polynomial\<close> where
  \<open>uminus_poly p = map (\<lambda>(a,b). (a,-b)) p\<close>

definition uminus_poly_nres :: \<open>llist_polynomial \<Rightarrow> llist_polynomial nres\<close> where
  \<open>uminus_poly_nres = REC\<^sub>T (\<lambda>f p.
    if p = [] then RETURN p
    else do {
      ((a,b), p) \<leftarrow> mop_list_pop_hd p;
      r \<leftarrow> f p; RETURN ((a, -b) # r)
    })\<close>

lemma uminus_poly_nres_spec: \<open>uminus_poly_nres p = RETURN (uminus_poly p)\<close>
  unfolding uminus_poly_nres_def uminus_poly_def
proof (induction p)
  case Nil
  show ?case by (subst RECT_unfold, refine_mono) auto
next
  case (Cons x p)
  show ?case
    apply (subst RECT_unfold, refine_mono)
    by (auto simp: Cons.IH split: prod.splits)
qed

sepref_register uminus_poly

sepref_def uminus_poly_impl is \<open>uminus_poly_nres\<close>
  :: \<open>polynomial_assn\<^sup>d \<rightarrow>\<^sub>a polynomial_assn\<close>
  unfolding uminus_poly_nres_def
  by sepref

lemma uminus_poly_fref:
  \<open>(uminus_poly_nres, RETURN o uminus_poly) \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: uminus_poly_nres_spec)

lemmas uminus_poly_hnr[sepref_fr_rules] =
  uminus_poly_impl.refine[FCOMP uminus_poly_fref]

definition mnml_eq :: \<open>monomial_abs \<Rightarrow> monomial_abs \<Rightarrow> bool\<close> where
  \<open>mnml_eq a b \<longleftrightarrow> a = b\<close>

sepref_register mnml_eq

lemma mnml_eq_op_hnr[sepref_fr_rules]:
  \<open>(uncurry mnml_eq_impl', uncurry (RETURN oo mnml_eq))
  \<in> monomial_assn\<^sup>k *\<^sub>a monomial_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding mnml_eq_def by (rule mnml_eq_hnr)

definition remove1_imp :: \<open>monomial_abs \<Rightarrow> llist_polynomial \<Rightarrow> llist_polynomial nres\<close> where
  \<open>remove1_imp r cs \<equiv> REC\<^sub>T (\<lambda>f cs.
    if cs=[] then RETURN cs
    else doN {
      (c,cs) \<leftarrow> mop_list_pop_hd cs;
      if mnml_eq c r then
        RETURN cs
      else doN {
        rs \<leftarrow> f cs;
        RETURN (c#rs) 
      }
    }
  ) cs\<close>

lemma remove1_imp_spec:
  \<open>remove1_imp r cs = RETURN (remove1 r cs)\<close>
  unfolding remove1_imp_def
proof (induction cs)
  case Nil
  show ?case by (subst RECT_unfold, refine_mono) auto
next
  case (Cons c cs)
  show ?case
    apply (subst RECT_unfold, refine_mono)
    by (auto simp: mop_list_pop_hd_def mnml_eq_def Cons.IH pw_eq_iff refine_pw_simps)
qed

lemma remove1_imp_correct:
  \<open>(RETURN oo remove1) = remove1_imp\<close>
  by (intro ext) (simp add: remove1_imp_spec)

term \<open>uncurry poly.cl_eq\<close>
term \<open>uncurry (RETURN oo (=))\<close>
sepref_def remove1_impl is \<open>uncurry (RETURN oo remove1)\<close>
  :: \<open>monomial_assn\<^sup>k *\<^sub>a polynomial_assn\<^sup>d\<rightarrow>\<^sub>a polynomial_assn\<close>
  unfolding remove1_imp_correct remove1_imp_def
    ls_emp
  apply sepref_dbg_keep
  apply sepref_dbg_id_keep

(* TODO: check if we could also make the string destructively alternatively *)
lemma check_extension_l_alt:
  \<open>check_extension_l spec A \<V> i v p = do {
    let b = i \<notin># dom_m A \<and> v \<notin> \<V> \<and> ([COPY v], -1) \<in> set p;
    if \<not>b
    then do {
      c \<leftarrow> check_extension_l_dom_err i;
      RETURN (error_msg i c)
    } else do {
        p' \<leftarrow> remove1_imp ([COPY v], -1) p;
        let b = vars_llist p' \<subseteq> \<V>;
        if \<not>b
        then do {
          c \<leftarrow> check_extension_l_new_var_multiple_err v p';
          RETURN (error_msg i c)
        }
        else do {
           p2 \<leftarrow> mult_poly_full p' p';
           let p' = map (\<lambda>(a,b). (a, -b)) p';
           q \<leftarrow> add_poly_l p2 p';
           eq \<leftarrow> weak_equality_l q [];
           if eq then do {
             RETURN (CSUCCESS)
           } else do {
            c \<leftarrow> check_extension_l_side_cond_err v p p' q;
            RETURN (error_msg i c)
          }
        }
      }
    }\<close>
  unfolding check_extension_l_def COPY_def
  by simp

thm remove1_impl.refine
sepref_register remove1
sepref_def check_extension_l_impl
  is \<open>uncurry5 check_extension_l\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a vars_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k *\<^sub>a strl_assn'\<^sup>k *\<^sub>a polynomial_assn\<^sup>k \<rightarrow>\<^sub>a
     status_assn\<close>
  (* supply [[show_types]] *)
  unfolding check_extension_l_alt
    fmlookup'_def[symmetric]
    in_dom_by_contains
    vars_llist_alt_def
    uminus_poly_def[symmetric]
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply sepref_dbg_side_unfold

  oops

sepref_def check_del_l_impl
  is \<open>uncurry2 check_del_l\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a si64_assn\<^sup>k \<rightarrow>\<^sub>a status_assn\<close>
  supply [[goals_limit=1]]
  unfolding check_del_l_def
    in_dom_by_contains
    fmlookup'_def[symmetric]
  by sepref

abbreviation pac_step_rel where
  \<open>pac_step_rel \<equiv> p2rel (\<langle>Id, \<langle>Id\<rangle>list_rel, Id\<rangle> pac_step_rel_raw)\<close>

sepref_register PAC_Polynomials_Operations.normalize_poly
  pac_src1 pac_src2 new_id pac_mult case_pac_step check_mult_l
  check_addition_l check_del_l check_extension_l

lemma is_Mult_lastI:
  \<open>\<not> is_Add b \<Longrightarrow> \<not>is_Mult b \<Longrightarrow> \<not>is_Extension b \<Longrightarrow> is_Del b\<close>
  by (cases b) auto

sepref_register is_cfailed is_Del

definition PAC_checker_l_step' ::  _ where
  \<open>PAC_checker_l_step' a b c d = PAC_checker_l_step a (b, c, d)\<close>

lemma PAC_checker_l_step_alt_def:
  \<open>PAC_checker_l_step a bcd e = (let (b,c,d) = bcd in PAC_checker_l_step' a b c d e)\<close>
  unfolding PAC_checker_l_step'_def by auto

sepref_decl_intf ('k) acode_status is "('k) code_status"
sepref_decl_intf ('k, 'b, 'lbl) apac_step is "('k, 'b, 'lbl) pac_step"

sepref_register merge_cstatus full_normalize_poly new_var is_Add

term pac_step_assn
sepref_def check_step_impl
  is \<open>uncurry4 PAC_checker_l_step'\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a status_assn\<^sup>d *\<^sub>a vars_assn\<^sup>d *\<^sub>a polys_assn\<^sup>d *\<^sub>a pac_step_assn\<^sup>d
  \<rightarrow>\<^sub>a status_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
  unfolding PAC_checker_l_step_def PAC_checker_l_step'_def
    pac_step.case_eq_if Let_def
     is_success_alt_def[symmetric]
    uminus_poly_def[symmetric]
  apply sepref_dbg_keep
  oops

definition PAC_checker_l' where
  \<open>PAC_checker_l' p \<V> A status steps = PAC_checker_l p (\<V>, A) status steps\<close>

lemma PAC_checker_l_alt_def:
  \<open>PAC_checker_l p \<V>A status steps =
    (let (\<V>, A) = \<V>A in PAC_checker_l' p \<V> A status steps)\<close>
  unfolding PAC_checker_l'_def by auto

sepref_def PAC_checker_l_impl
  is \<open>uncurry4 PAC_checker_l'\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a vars_assn\<^sup>d *\<^sub>a polys_assn\<^sup>d *\<^sub>a status_assn \<^sup>d *\<^sub>a (cl_assn' pac_step_assn)\<^sup>k \<rightarrow>\<^sub>a
     status_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
  unfolding PAC_checker_l_def is_success_alt_def[symmetric] PAC_checker_l_step_alt_def
    nres_bind_let_law[symmetric] PAC_checker_l'_def
  apply (subst nres_bind_let_law)
  apply sepref_dbg_keep
  oops

definition remap_polys_l_dom_err_imp :: \<open>_\<close>  where
  \<open>remap_polys_l_dom_err_imp =
    cl_to_clt ''Error during initialisation. Too many polynomials where provided. If this happens,'' @
    cl_to_clt ''please report the example to the authors, because something went wrong during '' @
    cl_to_clt ''code generation (code generation to arrays is likely to be broken).''\<close>

sepref_def remap_polys_l_dom_err_impl is \<open>uncurry0 (RETURN remap_polys_l_dom_err_imp)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a strlt_assn\<close>
  unfolding remap_polys_l_dom_err_imp_def
  by sepref

lemma remap_polys_l_dom_err_fref:
  \<open>(uncurry0 (RETURN remap_polys_l_dom_err_imp), uncurry0 remap_polys_l_dom_err)
  \<in> unit_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  unfolding remap_polys_l_dom_err_imp_def remap_polys_l_dom_err_def cl_to_clt_id
  apply auto
  oops

lemmas remap_polys_l_dom_err_hnr[sepref_fr_rules] =
  remapt_polys_l_dom_err_impl.refine[FCOMP remap_polys_l_dom_err_fref]

lemma pow_2_64: \<open>(2::nat) ^ 64 = 18446744073709551616\<close>
  by auto

abbreviation polys_assn_input where
  \<open>polys_assn_input \<equiv> iam_fmap_assn nat_assn poly_assn\<close>

sepref_register upper_bound_on_dom op_fmap_empty

sepref_def remap_polys_l_impl
  is \<open>uncurry2 remap_polys_l2\<close>
  :: \<open>polynomial_assn\<^sup>k *\<^sub>a vars_assn\<^sup>d *\<^sub>a polys_assn_input\<^sup>d \<rightarrow>\<^sub>a
    status_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro] indom_mI[dest]
  unfolding remap_polys_l2_def op_fmap_empty_def[symmetric] while_eq_nfoldli[symmetric]
    while_upt_while_direct pow_2_64
    in_dom_m_lookup_iff
    fmlookup'_def[symmetric]
    union_vars_poly_alt_def[symmetric]
  apply (rewrite at \<open>fmupd \<hole>\<close> uint64_of_nat_conv_def[symmetric])
  apply (subst while_upt_while_direct)
  apply simp
  apply (rewrite at \<open>op_fmap_empty\<close> annotate_assn[where A=\<open>polys_assn\<close>])
  by sepref

lemma remap_polys_l2_remap_polys_l:
  \<open>(uncurry2 remap_polys_l2, uncurry2 remap_polys_l) \<in> (Id \<times>\<^sub>r \<langle>Id\<rangle>set_rel) \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI fun_relI nres_relI)
  using remap_polys_l2_remap_polys_l by auto

lemma [sepref_fr_rules]:
   \<open>(uncurry2 remap_polys_l_impl,
     uncurry2 remap_polys_l) \<in> polynomial_assn\<^sup>k *\<^sub>a vars_assn\<^sup>d *\<^sub>a polys_assn_input\<^sup>d \<rightarrow>\<^sub>a
       status_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
   using hfcomp_tcomp_pre[OF remap_polys_l2_remap_polys_l remap_polys_l_impl.refine]
   by (auto simp: hrp_comp_def hfprod_def)

sepref_register remap_polys_l

sepref_def full_checker_l_impl
  is \<open>uncurry2 full_checker_l\<close>
  :: \<open>polynomial_assn\<^sup>d *\<^sub>a polys_assn_input\<^sup>d *\<^sub>a (cl_assn' pac_step_assn)\<^sup>d \<rightarrow>\<^sub>a
    status_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro]
  unfolding full_checker_l_def hs.fold_custom_empty
    union_vars_poly_alt_def[symmetric]
    PAC_checker_l_alt_def
  by sepref

sepref_def PAC_update_impl
  is \<open>uncurry2 (RETURN ooo fmupd)\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a polys_assn_input\<^sup>d \<rightarrow>\<^sub>a polys_assn_input\<close>
  unfolding comp_def
  by sepref

sepref_def PAC_empty_impl
  is \<open>uncurry0 (RETURN fmempty)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a polys_assn_input\<close>
  unfolding op_iam_fmap_empty_def[symmetric] pat_fmap_empty
  by sepref

sepref_def empty_vars_impl
  is \<open>uncurry0 (RETURN {})\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a vars_assn\<close>
  unfolding hs.fold_custom_empty
  by sepref
section \<open>Correctness theorem\<close>

context poly_embed
begin

definition full_poly_assn where
  \<open>full_poly_assn = hr_comp poly_assn (fully_unsorted_poly_rel O mset_poly_rel)\<close>

definition full_poly_input_assn where
  \<open>full_poly_input_assn = hr_comp
        (hr_comp polys_assn_input
          (\<langle>nat_rel, fully_unsorted_poly_rel O mset_poly_rel\<rangle>fmap_rel))
        polys_rel\<close>

definition fully_pac_assn where
  \<open>fully_pac_assn = (list_assn
        (hr_comp (pac_step_rel_assn uint64_nat_assn poly_assn string_assn)
          (p2rel
            (\<langle>nat_rel,
             fully_unsorted_poly_rel O
             mset_poly_rel, var_rel\<rangle>pac_step_rel_raw))))\<close>

definition code_status_assn where
  \<open>code_status_assn = hr_comp (status_assn raw_string_assn)
                            code_status_status_rel\<close>

definition full_vars_assn where
  \<open>full_vars_assn = hr_comp (hs.assn string_assn)
                              (\<langle>var_rel\<rangle>set_rel)\<close>

lemma polys_rel_full_polys_rel:
  \<open>polys_rel_full = Id \<times>\<^sub>r polys_rel\<close>
  by (auto simp: polys_rel_full_def)

definition full_polys_assn :: \<open>_\<close> where
\<open>full_polys_assn = hr_comp (hr_comp polys_assn
                              (\<langle>nat_rel,
                               sorted_poly_rel O mset_poly_rel\<rangle>fmap_rel))
                            polys_rel\<close>

text \<open>

Below is the full correctness theorems. It basically states that:

  \<^enum> assuming that the input polynomials have no duplicate variables


Then:

\<^enum> if the checker returns \<^term>\<open>CFOUND\<close>, the spec is in the ideal
  and the PAC file is correct

\<^enum> if the checker returns \<^term>\<open>CSUCCESS\<close>, the PAC file is correct (but
there is no information on the spec, aka checking failed)

\<^enum> if the checker return \<^term>\<open>CFAILED err\<close>, then checking failed (and
\<^term>\<open>err\<close> \<^emph>\<open>might\<close> give you an indication of the error, but the correctness
theorem does not say anything about that).


The input parameters are:

\<^enum> the specification polynomial represented as a list

\<^enum> the input polynomials as hash map (as an array of option polynomial)

\<^enum> a represention of the PAC proofs.

\<close>

lemma PAC_full_correctness: (* \htmllink{PAC-full-correctness} *)
  \<open>(uncurry2 full_checker_l_impl,
     uncurry2 (\<lambda>spec A _. PAC_checker_specification spec A))
    \<in> (full_poly_assn)\<^sup>k *\<^sub>a (full_poly_input_assn)\<^sup>d *\<^sub>a (fully_pac_assn)\<^sup>k \<rightarrow>\<^sub>a hr_comp
      (code_status_assn \<times>\<^sub>a full_vars_assn \<times>\<^sub>a hr_comp polys_assn
                              (\<langle>nat_rel, sorted_poly_rel O mset_poly_rel\<rangle>fmap_rel))
                            {((st, G), st', G').
                             st = st' \<and> (st \<noteq> FAILED \<longrightarrow> (G, G') \<in> Id \<times>\<^sub>r polys_rel)}\<close>
  using
    full_checker_l_impl.refine[FCOMP full_checker_l_full_checker',
      FCOMP full_checker_spec',
      unfolded full_poly_assn_def[symmetric]
        full_poly_input_assn_def[symmetric]
        fully_pac_assn_def[symmetric]
        code_status_assn_def[symmetric]
        full_vars_assn_def[symmetric]
        polys_rel_full_polys_rel
        hr_comp_prod_conv
        full_polys_assn_def[symmetric]]
      hr_comp_Id2
   by auto

text \<open>

It would be more efficient to move the parsing to Isabelle, as this
would be more memory efficient (and also reduce the TCB). But now
comes the fun part: It cannot work. A stream (of a file) is consumed
by side effects. Assume that this would work. The code could look like:

\<^term>\<open>
  let next_token = read_file file
  in f (next_token)
\<close>

This code is equal to (in the HOL sense of equality):
\<^term>\<open>
  let _ = read_file file;
      next_token = read_file file
  in f (next_token)
\<close>

However, as an hypothetical \<^term>\<open>read_file\<close> changes the underlying stream, we would get the next
token. Remark that this is already a weird point of ML compilers. Anyway, I see currently two
solutions to this problem:

\<^enum> The meta-argument: use it only in the Refinement Framework in a setup where copies are
disallowed. Basically, this works because we can express the non-duplication constraints on the type
level. However, we cannot forbid people from expressing things directly at the HOL level.

\<^enum> On the target language side, model the stream as the stream and the position. Reading takes two
arguments. First, the position to read. Second, the stream (and the current position) to read. If
the position to read does not match the current position, return an error. This would fit the
correctness theorem of the code generation (roughly ``if it terminates without exception, the answer
is the same''), but it is still unsatisfactory.
\<close>

end

definition \<phi> :: \<open>string \<Rightarrow> nat\<close> where
  \<open>\<phi> = (SOME \<phi>. bij \<phi>)\<close>

lemma bij_\<phi>: \<open>bij \<phi>\<close>
  using someI[of \<open>\<lambda>\<phi> :: string \<Rightarrow> nat. bij \<phi>\<close>]
  unfolding \<phi>_def[symmetric]
  using poly_embed_EX
  by auto

global_interpretation PAC: poly_embed where
  \<phi> = \<phi>
  apply standard
  apply (use bij_\<phi> in \<open>auto simp: bij_def\<close>)
  done


text \<open>The full correctness theorem is @{thm PAC.PAC_full_correctness}.\<close>

end
