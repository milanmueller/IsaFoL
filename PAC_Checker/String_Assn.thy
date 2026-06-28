theory String_Assn
  imports Isabelle_LLVM.LLVM_DS_Open_List Char_Assn
begin

text \<open>Implement Chars as Open Lists\<close>

type_synonym str = \<open>char list\<close>

term larray_assn

definition \<open>str_assn \<equiv> hr_comp \<upharpoonleft>os_list_assn (\<langle>the_pure char_assn\<rangle>list_rel)\<close>
lemma str_assn_pure: \<open>is_pure str_assn\<close>
  unfolding str_assn_def os_list_assn_def 
  (* do we have any chance here? I don't think we do... *)
  oops

(* We have to implement some functions for open lists which are not there yet *)
definition os_hd :: \<open>'a::llvm_rep os_list \<Rightarrow> 'a llM\<close> where[llvm_code]:
  \<open>os_hd p = doM { v \<leftarrow> ll_load p; Mreturn (node.val v)}\<close>

lemma os_hd_rule[vcg_rules]:
  \<open>xs \<noteq> [] \<Longrightarrow> llvm_htriple (\<upharpoonleft>os_list_assn xs r) (os_hd r) (\<lambda>x. \<up>(x=hd xs) ** \<upharpoonleft>os_list_assn xs r)\<close>
  apply (cases xs; simp)
  unfolding os_hd_def os_list_assn_def
  by vcg

definition os_tl :: \<open>'a::llvm_rep os_list \<Rightarrow> 'a os_list llM\<close> where[llvm_code]:
  \<open>os_tl p = doM {
    n \<leftarrow> ll_load p;
    ll_free p;
    Mreturn (node.next n)
  }\<close>

lemma op_tl_rule[vcg_rules]:
  \<open>xs \<noteq> [] \<Longrightarrow> llvm_htriple (\<upharpoonleft>os_list_assn xs r) (os_tl r) (\<lambda>x. \<upharpoonleft>os_list_assn (tl xs) x)\<close>
  apply (cases xs; simp)
  unfolding os_tl_def os_list_assn_def
  by vcg

definition os_list_get :: \<open>'a::llvm_rep os_list \<Rightarrow> 'b::len word \<Rightarrow> 'a llM\<close> where [llvm_code]:
  \<open>os_list_get p\<^sub>0 i\<^sub>0 = doM {
    (p, _) \<leftarrow> llc_while
      (\<lambda>(_, i). ll_cmp (i \<noteq> 0))
      (\<lambda>(p, i). doM {
        n \<leftarrow> ll_load p; 
        Mreturn (node.next n, i - 1)
      }) (p\<^sub>0, i\<^sub>0);
    n \<leftarrow> ll_load p;
    Mreturn (node.val n)
  }\<close>

lemma os_list_get_rule[vcg_rules]:
  \<open>unat i < length xs \<Longrightarrow> llvm_htriple
    (\<upharpoonleft>os_list_assn xs p)
    (os_list_get p i)
    (\<lambda>v. \<up>(v = xs ! unat i) ** \<upharpoonleft>os_list_assn xs p)\<close>
  unfolding os_list_get_def
  apply (rewrite annotate_llc_while [where
    I="\<lambda>(q, ii) _. lseg (take (unat i - unat ii) xs) p q
                 ** lseg (drop (unat i - unat ii) xs) q null
                 ** \<up>(unat ii \<le> unat i)"
    and R="measure (\<lambda>(_, ii). unat ii)"])
  apply vcg
  apply (simp add: os_list_assn_def; fri)
  subgoal by (auto simp: SOLVE_AUTO_DEFER_def)
  apply vcg
  \<comment> \<open>Loop body. State: pointer \<open>a\<close>, counter \<open>b\<close> with \<open>unat b \<le> unat i\<close>.
      Heap: \<open>lseg (take (unat i - unat b) xs) p a \<and>* lseg (drop (unat i - unat b) xs) a null\<close>.
      Goal: evaluate \<open>ll_cmp (b \<noteq> 0)\<close>, then per ctd branch (continue / return).\<close>
  subgoal premises prems for asf a b aa ba sa
    using prems
    apply (cases \<open>b = 0\<close>)
    subgoal
      \<comment> \<open>Terminate: \<open>b = 0\<close>, so \<open>drop (unat i) xs \<noteq> []\<close>
          (since \<open>unat i < length xs\<close>); decompose with \<open>lseg_Cons\<close>,
          load the node, return \<open>node.val n = xs ! unat i\<close>.\<close>
      \<comment> \<open>Expose the head of \<open>drop (unat i) xs\<close> so \<open>lseg_Cons\<close> can fire
          and \<open>vcg\<close> sees the \<open>ll_bpto\<close> at \<open>a\<close>. (Do NOT unfold
          \<open>ABSTRACT_def\<close> here \<mdash> \<open>vcg\<close> has a decomposition rule
          \<open>ABSTRACT_erule[vcg_decomp_erules]\<close> that handles the abstraction
          step automatically.)\<close>
      apply (subgoal_tac \<open>drop (unat i) xs = (xs ! unat i) # drop (Suc (unat i)) xs\<close>)
       prefer 2 subgoal by (simp add: Cons_nth_drop_Suc)
      \<comment> \<open>\<open>lseg_Cons\<close> + \<open>sep_conj_exists\<close> rewrites the heap layout to
          \<open>EXS x. lseg (take ...) p a \<and>* ll_bpto (Node (xs!unat i) x) a \<and>*
                  lseg (drop (Suc (unat i)) xs) x null \<and>* ↑(a \<noteq> null)\<close>.
          \<open>vcg_normalize_simps\<close> contains \<open>STATE_extract\<close> which lifts that
          \<open>EXS x\<close> out of the \<open>STATE\<close> wrapper to the meta-level; \<open>elim exE\<close>
          then introduces a fresh \<open>x\<close>.\<close>
      apply (simp add: lseg_Cons sep_conj_exists vcg_normalize_simps)
      apply (elim exE)
      \<comment> \<open>State is now \<open>STATE asf (lseg (take ...) p a \<and>*
            ll_bpto (Node (xs!unat i) x) a \<and>* lseg (drop (Suc ...) xs) x null \<and>*
            \<up>(a \<noteq> null)) sa\<close>, goal is
          \<open>wpa asf (ll_cmp False) (\<lambda>ctdi s. ABSTRACT asf ctdi bool.assn (\<lambda>ctd. ...))\<close>.
          Manually evaluate the \<open>ll_cmp False = Mreturn 0\<close> via
          \<open>vcg_normalize_simps\<close> (contains \<open>wpa_return\<close>), then unfold the
          ABSTRACT structure to reveal both branches, and drop the
          \<open>aa \<longrightarrow> ...\<close> branch using \<open>bool.assn False (from_bool False)\<close>.\<close>
      apply (simp add: ll_cmp_def vcg_normalize_simps ABSTRACT_def bool.assn_def
              Sepref_Basic.pure_def sep_algebra_simps pred_lift_extract_simps)
      \<comment> \<open>Residual: \<open>(\<exists>F. STATE asf F sa) \<and> wpa _ (ll_load a; return node.val n) _\<close>.
          First conjunct trivial. For the second, \<open>vcg\<close> consumes the load
          via \<open>ll_bpto\<close>; reassembly via \<open>id_take_nth_drop\<close> + \<open>lseg_append\<close>.\<close>
      apply (rule conjI)
      subgoal by blast
      apply vcg
      \<comment> \<open>Residual entailment: \<open>ll_bpto (Node (xs!i) x) a \<and>* lseg (drop (Suc i) xs) x null
            \<and>* lseg (take i xs) p a \<turnstile> lseg xs p null\<close>. Rewrite \<open>xs\<close> as
          \<open>take i xs @ xs!i # drop (Suc i) xs\<close> and let \<open>lseg_append\<close>+\<open>lseg_Cons\<close>
          + \<open>fri\<close> match the layout.\<close>
      apply (simp add: os_list_assn_def)
      \<comment> \<open>Residual entailment, all LLVM operations discharged:
          \<open>ll_bpto (Node (xs!i) x) a \<and>* lseg (drop (Suc i) xs) x null \<and>*
            lseg (take i xs) p a \<turnstile> \<up>True \<and>* lseg xs p null\<close>.
          The plan: fuse \<open>ll_bpto (Node (xs!i) x) a \<and>* lseg (drop (Suc i) xs) x null\<close>
          into \<open>lseg (xs!i # drop (Suc i) xs) a null\<close> via \<open>lseg_Cons\<close> with
          witness \<open>x\<close>, fold to \<open>lseg (drop i xs) a null\<close> via the
          \<open>drop (unat i) xs = ...\<close> hypothesis, then \<open>lseg_fuse\<close> +
          \<open>append_take_drop_id\<close> to reassemble \<open>lseg xs p null\<close>.
          \<open>subst\<close>-numbering on \<open>id_take_nth_drop\<close> is brittle because
          the lemma's RHS reintroduces \<open>xs\<close>; the cleaner route is the
          fuse direction above (or a structured Isar block with an
          intermediate \<open>have\<close>).\<close>
      apply (simp add: ENTAILS_def entails_def )
      sorry
    subgoal
      \<comment> \<open>Continue: \<open>b \<noteq> 0\<close>, so \<open>unat i - unat b < unat i \<le> length xs\<close>,
          hence \<open>drop (unat i - unat b) xs \<noteq> []\<close>. Decompose, load,
          step to \<open>(node.next n, b - 1)\<close>. New invariant index:
          \<open>unat i - unat (b - 1) = Suc (unat i - unat b)\<close>; rebuild
          the \<open>take\<close> using \<open>take_Suc_conv_app_nth\<close>.\<close>
      sorry
    done
  done

definition os_list_length :: \<open>'a::llvm_rep os_list \<Rightarrow> 'b::len word llM\<close> where [llvm_code]:
  \<open>os_list_length p\<^sub>0 = doM {
    (_, n) \<leftarrow> llc_while
      (\<lambda>(p, _). ll_cmp (p \<noteq> null))
      (\<lambda>(p, n). doM {
        nd \<leftarrow> ll_load p;
        Mreturn (node.next nd, n + 1)
      }) (p\<^sub>0, 0);
    Mreturn n
  }\<close>
lemma os_list_length_rule[vcg_rules]:
  \<open>llvm_htriple
    (\<upharpoonleft>os_list_assn xs p)
    (os_list_length p)
    (\<lambda>n. \<up>(unat n = length xs) ** \<upharpoonleft>os_list_assn xs p)\<close>
  unfolding os_list_length_def
  apply (rewrite annotate_llc_while [where
    I = \<open>\<lambda>(p', n) _. lseg (take (unat n) xs) p p'
                   ** lseg (drop (unat n) xs) p' null
                   ** \<up>(unat n \<le> length xs)\<close>
    and R = \<open>measure (\<lambda>(_, n). length xs - unat n)\<close>])
  apply vcg
  apply (simp add: os_list_assn_def; fri)
  subgoal by (auto simp: SOLVE_AUTO_DEFER_def)
  apply vcg
  \<comment> \<open>Loop body. State: pointer \<open>p'\<close>, counter \<open>n\<close> with \<open>unat n \<le> length xs\<close>.
      Heap: \<open>lseg (take (unat n) xs) p p' \<and>* lseg (drop (unat n) xs) p' null\<close>.
      Goal: evaluate \<open>ll_cmp (p' \<noteq> null)\<close>, then per ctd branch (continue / return).\<close>
  subgoal premises prems for asf p' n aa ba sa
    using prems
    apply (cases \<open>p' = null\<close>)
    subgoal
      \<comment> \<open>Terminate: \<open>p' = null\<close>, so \<open>lseg (drop (unat n) xs) null null\<close>
          forces \<open>drop (unat n) xs = []\<close>, i.e. \<open>length xs \<le> unat n\<close>.
          Combined with the invariant \<open>unat n \<le> length xs\<close>: \<open>unat n = length xs\<close>.
          Return \<open>n\<close>; reassemble \<open>os_list_assn xs p\<close> via \<open>lseg_append\<close>.\<close>
      sorry
    subgoal
      \<comment> \<open>Continue: \<open>p' \<noteq> null\<close>, so \<open>drop (unat n) xs \<noteq> []\<close>, hence
          \<open>unat n < length xs\<close>. Decompose with \<open>lseg_Cons\<close>, load, step
          to \<open>(node.next nd, n + 1)\<close>. NB: re-establishing the invariant
          needs \<open>unat (n + 1) = unat n + 1\<close> i.e. no wrap-around — requires
          a bound \<open>length xs < 2^LENGTH('b)\<close> currently missing from the
          lemma's precondition.\<close>
      sorry
    done
  done

(* Now we specialize open lists to string *)
lemma str_empty_refine[sepref_fr_rules]:
  \<open>(uncurry0 os_empty, uncurry0 (RETURN op_list_empty)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a str_assn\<close>
  unfolding os_empty_def op_list_empty_def
  apply sepref_to_hoare
  apply vcg
  by (auto simp: str_assn_def ENTAILS_def entails_def os_list_assn_def hr_comp_def sep_algebra_simps)
    
lemma str_is_empty_refine[sepref_fr_rules]:
  \<open>(os_is_empty, RETURN o op_list_is_empty) \<in> [\<lambda>_. True]\<^sub>a str_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  unfolding os_is_empty_def str_assn_def op_list_is_empty_def 
  apply sepref_to_hoare
  subgoal for x xi
    apply (cases x; cases \<open>xi=null\<close>; simp)
    subgoal
      apply vcg
      apply (simp add: sep_algebra_simps ENTAILS_def entails_def hr_comp_def os_list_assn_def)
      by (metis bool.rel_def bool1_rel_def brI from_bool_to_bool_iff)
    subgoal
      apply vcg
      by (simp add: sep_algebra_simps ENTAILS_def hr_comp_def os_list_assn_def)
    subgoal
      apply vcg
      by (simp add: sep_algebra_simps ENTAILS_def hr_comp_def os_list_assn_def) 
    subgoal
      apply vcg
      by (auto simp: ENTAILS_def entails_def sep_algebra_simps hr_comp_def
        os_list_assn_def bool1_rel_def bool.rel_def in_br_conv)
    done
  done

lemma str_hd_refine[sepref_fr_rules]:
  \<open>(os_hd, RETURN o op_list_hd) \<in> [\<lambda>xs. xs \<noteq> []]\<^sub>a str_assn\<^sup>k \<rightarrow> char_assn\<close>
  unfolding str_assn_def op_list_hd_def hr_comp_def 
  apply sepref_to_hoare
  apply auto
  apply vcg
  subgoal by auto
  subgoal
    apply (simp add: sep_algebra_simps EXTRACT_def POSTCOND_def STATE_def list_rel_def os_list_assn_def)
    by (metis (no_types, lifting) Sepref_Basic.pure_def char_assn_def
    list.rel_cases list.sel(1) pred_lift_extract_simps(2) sep_conj_commuteI
    the_pure_pure)
  done 

lemma str_tl_refine[sepref_fr_rules]:
  \<open>(os_tl, RETURN o op_list_tl) \<in> [\<lambda>xs. xs \<noteq> []]\<^sub>a str_assn\<^sup>d \<rightarrow> str_assn\<close>
  unfolding str_assn_def op_list_tl_def hr_comp_def
  apply sepref_to_hoare
  apply auto
  apply vcg
  subgoal by auto
  subgoal
    apply (simp add: sep_algebra_simps STATE_def EXTRACT_def POSTCOND_def
            os_list_assn_def list_rel_def)
    using list.rel_sel by blast  
  done

lemma str_prepend_refine[sepref_fr_rules]:
  \<open>(uncurry os_prepend, uncurry (RETURN oo op_list_prepend)) \<in> char_assn\<^sup>k *\<^sub>a str_assn\<^sup>d \<rightarrow>\<^sub>a str_assn\<close>
  unfolding str_assn_def os_prepend_def op_list_prepend_def
  apply sepref_to_hoare
  apply (auto simp: os_list_assn_def hr_comp_def)
  apply vcg
  apply (auto simp: sep_algebra_simps ENTAILS_def entails_def list_rel_def os_list_assn_def
          char_assn_def char_rel_def in_br_conv char_of_word_def br_def)
  by (metis (lifting) list.simps(11) lseg_Cons mem_Collect_eq old.prod.case
    pred_lift_extract_simps(2) pure_app_eq sep_conj_aci(3))

lemma str_assn_mk_free[sepref_frame_free_rules]:
  \<open>MK_FREE str_assn os_delete\<close>
  apply (rule MK_FREEI)
  unfolding str_assn_def hr_comp_def 
  by vcg

lemma str_get_refine[sepref_fr_rules]:
  \<open>(uncurry os_list_get, uncurry (RETURN oo op_list_get)) \<in>
  [\<lambda>(xs,i). i < length xs]\<^sub>a str_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(64))\<^sup>k \<rightarrow> char_assn\<close>
  unfolding op_list_get_def
  apply sepref_to_hoare
  apply (simp add: str_assn_def hr_comp_def os_list_assn_simps)
  apply vcg
  apply (simp add: sep_algebra_simps STATE_def EXTRACT_def POSTCOND_def snat_rel_def snat.rel_def
    os_list_assn_def
    snat_invar_def ll_cmp_def list_rel_def char_assn_def char_rel_def in_br_conv char_of_word_def)
  subgoal by (metis snat_invar_def snat_eq_unat_aux2 list_all2_lengthD)
  subgoal for bi a ai asf x sa
    (* Residual: pick witness ⟨x⟩, then separation-logic split of the heap
       into ⟨os_list_assn x ai⟩ ∗ pure ⟨char_assn (a!snat bi) (x!unat bi)⟩.
       Pattern in ⟨str_hd_refine⟩ uses ⟨list.rel_cases⟩ on the head; here
       we'd need ⟨list_all2_conv_all_nth⟩ at index ⟨snat bi = unat bi⟩. *)
    sorry
  done

(* NOTE: lemma as stated is not provable without a precondition like
   ⟨length xs < 2^(LENGTH('b) - 1)⟩ guaranteeing the result fits as snat.
   After existing tactics + this auto, the residual goal is
   ⟨length x = snat r⟩ and ⟨msb r ⟹ False⟩; the second cannot be discharged
   without such a bound. *)
lemma str_len_refine[sepref_fr_rules]:
  \<open>(os_list_length, RETURN o op_list_length) \<in> str_assn\<^sup>k \<rightarrow>\<^sub>a (snat_assn' TYPE(64))\<close>
  apply sepref_to_hoare
  apply (simp add: str_assn_def hr_comp_def os_list_assn_simps)
  apply vcg
  apply (simp add: sep_algebra_simps STATE_def EXTRACT_def POSTCOND_def os_list_assn_def
          list_rel_def char_assn_def char_rel_def in_br_conv char_of_word_def)
  apply (auto simp: ENTAILS_def entails_def snat_rel_def snat.rel_def br_def
          snat_invar_def list_all2_lengthD sep_algebra_simps pred_lift_extract_simps
          snat_eq_unat)
  sorry

experiment begin

  definition test :: \<open>str \<Rightarrow> char\<close> where
    \<open>test cs \<equiv> (if cs = [] then (char_of_word (0::(8 word))) else hd cs)\<close>

  sepref_def test_impl is \<open>RETURN o test\<close>
    :: \<open>str_assn\<^sup>k \<rightarrow>\<^sub>a char_assn\<close>
    unfolding test_def 
    by sepref

  (* export_llvm \<open>test_impl\<close> *)

  definition empty_check :: \<open>str \<Rightarrow> bool\<close> where
    \<open>empty_check cs \<equiv> cs = []\<close>

  sepref_def empty_check_impl is \<open>RETURN o empty_check\<close>
    :: \<open>str_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
    unfolding empty_check_def
    by sepref

  (* export_llvm empty_check_impl *)

  definition cons_test :: \<open>str \<Rightarrow> char \<Rightarrow> str\<close> where
    \<open>cons_test cs c = c # cs\<close>

  sepref_def cons_test_impl is \<open>uncurry (RETURN oo cons_test)\<close>
    :: \<open>str_assn\<^sup>d *\<^sub>a char_assn\<^sup>k \<rightarrow>\<^sub>a str_assn\<close>
    unfolding cons_test_def
    by sepref

  definition tail_test :: \<open>str \<Rightarrow> str\<close> where
    \<open>tail_test cs = (if cs = [] then cs else tl cs)\<close>

  sepref_def tail_test_impl is \<open>RETURN o tail_test\<close>
    :: \<open>str_assn\<^sup>d \<rightarrow>\<^sub>a str_assn\<close>
    unfolding tail_test_def
    by sepref

  (* definition swap_test' :: \<open>str \<Rightarrow> str\<close> where
   *   \<open>swap_test' cs = (if cs = [] then cs else
   *     let a = hd cs; bs = tl cs in
   *     a # bs
   *   )\<close> *)

  definition dest_cons_test :: \<open>str \<Rightarrow> str\<close> where
    \<open>dest_cons_test cs = (case cs of
      [] \<Rightarrow> cs
    | (c # cs') \<Rightarrow> c # cs'
    )\<close>

  sepref_def dest_cons_test_impl is \<open>RETURN o dest_cons_test\<close>
    :: \<open>str_assn\<^sup>d \<rightarrow>\<^sub>a str_assn\<close>
    unfolding dest_cons_test_def
    apply sepref_dbg_keep
    apply sepref_dbg_trans_keep
    apply sepref_dbg_trans_step_keep
    apply sepref_dbg_side_unfold
    oops

end

end
