theory LPAC_Codegen
  imports LPAC_Efficient_Checker_Synthesis
begin

text \<open>This theory exports all LLVM functions required for the C parser alongside a C header:
  builder functions for the checker's inputs and the checker entry point itself.\<close>
text \<open>The c-parser must by able to construct
  \<^item> @{term polynomiala_assn} - the target/spec polynomial.
  \<^item> @{term polysa_assn} - the given list of indexed polynomials.
  \<^item> @{term lpac_stepa_assn} - proof steps (and a list of steps.)
  We implement some basic builder functions that allow constructing these objects from primitives. 
\<close>

section \<open>Generic list builders\<close>
text \<open>All lists are built with the tail-pointer list @{term clt_assn'} (append in O(1)) and
  finally converted into the plain list @{term cl_assn'} that the checker consumes
  (@{term clt_to_cl}). A @{typ \<open>'a clt_list\<close>} is a by-value pair of pointers, which the C
  calling convention cannot pass; the builder is therefore boxed into a heap cell that
  @{term clt_builder_append} updates in place and @{term clt_builder_finish} frees again.\<close>

definition clt_builder_new :: \<open>'a::llvm_rep clt_list ptr llM\<close> where [llvm_code, llvm_inline]:
  \<open>clt_builder_new = doM { b \<leftarrow> clt_empty; ll_ref b }\<close>

definition clt_builder_append :: \<open>'a::llvm_rep clt_list ptr \<Rightarrow> 'a \<Rightarrow> unit llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>clt_builder_append bp x = doM { b \<leftarrow> ll_load bp; b' \<leftarrow> clt_snoc b x; ll_store b' bp }\<close>

definition clt_builder_finish :: \<open>'a::llvm_rep clt_list ptr \<Rightarrow> 'a cl_list llM\<close>
  where [llvm_code, llvm_inline]:
  \<open>clt_builder_finish bp = doM { b \<leftarrow> ll_load bp; ll_free bp; clt_to_cl b }\<close>

section \<open>Terms\<close>
text \<open>@{term monoma_assn} are constructed as a list of @{term stra_assn}.
  An array-based string can be directly built from C; \<open>term_append\<close> takes its two fields
  separately because the code exporter does not support nested types as parameters.\<close>

sepref_def term_emp is \<open>uncurry0 (RETURN [])\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a monoma_assn\<close>
  by sepref

definition term_builder_new :: \<open>stra_conc clt_list ptr llM\<close> where [llvm_code]:
  \<open>term_builder_new = clt_builder_new\<close>

definition term_append :: \<open>stra_conc clt_list ptr \<Rightarrow> 64 word \<Rightarrow> 8 word ptr \<Rightarrow> unit llM\<close>
  where [llvm_code]:
  \<open>term_append bp n p = clt_builder_append bp (n, p)\<close>

definition term_finish :: \<open>stra_conc clt_list ptr \<Rightarrow> monoma_conc llM\<close> where [llvm_code]:
  \<open>term_finish = clt_builder_finish\<close>

subsection \<open>Strings\<close>
text \<open>The (verified) string \<rightarrow> signed_big_int conversion, given by @{term str_sval_nres}
  expects a list of characters as input.\<close>

sepref_def strl_emp is \<open>uncurry0 (RETURN [])\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a strl_assn'\<close>
  by sepref

definition strl_builder_new :: \<open>8 word clt_list ptr llM\<close> where [llvm_code]:
  \<open>strl_builder_new = clt_builder_new\<close>

definition strl_append :: \<open>8 word clt_list ptr \<Rightarrow> 8 word \<Rightarrow> unit llM\<close> where [llvm_code]:
  \<open>strl_append = clt_builder_append\<close>

definition strl_finish :: \<open>8 word clt_list ptr \<Rightarrow> 8 word cl_list llM\<close> where [llvm_code]:
  \<open>strl_finish = clt_builder_finish\<close>

text \<open>Terms and character lists contain only 64-bit and 8-bit words and pointers, so the
  header generator can describe them completely. \<open>int64_t\<close> documents that lengths are
  \<open>snat\<close> values (most significant bit clear).\<close>
export_llvm
  term_emp is \<open>strnode* term_emp()\<close>
  term_builder_new is \<open>term_builder* term_builder_new()\<close>
  term_append is \<open>void term_append(term_builder*, int64_t, char*)\<close>
  term_finish is \<open>strnode* term_finish(term_builder*)\<close>
  strl_emp is \<open>charnode* strl_emp()\<close>
  strl_builder_new is \<open>strl_builder* strl_builder_new()\<close>
  strl_append is \<open>void strl_append(strl_builder*, char)\<close>
  strl_finish is \<open>charnode* strl_finish(strl_builder*)\<close>
  defines \<open>
    typedef struct {int64_t len; char *ptr;} stra;
    typedef struct {stra s; strnode *next;} strnode;
    typedef struct {strnode *head; strnode *tail;} term_builder;
    typedef struct {char c; charnode *next;} charnode;
    typedef struct {charnode *head; charnode *tail;} strl_builder;
  \<close>
  rewrites \<open>stra_conc node\<close> = strnode
           \<open>stra_conc clt_list\<close> = term_builder
           \<open>8 word node\<close> = charnode
           \<open>8 word clt_list\<close> = strl_builder
  file "code/term.ll"

section \<open>Big Integers\<close>
text \<open>The sign flag of @{typ sbi_conc} is a 1-bit word, which the header generator cannot
  express, and @{term str_sval_impl} returns the big integer by value. Everything from here on
  is therefore exported without a generated header; the hand-written
  \<^file>\<open>code/pasteque.h\<close> declares all remaining types as opaque structs.\<close>

definition str_sval_c :: \<open>8 word node ptr \<Rightarrow> sbi_conc ptr llM\<close> where [llvm_code]:
  \<open>str_sval_c l = doM { r \<leftarrow> str_sval_impl l; ll_ref r }\<close>

section \<open>Polynomials\<close>

sepref_def polynomial_emp is \<open>uncurry0 (RETURN [])\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a polynomiala_assn\<close>
  by sepref

definition polynomial_builder_new :: \<open>monomiala_conc clt_list ptr llM\<close> where [llvm_code]:
  \<open>polynomial_builder_new = clt_builder_new\<close>

text \<open>Takes the term and the boxed coefficient produced by @{term str_sval_c}; the box cell is
  freed here, and both are owned by the polynomial afterwards.\<close>
definition polynomial_append
  :: \<open>monomiala_conc clt_list ptr \<Rightarrow> monoma_conc \<Rightarrow> sbi_conc ptr \<Rightarrow> unit llM\<close> where [llvm_code]:
  \<open>polynomial_append bp t cp = doM { c \<leftarrow> ll_load cp; ll_free cp; clt_builder_append bp (t, c) }\<close>

definition polynomial_finish :: \<open>monomiala_conc clt_list ptr \<Rightarrow> polya_conc llM\<close> where [llvm_code]:
  \<open>polynomial_finish = clt_builder_finish\<close>

subsection \<open>Polynomial maps\<close>
text \<open>The map of indexed input polynomials. Values are stored boxed (\<open>polysa.bx\<close>), so the
  abstract update tags the value with @{term BOX}. \<open>sepref_def\<close> registers its result as
  refinement rule and rejects a \<open>\<lambda>\<close>-abstraction as abstract head, hence the named
  abstract operation.\<close>

sepref_def polymap_emp is \<open>uncurry0 (RETURN fmempty)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a polysa_assn\<close>
  by sepref

definition polymap_upd :: \<open>nat \<Rightarrow> 'v \<Rightarrow> (nat, 'v) fmap \<Rightarrow> (nat, 'v) fmap\<close> where
  \<open>polymap_upd k v m \<equiv> fmupd k (BOX v) m\<close>

text \<open>The precondition (index below \<open>INT64_MAX\<close>) must be checked on the C side.\<close>
sepref_def polymap_update is \<open>uncurry2 (RETURN ooo polymap_upd)\<close>
  :: \<open>[\<lambda>((k, _), _). k + 1 < max_snat 64]\<^sub>a
      si64_assn\<^sup>k *\<^sub>a polynomiala_assn\<^sup>d *\<^sub>a polysa_assn\<^sup>d \<rightarrow> polysa_assn\<close>
  unfolding polymap_upd_def
  by sepref

text \<open>The map itself is a by-value aggregate (array list), so it is boxed into a heap cell for
  the C side; @{term polymap_update_c} updates the cell in place.\<close>
type_synonym polymap_conc = \<open>64 word \<times> 64 word \<times> polya_conc ptr ptr\<close>

definition polymap_emp_c :: \<open>polymap_conc ptr llM\<close> where [llvm_code]:
  \<open>polymap_emp_c = doM { m \<leftarrow> polymap_emp; ll_ref m }\<close>

definition polymap_update_c :: \<open>64 word \<Rightarrow> polya_conc \<Rightarrow> polymap_conc ptr \<Rightarrow> unit llM\<close>
  where [llvm_code]:
  \<open>polymap_update_c i p mp = doM { m \<leftarrow> ll_load mp; m' \<leftarrow> polymap_update i p m; ll_store m' mp }\<close>

section \<open>Proof steps\<close>
text \<open>A proof is a @{term \<open>cl_assn' lpac_stepa_assn\<close>}. A step is a by-value tuple
  (\<^typ>\<open>lpac_stepa_conc\<close>), which cannot cross the C boundary, so the constructors of
  \<open>LPAC_Step_Assn_Array\<close> are fused with the append: C code never holds a single step.\<close>

subsection \<open>Sources of linear combinations\<close>

definition srcs_builder_new :: \<open>(polya_conc \<times> 64 word) clt_list ptr llM\<close> where [llvm_code]:
  \<open>srcs_builder_new = clt_builder_new\<close>

definition srcs_append
  :: \<open>(polya_conc \<times> 64 word) clt_list ptr \<Rightarrow> polya_conc \<Rightarrow> 64 word \<Rightarrow> unit llM\<close> where [llvm_code]:
  \<open>srcs_append bp p i = clt_builder_append bp (p, i)\<close>

definition srcs_finish :: \<open>(polya_conc \<times> 64 word) clt_list ptr \<Rightarrow> srcsa_conc llM\<close> where [llvm_code]:
  \<open>srcs_finish = clt_builder_finish\<close>

subsection \<open>Step lists\<close>

definition steps_builder_new :: \<open>lpac_stepa_conc clt_list ptr llM\<close> where [llvm_code]:
  \<open>steps_builder_new = clt_builder_new\<close>

definition steps_append_cl
  :: \<open>lpac_stepa_conc clt_list ptr \<Rightarrow> srcsa_conc \<Rightarrow> 64 word \<Rightarrow> polya_conc \<Rightarrow> unit llM\<close>
  where [llvm_code]:
  \<open>steps_append_cl bp srcs i r = doM { s \<leftarrow> mk_cla_impl srcs i r; clt_builder_append bp s }\<close>

definition steps_append_ext
  :: \<open>lpac_stepa_conc clt_list ptr \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 8 word ptr \<Rightarrow> polya_conc \<Rightarrow> unit llM\<close>
  where [llvm_code]:
  \<open>steps_append_ext bp i n p r = doM { s \<leftarrow> mk_lexta_impl i (n, p) r; clt_builder_append bp s }\<close>

definition steps_append_del :: \<open>lpac_stepa_conc clt_list ptr \<Rightarrow> 64 word \<Rightarrow> unit llM\<close>
  where [llvm_code]:
  \<open>steps_append_del bp i = doM { s \<leftarrow> mk_ldela_impl i; clt_builder_append bp s }\<close>

definition steps_finish :: \<open>lpac_stepa_conc clt_list ptr \<Rightarrow> lpac_stepa_conc cl_list llM\<close>
  where [llvm_code]:
  \<open>steps_finish = clt_builder_finish\<close>

section \<open>Checker entry point\<close>
text \<open>@{term full_checker_l_s2_impl} keeps the target and the input map and consumes the
  proof. The entry point consumes all three: it unboxes the map, runs the checker, stores the
  status message (only meaningful for the tag \<open>2\<close>, \<open>CFAILED\<close>) through the given pointer, frees
  the target and the inputs and returns the status tag (\<open>0\<close> = \<open>CSUCCESS\<close>, \<open>1\<close> = \<open>CFOUND\<close>). The
  shared variables and the final polynomials returned by the checker are not freed, as the
  driver terminates afterwards.\<close>

definition run_checker
  :: \<open>polymap_conc ptr \<Rightarrow> lpac_stepa_conc cl_list \<Rightarrow> polya_conc \<Rightarrow> stra_conc ptr \<Rightarrow> 8 word llM\<close>
  where [llvm_code]:
  \<open>run_checker mp prf tgt msgp = doM {
    m \<leftarrow> ll_load mp;
    ll_free mp;
    res \<leftarrow> full_checker_l_s2_impl tgt m prf;
    case res of (stm, vsp) \<Rightarrow>
    case stm of (st, msg) \<Rightarrow> doM {
      ll_store msg msgp;
      polya.cl_free tgt;
      polysa.bx.pmap_free m;
      Mreturn st
    }
  }\<close>

section \<open>Export\<close>
text \<open>The \<open>rewrites\<close> name every structure type occurring in the exported signatures, so the
  hand-written header \<^file>\<open>code/pasteque.h\<close> can use the same names as the LLVM file.\<close>
export_llvm (no_header)
  str_sval_c is str_sval
  polynomial_emp is polynomial_emp
  polynomial_builder_new is polynomial_builder_new
  polynomial_append is polynomial_append
  polynomial_finish is polynomial_finish
  polymap_emp_c is polymap_emp
  polymap_update_c is polymap_update
  srcs_builder_new is srcs_builder_new
  srcs_append is srcs_append
  srcs_finish is srcs_finish
  steps_builder_new is steps_builder_new
  steps_append_cl is steps_append_cl
  steps_append_ext is steps_append_ext
  steps_append_del is steps_append_del
  steps_finish is steps_finish
  run_checker is run_checker
  rewrites \<open>8 word node\<close> = charnode
           \<open>stra_conc\<close> = stra
           \<open>stra_conc node\<close> = strnode
           \<open>bi_conc\<close> = bi
           \<open>sbi_conc\<close> = sbi
           \<open>monomiala_conc\<close> = monomial
           \<open>monomiala_conc node\<close> = polynode
           \<open>monomiala_conc clt_list\<close> = polynomial_builder
           \<open>polya_conc \<times> 64 word\<close> = summand
           \<open>(polya_conc \<times> 64 word) node\<close> = srcsnode
           \<open>(polya_conc \<times> 64 word) clt_list\<close> = srcs_builder
           \<open>lpac_stepa_conc\<close> = step
           \<open>lpac_stepa_conc node\<close> = stepnode
           \<open>lpac_stepa_conc clt_list\<close> = steps_builder
           \<open>polymap_conc\<close> = polymap
  file "code/pasteque.ll"

end
