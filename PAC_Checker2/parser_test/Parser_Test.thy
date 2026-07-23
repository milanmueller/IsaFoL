theory Parser_Test
  imports PAC_Checker2_LLVM.LPAC_CodeExport
begin

text \<open>Smoke test for the C-parser importers. We run \<open>imp_inputs\<close>, \<open>imp_proof\<close> and
  \<open>imp_target\<close> on the parser-produced C structs and hand the resulting
  Isabelle-internal linked-list representations back to C through three
  out-pointers, so a C harness can observe them (non-null, walkable, freeable).

  All parameters are pointers and the return is a primitive (\<^typ>\<open>8 word\<close>), so the
  signature is C-ABI compatible. We deliberately omit an explicit prototype and
  \<open>defines\<close> block: the code generator then auto-emits the struct typedefs for the
  internal representations (\<open>node\<close>/\<open>os_list\<close>/\<open>pac_step_impl\<close>/\<open>sbin\<close>).\<close>

definition test_parsing ::
  \<open>c_inputs ptr \<Rightarrow> c_proof ptr \<Rightarrow> c_target ptr
   \<Rightarrow> (64 word \<times> poly_conc) os_list ptr   \<comment> \<open>out: parsed inputs\<close>
   \<Rightarrow> step_conc os_list ptr               \<comment> \<open>out: parsed proof\<close>
   \<Rightarrow> poly_conc ptr                       \<comment> \<open>out: parsed target\<close>
   \<Rightarrow> 8 word llM\<close>
  where [llvm_code]:
  \<open>test_parsing cinps_p cprf_p ctgt_p oinps oprf otgt \<equiv> doM {
     cinps \<leftarrow> ll_load cinps_p;
     cprf  \<leftarrow> ll_load cprf_p;
     ctgt  \<leftarrow> ll_load ctgt_p;
     isainps \<leftarrow> imp_inputs cinps;
     isaprf  \<leftarrow> imp_proof cprf;
     isatgt  \<leftarrow> imp_target ctgt;
     ll_store isainps oinps;
     ll_store isaprf  oprf;
     ll_store isatgt  otgt;
     Mreturn 0
   }\<close>

export_llvm
  test_parsing
  defines \<open>
    typedef struct {uint64_t len; char *ptr;} slice;
    typedef struct {uint64_t num_vars; slice *vars_ptr;} term;
    typedef struct {slice coeff; struct {char neg; term vars;};} monomial;
    typedef struct {uint64_t num_mnmls; monomial *mnmls_ptr;} polynomial;
    typedef struct {uint64_t idx; polynomial poly;} input;
    typedef struct {uint64_t num_inputs; input *inputs;} inputs;
    typedef struct {polynomial *poly_ptr; uint64_t idx;} summand;
    typedef struct {uint64_t num_summands; summand *summands_ptr;} summands;
    typedef struct {uint64_t target_idx; struct {summands summands; polynomial res;};} lc_rule;
    typedef struct {uint64_t idx; struct {slice var; polynomial poly;};} ext_rule;
    typedef struct {int32_t typ; union {lc_rule lc; uint64_t del; ext_rule ext;} u;} rule;
    typedef struct {uint64_t num_rules; rule *rules_ptr;} proof;
  \<close>
  file "../code/pasteque_parser_test.ll"

end
