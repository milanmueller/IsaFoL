theory LPAC_Checker_LLVM
  imports LPAC_Checker_Synthesis
begin

text \<open>Here we generate LLVM code from our refined functions.
  Also we define the c-facing interface.\<close>

export_llvm 
  PAC_checker_l_impl 
  defines \<open>
    
  \<close>
  file \<open>./code/pasteque.ll\<close>

end