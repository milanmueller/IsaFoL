# Makefile for the PAC checker C driver.
#
#   make pasteque   # the checker: trusted parser (parser.c) linked against the verified
#                   # builders and checker exported by LPAC_Codegen.thy (term.ll,
#                   # pasteque.ll). Refresh the .ll files with `isabelle build` first.
#
# Symbol hiding. Isabelle-LLVM names the auxiliary functions of every export_llvm
# from scratch (IICF_Copying_List_clt_snoc, clt_snoc1, LLVM_Codegen_clt_builder_finish,
# ...), so term.ll and pasteque.ll define the same names at different types and cannot
# be linked as they are. %_int.ll marks every definition that is not declared in one of
# the headers as `internal`; only the API named in term.h/pasteque.h/parser.h stays
# external.
#
# Checker entry point. pasteque.ll does not export run_checker yet; until it does,
# parser.c is compiled with -DPASTEQUE_NO_CHECKER (parse-only driver). The flag is
# derived from pasteque.ll, so the build switches over by itself once the export exists.

# The checker must be built with clang: -mllvm is clang-only, and the exported .ll is
# fed to the same invocation as parser.c so that -O3/-flto optimise the verified code
# together with the trusted parser (as IsaSAT does). Assembling the .ll separately with
# `clang -c` would emit an -O0 native object that the later -O3 -flto link cannot
# optimise (measured ~1.9x slower).
CC           ?= clang
CLANG_FORMAT ?= clang-format
# DFLAGS       ?= -march=native -mtune=native
DFLAGS       ?=
CFLAGS       ?= -std=c11 -O3 -flto -mllvm -inline-threshold=4000 -Wno-implicit-function-declaration

C_SRCS  := parser.c
HEADERS := parser.h pasteque.h term.h
LL      := pasteque.ll term.ll
LL_INT  := $(LL:.ll=_int.ll)

ifeq ($(shell grep -c '^define .*@run_checker\b' pasteque.ll),0)
CPPFLAGS += -DPASTEQUE_NO_CHECKER
endif

.PHONY: all clean format format-check
all: pasteque

format:
	$(CLANG_FORMAT) -i $(C_SRCS)

format-check:
	$(CLANG_FORMAT) --dry-run --Werror $(C_SRCS)

# Hide all definitions not declared in a header (see above). The extended regex lists
# the declared names as alternatives; `define <type> @name(` lines matching none of
# them get `internal` linkage.
%_int.ll: %.ll $(HEADERS)
	api=$$(grep -ohE '\b[A-Za-z_0-9]+\(' $(HEADERS) | tr -d '(' | sort -u | paste -sd'|'); \
	sed -E "/^define /{/@($$api)\(/!s/^define /define internal /}" $< > $@

pasteque: $(C_SRCS) $(HEADERS) $(LL_INT)
	$(CC) $(CFLAGS) $(CPPFLAGS) $(DFLAGS) -o $@ $(C_SRCS) $(LL_INT)

clean:
	$(RM) pasteque $(LL_INT)
