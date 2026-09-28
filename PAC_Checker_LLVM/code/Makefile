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

CC           ?= clang
CLANG_FORMAT ?= clang-format
# DFLAGS       ?= -march=native -mtune=native
DFLAGS       ?=
CFLAGS       ?= -std=c11 -O3 -flto -mllvm -inline-threshold=4000 -Wno-implicit-function-declaration

C_SRCS  := parser.c
HEADERS := parser.h pasteque.h term.h
# Isabelle-LLVM's support library defines the runtime hooks the exported code
# declares (isabelle_llvm_calloc/free/abort). stats.c brings its own counting
# hooks, so only the plain checker links it.
ISABELLE_LLVM ?= ../../../isabelle_llvm
LIB_ISABELLE_LLVM := $(ISABELLE_LLVM)/src/lib_isabelle_llvm.c
# stats.h is not in HEADERS: the internalization rule below derives the public
# API of the .ll from HEADERS, and the stats hooks are declared (not defined) in
# the .ll, so they must not be internalized -- but they are also not part of the
# exported API.
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

pasteque: $(C_SRCS) $(LIB_ISABELLE_LLVM) $(HEADERS) $(LL_INT)
	$(CC) $(CFLAGS) $(CPPFLAGS) $(DFLAGS) -o $@ $(C_SRCS) $(LIB_ISABELLE_LLVM) $(LL_INT)

# The instrumented driver (stats.c). parser.c is reused as a library, so its own
# main and its own runtime hooks are dropped with -DPARSER_NO_MAIN.
#
# STATS_LL_INT selects the .ll to measure. By default it is the injected one, so
# that the report contains the breakdown inside the verified code. Point it at
# $(LL_INT) to measure the code as exported: the driver then still reports the
# per-file parsing times and the allocator counters, and states that no checker
# phase was entered.
#
#   make pasteque_stats STATS_LL_INT="$(LL_INT)"     # no wrappers at all
#   make pasteque_stats STATS_TIER=2                 # also the per-operation phases
#
# STATS_TIER selects how deep to instrument; see the phase table in stats.h.
# Tier 2 wraps functions called once per polynomial operation, which perturbs
# the measurement noticeably — compare the total against ./pasteque.
STATS_TIER   ?= 1
STATS_LL_INT ?= pasteque_stats_int.ll term_int.ll

# The injected .ll. inject_stats.py renames each phase's definition and
# synthesizes a wrapper under the original name, so no call site changes; the
# %_int.ll rule above then internalizes the renamed bodies along with the rest.
pasteque_stats.ll: pasteque.ll stats.h inject_stats.py
	./inject_stats.py $< -o $@ --tier $(STATS_TIER)

pasteque_stats: $(C_SRCS) stats.c $(HEADERS) stats.h $(STATS_LL_INT)
	$(CC) $(CFLAGS) $(CPPFLAGS) $(DFLAGS) -DPARSER_NO_MAIN -o $@ \
	    $(C_SRCS) stats.c $(STATS_LL_INT)

clean:
	$(RM) pasteque pasteque_stats $(LL_INT) pasteque_stats.ll pasteque_stats_int.ll
