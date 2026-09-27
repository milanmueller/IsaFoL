# Makefile for the PAC checker C driver and parser test.
#
#   make pasteque         # the checker: trusted parser (parser.c) linked against
#                         # the verified, Isabelle-LLVM-exported run_checker.
#   make pasteque_shared  # same, but against the shared-variables checker
#                         # (run_shared_checker); parser.c is compiled with
#                         # -DPASTEQUE_SHARED and linked against pasteque_shared.ll.
#   make parser_test      # end-to-end smoke test of the verified importers:
#                         # parser.c (as a library) + parser_test.c + the LLVM
#                         # object assembled from pasteque_parser_test.ll.
#
# The two checker flavours each ship their own copy of the import functions, so
# they cannot be linked together — pick one at compile time via PASTEQUE_SHARED.
#
# pasteque.ll and pasteque_shared.ll are produced by the Isabelle session
# PAC_Checker2 (export_llvm in LPAC_CodeExport.thy); pasteque_parser_test.ll by
# PAC_Checker2_Parser_Test (Parser_Test.thy). Rebuild/refresh them with
# `isabelle build <session>` before rebuilding the corresponding C target.

# The checker targets must be built with clang: -mllvm is clang-only, and the
# exported .ll is fed to the same invocation as parser.c so that -O3/-flto
# optimise the verified code together with the trusted parser (as IsaSAT does).
# Assembling the .ll separately with `clang -c` would emit an -O0 native object
# that the later -O3 -flto link cannot optimise (measured ~1.9x slower).
CC           ?= clang
CLANG        ?= clang
CLANG_FORMAT ?= clang-format
# DFLAGS       ?= -march=native -mtune=native
DFLAGS       ?=
CFLAGS       ?= -std=c11 -O3 -flto -mllvm -inline-threshold=4000 -Wno-implicit-function-declaration

DRIVER  := pasteque
DRIVER_LL := pasteque.ll

SHARED_DRIVER := pasteque_shared
SHARED_DRIVER_LL := pasteque_shared.ll

TEST    := parser_test
TEST_LL := pasteque_parser_test.ll
TEST_LL_OBJ := $(TEST_LL:.ll=.o)

C_SRCS  := parser.c parser_test.c

.PHONY: all clean format format-check
all: $(DRIVER)

# Format all C sources in place (same .clang-format Helix uses on save).
format:
	$(CLANG_FORMAT) -i $(C_SRCS)

# CI-friendly check: fail if anything is not formatted.
format-check:
	$(CLANG_FORMAT) --dry-run --Werror $(C_SRCS)

# Isabelle/LLVM-exported IR for the smoke test: assemble with clang.
$(TEST_LL_OBJ): $(TEST_LL)
	$(CLANG) $(CFLAGS) -c -o $@ $<

# The checker: trusted parser.c (with its main) + the verified run_checker,
# compiled and LTO-linked in one invocation.
$(DRIVER): parser.c parser.h pasteque.h $(DRIVER_LL)
	$(CC) $(CFLAGS) $(DFLAGS) -o $@ parser.c $(DRIVER_LL)

# Same driver against the shared-variables checker: -DPASTEQUE_SHARED makes
# parser.c pull in pasteque_shared.h and call run_shared_checker.
$(SHARED_DRIVER): parser.c parser.h pasteque_shared.h $(SHARED_DRIVER_LL)
	$(CC) $(CFLAGS) -DPASTEQUE_SHARED $(DFLAGS) -o $@ parser.c $(SHARED_DRIVER_LL)

# Smoke test: test driver + parser-as-library (main dropped) + exported IR.
parser_test.o: parser_test.c parser.h pasteque.h
	$(CC) $(CFLAGS) -c -o $@ parser_test.c

# parser.c compiled as a library: PARSER_NO_MAIN drops its standalone main.
parser_lib.o: parser.c parser.h pasteque.h
	$(CC) $(CFLAGS) -DPARSER_NO_MAIN -c -o $@ parser.c

$(TEST): parser_test.o parser_lib.o $(TEST_LL_OBJ)
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $^

clean:
	$(RM) $(DRIVER) $(SHARED_DRIVER) \
	      $(TEST) parser_test.o parser_lib.o $(TEST_LL_OBJ)
