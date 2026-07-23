# Makefile for the PAC checker C driver and parser test.
#
#   make parser        # standalone trusted parser/dumper (parser.c, with main)
#   make parser_test   # end-to-end smoke test of the verified importers:
#                      # parser.c (as a library) + parser_test.c + the LLVM
#                      # object assembled from pasteque_parser_test.ll.
#
# pasteque_parser_test.ll is produced by the Isabelle session
# PAC_Checker2_Parser_Test (export_llvm in Parser_Test.thy). Build/refresh it
# with `isabelle build PAC_Checker2_Parser_Test` before `make parser_test`.

CC           ?= cc
CLANG        ?= clang
CLANG_FORMAT ?= clang-format
CFLAGS       ?= -Wall -Wextra -std=c11 -O2
LDFLAGS      ?=

DRIVER  := parser
TEST    := parser_test
TEST_LL := pasteque_parser_test.ll
TEST_LL_OBJ := $(TEST_LL:.ll=.o)

C_SRCS  := parser.c parser_test.c

.PHONY: all clean format format-check

# Default build stays self-contained (no generated .ll needed).
all: $(DRIVER)

# Format all C sources in place (same .clang-format Helix uses on save).
format:
	$(CLANG_FORMAT) -i $(C_SRCS)

# CI-friendly check: fail if anything is not formatted.
format-check:
	$(CLANG_FORMAT) --dry-run --Werror $(C_SRCS)

# Standalone parser/dumper — parser.c carries its own main.
$(DRIVER): parser.c parser.h pasteque.h
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ parser.c

# Smoke test: test driver + parser-as-library (main dropped) + exported IR.
parser_test.o: parser_test.c parser.h pasteque.h
	$(CC) $(CFLAGS) -c -o $@ parser_test.c

# parser.c compiled as a library: PARSER_NO_MAIN drops its standalone main.
parser_lib.o: parser.c parser.h pasteque.h
	$(CC) $(CFLAGS) -DPARSER_NO_MAIN -c -o $@ parser.c

# Isabelle/LLVM-exported IR: assemble with clang.
$(TEST_LL_OBJ): $(TEST_LL)
	$(CLANG) -c -o $@ $<

$(TEST): parser_test.o parser_lib.o $(TEST_LL_OBJ)
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $^

clean:
	$(RM) $(DRIVER) $(TEST) parser_test.o parser_lib.o $(TEST_LL_OBJ)
