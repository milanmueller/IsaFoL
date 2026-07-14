# Makefile for the PAC checker C driver (pasteque).
#
# For now this builds only the trusted C tokenizer/driver (pasteque.c).
# Once pasteque.c starts calling the verified builders exported from Isabelle,
# link in the LLVM object as well: `make LINK_LLVM=1`. That path compiles
# pasteque.ll with clang and expects runtime stubs for isabelle_llvm_calloc /
# isabelle_llvm_free (thin wrappers over calloc/free) — not written yet.

CC           ?= cc
CLANG        ?= clang
CLANG_FORMAT ?= clang-format
CFLAGS       ?= -Wall -Wextra -std=c11 -O2
LDFLAGS      ?=

TARGET  := pasteque
C_SRCS  := pasteque.c
C_OBJS  := $(C_SRCS:.c=.o)

# Optional: link the Isabelle-exported LLVM checker (see header above).
LINK_LLVM ?=
ifdef LINK_LLVM
LL_SRCS := pasteque.ll
LL_OBJS := $(LL_SRCS:.ll=.o)
endif

OBJS := $(C_OBJS) $(LL_OBJS)

.PHONY: all clean format format-check

all: $(TARGET)

# Format all C sources in place (same .clang-format Helix uses on save).
format:
	$(CLANG_FORMAT) -i $(C_SRCS)

# CI-friendly check: fail if anything is not formatted.
format-check:
	$(CLANG_FORMAT) --dry-run --Werror $(C_SRCS)

$(TARGET): $(OBJS)
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $(OBJS)

# C sources.
%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

# Isabelle/LLVM-exported IR: assemble with clang.
%.o: %.ll
	$(CLANG) $(CFLAGS) -c -o $@ $<

clean:
	$(RM) $(TARGET) $(C_OBJS) $(LL_OBJS)
