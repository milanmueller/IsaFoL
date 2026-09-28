/* parser.h — public interface of the trusted C tokenizer/parser (parser.c).
 *
 * The parser does not build any data structure of its own: it drives the
 * verified builder functions exported from LPAC_Codegen.thy (pasteque.h and
 * term.h) directly, so the objects it returns (polymap, stepnode, polynode) are
 * exactly the checker's own heap representation.
 */
#ifndef PARSER_H
#define PARSER_H

#include <stddef.h>
#include <stdint.h>

#include "pasteque.h" /* builders for polynomials, polynomial maps, proof
                          steps; includes term.h (stra, strnode, charnode) */

/* -- Runtime hooks of the Isabelle-LLVM-exported code ----------------------
 * The verified code allocates and frees its heap cells through these two
 * functions. The checker links the support library shipped with Isabelle-LLVM
 * (lib_isabelle_llvm.c, a copy of isabelle_llvm/src/); stats.c provides its
 * own counting versions instead. The prototypes mirror that library. The
 * parser allocates every string it hands to a builder through
 * isabelle_llvm_calloc, because the checker frees them with
 * isabelle_llvm_free. */
char *isabelle_llvm_calloc(size_t n, size_t m);
void isabelle_llvm_free(char *p);

/* -- Tokens: opaque to callers, produced by lex_file, consumed by parse_* -- */
typedef struct token token;
typedef struct {
  const token *data;
  size_t len;
} token_array;

/* Read a file and tokenize it. On success the caller owns both *buf_out (the
 * text the token slices point into) and ta_out->data. Returns 0 on success. */
int lex_file(const char *path, char **buf_out, token_array *ta_out);

/* Parsers. Each builds its result through the verified builders and returns
 * the finished object, which is then owned by the caller (i.e. must be handed
 * to the checker; there are no C-side destructors). Syntax errors are fatal:
 * they are reported on stderr and the process exits with status 1. */
polymap *parse_inputs(const token_array *ta);  /* input  ::= (id poly ';')* */
stepnode *parse_proof(const token_array *ta);  /* proof  ::= (rule)* */
polynode *parse_target(const token_array *ta); /* target ::= poly ';' */

/* -- Checker entry point -----------------------------------------------------
 * run_checker is exported by LPAC_Codegen.thy (into pasteque.ll) and declared
 * in the generated pasteque.h. The returned byte is the checker's status tag
 * (see status_assn in PAC_Checker_Error.thy): 0 = SUCCESS, 1 = FOUND,
 * 2 = FAILED. On FAILED an error message (length-carrying, not NUL-terminated,
 * allocated through isabelle_llvm_calloc) is stored through msg. All three
 * objects are consumed. */

#endif /* PARSER_H */
