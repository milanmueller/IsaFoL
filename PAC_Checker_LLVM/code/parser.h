/* parser.h — public interface of the trusted C tokenizer/parser (parser.c).
 *
 * The parser does not build any data structure of its own: it drives the
 * verified builder functions exported from LLVM_Codegen.thy (pasteque.h and
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
 * functions, which the driver (main in parser.c, or stats.c) must provide. The
 * parser allocates every string it hands to a builder through
 * isabelle_llvm_calloc, because the checker frees them with
 * isabelle_llvm_free. */
void *isabelle_llvm_calloc(uint64_t nmemb, uint64_t size);
void isabelle_llvm_free(void *ptr);

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
 * Expected to be exported by LLVM_Codegen.thy (into pasteque.ll) over the
 * builder representation, once the checker entry point is added there. The
 * returned byte is the checker's status tag (see status_assn in
 * PAC_Checker_Error.thy): 0 = SUCCESS, 1 = FOUND, 2 = FAILED. On FAILED an
 * error message (length-carrying, not NUL-terminated, allocated through
 * isabelle_llvm_calloc) is stored through msg. All three objects are consumed.
 * Until the export exists, build with -DPASTEQUE_NO_CHECKER to get a driver
 * that only lexes and parses. */
#ifndef PASTEQUE_NO_CHECKER
char run_checker(polymap *inputs, stepnode *proof, polynode *target, stra *msg);
#endif

#endif /* PARSER_H */
