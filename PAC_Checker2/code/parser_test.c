/* parser_test.c — smoke test for the verified C-parser importers.
 *
 * Reads an input/proof/target triple, parses them with the trusted C parser
 * (parser.c) into the Isabelle-facing ABI structs, then hands them to the
 * verified importers via the exported LLVM function `test_parsing`
 * (Parser_Test.thy). The importers turn the flat parser structs into the
 * Isabelle-internal singly-linked-list representations; we walk those lists
 * back out through three out-pointers and print them, confirming the parse +
 * import round-trip end-to-end.
 *
 * Build: link against pasteque_parser_test.o (assembled from the exported
 * pasteque_parser_test.ll) — see the Makefile `parser_test` target.
 */
#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "parser.h" /* trusted parser + the Isabelle-facing ABI structs */

/* -- Isabelle-internal representations returned by the importers -------------
 *
 * These mirror the LLVM aggregate types in pasteque_parser_test.ll. Every list
 * is a `Node { val; next }` singly-linked list (os_list = node*). Because every
 * field is 8-byte aligned (i8 tags pad to 8), the flat C structs below are
 * byte-compatible with the right-nested LLVM tuples. */

/* 8 word os_list — a string (bytes in original order). */
typedef struct str_node {
  uint8_t c;
  struct str_node *next;
} str_node;

/* monom_conc = strl_conc os_list — a monomial's variable list (list of strings). */
typedef struct mon_node {
  str_node *var;
  struct mon_node *next;
} mon_node;

/* sbin_conc = 64 word x 64 word x 64 word ptr — signed-big-int magnitude. */
typedef struct {
  uint64_t f0;
  uint64_t f1;
  uint64_t *f2;
} sbin;

/* sbi_conc = sbin_conc x 1 word — a coefficient (magnitude + sign flag). */
typedef struct {
  sbin num;
  uint8_t sign;
} sbi;

/* mnml_conc = monom_conc x sbi_conc — a monomial (term x coefficient). */
typedef struct {
  mon_node *term;
  sbi coeff;
} mnml;

/* poly_conc = mnml_conc os_list — a polynomial. */
typedef struct poly_node {
  mnml val;
  struct poly_node *next;
} poly_node;

/* (64 word x poly_conc) os_list — parsed inputs, an (idx, poly) list. */
typedef struct inp_node {
  uint64_t idx;
  poly_node *poly;
  struct inp_node *next;
} inp_node;

/* (poly_conc x 64 word) os_list — a lin-com step's summand sources. */
typedef struct src_node {
  poly_node *poly;
  uint64_t idx;
  struct src_node *next;
} src_node;

/* step_conc = pac_step_impl — a proof step (tag, new_id, res, srcs, var).
 * tag: 0 = CL (lin-com), 1 = EXT (extension), 2 = DEL (deletion). */
typedef struct step_node {
  uint8_t tag;
  uint64_t new_id;
  poly_node *res;
  src_node *srcs;
  str_node *var;
  struct step_node *next;
} step_node;

/* The exported importer. No `is` annotation on the Isabelle side, so the symbol
 * carries the theory prefix. Inputs are the flat parser structs; results come
 * back through three out-pointers. */
extern char Parser_Test_test_parsing(inputs *cinps, proof *cprf,
                                     polynomial *ctgt, inp_node **oinps,
                                     step_node **oprf, poly_node **otgt);

/* -- Runtime stubs expected by the Isabelle-LLVM code ------------------------ */
void *isabelle_llvm_calloc(uint64_t nmemb, uint64_t size) {
  return calloc(nmemb, size);
}
void isabelle_llvm_free(void *ptr) {
  free(ptr);
}

/* -- Printing the imported linked lists -------------------------------------- */
static void print_string(const str_node *s) {
  for (; s != NULL; s = s->next)
    putchar((char)s->c);
}

/* A term is the product of its variables; an empty term is a bare constant. */
static void print_term(const mon_node *t) {
  for (const mon_node *v = t; v != NULL; v = v->next) {
    if (v != t)
      putchar('*');
    print_string(v->var);
  }
}

/* Print a polynomial as the sum of its monomials' variable terms.
 *
 * Only the terms are meaningful right now: coefficients (magnitude *and* sign)
 * come from `slice_to_big_int`, which currently routes through the placeholder
 * `str_to_int \<equiv> \<lambda>_. RETURN 0` on the Isabelle side — so every coefficient is a
 * stubbed 0 and carries no sign. We therefore join monomials with a neutral
 * " + " and print the coefficient as "c" (a bare constant monomial as <const>). */
static void print_polynomial(const poly_node *p) {
  if (p == NULL) {
    printf("<empty>");
    return;
  }
  for (const poly_node *m = p; m != NULL; m = m->next) {
    if (m != p)
      printf(" + ");
    if (m->val.term != NULL) {
      printf("c*"); /* placeholder coefficient */
      print_term(m->val.term);
    } else {
      printf("<const>");
    }
  }
}

static size_t list_len_src(const src_node *s) {
  size_t n = 0;
  for (; s != NULL; s = s->next)
    n++;
  return n;
}

int main(int argc, char **argv) {
  if (argc != 4) {
    fprintf(stderr, "usage: %s <file.input> <file.proof> <file.target>\n",
            argv[0]);
    return 1;
  }

  /* Lex + parse the three files into the flat ABI structs. */
  char *ibuf = NULL, *pbuf = NULL, *tbuf = NULL;
  token_array ita = {0}, pta = {0}, tta = {0};
  if (lex_file(argv[1], &ibuf, &ita) != 0)
    return 1;
  if (lex_file(argv[2], &pbuf, &pta) != 0)
    return 1;
  if (lex_file(argv[3], &tbuf, &tta) != 0)
    return 1;

  arena a = {0};
  inputs ins = parse_inputs(&a, &ita);
  proof prf = parse_proof(&a, &pta);
  target tgt = parse_target(&a, &tta);

  /* Hand them to the verified importers. */
  inp_node *out_inps = NULL;
  step_node *out_prf = NULL;
  poly_node *out_tgt = NULL;
  char status = Parser_Test_test_parsing(&ins, &prf, &tgt.poly, &out_inps,
                                         &out_prf, &out_tgt);
  printf("test_parsing returned %d\n", (int)status);
  printf(
      "(note: coefficients are placeholder 0s until str_to_int is "
      "implemented; only variable terms are meaningful, shown as c*<vars>)\n");

  /* Walk the imported lists back out. */
  printf("\n== target ==\n  ");
  print_polynomial(out_tgt);
  putchar('\n');

  printf("\n== inputs ==\n");
  for (inp_node *in = out_inps; in != NULL; in = in->next) {
    printf("  [%" PRIu64 "] ", in->idx);
    print_polynomial(in->poly);
    putchar('\n');
  }

  printf("\n== proof ==\n");
  for (step_node *s = out_prf; s != NULL; s = s->next) {
    switch (s->tag) {
    case 0:
      printf("  CL  id=%" PRIu64 " (%zu sources) res=", s->new_id,
             list_len_src(s->srcs));
      print_polynomial(s->res);
      putchar('\n');
      break;
    case 1:
      printf("  EXT id=%" PRIu64 " var=", s->new_id);
      print_string(s->var);
      printf(" res=");
      print_polynomial(s->res);
      putchar('\n');
      break;
    case 2:
      printf("  DEL id=%" PRIu64 "\n", s->new_id);
      break;
    default:
      printf("  ??? tag=%u\n", (unsigned)s->tag);
      break;
    }
  }

  /* Smoke test: the imported lists (isabelle_llvm_calloc'd) and the parser arena
   * are intentionally left for process exit to reclaim. Free the lexer buffers. */
  arena_free(&a);
  free((void *)ita.data);
  free(ibuf);
  free((void *)pta.data);
  free(pbuf);
  free((void *)tta.data);
  free(tbuf);
  return 0;
}
