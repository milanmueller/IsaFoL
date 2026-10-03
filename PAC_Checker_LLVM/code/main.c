/* main.c — standalone driver for the PAC checker.
 *
 * Lexes and parses the three input files with the trusted parser (parser.c),
 * hands the built structures to the verified checker (run_checker, exported by
 * LPAC_Codegen.thy into pasteque.ll) and reports its verdict. The runtime hooks
 * of the exported code (isabelle_llvm_calloc/free) come from
 * lib_isabelle_llvm.c. stats.c is the instrumented counterpart of this file.
 */

/* clock_gettime()/CLOCK_MONOTONIC are POSIX, not ISO C — request them. */
#define _POSIX_C_SOURCE 200809L

#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#include "parser.h"

int main(int argc, char **argv) {
  if (argc != 4) {
    fprintf(stderr, "usage: %s <file.input> <file.proof> <file.target>\n",
            argv[0]);
    return 2;
  }

  /* Lex the three files. The text buffers only need to live until parsing is
   * done: the parser copies every string it hands to the verified code. */
  char *ibuf = NULL, *pbuf = NULL, *tbuf = NULL;
  token_array ita = {0}, pta = {0}, tta = {0};
  struct timespec t0, t1, t2, t3, t4;
  clock_gettime(CLOCK_MONOTONIC, &t0);
  if (lex_file(argv[1], &ibuf, &ita) != 0)
    return 2;
  if (lex_file(argv[2], &pbuf, &pta) != 0)
    return 2;
  if (lex_file(argv[3], &tbuf, &tta) != 0)
    return 2;
  clock_gettime(CLOCK_MONOTONIC, &t1);

  /* Parse directly into the checker's data structures. */
  polymap *ins = parse_inputs(&ita);
  stepnode *prf = parse_proof(&pta);
  polynode *tgt = parse_target(&tta);
  clock_gettime(CLOCK_MONOTONIC, &t2);

  free((void *)ita.data);
  free(ibuf);
  free((void *)pta.data);
  free(pbuf);
  free((void *)tta.data);
  free(tbuf);

  int exit_code;
  /* Hand the parsed structures to the verified checker (which consumes them).
   * The returned byte is the checker's status tag (see status_assn in
   * PAC_Checker_Error.thy):
   *   0 = SUCCESS  proof steps all check, but the target was not derived
   *   1 = FOUND    proof valid *and* it derives the target polynomial
   *   2 = FAILED   some proof step did not check
   * On FAILED the checker also stores an error message through the out-param:
   * a length-carrying (NOT NUL-terminated) string it allocated through
   * isabelle_llvm_calloc, owned by us afterwards. On SUCCESS/FOUND it is left
   * as {0, NULL}. */
  stra msg = {0};
  char status = run_checker(ins, prf, tgt, &msg);
  clock_gettime(CLOCK_MONOTONIC, &t3);

  const char *status_msg;
  switch (status) {
  case 0:
    status_msg = "SUCCESS (all steps check, but the target was not derived)";
    break;
  case 1:
    status_msg = "FOUND (proof valid and derives the target)";
    break;
  case 2:
    status_msg = "FAILED (a proof step did not check)";
    break;
  default:
    status_msg = "unknown status";
    break;
  }
  printf("%d\n", (int)status);
  fprintf(stderr, "run_checker: %s\n", status_msg);
  if (status == 2 && msg.ptr != NULL) { /* msg is only defined for FAILED */
    fprintf(stderr, "run_checker: %.*s\n", (int)msg.len, msg.ptr);
    isabelle_llvm_free(msg.ptr); // the checker allocated it, we own it
  }
  /* Exit 0 iff the proof is a valid derivation of the target (FOUND). */
  exit_code = status == 1 ? 0 : 1;
  clock_gettime(CLOCK_MONOTONIC, &t4);

  /* Phase timings (wall clock), in the style of the SML driver's stats block.
   */
#define SECS(a, b)                                                             \
  ((double)((b).tv_sec - (a).tv_sec) +                                         \
   1e-9 * (double)((b).tv_nsec - (a).tv_nsec))
  fprintf(stderr, "c ***** stats *****\n");
  fprintf(stderr, "c lexing: %.3f s\n", SECS(t0, t1));
  fprintf(stderr, "c parsing (incl. building): %.3f s\n", SECS(t1, t2));
  fprintf(stderr, "c checker: %.3f s\n", SECS(t2, t3));
  fprintf(stderr, "c teardown: %.3f s\n", SECS(t3, t4));
  fprintf(stderr, "c overall: %.3f s\n", SECS(t0, t4));
#undef SECS

  return exit_code;
}
