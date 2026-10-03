/* stats.c — instrumented driver for the PAC checker.
 *
 * Same program as main.c, but it additionally reports where the time inside the
 * verified checker goes. It links parser.c like main.c does, and defines its
 * own counting runtime hooks in place of lib_isabelle_llvm.c.
 *
 * Three kinds of numbers are produced:
 *
 *   1. Driver phases (lexing and parsing per input file, checking, teardown).
 *
 *   2. Checker phases. The verified code is a single call, so these come from
 *      the wrappers that inject_stats.py synthesizes into pasteque.ll; see
 *      stats.h for the phase table and the wrapper shape.
 *
 *   3. Allocator counters. The verified code reaches the allocator exclusively
 *      through isabelle_llvm_calloc/isabelle_llvm_free, which are defined here,
 *      so counting allocations and attributing their volume to the enclosing
 *      checker phase costs one array increment and no instrumentation at all.
 *
 */

/* clock_gettime()/CLOCK_MONOTONIC and getrusage() are POSIX, not ISO C. */
#define _POSIX_C_SOURCE 200809L

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/time.h>
#include <time.h>

#include "parser.h" /* lex_file, parse_*, run_checker, the runtime hooks */
#include "stats.h"  /* the phase table, the hook ABI */

// -- clock ----------------------------------------------------------------

static inline uint64_t pst_now_ns(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (uint64_t)ts.tv_sec * UINT64_C(1000000000) + (uint64_t)ts.tv_nsec;
}

static double pst_secs(uint64_t ns) { return (double)ns * 1e-9; }

// -- phase accounting ------------------------------------------------------

/* Deepest nesting of wrapped phases that is tracked. The phase table nests at
 * most a handful of levels; the limit only matters for a phase that recurses,
 * and exceeding it degrades the self-time attribution of the phases below the
 * limit rather than breaking the run. */
#define PST_STACK_MAX 256

static uint64_t pst_incl[PST_NPHASES];   /* phase and everything it calls */
static uint64_t pst_self[PST_NPHASES];   /* phase minus the nested phases */
static uint64_t pst_calls[PST_NPHASES];  /* activations, nested ones included */
static uint64_t pst_depth[PST_NPHASES];  /* current activations (re-entrancy) */
static uint64_t pst_start[PST_NPHASES];  /* timestamp of the outermost entry */
static uint64_t pst_abytes[PST_NPHASES]; /* bytes requested while innermost */
static uint64_t pst_acalls[PST_NPHASES]; /* allocations while innermost */

static int pst_stack[PST_STACK_MAX]; /* slots of the active phases */
static size_t pst_sp;                /* may exceed PST_STACK_MAX, see above */
static uint64_t pst_mark;            /* timestamp of the last transition */
static uint64_t pst_outside;         /* time with no phase active */
static int pst_started;              /* has any phase been entered yet? */
static uint64_t pst_unbalanced;      /* ignored hook calls, see pst_enter */

/* Slot the time is currently accruing to, or -1 outside any phase (and when
 * the stack overflowed, where the innermost tracked slot is unknown). */
static int pst_top(void) {
  if (pst_sp == 0 || pst_sp > PST_STACK_MAX)
    return -1;
  return pst_stack[pst_sp - 1];
}

/* Charge the time since the last transition to the phase currently on top and
 * start a new interval at `now`. Called on every enter and every exit, so each
 * boundary costs exactly one clock read. */
static void pst_charge(uint64_t now) {
  int top = pst_top();
  if (top >= 0)
    pst_self[top] += now - pst_mark;
  else if (pst_sp == 0)
    pst_outside += now - pst_mark;
  pst_mark = now;
}

void pst_enter(int64_t slot) {
  uint64_t now = pst_now_ns();

  /* The first entry starts the clock; before it there is no interval to
   * charge, and pst_outside must not absorb the whole parsing phase. */
  if (!pst_started) {
    pst_started = 1;
    pst_mark = now;
  } else {
    pst_charge(now);
  }

  if (slot >= 0 && slot < PST_NPHASES) {
    pst_calls[slot]++;
    if (pst_depth[slot]++ == 0)
      pst_start[slot] = now;
  } else {
    pst_unbalanced++;
  }

  if (pst_sp < PST_STACK_MAX)
    pst_stack[pst_sp] = (int)slot;
  pst_sp++;
}

void pst_exit(int64_t slot) {
  uint64_t now = pst_now_ns();

  /* An exit without a matching entry would pop a frame that is not ours and
   * corrupt every enclosing phase, so drop it instead. */
  if (pst_sp == 0) {
    pst_unbalanced++;
    return;
  }

  pst_charge(now); /* the interval just ended belongs to the exiting phase */
  pst_sp--;

  if (slot >= 0 && slot < PST_NPHASES && pst_depth[slot] > 0) {
    if (--pst_depth[slot] == 0)
      pst_incl[slot] += now - pst_start[slot];
  } else {
    pst_unbalanced++;
  }
}

const char *pst_phase_label(int64_t slot) {
  static const char *const labels[] = {
#define PST_LABEL(id, label, tier, regex) label,
      PST_PHASES(PST_LABEL)
#undef PST_LABEL
  };
  if (slot < 0 || slot >= PST_NPHASES)
    return "?";
  return labels[slot];
}

// -- runtime hooks of the Isabelle-LLVM-exported code ----------------------

static uint64_t pst_calloc_calls, pst_calloc_bytes, pst_free_calls;
#ifdef PST_TIME_ALLOC
static uint64_t pst_alloc_ns;
#endif

char *isabelle_llvm_calloc(size_t nmemb, size_t size) {
  int top = pst_top();
  pst_calloc_calls++;
  pst_calloc_bytes += nmemb * size;
  if (top >= 0) {
    pst_acalls[top]++;
    pst_abytes[top] += nmemb * size;
  }
#ifdef PST_TIME_ALLOC
  uint64_t t0 = pst_now_ns();
  char *p = calloc(nmemb, size);
  pst_alloc_ns += pst_now_ns() - t0;
  return p;
#else
  return calloc(nmemb, size);
#endif
}

void isabelle_llvm_free(char *ptr) {
  pst_free_calls++;
#ifdef PST_TIME_ALLOC
  uint64_t t0 = pst_now_ns();
  free(ptr);
  pst_alloc_ns += pst_now_ns() - t0;
#else
  free(ptr);
#endif
}

// -- reporting -------------------------------------------------------------

#define PST_MIB(bytes) ((double)(bytes) / (1024.0 * 1024.0))

void pst_report(double lex_parse_secs, double checker_secs,
                double teardown_secs, double total_secs) {
  struct rusage ru;
  int have_ru = getrusage(RUSAGE_SELF, &ru) == 0;

  /* Percentages are taken against the measured checker time rather than
   * against the total, so that they stay comparable across instances whose
   * parsing share differs. */
  double base = checker_secs > 0.0 ? checker_secs : 1.0;

  fprintf(stderr, "c\nc ***** checker phases *****\n");
  if (!pst_started) {
    fprintf(stderr, "c no phase was entered: pasteque.ll is not instrumented\n"
                    "c (build pasteque_stats against an injected .ll to get a "
                    "breakdown)\n");
  } else {
    /* The allocation columns count what the phase requested while it was the
       innermost active one, i.e. they are attributed like the self time. */
    fprintf(stderr, "c %-38s %9s %9s %7s %12s %12s %10s\n", "phase", "incl (s)",
            "self (s)", "self %", "calls", "allocs", "alloc MiB");
    for (int64_t s = 0; s < PST_NPHASES; s++) {
      if (pst_calls[s] == 0)
        continue; /* phase not wrapped at the injected tier */
      fprintf(stderr,
              "c %-38s %9.3f %9.3f %6.1f%% %12" PRIu64 " %12" PRIu64
              " %10.1f\n",
              pst_phase_label(s), pst_secs(pst_incl[s]), pst_secs(pst_self[s]),
              100.0 * pst_secs(pst_self[s]) / base, pst_calls[s], pst_acalls[s],
              PST_MIB(pst_abytes[s]));
    }
    /* Time inside run_checker that no wrapped phase accounts for. With CHECKER
     * wrapped this is the glue in run_checker itself and should be ~0; a large
     * value means a phase is missing from the table. */
    fprintf(stderr, "c %-38s %9s %9.3f %6.1f%%\n", "(unattributed)", "",
            pst_secs(pst_outside), 100.0 * pst_secs(pst_outside) / base);
    if (pst_sp != 0 || pst_unbalanced != 0)
      fprintf(stderr,
              "c WARNING: %" PRIu64 " unbalanced hook calls, %zu phases still "
              "open — the .ll injection is inconsistent with stats.h\n",
              pst_unbalanced, pst_sp);
  }

  fprintf(stderr, "c\nc ***** allocator *****\n");
  fprintf(stderr,
          "c isabelle_llvm_calloc: %" PRIu64 " calls, %.1f MiB requested\n",
          pst_calloc_calls, PST_MIB(pst_calloc_bytes));
  fprintf(stderr, "c isabelle_llvm_free:   %" PRIu64 " calls\n",
          pst_free_calls);
#ifdef PST_TIME_ALLOC
  fprintf(stderr, "c time in allocator: %.3f s = %.1f%% of the checker\n",
          pst_secs(pst_alloc_ns), 100.0 * pst_secs(pst_alloc_ns) / base);
#else
  fprintf(stderr, "c time in allocator: not measured (build with "
                  "-DPST_TIME_ALLOC)\n");
#endif

  fprintf(stderr, "c\nc ***** stats *****\n");
  fprintf(stderr, "c full init (lexing and parsing): %.3f s\n", lex_parse_secs);
  fprintf(stderr, "c time solving: %.3f s\n", checker_secs);
  /* Not folded into the checker time: nothing of the proof is checked here.
     The cost is the allocator consolidating the free list that the checker
     leaves behind, triggered by the first allocation afterwards. */
  fprintf(stderr, "c teardown (allocator): %.3f s\n", teardown_secs);
  fprintf(stderr, "c Overall: %.3f s", total_secs);
  if (have_ru)
    fprintf(stderr, " = %.3f s (usr) %.3f s (sys)",
            (double)ru.ru_utime.tv_sec + 1e-6 * (double)ru.ru_utime.tv_usec,
            (double)ru.ru_stime.tv_sec + 1e-6 * (double)ru.ru_stime.tv_usec);
  fprintf(stderr, "\n");
  if (have_ru)
    fprintf(stderr, "c peak RSS: %.1f MiB\n", (double)ru.ru_maxrss / 1024.0);
}

// -- driver ----------------------------------------------------------------

#define PST_SECS(a, b)                                                         \
  ((double)((b).tv_sec - (a).tv_sec) +                                         \
   1e-9 * (double)((b).tv_nsec - (a).tv_nsec))

/* Lex one file or exit. Unlike the driver in parser.c, this one handles the
 * three files one after the other so that each file's lexing and parsing can be
 * reported separately, as the SML checker does. */
static void pst_lex(const char *path, char **buf, token_array *ta) {
  if (lex_file(path, buf, ta) != 0)
    exit(2);
}

static void pst_release(char *buf, token_array *ta) {
  free((void *)ta->data);
  free(buf);
}

int main(int argc, char **argv) {
  if (argc != 4) {
    fprintf(stderr, "usage: %s <file.input> <file.proof> <file.target>\n",
            argv[0]);
    return 2;
  }

  struct timespec t0, t_in, t_prf, t_tgt, t_chk, t_end;
  char *buf = NULL;
  token_array ta = {0};

  clock_gettime(CLOCK_MONOTONIC, &t0);

  pst_lex(argv[1], &buf, &ta);
  polymap *ins = parse_inputs(&ta);
  pst_release(buf, &ta);
  clock_gettime(CLOCK_MONOTONIC, &t_in);

  pst_lex(argv[2], &buf, &ta);
  stepnode *prf = parse_proof(&ta);
  pst_release(buf, &ta);
  clock_gettime(CLOCK_MONOTONIC, &t_prf);

  pst_lex(argv[3], &buf, &ta);
  polynode *tgt = parse_target(&ta);
  pst_release(buf, &ta);
  clock_gettime(CLOCK_MONOTONIC, &t_tgt);

  int exit_code;
  /* The checker consumes all three structures. The returned byte is the status
   * tag of status_assn in PAC_Checker_Error.thy: 0 = SUCCESS (every step checks
   * but the target was not derived), 1 = FOUND (valid and derives the target),
   * 2 = FAILED (a step did not check). On FAILED an error message is stored
   * through the out-parameter: length-carrying, NOT NUL-terminated, allocated
   * through isabelle_llvm_calloc and owned by us afterwards. */
  stra msg = {0};
  char status = run_checker(ins, prf, tgt, &msg);
  clock_gettime(CLOCK_MONOTONIC, &t_chk);

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
    isabelle_llvm_free(msg.ptr);
  }
  exit_code = status == 1 ? 0 : 1;
  clock_gettime(CLOCK_MONOTONIC, &t_end);

  fprintf(stderr, "c\nc ***** input *****\n");
  fprintf(stderr, "c parsing polys file: %.3f s\n", PST_SECS(t0, t_in));
  fprintf(stderr, "c parsing pac file:   %.3f s\n", PST_SECS(t_in, t_prf));
  fprintf(stderr, "c parsing spec file:  %.3f s\n", PST_SECS(t_prf, t_tgt));

  pst_report(PST_SECS(t0, t_tgt), PST_SECS(t_tgt, t_chk),
             PST_SECS(t_chk, t_end), PST_SECS(t0, t_end));

  return exit_code;
}
