/* stats.h — phase table and hook ABI of the instrumented checker driver.
 * Author: Milan Müller - ALU Freiburg
 *
 * The verified code exported by LPAC_Codegen.thy is one opaque call
 * (run_checker), so the driver timers in parser.c can only report the checker
 * as a whole. To break it down, inject_stats.py rewrites pasteque.ll: for every
 * phase named below it renames the definition
 *
 *     define <ty> @F(<args>)          ->  define <ty> @F__inner(<args>)
 *
 * and synthesizes a wrapper that carries the original name and signature
 *
 *     define <ty> @F(<args>) {
 *       call void @pst_enter(i64 <slot>)
 *       %r = call <ty> @F__inner(<args>)
 *       call void @pst_exit(i64 <slot>)
 *       ret <ty> %r
 *     }
 *
 * Every caller therefore reaches the wrapper without any call site being
 * touched, and the signature is copied verbatim from the `define` line, so the
 * aggregate return types of the exported code need no C-side declaration.
 *
 * THE PHASE TABLE BELOW IS THE SINGLE SOURCE OF TRUTH: stats.c derives the slot
 * numbers and the report labels from it, and inject_stats.py reads the same
 * macro to learn which functions to wrap and with which slot number.
 */
#ifndef STATS_H
#define STATS_H

#include <stdint.h>

/* -- Phase table -----------------------------------------------------------
 * PST_PHASES(X) expands X(id, label, tier, regex) once per phase, in report
 * order. Fields:
 *
 *   id     C identifier; becomes the enum constant PST_<id> and thus the slot
 *          number passed to pst_enter/pst_exit. Slot numbers are positional,
 *          so INSERTING A PHASE RENUMBERS THE FOLLOWING ONES — the .ll must be
 *          re-injected after any edit here (the Makefile rule depends on
 *          stats.h, so this happens by itself).
 *   label  what the report prints.
 *   tier   how often the function runs; inject_stats.py wraps everything up to
 *          the tier given with --tier (default 1):
 *            0  O(1) per run           — free
 *            1  O(#proof steps)        — ~25 ns per call, noise on any
 *                                        instance worth measuring
 *            2  O(#polynomial ops)     — millions of calls; measurable
 *                                        perturbation, and wrapping makes the
 *                                        function an LTO optimization barrier
 *          Nothing hotter than tier 2 should ever be listed here: the leaf
 *          operations (mult_monoms, the add_poly fold bodies, the coefficient
 *          merge steps) are called often enough that timing them costs more
 *          than they take.
 *   regex  POSIX ERE matched against the function names defined in
 *          pasteque.ll. Isabelle-LLVM mangles instance copies with a hash
 *          suffix (..._f_041791690) that changes on every re-export, so the
 *          injector requires each regex to match EXACTLY ONE define and fails
 *          loudly otherwise instead of silently dropping a phase.
 *
 * Phases nest (CHECKER contains STEP_LOOP contains STEP contains CL ...). The
 * report gives both the inclusive time (the phase and everything it calls) and
 * the self time (the phase minus the nested phases), so the self column sums to
 * the inclusive time of CHECKER.
 *
 * The indentation of the labels is the call nesting that dominates a run, not a
 * strict tree: NORMALIZE_A for instance is reached from check_step, from
 * normalize_poly_sharedS and once from the checker itself for the target
 * polynomial. The self column is exact regardless of how a phase is reached;
 * only the reading of the indentation as a hierarchy is approximate.
 */
#define PST_PHASES(X)                                                          \
  X(CHECKER, "verified checker (total)", 0,                                    \
    "^LPAC_Efficient_Checker_Synthesis_full_checker_l_s2_impl$")               \
  X(REMAP, "  import input polynomials", 0,                                    \
    "^LPAC_Efficient_Checker_Synthesis_remap_polys_l2_with_err_s_impl$")       \
  X(STEP_LOOP, "  proof step loop", 0,                                         \
    "^LPAC_Efficient_Checker_Synthesis_PAC_checker_l_s_impl$")                 \
  X(STEP, "    check step (dispatch)", 1,                                      \
    "^LPAC_Efficient_Checker_Synthesis_check_step_s_impl$")                    \
  X(CL, "      linear combination", 1,                                         \
    "^LPAC_Efficient_Checker_Synthesis_check_linear_combi_l_s_impl$")          \
  X(CL_PREP, "        prepare sources", 1,                                     \
    "^LPAC_Efficient_Checker_Synthesis_linear_combi_l_prep_s_impl$")           \
  X(EXT, "      extension", 1,                                                 \
    "^LPAC_Efficient_Checker_Synthesis_check_extension_l_impl$")               \
  X(DEL, "      deletion", 1,                                                  \
    "^LPAC_Efficient_Checker_Synthesis_check_del_l_impl$")                     \
  X(NORMALIZE_A, "      normalize polynomial", 1,                              \
    "^LLVM_Polynomials_Array_fully_normalize_polya_impl$")                     \
  X(IMPORT_POLY, "        import polynomial", 2,                               \
    "^LPAC_Efficient_Checker_Synthesis_import_polyS_impl$")                    \
  X(NORMALIZE_S, "        normalize polynomial (shared)", 2,                   \
    "^LPAC_Efficient_Checker_Synthesis_normalize_poly_sharedS_impl$")          \
  X(SORT_COEFFS, "          sort coefficients", 2,                             \
    "^LPAC_Efficient_Checker_Synthesis_sort_all_coeffs_s_impl$")               \
  X(SORT_MONOMS, "          sort monomials", 2,                                \
    "^LPAC_Efficient_Checker_Synthesis_msort_monoms_impl$")                    \
  X(MULT_POLY, "        multiply polynomials", 2,                              \
    "^LPAC_Efficient_Checker_Synthesis_mult_poly_full_s_impl$")                \
  X(ADD_POLY, "        add polynomials", 2,                                    \
    "^LPAC_Efficient_Checker_Synthesis_add_poly_l_s_lc_impl$")                 \
  X(WEAK_EQ, "        weak equality test", 2,                                  \
    "^LPAC_Efficient_Checker_Synthesis_weak_equality_l_s_impl$")

/* Slot numbers. PST_NPHASES is the number of slots; the injector passes a slot
   in [0, PST_NPHASES) to the hooks below. */
enum {
#define PST_ENUM(id, label, tier, regex) PST_##id,
  PST_PHASES(PST_ENUM)
#undef PST_ENUM
      PST_NPHASES
};

/* -- Hooks called by the injected wrappers ---------------------------------
 * Both are called with a slot number from the enum above. They must be reached
 * in matching pairs; unbalanced or out-of-range calls are ignored rather than
 * trusted, so a mis-injected .ll degrades the report instead of corrupting the
 * process. Re-entrant phases (a phase reached again from inside itself) are
 * counted once: the inclusive time is only accumulated when the outermost
 * activation returns. */
void pst_enter(int64_t slot);
void pst_exit(int64_t slot);

/* Label of a slot, or "?" if out of range. */
const char *pst_phase_label(int64_t slot);

/* Print the phase breakdown, the allocator counters and the resource usage of
   the process to stderr, in the "c "-prefixed style of the SML checker.
   `teardown_secs` covers everything after the checker returned; it is reported
   separately because it is not negligible: the first allocation after the
   checker has freed its heap makes the allocator consolidate several hundred
   megabytes of free list, which on btor128 costs about as much as parsing the
   input polynomials. */
void pst_report(double lex_parse_secs, double checker_secs,
                double teardown_secs, double total_secs);

#endif /* STATS_H */
