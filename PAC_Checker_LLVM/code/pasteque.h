/* Hand-written header for code/pasteque.ll, exported with `export_llvm (no_header)`
   from LPAC_Codegen.thy. The signed big integer contains a 1-bit sign flag, which the
   Isabelle-LLVM header generator cannot express, and several values are LLVM aggregates.
   The type names match the `rewrites` clause of the export, i.e. the %-types in the .ll.

   Lists are built with a builder: X_builder_new() creates it, X_append(builder, ...) appends
   at the end in O(1), X_finish(builder) frees the builder and returns the finished list. */
#ifndef _PASTEQUE_H
#define _PASTEQUE_H 1

#include <stdint.h>
#include "term.h"   /* stra, strnode, term_builder (terms); charnode, strl_builder (character lists) */

typedef struct sbi sbi;                               /* signed big integer (boxed) */
typedef struct polynode polynode;                     /* polynomial: list of (term, coefficient) */
typedef struct polynomial_builder polynomial_builder;
typedef struct polymap polymap;                       /* indexed input polynomials (boxed) */
typedef struct srcsnode srcsnode;                     /* sources of a linear combination: list of (polynomial, index) */
typedef struct srcs_builder srcs_builder;
typedef struct stepnode stepnode;                     /* proof: list of steps */
typedef struct steps_builder steps_builder;

/* Big integers. Parses an ASCII signed decimal numeral given as a character list.
   Precondition: the list is a valid signed numeral. */
sbi* str_sval(charnode*);

/* Polynomials. polynomial_append consumes the term and the coefficient. */
polynode*            polynomial_emp(void);
polynomial_builder*  polynomial_builder_new(void);
void                 polynomial_append(polynomial_builder*, strnode* term, sbi* coeff);
polynode*            polynomial_finish(polynomial_builder*);

/* Indexed input polynomials. Precondition of polymap_update: idx < INT64_MAX. */
polymap* polymap_emp(void);
void     polymap_update(int64_t idx, polynode* poly, polymap*);

/* Sources of a linear combination step. */
srcs_builder* srcs_builder_new(void);
void          srcs_append(srcs_builder*, polynode* poly, int64_t idx);
srcsnode*     srcs_finish(srcs_builder*);

/* Proof steps. Steps are built directly into the step list. */
steps_builder* steps_builder_new(void);
void           steps_append_cl(steps_builder*, srcsnode* srcs, int64_t idx, polynode* res);
void           steps_append_ext(steps_builder*, int64_t idx, int64_t var_len, char* var, polynode* res);
void           steps_append_del(steps_builder*, int64_t idx);
stepnode*      steps_finish(steps_builder*);

/* Checker entry point. Consumes all three objects. Returns the status tag (see
   status_assn in PAC_Checker_Error.thy): 0 = SUCCESS, 1 = FOUND, 2 = FAILED. On FAILED a
   length-carrying, not NUL-terminated error message is stored through msg. */
char run_checker(polymap* inputs, stepnode* proof, polynode* target, stra* msg);

#endif
