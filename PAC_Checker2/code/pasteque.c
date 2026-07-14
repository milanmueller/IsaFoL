/* pasteque.c — trusted C tokenizer/driver for the PAC checker.
 * Author: Milan Müller - ALU Freiburg
 */

/* We implement a tokenizer for the syntax given in the paper
 * "Practical algebraic calculus and Nullstellensatz with the checkers Pacheck
 * and Pastèque and Nuss-Checker" by Daniela Kaufmann, Mathias Fleury, Armin Biere
 * and Manuel Kauers - https://doi.org/10.1007/s10703-022-00391-x
 *
 * letter       ::= ‘a’ | ‘b’ | . . . | ‘z’ | ‘A’ | ‘B’ | . . . | ‘Z’
 * number       ::= ‘0’ | ‘1’ | . . . | ‘9’
 * constant     ::= (number)+
 * variable     ::= letter (letter | number)∗
 * term         ::= variable (‘*’ variable)∗
 * monomial     ::= constant | [ constant ‘*’ ] term
 * poly         ::= [ ‘-’ ] monomial (‘+’ | ‘-’ monomial)∗
 * id           ::= constant
 * input        ::= (id polynomial ‘;’)∗
 * lin_com_rule ::= id '%' id ['*' '(' poly ')'] ('+' id ['*' '(' poly ')'])* ',' poly ';'
 * del rule     ::= id ‘d’ ‘;’
 * ext rule     ::= id ‘=’ variable ‘,’ poly ‘;’
 * proof        ::= (lin_com_rule | del rule | ext rule)∗
 * target       ::= poly ‘;’
 */

/* getline()/ssize_t are POSIX, not ISO C — request them explicitly. */
#define _POSIX_C_SOURCE 200809L

#include <assert.h>
#include <ctype.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// -- token type definitions -----------------------------------------------
typedef struct {
  const char *ptr;
  size_t len;
} slice;

typedef enum {
  T_EOF = 0,
  T_CONST, // [0-9]+
  T_VAR,   // [a-z | A-Z][a-z |A-Z | 0-9]*
  T_STAR,  // *
  T_PLUS,  // +
  T_MINUS, // -
  T_COMMA, // ,
  T_PERC,   // %
  T_EOL,    // ;
  T_EQ,     // =
  T_LPAREN, // (
  T_RPAREN, // )
} kind;

// ONLY for debugging - TODO: remove
static const char *kind_name(kind k) {
  static const char *const names[] = {
      [T_EOF] = "T_EOF",     [T_CONST] = "T_CONST", [T_VAR] = "T_VAR",
      [T_STAR] = "T_STAR",   [T_PLUS] = "T_PLUS",   [T_MINUS] = "T_MINUS",
      [T_COMMA] = "T_COMMA", [T_EOL] = "T_EOL",     [T_EQ] = "T_EQ",
      [T_PERC] = "T_PERC",   [T_LPAREN] = "T_LPAREN",
      [T_RPAREN] = "T_RPAREN",
  };
  return names[k];
}

typedef struct {
  kind kind;
  slice content;
} token;

typedef struct {
  token *data;
  size_t len;
  size_t cap;
} token_vec;

// After lexing, we shrink capacity to length
typedef struct {
  const token *data;
  size_t len;
} token_array;

// -- Lexing ----------------------------------------------------------
static void tv_push(token_vec *v, token t) {
  if (v->len == v->cap) {
    // Could init based on input lines, but for now we just have hardcoded 32
    size_t new_cap = v->cap ? v->cap * 2 : 32;
    token *new_v = realloc(v->data, new_cap * sizeof *new_v);
    if (new_v == NULL) {
      fprintf(stderr, "[ERROR]: Out of memory during tokenization.\n");
      exit(1);
    }
    v->data = new_v;
    v->cap = new_cap;
  }
  assert(v->len < v->cap);
  v->data[v->len++] = t;
}

static token next_token(const char *buf, size_t n, size_t *pos, size_t *line) {
  while (*pos < n && isspace((unsigned char)buf[*pos])) {
    if (buf[*pos] == '\n')
      (*line)++;
    (*pos)++;
  }
  if ((*pos) >= n)
    return (token){.kind = T_EOF};

  size_t start = *pos;
  char c = buf[*pos];

  if (isdigit((unsigned char)c)) {
    while (*pos < n && isdigit((unsigned char)buf[*pos]))
      (*pos)++;
    return (token){T_CONST, {buf + start, *pos - start}};
  }

  if (isalpha((unsigned char)c)) {
    while (*pos < n && isalnum((unsigned char)buf[*pos]))
      (*pos)++;
    return (token){T_VAR, {buf + start, *pos - start}};
  }

  (*pos)++;
  switch (c) {
  case '*':
    return (token){T_STAR, {buf + start, 1}};
  case '+':
    return (token){T_PLUS, {buf + start, 1}};
  case '-':
    return (token){T_MINUS, {buf + start, 1}};
  case ',':
    return (token){T_COMMA, {buf + start, 1}};
  case ';':
    return (token){T_EOL, {buf + start, 1}};
  case '=':
    return (token){T_EQ, {buf + start, 1}};
  case '%':
    return (token){T_PERC, {buf + start, 1}};
  case '(':
    return (token){T_LPAREN, {buf + start, 1}};
  case ')':
    return (token){T_RPAREN, {buf + start, 1}};
  default:
    fprintf(stderr, "[ERROR]: Unexpected '%c' on line '%zu'\n", c, *line);
    exit(1);
  }
}

static token_array tv_freeze(token_vec *v) {
  token *data = v->data;
  if (v->len > 0) {
    token *shrunk = realloc(v->data, v->len * sizeof *shrunk);
    if (shrunk != NULL) // a *shrinking* realloc may still (rarely) return NULL;
      data = shrunk; // if so, keep the original larger block — it's still valid
  }
  token_array a = {data, v->len};
  *v = (token_vec){0}; // consume the vec: exactly one owner from here on
  return a;
}

// -- Isabelle facing types ----------------------------------------------

// BASICs

typedef struct {
  const slice *vars_ptr;
  size_t num_vars;
} term;

typedef struct {
  // Note that the grammar allows monomials without coefficients
  // In this case we manually set the coefficient to 1 as we will
  // Always have a coefficient on the Isabelle side.
  slice coeff;
  bool neg;
  term vars; // Possibly empty
} monomial;

typedef struct {
  const monomial *mnmls_ptr;
  size_t num_mnmls;
} polynomial;

// INPUTS / SPEC

typedef struct {
  uint64_t idx;
  polynomial poly;
} input;

typedef struct {
  input *inputs;
  size_t num_inputs;
} inputs;

// PROOF

typedef struct {
  polynomial *poly_ptr; // Might be NULL
  uint64_t idx;
} summand;

typedef struct {
  // TODO: Re-check if this actually captures everything
  uint64_t target_idx;
  summand *summands;
  size_t num_summands;
  polynomial res;
} lc_rule;

typedef struct {
  uint64_t idx;
} del_rule;

typedef struct {
  uint64_t idx;
  slice var;
  polynomial *poly;
} ext_rule;

typedef enum {
  S_LINCOM = 0,
  S_DEL,
  S_EXT,
} rule_type;

typedef struct {
  rule_type typ;
  union {
    lc_rule lc;
    del_rule del;
    ext_rule ext;
  };
} rule;

typedef struct {
  rule *rules_ptr;
  size_t num_rules;
} proof;

// -- TARGET --

typedef struct {
  polynomial *poly;
} target;

// -- Parsing ------------------------------------------------------------

// Read file into one big buffer
static char *read_file(const char *path, size_t *out_len) {
  FILE *f = fopen(path, "rb");
  if (f == NULL) {
    fprintf(stderr, "error: cannot open file '%s'\n", path);
    return NULL;
  }
  fseek(f, 0, SEEK_END);
  long size = ftell(f);
  rewind(f);

  if (size < 0) {
    fclose(f);
    return NULL;
  }

  char *buf = malloc((size_t)size);
  if (buf == NULL) {
    fclose(f);
    return NULL;
  }

  *out_len = fread(buf, 1, (size_t)size, f);
  fclose(f);
  return buf;
}

static int process_file(const char *path) {
  size_t n = 0;
  char *buf = read_file(path, &n);
  if (buf == NULL)
    return 1;

  token_vec tv = {0};
  size_t pos = 0, line = 1;

  for (;;) {
    token t = next_token(buf, n, &pos, &line);
    tv_push(&tv, t);
    if (t.kind == T_EOF)
      break;
  }

  // temporary: show what we lexed, to verify the lexer before writing the parser
  for (size_t i = 0; i < tv.len; i++)
    printf("  kind=%s  '%.*s'\n", kind_name(tv.data[i].kind),
           (int)tv.data[i].content.len, tv.data[i].content.ptr);

  // later: token_array toks = { tv.data, tv.len };  ->  hand to the parser
  free(tv.data);
  free(buf);
  return 0;
}

int main(int argc, char **argv) {
  if (argc != 2) {
    fprintf(stderr, "usage: %s <file>\n", argv[0]);
    return 1;
  }
  return process_file(argv[1]);
}
