/* parser.c — trusted C tokenizer/parser for the PAC checker.
 * Author: Milan Müller - ALU Freiburg
 *
 * The parser builds the checker's data structures through the verified builder
 * functions exported from LLVM_Codegen.thy (pasteque.h, term.h): polynomials,
 * the map of input polynomials and the list of proof steps are appended to in
 * O(1) while the token stream is consumed in a single left-to-right pass. The
 * drivers (main.c, stats.c) link against this file; it defines no main.
 */

/* We implement a tokenizer for the syntax given in the paper
 * "Practical algebraic calculus and Nullstellensatz with the checkers Pacheck
 * and Pastèque and Nuss-Checker" by Daniela Kaufmann, Mathias Fleury, Armin
 * Biere and Manuel Kauers - https://doi.org/10.1007/s10703-022-00391-x
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
 * summand      ::= id [ '*' '(' poly ')' ]
 * lin_com_rule ::= id '%' summand ('+' summand)* ',' poly ';'
 * del rule     ::= id ‘d’ ‘;’
 * ext rule     ::= id ‘=’ variable ‘,’ poly ‘;’
 * proof        ::= (lin_com_rule | del rule | ext rule)∗
 * target       ::= poly ‘;’
 */

#include <assert.h>
#include <ctype.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "parser.h"

// -- token type definitions -----------------------------------------------

typedef enum {
  T_EOF = 0,
  T_CONST,  // [0-9]+
  T_VAR,    // [a-z | A-Z][a-z |A-Z | 0-9]*
  T_STAR,   // *
  T_PLUS,   // +
  T_MINUS,  // -
  T_COMMA,  // ,
  T_PERC,   // %
  T_EOL,    // ;
  T_EQ,     // =
  T_LPAREN, // (
  T_RPAREN, // )
} kind;

static const char *kind_name(kind k) {
  static const char *const names[] = {
      [T_EOF] = "T_EOF",     [T_CONST] = "T_CONST",   [T_VAR] = "T_VAR",
      [T_STAR] = "T_STAR",   [T_PLUS] = "T_PLUS",     [T_MINUS] = "T_MINUS",
      [T_COMMA] = "T_COMMA", [T_EOL] = "T_EOL",       [T_EQ] = "T_EQ",
      [T_PERC] = "T_PERC",   [T_LPAREN] = "T_LPAREN", [T_RPAREN] = "T_RPAREN",
  };
  return names[k];
}

typedef struct {
  size_t len;
  const char *ptr;
} slice;

struct token {
  kind kind;
  slice content;
  size_t line; // 1-based line of the token's first character, for errors
};

typedef struct {
  token *data;
  size_t len;
  size_t cap;
} token_vec;

// After lexing, we shrink capacity to length; `token_array` is in parser.h.

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

static token next_token(char *buf, size_t n, size_t *pos, size_t *line) {
  while (*pos < n && isspace((unsigned char)buf[*pos])) {
    if (buf[*pos] == '\n')
      (*line)++;
    (*pos)++;
  }
  if ((*pos) >= n)
    return (token){.kind = T_EOF, .line = *line};

  size_t start = *pos;
  char c = buf[*pos];

  if (isdigit((unsigned char)c)) {
    while (*pos < n && isdigit((unsigned char)buf[*pos]))
      (*pos)++;
    return (token){T_CONST, {.len = *pos - start, .ptr = buf + start}, *line};
  }

  if (isalpha((unsigned char)c)) {
    while (*pos < n && isalnum((unsigned char)buf[*pos]))
      (*pos)++;
    return (token){T_VAR, {.len = *pos - start, .ptr = buf + start}, *line};
  }

  (*pos)++;
  kind k;
  switch (c) {
  case '*':
    k = T_STAR;
    break;
  case '+':
    k = T_PLUS;
    break;
  case '-':
    k = T_MINUS;
    break;
  case ',':
    k = T_COMMA;
    break;
  case ';':
    k = T_EOL;
    break;
  case '=':
    k = T_EQ;
    break;
  case '%':
    k = T_PERC;
    break;
  case '(':
    k = T_LPAREN;
    break;
  case ')':
    k = T_RPAREN;
    break;
  default:
    fprintf(stderr, "[ERROR]: Unexpected '%c' on line %zu\n", c, *line);
    exit(1);
  }
  return (token){k, {.len = 1, .ptr = buf + start}, *line};
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

// -- Parsing ------------------------------------------------------------

typedef struct {
  const token_array *ta;
  size_t pos;
} cursor;

_Noreturn static void die_unexpected(const cursor *c, const char *want) {
  if (c->pos >= c->ta->len || c->ta->data[c->pos].kind == T_EOF)
    fprintf(stderr, "[ERROR] Unexpected end of input - expected %s\n", want);
  else {
    const token *t = &c->ta->data[c->pos];
    fprintf(stderr, "[ERROR] Line %zu: unexpected %s '%.*s' - expected %s\n",
            t->line, kind_name(t->kind), (int)t->content.len, t->content.ptr,
            want);
  }
  exit(1);
}

static kind peek(const cursor *c) {
  return c->pos < c->ta->len ? c->ta->data[c->pos].kind : T_EOF;
}

// Consume the next token if it is of kind k.
static bool accept(cursor *c, kind k) {
  if (peek(c) != k)
    return false;
  c->pos++;
  return true;
}

// Consume the next token, which must be of kind k, and return its text.
static slice expect(cursor *c, kind k, const char *want) {
  if (peek(c) != k)
    die_unexpected(c, want);
  return c->ta->data[c->pos++].content;
}

/* -- Handing data to the verified code --------------------------------------
 * Every object below is produced by a verified builder and afterwards owned by
 * the enclosing object (the checker frees it), so nothing is freed here. */

// Build a string from a slice (chars are copied)
static char *dup_bytes(slice s) {
  char *p = isabelle_llvm_calloc(s.len, 1);
  if (p == NULL) {
    fprintf(stderr, "[ERROR]: Out of memory while copying a variable name.\n");
    exit(1);
  }
  memcpy(p, s.ptr, s.len);
  return p;
}

/* All indices (input polynomials and proof steps) are signed 64-bit values on
 * the Isabelle side, and polymap_update additionally requires idx < INT64_MAX;
 * we apply that bound uniformly. */
static int64_t parse_index(cursor *c) {
  slice s = expect(c, T_CONST, "an index");
  assert(s.len > 0);
  uint64_t v = 0;
  for (size_t i = 0; i < s.len; i++) {
    unsigned d = (unsigned)(s.ptr[i] - '0');
    assert(d < 10); // the lexer only ever puts digits in a T_CONST
    if (v > ((uint64_t)INT64_MAX - 1 - d) / 10) {
      fprintf(stderr,
              "[ERROR] Index '%.*s' is too large (must be below %" PRId64 ")\n",
              (int)s.len, s.ptr, INT64_MAX);
      exit(1);
    }
    v = v * 10 + d;
  }
  return (int64_t)v;
}

/* Coefficients are arbitrary-precision, we use the exported `str_sval` for
 * string -> big-integer conversion. */
static sbi *make_coeff(slice digits, bool neg) {
  strl_builder *b = strl_builder_new();
  if (neg)
    strl_append(b, '-');
  for (size_t i = 0; i < digits.len; i++)
    strl_append(b, digits.ptr[i]);
  return str_sval(strl_finish(b));
}

static const slice ONE = {.len = 1, .ptr = "1"};

// term ::= variable ('*' variable)*
static strnode *parse_term(cursor *c) {
  term_builder *b = term_builder_new();
  slice v = expect(c, T_VAR, "a variable");
  for (;;) {
    term_append(b, (int64_t)v.len, dup_bytes(v));
    if (!accept(c, T_STAR))
      break;
    v = expect(c, T_VAR, "a variable after '*'");
  }
  return term_finish(b);
}

// monomial ::= constant | [ constant '*' ] term
// The sign is not part of the monomial in the grammar; the caller passes it.
static void parse_monomial(cursor *c, polynomial_builder *pb, bool neg) {
  // the grammar allows dropping a coefficient of 1, but the Isabelle side
  // always wants one
  slice coeff = ONE;
  strnode *t;
  if (peek(c) == T_CONST) {
    coeff = expect(c, T_CONST, "a constant");
    t = accept(c, T_STAR) ? parse_term(c) : term_emp(); // bare constant
  } else if (peek(c) == T_VAR) {
    t = parse_term(c);
  } else {
    die_unexpected(c, "a monomial");
  }
  polynomial_append(pb, t, make_coeff(coeff, neg));
}

// poly ::= [ '-' ] monomial ( ('+' | '-') monomial )*
static polynode *parse_polynomial(cursor *c) {
  polynomial_builder *pb = polynomial_builder_new();
  bool neg = accept(c, T_MINUS); // a leading sign belongs to the 1st monomial
  for (;;) {
    parse_monomial(c, pb, neg);
    if (accept(c, T_PLUS))
      neg = false;
    else if (accept(c, T_MINUS))
      neg = true;
    else
      break;
  }
  return polynomial_finish(pb);
}

// The constant polynomial 1, the implicit factor of a summand without one.
static polynode *poly_one(void) {
  polynomial_builder *pb = polynomial_builder_new();
  polynomial_append(pb, term_emp(), make_coeff(ONE, false));
  return polynomial_finish(pb);
}

/* inputs ::= (id poly ';')*
 * Later occurrences of an index overwrite earlier ones (the map is updated in
 * order). */
polymap *parse_inputs(const token_array *ta) {
  cursor c = {ta, 0};
  polymap *m = polymap_emp();
  while (peek(&c) != T_EOF) {
    int64_t idx = parse_index(&c);
    polynode *p = parse_polynomial(&c);
    expect(&c, T_EOL, "';'");
    polymap_update(idx, p, m);
  }
  return m;
}

// summand ::= id [ '*' '(' poly ')' ]
static void parse_summand(cursor *c, srcs_builder *b) {
  int64_t idx = parse_index(c);
  polynode *p;
  if (accept(c, T_STAR)) {
    expect(c, T_LPAREN, "'(' after '*'");
    p = parse_polynomial(c);
    expect(c, T_RPAREN, "')'");
  } else {
    p = poly_one(); // no coefficient: an implicit factor of 1
  }
  srcs_append(b, p, idx);
}

// lin_com_rule ::= id '%' summand ('+' summand)* ',' poly ';'
// The id and the '%' have already been consumed.
static void parse_lc_rule(cursor *c, steps_builder *sb, int64_t idx) {
  srcs_builder *b = srcs_builder_new();
  do
    parse_summand(c, b);
  while (accept(c, T_PLUS));
  expect(c, T_COMMA, "'+' or ','");
  polynode *res = parse_polynomial(c);
  expect(c, T_EOL, "';'");
  steps_append_cl(sb, srcs_finish(b), idx, res);
}

// ext rule ::= id '=' variable ',' poly ';'
// The id and the '=' have already been consumed.
static void parse_ext_rule(cursor *c, steps_builder *sb, int64_t idx) {
  slice var = expect(c, T_VAR, "a variable");
  expect(c, T_COMMA, "','");
  polynode *p = parse_polynomial(c);
  expect(c, T_EOL, "';'");
  steps_append_ext(sb, idx, (int64_t)var.len, dup_bytes(var), p);
}

// rule ::= lin_com_rule | del rule | ext rule — all three start with an id
static void parse_rule(cursor *c, steps_builder *sb) {
  int64_t idx = parse_index(c);
  switch (peek(c)) {
  case T_PERC:
    c->pos++;
    parse_lc_rule(c, sb, idx);
    break;
  case T_EQ:
    c->pos++;
    parse_ext_rule(c, sb, idx);
    break;
  case T_VAR: {
    // 'd' is not a keyword to the lexer, so it arrives as a one-letter variable
    slice s = c->ta->data[c->pos].content;
    if (s.len != 1 || s.ptr[0] != 'd')
      die_unexpected(c, "'%', 'd' or '='");
    c->pos++;
    expect(c, T_EOL, "';'");
    steps_append_del(sb, idx);
    break;
  }
  default:
    die_unexpected(c, "'%', 'd' or '='");
  }
}

// proof ::= (lin_com_rule | del rule | ext rule)*
stepnode *parse_proof(const token_array *ta) {
  cursor c = {ta, 0};
  steps_builder *sb = steps_builder_new();
  while (peek(&c) != T_EOF)
    parse_rule(&c, sb);
  return steps_finish(sb);
}

// target ::= poly ';' — the whole file is one polynomial
polynode *parse_target(const token_array *ta) {
  cursor c = {ta, 0};
  polynode *p = parse_polynomial(&c);
  expect(&c, T_EOL, "';'");
  if (peek(&c) != T_EOF)
    die_unexpected(&c, "end of file after the target polynomial");
  return p;
}

// -- IO ----------------------------------------------------------------------

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

/* Read a file and tokenize it. On success the caller owns both *buf_out (the
 * text the token slices point into) and ta_out->data. */
int lex_file(const char *path, char **buf_out, token_array *ta_out) {
  size_t n = 0;
  char *buf = read_file(path, &n);
  if (buf == NULL)
    return 1;
  /* Every string handed to the verified checker must have a length below 2^63:
   * the exported code represents strings as arrays with a signed 64-bit length.
   * All tokens are substrings of this buffer, so bounding the file bounds
   * them all. */
  if (n >= ((size_t)1 << 63)) {
    fprintf(stderr, "%s: file too large (%zu bytes)\n", path, n);
    free(buf);
    return 1;
  }

  token_vec tv = {0};
  size_t pos = 0, line = 1;

  for (;;) {
    token t = next_token(buf, n, &pos, &line);
    tv_push(&tv, t);
    if (t.kind == T_EOF)
      break;
  }

  *buf_out = buf;
  *ta_out = tv_freeze(&tv);
  return 0;
}
