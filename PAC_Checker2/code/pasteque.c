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
#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// -- Arena allocator ---------------------------------------------------------
// Note that with the current design, the arena would live on, next to the
// datastructures on the Isabelle side (often lists)...
// Maybe we free the arena from Isabelle?

#define ARENA_BLOCK_MIN (64u * 1024u)

typedef struct arena_block {
  struct arena_block *next;
  size_t used, cap;
  char data[];
} arena_block;

typedef struct {
  arena_block *head; // block we are bumping from; full blocks hang off ->next
} arena;

/* Prefer the ARENA_NEW macro below over calling this directly. */
static void *arena_alloc(arena *a, size_t n, size_t size, size_t align) {
  if (n != 0 && size > SIZE_MAX / n) {
    fprintf(stderr, "[ERROR]: Allocation size overflow.\n");
    exit(1);
  }
  size_t bytes = n * size;

  arena_block *cur = a->head;
  if (cur != NULL) {
    uintptr_t base = (uintptr_t)cur->data + cur->used;
    size_t pad = (size_t)(-base & (uintptr_t)(align - 1));
    size_t left = cur->cap - cur->used;
    if (pad <= left && bytes <= left - pad) {
      cur->used += pad + bytes;
      return (void *)(base + pad);
    }
  }

  size_t cap = bytes + align;
  if (cap < ARENA_BLOCK_MIN)
    cap = ARENA_BLOCK_MIN;
  arena_block *nb = malloc(sizeof *nb + cap);
  if (nb == NULL) {
    fprintf(stderr, "[ERROR]: Out of memory during parsing.\n");
    exit(1);
  }
  nb->cap = cap;

  uintptr_t base = (uintptr_t)nb->data;
  size_t pad = (size_t)(-base & (uintptr_t)(align - 1));
  nb->used = pad + bytes;

  if (cur != NULL && cap > ARENA_BLOCK_MIN) {
    // Oversized request: give it a block of its own and keep the current block
    // as head, so its remaining space still gets used by later allocations.
    nb->next = cur->next;
    cur->next = nb;
  } else {
    nb->next = cur;
    a->head = nb;
  }
  return (void *)(base + pad);
}

#define ARENA_NEW(a, T, n) ((T *)arena_alloc((a), (n), sizeof(T), _Alignof(T)))

static void arena_free(arena *a) {
  for (arena_block *b = a->head; b != NULL;) {
    arena_block *next = b->next;
    free(b);
    b = next;
  }
  a->head = NULL;
}

// -- token type definitions -----------------------------------------------
typedef struct {
  const char *ptr;
  size_t len;
} slice;

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
  polynomial poly;
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
  polynomial poly;
} target;

// -- Parsing ------------------------------------------------------------

_Noreturn static void die_unexpected(const token_array *ta, size_t pos,
                                     const char *want) {
  // TODO: tokens carry no line number yet, so errors cannot point at a line.
  if (pos >= ta->len || ta->data[pos].kind == T_EOF)
    fprintf(stderr, "[ERROR] Unexpected end of input - expected %s\n", want);
  else
    fprintf(stderr, "[ERROR] Unexpected %s '%.*s' - expected %s\n",
            kind_name(ta->data[pos].kind), (int)ta->data[pos].content.len,
            ta->data[pos].content.ptr, want);
  exit(1);
}

static uint64_t slice_to_u64(slice s) {
  assert(s.len > 0);
  uint64_t v = 0;
  for (size_t i = 0; i < s.len; i++) {
    unsigned d = (unsigned)(s.ptr[i] - '0');
    assert(d < 10); // the lexer only ever puts digits in a T_CONST
    // TODO: potentially we have to handle number >= UINT64_MAX.
    // In that case, casting should be done on the Isabelle side...
    if (v > (UINT64_MAX - d) / 10) {
      fprintf(stderr, "[ERROR] Index '%.*s' does not fit in 64 bits\n",
              (int)s.len, s.ptr);
      exit(1);
    }
    v = v * 10 + d;
  }
  return v;
}

static bool is_poly_token(kind k) {
  switch (k) {
  case T_CONST:
  case T_VAR:
  case T_STAR:
  case T_PLUS:
  case T_MINUS:
    return true;
  default:
    return false;
  }
}

/* A polynomial is built only from the tokens above, so its extent is just the
 * maximal run of them: whatever terminator the caller expects (';', ')', ',')
 * ends it implicitly, and parse_polynomial needs no terminator argument. */
static size_t poly_end(const token_array *ta, size_t pos) {
  while (pos < ta->len && is_poly_token(ta->data[pos].kind))
    pos++;
  return pos;
}

// poly ::= [ '-' ] monomial ( ('+' | '-') monomial )*
static size_t count_monomials(const token_array *ta, size_t pos, size_t end) {
  if (pos < end && ta->data[pos].kind == T_MINUS)
    pos++; // leading sign belongs to the first monomial, it is not a separator
  size_t n = 1;
  for (; pos < end; pos++)
    if (ta->data[pos].kind == T_PLUS || ta->data[pos].kind == T_MINUS)
      n++;
  return n;
}

// term ::= variable ('*' variable)*
static term parse_term(arena *a, const token_array *ta, size_t *pos,
                       size_t end) {
  if (*pos >= end || ta->data[*pos].kind != T_VAR)
    die_unexpected(ta, *pos, "a variable");

  size_t start = *pos, p = *pos + 1, num_vars = 1;
  while (p < end && ta->data[p].kind == T_STAR) {
    if (p + 1 >= end || ta->data[p + 1].kind != T_VAR)
      die_unexpected(ta, p + 1, "a variable after '*'");
    num_vars++;
    p += 2;
  }

  slice *vars = ARENA_NEW(a, slice, num_vars);
  for (size_t i = 0; i < num_vars; i++)
    vars[i] = ta->data[start + 2 * i].content;

  *pos = p;
  return (term){vars, num_vars};
}

// monomial ::= constant | [ constant '*' ] term
// The sign is not part of the monomial in the grammar; the caller fills it in.
static monomial parse_monomial(arena *a, const token_array *ta, size_t *pos,
                               size_t end) {
  static const char one[] = "1";
  slice coeff = {one, 1}; // the grammar allows dropping a coefficient of 1,
                          // but the Isabelle side always wants one

  if (*pos >= end)
    die_unexpected(ta, *pos, "a monomial");

  if (ta->data[*pos].kind == T_CONST) {
    coeff = ta->data[*pos].content;
    (*pos)++;
    if (*pos >= end || ta->data[*pos].kind != T_STAR)
      return (monomial){coeff, false, (term){NULL, 0}}; // bare constant
    (*pos)++;                                           // consume the '*'
  }
  return (monomial){coeff, false, parse_term(a, ta, pos, end)};
}

static polynomial parse_polynomial(arena *a, const token_array *ta,
                                   size_t *pos) {
  size_t end = poly_end(ta, *pos);
  if (end == *pos)
    die_unexpected(ta, *pos, "a polynomial");

  size_t num_mnmls = count_monomials(ta, *pos, end);
  monomial *mnmls = ARENA_NEW(a, monomial, num_mnmls);

  bool neg = false;
  if (ta->data[*pos].kind == T_MINUS) {
    neg = true;
    (*pos)++;
  }

  for (size_t i = 0;; i++) {
    assert(i < num_mnmls);
    mnmls[i] = parse_monomial(a, ta, pos, end);
    mnmls[i].neg = neg;
    if (*pos >= end) {
      assert(i + 1 == num_mnmls); // count_monomials agrees with what we parsed
      break;
    }
    switch (ta->data[*pos].kind) {
    case T_MINUS:
      neg = true;
      break;
    case T_PLUS:
      neg = false;
      break;
    default:
      die_unexpected(ta, *pos, "'+' or '-'");
    }
    (*pos)++;
  }
  return (polynomial){mnmls, num_mnmls};
}

// input ::= id poly ';'
static input parse_input(arena *a, const token_array *ta, size_t *pos) {
  if (*pos >= ta->len || ta->data[*pos].kind != T_CONST)
    die_unexpected(ta, *pos, "an index");
  uint64_t idx = slice_to_u64(ta->data[*pos].content);
  (*pos)++;

  polynomial poly = parse_polynomial(a, ta, pos);

  if (*pos >= ta->len || ta->data[*pos].kind != T_EOL)
    die_unexpected(ta, *pos, "';'");
  (*pos)++;

  return (input){idx, poly};
}

/* inputs ::= (id poly ';')*
 * Only parse_input consumes a ';' and it consumes exactly one, so the number of
 * inputs is the number of ';' in the token stream. Parsing still runs to T_EOF
 * rather than looping `num_inputs` times: an unterminated final input then
 * fails inside parse_input pointing at the missing ';', instead of silently
 * not being parsed and being reported as trailing garbage. */
static inputs parse_inputs(arena *a, const token_array *ta) {
  size_t num_inputs = 0;
  for (size_t i = 0; i < ta->len; i++)
    if (ta->data[i].kind == T_EOL)
      num_inputs++;

  input *arr = ARENA_NEW(a, input, num_inputs);
  size_t pos = 0, i = 0;
  while (pos < ta->len && ta->data[pos].kind != T_EOF) {
    input in = parse_input(a, ta, &pos); // bails out if no ';' terminates it
    assert(i < num_inputs); // ..so returning here means one more ';' was eaten
    arr[i++] = in;
  }
  assert(i == num_inputs);

  return (inputs){arr, num_inputs};
}

// summand ::= id [ '*' '(' poly ')' ]
static summand parse_summand(arena *a, const token_array *ta, size_t *pos) {
  if (*pos >= ta->len || ta->data[*pos].kind != T_CONST)
    die_unexpected(ta, *pos, "an index");
  uint64_t idx = slice_to_u64(ta->data[*pos].content);
  (*pos)++;

  if (*pos >= ta->len || ta->data[*pos].kind != T_STAR)
    return (summand){NULL, idx}; // no coefficient: an implicit factor of 1
  (*pos)++;

  if (*pos >= ta->len || ta->data[*pos].kind != T_LPAREN)
    die_unexpected(ta, *pos, "'(' after '*'");
  (*pos)++;

  polynomial *poly = ARENA_NEW(a, polynomial, 1);
  *poly = parse_polynomial(a, ta, pos);

  if (*pos >= ta->len || ta->data[*pos].kind != T_RPAREN)
    die_unexpected(ta, *pos, "')'");
  (*pos)++;

  return (summand){poly, idx};
}

/* The '+' separating two summands and the '+' inside a coefficient poly such as
 * '*(-l72*l62+l62-1)' are the same token, so only the ones outside parentheses
 * count. The list ends at the first ',' at depth 0 — a poly never contains one,
 * so that comma can only be the one before the result poly. */
static size_t count_summands(const token_array *ta, size_t pos) {
  size_t n = 1, depth = 0;
  for (; pos < ta->len; pos++) {
    switch (ta->data[pos].kind) {
    case T_LPAREN:
      depth++;
      break;
    case T_RPAREN:
      if (depth == 0)
        die_unexpected(ta, pos, "','"); // unbalanced: no '(' opened it
      depth--;
      break;
    case T_PLUS:
      if (depth == 0)
        n++;
      break;
    case T_COMMA:
      if (depth == 0)
        return n;
      break;
    case T_EOL:
    case T_EOF:
      die_unexpected(ta, pos, "','"); // rule ended before the result poly
    default:
      break;
    }
  }
  die_unexpected(ta, pos, "','");
}

// lin_com_rule ::= id '%' summand ('+' summand)* ',' poly ';'
// The id and the '%' have already been consumed.
static lc_rule parse_lc_rule(arena *a, const token_array *ta, size_t *pos,
                             uint64_t idx) {
  size_t num_summands = count_summands(ta, *pos);
  summand *summands = ARENA_NEW(a, summand, num_summands);

  for (size_t i = 0;; i++) {
    assert(i < num_summands);
    summands[i] = parse_summand(a, ta, pos);
    if (*pos >= ta->len || ta->data[*pos].kind != T_PLUS) {
      assert(i + 1 ==
             num_summands); // count_summands agrees with what we parsed
      break;
    }
    (*pos)++; // consume the '+' separating this summand from the next
  }

  if (*pos >= ta->len || ta->data[*pos].kind != T_COMMA)
    die_unexpected(ta, *pos, "','");
  (*pos)++;

  polynomial res = parse_polynomial(a, ta, pos);

  if (*pos >= ta->len || ta->data[*pos].kind != T_EOL)
    die_unexpected(ta, *pos, "';'");
  (*pos)++;

  return (lc_rule){idx, summands, num_summands, res};
}

// ext rule ::= id '=' variable ',' poly ';'
// The id and the '=' have already been consumed.
static ext_rule parse_ext_rule(arena *a, const token_array *ta, size_t *pos,
                               uint64_t idx) {
  if (*pos >= ta->len || ta->data[*pos].kind != T_VAR)
    die_unexpected(ta, *pos, "a variable");
  slice var = ta->data[*pos].content;
  (*pos)++;

  if (*pos >= ta->len || ta->data[*pos].kind != T_COMMA)
    die_unexpected(ta, *pos, "','");
  (*pos)++;

  polynomial poly = parse_polynomial(a, ta, pos);

  if (*pos >= ta->len || ta->data[*pos].kind != T_EOL)
    die_unexpected(ta, *pos, "';'");
  (*pos)++;

  return (ext_rule){idx, var, poly};
}

// rule ::= lin_com_rule | del rule | ext rule — all three start with an id
static rule parse_rule(arena *a, const token_array *ta, size_t *pos) {
  if (*pos >= ta->len || ta->data[*pos].kind != T_CONST)
    die_unexpected(ta, *pos, "an index");
  uint64_t idx = slice_to_u64(ta->data[*pos].content);
  (*pos)++;

  if (*pos >= ta->len)
    die_unexpected(ta, *pos, "'%', 'd' or '='");

  switch (ta->data[*pos].kind) {
  case T_PERC:
    (*pos)++;
    return (rule){.typ = S_LINCOM, .lc = parse_lc_rule(a, ta, pos, idx)};
  case T_EQ:
    (*pos)++;
    return (rule){.typ = S_EXT, .ext = parse_ext_rule(a, ta, pos, idx)};
  case T_VAR: {
    // 'd' is not a keyword to the lexer, so it arrives as a one-letter variable
    slice s = ta->data[*pos].content;
    if (s.len != 1 || s.ptr[0] != 'd')
      die_unexpected(ta, *pos, "'%', 'd' or '='");
    (*pos)++;
    if (*pos >= ta->len || ta->data[*pos].kind != T_EOL)
      die_unexpected(ta, *pos, "';'");
    (*pos)++;
    return (rule){.typ = S_DEL, .del = (del_rule){idx}};
  }
  default:
    die_unexpected(ta, *pos, "'%', 'd' or '='");
  }
}

/* proof ::= (lin_com_rule | del rule | ext rule)*
 * Each rule ends in exactly one ';' and no rule contains another, so the number
 * of rules is the number of ';' — the same counting argument as parse_inputs.
 * The ';' inside a coefficient poly is impossible: those are paren-delimited. */
static proof parse_proof(arena *a, const token_array *ta) {
  size_t num_rules = 0;
  for (size_t i = 0; i < ta->len; i++)
    if (ta->data[i].kind == T_EOL)
      num_rules++;

  rule *arr = ARENA_NEW(a, rule, num_rules);
  size_t pos = 0, i = 0;
  while (pos < ta->len && ta->data[pos].kind != T_EOF) {
    rule r = parse_rule(a, ta, &pos); // bails out if no ';' terminates it
    assert(i < num_rules); // ..so returning here means one more ';' was eaten
    arr[i++] = r;
  }
  assert(i == num_rules);

  return (proof){arr, num_rules};
}

// target ::= poly ';' — the whole file is one polynomial
static target parse_target(arena *a, const token_array *ta) {
  size_t pos = 0;
  polynomial poly = parse_polynomial(a, ta, &pos);

  if (pos >= ta->len || ta->data[pos].kind != T_EOL)
    die_unexpected(ta, pos, "';'");
  pos++;

  if (pos < ta->len && ta->data[pos].kind != T_EOF)
    die_unexpected(ta, pos, "end of file after the target polynomial");

  return (target){poly};
}

// -- IO ----------------------------------------------------------------------

typedef enum { F_INPUT = 0, F_PROOF, F_TARGET } file_type;

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

/* ONLY for debugging - TODO: remove
 * Prints back in input syntax, so that `pasteque f.input` reproduces f.input
 * verbatim and the parser can be checked by diffing. */
static void dump_polynomial(const polynomial *p) {
  for (size_t i = 0; i < p->num_mnmls; i++) {
    const monomial *m = &p->mnmls_ptr[i];
    if (m->neg)
      printf("-");
    else if (i > 0)
      printf("+");

    // a coefficient of 1 in front of a term was possibly synthesized by us
    bool hide_coeff =
        m->vars.num_vars > 0 && m->coeff.len == 1 && m->coeff.ptr[0] == '1';
    if (!hide_coeff)
      printf("%.*s", (int)m->coeff.len, m->coeff.ptr);

    for (size_t j = 0; j < m->vars.num_vars; j++)
      printf("%s%.*s", (j == 0 && hide_coeff) ? "" : "*",
             (int)m->vars.vars_ptr[j].len, m->vars.vars_ptr[j].ptr);
  }
}

/* ONLY for debugging - TODO: remove */
static void dump_rule(const rule *r) {
  switch (r->typ) {
  case S_LINCOM:
    printf("%" PRIu64 " %% ", r->lc.target_idx);
    for (size_t i = 0; i < r->lc.num_summands; i++) {
      const summand *s = &r->lc.summands[i];
      if (i > 0)
        printf(" + ");
      printf("%" PRIu64, s->idx);
      if (s->poly_ptr != NULL) { // a missing coefficient means 1, not 1*(1)
        printf(" *(");
        dump_polynomial(s->poly_ptr);
        printf(")");
      }
    }
    printf(", ");
    dump_polynomial(&r->lc.res);
    printf(";\n");
    break;
  case S_DEL:
    printf("%" PRIu64 " d;\n", r->del.idx);
    break;
  case S_EXT:
    printf("%" PRIu64 " = %.*s, ", r->ext.idx, (int)r->ext.var.len,
           r->ext.var.ptr);
    dump_polynomial(&r->ext.poly);
    printf(";\n");
    break;
  }
}

/* Read a file and tokenize it. On success the caller owns both *buf_out (the
 * text the token slices point into) and ta_out->data. */
static int lex_file(const char *path, char **buf_out, token_array *ta_out) {
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

  *buf_out = buf;
  *ta_out = tv_freeze(&tv);
  return 0;
}

static int process_file(const char *path, file_type typ) {
  char *buf = NULL;
  token_array ta = {0};
  if (lex_file(path, &buf, &ta) != 0)
    return 1;

  arena a = {0};

  // temporary: print back what we parsed, to verify the parser - TODO: remove
  switch (typ) {
  case F_INPUT: {
    inputs ins = parse_inputs(&a, &ta);
    for (size_t i = 0; i < ins.num_inputs; i++) {
      printf("%" PRIu64 " ", ins.inputs[i].idx);
      dump_polynomial(&ins.inputs[i].poly);
      printf(";\n");
    }
    break;
  }
  case F_PROOF: {
    proof p = parse_proof(&a, &ta);
    for (size_t i = 0; i < p.num_rules; i++)
      dump_rule(&p.rules_ptr[i]);
    break;
  }
  case F_TARGET: {
    target t = parse_target(&a, &ta);
    dump_polynomial(&t.poly);
    printf(";\n");
    break;
  }
  }

  arena_free(&a);
  free((void *)ta.data);
  free(buf);
  return 0;
}

int main(int argc, char **argv) {
  if (argc != 4) {
    fprintf(stderr, "usage: %s <file.input> <file.proof> <file.target>\n",
            argv[0]);
    return 1;
  }
  if (process_file(argv[1], F_INPUT) != 0)
    return 1;
  if (process_file(argv[2], F_PROOF) != 0)
    return 1;
  if (process_file(argv[3], F_TARGET) != 0)
    return 1;
  return 0;
}
