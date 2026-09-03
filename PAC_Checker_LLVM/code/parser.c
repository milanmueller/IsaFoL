/* parser.c — trusted C tokenizer/parser for the PAC checker.
 * Author: Milan Müller - ALU Freiburg
 *
 * The Isabelle-facing data structures come from pasteque.h (via parser.h). This
 * file also carries a small standalone dump driver (process_file + main), guarded
 * by PARSER_NO_MAIN so parser.c can be reused as a library (e.g. by parser_test.c).
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

/* The Isabelle-facing data structures (slice, term, monomial, polynomial,
 * input, inputs, summand, summands, lc_rule, ext_rule, rule, proof) and the
 * parser API live in parser.h, which pulls in the generated ABI header
 * pasteque.h. Their memory layout matches the verified import functions. */
#include "parser.h"

// -- Arena allocator ---------------------------------------------------------
// Note that with the current design, the arena would live on, next to the
// datastructures on the Isabelle side (often lists)...
// Maybe we free the arena from Isabelle?

#define ARENA_BLOCK_MIN (64u * 1024u)

// `arena_block` is forward-declared in parser.h (opaque); `arena` is defined
// there too. Only the block layout is private to this file.
struct arena_block {
  struct arena_block *next;
  size_t used, cap;
  char data[];
};

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

void arena_free(arena *a) {
  for (arena_block *b = a->head; b != NULL;) {
    arena_block *next = b->next;
    free(b);
    b = next;
  }
  a->head = NULL;
}

// -- token type definitions -----------------------------------------------
// `slice` comes from pasteque.h (length-first: { uint64_t len; char *ptr; }).

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

// `token` is forward-declared in parser.h (opaque to callers); define it here.
struct token {
  kind kind;
  slice content;
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
    return (token){.kind = T_EOF};

  size_t start = *pos;
  char c = buf[*pos];

  if (isdigit((unsigned char)c)) {
    while (*pos < n && isdigit((unsigned char)buf[*pos]))
      (*pos)++;
    return (token){T_CONST, {.len = *pos - start, .ptr = buf + start}};
  }

  if (isalpha((unsigned char)c)) {
    while (*pos < n && isalnum((unsigned char)buf[*pos]))
      (*pos)++;
    return (token){T_VAR, {.len = *pos - start, .ptr = buf + start}};
  }

  (*pos)++;
  switch (c) {
  case '*':
    return (token){T_STAR, {.len = 1, .ptr = buf + start}};
  case '+':
    return (token){T_PLUS, {.len = 1, .ptr = buf + start}};
  case '-':
    return (token){T_MINUS, {.len = 1, .ptr = buf + start}};
  case ',':
    return (token){T_COMMA, {.len = 1, .ptr = buf + start}};
  case ';':
    return (token){T_EOL, {.len = 1, .ptr = buf + start}};
  case '=':
    return (token){T_EQ, {.len = 1, .ptr = buf + start}};
  case '%':
    return (token){T_PERC, {.len = 1, .ptr = buf + start}};
  case '(':
    return (token){T_LPAREN, {.len = 1, .ptr = buf + start}};
  case ')':
    return (token){T_RPAREN, {.len = 1, .ptr = buf + start}};
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
  return (term){.num_vars = num_vars, .vars_ptr = vars};
}

// monomial ::= constant | [ constant '*' ] term
// The sign is not part of the monomial in the grammar; the caller fills it in.
static monomial parse_monomial(arena *a, const token_array *ta, size_t *pos,
                               size_t end) {
  static const char one[] = "1";
  // the grammar allows dropping a coefficient of 1, but the Isabelle side
  // always wants one (read-only, so casting away const on the literal is safe)
  slice coeff = {.len = 1, .ptr = (char *)one};

  if (*pos >= end)
    die_unexpected(ta, *pos, "a monomial");

  if (ta->data[*pos].kind == T_CONST) {
    coeff = ta->data[*pos].content;
    (*pos)++;
    if (*pos >= end || ta->data[*pos].kind != T_STAR)
      return (monomial){
          .coeff = coeff,
          .neg = false,
          .vars = (term){.num_vars = 0, .vars_ptr = NULL}}; // bare constant
    (*pos)++;                                               // consume the '*'
  }
  return (monomial){
      .coeff = coeff, .neg = false, .vars = parse_term(a, ta, pos, end)};
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
  return (polynomial){.num_mnmls = num_mnmls, .mnmls_ptr = mnmls};
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

  return (input){.idx = idx, .poly = poly};
}

/* inputs ::= (id poly ';')*
 * Only parse_input consumes a ';' and it consumes exactly one, so the number of
 * inputs is the number of ';' in the token stream. Parsing still runs to T_EOF
 * rather than looping `num_inputs` times: an unterminated final input then
 * fails inside parse_input pointing at the missing ';', instead of silently
 * not being parsed and being reported as trailing garbage. */
inputs parse_inputs(arena *a, const token_array *ta) {
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

  return (inputs){.num_inputs = num_inputs, .inputs = arr};
}

// summand ::= id [ '*' '(' poly ')' ]
static summand parse_summand(arena *a, const token_array *ta, size_t *pos) {
  if (*pos >= ta->len || ta->data[*pos].kind != T_CONST)
    die_unexpected(ta, *pos, "an index");
  uint64_t idx = slice_to_u64(ta->data[*pos].content);
  (*pos)++;

  if (*pos >= ta->len || ta->data[*pos].kind != T_STAR)
    return (summand){.poly_ptr = NULL,
                     .idx = idx}; // no coefficient: an implicit factor of 1
  (*pos)++;

  if (*pos >= ta->len || ta->data[*pos].kind != T_LPAREN)
    die_unexpected(ta, *pos, "'(' after '*'");
  (*pos)++;

  polynomial *poly = ARENA_NEW(a, polynomial, 1);
  *poly = parse_polynomial(a, ta, pos);

  if (*pos >= ta->len || ta->data[*pos].kind != T_RPAREN)
    die_unexpected(ta, *pos, "')'");
  (*pos)++;

  return (summand){.poly_ptr = poly, .idx = idx};
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
  summand *smds = ARENA_NEW(a, summand, num_summands);

  for (size_t i = 0;; i++) {
    assert(i < num_summands);
    smds[i] = parse_summand(a, ta, pos);
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

  return (lc_rule){.target_idx = idx,
                   .summands = (summands){.num_summands = num_summands,
                                          .summands_ptr = smds},
                   .res = res};
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

  return (ext_rule){.idx = idx, .var = var, .poly = poly};
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
    return (rule){.typ = S_LINCOM, .u.lc = parse_lc_rule(a, ta, pos, idx)};
  case T_EQ:
    (*pos)++;
    return (rule){.typ = S_EXT, .u.ext = parse_ext_rule(a, ta, pos, idx)};
  case T_VAR: {
    // 'd' is not a keyword to the lexer, so it arrives as a one-letter variable
    slice s = ta->data[*pos].content;
    if (s.len != 1 || s.ptr[0] != 'd')
      die_unexpected(ta, *pos, "'%', 'd' or '='");
    (*pos)++;
    if (*pos >= ta->len || ta->data[*pos].kind != T_EOL)
      die_unexpected(ta, *pos, "';'");
    (*pos)++;
    return (rule){.typ = S_DEL, .u.del = idx}; // del arm is a bare uint64_t
  }
  default:
    die_unexpected(ta, *pos, "'%', 'd' or '='");
  }
}

/* proof ::= (lin_com_rule | del rule | ext rule)*
 * Each rule ends in exactly one ';' and no rule contains another, so the number
 * of rules is the number of ';' — the same counting argument as parse_inputs.
 * The ';' inside a coefficient poly is impossible: those are paren-delimited. */
proof parse_proof(arena *a, const token_array *ta) {
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

  return (proof){.num_rules = num_rules, .rules_ptr = arr};
}

// target ::= poly ';' — the whole file is one polynomial
target parse_target(arena *a, const token_array *ta) {
  size_t pos = 0;
  polynomial poly = parse_polynomial(a, ta, &pos);

  if (pos >= ta->len || ta->data[pos].kind != T_EOL)
    die_unexpected(ta, pos, "';'");
  pos++;

  if (pos < ta->len && ta->data[pos].kind != T_EOF)
    die_unexpected(ta, pos, "end of file after the target polynomial");

  return (target){.poly = poly};
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

/* ONLY for debugging - TODO: remove
 * Prints back in input syntax, so that `pasteque f.input` reproduces f.input
 * verbatim and the parser can be checked by diffing. */
void dump_polynomial(const polynomial *p) {
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
void dump_rule(const rule *r) {
  switch (r->typ) {
  case S_LINCOM:
    printf("%" PRIu64 " %% ", r->u.lc.target_idx);
    for (size_t i = 0; i < r->u.lc.summands.num_summands; i++) {
      const summand *s = &r->u.lc.summands.summands_ptr[i];
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
    dump_polynomial(&r->u.lc.res);
    printf(";\n");
    break;
  case S_DEL:
    printf("%" PRIu64 " d;\n", r->u.del);
    break;
  case S_EXT:
    printf("%" PRIu64 " = %.*s, ", r->u.ext.idx, (int)r->u.ext.var.len,
           r->u.ext.var.ptr);
    dump_polynomial(&r->u.ext.poly);
    printf(";\n");
    break;
  }
}

/* Read a file and tokenize it. On success the caller owns both *buf_out (the
 * text the token slices point into) and ta_out->data. */
int lex_file(const char *path, char **buf_out, token_array *ta_out) {
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

/* The standalone checker driver below (main) is compiled only when parser.c is
 * built as its own program. When parser.c is reused as a library (e.g. by
 * parser_test.c), define PARSER_NO_MAIN to drop it — parser_test.c brings its
 * own main and its own copies of the runtime stubs. */
#ifndef PARSER_NO_MAIN

/* -- Runtime stubs expected by the Isabelle-LLVM-exported `run_checker` -------
 * The verified code allocates/frees its heap structures through these hooks;
 * the code generator leaves them as external declarations (see pasteque.ll). */
void *isabelle_llvm_calloc(uint64_t nmemb, uint64_t size) {
  return calloc(nmemb, size);
}
void isabelle_llvm_free(void *ptr) {
  free(ptr);
}

/* Optionally echo the parsed structures back in input syntax (see -v below).
 * dump_polynomial/dump_rule write to stdout, so the headers do too, keeping the
 * verbose dump self-consistent (the machine-readable status still follows it). */
static void dump_parsed(const inputs *ins, const proof *prf,
                        const target *tgt) {
  printf("== inputs ==\n");
  for (size_t i = 0; i < ins->num_inputs; i++) {
    printf("%" PRIu64 " ", ins->inputs[i].idx);
    dump_polynomial(&ins->inputs[i].poly);
    printf(";\n");
  }
  printf("== proof ==\n");
  for (size_t i = 0; i < prf->num_rules; i++)
    dump_rule(&prf->rules_ptr[i]);
  printf("== target ==\n");
  dump_polynomial(&tgt->poly);
  printf(";\n");
}

int main(int argc, char **argv) {
  bool verbose = false;
  int argi = 1;
  if (argc - argi > 0 && strcmp(argv[argi], "-v") == 0) {
    verbose = true;
    argi++;
  }
  if (argc - argi != 3) {
    fprintf(stderr, "usage: %s [-v] <file.input> <file.proof> <file.target>\n",
            argv[0]);
    return 2;
  }

  /* Lex + parse the three files into the flat Isabelle-facing ABI structs. The
   * text buffers must stay alive while the checker runs: the parsed tree's
   * slices point into them, and the importers read the bytes through. */
  char *ibuf = NULL, *pbuf = NULL, *tbuf = NULL;
  token_array ita = {0}, pta = {0}, tta = {0};
  if (lex_file(argv[argi], &ibuf, &ita) != 0)
    return 2;
  if (lex_file(argv[argi + 1], &pbuf, &pta) != 0)
    return 2;
  if (lex_file(argv[argi + 2], &tbuf, &tta) != 0)
    return 2;

  arena a = {0};
  inputs ins = parse_inputs(&a, &ita);
  proof prf = parse_proof(&a, &pta);
  target tgt = parse_target(&a, &tta);

  if (verbose)
    dump_parsed(&ins, &prf, &tgt);

  /* Hand the parsed structures to the verified checker. `target` collapses to a
   * bare polynomial on the Isabelle side, so we pass &tgt.poly. The returned
   * byte is the checker's status tag (see status_assn in PAC_Checker_Error.thy):
   *   0 = SUCCESS  proof steps all check, but the target was not derived
   *   1 = FOUND    proof valid *and* it derives the target polynomial
   *   2 = FAILED   some proof step did not check
   * On FAILED the checker also stores an error message through the out-slice:
   * a length-carrying (NOT NUL-terminated) string it allocated through
   * isabelle_llvm_calloc, owned by us afterwards. On SUCCESS/FOUND the slice is
   * left as {0, NULL}. */
  slice msg = {0};
  char status = RUN_CHECKER(&ins, &prf, &tgt.poly, &msg);

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
  if (msg.ptr != NULL) {
    fprintf(stderr, "run_checker: %.*s\n", (int)msg.len, msg.ptr);
    isabelle_llvm_free(msg.ptr); // the checker allocated it, we own it
  }

  arena_free(&a);
  free((void *)ita.data);
  free(ibuf);
  free((void *)pta.data);
  free(pbuf);
  free((void *)tta.data);
  free(tbuf);

  /* Exit 0 iff the proof is a valid derivation of the target (FOUND). */
  return status == 1 ? 0 : 1;
}
#endif /* PARSER_NO_MAIN */
