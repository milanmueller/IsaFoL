#!/usr/bin/env python3
"""inject_stats.py — add phase timing wrappers to the exported checker IR.

Author: Milan Müller - ALU Freiburg

The verified checker reaches the C driver as a single call (run_checker), so the
driver timers in parser.c/stats.c cannot say where the time inside it goes. This
script rewrites the IR exported by LPAC_Codegen.thy so that the phases listed in
stats.h report themselves to the hooks implemented in stats.c.

    ./inject_stats.py pasteque.ll -o pasteque_stats.ll

For every phase it renames the definition and synthesizes a wrapper that carries
the original name and signature:

    define <ret> @F(<params>) #0 {        ->  define <ret> @F__inner(<params>) #0 {
                                                ... unchanged body ...
                                              }
                                              define <ret> @F(<params>) #0 {
                                                call void @pst_enter(i64 <slot>)
                                                %pst.r = call <ret> @F__inner(...)
                                                call void @pst_exit(i64 <slot>)
                                                ret <ret> %pst.r
                                              }

Only the `define` header line of the phase is touched; no call site and no
instruction of any body is rewritten, and the wrapper's signature is copied
from the original header rather than restated. That matters because the
exported functions return deeply nested LLVM aggregates, which a hand-written
C-level wrapper could only reproduce by guessing the aggregate ABI.

Consequences of wrapping by renaming, both handled on the C side:

  * A self-recursive phase reaches its own wrapper on every recursive call,
    because the recursive call in the body still refers to the original name.
    stats.c therefore keeps a per-slot activation count and only accumulates
    the inclusive time when the outermost activation returns.
  * A wrapped function can no longer be inlined into its callers and blocks
    interprocedural optimization across the call, so an instrumented binary is
    not the production binary. The tier mechanism (see stats.h) keeps the
    default instrumentation at O(#proof steps) calls.

The phase table in stats.h is the single source of truth: this script reads the
PST_PHASES macro from it, so slot numbers cannot drift from the enum that
stats.c derives from the same macro.
"""

import argparse
import os
import re
import sys

# -- reading the phase table from stats.h ----------------------------------

# X(id, "label", tier, "regex") — one entry per phase, in slot order.
_ENTRY_RE = re.compile(
    r'X\(\s*(\w+)\s*,\s*"((?:[^"\\]|\\.)*)"\s*,\s*(\d+)\s*,'
    r'\s*"((?:[^"\\]|\\.)*)"\s*\)'
)


def _unescape(s):
    """Undo the C string escapes that can occur in the phase table."""
    return s.replace('\\"', '"').replace("\\\\", "\\")


class Phase:
    def __init__(self, slot, ident, label, tier, pattern):
        self.slot = slot
        self.ident = ident
        self.label = label
        self.tier = tier
        self.pattern = pattern
        self.regex = re.compile(pattern)
        self.target = None  # name of the matched define, filled in later


def read_phases(path):
    """Parse the PST_PHASES macro of stats.h into a list of Phase objects.

    The slot number is the position in the table, matching the enum that
    stats.c derives from the same macro."""
    with open(path, encoding="utf-8") as f:
        text = f.read()

    start = text.find("#define PST_PHASES(X)")
    if start < 0:
        sys.exit(f"{path}: no '#define PST_PHASES(X)' found")

    # The macro body ends at the first line that does not continue.
    body, line_start = [], start
    for line in text[start:].splitlines():
        body.append(line)
        if not line.rstrip().endswith("\\"):
            break
    macro = "\n".join(body).replace("\\\n", "\n")

    phases = []
    for slot, m in enumerate(_ENTRY_RE.finditer(macro)):
        phases.append(
            Phase(slot, m.group(1), _unescape(m.group(2)), int(m.group(3)),
                  _unescape(m.group(4)))
        )
    if not phases:
        sys.exit(f"{path}: PST_PHASES is empty or could not be parsed")
    del line_start
    return phases


# -- parsing LLVM `define` header lines -------------------------------------

# Everything that may precede the return type of a define. Anything else in
# that position is rejected rather than guessed at, so an IR feature this script
# has not seen turns into an error instead of a silently broken wrapper.
_PRE_TYPE_KEYWORDS = {
    # linkage
    "private", "internal", "available_externally", "linkonce", "weak",
    "common", "appending", "extern_weak", "linkonce_odr", "weak_odr",
    "external",
    # runtime preemption, visibility, dll storage
    "dso_local", "dso_preemptable", "default", "hidden", "protected",
    "dllimport", "dllexport",
    # calling conventions
    "ccc", "fastcc", "coldcc", "webkit_jscc", "anyregcc", "preserve_mostcc",
    "preserve_allcc", "cxx_fast_tlscc", "swiftcc", "swifttailcc", "tailcc",
    "cfguard_checkcc", "ghccc", "tailcc",
    # return value attributes
    "zeroext", "signext", "inreg", "noalias", "nonnull", "noundef", "returned",
}

_OPEN, _CLOSE = "([{<", ")]}>"

_NAME_RE = re.compile(r'@(?:"(?:[^"\\]|\\.)*"|[-a-zA-Z$._0-9]+)')
# A trailing SSA parameter name, i.e. what separates `%polymap %x1` into the
# type `%polymap` and the name `%x1`.
_PARAM_NAME_RE = re.compile(r'\s(%(?:"(?:[^"\\]|\\.)*"|[-a-zA-Z$._0-9]+))\s*$')


def _split_top_level(text, sep=","):
    """Split on `sep` occurrences that are not nested inside a type.

    Parameter lists contain literal aggregate types such as
    `{ i64, { i64, %stra* } }`, whose commas must not be treated as parameter
    separators."""
    parts, depth, cur = [], 0, []
    for ch in text:
        if ch in _OPEN:
            depth += 1
        elif ch in _CLOSE:
            depth -= 1
        if ch == sep and depth == 0:
            parts.append("".join(cur))
            cur = []
        else:
            cur.append(ch)
    parts.append("".join(cur))
    return parts


class Define:
    """The header line of an LLVM function definition, taken apart.

    line == "define " + pre + name + "(" + params + ")" + tail
    """

    def __init__(self, index, line, pre, name, params, tail):
        self.index = index  # line number in the input, 0-based
        self.line = line
        self.pre = pre  # linkage/cconv/attributes and the return type
        self.name = name  # including the leading '@'
        self.params = params  # raw text between the parentheses
        self.tail = tail  # attribute groups and the opening brace

    @property
    def ret_type(self):
        """The return type alone, i.e. `pre` minus the leading keywords."""
        tokens = _split_top_level(self.pre.strip(), " ")
        tokens = [t for t in tokens if t]
        while tokens and tokens[0] in _PRE_TYPE_KEYWORDS:
            tokens.pop(0)
        # `cc <n>` and `align <n>`/`dereferenceable(<n>)` take an argument.
        while len(tokens) >= 2 and tokens[0] in ("cc", "align"):
            tokens = tokens[2:]
        if not tokens:
            sys.exit(f"line {self.index + 1}: no return type in {self.line!r}")
        return " ".join(tokens)

    def param_types(self):
        """Parameter types with the SSA names stripped, in order.

        Parameter attributes precede the name and are kept, so a parameter such
        as `i8* nocapture %p` becomes `i8* nocapture`."""
        raw = self.params.strip()
        if not raw:
            return []
        out = []
        for p in _split_top_level(raw):
            p = p.strip()
            if p == "...":
                sys.exit(
                    f"line {self.index + 1}: {self.name} is variadic; "
                    "a wrapper cannot forward its arguments"
                )
            out.append(_PARAM_NAME_RE.sub("", p).strip())
        return out


def parse_define(index, line):
    """Take a `define ...` header line apart, or return None if it is not one."""
    if not line.startswith("define "):
        return None

    # The function name is the first '@' outside any type: the return type may
    # itself mention named types, as in `{ i8, %stra }`.
    depth, at = 0, None
    for i, ch in enumerate(line):
        if ch in _OPEN:
            depth += 1
        elif ch in _CLOSE:
            depth -= 1
        elif ch == "@" and depth == 0:
            at = i
            break
    if at is None:
        sys.exit(f"line {index + 1}: no function name in {line!r}")

    m = _NAME_RE.match(line, at)
    if not m:
        sys.exit(f"line {index + 1}: malformed function name in {line!r}")
    name = m.group(0)

    if line[m.end()] != "(":
        sys.exit(f"line {index + 1}: expected '(' after {name}")
    depth, close = 0, None
    for i in range(m.end(), len(line)):
        if line[i] in _OPEN:
            depth += 1
        elif line[i] in _CLOSE:
            depth -= 1
            if depth == 0:
                close = i
                break
    if close is None:
        sys.exit(f"line {index + 1}: unterminated parameter list of {name}")

    return Define(
        index=index,
        line=line,
        pre=line[len("define "):at],
        name=name,
        params=line[m.end() + 1:close],
        tail=line[close + 1:],
    )


# -- injection --------------------------------------------------------------

HOOK_ENTER = "@pst_enter"
HOOK_EXIT = "@pst_exit"
INNER_SUFFIX = "__inner"


def make_wrapper(d, slot):
    """Build the wrapper definition that replaces `d` under its original name."""
    types = d.param_types()
    names = [f"%pst.a{i}" for i in range(len(types))]
    sig = ", ".join(f"{t} {n}" for t, n in zip(types, names))
    args = ", ".join(f"{t} {n}" for t, n in zip(types, names))
    ret = d.ret_type

    lines = [f"define {d.pre}{d.name}({sig}){d.tail}"]
    lines.append(f"  call void {HOOK_ENTER}(i64 {slot})")
    if ret == "void":
        lines.append(f"  call void {d.name}{INNER_SUFFIX}({args})")
        lines.append(f"  call void {HOOK_EXIT}(i64 {slot})")
        lines.append("  ret void")
    else:
        lines.append(f"  %pst.r = call {ret} {d.name}{INNER_SUFFIX}({args})")
        lines.append(f"  call void {HOOK_EXIT}(i64 {slot})")
        lines.append(f"  ret {ret} %pst.r")
    lines.append("}")
    return "\n".join(lines)


def inject(ll_lines, phases, tier, only):
    """Rename the selected phases and return (new lines, selected phases)."""
    defines = {}
    for i, line in enumerate(ll_lines):
        d = parse_define(i, line)
        if d is None:
            continue
        if d.name.endswith(INNER_SUFFIX):
            sys.exit(
                f"{d.name} is already present: the input looks like it has "
                "been injected before; run this on the .ll as exported"
            )
        defines[d.name.lstrip("@")] = d

    selected = []
    for p in phases:
        if only is not None:
            if p.ident not in only:
                continue
        elif p.tier > tier:
            continue

        hits = [n for n in defines if p.regex.search(n)]
        # Isabelle-LLVM mangles instance copies with a hash suffix that changes
        # on every re-export, so an ambiguous or stale pattern must be an error:
        # silently dropping the phase would leave a plausible-looking report
        # with a missing row.
        if len(hits) != 1:
            detail = "\n".join(f"    {h}" for h in sorted(hits)[:10])
            sys.exit(
                f"phase {p.ident} (slot {p.slot}): pattern {p.pattern!r} "
                f"matched {len(hits)} definitions, expected exactly 1"
                + (f"\n{detail}" if hits else "")
                + "\n  Update the pattern in stats.h; the mangled names change "
                "when the checker is re-exported."
            )
        p.target = hits[0]
        selected.append(p)

    if not selected:
        sys.exit("no phase selected: nothing to inject")

    out = list(ll_lines)
    wrappers = []
    for p in selected:
        d = defines[p.target]
        out[d.index] = (
            f"define {d.pre}{d.name}{INNER_SUFFIX}({d.params}){d.tail}"
        )
        wrappers.append(make_wrapper(d, p.slot))

    out.append("")
    out.append("; -- phase instrumentation, generated by inject_stats.py ----")
    out.append("; The hooks are implemented in stats.c; the slot numbers are")
    out.append("; the positions in the PST_PHASES table of stats.h.")
    out.append(f"declare void {HOOK_ENTER}(i64)")
    out.append(f"declare void {HOOK_EXIT}(i64)")
    out.append("")
    for p, w in zip(selected, wrappers):
        out.append(f"; slot {p.slot}: {p.ident}")
        out.append(w)
        out.append("")
    return out, selected


# -- command line -----------------------------------------------------------


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    ap = argparse.ArgumentParser(
        description="Wrap the checker phases listed in stats.h for timing.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="The phase table lives in stats.h and is shared with stats.c.",
    )
    ap.add_argument("input", help="the .ll as exported by Isabelle")
    ap.add_argument("-o", "--output", help="where to write the injected .ll")
    ap.add_argument(
        "--stats-h", default=os.path.join(here, "stats.h"),
        help="the header carrying the PST_PHASES table (default: %(default)s)",
    )
    ap.add_argument(
        "--tier", type=int, default=1,
        help="wrap phases up to this tier: 0 = once per run, 1 = per proof "
             "step, 2 = per polynomial operation (default: %(default)s). "
             "Higher tiers cost more measurement overhead and block more "
             "optimization; see stats.h.",
    )
    ap.add_argument(
        "--only", metavar="ID,ID,...",
        help="wrap exactly these phases by identifier, ignoring --tier",
    )
    ap.add_argument(
        "--list", action="store_true",
        help="only report which definition each phase would wrap",
    )
    args = ap.parse_args()

    phases = read_phases(args.stats_h)
    only = None
    if args.only:
        only = {s.strip() for s in args.only.split(",") if s.strip()}
        known = {p.ident for p in phases}
        unknown = only - known
        if unknown:
            sys.exit(
                f"unknown phase(s): {', '.join(sorted(unknown))}\n"
                f"known: {', '.join(sorted(known))}"
            )

    with open(args.input, encoding="utf-8") as f:
        ll_lines = f.read().splitlines()

    out, selected = inject(ll_lines, phases, args.tier, only)

    width = max(len(p.ident) for p in selected)
    for p in selected:
        print(f"  slot {p.slot:2d}  tier {p.tier}  {p.ident:<{width}}  "
              f"{p.target}", file=sys.stderr)
    skipped = len(phases) - len(selected)
    print(
        f"{len(selected)} phase(s) wrapped, {skipped} not selected"
        + (f" (above tier {args.tier})" if only is None else ""),
        file=sys.stderr,
    )

    if args.list:
        return

    if not args.output:
        sys.exit("-o/--output is required unless --list is given")
    with open(args.output, "w", encoding="utf-8") as f:
        f.write("\n".join(out) + "\n")
    print(f"wrote {args.output}", file=sys.stderr)


if __name__ == "__main__":
    main()
