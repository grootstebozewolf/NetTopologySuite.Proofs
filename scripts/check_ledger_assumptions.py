#!/usr/bin/env python3
# =============================================================================
# scripts/check_ledger_assumptions.py
# -----------------------------------------------------------------------------
# Claim check for the `doc-kind: ledger` docs/verified-claims.md: every row in
# a `| file : theorem | Meaning | Ax |` table is compared against what the
# kernel says, not against what the prose says.
#
# Per row, every `Mod.v : name` in the first cell is resolved (Locate, scoped
# to that module) and its `Print Assumptions` is read. With
#   A = the axiom allowlist (docs/axiom-allowlist.txt, the 3 Reals axioms)
#   F = A + Flocq's Classical_Prop.classic (the "4" in the Ax legend)
# the row fails when:
#   unconditional  it is not tagged `[cond]` and an assumption outside F
#                  shows up (a Section Hypothesis/Variable the theorem was
#                  never closed over, an Axiom/Parameter, an Admitted). A
#                  conditional or axiom-dependent theorem cannot be listed
#                  as unconditional.
#   ax             the Ax cell over-claims: `0` but not closed; `3` but
#                  outside A; `4` but outside F; `1`/`2` but more axioms
#                  than that. Under-claiming (Ax 3, closed) is allowed.
#                  `C` is refused: the ledger used it both for "closed" and
#                  for Category C (`classic`), so it states neither.
#   resolve        a cited name has no definition in its module.
# Rows in a `[cond]` row may carry extra assumptions; their Ax cell is then
# checked against the allowlisted part only.
#
# Needs the built .vo files (`make full`). CI runs it in the rocq-flocq job
# beside `check_claim_statements.py --elaborate`, sharing its probe runner
# (ROCQ_CMD overrides the launcher). A row's verdicts are printed as
#   [ledger] FAIL <line>: `Mod.v : name` <rule>: <detail>
#
# --list         print the parsed rows (no rocq), for review.
# --selftest     parser and verdict checks on canned Print Assumptions text.
#
# Exit: 0 all rows hold · 1 a row over-claims · 2 probe / usage error.
#
# License: BSD-3-Clause (see LICENSE)
# AI assistance disclosure: AI-drafted; human review pending.
# =============================================================================

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check_claim_statements as ccs  # noqa: E402  (shared probe runner)

ROOT = ccs.ROOT
LEDGER = "docs/verified-claims.md"
ALLOWLIST = os.path.join(ROOT, "docs", "axiom-allowlist.txt")
CLASSIC = "Coq.Logic.Classical_Prop.classic"
ANCHOR = re.compile(r"`([A-Za-z0-9_]+\.v)\s*:\s*([A-Za-z0-9_'{},]+)`")
TAG = "[ledger]"


def allowlist():
    out = set()
    with open(ALLOWLIST, encoding="utf-8") as fh:
        for ln in fh:
            ln = ln.split("#", 1)[0].strip()
            if ln:
                out.add(ln)
    return out


def short(ax):
    """Compare by the last two path components: Rocq prints Stdlib axioms as
    `Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep` or
    `Coq.Logic...` depending on version; the allowlist uses
    `FunctionalExtensionality.functional_extensionality_dep`."""
    parts = ax.split(".")
    return ".".join(parts[-2:])


def cells(line):
    s = line.strip()
    if not s.startswith("|"):
        return None
    # split on unescaped pipes outside backticks
    out, cur, tick = [], "", False
    i = 1
    while i < len(s):
        ch = s[i]
        if ch == "`":
            tick = not tick
        if ch == "\\" and i + 1 < len(s) and s[i + 1] == "|":
            cur += "|"
            i += 2
            continue
        if ch == "|" and not tick:
            out.append(cur.strip())
            cur = ""
        else:
            cur += ch
        i += 1
    if cur.strip():
        out.append(cur.strip())
    return out


def expand(name):
    if "{" not in name:
        return [name]
    stem, rest = name.split("{", 1)
    opts, tail = rest.split("}", 1) if "}" in rest else (rest, "")
    return [stem + o.strip() + tail for o in opts.split(",")]


COND = re.compile(r"\[cond\]|\bcond per entry\b")


def ax_value(cell):
    """Normalise an Ax cell: `0/3` (mixed row) -> its ceiling `3`; the
    `Flocq C1 (classic)` spelling -> `4`."""
    v = cell.strip("` *")
    if "classic" in v:
        return "4"
    if re.match(r"^\d+(/\d+)+$", v):
        return str(max(int(x) for x in v.split("/")))
    return v


def parse_rows(text):
    """-> [(lineno, ax, cond, [(Mod.v, name)])] for rows of Ax tables."""
    rows, in_ax = [], False
    for i, ln in enumerate(text.split("\n"), 1):
        c = cells(ln)
        if c is None:
            in_ax = False
            continue
        if c and set("".join(c)) <= set("-: "):
            continue                       # separator row
        if c and c[-1].strip("` *") == "Ax" and "theorem" in c[0]:
            in_ax = True
            continue
        if not in_ax or len(c) < 3:
            continue
        refs = [(m.group(1), n) for m in ANCHOR.finditer(c[0])
                for n in expand(m.group(2))]
        if not refs:
            continue
        rows.append((i, ax_value(c[-1]), bool(COND.search(ln)), refs))
    return rows


def verdict(ax_cell, cond, axioms, allow):
    """-> list of (rule, detail). `axioms` are fully qualified names."""
    A = {short(a) for a in allow}
    F = A | {short(CLASSIC)}
    names = [short(a) for a in axioms]
    extra = [a for a, n in zip(axioms, names) if n not in F]
    known = [n for n in names if n in F]
    out = []
    if extra and not cond:
        out.append(("unconditional", "listed without `[cond]` but rests on "
                    "%s" % ", ".join(extra)))
    used = known if cond else names
    if ax_cell == "0":
        if used:
            out.append(("ax", "Ax `%s` claims closed; uses %s"
                        % (ax_cell, ", ".join(used))))
    elif ax_cell == "3":
        bad = [n for n in used if n not in A]
        if bad:
            out.append(("ax", "Ax `3` (Reals allowlist) but uses %s"
                        % ", ".join(bad)))
    elif ax_cell == "4":
        bad = [n for n in used if n not in F]
        if bad:
            out.append(("ax", "Ax `4` but uses %s" % ", ".join(bad)))
    elif ax_cell.isdigit():
        if len(used) > int(ax_cell):
            out.append(("ax", "Ax `%s` but uses %d: %s"
                        % (ax_cell, len(used), ", ".join(used))))
    else:
        out.append(("ax", "unrecognised Ax cell `%s` (want 0|1|2|3|4; `C` "
                    "is ambiguous)" % ax_cell))
    return out


def module_of(base):
    for lane in ("theories", "theories-flocq"):
        if os.path.isfile(os.path.join(ROOT, lane, base)):
            return "%s/%s" % (lane, base)
    return None


def locate_pick(text, ln):
    """From `Locate name.` output pick the constant/inductive under module
    logical name `ln` (also inside its submodules)."""
    for line in text.split("\n"):
        m = re.match(r"^\s*(Constant|Inductive|Constructor|Projection)\s+"
                     r"([\w'.]+)", line)
        if m and (m.group(2).startswith(ln + ".")):
            return m.group(2)
    return None


def run_all(rows, allow):
    errs, fails = [], []
    mods, todo = {}, []
    for lineno, ax, cond, refs in rows:
        for base, name in refs:
            rel = module_of(base)
            if rel is None:
                fails.append((lineno, base, name, "resolve",
                              "no %s under theories*/" % base))
                continue
            mods[rel] = ccs.logical_name(rel)
            todo.append((lineno, ax, cond, base, name, mods[rel]))
    head = "".join("Require %s.\n" % m for m in sorted(set(mods.values())))
    head += "Set Printing Width 100000.\n"
    body = head
    for k, (_l, _a, _c, _b, name, _ln) in enumerate(todo):
        body += ccs.mark("LOC %d" % k) + "Locate %s.\n" % name
    body += ccs.mark("END")
    rc, out = ccs.run_probe("Ledger_locate", body)
    if rc != 0:
        errs.append("locate probe failed (rc %d):\n%s" % (rc, out[-3000:]))
        return errs, fails
    sec = ccs.sections(out)
    resolved = []
    for k, (lineno, ax, cond, base, name, ln) in enumerate(todo):
        fq = locate_pick(sec.get("LOC %d" % k, ""), ln)
        if fq is None:
            fails.append((lineno, base, name, "resolve",
                          "not defined in %s" % ln))
        else:
            resolved.append((lineno, ax, cond, base, name, fq))
    body = head
    for k, r in enumerate(resolved):
        body += ccs.mark("PA %d" % k) + "Print Assumptions %s.\n" % r[5]
    body += ccs.mark("END")
    rc, out = ccs.run_probe("Ledger_assumptions", body)
    if rc != 0:
        errs.append("assumptions probe failed (rc %d):\n%s" % (rc, out[-3000:]))
        return errs, fails
    sec = ccs.sections(out)
    for k, (lineno, ax, cond, base, name, fq) in enumerate(resolved):
        axioms, problems = ccs.parse_assumptions(sec.get("PA %d" % k, ""))
        for p in problems:
            fails.append((lineno, base, name, "parse", p))
        for rule, detail in verdict(ax, cond, axioms, allow):
            fails.append((lineno, base, name, rule, detail))
    return errs, fails


def selftest():
    allow = {"ClassicalDedekindReals.sig_not_dec",
             "ClassicalDedekindReals.sig_forall_dec",
             "FunctionalExtensionality.functional_extensionality_dep"}
    R = ["Stdlib.Reals.ClassicalDedekindReals.sig_not_dec"]
    cases = [
        ("3", False, R, []),
        ("3", False, [], []),                               # under-claim ok
        ("0", False, R, ["ax"]),
        ("C", False, [], ["ax"]),
        ("3", False, R + [CLASSIC], ["ax"]),
        ("4", False, R + [CLASSIC], []),
        ("3", False, R + ["NTS.Proofs.Foo.H"], ["unconditional", "ax"]),
        ("3", True, R + ["NTS.Proofs.Foo.H"], []),           # honest [cond]
        ("2", False, R * 3, ["ax"]),
        ("?", False, [], ["ax"]),
    ]
    bad = 0
    for ax, cond, axioms, want in cases:
        got = [r for r, _ in verdict(ax, cond, axioms, allow)]
        if got != want:
            bad += 1
            print("%s selftest FAIL: Ax %s cond %s %s -> %s, want %s"
                  % (TAG, ax, cond, axioms, got, want), file=sys.stderr)
    text = ("| `file : theorem` | Meaning | Ax |\n|---|---|---|\n"
            "| `A.v : x` (+`B.v : y_{1,2}`) | m `[cond]` | 3 |\n"
            "| `C.v : z` | a \\| b | C |\n"
            "| `E.v : e` | mixed `[exact/cond per entry]` | 0/3 |\n"
            "| `G.v : g` | m | Flocq C1 (`classic`) |\n\n"
            "| other | table |\n|---|---|\n| `D.v : w` | 3 |\n")
    rows = parse_rows(text)
    want = [(3, "3", True, [("A.v", "x"), ("B.v", "y_1"), ("B.v", "y_2")]),
            (4, "C", False, [("C.v", "z")]),
            (5, "3", True, [("E.v", "e")]),
            (6, "4", False, [("G.v", "g")])]
    if rows != want:
        bad += 1
        print("%s selftest FAIL: parse_rows -> %r" % (TAG, rows), file=sys.stderr)
    if locate_pick("Constant NTS.Proofs.Foo.M.x\nConstant NTS.Proofs.Bar.x",
                   "NTS.Proofs.Foo") != "NTS.Proofs.Foo.M.x":
        bad += 1
        print("%s selftest FAIL: locate_pick" % TAG, file=sys.stderr)
    if bad:
        return 2
    print("%s selftest ok" % TAG)
    return 0


def main(argv):
    rc = selftest()
    if rc or argv[:1] == ["--selftest"]:
        return rc
    with open(os.path.join(ROOT, LEDGER), encoding="utf-8") as fh:
        rows = parse_rows(fh.read())
    if argv[:1] == ["--list"]:
        for lineno, ax, cond, refs in rows:
            print("%d\t%s\t%s\t%s" % (lineno, ax, "cond" if cond else "-",
                                      ", ".join("%s : %s" % r for r in refs)))
        return 0
    allow = allowlist()
    errs, fails = run_all(rows, allow)
    for e in errs:
        print("%s ERROR %s" % (TAG, e), file=sys.stderr)
    for lineno, base, name, rule, detail in fails:
        print("%s FAIL %s:%d: `%s : %s` %s: %s"
              % (TAG, LEDGER, lineno, base, name, rule, detail))
    if errs:
        return 2
    if fails:
        return 1
    n = sum(len(r[3]) for r in rows)
    print("%s OK: %d rows, %d cited names hold their Ax / [cond] claim"
          % (TAG, len(rows), n))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
