#!/usr/bin/env python3
# =============================================================================
# scripts/check_hypothesis_ledger.py
# -----------------------------------------------------------------------------
# Hypothesis ledger: docs/hypothesis-ledger.tsv lists, per conditional
# theorem, each hypothesis that carries deferred content, and its status:
#
#   discharged  a Qed theorem proves it outright (evidence).
#   reduced     proved from other premises that are themselves open guards
#               (evidence = the reduction).
#   instance    proved for named instances only (evidence), not in general.
#   open        nothing proves or refutes it.
#   refuted     a Qed theorem proves it false (evidence). With scope
#               `universal` the headline is vacuous: nothing satisfies it.
#   circular    the hypothesis restates the conclusion.
#   placeholder the named Prop is defined as `True`: it holds trivially and
#               the content it names (in a comment) is not formalised.
#
# check_ledger_assumptions.py reads `Print Assumptions`, which never sees an
# inline premise (`H -> concl`). This check is the other half:
#
#   coverage    every `Mod.v : name` in the first cell of a conditional row
#               of docs/verified-claims.md (tagged `[cond]` or "cond per
#               entry", as check_ledger_assumptions.py reads it) has at least
#               one ledger line, unless declared in UNAUDITED below (a
#               shrinking list, now empty). A `name*` cite expands to every
#               definition with that prefix.
#   tag         a ledger theorem with any non-discharged hypothesis is cited
#               only in rows tagged `[cond]` (no `[exact]`-only row).
#   refuted     a theorem with a `refuted` hypothesis (any scope) is cited
#               only in rows that name the refuting theorem (the evidence's
#               bare name). A per-input refutation shrinks what the row
#               covers; a reader must be able to find the witness.
#   vacuous     a `universal` + `refuted` hypothesis also needs the word
#               "vacuous" in the row (nothing satisfies it); a `circular`
#               one needs "circular"; a `placeholder` one needs
#               "placeholder" (case-insensitive).
#   premise     a theorem cited in a NON-conditional row whose source
#               statement has premises (count_premises: top-level `->`,
#               open-Section Hypothesis/Context) needs ledger lines (a guard
#               is `discharged`), unless frozen in
#               docs/hypothesis-ledger-premise-baseline.txt (shrink-only:
#               an entry that is no longer debt fails). Textual detector;
#               limits listed at premise_count().
#   resolve     every theorem and evidence anchor names a definition in
#               theories/, theories-flocq/ or docs/h1-vacuity/.
#   fields      status, scope in vocabulary; evidence present where the
#               status needs it.
#
# Known limit: `discharged` / `reduced` / `refuted` trust the evidence
# anchor -- this script checks that it resolves, not that its statement
# matches the hypothesis.  That match is reviewed by hand.
#
# Static: no rocq needed. Kernel facts behind `refuted` evidence are
# compiled by the rocq jobs (product modules) and hunt_probe_smoke.sh.
#
# Usage: check_hypothesis_ledger.py [--summary | --selftest]
#   --summary   also print per-theorem and total status counts.
#   --selftest  row-rule checks on canned rows only (also run first always).
# Exit: 0 ok · 1 violation · 2 usage / IO error.
#
# License: BSD-3-Clause (see LICENSE)
# AI assistance disclosure: AI-drafted; human review pending.
# =============================================================================

import csv
import os
import re
import sys
from collections import Counter, OrderedDict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEDGER = os.path.join(ROOT, "docs", "hypothesis-ledger.tsv")
CLAIMS = os.path.join(ROOT, "docs", "verified-claims.md")
PREMISE_BASELINE = os.path.join(ROOT, "docs",
                                "hypothesis-ledger-premise-baseline.txt")
LANES = ("theories", "theories-flocq", os.path.join("docs", "h1-vacuity"))
TAG = "[hyp-ledger]"

STATUS = ("discharged", "reduced", "instance", "open", "refuted", "circular",
          "placeholder")
NEEDS_EVIDENCE = ("discharged", "reduced", "instance", "refuted")
SCOPE = ("universal", "per-input")
ANCHOR = re.compile(r"`?([A-Za-z0-9_]+\.v)\s*:\s*([A-Za-z0-9_']+)`?")
COND = re.compile(r"\[cond\]|\bcond per entry\b")  # as check_ledger_assumptions
DEF = r"^\s*(?:Local\s+|Global\s+)?(?:Theorem|Lemma|Corollary|Proposition|Fact|Remark|Definition|Fixpoint|Inductive|Record)\s+%s\b"

# [cond] ledger theorems not yet itemised. Shrink only (empty since the
# 2026-11 itemisation; a new [cond] row needs ledger lines, not an entry here).
UNAUDITED = set()

_src_cache = {}


def sources(base):
    out = []
    for lane in LANES:
        p = os.path.join(ROOT, lane, base)
        if os.path.isfile(p):
            if p not in _src_cache:
                with open(p, encoding="utf-8") as fh:
                    _src_cache[p] = fh.read()
            out.append(_src_cache[p])
    return out


def resolves(base, name):
    pat = re.compile(DEF % re.escape(name), re.M)
    return any(pat.search(t) for t in sources(base))


def prefixed(base, pre):
    """Names defined in `base` that start with `pre` (for `pre*` cites)."""
    pat = re.compile(DEF % (re.escape(pre) + r"[A-Za-z0-9_']*"), re.M)
    out = []
    for src in sources(base):
        for m in pat.finditer(src):
            n = re.search(r"\b(%s[A-Za-z0-9_']*)" % re.escape(pre),
                          m.group(0)).group(1)
            if n not in out:
                out.append(n)
    return out or [pre + "*"]


def key(base, name):
    return "%s : %s" % (base, name)


def read_ledger():
    with open(LEDGER, encoding="utf-8", newline="") as fh:
        rows = list(csv.DictReader(fh, delimiter="\t"))
    want = ["theorem", "hypothesis", "scope", "status", "evidence", "note"]
    if not rows or list(rows[0].keys()) != want:
        raise ValueError("header must be: " + "\t".join(want))
    return rows


def claim_rows():
    """-> [(lineno, line, cond, [Mod.v : name])] for table rows of the ledger
    whose first cell cites theorems."""
    out = []
    with open(CLAIMS, encoding="utf-8") as fh:
        for i, ln in enumerate(fh, 1):
            if not ln.startswith("| `") and not ln.startswith("| eval"):
                continue
            first = ln.split(" | ", 1)[0]
            refs = []
            for m in ANCHOR.finditer(first):
                if first[m.end(2):m.end(2) + 1] == "*":   # `Mod.v : pre_*`
                    refs += [key(m.group(1), n)
                             for n in prefixed(m.group(1), m.group(2))]
                else:
                    refs.append(key(m.group(1), m.group(2)))
            if refs:
                out.append((i, ln, bool(COND.search(ln)), refs))
    return out


def check(rows, claims):
    fails = []
    by_thm = OrderedDict()
    for n, r in enumerate(rows, 2):
        where = "%s:%d" % (os.path.relpath(LEDGER, ROOT), n)
        m = ANCHOR.fullmatch(r["theorem"].strip())
        if not m:
            fails.append((where, "fields", "theorem `%s` is not `Mod.v : name`"
                          % r["theorem"]))
            continue
        thm = key(m.group(1), m.group(2))
        by_thm.setdefault(thm, []).append(r)
        if not resolves(m.group(1), m.group(2)):
            fails.append((where, "resolve", "`%s` has no definition" % thm))
        if r["status"] not in STATUS:
            fails.append((where, "fields", "status `%s` not in %s"
                          % (r["status"], "|".join(STATUS))))
        if r["scope"] not in SCOPE:
            fails.append((where, "fields", "scope `%s` not in %s"
                          % (r["scope"], "|".join(SCOPE))))
        ev = r["evidence"].strip()
        if ev:
            e = ANCHOR.fullmatch(ev)
            if not e:
                fails.append((where, "fields", "evidence `%s` is not "
                              "`Mod.v : name`" % ev))
            elif not resolves(e.group(1), e.group(2)):
                fails.append((where, "resolve", "evidence `%s` has no "
                              "definition" % ev))
        elif r["status"] in NEEDS_EVIDENCE:
            fails.append((where, "fields", "status `%s` needs evidence"
                          % r["status"]))
    claims_path = os.path.relpath(CLAIMS, ROOT)
    for lineno, ln, cond, refs in claims:
        where = "%s:%d" % (claims_path, lineno)
        for ref in refs:
            hs = by_thm.get(ref)
            if cond and hs is None and ref not in UNAUDITED:
                fails.append((where, "coverage", "`%s` is in a [cond] row "
                              "but has no hypothesis-ledger line" % ref))
            if hs is None:
                continue
            for rule, detail in row_verdict(ln, cond, ref, hs):
                fails.append((where, rule, detail))
    stale = sorted(u for u in UNAUDITED if u in by_thm)
    for u in stale:
        fails.append((os.path.relpath(__file__, ROOT), "coverage",
                      "`%s` is itemised; delete it from UNAUDITED" % u))
    debt = premise_debt(claims, by_thm)
    base = read_baseline()
    bpath = os.path.relpath(PREMISE_BASELINE, ROOT)
    for ref, (lineno, k) in sorted(debt.items()):
        if ref not in base:
            fails.append(("%s:%d" % (claims_path, lineno), "premise",
                          "`%s` has %d premise(s) but its row is not "
                          "conditional and it has no ledger lines; ledger "
                          "them (a guard is `discharged`)" % (ref, k)))
    for ref in sorted(base - set(debt)):
        fails.append((bpath, "premise", "`%s` is no longer premise debt "
                      "(ledgered, conditional, premise-free or uncited); "
                      "delete it from the baseline" % ref))
    return fails, by_thm


def says(word, ln):
    """`word` in the row, not negated: "non-vacuous" / "not circular" /
    "no placeholder" do not count."""
    return re.search(r"(?<![\w-])(?<!non-)(?<!not )(?<!no )%s" % word, ln,
                     re.I) is not None


# --- premise detection (textual) -------------------------------------------
# Counts the premises of a cited theorem from its SOURCE statement: top-level
# `->` antecedents after `forall` binders (an `<->` is not one), binders
# before the colon that are not types of values are not counted, plus every
# Hypothesis / Hypotheses / Context declared in a Section still open at the
# theorem.  Known limits: a premise hidden inside a named Prop that is the
# CONCLUSION (e.g. `Theorem t : jordan_true_region_taut.`) is not seen;
# premises written as binders `(H : P)` before the colon are not counted;
# notations that expand to implications are not seen.  It flags candidates;
# `check_ledger_assumptions.py` remains the kernel-level check.

THM_DEF = (r"^\s*(?:Local\s+|Global\s+)?(?:Theorem|Lemma|Corollary|"
           r"Proposition|Fact|Remark|Example)\s+%s\b")


def strip_comments(s):
    out, depth, i = [], 0, 0
    while i < len(s):
        if s.startswith("(*", i):
            depth += 1
            i += 2
        elif depth and s.startswith("*)", i):
            depth -= 1
            i += 2
        else:
            if not depth:
                out.append(s[i])
            i += 1
    return "".join(out)


def split_arrows(s):
    parts, depth, cur, i = [], 0, "", 0
    while i < len(s):
        ch = s[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        if (depth == 0 and s.startswith("->", i)
                and not (i > 0 and s[i - 1] == "<")):
            parts.append(cur)
            cur = ""
            i += 2
            continue
        cur += ch
        i += 1
    parts.append(cur)
    return parts


def count_premises(stmt):
    s, n = stmt.strip(), 0
    while True:
        if re.match(r"forall\b", s):
            depth = 0
            for i, ch in enumerate(s):
                if ch in "([{":
                    depth += 1
                elif ch in ")]}":
                    depth -= 1
                elif ch == "," and depth == 0:
                    s = s[i + 1:].strip()
                    break
            else:
                return n
            continue
        parts = split_arrows(s)
        if len(parts) == 1:
            return n
        n += len(parts) - 1
        s = parts[-1].strip()


_strip_cache = {}


def premise_count(base, name):
    """Premises of `base : name` read from source, or None (not a theorem
    in this tree, e.g. a Definition)."""
    for lane in LANES:
        path = os.path.join(ROOT, lane, base)
        if not os.path.isfile(path):
            continue
        if path not in _strip_cache:
            with open(path, encoding="utf-8") as fh:
                _strip_cache[path] = strip_comments(fh.read())
        src = _strip_cache[path]
        m = re.search(THM_DEF % re.escape(name), src, re.M)
        if not m:
            continue
        rest = src[m.end():]
        cut = [x for x in (rest.find("Proof."), rest.find(":=")) if x >= 0]
        stmt = rest[:min(cut)] if cut else rest
        depth, colon = 0, None
        for i, ch in enumerate(stmt):
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
            elif ch == ":" and depth == 0 and not stmt.startswith(":=", i):
                colon = i
                break
        body = stmt[colon + 1:] if colon is not None else stmt
        n = count_premises(body.rstrip().rstrip("."))
        stack = []
        for mm in re.finditer(r"^\s*(?:Section\s+(\w+)|End\s+(\w+)|"
                              r"(Hypothesis|Hypotheses|Context)\b[^.]*)\.",
                              src[:m.start()], re.M):
            if mm.group(1):
                stack.append([mm.group(1), 0])
            elif mm.group(2):
                if stack and stack[-1][0] == mm.group(2):
                    stack.pop()
            elif mm.group(3) and stack:
                stack[-1][1] += 1
        return n + sum(h for _, h in stack)
    return None


def read_baseline():
    out = set()
    if os.path.isfile(PREMISE_BASELINE):
        with open(PREMISE_BASELINE, encoding="utf-8") as fh:
            for ln in fh:
                ln = ln.split("#", 1)[0].strip()
                if ln:
                    out.add(ln)
    return out


def premise_debt(claims, by_thm):
    """Theorems cited in non-conditional rows, with premises, without
    ledger lines -> {ref: (lineno, count)}."""
    out = {}
    for lineno, ln, cond, refs in claims:
        if cond:
            continue
        for ref in refs:
            if ref in by_thm or ref in out:
                continue
            base, name = ref.split(" : ")
            k = premise_count(base, name)
            if k:
                out[ref] = (lineno, k)
    return out


def row_verdict(ln, cond, ref, hs):
    """Rules for one claims row `ln` citing theorem `ref`, whose ledger
    lines are `hs`. -> [(rule, detail)]."""
    out = []
    if not cond and any(h["status"] != "discharged" for h in hs):
        out.append(("tag", "`%s` has open/reduced/refuted hypotheses but "
                    "the row is not [cond]" % ref))
    for h in hs:
        what = "`%s` (`%s`)" % (ref, h["hypothesis"][:60])
        if h["status"] == "refuted":
            e = ANCHOR.fullmatch(h["evidence"].strip())
            name = e.group(2) if e else h["evidence"].strip()
            if not re.search(r"(?<![\w'])%s(?![\w'])" % re.escape(name), ln):
                out.append(("refuted", "%s is refuted by `%s`; the row must "
                            "cite it" % (what, name)))
            if h["scope"] == "universal" and not says("vacuous", ln):
                out.append(("vacuous", "%s is refuted for every input; the "
                            "row must say \"vacuous\"" % what))
        elif h["status"] == "circular" and not says("circular", ln):
            out.append(("vacuous", "%s restates the conclusion; the row "
                        "must say \"circular\"" % what))
        elif h["status"] == "placeholder" and not says("placeholder", ln):
            out.append(("placeholder", "%s is defined as True; the row must "
                        "say \"placeholder\"" % what))
    return out


def selftest():
    hs = lambda st, sc, ev="": [{"hypothesis": "H", "status": st,
                                 "scope": sc, "evidence": ev}]
    ev = "Q.v : h_refuted"
    cases = [
        ("| x `[cond]` |", True, hs("open", "per-input"), []),
        ("| x `[exact]` |", False, hs("open", "per-input"), ["tag"]),
        ("| x `[exact]` |", False, hs("discharged", "per-input", ev), []),
        ("| x `[cond]` |", True, hs("refuted", "per-input", ev), ["refuted"]),
        ("| x `Q.v : h_refuted` `[cond]` |", True,
         hs("refuted", "per-input", ev), []),
        ("| x h_refuted_more `[cond]` |", True,
         hs("refuted", "per-input", ev), ["refuted"]),
        ("| x h_refuted `[cond]` |", True,
         hs("refuted", "universal", ev), ["vacuous"]),
        ("| VACUOUS x h_refuted `[cond]` |", True,
         hs("refuted", "universal", ev), []),
        ("| x `[cond]` |", True, hs("circular", "universal"), ["vacuous"]),
        ("| CIRCULAR x `[cond]` |", True, hs("circular", "universal"), []),
        ("| x `[cond]` |", True, hs("placeholder", "universal"),
         ["placeholder"]),
        ("| x (placeholder) `[cond]` |", True, hs("placeholder", "universal"),
         []),
    ]
    cases += [
        ("| non-vacuous x h_refuted `[cond]` |", True,
         hs("refuted", "universal", ev), ["vacuous"]),
        ("| not circular `[cond]` |", True, hs("circular", "universal"),
         ["vacuous"]),
    ]
    bad = 0
    for stmt, want in [
            ("forall a b, P a -> Q b -> R", 2),
            ("forall (f : R -> R) x, f x = 0", 0),
            ("forall a, P a <-> Q a", 0),
            ("forall a, (P a -> Q a) -> forall b, S b -> T", 2),
            ("A -> B -> C", 2)]:
        if count_premises(stmt) != want:
            bad += 1
            print("%s selftest FAIL: count_premises(%r) != %d"
                  % (TAG, stmt, want), file=sys.stderr)
    for ln, cond, h, want in cases:
        got = [r for r, _ in row_verdict(ln, cond, "T.v : t", h)]
        if got != want:
            bad += 1
            print("%s selftest FAIL: %r -> %s, want %s" % (TAG, ln, got, want),
                  file=sys.stderr)
    if bad:
        return 2
    print("%s selftest ok (%d cases)" % (TAG, len(cases) + 5))
    return 0


def summary(by_thm):
    tot = Counter()
    for thm, hs in by_thm.items():
        c = Counter(h["status"] for h in hs)
        tot.update(c)
        print("%s %-70s %s" % (TAG, thm, " ".join(
            "%s=%d" % (s, c[s]) for s in STATUS if c[s])))
    print("%s TOTAL %d theorems, %d hypotheses: %s; unaudited theorems: %d"
          % (TAG, len(by_thm), sum(tot.values()),
             ", ".join("%s %d" % (s, tot[s]) for s in STATUS),
             len(UNAUDITED)))


def main(argv):
    rc = selftest()
    if rc or "--selftest" in argv:
        return rc
    try:
        rows = read_ledger()
        claims = claim_rows()
    except (OSError, ValueError) as exc:
        print("%s ERROR %s" % (TAG, exc), file=sys.stderr)
        return 2
    fails, by_thm = check(rows, claims)
    if "--summary" in argv:
        summary(by_thm)
    for where, rule, detail in fails:
        print("%s FAIL %s: %s: %s" % (TAG, where, rule, detail))
    if fails:
        return 1
    print("%s OK: %d hypotheses over %d theorems; every [cond] row covered "
          "or listed unaudited (%d)" % (TAG, len(rows), len(by_thm),
                                        len(UNAUDITED)))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
