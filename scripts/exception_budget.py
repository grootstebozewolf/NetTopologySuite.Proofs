#!/usr/bin/env python3
# =============================================================================
# scripts/exception_budget.py
# -----------------------------------------------------------------------------
# The Observatory's exception budget: every registered exception, classified.
# The objective is not zero exceptions but zero UNEXPLAINED exceptions.
#
# Sources (each entry is one exception):
#   docs/audit-exceptions.txt          files allowed axioms beyond the
#                                      allowlist; class from the nearest
#                                      `# class: <name>` tag above the entry
#   docs/oracle-handrolled-allowlist.txt  frozen hand-rolled kernels
#                                      -> implementation
#   docs/admitted-deferred-proofs.txt  deferred Admitted -> debt
#   docs/admitted-counterexamples.txt  Admitted verified counterexamples -> qex
#
# Classes:
#   debt            avoidable; target 0
#   implementation  inherited from the implementation model (Flocq binary64,
#                   interface kernels); minimize
#   library         inherited from the Stdlib real-analysis library; explicit
#   qex             the stronger claim is false; preserve
#   unclassified    untagged audit exception; must be 0
#
# Usage:
#   python3 scripts/exception_budget.py          print the budget
#   python3 scripts/exception_budget.py --check  also exit 1 on an untagged
#                                                entry or an unknown class
#
# License: BSD-3-Clause (see LICENSE)
# AI assistance disclosure: AI-drafted; human review pending.
# =============================================================================

import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

CLASSES = ("debt", "implementation", "library", "qex")
LABELS = {
    "debt": "Proof debt",
    "implementation": "Implementation boundary",
    "library": "Library boundary",
    "qex": "QEX boundary",
    "unclassified": "Unclassified",
}
TARGETS = {
    "debt": "0",
    "implementation": "minimize",
    "library": "explicit",
    "qex": "preserve",
    "unclassified": "0",
}

AUDIT = "docs/audit-exceptions.txt"
FIXED = (
    ("docs/oracle-handrolled-allowlist.txt", "implementation"),
    ("docs/admitted-deferred-proofs.txt", "debt"),
    ("docs/admitted-counterexamples.txt", "qex"),
)
TAG = re.compile(r"^#\s*class:\s*(\S+)\s*$")


def _lines(rel):
    path = os.path.join(ROOT, rel)
    if not os.path.exists(path):
        return None
    with open(path, encoding="utf-8") as fh:
        return fh.read().splitlines()


def _entries(lines):
    return [ln.strip() for ln in lines
            if ln.strip() and not ln.lstrip().startswith("#")]


def budget():
    """Return (counts, problems): counts per class (plus 'unclassified' and
    'total'), problems a list of human-readable violations."""
    counts = {c: 0 for c in CLASSES}
    counts["unclassified"] = 0
    problems = []

    lines = _lines(AUDIT)
    if lines is None:
        problems.append(f"{AUDIT} not found")
        lines = []
    current = None
    for n, ln in enumerate(lines, 1):
        s = ln.strip()
        m = TAG.match(s)
        if m:
            current = m.group(1)
            if current not in CLASSES:
                problems.append(f"{AUDIT}:{n}: unknown class '{current}' "
                                f"(one of: {', '.join(CLASSES)})")
            continue
        if not s or s.startswith("#"):
            continue
        if current in CLASSES:
            counts[current] += 1
        else:
            counts["unclassified"] += 1
            problems.append(f"{AUDIT}:{n}: {s} has no `# class:` tag above it")

    for rel, cls in FIXED:
        fl = _lines(rel)
        if fl is None:
            problems.append(f"{rel} not found")
            continue
        counts[cls] += len(_entries(fl))

    counts["total"] = sum(counts[c] for c in CLASSES) + counts["unclassified"]
    return counts, problems


def accounted_pct(counts):
    total = counts["total"]
    if total == 0:
        return 100
    return round(100 * (total - counts["unclassified"]) / total)


def main(argv):
    check = "--check" in argv
    counts, problems = budget()
    print(f"EXCEPTION BUDGET  {counts['total']} total")
    for c in CLASSES + ("unclassified",):
        print(f"  {LABELS[c]:<26}{counts[c]:>5}   target {TARGETS[c]}")
    print(f"  {'Accounted for':<26}{accounted_pct(counts):>4}%   target 100%")
    for p in problems:
        print(f"[exception-budget] {p}", file=sys.stderr)
    if check and problems:
        print("[exception-budget] FAIL: every exception needs a class "
              "(see the header of docs/audit-exceptions.txt).", file=sys.stderr)
        return 1
    if check:
        print("[exception-budget] OK: every exception is classified.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
