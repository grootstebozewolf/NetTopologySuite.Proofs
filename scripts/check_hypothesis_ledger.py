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
#
# check_ledger_assumptions.py reads `Print Assumptions`, which never sees an
# inline premise (`H -> concl`). This check is the other half:
#
#   coverage    every `Mod.v : name` in the first cell of a `[cond]` row of
#               docs/verified-claims.md has at least one ledger line, unless
#               declared in UNAUDITED below (a shrinking list).
#   tag         a ledger theorem with any non-discharged hypothesis is cited
#               only in rows tagged `[cond]` (no `[exact]`-only row).
#   vacuous     a theorem with a `universal` + `refuted` or a `circular`
#               hypothesis is cited only in rows that say "vacuous" or
#               "circular" (case-insensitive).
#   resolve     every theorem and evidence anchor names a definition in
#               theories/, theories-flocq/ or docs/h1-vacuity/.
#   fields      status, scope in vocabulary; evidence present where the
#               status needs it.
#
# Static: no rocq needed. Kernel facts behind `refuted` evidence are
# compiled by the rocq jobs (product modules) and hunt_probe_smoke.sh.
#
# Usage: check_hypothesis_ledger.py [--summary]
#   --summary   also print per-theorem and total status counts.
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
LANES = ("theories", "theories-flocq", os.path.join("docs", "h1-vacuity"))
TAG = "[hyp-ledger]"

STATUS = ("discharged", "reduced", "instance", "open", "refuted", "circular")
NEEDS_EVIDENCE = ("discharged", "reduced", "instance", "refuted")
SCOPE = ("universal", "per-input")
ANCHOR = re.compile(r"`?([A-Za-z0-9_]+\.v)\s*:\s*([A-Za-z0-9_']+)`?")
COND = re.compile(r"\[cond\]")
DEF = r"^\s*(?:Local\s+|Global\s+)?(?:Theorem|Lemma|Corollary|Proposition|Fact|Remark|Definition|Fixpoint|Inductive|Record)\s+%s\b"

# [cond] ledger theorems not yet itemised. Shrink only.
UNAUDITED = {
    "DelaunayEmptyCircle.v : in_circle_test_iff_b64_inCircle_exact_pos",
    "OverlayBridgeUnconditional.v : extract_rings_valid_holes_of_guards",
    "TriangleContainmentConvex.v : gtri_region_is_convex",
    "TriangleContainmentConvex.v : gtri_region_contains_segment",
    "CurveLineariseGuardBridge.v : to_geometry_result_valid_of_guards",
    "RelateNGContains.v : triangle_pair_regime_contains",
    "RelateNGContains.v : contains_b_ring_inside",
    "ArcArcCirclesSpan.v : arc_arc_intersects_of_circles_and_span",
    "RelateCurveMatrix.v : geom_de9im_ii_cell_dim2_sound",
    "ArcControlTriangleInSegment.v : arc_control_triangle_in_circular_segment",
    "BufferAssembly.v : assemble_open_miter_chain",
    "BufferAssembly.v : assemble_closed_miter_closed",
    "BufferEndcap.v : flat_cap_ring_closed",
    "RingCurvatureModels.v : extract_rings_valid_hyperbolic_of_guards",
    "RingCurvatureModels.v : extract_rings_valid_spherical_hemisphere_of_guards",
    "DelaunayFlipWitness.v : inCircle_R_double_swap",
    "DelaunayFlipWitness.v : inCircle_R_flip_witness_iff",
    "DelaunayFlipWitness.v : inCircle_R_flip_witness",
    "TriangleContainmentConvex.v : gtri_region_strict_is_convex",
    "TriangleContainmentConvex.v : gtri_region_strict_contains_segment",
    "RelateNGContains.v : contains_b_ring_strictly_inside",
    "CurveLineariseGuardBridge.v : to_geometry_result_valid_holes_of_guards",
    "BufferAssembly.v : two_sided_walk_closed",
    "Orient_b64_stage_d_cc.v : b64_orient_sign_stage_d_cc_sound",
    "Shewchuk_vs_Z2.v : shewchuk_stage_d_cc_agrees_with_exact_intdet",
    "Orient_b64_stage_d.v : b64_orient_sign_exact_sound",
    "Orient_b64_expansion.v : b64_orient2d_expansion_nonoverlap",
    "Shewchuk_vs_Z2.v : shewchuk_vs_z2_tiny_headline",
    "Shewchuk_vs_Z2.v : shewchuk_vs_z2_tiny_headline_cc",
    "Shewchuk_vs_Z2.v : orient2d_exact_cc_agrees_with_exact_intdet_cc",
}

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
            refs = [key(m.group(1), m.group(2)) for m in ANCHOR.finditer(first)]
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
            if not cond and any(h["status"] != "discharged" for h in hs):
                fails.append((where, "tag", "`%s` has open/reduced/refuted "
                              "hypotheses but the row is not [cond]" % ref))
            vac = [h for h in hs if h["status"] == "circular" or
                   (h["status"] == "refuted" and h["scope"] == "universal")]
            if vac and not re.search(r"vacuous|circular", ln, re.I):
                fails.append((where, "vacuous", "`%s` rests on a %s "
                              "hypothesis (`%s`); the row must say so"
                              % (ref, vac[0]["status"],
                                 vac[0]["hypothesis"][:60])))
    stale = sorted(u for u in UNAUDITED if u in by_thm)
    for u in stale:
        fails.append((os.path.relpath(__file__, ROOT), "coverage",
                      "`%s` is itemised; delete it from UNAUDITED" % u))
    return fails, by_thm


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
