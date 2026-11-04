#!/usr/bin/env python3
# =============================================================================
# scripts/gen_dashboard.py
# -----------------------------------------------------------------------------
# Generate dashboard/index.html — the in-repo "observatory" for the Proofs
# corpus.  It reports ONLY on data that exists in this repository:
#
#   - docs/verified-claims.md   (citable theorem index + regime tags)
#   - TRIAGE_NTS_JTS_ISSUES.md  (per-issue #64-#69 status table)
#   - oracle/*_vectors.txt, *_tests.txt  (differential test vectors)
#   - docs/admitted-*.txt, axiom-allowlist.txt, oracle-handrolled-allowlist.txt
#
# It is deliberately NOT a JTS/NTS test runner.  This corpus is the *oracle /
# reference* (the cross-project differential harness lives downstream in
# NetTopologySuite.Curve); the dashboard deep-links out to JTS/NTS rather than
# pretending to execute them.  The page preserves the corpus's honest
# proven / conditional / deferred distinctions — no flattened "all green".
#
# Self-contained: emits one HTML file with inline CSS, no network/CDN deps,
# no build step.  Re-run on every push via .github/workflows/pages.yml.
#
# Usage:  python3 scripts/gen_dashboard.py            # writes dashboard/index.html
#         python3 scripts/gen_dashboard.py --check    # fail if regenerated HTML differs
#         python3 scripts/gen_dashboard.py --check-freshness [--strict]
#                 # warn (fail with --strict) when the commit shown in the committed
#                 # dashboard is behind HEAD for the dashboard's INPUT paths
#
# License: BSD-3-Clause (see LICENSE)
# AI assistance disclosure: AI-drafted, human-reviewed.  Assisted-by: Claude
# =============================================================================

import os, re, sys, html, json, subprocess
from datetime import datetime, timezone

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "dashboard", "index.html")

REGIMES = ["exact", "full-b64", "int-b64", "int-b64-arc", "int", "b64-rne",
           "structural", "cond", "oracle"]
def regime_hits(text, regime):
    """Occurrences of [regime] in a claims-table line."""
    return len(re.findall(r"\[" + re.escape(regime) + r"\]", text))
REGIME_LABEL = {
    "exact": "exact reals",
    "full-b64": "all finite binary64",
    "int-b64": "int-coord binary64",
    "int-b64-arc": "int-coord binary64 (arc)",
    "int": "exact integer (0 axioms)",
    "b64-rne": "binary64 RNE, stated intake and budget",
    "structural": "structure / guard (no numeric claim)",
    "cond": "conditional (named hyps)",
    "oracle": "extracted / differential",
}
# proven (unconditional soundness) vs conditional vs oracle-only vs structural.
# Rule separating proven from conditional for binary64 rows: a regime is "proven"
# when every hypothesis is on the INPUTS and is checked by the evaluator's own
# intake predicate or an explicit argument bound (b64-rne: sin_accept,
# fresnel_accept, cm_accept, |z| <= Z); it is "conditional" when the hypotheses are
# premises on intermediate values that the caller must discharge (round-chain's
# b64_safe).  "structural" rows (a guard or shape lemma with no numeric content)
# are counted and shown but are NOT in the headline proven total.
REGIME_KIND = {
    "exact": "proven", "full-b64": "proven", "int-b64": "proven",
    "int-b64-arc": "proven", "int": "proven", "b64-rne": "proven",
    "structural": "structural", "cond": "conditional", "oracle": "oracle",
}
REGIME_COLOR = {
    "exact": "#16a34a", "full-b64": "#15803d", "int-b64": "#65a30d",
    "int-b64-arc": "#84cc16", "int": "#0891b2", "b64-rne": "#a3e635",
    "structural": "#64748b", "cond": "#d97706", "oracle": "#2563eb",
}


def read(path):
    p = os.path.join(ROOT, path)
    if not os.path.exists(p):
        return None
    with open(p, encoding="utf-8") as f:
        return f.read()


def git(*args, default=""):
    try:
        return subprocess.check_output(["git", "-C", ROOT, *args],
                                       stderr=subprocess.DEVNULL).decode().strip()
    except Exception:
        return default


# -- verified-claims.md ------------------------------------------------------

PROVEN_REGIMES = {"exact", "full-b64", "int-b64", "int-b64-arc", "int", "b64-rne"}


def parse_claims():
    txt = read("docs/verified-claims.md") or ""
    theorem_lines = [ln for ln in txt.splitlines()
                     if re.match(r'^\| `[^`]+ : ', ln)]
    total = len(theorem_lines)
    # count regime tags only in actual theorem rows, not headers/legends
    regime_counts = {r: sum(regime_hits(ln, r) for ln in theorem_lines)
                     for r in REGIMES}
    # per-section row + regime breakdown; all Issue #67 sections are merged
    def _is_67(title):
        return (re.search(r'Issue #67', title) or
                re.search(r'integer-coordinate substrate.*#67', title))

    # coverage_cells[feat_tag][geom_tag] = {"proven": int, "cond": int, "oracle": int}
    coverage_cells = {f: {g: {"proven": 0, "cond": 0, "oracle": 0}
                          for g in COVERAGE_GEOM_TAGS}
                      for f in COVERAGE_FEAT_TAGS}

    sections = []
    group67 = {"title": "Issue #67 — RelateNG / DE-9IM (all sessions)",
               "rows": 0, "regimes": {r: 0 for r in REGIMES}, "group": True}
    cur = None
    cur_feats = []
    cur_geoms = []
    for line in txt.splitlines():
        m = re.match(r'^## (.+)$', line)
        if m:
            raw = m.group(1).strip()
            # strip trailing HTML comment to get display title
            title = re.sub(r'\s*<!--[\s\S]*?-->', '', raw).strip()
            # parse feat/geom tags from the comment
            feat_m = re.search(r'feat:([\w,\-]+)', raw)
            geom_m = re.search(r'geom:([\w,]+)', raw)
            cur_feats = feat_m.group(1).split(',') if feat_m else []
            cur_geoms = geom_m.group(1).split(',') if geom_m else []
            if _is_67(title):
                cur = group67
                if group67 not in sections:
                    sections.append(group67)
            else:
                cur = {"title": title, "rows": 0,
                       "regimes": {r: 0 for r in REGIMES}}
                sections.append(cur)
        elif cur is not None and re.match(r'^\| `[^`]+ : ', line):
            cur["rows"] += 1
            for r in REGIMES:
                cur["regimes"][r] += regime_hits(line, r)
            # accumulate coverage matrix counts
            if cur_feats and cur_geoms:
                row_proven = sum(regime_hits(line, r) for r in PROVEN_REGIMES)
                row_cond   = regime_hits(line, "cond")
                row_oracle = len(re.findall(r'\[oracle\]', line))
                for ftag in cur_feats:
                    if ftag in coverage_cells:
                        for gtag in cur_geoms:
                            if gtag in coverage_cells[ftag]:
                                coverage_cells[ftag][gtag]["proven"] += row_proven
                                coverage_cells[ftag][gtag]["cond"]   += row_cond
                                coverage_cells[ftag][gtag]["oracle"]  += row_oracle
    sections = [s for s in sections if s["rows"] > 0]
    return total, regime_counts, sections, coverage_cells


# -- TRIAGE issue table ------------------------------------------------------

def parse_issues():
    txt = read("TRIAGE_NTS_JTS_ISSUES.md") or ""
    issues = []
    for line in txt.splitlines():
        if re.match(r'^\| \*\*#6[4-9]\*\*', line):
            cells = [c.strip() for c in line.split("|")]
            # cells: ['', '**#64**', 'Area', '`Priority`', 'proof-state', 'Verdict', '']
            num = re.sub(r'[*#]', '', cells[1])
            area = cells[2]
            priority = cells[3].strip("`")
            verdict = cells[-2]
            issues.append({"num": num, "area": area,
                           "priority": priority, "verdict": verdict})
    return issues


# -- oracle modes ------------------------------------------------------------

def _parse_coverage_tag(path):
    """Return list of (feat, geom) pairs from a '# coverage: feat:X geom:Y,Z' line."""
    pairs = []
    try:
        with open(path, encoding="utf-8") as f:
            for i, ln in enumerate(f):
                if i > 10:
                    break
                m = re.search(r'coverage:\s*feat:([\w,\-]+)\s+geom:([\w,]+)', ln)
                if m:
                    for ft in m.group(1).split(","):
                        for gt in m.group(2).split(","):
                            pairs.append((ft.strip(), gt.strip()))
    except OSError:
        pass
    return pairs


def parse_oracle():
    odir = os.path.join(ROOT, "oracle")
    modes = []
    if os.path.isdir(odir):
        for fn in sorted(os.listdir(odir)):
            fpath = os.path.join(odir, fn)
            if fn.endswith("_vectors.txt"):
                kind, name = "vectors", fn[:-len("_vectors.txt")]
                with open(fpath, encoding="utf-8") as f:
                    n = sum(1 for ln in f
                            if ln.strip() and not ln.lstrip().startswith("#"))
            elif fn.endswith("_tests.txt"):
                kind, name = "tests", fn[:-len("_tests.txt")]
                with open(fpath, encoding="utf-8") as f:
                    n = sum(1 for ln in f
                            if ln.strip() and not ln.lstrip().startswith("#"))
            elif fn.startswith("red_") and fn.endswith("_tests.py"):
                kind, name = "red-tests", fn[:-len("_tests.py")]
                with open(fpath, encoding="utf-8") as f:
                    # two styles: `x = run(...)` cases, or assert_eq/assert_true calls
                    n = sum(1 for ln in f
                            if "= run(" in ln
                            or re.match(r"\s*(assert_eq|assert_true)\(", ln))
            else:
                continue
            coverage_tags = _parse_coverage_tag(fpath)
            modes.append({"name": name, "kind": kind, "count": n,
                          "file": fn, "coverage_tags": coverage_tags})
    return modes


# -- registries (count non-comment, non-blank entries) -----------------------

def count_entries(path):
    txt = read(path)
    if txt is None:
        return None
    return sum(1 for ln in txt.splitlines()
               if ln.strip() and not ln.lstrip().startswith("#"))


# ---------------------------------------------------------------------------
# HTML rendering
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# Coverage matrix — which NTS features are proven for which geometry types
# ---------------------------------------------------------------------------
# Levels: "full"=Qed theorems, "partial"=some/conditional coverage, "none"=no coverage
# Short tag keys used in verified-claims.md section comments.
# COVERAGE_FEAT_TAGS / COVERAGE_GEOM_TAGS define the canonical order.
COVERAGE_FEAT_TAGS = ["distance", "arc-len", "area", "relate", "overlay", "buffer",
                      "join", "metric"]
COVERAGE_GEOM_TAGS = ["arc", "cs", "cc", "cp", "multi"]
# Tags that classify a section without earning a matrix row/column.  `ls`/`poly`/
# `pt` are the LINEAR subjects: recorded so a section is classified, deliberately
# absent from a matrix whose columns are curve types.  See the "Coverage tags"
# block in docs/verified-claims.md, which is the documented vocabulary; check 5
# in _check_grounding enforces that nothing outside these sets appears.
# `valid` (validity / simplicity) is a strong candidate for a matrix ROW rather
# than a bare classifier -- CircularStringValid.v, RingContactSound.v's
# ring_not_simple_* family, RelateCurveArcSegment.v : valid_arc_seg_curve_ring and
# CurveRingOffset.v : curve_ring_offset_valid all populate it across arc/cs/cc.
# Left as a classifier here because growing the published table is the
# maintainer's call, not a side effect of registering a tag.
NON_MATRIX_FEAT_TAGS = {"curves", "foundations", "teaching", "valid"}
NON_MATRIX_GEOM_TAGS = {"ls", "poly", "pt"}
KNOWN_FEAT_TAGS = set(COVERAGE_FEAT_TAGS) | NON_MATRIX_FEAT_TAGS
KNOWN_GEOM_TAGS = set(COVERAGE_GEOM_TAGS) | NON_MATRIX_GEOM_TAGS

COVERAGE_FEAT_LABEL = {
    "distance": "Distance",
    "arc-len":  "Arc / chord length",
    "area":     "Area / perimeter",
    "relate":   "Relate (DE-9IM)",
    "overlay":  "Intersection / Overlay",
    "buffer":   "Buffer",
    "join":     "Join continuity (C¹ / C²)",
    "metric":   "LEC / MIC",
}
COVERAGE_GEOM_LABEL = {
    "arc": "Arc", "cs": "CS", "cc": "CC", "cp": "CP", "multi": "Multi",
}
# Keep display names for backward compat (COVERAGE_MATRIX tooltip lookup)
COVERAGE_FEATURES  = [COVERAGE_FEAT_LABEL[t] for t in COVERAGE_FEAT_TAGS]
COVERAGE_GEOMTYPES = [COVERAGE_GEOM_LABEL[t] for t in COVERAGE_GEOM_TAGS]
# Abbreviations are shared with the grootstebozewolf/jts fork; the initials always
# match the type (CS starts "Circular", CC starts "Compound").  See CONTEXT.md
# "Curve types".  A previous revision had CS=CompoundCurve and CC=CurveCollection —
# the latter is a type no engine has (zero classes in JTS, GEOS and NTS), and it
# was squatting on the abbreviation CompoundCurve needs.  Substrate note: in
# theories/CurveGeometry.v a `CurveRing` (list of CSChord|CSArc) *is* a
# CompoundCurve; an all-CSArc ring is a CircularString.  There is no separate
# Rocq type for either, and none at all for a "CurveCollection".
COVERAGE_GEOMTYPE_LONG = {
    "Arc": "CircularArc (primitive — not a geometry type)",
    "CS": "CircularString",
    "CC": "CompoundCurve",
    "CP": "CurvePolygon",
    "Multi": "MultiCurve / MultiSurface",
}
# Source-of-record note for each cell.  Only element [1] is read (the icon comes
# from live theorem/oracle counts via _coverage_level), so element [0] is kept
# purely as the audited verdict for a human reading this file.
#
# Notes rewritten 2026-08-22 from a corpus audit, after the CS/CC relabel.  Slice
# numbers were dropped throughout: they contradict each other across plan.md and
# the oracle files (Area is "Slice 6" in one and "Slice 7" in the other; arc-len
# is "Slice 9" vs "Slice 11").
#
# CITE BY NAME, NEVER BY LINE.  A `File.v : theorem_name` reference survives a
# refactor and validate-claims.sh verifies the name against source; a
# `File.v:123` hook rots the moment anything above it moves, and nothing
# recompiles prose.  Check 4 in _check_grounding fails the build on any such
# hook in these notes -- the same stance validate-claims.sh takes on the doc,
# where a prose `File.v:123` is read as a claim citing a theorem named "123".
COVERAGE_MATRIX = {
    "Distance": {
        "Arc":   ("qed",      "Qed: ArcPointDistance.v : point_to_arc_dist_radial_lower, point_to_arc_attains_radial; closed form LECArcRow.v : arc_dist_exact; pairwise ArcArcDistance.v : arc_arc_dist_external + ArcSegmentDistance.v"),
        "CS":    ("none",     "No Rocq theorem for a multi-arc run. LECFlattenRow.v : obstacle_list_flatten_exact (Qed) is a min-fold over an UNORDERED member union (runion_list) — collection semantics, not a head-to-tail run, and point-to-region clearance rather than geometry-to-geometry distance. Oracle DISTANCE_UNIFIED has no head-to-tail multi-arc vector: its only two-arc case in red_distance_unified_tests.py is two DISCONNECTED arcs"),
        "CC":    ("oracle",   "Oracle vectors only: DISTANCE_UNIFIED red_distance_unified_tests.py (chord then arc, head-to-tail), (chord, chord, arc). No Rocq distance theorem over a CurveRing"),
        "CP":    ("oracle",   "Oracle DISTANCE_UNIFIED + TestCurvePolygon_Distance_MultiCurve; core arc distance proven but composite dispatch not Qed"),
        "Multi": ("oracle",   "Member recursion / min-fold — where the retired CurveCollection cell's content belongs: docs/arc-offset-red-test-example.cs recurses exactly like the Multi* branches. Oracle DISTANCE_UNIFIED; no Qed composite"),
    },
    "Arc / chord length": {
        "Arc":   ("qed",      "Qed: ArcLength.v : chord_le_arc_length, chord_subtended_sq; ArcChordLength.v : arc_chord_le_arc_length, arc_chord_dist_sq_via_sweep; subdivision budget ArcChordSubdivision.v : equal_angle_chords_achieve_eps"),
        "CS":    ("none",     "NO CONCATENATION EXISTS — neither a Rocq summation lemma over consecutive arc lengths nor an oracle vector containing two arcs (red_length_unified_tests.py holds two 'A' lines in total and never two in one vector). The corpus's only additive-over-concatenation lemma is RingOrientation.v signed_area2_app, which is linear-only and arc-blind. A previous revision of this cell claimed 'concatenation proven'; it was unearned"),
        "CC":    ("oracle",   "Oracle vectors only: LENGTH_UNIFIED red_length_unified_tests.py, whose own comment reads 'Mixed chord + arc (simulates CompoundCurve / CC segments)' — chord (0,0)-(1,0) then arc (1,0) to (0,1), head-to-tail. No Rocq theorem"),
        "CP":    ("oracle",   "Oracle LENGTH_UNIFIED / ARC_LEN_UNIFIED: perimeter via rings. No Rocq perimeter aggregate exists over any curve structure"),
        "Multi": ("oracle",   "Oracle LENGTH_UNIFIED / ARC_LEN_UNIFIED: recursion + segment length sum; red_length_unified_tests.py"),
    },
    "Area / perimeter": {
        "Arc":   ("qed",      "Qed: ArcArea.v : segment_area_sector_minus_triangle, segment_area_nonneg, segment_area_half_disc, segment_area_full_disc; centroid ArcAreaCentroid.v; CurveBufferArea.v : buffer_arc_area_grows"),
        "CS":    ("none",     "No area or perimeter fold over a CurveRing exists anywhere in the corpus. AREA_UNIFIED does sum a per-segment sector contribution (driver.ml) but no vector has two arcs — red_area_unified_tests.py is one arc plus its closing chord"),
        "CC":    ("oracle",   "Oracle vectors only: AREA_UNIFIED red_area_unified_tests.py (arc + chord closed ring), ('CC-like multi seg (compound)'), (chord, arc, chord, chord). No Rocq theorem"),
        "CP":    ("oracle",   "Triangle polygon area + AREA_UNIFIED. Note CurvePolygonOrientation.v : takes signed areas as OPAQUE reals supplied by the oracle, so it states no area fact of its own"),
        "Multi": ("oracle",   "Oracle AREA_UNIFIED: recursion, shoelace + arc sectors; red_area_unified_tests.py"),
    },
    "Relate (DE-9IM)": {
        "Arc":   ("qed",      "Qed for a partial cell set: RelateArcAnalytic.v : arc_analytic_proper_cross_share plus the sweep-range chain; single-arc lens RelateCurveArcSegment.v : point_in_ring_arc_seg_iff; disk witnesses in RelateCurveMatrix.v. Oracle CURVE_RELATE_MATRIX vectors are all single-segment"),
        "CS":    ("qed-adj",  "Real multi-arc Rocq content, but the predicate is SIMPLICITY, not DE-9IM: RingContactSound.v : ring_not_simple_of_arc_arc_circle_cross, _witness, _shared_endpoint (all Qed) quantify over a CurveRing indexed at i,j; consecutive-arc case ArcArcSound.v. DE-9IM proper: nothing — every bridge in RelateCurveBoundaryMeet.v is chord-chord, and RingContactSound.v : states the arc boundary cells remain on the deferred frontier. No multi-arc CURVE_RELATE_MATRIX vector"),
        "CC":    ("qed-adj",  "Simplicity Qed for mixed arc/chord pairs: RingContactSound.v : ring_not_simple_of_arc_chord, holes_not_disjoint_of_arc_chord. DE-9IM predicates do reduce over mixed rings — RelateCurveInscribedGeometry.v (Qed) — but via LINEARISED point sets (to_geometry vs inscribed_geometry), so they are arc-blind by construction, not arc-exact DE-9IM"),
        "CP":    ("qed",      "Triangle touch + regime guard; CURVE_RELATE_MATRIX"),
        "Multi": ("oracle",   "DE-9IM integer substrate (#67). red_relate_unified_tests.py is the only multi-segment relate vector and it is ALL CHORDS — no arc member"),
    },
    "Intersection / Overlay": {
        "Arc":   ("qed-cond", "CONDITIONAL: ArcOverlay.v : arc_overlay_correct_chord_approx is Qed but assumes H_A_bridge / H_B_bridge (), which the corpus does not discharge; says the unconditional headline is deferred. Contact kernels in OverlayContactSound.v are unconditional. Oracle OVERLAY_UNIFIED single-arc vectors red_overlay_unified_tests.py,"),
        "CS":    ("qed-cond", "Generic only: arc_overlay_correct_chord_approx quantifies over CurveGeometry so it formally applies to an all-arc ring, but its conclusion is an existential over arcs_of A ++ arcs_of B with NO ordering, adjacency or concatenation content — and the hypotheses are open. No CircularString-specific overlay lemma; no 2+-arc OVERLAY_UNIFIED vector"),
        "CC":    ("oracle",   "Oracle vectors only: OVERLAY_UNIFIED red_overlay_unified_tests.py (chord then arc, head-to-tail, vs a chord), (chord,chord vs chord,arc). Plus the generic conditional above. No CompoundCurve-specific overlay theorem"),
        "CP":    ("oracle",   "Oracle OVERLAY_UNIFIED: delegation for CurvePolygon"),
        "Multi": ("oracle",   "Oracle OVERLAY_UNIFIED: recursion for Multi* + arc-aware overlay; red_overlay_unified_tests.py"),
    },
    "Buffer": {
        "Arc":   ("qed",      "Qed: ArcOffset.v : arc_offset_dist_exact, _dist_lower, inner_offset_past_center_not_at_distance, arc_offset_tangent_parallel, arc_offset_no_kink, arc_offset_length. Oracle ARC_BUFFER_SIMPLE — note its header declares single-arc only, so the 'cs' half of its geom:arc,cs tag is unearned by its vectors"),
        "CS":    ("qed",      "THE ONE ROW with real multi-member Rocq content: CurveRingOffset.v : curve_ring_offset_valid (Qed) — a whole CurveRing offset by d stays a valid curve ring; supporting _adjacent, _closed. Join variants CurveOffsetAssembly.v (round), CurveMiterJoin.v, CurveBevelJoin.v, CurveCapWalk.v : curve_chain_buffer_valid. SCOPE: structural validity — arcs valid, adjacency, closedness — NOT buffer area or point-set correctness. No 2+-arc BUFFER_UNIFIED vector"),
        "CC":    ("qed",      "Qed, and literally the mixed case: curve_ring_offset maps over CSChord and CSArc alike (CurveRingOffset.v), with the mixed-member join at segment_join_offset_continuous; CurveBevelJoin.v : isolates the all-chord sub-case. Oracle BUFFER_UNIFIED head-to-tail compound vectors red_buffer_unified_tests.py (closed chord/arc/chord/chord thin-neck erosion), (multi-component with an arc member)"),
        "CP":    ("oracle",   "oracle/buffer_region_tests.txt + red_buffer_unified_tests.py; SegmentGraph + RingBuilder (nodes/inters, area filter); hole survival via ncomps"),
        "Multi": ("oracle",   "BUFFER_UNIFIED is the only unified mode with a real multi-component envelope (driver.ml ncomps) — the others parse a flat segment list. Red tests for no spurious rings + erosion count"),
    },
    # Added 2026-08-23.  These two rows hold the corpus's deepest curve work and
    # were invisible because no feature tag reached them: the join/offset claims
    # live inside "Phase 4 — Native curves" and the Koc section, and the LEC/MIC
    # claims were tagged feat:metric, which was not a matrix feature.
    "Join continuity (C¹ / C²)": {
        "Arc":   ("qed",      "Qed: ArcOffset.v : arc_offset_tangent_parallel, arc_offset_no_kink, arc_offset_tangent_reverses_past_singularity. Decision procedures CurveJoinClassify.v : g1_decision_correct, uturn_decision_correct. Round-join filler arc CurveRoundJoin.v : round_join_arc_valid, round_join_connects — both sit after End JoinFacts, so they carry no section hypotheses"),
        "CS":    ("qed",      "The strongest CS cell in the matrix. Arc-to-arc C¹ join: CompoundCurveKocJoin.v : koc25_compound_join_C1 (Qed) — the junction lies on BOTH circles at radii R1 and R2, and both radii are perpendicular to the shared tangent; koc25_compound_centers_collinear gives the classical S1-C-S2 collinearity; koc25_mirror_negates_slope covers the reverse curve (R2 < 0). Plus a genuine NEGATIVE result: CurveRingOffset.v : tangent_continuity_insufficient_for_offset (Qed) exhibits an S-curve — unit radii, shared endpoint, anti-parallel normals — whose offsets TEAR, (2,0) against (0,0). Tangent-line continuity is provably NOT sufficient for offset continuity across an arc-arc join. No oracle mode exercises joins at all"),
        "CC":    ("qed",      "The real content of this column. C¹ across all four joints of the five-member EN 13803-1 chain TC1-CA1-TC2-CA2-TC3 — clothoid transitions plus circular arcs, so genuinely mixed members: CompoundCurveAssembly.v : koc_compound_assembly_C1 (Qed), built from koc_joint_transition_to_arc and koc_joint_arc_to_transition, with slope provenance at and the whole result reproven after the stakeout transform to the national grid at koc_assembly_C1_in_grid. C² / curvature continuity is the companion: CompoundCurveCurvature.v : koc_compound_assembly_C0 (Qed) — no jump in lateral acceleration at any of the four joints — with koc_tc2_linear_ramp and koc_assembly_C0_to_straight. Generic segment-pair version CurveRingOffset.v : segment_join_offset_continuous. Oracle: nothing"),
        "CP":    ("none",     "Nothing found. Join continuity is a member-boundary property; no CurvePolygon ring-join theorem exists"),
        "Multi": ("none",     "Nothing found"),
    },
    "LEC / MIC": {
        "Arc":   ("qed",      "Qed: LECArcRow.v : arc_dist_exact — unconditional lower bound AND attainment, no case hypotheses survive — with empty_disk_arc_iff and the span gate arc_span_contains_iff_sign, which replaces atan2 with a single multiplication; refutation query_side_sector_hypothesis_refuted. MIC side MICChordNecessity.v : mic_cell_bound_exact_arc, chord_of_arc_understates_at_centre. Oracle OBSTACLE_DISTANCE singleton-ARC vectors with bit-parity asserted against the ARC_DISTANCE kernel; LEC_CIRCLE"),
        "CS":    ("qed",      "LECObstacleDistance.v : empty_disk_ring_iff — its own header calls this the full-circle CircularString ring — with empty_disk_disc_iff and obstacle_distance_headline (Qed). CAVEAT: LEC_CIRCLE accepts a 5-point CIRCULARSTRING form, but driver.ml runs circumcentre on the FIRST THREE POINTS ONLY and collapses the result to one (centre, radius), so it is a single-circle primitive, not a multi-arc run"),
        "CC":    ("qed",      "Qed for a MIXED member list — and the one place a 'delegation/sum over members' claim is actually earned by a proof: LECFlattenRow.v : typed_obstacle mixes TArc and TRing (curved) with TSeg (linear) in one list, typed_row_exact certifies every row against its closed form, and obstacle_list_flatten_exact plus empty_disk_flatten_iff fold them. The file's header states it closes the ledger's 'CompoundCurve / n-ary flatten' rung. CAVEAT: the fold is over an UNORDERED union (runion_list) — adjacency between members is never stated or used, so this is collection semantics, not a head-to-tail run. Also proven: no unit exists for the empty list, matching the oracle's k=0 DEGENERATE gate"),
        "CP":    ("qed",      "Qed: MaximumInscribedCircle.v and LargestEmptyCircle.v (unit square, side midpoints), CellRadiusBound.v cell-pruning bound, LECChordGap.v : lec_chord_hypothesis_refuted with lec_circle_closed_form, and candidate completeness at three strengths — LECCandidateVertex.v (witness-scoped), LECCandidateComplete.v (general), LECCandidateWeighted.v (weighted / Apollonius)"),
        "Multi": ("qed",      "The min-fold over an unordered union IS collection semantics, so LECFlattenRow.v : is the honest home of member-recursion claims — permutation and duplication invariants included (oracle obstacle_distance_tests.txt,). This is where the retired CurveCollection column's 'delegation/sum' prose actually belongs"),
    },
}
COVERAGE_ICON  = {"full": "✅", "partial": "⚠️", "none": "❌"}
COVERAGE_BG    = {"full": "#dcfce7", "partial": "#fef9c3", "none": "#fee2e2"}
COVERAGE_FG    = {"full": "#166534", "partial": "#854d0e", "none": "#991b1b"}

PRIORITY_COLOR = {
    "Immediate": "#dc2626", "Urgent": "#ea580c",
    "Non-urgent": "#0891b2", "Expectant": "#6b7280",
}


def e(s):
    return html.escape(str(s))


def _coverage_level(cell, feat_label=None, geom_label=None):
    proven = cell["proven"]
    cond   = cell["cond"]
    oracle = cell["oracle"]
    total  = proven + cond + oracle
    if total == 0:
        return "none"
    if proven > 0 and cond == 0:
        return "full"
    # matrix notes may describe "full" aspirational/oracle-backed plans (e.g. unified dispatch)
    # but icon/level follows actual theorem counts from claims + oracle tags.
    # "partial" for planned but not-yet-Qed composite support.
    return "partial"


def coverage_matrix_html(coverage_cells):
    geom_tags = COVERAGE_GEOM_TAGS
    header = "".join(
        f'<th title="{e(COVERAGE_GEOMTYPE_LONG[COVERAGE_GEOM_LABEL[g]])}">'
        f'{e(COVERAGE_GEOM_LABEL[g])}</th>' for g in geom_tags)
    rows = ""
    for ftag in COVERAGE_FEAT_TAGS:
        feat_label = COVERAGE_FEAT_LABEL[ftag]
        cells = ""
        for gtag in geom_tags:
            geom_label = COVERAGE_GEOM_LABEL[gtag]
            cell  = coverage_cells.get(ftag, {}).get(gtag, {"proven": 0, "cond": 0, "oracle": 0})
            level = _coverage_level(cell, feat_label, geom_label)
            bg    = COVERAGE_BG[level]
            fg    = COVERAGE_FG[level]
            icon  = COVERAGE_ICON[level]
            p, cond_n, o = cell["proven"], cell["cond"], cell["oracle"]
            tip = f"{p} proven, {cond_n} cond, {o} oracle tag(s)"
            static_note = COVERAGE_MATRIX.get(feat_label, {}).get(geom_label, ("", ""))[1]
            if static_note:
                tip += f" — {static_note}"
            cells += (f'<td style="text-align:center;background:{bg};color:{fg}'
                      f';font-size:16px" title="{e(tip)}">{icon}</td>')
        rows += f"<tr><td><b>{e(feat_label)}</b></td>{cells}</tr>"
    return (
        f'<table><thead><tr><th>Feature \\ Geometry</th>{header}</tr></thead>'
        f'<tbody>{rows}</tbody></table>'
        f'<p class="muted" style="font-size:12px;margin-top:6px">'
        f'✅&nbsp;Qed (unconditional)&nbsp; ⚠️&nbsp;partial / conditional&nbsp; '
        f'❌&nbsp;no corpus coverage — hover a cell for theorem counts + source note.</p>'
    )


def bar(segments, width=320):
    """segments: list of (value, color). Returns an inline stacked bar."""
    total = sum(v for v, _ in segments) or 1
    parts = []
    for v, c in segments:
        pct = 100.0 * v / total
        if pct <= 0:
            continue
        parts.append(f'<span style="display:inline-block;height:14px;'
                     f'width:{pct:.3f}%;background:{c}"></span>')
    return (f'<span style="display:inline-flex;width:{width}px;border-radius:7px;'
            f'overflow:hidden;background:#e5e7eb;vertical-align:middle">'
            + "".join(parts) + "</span>")


def parse_laser_ratchet():
    """Vendored engine-side perf data; see docs/laser-ratchet.json."""
    path = os.path.join(ROOT, "docs", "laser-ratchet.json")
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError):
        return None


def _ratio_badge(ratio, slack):
    """Green when the ratchet holds, red when it does not."""
    if ratio is None:
        return '<span class="muted">—</span>'
    try:
        ratio = float(ratio)
    except (TypeError, ValueError):
        return '<span class="muted">—</span>'
    ok = ratio <= slack
    bg, fg = ("#dcfce7", "#166534") if ok else ("#fee2e2", "#991b1b")
    mark = "✅" if ok else "❌"
    return (f'<span style="background:{bg};color:{fg};border-radius:5px;'
            f'padding:1px 6px;white-space:nowrap">{mark}&nbsp;{ratio:.3f}×</span>')


def _as_float(v):
    if v is None or v == "":
        return None
    try:
        return float(v)
    except (TypeError, ValueError):
        return None


# Bible zoo members that are not JTS Year-1. Caption only — do not invent
# timings. JTS Year-1 is ExactCircularArc; these are library work, not
# lasers the jts curve PR still owes.
YEAR2_ZOO_TYPES = frozenset({
    "ExactEllipticalArc", "ExactCubicBezier", "ExactClothoid", "ExactNurbsSegment",
})


def _gate_has_rows(g):
    rows = g.get("rows") if isinstance(g, dict) else None
    return isinstance(rows, list) and len(rows) > 0


def _fmt_ms_pair(laser, chainsaw, digits=3, extra_class=""):
    lf, cf = _as_float(laser), _as_float(chainsaw)
    if lf is None or cf is None:
        return '<td class="muted">—</td>'
    cls = "num" + (f" {extra_class}" if extra_class else "")
    return f'<td class="{cls}">{lf:.{digits}f} / {cf:.{digits}f} ms</td>'


def _render_operation_gate(h, slack):
    """One harness block. Tolerates missing red_* and extra keys (chord_path)."""
    note = f' — {h["note"]}' if h.get("note") else ""
    module = h.get("module") or "—"
    chainsaw_leg = h.get("chainsaw_leg") or "—"
    html_rows = (f'<tr style="background:#f8fafc"><td colspan="6">'
                 f'<b>{e(h.get("harness") or "?")}</b> <span class="muted">· {e(module)}'
                 f' · chainsaw leg: {e(chainsaw_leg)}{e(note)}</span></td></tr>')
    for r in h.get("rows") or []:
        red_ratio = _as_float(r.get("red_ratio"))
        if red_ratio is None and r.get("red_laser") is None:
            red = '<td class="muted" colspan="2">not transcribed</td>'
        else:
            red = (_fmt_ms_pair(r.get("red_laser"), r.get("red_chainsaw"),
                               extra_class="muted")
                   + f'<td class="num">{_ratio_badge(red_ratio, slack)}</td>')
        extra = ('<span class="muted">chord path</span>'
                 if r.get("chord_path") else "")
        now_l, now_c = _as_float(r.get("now_laser")), _as_float(r.get("now_chainsaw"))
        if now_l is None or now_c is None:
            now = '<td class="muted">—</td>'
        else:
            now = f'<td class="num">{now_l:.3f} / {now_c:.3f} ms</td>'
        html_rows += (f'<tr><td>{e(r.get("case") or "")}</td>{red}'
                      f'{now}'
                      f'<td class="num">{_ratio_badge(_as_float(r.get("now_ratio")), slack)}</td>'
                      f'<td>{extra}</td></tr>')
    return html_rows


def laser_ratchet_html(lr):
    if not lr:
        return ('<p class="muted">No <code>docs/laser-ratchet.json</code> — '
                'perf section skipped.</p>')
    slack = _as_float((lr.get("contract") or {}).get("slack")) or 1.15
    prov  = lr.get("provenance") or {}
    types = lr.get("types") or []

    # ---- curve-type coverage of the ratchet
    # Year-2 zoo chips are HOLD library work, not a red "JTS still owes
    # four Exact* types" debt on the curve PR.
    chips = []
    for t in types:
        name = t.get("name") or "?"
        note = t.get("note") or ""
        if t.get("measured"):
            bg, fg, mark = "#dcfce7", "#166534", "✅ measured"
        elif t.get("implemented"):
            bg, fg, mark = "#fef9c3", "#854d0e", "⚠️ unmeasured"
        elif name in YEAR2_ZOO_TYPES:
            bg, fg, mark = "#f1f5f9", "#334155", "library work, not JTS PR 7"
            if "library work" not in note.lower():
                note = (note + " — " if note else "") + \
                       "Year-2 zoo: library work, not JTS PR 7"
        else:
            bg, fg, mark = "#fee2e2", "#991b1b", "❌ not implemented"
        chips.append(f'<span class="chip" style="border-color:{fg};background:{bg}'
                     f';color:{fg}" title="{e(note)}"><b>{e(name)}</b>'
                     f'&nbsp;{mark}</span>')
    types_html = (
        f'<p class="muted">JTS Year-1 is <b>ExactCircularArc</b> (measured). '
        f'The Year-2 zoo types are <b>library work, not JTS PR 7</b> — not '
        f'missing lasers that PR still owes.</p>'
        f'<div class="chips">' + "".join(chips) + "</div>")

    # ---- primitive (per-curve-type) gates
    prows = ""
    for g in lr.get("primitive_gates") or []:
        laser_ns = _as_float(g.get("laser_ns"))
        chainsaw_ns = _as_float(g.get("chainsaw_ns"))
        ratio = _as_float(g.get("ratio"))
        if ratio is None and laser_ns is not None and chainsaw_ns:
            ratio = laser_ns / chainsaw_ns
        if laser_ns is None or chainsaw_ns is None:
            laser_cell = '<td class="muted">—</td>'
            chainsaw_cell = '<td class="muted">—</td>'
        else:
            laser_cell = (f'<td class="num" title="{g["laser_ns"]} ns">'
                          f'{laser_ns / 1e6:.1f} ms</td>')
            chainsaw_cell = (f'<td class="num" title="{g["chainsaw_ns"]} ns">'
                             f'{chainsaw_ns / 1e6:.1f} ms</td>')
        calls = g.get("calls")
        calls_txt = f"{calls:,} calls" if isinstance(calls, int) else "calls n/a"
        stat = g.get("stat") or "—"
        conditions = g.get("conditions") or ""
        prows += (f'<tr><td><code>{e(g.get("id") or "?")}</code></td>'
                  f'<td>{e(g.get("op") or "")}</td>'
                  f'{laser_cell}{chainsaw_cell}'
                  f'<td class="num">{_ratio_badge(ratio, slack)}</td>'
                  f'<td class="muted">{e(stat)} over {calls_txt} · '
                  f'{e(conditions)}</td></tr>')

    # ---- operation-level gates, plus formerly-ungauged harnesses that now
    # carry rows (jts may leave them under ungauged_gates or move them).
    operation_gates = list(lr.get("operation_gates") or [])
    still_ungauged = []
    for u in lr.get("ungauged_gates") or []:
        if _gate_has_rows(u):
            operation_gates.append(u)
        else:
            still_ungauged.append(u)

    orows = ""
    for h in operation_gates:
        orows += _render_operation_gate(h, slack)

    ungauged = ", ".join(f'<code>{e(u.get("harness") or "?")}</code>'
                         for u in still_ungauged)
    if still_ungauged:
        ungauged_html = (
            f'<h3>Gates live but unmeasured</h3>'
            f'<p class="muted">A 1.15× assertion is armed in each of these, but no '
            f'numbers have been transcribed: {ungauged}.</p>')
    else:
        ungauged_html = ""

    caveats = "".join(f"<li>{e(c)}</li>" for c in (prov.get("caveats") or []))
    pr = prov.get("pr")
    pr_bit = f' PR&nbsp;#{e(pr)},' if pr is not None else ""

    return (
        f'<p><b>Contract:</b> <code>{e((lr.get("contract") or {}).get("expr") or "")}</code> · '
        f'{e((lr.get("contract") or {}).get("scope") or "")}</p>'
        f'{types_html}'
        f'<h3>Per-curve-type ratchet — ExactCircularArc</h3>'
        f'<table><thead><tr><th>Gate</th><th>Operation</th><th>Laser</th>'
        f'<th>Chainsaw</th><th>Ratio</th><th>Conditions</th></tr></thead>'
        f'<tbody>{prows}</tbody></table>'
        f'<h3>Operation gates — red baseline vs current</h3>'
        f'<p class="muted">Each pair is laser&nbsp;/&nbsp;chainsaw. <b>Red</b> is '
        f'the state that opened the gate; <b>current</b> is after the laser landed. '
        f'The red column is kept deliberately — the interesting number is that '
        f'overlay started <b>30× slower</b> than densifying, not that it now wins.</p>'
        f'<table><thead><tr><th>Case</th><th>Red laser / chainsaw</th>'
        f'<th>Red ratio</th><th>Current laser / chainsaw</th>'
        f'<th>Current ratio</th><th></th></tr></thead>'
        f'<tbody>{orows}</tbody></table>'
        f'{ungauged_html}'
        f'<h3>Provenance</h3>'
        f'<p class="muted">Imported {e(prov.get("imported") or "")} from '
        f'<code>{e(prov.get("source_repo") or "")}</code>{pr_bit} branch '
        f'<code>{e(prov.get("branch") or "")}</code>, tip <code>{e(prov.get("tip") or "")}</code>. '
        f'Method: {e(prov.get("method") or "")}.</p>'
        f'<ul class="muted" style="font-size:12px;line-height:1.6">{caveats}</ul>')


def render(data):
    claims_total, regime_counts, sections, coverage_cells = data["claims"]
    issues = data["issues"]
    modes = data["oracle"]
    reg = data["registries"]
    sha = data["sha"]
    sha_short = sha[:9] if sha else "working tree"
    when = data["when"]

    proven = sum(regime_counts[r] for r in REGIMES if REGIME_KIND[r] == "proven")
    conditional = regime_counts["cond"]
    oracle_tagged = regime_counts["oracle"]
    oracle_vectors = sum(m["count"] for m in modes)

    def regime_legend():
        items = []
        for r in REGIMES:
            items.append(
                f'<span class="chip" style="border-color:{REGIME_COLOR[r]}">'
                f'<span class="dot" style="background:{REGIME_COLOR[r]}"></span>'
                f'{e(r)} <span class="muted">({e(REGIME_LABEL[r])})</span> '
                f'<b>{regime_counts[r]}</b></span>')
        return '<div class="chips">' + "".join(items) + "</div>"

    # ---- overview stat cards
    cards = [
        ("Cited theorems", claims_total, "in docs/verified-claims.md", "#0f172a"),
        ("Proven (unconditional)", proven, "[exact] · [full-b64] · [int-b64]", "#16a34a"),
        ("Conditional headlines", conditional, "[cond] — named hypotheses", "#d97706"),
        ("Oracle vectors", oracle_vectors, f"across {len(modes)} differential modes", "#2563eb"),
    ]
    card_html = "".join(
        f'<div class="card"><div class="card-v" style="color:{c}">{e(v)}</div>'
        f'<div class="card-t">{e(t)}</div><div class="card-s muted">{e(s)}</div></div>'
        for (t, v, s, c) in cards)

    # ---- issues
    issue_rows = ""
    for it in issues:
        pc = PRIORITY_COLOR.get(it["priority"], "#6b7280")
        issue_rows += (
            f'<tr><td><a href="https://github.com/grootstebozewolf/'
            f'NetTopologySuite.Proofs/issues/{e(it["num"])}">#{e(it["num"])}</a></td>'
            f'<td>{e(it["area"])}</td>'
            f'<td><span class="pill" style="background:{pc}">{e(it["priority"])}</span></td>'
            f'<td class="muted">{e(it["verdict"])}</td></tr>')

    # ---- claims by section
    sec_rows = ""
    for s in sections:
        segs = [(s["regimes"][r], REGIME_COLOR[r]) for r in REGIMES]
        is_group = s.get("group", False)
        style = ' style="font-weight:600;background:#f8fafc"' if is_group else ""
        sec_rows += (
            f'<tr{style}><td>{e(s["title"])}</td>'
            f'<td class="num">{s["rows"]}</td>'
            f'<td>{bar(segs)}</td></tr>')

    # ---- oracle modes
    mode_rows = ""
    for m in sorted(modes, key=lambda x: (-x["count"], x["name"])):
        mode_rows += (
            f'<tr><td><code>{e(m["name"].upper())}</code></td>'
            f'<td>{e(m["kind"])}</td><td class="num">{e(m["count"])}</td>'
            f'<td class="muted"><code>oracle/{e(m["file"])}</code></td></tr>')

    # ---- audit / registries
    def regrow(label, n, note):
        val = "—" if n is None else str(n)
        return (f'<tr><td>{e(label)}</td><td class="num">{e(val)}</td>'
                f'<td class="muted">{e(note)}</td></tr>')
    audit_rows = (
        regrow("Classical-reals axioms (theories/)", 3,
               "sig_not_dec · sig_forall_dec · functional_extensionality_dep")
        + regrow("Flocq binary64 adds", 1, "Classical_Prop.classic")
        + regrow("Admitted — verified counterexamples", reg["counterexamples"],
                 "docs/admitted-counterexamples.txt (provably-strongest)")
        + regrow("Admitted — deferred (proof structured)", reg["deferred"],
                 "docs/admitted-deferred-proofs.txt")
        + regrow("Hand-rolled interface-boundary kernels", reg["handroll"],
                 "docs/oracle-handrolled-allowlist.txt (frozen ratchet)"))

    return TEMPLATE.format(
        sha_short=e(sha_short), sha=e(sha), when=e(when),
        card_html=card_html, regime_legend=regime_legend(),
        issue_rows=issue_rows, sec_rows=sec_rows, mode_rows=mode_rows,
        audit_rows=audit_rows, coverage_matrix=coverage_matrix_html(coverage_cells),
        laser_ratchet=laser_ratchet_html(data["laser_ratchet"]),
        claims_total=claims_total, n_modes=len(modes),
        oracle_vectors=oracle_vectors, oracle_tagged=oracle_tagged)


TEMPLATE = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>NetTopologySuite.Proofs — Observatory</title>
<style>
  :root {{ --bg:#f8fafc; --fg:#0f172a; --muted:#64748b; --line:#e2e8f0;
           --card:#ffffff; --accent:#1e293b; }}
  * {{ box-sizing:border-box; }}
  body {{ margin:0; background:var(--bg); color:var(--fg);
          font:15px/1.55 -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,
          Helvetica,Arial,sans-serif; }}
  a {{ color:#2563eb; text-decoration:none; }}
  a:hover {{ text-decoration:underline; }}
  header {{ background:linear-gradient(120deg,#0f172a,#1e3a5f);
            color:#fff; padding:34px 24px 26px; }}
  header .wrap {{ max-width:1100px; margin:0 auto; }}
  header h1 {{ margin:0 0 4px; font-size:26px; letter-spacing:-.4px; }}
  header p {{ margin:6px 0 0; color:#cbd5e1; max-width:760px; }}
  .pills-top {{ margin-top:14px; }}
  .pills-top a {{ color:#e2e8f0; border:1px solid #475569; border-radius:999px;
                  padding:4px 12px; margin-right:8px; font-size:13px;
                  display:inline-block; }}
  main {{ max-width:1100px; margin:0 auto; padding:24px; }}
  .note {{ background:#fffbeb; border:1px solid #fde68a; border-radius:10px;
           padding:12px 16px; margin:0 0 24px; font-size:14px; color:#78350f; }}
  .cards {{ display:grid; grid-template-columns:repeat(auto-fit,minmax(210px,1fr));
            gap:14px; margin-bottom:28px; }}
  .card {{ background:var(--card); border:1px solid var(--line);
           border-radius:12px; padding:16px 18px; }}
  .card-v {{ font-size:30px; font-weight:700; letter-spacing:-.5px; }}
  .card-t {{ font-weight:600; margin-top:2px; }}
  .card-s {{ font-size:12.5px; margin-top:2px; }}
  section {{ margin:0 0 34px; }}
  h2 {{ font-size:18px; margin:0 0 12px; padding-bottom:6px;
        border-bottom:2px solid var(--line); }}
  table {{ width:100%; border-collapse:collapse; background:var(--card);
           border:1px solid var(--line); border-radius:12px; overflow:hidden; }}
  th,td {{ text-align:left; padding:9px 12px; border-bottom:1px solid var(--line);
           vertical-align:top; font-size:13.5px; }}
  th {{ background:#f1f5f9; font-size:12px; text-transform:uppercase;
        letter-spacing:.4px; color:var(--muted); }}
  tr:last-child td {{ border-bottom:none; }}
  td.num {{ text-align:right; font-variant-numeric:tabular-nums; font-weight:600; }}
  .muted {{ color:var(--muted); }}
  code {{ background:#f1f5f9; padding:1px 5px; border-radius:5px; font-size:12.5px; }}
  .pill {{ color:#fff; border-radius:999px; padding:2px 10px; font-size:12px;
           font-weight:600; white-space:nowrap; }}
  .chips {{ display:flex; flex-wrap:wrap; gap:8px; margin-bottom:14px; }}
  .chip {{ border:1px solid; border-radius:999px; padding:3px 11px; font-size:12.5px;
           background:#fff; }}
  .chip .dot {{ display:inline-block; width:9px; height:9px; border-radius:50%;
                margin-right:5px; vertical-align:middle; }}
  footer {{ max-width:1100px; margin:0 auto; padding:18px 24px 50px;
            color:var(--muted); font-size:12.5px; border-top:1px solid var(--line); }}
  .scales {{ display:grid; grid-template-columns:repeat(auto-fit,minmax(240px,1fr));
              gap:14px; margin-top:12px; }}
  .scale {{ background:var(--card); border:1px solid var(--line); border-radius:12px;
             padding:16px 18px; border-top:4px solid #1e293b; }}
  .scale.macro {{ border-top-color:#3d8f6e; }}
  .scale.meso {{ border-top-color:#6b8cae; }}
  .scale.micro {{ border-top-color:#c4894a; }}
  .scale h3 {{ margin:0 0 6px; font-size:15px; }}
  .scale .tag {{ display:inline-block; font-size:11px; font-weight:700; letter-spacing:.06em;
                  text-transform:uppercase; color:#64748b; margin-bottom:8px; }}
  .scale ul {{ margin:8px 0 0; padding-left:18px; font-size:13px; color:#475569; }}
  .scale code {{ font-size:11.5px; }}
  .machine {{ background:#f1f5f9; border-radius:10px; padding:12px 14px; font-family:ui-monospace,SFMono-Regular,Menlo,monospace;
               font-size:12.5px; line-height:1.55; color:#0f172a; margin-top:12px; white-space:pre; overflow-x:auto; }}
</style>
</head>
<body>
<header><div class="wrap">
  <h1>NetTopologySuite.Proofs — Observatory</h1>
  <p>Status of the mechanically-verified Rocq/Coq corpus that serves as the
     <b>soundness oracle</b> for the JTS&nbsp;→&nbsp;NTS geometry stack. Every
     number on this page is generated from in-repo source of record; nothing is
     hand-maintained.</p>
  <div class="pills-top">
    <a href="https://github.com/MerkatorBV/NetTopologySuite.Proofs">Proofs repo</a>
    <a href="https://github.com/NetTopologySuite/NetTopologySuite">NTS (.NET port)</a>
    <a href="https://github.com/locationtech/jts">JTS (Java reference)</a>
    <a href="https://github.com/locationtech/jts/issues/1195">JTS#1195 Curve EPIC</a>
    <a href="https://github.com/MerkatorBV/NetTopologySuite.Proofs/blob/main/docs/macro-meso-micro.md">Macro · Meso · Micro</a>
  </div>
</div></header>

<main>
  <div class="note"><b>Scope.</b> This is the proof / oracle <i>reference</i>, not a
    JTS/NTS test runner. The cross-project differential harness lives downstream in
    <code>NetTopologySuite.Curve</code>; here we report what is formally proven and
    which extracted oracle vectors back it, and link out to the upstream projects.
    Proven / conditional / oracle distinctions are kept explicit — there is no
    flattened &ldquo;all green&rdquo; health score.</div>

  <section>
    <h2>Macro · Meso · Micro</h2>
    <p class="muted">How the corpus is navigated for humans, auditors, and agents.
      ~thousands of statements are not maintained as a flat list — they are a
      <b>three-scale stack</b> tied to board epics (#64–#69), modules, and
      machine tags. Full write-up:
      <a href="https://github.com/MerkatorBV/NetTopologySuite.Proofs/blob/main/docs/macro-meso-micro.md"><code>docs/macro-meso-micro.md</code></a>.</p>
    <div class="scales">
      <div class="scale macro">
        <div class="tag">Macro</div>
        <h3>Domains & epics</h3>
        <p class="muted" style="margin:0;font-size:13px">Human-scale navigation.
          One board epic / topic owns a geometry family.</p>
        <ul>
          <li><code>topic: mesh</code> · <code>relate</code> · <code>arc</code> · <code>koc</code> · …</li>
          <li>Issues <b>#64–#69</b> (plus teaching ladder)</li>
          <li>Blast cone starts at domain epicenter</li>
        </ul>
      </div>
      <div class="scale meso">
        <div class="tag">Meso</div>
        <h3>Modules (.v files)</h3>
        <p class="muted" style="margin:0;font-size:13px">Audit atoms — not 5k+ free-floating theorems.
          ~hundreds of modules with Require edges.</p>
        <ul>
          <li>Layer law: core → predicates → <b>overlay</b> → Jordan → arcs → mesh</li>
          <li>ADR-0001: Jordan needs Overlay; rocq makefile</li>
          <li>Self-contained smoke / tripwire files when Overlay blocks</li>
        </ul>
      </div>
      <div class="scale micro">
        <div class="tag">Micro</div>
        <h3>Claims & witnesses</h3>
        <p class="muted" style="margin:0;font-size:13px">RGR unit of work: one claim, one witness, one Eval→Qed.</p>
        <ul>
          <li><code>claimId: 68-a</code> (board) or micro seed <code>even-square</code></li>
          <li><code>witness: empty-circle</code> · <code>(* WITNESS {{…}} *)</code></li>
          <li>Red → Green → Refactor; mutation checks vacuity</li>
        </ul>
      </div>
    </div>
    <div class="machine">topic: mesh
claimId: 68-a
witness: empty-circle</div>
    <p class="muted" style="margin-top:10px;font-size:12.5px">
      Machine header for PRs. <code>topic:</code> = macro · <code>claimId:</code> = micro board key ·
      <code>witness:</code> = falsifier for eval/mutation. Use <code>claimId: none</code> /
      <code>witness: none</code> only when intentionally off-board.
      Dynamic micro-kernel claims register from board sync / WITNESS payloads.
    </p>
  </section>

  <section>
    <div class="cards">{card_html}</div>
    {regime_legend}
  </section>

  <section>
    <h2>Issue tracker (#64–#69) — macro epics</h2>
    <table><thead><tr><th>Issue</th><th>Area</th><th>Priority</th>
      <th>Verdict (from TRIAGE)</th></tr></thead>
      <tbody>{issue_rows}</tbody></table>
  </section>

  <section>
    <h2>Feature × geometry-type coverage</h2>
    <p class="muted">Which NTS operations have mechanically-verified proofs for
      each curve geometry type. Column headers:
      <b>CS</b>&nbsp;=&nbsp;CircularString, <b>CC</b>&nbsp;=&nbsp;CompoundCurve,
      <b>CP</b>&nbsp;=&nbsp;CurvePolygon,
      <b>Multi</b>&nbsp;=&nbsp;MultiCurve&nbsp;/&nbsp;MultiSurface — the
      abbreviations used by the <code>grootstebozewolf/jts</code> fork, so a row
      reads the same in both trackers. <b>Arc</b>&nbsp;=&nbsp;CircularArc is this
      corpus's single-arc <em>primitive</em>, not a geometry type: an Arc theorem
      is not a CS theorem until something concatenates it.
      Hover a cell for the source-of-record lemma or the reason it is empty.</p>
    <p class="muted">Read the icons with care: they are driven by theorem and
      oracle-tag <em>counts</em>, and every <code>red_*_unified_tests.py</code>
      file carries one blanket <code>geom:arc,cs,cc,cp,multi</code> tag, so a
      single unified file credits itself to all five columns at once. The hover
      note is the honest per-column reading.</p>
    {coverage_matrix}
  </section>

  <section>
    <h2>Laser ratchet — exact curves vs densified</h2>
    <p class="muted">The <b>laser</b> is the curve-preserving path; the
      <b>chainsaw</b> is densify-then-compute. These are engine-side measurements
      from the JTS fork, vendored into
      <code>docs/laser-ratchet.json</code> so this page keeps reporting only on
      data that lives in this repo. They are <em>timings, not proofs</em> — no
      theorem below depends on them.</p>
    {laser_ratchet}
  </section>

  <section>
    <h2>Cited theorems by area — {claims_total} total</h2>
    <p class="muted">Each bar shows the regime mix of that section's claims
      (colours match the legend above).</p>
    <table><thead><tr><th>Section</th><th>Claims</th><th>Regime mix</th></tr></thead>
      <tbody>{sec_rows}</tbody></table>
  </section>

  <section>
    <h2>Oracle coverage — {n_modes} modes, {oracle_vectors} vectors</h2>
    <p class="muted">Extracted differential-test vectors (with reference expected
      outputs) the C# port is checked against. Run via
      <code>oracle/driver.ml</code> (RocqRefRunner).</p>
    <table><thead><tr><th>Mode</th><th>Kind</th><th>Vectors</th><th>Source</th></tr>
      </thead><tbody>{mode_rows}</tbody></table>
  </section>

  <section>
    <h2>Trust footprint &amp; audit</h2>
    <p class="muted">Qed-closure is enforced corpus-wide by
      <code>scripts/check_admitted.sh</code>; claim citations by
      <code>scripts/validate-claims.sh</code>. Every <code>Admitted</code> is
      registered as either a verified counterexample or a structured deferral.</p>
    <table><thead><tr><th>Item</th><th>Count</th><th>Source of record</th></tr>
      </thead><tbody>{audit_rows}</tbody></table>
  </section>
</main>

<footer>
  Generated by <code>scripts/gen_dashboard.py</code> from corpus commit
  <code>{sha_short}</code> · {when}. Source of record:
  <code>docs/verified-claims.md</code>, <code>TRIAGE_NTS_JTS_ISSUES.md</code>,
  <code>oracle/</code>, <code>docs/macro-meso-micro.md</code>. Companion project —
  not a verified implementation; every theorem ends with <code>Qed</code>.
  Navigation paradigm: <b>macro / meso / micro</b>.
</footer>
</body>
</html>
"""


_grounding_error_count = 0

# Count hardcoded in render()'s audit table — must stay in sync with axiom-allowlist.txt
_STATIC_AXIOM_COUNT = 3


def _check_grounding():
    errors = []
    # 1. Axiom allowlist count must match the hardcoded value shown in the audit table
    n_axioms = count_entries("docs/axiom-allowlist.txt")
    if n_axioms is None:
        errors.append("docs/axiom-allowlist.txt not found (shown in audit table as 3)")
    elif n_axioms != _STATIC_AXIOM_COUNT:
        errors.append(
            f"docs/axiom-allowlist.txt has {n_axioms} entries "
            f"but render() hardcodes {_STATIC_AXIOM_COUNT}")
    # 2. All registry files referenced by the audit table must exist
    for path in [
        "docs/admitted-counterexamples.txt",
        "docs/admitted-deferred-proofs.txt",
        "docs/oracle-handrolled-allowlist.txt",
    ]:
        if count_entries(path) is None:
            errors.append(f"{path} not found (referenced in audit table)")
    # 3. Every [tag] in table rows of verified-claims.md must be a known regime
    txt = read("docs/verified-claims.md") or ""
    known = set(REGIMES)
    seen_unknown = set()
    for line in txt.splitlines():
        if not (line.startswith("|") and "`" in line):
            continue
        for tag in re.findall(r'`\[([a-z][a-z0-9-]*)\]`', line):
            if tag not in known and tag not in seen_unknown:
                seen_unknown.add(tag)
                errors.append(
                    f"unknown regime tag [{tag}] in docs/verified-claims.md table "
                    f"(known: {', '.join(REGIMES)})")
    # 4. No file:line references in the coverage notes.  Line numbers rot on the
    #    first refactor and nothing recompiles a prose hook, so cite a theorem by
    #    NAME -- which validate-claims.sh actually verifies.  This mirrors the
    #    deliberate behaviour of validate-claims.sh, which treats a prose
    #    `File.v:123` as a claim citing a theorem named "123" and fails.
    for feat, row in COVERAGE_MATRIX.items():
        for geom, (_, note) in row.items():
            for hook in re.findall(r'[A-Za-z_][A-Za-z0-9_]*\.(?:v|ml|py|txt|cs):\d+',
                                   note):
                errors.append(
                    f"line-number hook '{hook}' in COVERAGE_MATRIX[{feat!r}][{geom!r}] "
                    f"— cite the theorem by name instead; line numbers go stale")
    # 5. Every feat:/geom: coverage tag must be in the documented vocabulary.
    #    This is the check that would have caught `cs` drifting from
    #    CircularString to CompoundCurve to "any CurveSegment".
    for m in re.finditer(r'coverage:|feat:([\w,\-]+)\s+geom:([\w,]+)', txt):
        if not m.group(1):
            continue
        for tag in m.group(1).split(","):
            if tag.strip() and tag.strip() not in KNOWN_FEAT_TAGS:
                errors.append(f"unknown feat tag '{tag.strip()}' in "
                              f"docs/verified-claims.md (known: "
                              f"{', '.join(sorted(KNOWN_FEAT_TAGS))})")
        for tag in m.group(2).split(","):
            if tag.strip() and tag.strip() not in KNOWN_GEOM_TAGS:
                errors.append(f"unknown geom tag '{tag.strip()}' in "
                              f"docs/verified-claims.md (known: "
                              f"{', '.join(sorted(KNOWN_GEOM_TAGS))})")
    for msg in errors:
        print("GROUNDING WARN:", msg, file=sys.stderr)
    return len(errors)


def build():
    global _grounding_error_count
    when = git("log", "-1", "--format=%cd", "--date=format:%Y-%m-%d")
    if not when:
        when = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    claims_data = parse_claims()
    oracle_modes = parse_oracle()

    # Merge oracle coverage tags into coverage_cells (oracle contribution alongside proofs)
    _, _, _, coverage_cells = claims_data
    for mode in oracle_modes:
        for (ft, gt) in mode.get("coverage_tags", []):
            if ft in coverage_cells and gt in coverage_cells[ft]:
                coverage_cells[ft][gt]["oracle"] += mode["count"] or 1

    data = {
        "claims": claims_data,
        "issues": parse_issues(),
        "oracle": oracle_modes,
        "laser_ratchet": parse_laser_ratchet(),
        "registries": {
            "counterexamples": count_entries("docs/admitted-counterexamples.txt"),
            "deferred": count_entries("docs/admitted-deferred-proofs.txt"),
            "handroll": count_entries("docs/oracle-handrolled-allowlist.txt"),
        },
        "sha": git("rev-parse", "HEAD"),
        "when": when,
    }
    _grounding_error_count = _check_grounding()
    return render(data)


def dashboard_inputs():
    """Paths whose change alters the generated page: the `paths:` filter of
    .github/workflows/pages.yml (single source, parsed here so the two cannot
    drift), minus the committed page itself.  None if pages.yml has no list."""
    txt = read(".github/workflows/pages.yml")
    if txt is None:
        return None
    paths, in_paths = [], False
    for ln in txt.splitlines():
        if re.match(r"^\s+paths:\s*$", ln):
            in_paths = True
            continue
        m = re.match(r"^\s+-\s+(\S+)\s*$", ln)
        if in_paths and m:
            paths.append(m.group(1).rstrip("*").rstrip("/"))
        elif in_paths:
            break
    return (paths + [":(exclude)dashboard/index.html"]) if paths else None


def check_freshness(strict):
    """Warn when the corpus commit shown in dashboard/index.html is behind HEAD
    for the dashboard's input paths.  The page embeds the commit it was generated
    from, which is always at least one behind the commit that stores it, so the
    test counts only commits since then that touched an input.  Warn-only unless
    strict.  Returns the process exit code."""
    def warn(msg):
        print(("::warning::" if os.environ.get("GITHUB_ACTIONS") else "warning: ") + msg)
        return 1 if strict else 0
    html = read("dashboard/index.html")
    if html is None:
        return warn("dashboard/index.html not found")
    m = re.search(r"corpus commit\s*<code>([0-9a-f]{7,40})</code>", html)
    if not m:
        return warn("dashboard/index.html shows no corpus commit")
    sha = m.group(1)
    if not git("cat-file", "-t", sha + "^{commit}"):
        return warn(f"dashboard shows commit {sha}, which is not in this clone "
                    "(shallow history?): freshness not verified")
    inputs = dashboard_inputs()
    if inputs is None:
        return warn("cannot read the paths: filter of .github/workflows/pages.yml")
    # default=None: a failing git call must not read as "nothing changed"
    behind_all = git("rev-list", "--count", f"{sha}..HEAD", default=None)
    touching = git("rev-list", f"{sha}..HEAD", "--", *inputs, default=None)
    if behind_all is None or touching is None:
        return warn(f"git could not list {sha}..HEAD: freshness not verified")
    # The commit that last stored the page contains its own regeneration, so
    # its input changes are already reflected and must not count as stale.
    stored_by = git("log", "-1", "--format=%H", "--", "dashboard/index.html")
    behind_in = str(len([c for c in touching.split() if c != stored_by]))
    if behind_in == "0":
        print(f"dashboard fresh: shows {sha}; {behind_all} commit(s) behind HEAD, "
              "none touching dashboard inputs")
        return 0
    return warn(f"dashboard shows corpus commit {sha}, {behind_in} commit(s) behind HEAD "
                f"touched its inputs ({behind_all} behind in total): regenerate with "
                "python3 scripts/gen_dashboard.py")


def main():
    if "--check-freshness" in sys.argv:
        sys.exit(check_freshness("--strict" in sys.argv))
    if "--check-grounding" in sys.argv:
        build()
        n = count_entries("docs/axiom-allowlist.txt") or 0
        if _grounding_error_count:
            sys.exit(1)
        print(f"grounding ok: axiom count={n}, registry files present, regime tags clean")
        return
    out_html = build()
    if "--check" in sys.argv:
        existing = ""
        if os.path.exists(OUT):
            with open(OUT, encoding="utf-8") as f:
                existing = f.read()
        if existing != out_html:
            print("dashboard/index.html is stale — run: python3 scripts/gen_dashboard.py",
                  file=sys.stderr)
            sys.exit(1)
        print("dashboard/index.html is up to date.")
        return
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w", encoding="utf-8") as f:
        f.write(out_html)
    print(f"wrote {os.path.relpath(OUT, ROOT)}")


if __name__ == "__main__":
    main()
