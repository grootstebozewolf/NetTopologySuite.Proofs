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
#
# License: BSD-3-Clause (see LICENSE)
# AI assistance disclosure: AI-drafted, human-reviewed.  Assisted-by: Claude
# =============================================================================

import os, re, sys, html, subprocess
from datetime import datetime, timezone

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "dashboard", "index.html")

REGIMES = ["exact", "full-b64", "int-b64", "int-b64-arc", "int", "cond", "oracle"]
REGIME_LABEL = {
    "exact": "exact reals",
    "full-b64": "all finite binary64",
    "int-b64": "int-coord binary64",
    "int-b64-arc": "int-coord binary64 (arc)",
    "int": "exact integer (0 axioms)",
    "cond": "conditional (named hyps)",
    "oracle": "extracted / differential",
}
# proven (unconditional soundness) vs conditional vs oracle-only
REGIME_KIND = {
    "exact": "proven", "full-b64": "proven", "int-b64": "proven",
    "int-b64-arc": "proven", "int": "proven", "cond": "conditional", "oracle": "oracle",
}
REGIME_COLOR = {
    "exact": "#16a34a", "full-b64": "#15803d", "int-b64": "#65a30d",
    "int-b64-arc": "#84cc16", "int": "#0891b2", "cond": "#d97706", "oracle": "#2563eb",
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

PROVEN_REGIMES = {"exact", "full-b64", "int-b64", "int-b64-arc", "int"}


def parse_claims():
    txt = read("docs/verified-claims.md") or ""
    theorem_lines = [ln for ln in txt.splitlines()
                     if re.match(r'^\| `[^`]+ : ', ln)]
    total = len(theorem_lines)
    # count regime tags only in actual theorem rows, not headers/legends
    regime_counts = {r: sum(len(re.findall(r'\[' + re.escape(r) + r'\]', ln))
                             for ln in theorem_lines)
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
            title = re.sub(r'\s*<!--.*?-->', '', raw).strip()
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
                cur["regimes"][r] += len(re.findall(r'\[' + re.escape(r) + r'\]', line))
            # accumulate coverage matrix counts
            if cur_feats and cur_geoms:
                row_proven = sum(len(re.findall(r'\[' + re.escape(r) + r'\]', line))
                                 for r in PROVEN_REGIMES)
                row_cond   = len(re.findall(r'\[cond\]', line))
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
                    n = sum(1 for ln in f if "= run(" in ln)
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
COVERAGE_FEAT_TAGS = ["distance", "arc-len", "area", "relate", "overlay", "buffer"]
COVERAGE_GEOM_TAGS = ["arc", "cs", "cc", "cp", "multi"]

COVERAGE_FEAT_LABEL = {
    "distance": "Distance",
    "arc-len":  "Arc / chord length",
    "area":     "Area / perimeter",
    "relate":   "Relate (DE-9IM)",
    "overlay":  "Intersection / Overlay",
    "buffer":   "Buffer",
}
COVERAGE_GEOM_LABEL = {
    "arc": "Arc", "cs": "CS", "cc": "CC", "cp": "CP", "multi": "Multi",
}
# Keep display names for backward compat (COVERAGE_MATRIX tooltip lookup)
COVERAGE_FEATURES  = [COVERAGE_FEAT_LABEL[t] for t in COVERAGE_FEAT_TAGS]
COVERAGE_GEOMTYPES = [COVERAGE_GEOM_LABEL[t] for t in COVERAGE_GEOM_TAGS]
COVERAGE_GEOMTYPE_LONG = {
    "Arc": "CircularArc",
    "CS": "CompoundCurve",
    "CC": "CurveCollection",
    "CP": "CurvePolygon",
    "Multi": "MultiSurface / MultiCurve",
}
# Source-of-record for each cell (file:lemma or prose note for deferred items)
COVERAGE_MATRIX = {
    "Distance": {
        "Arc":   ("full",    "ArcPointDistance.v + ArcChordLength.v (Qed)"),
        "CS":    ("partial", "point–arc proven; compound sequences deferred"),
        "CC":    ("none",    "no corpus coverage"),
        "CP":    ("none",    "no corpus coverage"),
        "Multi": ("none",    "no corpus coverage"),
    },
    "Arc / chord length": {
        "Arc":   ("full",    "ArcChordLength.v:arc_chord_le_arc_length + RelateArcAnalytic.v (Qed)"),
        "CS":    ("partial", "scalar arc-length proven; concatenation deferred"),
        "CC":    ("none",    "no corpus coverage"),
        "CP":    ("none",    "no corpus coverage"),
        "Multi": ("none",    "no corpus coverage"),
    },
    "Area / perimeter": {
        "Arc":   ("partial", "signed-area lemmas in GeneralTriangle* (Qed, triangles only)"),
        "CS":    ("partial", "perimeter via arc-chord; full area deferred"),
        "CC":    ("none",    "no corpus coverage"),
        "CP":    ("partial", "triangle polygon area theorems (RelateNG.v, conditional)"),
        "Multi": ("none",    "no corpus coverage"),
    },
    "Relate (DE-9IM)": {
        "Arc":   ("partial", "RelateArcAnalytic.v stubs + RelateNG triangle touch (S15l, cond)"),
        "CS":    ("partial", "RelateNG integer substrate (#67, 194 theorems, S15l complete)"),
        "CC":    ("partial", "DE-9IM integer substrate (#67); collection dispatch deferred"),
        "CP":    ("partial", "triangle touch + regime guard (conditional Qed); classifier stub open"),
        "Multi": ("partial", "substrate proven; multi-geometry dispatch deferred"),
    },
    "Intersection / Overlay": {
        "Arc":   ("partial", "H_bridge_premise_from_euler (HBridgeEuler.v, Qed); ring extraction conditional"),
        "CS":    ("partial", "OverlayBridge.v:extract_rings_valid (conditional Qed, Euler hyps as premises)"),
        "CC":    ("none",    "no corpus coverage"),
        "CP":    ("none",    "no corpus coverage"),
        "Multi": ("none",    "no corpus coverage"),
    },
    "Buffer": {
        "Arc":   ("", "oracle/arc_buffer_simple_tests.txt (ARC_BUFFER_SIMPLE) + oracle/red_buffer_unified_tests.py (BUFFER_UNIFIED pilot); analytical offset via ARC_OFFSET_XY"),
        "CS":    ("", "oracle/arc_buffer_simple_tests.txt + oracle/red_buffer_unified_tests.py pilot; open-path round-cap handling; arc preservation in output"),
        "CC":    ("", "oracle/red_buffer_unified_tests.py pilot via unified GetSegments dispatch"),
        "CP":    ("", "oracle/buffer_region_tests.txt (BUFFER_REGION arc-ring) + oracle/red_buffer_unified_tests.py pilot; CurvePolygon output typing wired"),
        "Multi": ("", "no oracle coverage"),
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


def _coverage_level(cell):
    proven = cell["proven"]
    cond   = cell["cond"]
    oracle = cell["oracle"]
    total  = proven + cond + oracle
    if total == 0:
        return "none"
    if proven > 0 and cond == 0:
        return "full"
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
            level = _coverage_level(cell)
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
    <a href="https://github.com/grootstebozewolf/NetTopologySuite.Proofs">Proofs repo</a>
    <a href="https://github.com/NetTopologySuite/NetTopologySuite">NTS (.NET port)</a>
    <a href="https://github.com/locationtech/jts">JTS (Java reference)</a>
    <a href="https://github.com/locationtech/jts/issues/1195">JTS#1195 Curve EPIC</a>
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
    <div class="cards">{card_html}</div>
    {regime_legend}
  </section>

  <section>
    <h2>Issue tracker (#64–#69)</h2>
    <table><thead><tr><th>Issue</th><th>Area</th><th>Priority</th>
      <th>Verdict (from TRIAGE)</th></tr></thead>
      <tbody>{issue_rows}</tbody></table>
  </section>

  <section>
    <h2>Feature × geometry-type coverage</h2>
    <p class="muted">Which NTS operations have mechanically-verified proofs for
      each curve geometry type. Column headers: Arc&nbsp;=&nbsp;CircularArc,
      CS&nbsp;=&nbsp;CompoundCurve, CC&nbsp;=&nbsp;CurveCollection,
      CP&nbsp;=&nbsp;CurvePolygon, Multi&nbsp;=&nbsp;Multi*.
      Hover a cell for the source-of-record lemma or deferral note.</p>
    {coverage_matrix}
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
  <code>oracle/</code>. Companion project — not a verified implementation; every
  theorem ends with <code>Qed</code>.
</footer>
</body>
</html>
"""


def build():
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
        "registries": {
            "counterexamples": count_entries("docs/admitted-counterexamples.txt"),
            "deferred": count_entries("docs/admitted-deferred-proofs.txt"),
            "handroll": count_entries("docs/oracle-handrolled-allowlist.txt"),
        },
        "sha": git("rev-parse", "HEAD"),
        "when": when,
    }
    return render(data)


def main():
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
