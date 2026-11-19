#!/usr/bin/env python3
"""KLIC hot-pixel demo: stock GEOS contradicts itself near a dig-polygon
corner; the verified kernel gives one answer with a stated, proved bound.

  python tools/klic-demo/demo.py [--png klic_hotpixel_demo.png] [--json out.json]

Two kinds of numbers are printed, and kept apart:

  PROVED   computed by the Rocq-extracted kernel (ocaml/hotpixel_q.ml) whose
           functions carry Qed reflection theorems (HotPixel_Q_exec.v); the
           1/2-cell displacement bound is a theorem, not a measurement.
  TESTED   measured by running a stock tool (Shapely/GEOS live; JTS, NTS and
           PostGIS from the recorded run in results/stock_results.json) or by
           plain Python Fraction arithmetic.  These are observations with the
           tool version printed beside them.

Scope: node placement and hot-pixel passing on a snap-rounding grid.  This is
not a verified overlay; nothing here proves the topology of an intersection
or a covers() answer.  Input data is SYNTHETIC (make_data.py).

BSD-3-Clause, NetTopologySuite.Proofs contributors.  Co-authored with Claude.
"""
from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path

import shapely
from shapely import wkt as shapely_wkt

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import verified_hotpixel as vk  # noqa: E402

CASE_A = HERE / "cases" / "caseA_pairs.wkt"
CASE_B = HERE / "cases" / "caseB.wkt"
STOCK = HERE / "results" / "stock_results.json"
STOCK_REAL = HERE / "results" / "stock_results_kadaster_examples.json"
REAL = HERE / "results" / "kadaster_examples.json"
GRID_S = 1  # input is in millimetres: s = 1 is the 1 mm grid
HALF = Fraction(1, 2)
PM_PER_MM = 10**9

THEOREMS = {
    "snap": "q_snap_coord_correct",
    "bound": "q_snap_disp_bound",
    "passes": "q_passes_through_closed_reflect",
    "touches": "q_touches_closed_reflect",
    "intersection": "q_seg_intersection_sound",
    "round": "q_round_ne_correct",
    "rd_repr": "rd_mm_grid_representable_b64",
    "b64_link": "b64_passes_through_implies_q",
}


def _edges(ring):
    return list(zip(ring[:-1], ring[1:]))


def _read_pairs(path):
    with open(path) as f:
        return [tuple(line.strip().split(";")) for line in f if line.strip()]


def _geos_points(geom):
    """All vertex coordinates of a Shapely geometry, as exact Fractions of the
    doubles GEOS returned."""
    return [(Fraction(x), Fraction(y)) for x, y in shapely.get_coordinates(geom)]


def case_a(pairs, s=GRID_S):
    """Case A: stock covers() vs the verified node placement, 3000 pairs."""
    covers_false = 0
    geos_pts = []
    for dtext, ctext in pairs:
        d, c = shapely_wkt.loads(dtext), shapely_wkt.loads(ctext)
        inter = c.intersection(d)
        covers_false += not d.covers(inter)
        geos_pts.append(_geos_points(inter))

    # Verified: exact nodes cable x each dig edge.
    inter_q, owners = [], []
    for k, (dtext, ctext) in enumerate(pairs):
        ring = vk.coords_from_wkt_text(dtext)
        c0, c1 = vk.coords_from_wkt_text(ctext)
        for e0, e1 in _edges(ring):
            inter_q.append((c0, c1, e0, e1))
            owners.append((k, c0, c1, e0, e1))
    nodes = vk.intersections_many(inter_q)
    hits = [(o, n) for o, n in zip(owners, nodes) if n is not None]

    # Snap every node (both coordinates) with the kernel.
    snaps = vk.snap_many([v for _, n in hits for v in n], s)
    snapped = [((snaps[2 * i][0], snaps[2 * i + 1][0]), (snaps[2 * i][1], snaps[2 * i + 1][1]))
               for i in range(len(hits))]
    max_disp = max(d for _, ds in snapped for d in ds)

    # Hot-pixel consistency: cable AND the dig edge both pass through the
    # snapped node's pixel, so snap rounding gives both the same node.
    qs = []
    for ((k, c0, c1, e0, e1), _), (sn, _) in zip(hits, snapped):
        qs.append((c0, c1, sn))
        qs.append((e0, e1, sn))
    pv = vk.passes_many(qs, s)
    both = sum(1 for i in range(len(hits)) if pv[2 * i] and pv[2 * i + 1])

    # TESTED: how far GEOS's intersection endpoints are from the exact nodes.
    exact_by_pair = {}
    for (o, n) in hits:
        exact_by_pair.setdefault(o[0], []).append(n)
    worst = Fraction(0)
    for k, pts in enumerate(geos_pts):
        ex = exact_by_pair.get(k, [])
        for gx, gy in pts:
            best = min(max(abs(gx - ex_x), abs(gy - ex_y)) for ex_x, ex_y in ex)
            if best < 1:  # endpoints that are nodes (not cable endpoints)
                worst = max(worst, best)
    return {
        "pairs": len(pairs),
        "stock_covers_false": covers_false,
        "verified_nodes": len(hits),
        "verified_max_disp_mm": str(max_disp),
        "verified_bound_mm": str(HALF / s),
        "verified_bound_holds": max_disp <= HALF / s,
        "verified_hotpixel_both": both,
        "geos_max_node_error_pm": float(worst * PM_PER_MM),
    }


def case_b(s=GRID_S, scale_to_metres=False):
    """Case B: one cable clipping a dig corner ~0.3 mm deep."""
    dtext, ctext = _read_pairs(CASE_B)[0]
    d, c = shapely_wkt.loads(dtext), shapely_wkt.loads(ctext)
    inter = c.intersection(d)
    stock = {"intersects": bool(c.intersects(d)), "relate": d.relate(c),
             "relate_interior_interior": d.relate(c)[0], "covers": bool(d.covers(inter)),
             "intersection_wkt": shapely.to_wkt(inter, rounding_precision=-1),
             "intersection_length_mm": inter.length}

    ring = vk.coords_from_wkt_text(dtext)
    c0, c1 = vk.coords_from_wkt_text(ctext)
    f = Fraction(1, 1000) if scale_to_metres else Fraction(1)
    if scale_to_metres:  # the same geometry written in metres, exactly
        ring = [(x * f, y * f) for x, y in ring]
        c0, c1 = (c0[0] * f, c0[1] * f), (c1[0] * f, c1[1] * f)
    corners = ring[:-1]
    # Which corner pixels does the cable pass through?
    corner_pass = vk.passes_many([(c0, c1, v) for v in corners], s)
    # Exact nodes with the dig edges, then snapped.
    nodes = [n for n in vk.intersections_many([(c0, c1, e0, e1) for e0, e1 in _edges(ring)]) if n]
    snaps = vk.snap_many([v for n in nodes for v in n], s)
    snapped = [(snaps[2 * i][0], snaps[2 * i + 1][0]) for i in range(len(nodes))]
    disps = [(snaps[2 * i][1], snaps[2 * i + 1][1]) for i in range(len(nodes))]
    hit = [i for i, p in enumerate(corner_pass) if p]
    return {
        "stock": stock,
        "corner_passes": corner_pass,
        "corner_hit": hit,
        "corner_hit_xy": [[str(corners[i][0]), str(corners[i][1])] for i in hit],
        "exact_nodes": [[str(x), str(y)] for x, y in nodes],
        "exact_nodes_float": [[float(x), float(y)] for x, y in nodes],
        "snapped_nodes": [[str(x), str(y)] for x, y in snapped],
        "snap_disp_mm": [[str(a / f), str(b / f)] for a, b in disps],
        "max_disp_mm": str(max(max(a, b) for a, b in disps) / f),
        "bound_mm": str(HALF / s / f),
        "snapped_on_corner": [p == corners[hit[0]] for p in snapped] if hit else [],
    }


def metre_float_hazard():
    """TESTED: metre text of a mm grid node is not a binary64 value."""
    dtext, _ = _read_pairs(CASE_B)[0]
    x_mm = int(vk.coords_from_wkt_text(dtext)[1][0])
    exact = Fraction(x_mm, 1000)
    as_double = Fraction(float(exact))
    return {"x_mm": str(x_mm), "x_m_exact": f"{x_mm // 1000}.{x_mm % 1000:03d}",
            "x_m_double_error_pm": float(abs(as_double - exact) * 10**12),
            "double_exact": as_double == exact}


def load_stock(path=STOCK):
    if not path.exists():
        return None
    return json.loads(path.read_text())


def real_summary():
    """Kadaster public example deliveries (recorded run, see real_data/)."""
    if not REAL.exists():
        return None
    d = json.loads(REAL.read_text())
    per = [r for dl in d["deliveries"] for r in dl["per_dig"]]
    return {
        "source": d["source"],
        "deliveries": len(d["deliveries"]),
        "lines": sum(dl["lines"] for dl in d["deliveries"]),
        "geos": sorted({f"Shapely {dl['shapely']} / GEOS {dl['geos']}" for dl in d["deliveries"]}),
        "stock_covers_false": sum(r["stock_covers_false"] for r in per),
        "deliveries_with_covers_false": sum(1 for r in per if r["stock_covers_false"]),
        "verified_dig_vertex_hotpixel_passes": sum(r["hotpixel_vertex_passes"] for r in per),
        "verified_exact_nodes": sum(r["exact_nodes"] for r in per),
        "verified_max_disp_m": str(max(Fraction(r["max_snap_disp_m"]) for r in per)),
        "verified_bound_holds": all(r["bound_holds"] for r in per),
    }


def compute():
    pairs = _read_pairs(CASE_A)
    res = {
        "shapely_version": shapely.__version__,
        "geos_version": shapely.geos_version_string,
        "data_label": "SYNTHETIC (make_data.py), integer-mm coordinates at RD magnitudes",
        "theorems": THEOREMS,
        "caseA": case_a(pairs),
        "caseB": case_b(),
        "caseB_metres_s1000": case_b(s=1000, scale_to_metres=True),
        "metre_float_hazard": metre_float_hazard(),
        "stock_recorded": load_stock(),
        "stock_recorded_real": load_stock(STOCK_REAL),
        "real": real_summary(),
    }
    return res


def _dec(q: str) -> str:
    """Six-decimal view of an exact rational string (display only)."""
    return f"{float(Fraction(q)):.6f}"


def _fmt_stock_row(r):
    if r.get("status") != "ok":
        return f"  {r['tool']:<8} not run: {r.get('reason', '')}"
    a, b = r["caseA"], r["caseB"]
    return (f"  {r['tool']:<8} {r['version']:<52} A covers=False {a['covers_false']:>5}/{a['pairs']}"
            f"   B intersects={str(b['intersects']):<5} relate[II]={b['relate'][0]} covers={b['covers']}")


def report(res) -> str:
    A, B, Bm, H = res["caseA"], res["caseB"], res["caseB_metres_s1000"], res["metre_float_hazard"]
    L = []
    L.append(f"KLIC hot-pixel demo  |  Shapely {res['shapely_version']} / GEOS {res['geos_version']}")
    L.append(f"data: {res['data_label']}")
    L.append("")
    L.append("CASE A  cable ∩ dig, then dig.covers(cable ∩ dig)            [TESTED, stock]")
    L.append(f"  GEOS: covers = False on {A['stock_covers_false']}/{A['pairs']} random pairs")
    L.append(f"  GEOS node error vs exact intersection: max {A['geos_max_node_error_pm']:.1f} pm"
             "   (picometres: GEOS is not badly wrong)")
    L.append("CASE A  verified node placement, 1 mm grid                    [PROVED per answer]")
    L.append(f"  exact nodes: {A['verified_nodes']}   max snap displacement: {_dec(A['verified_max_disp_mm'])} mm"
             f"  <= bound {A['verified_bound_mm']} mm ({THEOREMS['bound']})")
    L.append(f"  cable and dig edge both pass the node's hot pixel: {A['verified_hotpixel_both']}/"
             f"{A['verified_nodes']} ({THEOREMS['passes']})")
    L.append("")
    s = B["stock"]
    L.append("CASE B  cable clips a dig corner ~0.3 mm deep                 [TESTED, stock]")
    L.append(f"  cable.intersects(dig)          = {s['intersects']}")
    L.append(f"  dig.relate(cable) [int/int]    = {s['relate_interior_interior']}   ({s['relate']}: cable runs through the interior)")
    L.append(f"  dig.covers(cable ∩ dig)        = {s['covers']}   (the returned {s['intersection_length_mm']:.3f} mm piece)")
    L.append("  -> three answers that cannot all be right, and no stated error bound")
    L.append("CASE B  verified                                              [PROVED per answer]")
    L.append(f"  cable passes through corner pixel(s): {B['corner_hit']} at {B['corner_hit_xy']}")
    for ex, sn, dd, oc in zip(B["exact_nodes_float"], B["snapped_nodes"], B["snap_disp_mm"], B["snapped_on_corner"]):
        L.append(f"  node exact ({ex[0]:.6f}, {ex[1]:.6f}) -> grid ({sn[0]}, {sn[1]})"
                 f"  |d| = ({_dec(dd[0])}, {_dec(dd[1])}) mm{'  = the corner' if oc else ''}")
    L.append(f"  max displacement {_dec(B['max_disp_mm'])} mm <= {B['bound_mm']} mm (exact rationals in --json)")
    L.append("")
    L.append("UNIT SCALE  same case in metres, s = 1000 (1 mm grid)         [PROVED per answer]")
    L.append(f"  corner hit {Bm['corner_hit']}, snapped nodes {Bm['snapped_nodes']} m, max displacement {_dec(Bm['max_disp_mm'])} mm")
    L.append(f"  metre text {H['x_m_exact']} as a binary64: off by {H['x_m_double_error_pm']:.3f} pm (exact: {H['double_exact']})"
             "   [TESTED] -> metres are parsed as exact decimals")
    L.append("")
    st = res["stock_recorded"]
    if st:
        L.append(f"STOCK TOOLS  recorded run {st['run_utc']} (stock/run_all.py)          [TESTED]")
        for r in st["results"]:
            L.append(_fmt_stock_row(r))
    else:
        L.append("STOCK TOOLS  no recorded run (python stock/run_all.py)")
    R, SR = res["real"], res["stock_recorded_real"]
    if R:
        L.append("")
        L.append(f"REAL DATA  {R['deliveries']} public Kadaster example deliveries, {R['lines']} utility lines")
        L.append(f"  source: {R['source']}")
        L.append(f"  verified: dig-vertex hot-pixel passes {R['verified_dig_vertex_hotpixel_passes']};"
                 f" {R['verified_exact_nodes']} exact nodes, max snap displacement"
                 f" {_dec(str(Fraction(R['verified_max_disp_m']) * 1000))} mm <= 0.5 mm   [PROVED per answer]")
        L.append(f"  {R['geos'][0]}: covers=False on {R['stock_covers_false']} lines"
                 f" in {R['deliveries_with_covers_false']}/{R['deliveries']} deliveries   [TESTED]")
        if SR:
            for r in SR["results"]:
                a = r["caseA"]
                L.append(f"  {r['tool']:<8} {r['version']:<52} covers=False {a['covers_false']:>4}/{a['pairs']}"
                         f"  (empty ∩ {a['pairs'] - a['nonempty']})")
    L.append("")
    L.append("Proved = Qed in theories-flocq/HotPixel_Q_exec.v, standard classical axioms only")
    L.append("(proof_audit/print_assumptions.txt).  Scope: node placement + hot-pixel passing,")
    L.append("not a verified overlay.")
    return "\n".join(L)


def figure(res, path):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.patches import Rectangle

    B = res["caseB"]
    dtext, ctext = _read_pairs(CASE_B)[0]
    cx_, cy_ = (Fraction(v) for v in B["corner_hit_xy"][0])
    ox, oy = float(cx_), float(cy_)
    # Exact offsets from the corner, then clipped to the view window, so a
    # 20 m segment is not drawn at sub-mm zoom (matplotlib artefacts).
    from shapely.geometry import LineString, Polygon, box
    relq = lambda p: (float(p[0] - cx_), float(p[1] - cy_))  # noqa: E731
    view = box(-3, -3, 3, 3)
    ring_rel = Polygon([relq(p) for p in vk.coords_from_wkt_text(dtext)]).intersection(view)
    cab_rel = LineString([relq(p) for p in vk.coords_from_wkt_text(ctext)]).intersection(view)

    fig = plt.figure(figsize=(13, 6.9), dpi=110)
    gs = fig.add_gridspec(2, 2, width_ratios=[1.05, 1], height_ratios=[1, 0.42])
    ax = fig.add_subplot(gs[0, 0])
    for g in range(-3, 4):
        ax.axhline(g, color="#ddd", lw=0.6, zorder=0)
        ax.axvline(g, color="#ddd", lw=0.6, zorder=0)
    ax.add_patch(Rectangle((-0.5, -0.5), 1, 1, fc="#f2c94c55", ec="#b7950b", lw=1.2, zorder=1,
                           label="hot pixel of the corner (1 mm)"))
    rx, ry = ring_rel.exterior.xy
    ax.fill(rx, ry, fc="#3b82f622", ec="#1d4ed8", lw=1.6, label="dig polygon", zorder=2)
    cx0, cy0 = cab_rel.xy
    ax.plot(cx0, cy0, color="#c0392b", lw=1.6, label="cable", zorder=3)
    gpts = [relq(p) for p in _geos_points(shapely_wkt.loads(B["stock"]["intersection_wkt"]))]
    ax.plot([p[0] for p in gpts], [p[1] for p in gpts], color="#16a34a", lw=4, alpha=0.7,
            label="GEOS cable ∩ dig (covers=False)", zorder=4)
    for ex, ey in B["exact_nodes"]:
        ax.plot(float(Fraction(ex) - cx_), float(Fraction(ey) - cy_), "o", mfc="white", mec="black", ms=6, zorder=5)
    ax.plot([], [], "o", mfc="white", mec="black", label="exact nodes (ℚ, kernel)")
    for sx, sy in B["snapped_nodes"]:
        ax.plot(float(Fraction(sx) - cx_), float(Fraction(sy) - cy_), "s", color="black", ms=7, zorder=6)
    ax.plot([], [], "s", color="black", label="snapped nodes, 1 mm grid (kernel)")
    ax.set_xlim(-2.2, 2.2)
    ax.set_ylim(-2.2, 2.2)
    ax.set_aspect("equal")
    ax.set_xlabel("mm from corner (RD x ≈ %.0f mm)" % ox)
    ax.set_ylabel("mm from corner (RD y ≈ %.0f mm)" % oy)
    ax.set_title("Case B: cable clips a dig corner 0.30 mm deep", fontsize=11)
    ax.legend(loc="lower left", fontsize=7.5, framealpha=0.95)

    ax2 = fig.add_subplot(gs[0, 1])
    ax2.axis("off")
    s = B["stock"]
    A = res["caseA"]
    txt = [
        ("TESTED — stock Shapely %s / GEOS %s" % (res["shapely_version"], res["geos_version"]), "bold", "#7f1d1d"),
        ("Case B  cable.intersects(dig)       = %s" % s["intersects"], None, "black"),
        ("        dig.relate(cable)[int/int]  = %s" % s["relate_interior_interior"], None, "black"),
        ("        dig.covers(cable ∩ dig)     = %s" % s["covers"], None, "black"),
        ("Case A  covers=False on %d / %d pairs" % (A["stock_covers_false"], A["pairs"]), None, "black"),
        ("        node error ≤ %.0f pm — tiny, but no stated bound" % A["geos_max_node_error_pm"], None, "black"),
        ("", None, "black"),
        ("PROVED — Rocq-extracted kernel, Qed, 1 mm grid", "bold", "#14532d"),
        ("Case B  cable passes the corner's hot pixel: yes", None, "black"),
        ("        %d nodes → %d on the corner, max |d| %.4f mm ≤ ½ mm"
         % (len(B["snapped_nodes"]), sum(B["snapped_on_corner"]), float(Fraction(B["max_disp_mm"]))), None, "black"),
        ("Case A  %d nodes, max |d| %.4f mm ≤ ½ mm" % (A["verified_nodes"], float(Fraction(A["verified_max_disp_mm"]))), None, "black"),
        ("        cable & dig edge share the node pixel: %d/%d" % (A["verified_hotpixel_both"], A["verified_nodes"]), None, "black"),
        ("Theorems: q_snap_disp_bound, q_passes_through_closed_reflect,", None, "#333"),
        ("q_seg_intersection_sound, q_snap_coord_correct (HotPixel_Q_exec.v)", None, "#333"),
        ("Scope: node placement + hot-pixel passing; not a verified overlay.", None, "#555"),
    ]
    y = 0.98
    for t, w, col in txt:
        ax2.text(0.0, y, t, family="monospace", fontsize=8.6, weight=w or "normal", color=col,
                 transform=ax2.transAxes, va="top")
        y -= 0.062

    ax3 = fig.add_subplot(gs[1, :])
    ax3.axis("off")
    st = res["stock_recorded"]
    rows = []
    real = {r["tool"]: r for r in res["stock_recorded_real"]["results"]} if res["stock_recorded_real"] else {}
    if st:
        for r in st["results"]:
            if r.get("status") != "ok":
                rows.append([r["tool"], "not run", r.get("reason", ""), "", "", "", ""])
                continue
            a, b = r["caseA"], r["caseB"]
            ra = real.get(r["tool"], {}).get("caseA")
            rows.append([r["tool"], r["version"], f"{a['covers_false']} / {a['pairs']}",
                         str(b["intersects"]), b["relate"][0], str(b["covers"]),
                         f"{ra['covers_false']} / {ra['pairs']}" if ra else "—"])
    R = res["real"]
    rows.append(["verified kernel", "HotPixel_Q_exec.v (Qed) → OCaml",
                 "no overlay; nodes ≤ ½ mm", "passes corner pixel", "—", "n/a (no overlay)",
                 f"{R['verified_dig_vertex_hotpixel_passes']} vertex-pixel passes" if R else "—"])
    tab = ax3.table(cellText=rows,
                    colLabels=["tool", "version (as printed by the tool)", "A: covers=False",
                               "B: intersects", "B: relate II", "B: covers(∩)",
                               "Kadaster examples: covers=False"],
                    loc="upper center", cellLoc="left", colWidths=[0.09, 0.3, 0.13, 0.11, 0.07, 0.1, 0.18])
    tab.auto_set_font_size(False)
    tab.set_fontsize(8.2)
    tab.scale(1, 1.35)
    when = st["run_utc"] if st else "—"
    ax3.set_title(f"Per-tool results, same inputs (TESTED; recorded run {when}). Synthetic cases A/B; last column: "
                  f"24 public Kadaster KLIC example deliveries (kadaster/klic-win)", fontsize=9.5, loc="left")
    fig.text(0.01, 0.01, "Cases A/B: synthetic KLIC-shaped data (integer mm at RD magnitudes). "
             "NetTopologySuite.Proofs contributors, BSD-3-Clause; co-authored with Claude.",
             fontsize=7.5, color="#555")
    fig.tight_layout(rect=(0, 0.02, 1, 1))
    fig.savefig(path)
    plt.close(fig)


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--png", default=str(HERE / "klic_hotpixel_demo.png"))
    ap.add_argument("--json", default=None)
    ap.add_argument("--no-png", action="store_true")
    a = ap.parse_args(argv)
    res = compute()
    print(report(res))
    if a.json:
        Path(a.json).write_text(json.dumps(res, indent=2, default=str) + "\n")
    if not a.no_png:
        figure(res, a.png)
        print(f"\nfigure: {a.png}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
