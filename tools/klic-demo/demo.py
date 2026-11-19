#!/usr/bin/env python3
"""KLIC hot-pixel demo: stock geometry libraries contradict themselves near a
dig polygon; the verified kernel gives one answer with a stated, proved bound.

  python tools/klic-demo/demo.py [--png klic_hotpixel_demo.png] [--json out.json]

Cases (all SYNTHETIC, KLIC-shaped, RD millimetres):
  A   handover LS-0042 crosses dig polygon GP-0001 (data/klic_handover_mm.wkt)
  A*  the same check on 3000 random (dig, cable) pairs (cases/caseA_pairs.wkt)
  B   handover MS-0007 passes 0.30 mm OUTSIDE a GP-0001 vertex
  C   a cable clips a dig corner ~0.3 mm INSIDE (cases/caseC.wkt)

Two kinds of numbers are printed, and kept apart:

  PROVED   computed by the Rocq-extracted kernel (ocaml/hotpixel_q.ml) whose
           functions carry Qed reflection theorems (HotPixel_Q_exec.v); the
           1/2-cell displacement bound is a theorem, not a measurement.
  TESTED   measured by running a stock tool (Shapely/GEOS live; JTS, NTS and
           PostGIS from the recorded run in results/stock_results.json) or by
           plain Python Fraction / Shapely arithmetic.  These are observations
           with the tool version printed beside them.

Scope: node placement and hot-pixel passing on a snap-rounding grid.  This is
not a verified overlay; nothing here proves the topology of an intersection
or a covers() answer.

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

PAIRS = HERE / "cases" / "caseA_pairs.wkt"
CASE_C = HERE / "cases" / "caseC.wkt"
HANDOVER = HERE / "data" / "klic_handover_mm.wkt"
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


# --------------------------------------------------------------------------
# helpers
# --------------------------------------------------------------------------

def _edges(ring):
    return list(zip(ring[:-1], ring[1:]))


def _read_pairs(path):
    with open(path) as f:
        return [tuple(line.strip().split(";")) for line in f if line.strip()]


def read_handover():
    """{fid: wkt text} from the tab-separated handover file."""
    out = {}
    for line in HANDOVER.read_text().splitlines():
        if line.startswith("#") or not line.strip():
            continue
        fid, _typ, _thema, w = line.split("\t")
        out[fid] = w
    return out


def _geos_points(geom):
    """Vertex coordinates of a Shapely geometry, as exact Fractions of the
    doubles GEOS returned."""
    return [(Fraction(x), Fraction(y)) for x, y in shapely.get_coordinates(geom)]


def _s(q) -> str:
    return str(Fraction(q))


def _dec(q) -> str:
    """Six-decimal view of an exact rational (display only)."""
    return f"{float(Fraction(q)):.6f}"


def _cheb(p, q):
    return max(abs(p[0] - q[0]), abs(p[1] - q[1]))


# --------------------------------------------------------------------------
# A*: 3000 random pairs
# --------------------------------------------------------------------------

def random_a(pairs, s=GRID_S):
    covers_false = 0
    geos_pts = []
    for dtext, ctext in pairs:
        d, c = shapely_wkt.loads(dtext), shapely_wkt.loads(ctext)
        inter = c.intersection(d)
        covers_false += not d.covers(inter)
        geos_pts.append(_geos_points(inter))

    inter_q, owners = [], []
    for k, (dtext, ctext) in enumerate(pairs):
        ring = vk.coords_from_wkt_text(dtext)
        c0, c1 = vk.coords_from_wkt_text(ctext)
        for e0, e1 in _edges(ring):
            inter_q.append((c0, c1, e0, e1))
            owners.append((k, c0, c1, e0, e1))
    nodes = vk.intersections_many(inter_q)
    hits = [(o, n) for o, n in zip(owners, nodes) if n is not None]

    snaps = vk.snap_many([v for _, n in hits for v in n], s)
    snapped = [((snaps[2 * i][0], snaps[2 * i + 1][0]), (snaps[2 * i][1], snaps[2 * i + 1][1]))
               for i in range(len(hits))]
    max_disp = max(d for _, ds in snapped for d in ds)

    qs = []
    for ((k, c0, c1, e0, e1), _), (sn, _) in zip(hits, snapped):
        qs.append((c0, c1, sn))
        qs.append((e0, e1, sn))
    pv = vk.passes_many(qs, s)
    both = sum(1 for i in range(len(hits)) if pv[2 * i] and pv[2 * i + 1])

    exact_by_pair = {}
    for (o, n) in hits:
        exact_by_pair.setdefault(o[0], []).append(n)
    worst = Fraction(0)
    for k, pts in enumerate(geos_pts):
        ex = exact_by_pair.get(k, [])
        for p in pts:
            best = min(_cheb(p, e) for e in ex)
            if best < 1:  # intersection endpoints that are nodes
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


# --------------------------------------------------------------------------
# A and B: the handover scenario (GP-0001, LS-0042, MS-0007)
# --------------------------------------------------------------------------

def case_a(s=GRID_S):
    """LS-0042 crosses GP-0001."""
    h = read_handover()
    dig, ls = shapely_wkt.loads(h["GP-0001"]), shapely_wkt.loads(h["LS-0042"])
    inter = ls.intersection(dig)
    gpts = [shapely.Point(p) for p in shapely.get_coordinates(inter)]
    sr = shapely.intersection(ls, dig, grid_size=1)
    stock = {
        "intersects": bool(ls.intersects(dig)),
        "intersection_wkt": shapely.to_wkt(inter, rounding_precision=-1),
        "covers": bool(dig.covers(inter)),
        "within": bool(inter.within(dig)),
        "points_on_cable": [bool(ls.intersects(p)) for p in gpts],
        "points_on_boundary": [bool(dig.boundary.intersects(p)) for p in gpts],
        "sr_wkt": shapely.to_wkt(sr, rounding_precision=-1),
        "sr_covers": bool(shapely.set_precision(dig, 1).covers(sr)),
    }

    ring = vk.coords_from_wkt_text(h["GP-0001"])
    c0, c1 = vk.coords_from_wkt_text(h["LS-0042"])
    edges = _edges(ring)
    nodes = vk.intersections_many([(c0, c1, e0, e1) for e0, e1 in edges])
    hit = [(i, n) for i, n in enumerate(nodes) if n is not None]
    snaps = vk.snap_many([v for _, n in hit for v in n], s)
    snapped = [(snaps[2 * k][0], snaps[2 * k + 1][0]) for k in range(len(hit))]
    disps = [(snaps[2 * k][1], snaps[2 * k + 1][1]) for k in range(len(hit))]
    pv = vk.passes_many([q for (i, _), sn in zip(hit, snapped)
                         for q in ((c0, c1, sn), (edges[i][0], edges[i][1], sn))], s)

    # GEOS crossing points vs the exact node of the DOUBLES GEOS was given
    # (the decimal text is a shortest round-trip repr, not the double's exact
    # value).  Exact node by the kernel; the error itself is TESTED arithmetic.
    dbl = lambda pts: [(Fraction(float(x)), Fraction(float(y))) for x, y in pts]  # noqa: E731
    d0, d1 = dbl([c0, c1])
    dn = [n for n in vk.intersections_many([(d0, d1, e0, e1) for e0, e1 in _edges(dbl(ring))]) if n]
    geos_err_pm = [float(min(_cheb(p, n) for n in dn) * PM_PER_MM) for p in _geos_points(inter)]

    # Noded 1 mm arrangement: dig vertices snapped by the kernel, the snapped
    # nodes inserted on their edges; the verified inside part joins the nodes.
    vs = vk.snap_many([v for p in ring[:-1] for v in p], s)
    vsn = [(vs[2 * k][0], vs[2 * k + 1][0]) for k in range(len(ring) - 1)]
    noded = []
    for i in range(len(ring) - 1):
        noded.append(vsn[i])
        noded.extend(sn for (j, _), sn in zip(hit, snapped) if j == i)
    noded.append(noded[0])
    noded_poly = shapely.Polygon([(float(x), float(y)) for x, y in noded])
    order = sorted(range(len(snapped)), key=lambda k: snapped[k][0])
    inside = shapely.LineString([(float(snapped[k][0]), float(snapped[k][1])) for k in order])
    return {
        "stock": stock,
        "exact_nodes": [[_s(x), _s(y)] for _, (x, y) in hit],
        "exact_nodes_float": [[float(x), float(y)] for _, (x, y) in hit],
        "node_edges": [i for i, _ in hit],
        "snapped_nodes": [[_s(x), _s(y)] for x, y in snapped],
        "snap_disp_mm": [[_s(a), _s(b)] for a, b in disps],
        "max_disp_mm": _s(max(max(a, b) for a, b in disps)),
        "bound_mm": _s(HALF / s),
        "passes_cable_and_edge": [[pv[2 * k], pv[2 * k + 1]] for k in range(len(hit))],
        "geos_point_error_pm": geos_err_pm,
        "tested_inside_part_wkt": inside.wkt,
        "tested_noded_dig_valid": bool(noded_poly.is_valid),
        "tested_noded_dig_covers_inside": bool(noded_poly.covers(inside)),
        "tested_inside_equals_geos_sr": bool(shapely.equals(inside, sr)) if not sr.is_empty else False,
    }


def case_b(s=GRID_S, scale_to_metres=False):
    """MS-0007 passes 0.30 mm outside a GP-0001 vertex."""
    h = read_handover()
    dig, ms = shapely_wkt.loads(h["GP-0001"]), shapely_wkt.loads(h["MS-0007"])
    stock = {
        "intersects": bool(ms.intersects(dig)),
        "intersection_wkt": shapely.to_wkt(ms.intersection(dig), rounding_precision=-1),
        "distance_mm": float(ms.distance(dig)),
        "sr_intersection_wkt": shapely.to_wkt(shapely.intersection(ms, dig, grid_size=1), rounding_precision=-1),
        "reduced_intersects": bool(shapely.set_precision(ms, 1).intersects(shapely.set_precision(dig, 1))),
    }
    ring = vk.coords_from_wkt_text(h["GP-0001"])
    m0, m1 = vk.coords_from_wkt_text(h["MS-0007"])
    f = Fraction(1, 1000) if scale_to_metres else Fraction(1)
    if scale_to_metres:  # the same geometry in metres, exactly
        ring = [(x * f, y * f) for x, y in ring]
        m0, m1 = (m0[0] * f, m0[1] * f), (m1[0] * f, m1[1] * f)
    verts = ring[:-1]
    vs = vk.snap_many([v for p in verts for v in p], s)
    centres = [(vs[2 * k][0], vs[2 * k + 1][0]) for k in range(len(verts))]
    vdisp = [(vs[2 * k][1], vs[2 * k + 1][1]) for k in range(len(verts))]
    pv = vk.passes_many([(m0, m1, c) for c in centres], s)
    hit = [k for k, p in enumerate(pv) if p]
    # TESTED: exact distance of the hit vertex from the cable line (Fraction)
    (x0, y0), (x1, y1) = m0, m1
    gap2 = []
    for k in hit:
        vx, vy = verts[k]
        cr = (x1 - x0) * (vy - y0) - (y1 - y0) * (vx - x0)
        gap2.append(cr * cr / ((x1 - x0) ** 2 + (y1 - y0) ** 2) / (f * f))
    return {
        "stock": stock,
        "vertex_passes": pv,
        "vertex_hit": hit,
        "hot_pixel_centre": [[_s(centres[k][0]), _s(centres[k][1])] for k in hit],
        "vertex_snap_disp_mm": [[_s(vdisp[k][0] / f), _s(vdisp[k][1] / f)] for k in hit],
        "bound_mm": _s(HALF / s / f),
        "vertex_gap_mm_float": [float(g) ** 0.5 for g in gap2],
    }


# --------------------------------------------------------------------------
# C: corner clip (cases/caseC.wkt)
# --------------------------------------------------------------------------

def case_c(s=GRID_S, scale_to_metres=False):
    dtext, ctext = _read_pairs(CASE_C)[0]
    d, c = shapely_wkt.loads(dtext), shapely_wkt.loads(ctext)
    inter = c.intersection(d)
    stock = {"intersects": bool(c.intersects(d)), "relate": d.relate(c),
             "relate_interior_interior": d.relate(c)[0], "covers": bool(d.covers(inter)),
             "intersection_wkt": shapely.to_wkt(inter, rounding_precision=-1),
             "intersection_length_mm": inter.length}

    ring = vk.coords_from_wkt_text(dtext)
    c0, c1 = vk.coords_from_wkt_text(ctext)
    f = Fraction(1, 1000) if scale_to_metres else Fraction(1)
    if scale_to_metres:
        ring = [(x * f, y * f) for x, y in ring]
        c0, c1 = (c0[0] * f, c0[1] * f), (c1[0] * f, c1[1] * f)
    corners = ring[:-1]
    corner_pass = vk.passes_many([(c0, c1, v) for v in corners], s)
    nodes = [n for n in vk.intersections_many([(c0, c1, e0, e1) for e0, e1 in _edges(ring)]) if n]
    snaps = vk.snap_many([v for n in nodes for v in n], s)
    snapped = [(snaps[2 * i][0], snaps[2 * i + 1][0]) for i in range(len(nodes))]
    disps = [(snaps[2 * i][1], snaps[2 * i + 1][1]) for i in range(len(nodes))]
    hit = [i for i, p in enumerate(corner_pass) if p]
    return {
        "stock": stock,
        "corner_passes": corner_pass,
        "corner_hit": hit,
        "corner_hit_xy": [[_s(corners[i][0]), _s(corners[i][1])] for i in hit],
        "exact_nodes": [[_s(x), _s(y)] for x, y in nodes],
        "exact_nodes_float": [[float(x), float(y)] for x, y in nodes],
        "snapped_nodes": [[_s(x), _s(y)] for x, y in snapped],
        "snap_disp_mm": [[_s(a / f), _s(b / f)] for a, b in disps],
        "max_disp_mm": _s(max(max(a, b) for a, b in disps) / f),
        "bound_mm": _s(HALF / s / f),
        "snapped_on_corner": [p == corners[hit[0]] for p in snapped] if hit else [],
    }


def metre_float_hazard():
    """TESTED: metre text of a mm grid node is not a binary64 value."""
    dtext, _ = _read_pairs(CASE_C)[0]
    x_mm = int(vk.coords_from_wkt_text(dtext)[1][0])
    exact = Fraction(x_mm, 1000)
    as_double = Fraction(float(exact))
    return {"x_mm": str(x_mm), "x_m_exact": f"{x_mm // 1000}.{x_mm % 1000:03d}",
            "x_m_double_error_pm": float(abs(as_double - exact) * 10**12),
            "double_exact": as_double == exact}


# --------------------------------------------------------------------------
# recorded runs
# --------------------------------------------------------------------------

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
    return {
        "shapely_version": shapely.__version__,
        "geos_version": shapely.geos_version_string,
        "data_label": "SYNTHETIC, KLIC-shaped (IMKL structure, RD New EPSG:28992), millimetres",
        "theorems": THEOREMS,
        "caseA": case_a(),
        "randomA": random_a(_read_pairs(PAIRS)),
        "caseB": case_b(),
        "caseB_metres_s1000": case_b(s=1000, scale_to_metres=True),
        "caseC": case_c(),
        "caseC_metres_s1000": case_c(s=1000, scale_to_metres=True),
        "metre_float_hazard": metre_float_hazard(),
        "stock_recorded": load_stock(),
        "stock_recorded_real": load_stock(STOCK_REAL),
        "real": real_summary(),
    }


# --------------------------------------------------------------------------
# report
# --------------------------------------------------------------------------

def _yn(v):
    return "True " if v else "False"


def report(res) -> str:
    A, Ar, B, Bm, C, Cm, H = (res[k] for k in ("caseA", "randomA", "caseB", "caseB_metres_s1000",
                                                 "caseC", "caseC_metres_s1000", "metre_float_hazard"))
    L = []
    L.append(f"KLIC hot-pixel demo  |  Shapely {res['shapely_version']} / GEOS {res['geos_version']}")
    L.append(f"data: {res['data_label']}")
    L.append("")
    s = A["stock"]
    L.append("CASE A  LS-0042 crosses dig polygon GP-0001                    [TESTED, stock]")
    L.append(f"  cable.intersects(dig)                 = {s['intersects']}")
    L.append(f"  dig.covers(cable ∩ dig)               = {s['covers']}   within = {s['within']}")
    L.append(f"  crossing points on the cable          = {s['points_on_cable']}")
    L.append(f"  crossing points on the dig boundary   = {s['points_on_boundary']}")
    L.append(f"  crossing points vs exact node         = {', '.join(f'{e:.1f} pm' for e in A['geos_point_error_pm'])}")
    L.append(f"  snap-rounded (1 mm): set_precision(dig).covers(SR ∩) = {s['sr_covers']}")
    L.append("CASE A  verified                                              [PROVED per answer]")
    for ex, sn, dd, pp in zip(A["exact_nodes_float"], A["snapped_nodes"], A["snap_disp_mm"], A["passes_cable_and_edge"]):
        L.append(f"  node exact ({ex[0]:.6f}, {ex[1]:.6f}) -> grid ({sn[0]}, {sn[1]})"
                 f"  |d| = ({_dec(dd[0])}, {_dec(dd[1])}) mm  passes(cable)={pp[0]} passes(edge)={pp[1]}")
    L.append(f"  max displacement {_dec(A['max_disp_mm'])} mm <= {A['bound_mm']} mm ({THEOREMS['bound']})")
    L.append(f"  [TESTED] noded 1 mm dig polygon valid = {A['tested_noded_dig_valid']}, covers verified inside part"
             f" = {A['tested_noded_dig_covers_inside']}; inside part equals GEOS SR result = {A['tested_inside_equals_geos_sr']}")
    L.append("")
    L.append("CASE A*  the same covers() check on 3000 random pairs          [TESTED, stock]")
    L.append(f"  GEOS: covers = False on {Ar['stock_covers_false']}/{Ar['pairs']} pairs;"
             f" node error vs exact: max {Ar['geos_max_node_error_pm']:.1f} pm (picometres: not badly wrong)")
    L.append(f"  verified: {Ar['verified_nodes']} nodes, max |d| {_dec(Ar['verified_max_disp_mm'])} mm <= ½ mm;"
             f" cable and dig edge share the node pixel {Ar['verified_hotpixel_both']}/{Ar['verified_nodes']}"
             "   [PROVED per answer]")
    L.append("")
    s = B["stock"]
    L.append("CASE B  MS-0007 passes 0.30 mm outside a GP-0001 vertex          [TESTED, stock]")
    L.append(f"  ms.intersects(dig)                           = {s['intersects']}   (distance {s['distance_mm']:.6f} mm)")
    L.append(f"  intersection(ms, dig, grid_size=1)           = {s['sr_intersection_wkt']}")
    L.append(f"  set_precision(ms,1).intersects(set_precision(dig,1)) = {s['reduced_intersects']}")
    L.append("  -> at 1 mm precision, two calls say 'no contact' and one returns a contact point; no bound")
    L.append("CASE B  verified                                              [PROVED per answer]")
    L.append(f"  MS-0007 passes through the 1 mm hot pixel of vertex {B['vertex_hit']} at {B['hot_pixel_centre']}"
             f"  (all vertices: {B['vertex_passes']})")
    L.append(f"  vertex -> pixel centre |d| = {[[_dec(a), _dec(b)] for a, b in B['vertex_snap_disp_mm']]} mm <= ½ mm;"
             f" exact vertex-to-cable gap {[f'{g:.6f}' for g in B['vertex_gap_mm_float']]} mm [TESTED]")
    L.append("  -> a snap-rounding noder must node MS-0007 at that vertex: one answer, displacement <= ½ mm/coord")
    L.append("")
    s = C["stock"]
    L.append("CASE C  a cable clips a dig corner 0.296 mm deep              [TESTED, stock]")
    L.append(f"  cable.intersects(dig) = {s['intersects']}; dig.relate(cable)[int/int] = {s['relate_interior_interior']}"
             f" ({s['relate']}); dig.covers(cable ∩ dig) = {s['covers']}  (the returned {s['intersection_length_mm']:.3f} mm piece)")
    L.append("CASE C  verified                                              [PROVED per answer]")
    L.append(f"  cable passes through corner pixel(s) {C['corner_hit']} at {C['corner_hit_xy']}")
    for ex, sn, dd, oc in zip(C["exact_nodes_float"], C["snapped_nodes"], C["snap_disp_mm"], C["snapped_on_corner"]):
        L.append(f"  node exact ({ex[0]:.6f}, {ex[1]:.6f}) -> grid ({sn[0]}, {sn[1]})"
                 f"  |d| = ({_dec(dd[0])}, {_dec(dd[1])}) mm{'  = the corner' if oc else ''}")
    L.append(f"  max displacement {_dec(C['max_disp_mm'])} mm <= {C['bound_mm']} mm")
    L.append("")
    L.append("UNIT SCALE  cases B and C in metres, s = 1000 (1 mm grid)    [PROVED per answer]")
    L.append(f"  B: vertex passes {Bm['vertex_passes']} (mm run: {B['vertex_passes']}); pixel centre {Bm['hot_pixel_centre']} m")
    L.append(f"  C: corner hit {Cm['corner_hit']}, snapped nodes {Cm['snapped_nodes']} m, max |d| {_dec(Cm['max_disp_mm'])} mm")
    L.append(f"  metre text {H['x_m_exact']} as a binary64: off by {H['x_m_double_error_pm']:.3f} pm"
             f" (exact: {H['double_exact']})   [TESTED] -> metres are parsed as exact decimals")
    L.append("")
    st = res["stock_recorded"]
    if st:
        L.append(f"STOCK TOOLS  recorded run {st['run_utc']} (stock/run_all.py)          [TESTED]")
        L.append(f"  {'tool':<8} {'A covers':<9} {'A pts on cable':<15} {'A* covers=F':<12} "
                 f"{'B intersects':<13} {'B SR ∩':<28} {'B reduced':<10} {'C covers':<8}")
        for r in st["results"]:
            if r.get("status") != "ok":
                L.append(f"  {r['tool']:<8} not run: {r.get('reason', '')}")
                continue
            a, b, c, ra = r["caseA"], r["caseB"], r["caseC"], r["randomA"]
            L.append(f"  {r['tool']:<8} {_yn(a['covers']):<9} {str(a['points_on_cable']):<15} "
                     f"{ra['covers_false']:>4}/{ra['pairs']:<7} {_yn(b['intersects']):<13} "
                     f"{b['sr_intersection'].replace('POINT(', 'POINT ('):<28} {_yn(b['reduced_intersects']):<10} {_yn(c['covers'])}")
        L.append("  versions: " + "; ".join(r["version"] for r in st["results"] if r.get("status") == "ok"))
    else:
        L.append("STOCK TOOLS  no recorded run (python stock/run_all.py)")
    R, SR = res["real"], res["stock_recorded_real"]
    if R:
        L.append("")
        L.append(f"REAL DATA  {R['deliveries']} public Kadaster example deliveries, {R['lines']} utility lines")
        L.append(f"  source: {R['source']}")
        L.append(f"  verified: dig-vertex hot-pixel passes {R['verified_dig_vertex_hotpixel_passes']};"
                 f" {R['verified_exact_nodes']} exact nodes, max snap displacement"
                 f" {_dec(Fraction(R['verified_max_disp_m']) * 1000)} mm <= 0.5 mm   [PROVED per answer]")
        if SR:
            for r in SR["results"]:
                a = r["randomA"]
                L.append(f"  {r['tool']:<8} {r['version']:<52} covers=False {a['covers_false']:>4}/{a['pairs']}"
                         f"  (empty ∩ {a['pairs'] - a['nonempty']})   [TESTED]")
    L.append("")
    L.append("Proved = Qed in theories-flocq/HotPixel_Q_exec.v, standard classical axioms only")
    L.append("(proof_audit/print_assumptions.txt).  Scope: node placement + hot-pixel passing,")
    L.append("not a verified overlay.")
    return "\n".join(L)


# --------------------------------------------------------------------------
# figure
# --------------------------------------------------------------------------

def _zoom_panel(ax, title, centre, polys, lines, pixel, marks, note, note_color):
    from matplotlib.patches import Rectangle
    cx_, cy_ = centre
    relq = lambda p: (float(p[0] - cx_), float(p[1] - cy_))  # noqa: E731
    view = shapely.box(-3, -3, 3, 3)
    for g in range(-3, 4):
        ax.axhline(g, color="#e3e3e3", lw=0.6, zorder=0)
        ax.axvline(g, color="#e3e3e3", lw=0.6, zorder=0)
    ax.add_patch(Rectangle((float(pixel[0] - cx_) - 0.5, float(pixel[1] - cy_) - 0.5), 1, 1,
                           fc="#f2c94c55", ec="#b7950b", lw=1.2, zorder=1, label="hot pixel (1 mm)"))
    for ring, lab in polys:
        p = shapely.Polygon([relq(q) for q in ring]).intersection(view)
        if not p.is_empty:
            x, y = p.exterior.xy
            ax.fill(x, y, fc="#3b82f622", ec="#1d4ed8", lw=1.6, label=lab, zorder=2)
    for pts, lab, col, lw, alpha in lines:
        g = shapely.LineString([relq(q) for q in pts]).intersection(view)
        if not g.is_empty:
            x, y = g.xy
            ax.plot(x, y, color=col, lw=lw, alpha=alpha, label=lab, zorder=3)
    for pts, style, lab in marks:
        for i, q in enumerate(pts):
            x, y = relq(q)
            ax.plot(x, y, **style, zorder=5, label=lab if i == 0 else None)
    ax.set_xlim(-2.2, 2.2)
    ax.set_ylim(-2.2, 2.2)
    ax.set_aspect("equal")
    ax.set_xlabel(f"mm from pixel centre (RD x ≈ {float(cx_):.0f} mm)", fontsize=8)
    ax.set_ylabel(f"mm (RD y ≈ {float(cy_):.0f} mm)", fontsize=8)
    ax.set_title(title, fontsize=10)
    ax.legend(loc="lower left", fontsize=6.8, framealpha=0.95)
    ax.text(0.02, 0.98, note, transform=ax.transAxes, va="top", fontsize=7.2, family="monospace",
            color=note_color, bbox=dict(fc="white", ec=note_color, lw=0.8))


def figure(res, path):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    A, B, C = res["caseA"], res["caseB"], res["caseC"]
    h = read_handover()
    dig = vk.coords_from_wkt_text(h["GP-0001"])
    ls = vk.coords_from_wkt_text(h["LS-0042"])
    ms = vk.coords_from_wkt_text(h["MS-0007"])
    F = lambda xy: (Fraction(xy[0]), Fraction(xy[1]))  # noqa: E731

    fig = plt.figure(figsize=(15, 8.4), dpi=110)
    gs = fig.add_gridspec(2, 3, height_ratios=[1, 0.42])

    # A: first node
    nA = F(A["snapped_nodes"][0])
    _zoom_panel(fig.add_subplot(gs[0, 0]), "A · LS-0042 crosses GP-0001 (node 1)", nA,
                [(dig, "dig polygon GP-0001")],
                [(ls, "cable LS-0042", "#c0392b", 1.6, 1)], nA,
                [([F(A["exact_nodes"][0])], dict(marker="o", mfc="white", mec="black", ms=6), "exact node (ℚ, kernel)"),
                 ([nA], dict(marker="s", color="black", ms=7), "snapped node (kernel)")],
                "STOCK: covers(∩)=%s, crossing pts on cable=%s\nPROVED: passes(cable)=%s passes(edge)=%s\n|d| ≤ ½ mm (q_snap_disp_bound)"
                % (A["stock"]["covers"], A["stock"]["points_on_cable"], *A["passes_cable_and_edge"][0]), "#333")

    # B: vertex pass
    cB = F(B["hot_pixel_centre"][0])
    vB = dig[B["vertex_hit"][0]]
    _zoom_panel(fig.add_subplot(gs[0, 1]), "B · MS-0007 passes 0.30 mm outside a vertex", cB,
                [(dig, "dig polygon GP-0001")],
                [(ms, "cable MS-0007", "#c0392b", 1.6, 1)], cB,
                [([vB], dict(marker="o", color="#555", ms=6), "dig vertex (input)"),
                 ([cB], dict(marker="s", color="black", ms=7), "hot-pixel centre (kernel snap)")],
                "STOCK: intersects=%s\n  intersection(grid_size=1)=POINT\n  set_precision(..).intersects=%s\nPROVED: passes through pixel = True"
                % (B["stock"]["intersects"], B["stock"]["reduced_intersects"]), "#333")

    # C: corner clip
    dtext, ctext = _read_pairs(CASE_C)[0]
    cC = F(C["corner_hit_xy"][0])
    gpts = _geos_points(shapely_wkt.loads(C["stock"]["intersection_wkt"]))
    _zoom_panel(fig.add_subplot(gs[0, 2]), "C · cable clips a corner 0.30 mm deep", cC,
                [(vk.coords_from_wkt_text(dtext), "dig polygon")],
                [(vk.coords_from_wkt_text(ctext), "cable", "#c0392b", 1.6, 1),
                 (gpts, "GEOS cable ∩ dig", "#16a34a", 4, 0.7)], cC,
                [([F(p) for p in C["exact_nodes"]], dict(marker="o", mfc="white", mec="black", ms=6), "exact nodes (ℚ)"),
                 ([F(p) for p in C["snapped_nodes"]], dict(marker="s", color="black", ms=7), "snapped nodes")],
                "STOCK: intersects=%s relate II=%s\n  covers(∩)=%s\nPROVED: passes corner pixel; |d| ≤ ½ mm"
                % (C["stock"]["intersects"], C["stock"]["relate_interior_interior"], C["stock"]["covers"]), "#333")

    ax3 = fig.add_subplot(gs[1, :])
    ax3.axis("off")
    st = res["stock_recorded"]
    real = {r["tool"]: r for r in res["stock_recorded_real"]["results"]} if res["stock_recorded_real"] else {}
    rows = []
    for r in (st["results"] if st else []):
        if r.get("status") != "ok":
            rows.append([r["tool"], "not run: " + r.get("reason", "")] + [""] * 8)
            continue
        a, b, c, ra = r["caseA"], r["caseB"], r["caseC"], r["randomA"]
        rr = real.get(r["tool"], {}).get("randomA")
        rows.append([r["tool"], r["version"].replace(" (compatible with JTS 1.20.0)", ""),
                     str(a["covers"]), "/".join("T" if v else "F" for v in a["points_on_cable"]),
                     f"{ra['covers_false']}/{ra['pairs']}",
                     str(b["intersects"]), "POINT" if "POINT" in b["sr_intersection"] else b["sr_intersection"],
                     str(b["reduced_intersects"]), str(c["covers"]),
                     f"{rr['covers_false']}/{rr['pairs']}" if rr else "—"])
    R = res["real"]
    rows.append(["verified kernel", "HotPixel_Q_exec.v (Qed) → OCaml", "n/a", "nodes ≤ ½ mm",
                 "n/a", "passes vertex pixel", "—", "—", "n/a",
                 f"{R['verified_dig_vertex_hotpixel_passes']} vertex passes" if R else "—"])
    tab = ax3.table(cellText=rows,
                    colLabels=["tool", "version (as printed)", "A: covers(∩)", "A: pts on cable",
                               "A*: covers=False", "B: intersects", "B: ∩ at 1 mm", "B: reduced ∩s",
                               "C: covers(∩)", "Kadaster: covers=False"],
                    loc="upper center", cellLoc="left",
                    colWidths=[0.08, 0.21, 0.07, 0.08, 0.09, 0.09, 0.07, 0.08, 0.07, 0.13])
    tab.auto_set_font_size(False)
    tab.set_fontsize(7.8)
    tab.scale(1, 1.4)
    when = st["run_utc"] if st else "—"
    ax3.set_title(f"Per-tool results on the same inputs (TESTED; recorded run {when}). A*: 3000 random pairs. "
                  "Last column: 24 public Kadaster KLIC example deliveries.", fontsize=9, loc="left")
    fig.suptitle("KLIC dig polygon × cable near a hot pixel — stock tools vs the Rocq-extracted kernel "
                 "(1 grid unit = 1 mm)", fontsize=12, weight="bold")
    fig.text(0.01, 0.01, "Cases A–C: SYNTHETIC KLIC-shaped data (RD mm). PROVED = Qed theorems in HotPixel_Q_exec.v; "
             "not a verified overlay. NetTopologySuite.Proofs contributors, BSD-3-Clause; co-authored with Claude.",
             fontsize=7.5, color="#555")
    fig.tight_layout(rect=(0, 0.02, 1, 0.97))
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
