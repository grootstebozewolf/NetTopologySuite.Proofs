#!/usr/bin/env python3
"""Run the hot-pixel analysis on a real IMKL (KLIC) GML delivery, locally.

  python tools/klic-demo/imkl_loader.py <delivery.xml | delivery-dir> [--json out.json]
         [--grid-mm 1] [--dig-regex graafpolygoon] [--show-locations]

Designed for CONFIDENTIAL deliveries: everything runs on this machine (the
verified kernel is a local OCaml binary; Shapely is local), nothing is sent
anywhere, and by default the report contains counts only -- no coordinates.
Pass --show-locations to list RD coordinates of the hot-pixel cases.

Reading the GML
  * Coordinates are taken from the TEXT of gml:posList / gml:pos /
    gml:coordinates as exact decimals (Fraction), never via float, so the
    delivery's metres (EPSG:28992) are used exactly.  srsDimension 3 is
    accepted; the third ordinate is dropped.
  * Dig polygon(s): every gml:Polygon (exterior ring) inside an element whose
    local name matches --dig-regex (default: graafpolygoon, case-insensitive).
  * Utility lines: every gml:LineString / gml:LineStringSegment of a feature
    (the child of the GML member element) whose local name matches
    --line-feature-regex (default: utilitylink, i.e. us-net-common:UtilityLink
    net:centrelineGeometry).  Annotatie / Maatvoering lines are skipped.
    Use --line-feature-regex '' to take every line.
  The element names follow IMKL 2.x as published by Geonovum; if a delivery
  uses other names, adjust --dig-regex.  Parsing uses the standard-library
  XML parser, which does not fetch external entities.

What is reported (per dig polygon, all lines)
  PROVED per answer (extracted Rocq kernel, HotPixel_Q_exec.v, s = 1000/grid):
    - hot-pixel cases: line segments that pass through the hot pixel of a
      dig-polygon vertex (q_passes_through_closed_reflect) without the vertex
      being one of their endpoints -- the case-B situation
    - exact line x dig-edge nodes (q_seg_intersection_sound), their 1 mm grid
      positions and the max displacement (<= 1/2 mm, q_snap_disp_bound)
  TESTED (stock Shapely/GEOS, version printed):
    - lines where dig.covers(line ∩ dig) is False (the case-A situation)
    - lines where intersects / relate / covers(∩) disagree (case B)

BSD-3-Clause, NetTopologySuite.Proofs contributors.  Co-authored with Claude.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import xml.etree.ElementTree as ET
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import verified_hotpixel as vk  # noqa: E402

GML_NS = ("http://www.opengis.net/gml/3.2", "http://www.opengis.net/gml")
MEMBER_NAMES = {"featureMember", "featureMembers", "member", "members"}


def _local(tag: str) -> str:
    return tag.rsplit("}", 1)[-1]


def _ns(tag: str) -> str:
    return tag[1:].split("}", 1)[0] if tag.startswith("{") else ""


def _is_gml(el, name) -> bool:
    return _local(el.tag) == name and _ns(el.tag) in GML_NS


def _dim(el, default=2) -> int:
    v = el.get("srsDimension")
    return int(v) if v else default


def _coords(el, inherited_dim=2):
    """Exact coordinates under a gml geometry element, as [(Fraction, Fraction)]."""
    dim = _dim(el, inherited_dim)
    pts = []
    for sub in el.iter():
        if _is_gml(sub, "posList"):
            d = _dim(sub, dim)
            toks = sub.text.split()
            for i in range(0, len(toks) - d + 1, d):
                pts.append((Fraction(toks[i]), Fraction(toks[i + 1])))
        elif _is_gml(sub, "pos"):
            toks = sub.text.split()
            pts.append((Fraction(toks[0]), Fraction(toks[1])))
        elif _is_gml(sub, "coordinates"):
            cs, ts = sub.get("cs", ","), sub.get("ts", " ")
            for tup in sub.text.strip().split(ts):
                if tup.strip():
                    a = tup.split(cs)
                    pts.append((Fraction(a[0]), Fraction(a[1])))
    return pts


def load_imkl(path, dig_regex="graafpolygoon", line_feature_regex="utilitylink"):
    """Parse one IMKL GML file (or every .xml/.gml in a directory)."""
    p = Path(path)
    files = sorted([*p.glob("**/*.xml"), *p.glob("**/*.gml")]) if p.is_dir() else [p]
    rx = re.compile(dig_regex, re.I)
    lrx = re.compile(line_feature_regex, re.I) if line_feature_regex else None
    digs, lines, srs = [], [], set()
    for f in files:
        root = ET.parse(f).getroot()
        parent = {c: q for q in root.iter() for c in q}

        def ancestors(el):
            while el in parent:
                el = parent[el]
                yield el

        for el in root.iter():
            if el.get("srsName"):
                srs.add(el.get("srsName"))
            if _is_gml(el, "Polygon"):
                if any(rx.search(_local(a.tag)) for a in ancestors(el)):
                    ext = next((s for s in el.iter() if _local(s.tag) == "exterior"), el)
                    ring = _coords(ext, _dim(el))
                    if ring and ring[0] != ring[-1]:
                        ring.append(ring[0])
                    if len(ring) >= 4:
                        digs.append({"file": f.name, "ring": ring})
            elif _is_gml(el, "LineString") or _is_gml(el, "LineStringSegment"):
                anc = list(ancestors(el))
                if any(rx.search(_local(a.tag)) for a in anc):
                    continue
                if _is_gml(el, "LineStringSegment") and any(_is_gml(a, "LineStringSegment") for a in anc):
                    continue
                feature = "unknown"
                for a, nxt in zip(anc, anc[1:]):
                    if _local(nxt.tag) in MEMBER_NAMES:
                        feature = _local(a.tag)
                        break
                if lrx is not None and not lrx.search(feature):
                    continue
                pts = _coords(el, _dim(el))
                if len(pts) >= 2:
                    lines.append({"file": f.name, "feature": feature, "pts": pts})
    return {"files": [str(f) for f in files], "srs": sorted(srs), "digs": digs, "lines": lines}


def _bbox_hits(a, b, c, r):
    """Conservative prefilter: can segment ab touch the closed square of
    half-width r around c?  (Bounding-box test; only skips impossible pairs.)"""
    return (min(a[0], b[0]) <= c[0] + r and max(a[0], b[0]) >= c[0] - r and
            min(a[1], b[1]) <= c[1] + r and max(a[1], b[1]) >= c[1] - r)


def analyse(delivery, grid_m=Fraction(1, 1000), show_locations=False):
    """Hot-pixel analysis of a loaded delivery; coordinates in metres."""
    import shapely
    from shapely.geometry import LineString, Polygon

    s = 1 / grid_m  # scale: grid spacing 1/s metres
    r = grid_m / 2
    out = {"shapely": shapely.__version__, "geos": shapely.geos_version_string,
           "grid_m": str(grid_m), "files": len(delivery["files"]), "srs": delivery["srs"],
           "dig_polygons": len(delivery["digs"]), "lines": len(delivery["lines"]), "per_dig": []}
    for di, dig in enumerate(delivery["digs"]):
        ring = dig["ring"]
        verts = ring[:-1]
        edges = list(zip(ring[:-1], ring[1:]))
        dpoly = Polygon([(float(x), float(y)) for x, y in ring])
        # --- PROVED per answer: vertex hot pixels and nodes -------------
        pass_q, pass_meta = [], []
        inter_q = []
        for li, ln in enumerate(delivery["lines"]):
            for a, b in zip(ln["pts"][:-1], ln["pts"][1:]):
                for vi, v in enumerate(verts):
                    if v in (a, b) or not _bbox_hits(a, b, v, r):
                        continue
                    pass_q.append((a, b, v))
                    pass_meta.append((li, vi))
                for e0, e1 in edges:
                    inter_q.append((a, b, e0, e1))
        passes = vk.passes_many(pass_q, s) if pass_q else []
        hot = [(m, q) for m, q, ok in zip(pass_meta, pass_q, passes) if ok]
        nodes = [n for n in vk.intersections_many(inter_q) if n] if inter_q else []
        snaps = vk.snap_many([c for n in nodes for c in n], s) if nodes else []
        max_disp = max((d for _, d in snaps), default=Fraction(0))
        # --- TESTED: stock GEOS on the same lines ------------------------
        covers_false = disagree = touching = 0
        for ln in delivery["lines"]:
            g = LineString([(float(x), float(y)) for x, y in ln["pts"]])
            if not g.intersects(dpoly):
                continue
            touching += 1
            inter = g.intersection(dpoly)
            cov = dpoly.covers(inter)
            covers_false += not cov
            if dpoly.relate(g)[0] != "F" and not cov:
                disagree += 1
        rec = {
            "dig": di,
            "lines_touching_dig": touching,
            "hotpixel_vertex_passes": len(hot),
            "exact_nodes": len(nodes),
            "max_snap_disp_m": str(max_disp),
            "bound_m": str(r),
            "bound_holds": max_disp <= r,
            "stock_covers_false": covers_false,
            "stock_intersects_relate_covers_disagree": disagree,
        }
        if show_locations:
            rec["hotpixel_cases"] = [
                {"feature": delivery["lines"][li]["feature"], "vertex_rd_m": [str(verts[vi][0]), str(verts[vi][1])]}
                for (li, vi), _ in hot]
        out["per_dig"].append(rec)
    return out


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("delivery")
    ap.add_argument("--grid-mm", default="1", help="grid spacing in millimetres (default 1)")
    ap.add_argument("--dig-regex", default="graafpolygoon")
    ap.add_argument("--line-feature-regex", default="utilitylink")
    ap.add_argument("--json", default=None)
    ap.add_argument("--show-locations", action="store_true")
    a = ap.parse_args(argv)
    d = load_imkl(a.delivery, a.dig_regex, a.line_feature_regex)
    if not d["digs"]:
        print(f"no dig polygon found (elements matching /{a.dig_regex}/i); "
              f"{len(d['lines'])} line geometries read", file=sys.stderr)
        return 2
    res = analyse(d, Fraction(a.grid_mm) / 1000, a.show_locations)
    print(json.dumps(res, indent=2))
    if a.json:
        Path(a.json).write_text(json.dumps(res, indent=2) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
