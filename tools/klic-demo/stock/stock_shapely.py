#!/usr/bin/env python3
"""klic-demo stock run on Shapely / GEOS.  Same predicates as the JTS, NTS and
PostGIS runners in this directory.

  randomA  for each (dig, cable) pair, inter = cable.intersection(dig);
           count pairs where dig.covers(inter) is False.
  caseA    handover LS-0042 x GP-0001: covers / within of cable ∩ dig, and
           whether each computed crossing point lies on the cable and on the
           dig boundary; snap-rounded (1 mm) overlay covers.
  caseB    handover MS-0007, 0.30 mm outside a GP-0001 vertex: intersects,
           intersection, snap-rounded (1 mm) intersection, precision-reduced
           (1 mm) intersects.
  caseC    cable clips a dig corner ~0.3 mm deep: intersects, relate,
           dig.covers(cable ∩ dig).

Usage: python stock_shapely.py <caseA_pairs.wkt> <caseC.wkt> <klic_handover_mm.wkt>
BSD-3-Clause, NetTopologySuite.Proofs contributors.
"""
from __future__ import annotations

import json
import platform
import sys

import shapely
from shapely import wkt


def read_handover(path):
    """GP-0001, LS-0042, MS-0007 from the tab-separated handover file."""
    g = {}
    with open(path) as f:
        for line in f:
            if line.startswith("#") or not line.strip():
                continue
            fid, _typ, _thema, w = line.rstrip("\n").split("\t")
            g[fid] = wkt.loads(w)
    return g["GP-0001"], g["LS-0042"], g["MS-0007"]


def handover(path):
    dig, ls, ms = read_handover(path)
    inter = ls.intersection(dig)
    pts = [shapely.Point(p) for p in shapely.get_coordinates(inter)]
    sr = shapely.intersection(ls, dig, grid_size=1)
    case_a = {"covers": bool(dig.covers(inter)), "within": bool(inter.within(dig)),
              "points_on_cable": [bool(ls.intersects(p)) for p in pts],
              "points_on_boundary": [bool(dig.boundary.intersects(p)) for p in pts],
              "sr_covers": bool(shapely.set_precision(dig, 1).covers(sr))}
    srb = shapely.intersection(ms, dig, grid_size=1)
    case_b = {"intersects": bool(ms.intersects(dig)),
              "intersection_empty": bool(ms.intersection(dig).is_empty),
              "sr_intersection": shapely.to_wkt(srb, rounding_precision=-1),
              "reduced_intersects": bool(shapely.set_precision(ms, 1).intersects(shapely.set_precision(dig, 1)))}
    return case_a, case_b


def run(a_path: str, b_path: str, h_path: str) -> dict:
    n = nonempty = covers_false = 0
    with open(a_path) as f:
        for line in f:
            if not line.strip():
                continue
            d, c = (wkt.loads(t) for t in line.strip().split(";"))
            inter = c.intersection(d)
            n += 1
            nonempty += not inter.is_empty
            covers_false += not d.covers(inter)
    with open(b_path) as f:
        d, c = (wkt.loads(t) for t in f.readline().strip().split(";"))
    inter = c.intersection(d)
    case_a, case_b = handover(h_path)
    return {
        "tool": "Shapely",
        "version": f"Shapely {shapely.__version__} / GEOS {shapely.geos_version_string}",
        "runtime": f"Python {platform.python_version()}",
        "randomA": {"pairs": n, "nonempty": nonempty, "covers_false": covers_false},
        "caseA": case_a,
        "caseB": case_b,
        "caseC": {"intersects": bool(c.intersects(d)), "relate": d.relate(c),
                  "covers": bool(d.covers(inter)),
                  "intersection": shapely.to_wkt(inter, rounding_precision=-1)},
    }


if __name__ == "__main__":
    print(json.dumps(run(sys.argv[1], sys.argv[2], sys.argv[3])))
