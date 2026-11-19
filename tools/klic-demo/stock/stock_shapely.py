#!/usr/bin/env python3
"""klic-demo stock run on Shapely / GEOS.  Same predicates as the JTS, NTS and
PostGIS runners in this directory.

  case A: for each (dig, cable) pair, inter = cable.intersection(dig);
          count pairs where dig.covers(inter) is False.
  case B: cable.intersects(dig), dig.relate(cable), dig.covers(cable ∩ dig).

Usage: python stock_shapely.py <caseA_pairs.wkt> <caseB.wkt>   (one JSON line)
BSD-3-Clause, NetTopologySuite.Proofs contributors.
"""
from __future__ import annotations

import json
import platform
import sys

import shapely
from shapely import wkt


def run(a_path: str, b_path: str) -> dict:
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
    return {
        "tool": "Shapely",
        "version": f"Shapely {shapely.__version__} / GEOS {shapely.geos_version_string}",
        "runtime": f"Python {platform.python_version()}",
        "caseA": {"pairs": n, "nonempty": nonempty, "covers_false": covers_false},
        "caseB": {"intersects": bool(c.intersects(d)), "relate": d.relate(c),
                  "covers": bool(d.covers(inter)),
                  "intersection": shapely.to_wkt(inter, rounding_precision=-1)},
    }


if __name__ == "__main__":
    print(json.dumps(run(sys.argv[1], sys.argv[2])))
