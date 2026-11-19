#!/usr/bin/env python3
"""Generate the SYNTHETIC KLIC-shaped inputs for the demo (deterministic).

Everything is in millimetres at Dutch RD (EPSG:28992) magnitudes
(x ~ 1.55e8 mm, y ~ 4.63e8 mm), and every coordinate is an INTEGER number of
millimetres -- the precision of an IMKL delivery written in metres with three
decimals.  So all input vertices already lie on the 1 mm grid; the hot-pixel
cases come from where segments run, not from sub-mm input noise.

Outputs (tool-neutral WKT, one record per line, fields separated by ';'):

  cases/caseA_pairs.wkt   3000 lines  "<dig polygon>;<cable linestring>"
  cases/caseB.wkt         1 line      "<dig polygon>;<cable linestring>"
                          the cable clips a dig-polygon corner ~0.3 mm deep
  data/klic_synthetic_mm.wkt  a small "delivery" for the figure:
                          line 1 the dig polygon, then one cable per line

This is synthetic data.  It is shaped like a KLIC delivery (a dig polygon,
long straight cable segments, RD millimetre coordinates); it is not one.
"""
from __future__ import annotations

import math
import random
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
X0, Y0 = 155_000_000, 463_000_000  # RD origin of the synthetic area, mm
SEED_A = 20261119
N_PAIRS = 3000


def mm(v: float) -> int:
    return int(round(v))


def rect(cx, cy, w, h, a):
    ca, sa = math.cos(a), math.sin(a)
    return [(mm(cx + ca * dx - sa * dy), mm(cy + sa * dx + ca * dy))
            for dx, dy in [(-w / 2, -h / 2), (w / 2, -h / 2), (w / 2, h / 2), (-w / 2, h / 2)]]


def poly_wkt(pts) -> str:
    ring = pts + [pts[0]]
    return "POLYGON ((" + ", ".join(f"{x} {y}" for x, y in ring) + "))"


def line_wkt(pts) -> str:
    return "LINESTRING (" + ", ".join(f"{x} {y}" for x, y in pts) + ")"


def case_a_pairs():
    rnd = random.Random(SEED_A)
    out = []
    for _ in range(N_PAIRS):
        cx = X0 + rnd.uniform(0, 1e6)
        cy = Y0 + rnd.uniform(0, 1e6)
        w, h = rnd.uniform(5e3, 30e3), rnd.uniform(3e3, 15e3)
        a = rnd.uniform(0, math.pi)
        dig = rect(cx, cy, w, h, a)
        b = rnd.uniform(0, math.pi)
        off = rnd.uniform(-h / 3, h / 3)
        px, py = cx - math.sin(a) * off, cy + math.cos(a) * off
        L = 60e3
        cable = [(mm(px - math.cos(b) * L / 2), mm(py - math.sin(b) * L / 2)),
                 (mm(px + math.cos(b) * L / 2), mm(py + math.sin(b) * L / 2))]
        out.append((dig, cable))
    return out


def cross_and_len2(v, p0, p1):
    """Exact integer cross product (p1-p0) x (v-p0) and squared length |p1-p0|^2.
    The signed distance of v from the line is cross / sqrt(len2)."""
    (x0, y0), (x1, y1), (vx, vy) = p0, p1, v
    cross = (x1 - x0) * (vy - y0) - (y1 - y0) * (vx - x0)
    return cross, (x1 - x0) ** 2 + (y1 - y0) ** 2


def case_b():
    """A 20 m x 10 m dig polygon (integer-mm vertices) and a 40 m cable with
    integer-mm endpoints whose line clips corner 1 between 0.29 and 0.31 mm
    deep.  Deterministic search; the first hit is taken."""
    cx, cy = X0 + 512_345, Y0 + 287_654
    dig = rect(cx, cy, 20_000, 10_000, 0.4363323129985824)  # 25 degrees
    vx, vy = dig[1]
    # outward bisector at corner 1, and the tangent direction
    ox, oy = vx - cx, vy - cy
    n = math.hypot(ox, oy)
    ox, oy = ox / n, oy / n
    tx, ty = -oy, ox
    for k in range(1, 20000):
        depth = 0.30 + 0.0001 * ((k % 200) - 100)  # sweep 0.29 .. 0.31
        px, py = vx - ox * depth, vy - oy * depth
        L0, L1 = 20_000 + 7 * k, 20_000 + 13 * k
        p0 = (mm(px - tx * L0), mm(py - ty * L0))
        p1 = (mm(px + tx * L1), mm(py + ty * L1))
        # exact depth of the vertex beyond the cable line (inside = vertex is
        # on the far side from the polygon centre)
        c_v, len2 = cross_and_len2((vx, vy), p0, p1)
        c_c, _ = cross_and_len2((mm(cx), mm(cy)), p0, p1)
        # depth^2 = c_v^2 / len2, compared exactly against 0.29^2 .. 0.31^2
        d2 = Fraction(c_v * c_v, len2)
        if c_v * c_c < 0 and Fraction(29, 100) ** 2 <= d2 <= Fraction(31, 100) ** 2:
            return dig, [p0, p1], d2
    raise SystemExit("case B search failed")


def delivery(dig_b, cable_b):
    rnd = random.Random(SEED_A + 1)
    xs = [p[0] for p in dig_b]
    ys = [p[1] for p in dig_b]
    cx, cy = sum(xs) / 4, sum(ys) / 4
    cables = [cable_b]
    for _ in range(7):
        b = rnd.uniform(0, math.pi)
        off = rnd.uniform(-4e3, 4e3)
        px, py = cx + math.cos(b + math.pi / 2) * off, cy + math.sin(b + math.pi / 2) * off
        L = 36e3
        cables.append([(mm(px - math.cos(b) * L / 2), mm(py - math.sin(b) * L / 2)),
                       (mm(px + math.cos(b) * L / 2), mm(py + math.sin(b) * L / 2))])
    return cables


def m_text(v_mm: int) -> str:
    """Integer millimetres as exact metre text with three decimals."""
    sign = "-" if v_mm < 0 else ""
    v = abs(v_mm)
    return f"{sign}{v // 1000}.{v % 1000:03d}"


def imkl_fixture(dig, cables) -> str:
    """A SYNTHETIC GML file shaped like an IMKL 2.x delivery fragment (dig
    polygon + utility-link centrelines, EPSG:28992 metres, 3 decimals).  For
    testing imkl_loader.py only; it is not Kadaster data and not schema-valid
    IMKL."""
    def poslist(pts):
        return " ".join(f"{m_text(x)} {m_text(y)}" for x, y in pts)
    ring = dig + [dig[0]]
    members = [f"""  <gml:featureMember>
    <imkl:Graafpolygoon gml:id="gp-1">
      <imkl:geometrie>
        <gml:Polygon gml:id="gp-1-g" srsName="urn:ogc:def:crs:EPSG::28992" srsDimension="2">
          <gml:exterior><gml:LinearRing><gml:posList>{poslist(ring)}</gml:posList></gml:LinearRing></gml:exterior>
        </gml:Polygon>
      </imkl:geometrie>
    </imkl:Graafpolygoon>
  </gml:featureMember>"""]
    for i, c in enumerate(cables):
        members.append(f"""  <gml:featureMember>
    <us-net-el:ElectricityCable gml:id="cable-{i}">
      <net:centrelineGeometry>
        <gml:LineString gml:id="cable-{i}-g" srsName="urn:ogc:def:crs:EPSG::28992" srsDimension="2">
          <gml:posList>{poslist(c)}</gml:posList>
        </gml:LineString>
      </net:centrelineGeometry>
    </us-net-el:ElectricityCable>
  </gml:featureMember>""")
    return ("""<?xml version="1.0" encoding="UTF-8"?>
<!-- SYNTHETIC test fixture for tools/klic-demo/imkl_loader.py, generated by
     make_data.py.  Shaped like an IMKL 2.x delivery fragment; NOT Kadaster
     data, NOT schema-valid IMKL. -->
<gml:FeatureCollection xmlns:gml="http://www.opengis.net/gml/3.2"
    xmlns:imkl="http://www.geostandaarden.nl/imkl/wibon"
    xmlns:net="http://inspire.ec.europa.eu/schemas/net/4.0"
    xmlns:us-net-el="http://inspire.ec.europa.eu/schemas/us-net-el/4.0">
""" + "\n".join(members) + "\n</gml:FeatureCollection>\n")


def main():
    (HERE / "cases").mkdir(exist_ok=True)
    (HERE / "data").mkdir(exist_ok=True)
    with open(HERE / "cases" / "caseA_pairs.wkt", "w", newline="\n") as f:
        for dig, cable in case_a_pairs():
            f.write(f"{poly_wkt(dig)};{line_wkt(cable)}\n")
    dig_b, cable_b, depth = case_b()
    with open(HERE / "cases" / "caseB.wkt", "w", newline="\n") as f:
        f.write(f"{poly_wkt(dig_b)};{line_wkt(cable_b)}\n")
    with open(HERE / "data" / "klic_synthetic_mm.wkt", "w", newline="\n") as f:
        f.write(poly_wkt(dig_b) + "\n")
        for c in delivery(dig_b, cable_b):
            f.write(line_wkt(c) + "\n")
    (HERE / "tests" / "fixtures").mkdir(parents=True, exist_ok=True)
    with open(HERE / "tests" / "fixtures" / "synthetic_imkl.xml", "w", newline="\n") as f:
        f.write(imkl_fixture(dig_b, delivery(dig_b, cable_b)))
    print(f"case B corner clip depth^2 (exact) = {depth} mm^2 (depth ~ {math.sqrt(depth):.6f} mm)")


if __name__ == "__main__":
    main()
