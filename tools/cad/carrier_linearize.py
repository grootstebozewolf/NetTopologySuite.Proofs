#!/usr/bin/env python3
"""Any CAD carrier record to linear WKT, with a stated Hausdorff bound.

``glyph_linearize`` covers text rows. This module covers the rest of the
carrier, so every record an extractor writes can reach GIS:

* Chord: a two-point LINESTRING. Exact: the bound is 0.
* Arc and Circle: a LINESTRING (closed for a circle) with its vertices on
  the circle, cut so each chord's sagitta is at most ``d``. Arc angles are
  counter-clockwise from ``startAngle`` to ``endAngle`` in the record's
  OCS, in the record's angle unit, plus ``frameAngle`` when present.
* BulgePolyline: a LINESTRING, closed when the polyline is, its bulge arcs
  cut to sagitta ``d`` as above.
* Compound of Chord and BulgePolyline members (a 2D POLYLINE): one
  LINESTRING through the members in order.
* Bezier: Wang's chord count, decided in rationals.
* BSpline (clamped, polynomial): split into Bezier spans by knot insertion,
  then Wang's count per span. Decreasing knots, or an interior knot
  repeated more often than the degree (a break in the curve), decline. A rational B-spline (weights not all 1)
  declines: Wang's bound is for polynomial curves.
* Ring: a MULTIPOLYGON under its winding rule (nonzero or evenodd), filled
  exactly by ``nonzero_node``. When the flattened contours meet, the result
  is noded and ``hausdorff`` is null, as for text.
* A Compound of glyph members (a text row): ``glyph_linearize``.

Points are placed through the record's link chain, local to world.
``d`` is the record's sagitta tolerance, or a world bound passed as
``hausdorff`` divided by the chain's scale ``k``; the reported bound is
``k*d`` (for exact arithmetic, as in ``glyph_linearize``). Elevation is not
written: the output is 2D.

Declines: Ellipse and Spiral records (their own Linearizes bounds are not
here), Unsupported, a rational B-spline, and a record whose tolerance
states no chord height.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path
from typing import Any

import glyph_linearize
from glyph_linearize import _apply, any_meet, arc_points, bezier_point, chain_scale, wang_count

Decline = tuple[str, str]
Point = tuple[float, float]


def _place(points: list[Point], links: list[dict[str, Any]]) -> list[Point]:
    placed = []
    for point in points:
        for link in links:
            point = _apply(point, link)
        placed.append(point)
    return placed


def _local_d(row: dict[str, Any], hausdorff: float | None) -> float | Decline:
    if hausdorff is not None:
        return hausdorff / chain_scale(row["placement"]["links"])
    tolerance = row["tolerance"]
    if tolerance["kind"] == "sagitta":
        return tolerance["d"]
    return ("ID_ToleranceKindUnsupported", f"{tolerance['kind']} states no chord height")


def circle_points(center: Point, radius: float, start: float, sweep: float, d: float) -> list[Point]:
    """Points from ``start`` through ``sweep`` radians (counter-clockwise), chords of sagitta at most ``d``."""
    step = 2.0 * math.acos(max(-1.0, 1.0 - d / radius)) if d < 2 * radius else math.pi
    count = max(1, math.ceil(sweep / step))
    return [
        (center[0] + radius * math.cos(start + sweep * k / count), center[1] + radius * math.sin(start + sweep * k / count))
        for k in range(count + 1)
    ]


def _segments_points(segments: list[dict[str, Any]], d: float, closed: bool) -> list[Point]:
    points: list[Point] = []
    for segment in segments:
        start, end = tuple(segment["start"]), tuple(segment["end"])
        points.extend(arc_points(start, end, segment["bulge"], d) if segment["kind"] == "Arc" else [start])
    points.append(tuple(segments[0]["start"]) if closed else tuple(segments[-1]["end"]))
    return points


def bezier_spans(degree: int, controls: list[Point], knots: list[float]) -> list[list[Point]]:
    """A clamped B-spline as Bezier spans: insert every interior knot up to multiplicity ``degree`` (Boehm)."""
    points = [tuple(point) for point in controls]
    knots = list(knots)
    for value in sorted(set(knots[degree + 1 : -degree - 1])):
        while knots.count(value) < degree:
            span = max(i for i in range(len(knots) - 1) if knots[i] <= value < knots[i + 1])
            inserted = []
            for i in range(span - degree + 1, span + 1):
                a = (value - knots[i]) / (knots[i + degree] - knots[i])
                p, q = points[i - 1], points[i]
                inserted.append(((1 - a) * p[0] + a * q[0], (1 - a) * p[1] + a * q[1]))
            points = points[: span - degree + 1] + inserted + points[span:]
            knots.insert(span + 1, value)
    return [points[k : k + degree + 1] for k in range(0, len(points) - degree, degree)]


def _bezier_points(controls: list[Point], d: float) -> list[Point]:
    count = wang_count(controls, d)
    return [bezier_point(controls, k / count) for k in range(count + 1)]


def _line(points: list[Point]) -> str:
    return "(" + ", ".join(f"{x!r} {y!r}" for x, y in points) + ")"


def linearize_record(row: dict[str, Any], hausdorff: float | None = None) -> dict[str, Any] | Decline:
    """One carrier entity row as ``{"wkt", "hausdorff", ...}``, or a decline."""
    if hausdorff is not None and not (math.isfinite(hausdorff) and hausdorff > 0):
        return ("ID_ToleranceNonPositive", "hausdorff bound is not a positive finite number")
    if row.get("record") != "entity":
        return ("ID_UnsupportedEntity", "row is not an entity record")
    kind, params, links = row["kind"], row["params"], row["placement"]["links"]
    if kind == "Compound" and any(member["kind"] == "Compound" for member in params["members"]):
        return glyph_linearize.linearize_row(row, hausdorff)
    if kind in ("Ellipse", "Spiral", "Unsupported"):
        return ("ID_UnsupportedEntity", f"{kind} records are not linearized here")
    d = _local_d(row, hausdorff)
    if isinstance(d, tuple):
        return d
    bound = chain_scale(links) * d

    if kind == "Chord":
        points = [tuple(params["start"]), tuple(params["end"])]
        return {"wkt": "LINESTRING " + _line(_place(points, links)), "hausdorff": 0.0}
    if kind in ("Arc", "Circle"):
        center, radius = tuple(params["center"]), params["radius"]
        if kind == "Circle":
            start, sweep = 0.0, 2 * math.pi
        else:
            unit = math.radians if params.get("angleUnit", "degree") == "degree" else float
            start = unit(params["startAngle"]) + params.get("frameAngle", 0.0)
            raw = unit(params["endAngle"]) - unit(params["startAngle"])
            sweep = raw % (2 * math.pi) or (2 * math.pi if abs(raw) > 1e-12 else 0.0)
        points = circle_points(center, radius, start, sweep, d)
        if kind == "Circle":
            points[-1] = points[0]
        return {"wkt": "LINESTRING " + _line(_place(points, links)), "hausdorff": bound}
    if kind == "BulgePolyline":
        points = _segments_points(params["segments"], d, params["closed"])
        return {"wkt": "LINESTRING " + _line(_place(points, links)), "hausdorff": bound}
    if kind == "Compound":
        segments: list[dict[str, Any]] = []
        for member in params["members"]:
            if member["kind"] == "Chord":
                segments.append({"kind": "Chord", **member["params"], "bulge": 0.0})
            elif member["kind"] == "BulgePolyline":
                segments.extend(member["params"]["segments"])
            else:
                return ("ID_UnsupportedEntity", f"{member['kind']} member in a polyline Compound")
        closed = segments[-1]["end"] == segments[0]["start"]
        points = _segments_points(segments, d, closed)
        return {"wkt": "LINESTRING " + _line(_place(points, links)), "hausdorff": bound}
    if kind == "Bezier":
        points = _bezier_points([tuple(p) for p in params["controlPoints"]], d)
        return {"wkt": "LINESTRING " + _line(_place(points, links)), "hausdorff": bound}
    if kind == "BSpline":
        if any(not math.isclose(w, 1.0, rel_tol=1e-12) for w in params["weights"]):
            return ("ID_UnsupportedEntity", "rational B-spline: Wang's bound is for polynomial curves")
        degree, knots = params["degree"], params["knots"]
        if any(b < a for a, b in zip(knots, knots[1:])):
            return ("ID_DegenerateEntity", "B-spline knots decrease")
        if any(knots.count(k) > degree for k in set(knots[degree + 1 : -degree - 1])):
            return ("ID_DegenerateEntity", "B-spline interior knot repeated more often than its degree")
        points: list[Point] = []
        for span in bezier_spans(params["degree"], params["controlPoints"], params["knots"]):
            part = _bezier_points(span, d)
            points.extend(part if not points else part[1:])
        return {"wkt": "LINESTRING " + _line(_place(points, links)), "hausdorff": bound}
    if kind == "Ring":
        import nonzero_node

        rings = [_place(_segments_points(contour, d, True)[:-1], links) for contour in params["contours"]]
        try:
            merged = nonzero_node.nonzero_polygons(rings, params["windingRule"])
        except ValueError as error:
            return ("ID_NonzeroOverlapNotYet", str(error))
        if not merged:
            return ("ID_DegenerateEntity", "the region fills nothing")
        polygons = []
        for shell, holes in merged:
            parts = []
            for ring in [shell] + holes:
                points = [(float(x), float(y)) for x, y in ring]
                points = [p for p, q in zip(points, points[-1:] + points[:-1]) if p != q]
                parts.append(_line(points + points[:1]))
            polygons.append("(" + ", ".join(parts) + ")")
        noded = any_meet(rings)
        return {
            "wkt": "MULTIPOLYGON (" + ", ".join(polygons) + ")",
            "hausdorff": None if noded else bound,
            "contourHausdorff": bound,
            "noded": noded,
        }
    return ("ID_UnsupportedEntity", f"{kind} records are not linearized here")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Linearize CAD carrier JSON lines to WKT.")
    parser.add_argument("records", type=Path, help="JSON lines from an extractor")
    parser.add_argument("--hausdorff", type=float, default=None, help="world Hausdorff bound")
    args = parser.parse_args(argv)
    if not args.records.is_file():
        print(f"not a file: {args.records}", file=sys.stderr)
        return 2
    for line in args.records.read_text(encoding="utf-8").splitlines():
        row = json.loads(line)
        if row.get("record") != "entity":
            continue
        out = linearize_record(row, args.hausdorff)
        if isinstance(out, tuple):
            out = {"decline": out[0], "reason": out[1]}
        print(json.dumps({"handle": row["provenance"]["handle"], **out}, allow_nan=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
