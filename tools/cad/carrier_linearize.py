#!/usr/bin/env python3
"""Any CAD carrier record to linear WKT, with a stated Hausdorff bound.

``glyph_linearize`` covers text rows. This module covers the rest of the
carrier, so every record an extractor writes can reach GIS:

* Chord: a two-point LINESTRING. Exact: the bound is 0, whatever the
  tolerance says.
* Arc and Circle: a LINESTRING (closed for a circle, at least 3 segments)
  with its vertices on the circle. Arc angles run counter-clockwise from
  ``startAngle`` to ``endAngle`` in the record's OCS, in degrees or
  radians, plus ``frameAngle`` when present; another angle unit declines,
  and an arc of zero sweep declines as degenerate.
* BulgePolyline: a LINESTRING, closed when the polyline is.
* Compound of Chord and BulgePolyline members (a 2D POLYLINE): one
  LINESTRING through the members in order.
* Ellipse: a LINESTRING (closed for a whole ellipse) at equal parameter
  steps, counter-clockwise from ``startParam`` to ``endParam`` about the
  major axis. The step count comes from the second-derivative bound in
  ``ellipse_points``. Only a sagitta or a world bound applies: an angle
  step or segment count declines.
* Bezier: Wang's chord count, decided in rationals.
* BSpline: clamped and polynomial, split into Bezier spans by knot
  insertion, then Wang's count per span. Weights that are all equal
  (within 1e-9 of the first, as the extractor tests unit weights) are a
  polynomial curve. Unequal weights (rational), unclamped knots,
  decreasing knots, or an interior knot repeated above the degree (a break
  in the curve) decline.
* Ring: a MULTIPOLYGON under its winding rule (nonzero or evenodd). When
  the flattened contours do not meet, each is classified by exact winding
  numbers, without noding; when they meet, ``nonzero_node`` fills them
  exactly, the result is marked noded and ``hausdorff`` is null, as for
  text.
* A Compound of glyph members (a text row): ``glyph_linearize``.

Tolerance. A sagitta ``d`` bounds every chord's distance from its arc or
curve. An ``angleStep`` alpha cuts arcs and circles (and polyline bulges)
into steps of at most alpha, whose sagitta is ``r * (1 - cos(alpha / 2))``
for each radius ``r``; it does not apply to Beziers and B-splines, which
then decline. A world bound passed as ``hausdorff`` is divided by the
chain's scale ``k``. The reported bound is ``k`` times the largest local
sagitta used (for exact arithmetic, as in ``glyph_linearize``).

Every row ends as WKT or a named decline. A malformed record (a missing
key, an empty list) declines as ID_DegenerateEntity rather than stopping
a run. Spiral records decline: their own Linearizes bound is not here.

A record's ``lenient`` notes (what lenient extraction left out of it,
such as a polyline's width) are copied to the output: the bound is to the
record, not to what the source draws.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path
from typing import Any, Callable

import glyph_linearize
from glyph_linearize import _apply, any_meet, arc_points, bezier_point, chain_scale, wang_count, winding

Decline = tuple[str, str]
Point = tuple[float, float]
# The chord height to use for an arc of a given (local) radius.
Sagitta = Callable[[float], float]
_UNIT_EPS = 1e-9  # the extractor's tolerance for unit weights


class _Declined(Exception):
    def __init__(self, decline_id: str, reason: str) -> None:
        super().__init__(reason)
        self.decline = (decline_id, reason)


def _place(points: list[Point], links: list[dict[str, Any]]) -> list[Point]:
    placed = []
    for point in points:
        for link in links:
            point = _apply(point, link)
        placed.append(point)
    return placed


def _sagitta(row: dict[str, Any], hausdorff: float | None, curved: bool) -> Sagitta:
    """The local chord height for each radius, from the bound asked for or the record's tolerance."""
    if hausdorff is not None:
        d = hausdorff / chain_scale(row["placement"]["links"])
        return lambda _radius: d
    tolerance = row["tolerance"]
    if tolerance["kind"] == "sagitta":
        d = float(tolerance["d"])
        return lambda _radius: d
    if tolerance["kind"] == "angleStep" and not curved:
        unit = tolerance.get("angleUnit", "degree")
        if unit not in ("degree", "radian"):
            raise _Declined("ID_ToleranceKindUnsupported", f"angle step in {unit}")
        alpha = math.radians(tolerance["alpha"]) if unit == "degree" else float(tolerance["alpha"])
        return lambda radius: radius * (1.0 - math.cos(alpha / 2.0))
    raise _Declined("ID_ToleranceKindUnsupported", f"{tolerance['kind']} gives no chord height here")


def circle_points(center: Point, radius: float, start: float, sweep: float, d: float) -> list[Point]:
    """Points from ``start`` through ``sweep`` radians (counter-clockwise), chords of sagitta at most ``d``.

    A full circle gets at least 3 segments, so it stays a ring with area.
    """
    step = 2.0 * math.acos(max(-1.0, 1.0 - d / radius)) if d < 2 * radius else math.pi
    count = max(1, math.ceil(sweep / step))
    if sweep >= 2 * math.pi - 1e-12:
        count = max(count, 3)
    return [
        (center[0] + radius * math.cos(start + sweep * k / count), center[1] + radius * math.sin(start + sweep * k / count))
        for k in range(count + 1)
    ]


def ellipse_points(
    center: Point, major: Point, ratio: float, start: float, sweep: float, d: float
) -> tuple[list[Point], float]:
    """Points at equal parameter steps from ``start`` through ``sweep`` (counter-clockwise), and their bound.

    The ellipse is ``p(t) = c + M cos t + N sin t`` with ``N = ratio * M`` turned a quarter
    counter-clockwise. On a step of length ``h`` the chord ``L`` from ``p(t0)`` to ``p(t0 + h)``
    satisfies ``|p(t) - L(t)| <= (t - t0)(t0 + h - t) / 2 * max |p''| <= h^2 / 8 * A`` (the
    integral form of the interpolation remainder, which holds for vector values), where
    ``A = max(|M|, |N|) >= |p''(t)| = |M cos t + N sin t|``. Matching each ``p(t)`` with ``L(t)``
    bounds the Hausdorff distance both ways, so the step count is the least ``n`` with
    ``A (sweep / n)^2 / 8 <= d``. A whole ellipse gets at least 3 segments.
    """
    mx, my = major
    nx, ny = -ratio * my, ratio * mx
    a = max(math.hypot(mx, my), math.hypot(nx, ny))
    count = max(1, math.ceil(sweep * math.sqrt(a / (8.0 * d))))
    if sweep >= 2 * math.pi - 1e-12:
        count = max(count, 3)
    while a * (sweep / count) ** 2 / 8.0 > d:  # guard the float ceiling
        count += 1
    points = []
    for k in range(count + 1):
        t = start + sweep * k / count
        c, s = math.cos(t), math.sin(t)
        points.append((center[0] + mx * c + nx * s, center[1] + my * c + ny * s))
    return points, a * (sweep / count) ** 2 / 8.0


def _ellipse_points(params: dict[str, Any], sagitta: Sagitta) -> tuple[list[Point], float]:
    if params.get("angleUnit", "radian") != "radian":
        raise _Declined("ID_UnsupportedEntity", f"ellipse params in {params.get('angleUnit')}")
    center, major = tuple(params["center"]), tuple(params["majorAxis"])
    ratio, start, end = float(params["ratio"]), float(params["startParam"]), float(params["endParam"])
    numbers = (*center, *major, ratio, start, end)
    if not all(math.isfinite(v) for v in numbers):
        raise _Declined("ID_DegenerateEntity", "a non-finite ellipse number")
    if not (ratio > 0 and math.hypot(*major) > 0):
        raise _Declined("ID_DegenerateEntity", "an ellipse with no area")
    raw = end - start
    sweep = raw % (2 * math.pi)
    if sweep <= 1e-12:
        if abs(raw) <= 1e-12:
            raise _Declined("ID_DegenerateEntity", "an ellipse arc of zero sweep")
        sweep = 2 * math.pi  # a whole ellipse stated as 0 to 2 pi
    d = sagitta(0.0)
    points, bound = ellipse_points(center, major, ratio, start, sweep, d)
    if sweep == 2 * math.pi:
        points[-1] = points[0]
    return points, bound


def _bulge_radius(start: Point, end: Point, bulge: float) -> float:
    chord = math.hypot(end[0] - start[0], end[1] - start[1])
    return chord / (2.0 * math.sin(2.0 * math.atan(abs(bulge))))


def _segments_points(segments: list[dict[str, Any]], sagitta: Sagitta, closed: bool) -> tuple[list[Point], float]:
    """The vertices of a bulge chain, and the largest local sagitta used."""
    if not segments:
        raise _Declined("ID_DegenerateEntity", "a polyline with no segments")
    points: list[Point] = []
    worst = 0.0
    for segment in segments:
        start, end = tuple(segment["start"]), tuple(segment["end"])
        if segment["kind"] == "Arc" and segment["bulge"]:
            d = sagitta(_bulge_radius(start, end, segment["bulge"]))
            worst = max(worst, d)
            points.extend(arc_points(start, end, segment["bulge"], d))
        else:
            points.append(start)
    points.append(tuple(segments[0]["start"]) if closed else tuple(segments[-1]["end"]))
    return points, worst


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


def _linestring(points: list[Point], links: list[dict[str, Any]], local_bound: float) -> dict[str, Any]:
    return {"wkt": "LINESTRING " + _line(_place(points, links)), "hausdorff": chain_scale(links) * local_bound}


def _check_bspline(params: dict[str, Any]) -> list[Point]:
    """Validated polynomial control points, or a decline."""
    degree, controls, knots = int(params["degree"]), params["controlPoints"], [float(k) for k in params["knots"]]
    weights = [float(w) for w in params.get("weights") or [1.0] * len(controls)]
    if degree < 1 or len(controls) < degree + 1 or len(weights) != len(controls):
        raise _Declined("ID_DegenerateEntity", "B-spline degree, control points and weights do not agree")
    if len(knots) != len(controls) + degree + 1:
        raise _Declined("ID_UnclampedKnots", "B-spline knot count is not control points + degree + 1")
    if len(set(knots[: degree + 1])) != 1 or len(set(knots[-degree - 1 :])) != 1:
        raise _Declined("ID_UnclampedKnots", "B-spline knots are not clamped")
    if any(b < a for a, b in zip(knots, knots[1:])) or knots[0] == knots[-1]:
        raise _Declined("ID_DegenerateEntity", "B-spline knots decrease or span nothing")
    if any(knots.count(k) > degree for k in set(knots[degree + 1 : -degree - 1])):
        raise _Declined("ID_DegenerateEntity", "B-spline interior knot repeated more often than its degree")
    if weights[0] <= 0 or not all(math.isfinite(w) and w > 0 for w in weights):
        raise _Declined("ID_DegenerateEntity", "B-spline weights are not positive")
    # Equal weights cancel: the curve is polynomial whatever their common value.
    if any(abs(w / weights[0] - 1.0) > _UNIT_EPS for w in weights):
        raise _Declined("ID_UnsupportedEntity", "rational B-spline: Wang's bound is for polynomial curves")
    return [tuple(point) for point in controls]


def _ring(params: dict[str, Any], sagitta: Sagitta, links: list[dict[str, Any]], scale: float) -> dict[str, Any]:
    rule = params["windingRule"]
    if rule not in ("nonzero", "evenodd"):
        raise _Declined("ID_UnsupportedEntity", f"winding rule {rule}")
    contours = params["contours"]
    if not contours:
        raise _Declined("ID_DegenerateEntity", "a Ring with no contours")
    rings, worst = [], 0.0
    for contour in contours:
        points, used = _segments_points(contour, sagitta, True)
        rings.append(_place(points[:-1], links))
        worst = max(worst, used)
    bound = scale * worst
    if any(len(ring) < 3 for ring in rings):
        raise _Declined("ID_DegenerateEntity", "a Ring contour with fewer than three vertices")
    filled = (lambda w: w % 2 != 0) if rule == "evenodd" else (lambda w: w != 0)

    if not any_meet(rings):
        # The fast path: no contour meets another, so each is a whole boundary or none.
        from glyph_linearize import _signed_area2

        areas = [_signed_area2(ring) for ring in rings]
        if any(area == 0 for area in areas):
            raise _Declined("ID_DegenerateEntity", "a Ring contour with no area")
        shells, holes = [], []
        for i, ring in enumerate(rings):
            outside = sum(winding(other, ring[0]) for j, other in enumerate(rings) if j != i)
            inside = outside + (1 if areas[i] > 0 else -1)
            if not filled(outside) and filled(inside):
                shells.append(i)
            elif filled(outside) and not filled(inside):
                holes.append(i)
        if not shells:
            raise _Declined("ID_DegenerateEntity", "the region fills nothing")
        oriented = lambda i, ccw: rings[i] if (areas[i] > 0) == ccw else rings[i][::-1]
        held: dict[int, list[int]] = {i: [] for i in shells}
        for hole in holes:
            around = [s for s in shells if winding(rings[s], rings[hole][0]) != 0]
            if not around:
                raise _Declined("ID_DegenerateEntity", "a hole with no shell")
            held[min(around, key=lambda s: abs(areas[s]))].append(hole)
        polygons = [
            "(" + ", ".join(_line(ring + ring[:1]) for ring in [oriented(s, True)] + [oriented(h, False) for h in held[s]]) + ")"
            for s in shells
        ]
        return {"wkt": "MULTIPOLYGON (" + ", ".join(polygons) + ")", "hausdorff": bound,
                "contourHausdorff": bound, "noded": False}

    import nonzero_node

    try:
        merged = nonzero_node.nonzero_polygons(rings, rule)
    except ValueError as error:
        raise _Declined("ID_NonzeroOverlapNotYet", str(error)) from error
    if not merged:
        raise _Declined("ID_DegenerateEntity", "the region fills nothing")
    polygons = []
    for shell, holes in merged:
        parts = []
        for ring in [shell] + holes:
            points = [(float(x), float(y)) for x, y in ring]
            points = [p for p, q in zip(points, points[-1:] + points[:-1]) if p != q]
            parts.append(_line(points + points[:1]))
        polygons.append("(" + ", ".join(parts) + ")")
    return {"wkt": "MULTIPOLYGON (" + ", ".join(polygons) + ")", "hausdorff": None,
            "contourHausdorff": bound, "noded": True}


def _linearize(row: dict[str, Any], hausdorff: float | None) -> dict[str, Any] | Decline:
    kind, params, links = row["kind"], row["params"], row["placement"]["links"]
    if kind == "Chord":
        # Exact: no tolerance is needed.
        points = [tuple(params["start"]), tuple(params["end"])]
        if points[0] == points[1]:
            raise _Declined("ID_DegenerateEntity", "a Chord of zero length")
        return _linestring(points, links, 0.0)
    if kind == "Compound" and params["members"] and any(m["kind"] == "Compound" for m in params["members"]):
        return glyph_linearize.linearize_row(row, hausdorff)
    if kind in ("Spiral", "Unsupported"):
        raise _Declined("ID_UnsupportedEntity", f"{kind} records are not linearized here")
    sagitta = _sagitta(row, hausdorff, curved=kind in ("Bezier", "BSpline", "Ellipse"))
    if kind == "Ellipse":
        points, bound = _ellipse_points(params, sagitta)
        return _linestring(points, links, bound)

    if kind in ("Arc", "Circle"):
        center, radius = tuple(params["center"]), float(params["radius"])
        if not radius > 0:
            raise _Declined("ID_DegenerateEntity", "radius is not positive")
        if kind == "Circle":
            start, sweep = 0.0, 2 * math.pi
        else:
            unit = params.get("angleUnit", "degree")
            if unit not in ("degree", "radian"):
                raise _Declined("ID_UnsupportedEntity", f"arc angles in {unit}")
            to_radians = math.radians if unit == "degree" else float
            start = to_radians(params["startAngle"]) + float(params.get("frameAngle", 0.0))
            raw = to_radians(params["endAngle"]) - to_radians(params["startAngle"])
            sweep = raw % (2 * math.pi)
            if sweep <= 1e-12:
                if abs(raw) <= 1e-12:
                    raise _Declined("ID_DegenerateEntity", "an arc of zero sweep")
                sweep = 2 * math.pi  # a whole turn stated as 0 to 360
        d = sagitta(radius)
        points = circle_points(center, radius, start, sweep, d)
        if kind == "Circle":
            points[-1] = points[0]
        return _linestring(points, links, d)
    if kind == "BulgePolyline":
        points, worst = _segments_points(params["segments"], sagitta, bool(params["closed"]))
        return _linestring(points, links, worst)
    if kind == "Compound":
        segments: list[dict[str, Any]] = []
        for member in params["members"]:
            if member["kind"] == "Chord":
                segments.append({"kind": "Chord", **member["params"], "bulge": 0.0})
            elif member["kind"] == "BulgePolyline":
                segments.extend(member["params"]["segments"])
            else:
                raise _Declined("ID_UnsupportedEntity", f"{member['kind']} member in a polyline Compound")
        if not segments:
            raise _Declined("ID_DegenerateEntity", "a Compound with no members")
        closed = segments[-1]["end"] == segments[0]["start"]
        points, worst = _segments_points(segments, sagitta, closed)
        return _linestring(points, links, worst)
    if kind == "Bezier":
        d = sagitta(0.0)
        return _linestring(_bezier_points([tuple(p) for p in params["controlPoints"]], d), links, d)
    if kind == "BSpline":
        controls = _check_bspline(params)
        d = sagitta(0.0)
        points: list[Point] = []
        for span in bezier_spans(int(params["degree"]), controls, [float(k) for k in params["knots"]]):
            part = _bezier_points(span, d)
            points.extend(part if not points else part[1:])
        return _linestring(points, links, d)
    if kind == "Ring":
        return _ring(params, sagitta, links, chain_scale(links))
    raise _Declined("ID_UnsupportedEntity", f"{kind} records are not linearized here")


def linearize_record(row: dict[str, Any], hausdorff: float | None = None) -> dict[str, Any] | Decline:
    """One carrier entity row as ``{"wkt", "hausdorff", ...}``, or a named decline. Never raises."""
    if hausdorff is not None and not (math.isfinite(hausdorff) and hausdorff > 0):
        return ("ID_ToleranceNonPositive", "hausdorff bound is not a positive finite number")
    if not isinstance(row, dict) or row.get("record") != "entity":
        return ("ID_UnsupportedEntity", "row is not an entity record")
    try:
        out = _linearize(row, hausdorff)
        if isinstance(out, dict) and row.get("lenient"):
            # The bound is to the record; what lenient left out of it travels with the WKT.
            out = {**out, "lenient": row["lenient"]}
        return out
    except _Declined as declined:
        return declined.decline
    except (KeyError, IndexError, TypeError, ValueError, ZeroDivisionError, OverflowError) as error:
        # Totality holds here too: a malformed record is a named decline, not a crash.
        return ("ID_DegenerateEntity", f"malformed {row.get('kind')} record: {type(error).__name__}: {error}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Linearize CAD carrier JSON lines to WKT.")
    parser.add_argument("records", type=Path, help="JSON lines from an extractor")
    parser.add_argument("--hausdorff", type=float, default=None, help="world Hausdorff bound")
    args = parser.parse_args(argv)
    if not args.records.is_file():
        print(f"not a file: {args.records}", file=sys.stderr)
        return 2
    for number, line in enumerate(args.records.read_text(encoding="utf-8").splitlines(), start=1):
        try:
            row = json.loads(line)
        except json.JSONDecodeError as error:
            print(json.dumps({"line": number, "decline": "ID_DegenerateEntity", "reason": f"not JSON: {error}"}))
            continue
        if not isinstance(row, dict) or row.get("record") != "entity":
            continue
        out = linearize_record(row, args.hausdorff)
        if isinstance(out, tuple):
            out = {"decline": out[0], "reason": out[1]}
        handle = (row.get("provenance") or {}).get("handle")
        print(json.dumps({"handle": handle, **out}, allow_nan=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
