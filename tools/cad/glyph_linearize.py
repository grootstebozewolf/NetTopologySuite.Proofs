#!/usr/bin/env python3
"""Text carrier record to linear WKT, with a stated Hausdorff bound.

Input is one row written by ``text_glyphs.run_record`` or ``block_record``:
a Compound of glyph members. An outline glyph is a Ring plus one Compound
of Chord and Bezier spans per contour; a stroke glyph is a Compound of
BulgePolyline strokes. Outline glyphs become a MULTIPOLYGON, stroke
glyphs a MULTILINESTRING, and a row that holds both (an MTEXT that
switches between outline and stroke fonts) a GEOMETRYCOLLECTION of the
two. Output is in world coordinates, exterior rings counter-clockwise and
holes clockwise, the GIS convention.

The Ring's ``windingRule`` must be ``nonzero``; any other rule declines,
since only nonzero is implemented. Its ``orientation`` is checked against
the sign of its own contour skeleton, and a mismatch declines as a
producer error. The output orientation is then computed from the
flattened rings.

Flattening is uniform in the parameter. A Bezier of degree p with control
points P_i is cut into ``n = ceil(sqrt(p*(p-1)*M / (8*d)))`` chords, where
``M = max |P_i - 2*P_(i+1) + P_(i+2)|`` (Wang). Every chord is then within
``d`` of its curve piece, in local units, so the polyline is within the
Hausdorff bound ``k*d`` of the placed contour, where ``k`` is the product
of the link scales (``tolerance.json``, sagitta). The chord count is
computed exactly (``n**4 * 64 * d**2 >= (p*(p-1))**2 * M**2`` in rationals),
so no float rounding can leave it one chord short. The bound is for exact
arithmetic: it leaves out the float error of de Casteljau evaluation and
of ``cos`` and ``sin`` in the placement, a few ulps of the coordinates.

``d`` comes from the record's sagitta tolerance, or from ``hausdorff``, a
world bound that is divided by ``k``. A record with neither declines as
ID_ToleranceKindUnsupported.

Fill is the nonzero rule over all contours of the text together. A
contour is a polygon boundary when the winding number changes between
zero and nonzero across it: zero outside is a shell, zero inside is a
hole, and a contour with nonzero on both sides is not a boundary. Winding
numbers and the crossing test are exact rational arithmetic on the
flattened vertices. When flattened contours cross, touch or overlap,
``nonzero_node`` nodes them exactly and the result is marked ``noded``.
Crossing points are rational and are rounded to floats on output; that
rounding is an unbounded step (consecutive duplicates it creates are
dropped, but a touch could in principle become a crossing). The output
carries two numbers: ``contourHausdorff`` is ``k*d``, the bound of each
flattened contour, and ``hausdorff`` is the same number when nothing was
noded and ``null`` when something was, because the bound is not proved
for the merged boundary.

A stroke-font row (glyph members made of BulgePolyline strokes) becomes a
MULTILINESTRING instead. An arc of radius ``r`` and sweep ``theta`` is cut
into ``ceil(theta / (2*acos(1 - d/r)))`` chords, so each chord's sagitta
is at most ``d``; the vertices lie on the arc.

Any other row declines as ID_UnsupportedEntity.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any

Decline = tuple[str, str]
Point = tuple[float, float]


def _apply(point: Point, link: dict[str, Any]) -> Point:
    """Reflect, then uniform scale, then rotate, then translate."""
    x, y = point
    if link["reflect"]:
        x = -x
    x, y = x * link["scale"], y * link["scale"]
    angle = math.radians(link["rotate"])
    cosine, sine = math.cos(angle), math.sin(angle)
    return (cosine * x - sine * y + link["translate"][0], sine * x + cosine * y + link["translate"][1])


def chain_scale(links: list[dict[str, Any]]) -> float:
    scale = 1.0
    for link in links:
        scale *= link["scale"]
    return scale


def wang_count(points: list[Point], d: float) -> int:
    """Chords needed so a uniform polyline is within ``d`` of the Bezier.

    The least ``n >= 1`` with ``n >= sqrt(p*(p-1)*M / (8*d))``, decided in
    rationals as ``n**4 * 64 * d**2 >= (p*(p-1))**2 * M**2``, where ``M**2``
    is the largest squared second difference of the control points.
    """
    degree = len(points) - 1
    exact = [(Fraction(x), Fraction(y)) for x, y in points]
    m2 = max(
        ((a[0] - 2 * b[0] + c[0]) ** 2 + (a[1] - 2 * b[1] + c[1]) ** 2 for a, b, c in zip(exact, exact[1:], exact[2:])),
        default=Fraction(0),
    )
    if m2 == 0:
        return 1
    need = Fraction(degree * (degree - 1)) ** 2 * m2
    d2 = 64 * Fraction(d) ** 2

    def enough(n: int) -> bool:
        return Fraction(n) ** 4 * d2 >= need

    # A float guess, then fix it up exactly in either direction.
    n = max(1, math.ceil(math.sqrt(degree * (degree - 1) * math.sqrt(float(m2)) / (8.0 * d))))
    while n > 1 and enough(n - 1):
        n -= 1
    while not enough(n):
        n += 1
    return n


def bezier_point(points: list[Point], t: float) -> Point:
    """De Casteljau."""
    work = list(points)
    while len(work) > 1:
        work = [
            ((1 - t) * a[0] + t * b[0], (1 - t) * a[1] + t * b[1])
            for a, b in zip(work, work[1:])
        ]
    return work[0]


def _span_points(member: dict[str, Any], d: float) -> list[Point] | Decline:
    """Start point and interior points of one span. The end point is the next start."""
    params = member["params"]
    if member["kind"] == "Chord":
        return [tuple(params["start"])]
    if member["kind"] != "Bezier":
        return ("ID_UnsupportedEntity", f"{member['kind']} span in a glyph contour")
    control = [tuple(point) for point in params["controlPoints"]]
    count = wang_count(control, d)
    return [control[0]] + [bezier_point(control, index / count) for index in range(1, count)]


def _signed_area2(ring: list[Point]) -> Fraction:
    total = Fraction(0)
    for (x1, y1), (x2, y2) in zip(ring, ring[1:] + ring[:1]):
        total += Fraction(x1) * Fraction(y2) - Fraction(x2) * Fraction(y1)
    return total


def _orient(a: Point, b: Point, c: Point) -> int:
    value = (Fraction(b[0]) - Fraction(a[0])) * (Fraction(c[1]) - Fraction(a[1])) - (
        Fraction(b[1]) - Fraction(a[1])
    ) * (Fraction(c[0]) - Fraction(a[0]))
    return (value > 0) - (value < 0)


def _in_box(a: Point, b: Point, p: Point) -> bool:
    return min(a[0], b[0]) <= p[0] <= max(a[0], b[0]) and min(a[1], b[1]) <= p[1] <= max(a[1], b[1])


def _segments_meet(a: Point, b: Point, c: Point, d: Point) -> bool:
    """True when closed segments ab and cd share a point."""
    if max(a[0], b[0]) < min(c[0], d[0]) or max(c[0], d[0]) < min(a[0], b[0]):
        return False
    if max(a[1], b[1]) < min(c[1], d[1]) or max(c[1], d[1]) < min(a[1], b[1]):
        return False
    o1, o2, o3, o4 = _orient(a, b, c), _orient(a, b, d), _orient(c, d, a), _orient(c, d, b)
    if o1 != o2 and o3 != o4:
        return True
    return (
        (o1 == 0 and _in_box(a, b, c))
        or (o2 == 0 and _in_box(a, b, d))
        or (o3 == 0 and _in_box(c, d, a))
        or (o4 == 0 and _in_box(c, d, b))
    )


def any_meet(rings: list[list[Point]]) -> bool:
    """True when any two edges of the rings share a point, other than neighbours in one ring at their joint.

    An x-sorted sweep: edges are taken by their left end, and an edge is only
    tested against the edges whose x range still reaches it. The tests
    themselves are the exact ``_segments_meet``.
    """
    edges = []
    for r, ring in enumerate(rings):
        count = len(ring)
        for i in range(count):
            a, b = ring[i], ring[(i + 1) % count]
            edges.append((min(a[0], b[0]), max(a[0], b[0]), min(a[1], b[1]), max(a[1], b[1]), r, i, count, a, b))
    edges.sort(key=lambda edge: edge[0])
    active: list[tuple] = []
    for edge in edges:
        x0, x1, y0, y1, r, i, count, a, b = edge
        active = [other for other in active if other[1] >= x0]
        for other in active:
            if other[3] < y0 or other[2] > y1:
                continue
            if other[4] == r:
                gap = abs(other[5] - i)
                if gap == 1 or gap == count - 1:
                    continue
            if _segments_meet(a, b, other[7], other[8]):
                return True
        active.append(edge)
    return False


def winding(ring: list[Point], point: Point) -> int:
    """Winding number of a ring about a point that is not on it."""
    total = 0
    for a, b in zip(ring, ring[1:] + ring[:1]):
        if a[1] <= point[1]:
            if b[1] > point[1] and _orient(a, b, point) > 0:
                total += 1
        elif b[1] <= point[1] and _orient(a, b, point) < 0:
            total -= 1
    return total


def arc_points(start: Point, end: Point, bulge: float, d: float) -> list[Point]:
    """Start and interior vertices of a bulge arc cut to sagitta ``d``. The end is not included."""
    # The carrier writes b = 0 as a Chord, so an Arc here always bulges.
    assert bulge != 0, "an Arc segment with bulge 0"
    chord = math.hypot(end[0] - start[0], end[1] - start[1])
    sweep = 4.0 * math.atan(abs(bulge))
    radius = chord / (2.0 * math.sin(sweep / 2.0))
    step = 2.0 * math.acos(max(-1.0, 1.0 - d / radius))
    count = max(1, math.ceil(sweep / step))
    # The centre is off the chord midpoint by (1 - b^2) / (4 b) times the chord's left normal.
    offset = (1.0 - bulge * bulge) / (4.0 * bulge)
    cx = (start[0] + end[0]) / 2.0 - offset * (end[1] - start[1])
    cy = (start[1] + end[1]) / 2.0 + offset * (end[0] - start[0])
    first = math.atan2(start[1] - cy, start[0] - cx)
    turn = math.copysign(sweep, bulge) / count
    return [start] + [
        (cx + radius * math.cos(first + turn * index), cy + radius * math.sin(first + turn * index))
        for index in range(1, count)
    ]


def _stroke_lines(glyph: dict[str, Any], d_world: float | None) -> list[list[Point]] | Decline:
    links = glyph["placement"]["links"]
    tolerance = glyph["tolerance"]
    if d_world is not None:
        d = d_world / chain_scale(links)
    elif tolerance["kind"] == "sagitta":
        d = tolerance["d"]
    else:
        return ("ID_ToleranceKindUnsupported", f"{tolerance['kind']} states no chord height")
    lines = []
    for stroke in glyph["params"]["members"]:
        if stroke["kind"] != "BulgePolyline":
            return ("ID_UnsupportedEntity", "stroke glyph member is not a BulgePolyline")
        local: list[Point] = []
        for segment in stroke["params"]["segments"]:
            start, end = tuple(segment["start"]), tuple(segment["end"])
            local.extend(arc_points(start, end, segment["bulge"], d) if segment["kind"] == "Arc" else [start])
        local.append(tuple(stroke["params"]["segments"][-1]["end"]))
        line = []
        for point in local:
            for link in links:
                point = _apply(point, link)
            line.append(point)
        lines.append(line)
    return lines


def _linearize_strokes(glyphs: list[dict[str, Any]], hausdorff: float | None) -> dict[str, Any] | Decline:
    """MULTILINESTRING body and count for the stroke glyphs."""
    lines: list[list[Point]] = []
    bound = hausdorff or 0.0
    for glyph in glyphs:
        found = _stroke_lines(glyph, hausdorff)
        if isinstance(found, tuple):
            return found
        lines.extend(found)
        if hausdorff is None:
            bound = max(bound, chain_scale(glyph["placement"]["links"]) * glyph["tolerance"]["d"])
    body = ", ".join("(" + ", ".join(f"{x!r} {y!r}" for x, y in line) + ")" for line in lines)
    return {"wkt": "MULTILINESTRING (" + body + ")", "bound": bound, "lines": len(lines), "noded": False}


def _is_stroke_glyph(glyph: dict[str, Any]) -> bool:
    return glyph["kind"] == "Compound" and (glyph["params"].get("members") or [{}])[0].get("kind") == "BulgePolyline"


def _glyph_contours(glyph: dict[str, Any], d_world: float | None) -> list[list[Point]] | Decline:
    members = glyph["params"].get("members") if glyph["kind"] == "Compound" else None
    if not members or members[0]["kind"] != "Ring" or len(members) < 2:
        return ("ID_UnsupportedEntity", "member is not a glyph outline")
    ring_params = members[0]["params"]
    if ring_params.get("windingRule") != "nonzero":
        return ("ID_UnsupportedEntity", f"winding rule {ring_params.get('windingRule')} is not linearized")
    skeleton, recorded = ring_params.get("contours", []), ring_params.get("orientation", [])
    if len(skeleton) != len(members) - 1 or len(recorded) != len(skeleton):
        return ("ID_DegenerateEntity", "Ring contours do not match the glyph contours")
    for chords, sign in zip(skeleton, recorded):
        area = _signed_area2([tuple(chord["start"]) for chord in chords])
        if area == 0 or ("ccw" if area > 0 else "cw") != sign:
            return ("ID_DegenerateEntity", "recorded orientation disagrees with the contour")
    links = glyph["placement"]["links"]
    scale = chain_scale(links)
    tolerance = glyph["tolerance"]
    if d_world is not None:
        d = d_world / scale
    elif tolerance["kind"] == "sagitta":
        d = tolerance["d"]
    else:
        return ("ID_ToleranceKindUnsupported", f"{tolerance['kind']} states no chord height")
    rings = []
    for contour in members[1:]:
        if contour["kind"] != "Compound":
            return ("ID_UnsupportedEntity", "glyph contour is not a Compound")
        local: list[Point] = []
        for span in contour["params"]["members"]:
            points = _span_points(span, d)
            if isinstance(points, tuple):
                return points
            local.extend(points)
        ring = []
        for point in local:
            for link in links:
                point = _apply(point, link)
            ring.append(point)
        rings.append(ring)
    return rings


def _wkt_ring(ring: list[Point]) -> str:
    return "(" + ", ".join(f"{x!r} {y!r}" for x, y in ring + ring[:1]) + ")"


def _linearize_outlines(glyphs: list[dict[str, Any]], hausdorff: float | None) -> dict[str, Any] | Decline:
    """MULTIPOLYGON body and count for the outline glyphs."""
    rings: list[list[Point]] = []
    bound = 0.0
    for glyph in glyphs:
        contours = _glyph_contours(glyph, hausdorff)
        if isinstance(contours, tuple):
            return contours
        rings.extend(contours)
        if hausdorff is None:
            bound = max(bound, chain_scale(glyph["placement"]["links"]) * glyph["tolerance"]["d"])
    if hausdorff is not None:
        bound = hausdorff

    areas = [_signed_area2(ring) for ring in rings]
    if any(len(ring) < 3 or area == 0 for ring, area in zip(rings, areas)):
        return ("ID_DegenerateEntity", "flattened contour has no area")
    if any_meet(rings):
        import nonzero_node

        try:
            merged = nonzero_node.nonzero_polygons(rings)
        except ValueError as error:
            return ("ID_NonzeroOverlapNotYet", str(error))
        if not merged:
            return ("ID_DegenerateEntity", "text fills nothing")
        rounded = []
        for shell, inner in merged:
            polygon = []
            for ring in [shell] + inner:
                # Rounding the rational vertices can make neighbours equal; drop the repeats.
                points = [(float(x), float(y)) for x, y in ring]
                points = [p for p, q in zip(points, points[-1:] + points[:-1]) if p != q]
                if len(points) < 3:
                    return ("ID_DegenerateEntity", "a noded ring collapses when rounded to floats")
                polygon.append(points)
            rounded.append(polygon)
        polygons = ["(" + ", ".join(_wkt_ring(ring) for ring in polygon) + ")" for polygon in rounded]
        return {"wkt": "MULTIPOLYGON (" + ", ".join(polygons) + ")", "bound": bound, "polygons": len(polygons), "noded": True}

    shells: list[int] = []
    holes: list[int] = []
    for i, ring in enumerate(rings):
        outside = sum(winding(other, ring[0]) for j, other in enumerate(rings) if j != i)
        inside = outside + (1 if areas[i] > 0 else -1)
        if outside == 0 and inside != 0:
            shells.append(i)
        elif outside != 0 and inside == 0:
            holes.append(i)

    def ccw(i: int, want: bool) -> list[Point]:
        return rings[i] if (areas[i] > 0) == want else rings[i][::-1]

    held: dict[int, list[int]] = {i: [] for i in shells}
    for hole in holes:
        around = [s for s in shells if winding(rings[s], rings[hole][0]) != 0]
        if not around:
            return ("ID_DegenerateEntity", "hole has no shell")
        held[min(around, key=lambda s: abs(areas[s]))].append(hole)
    if not shells:
        return ("ID_DegenerateEntity", "text fills nothing")
    polygons = [
        "(" + ", ".join([_wkt_ring(ccw(s, True))] + [_wkt_ring(ccw(h, False)) for h in held[s]]) + ")"
        for s in shells
    ]
    return {"wkt": "MULTIPOLYGON (" + ", ".join(polygons) + ")", "bound": bound, "polygons": len(polygons), "noded": False}


def linearize_row(row: dict[str, Any], hausdorff: float | None = None) -> dict[str, Any] | Decline:
    """A text carrier row as WKT, or a decline.

    The result has ``wkt``, ``hausdorff``, ``contourHausdorff`` and
    ``noded``, plus ``polygons`` for outline glyphs and ``lines`` for
    stroke glyphs. ``hausdorff`` is ``null`` when the outlines were noded.

    The ``hausdorff`` argument is a world bound. Without it the record's
    sagitta is used and the bound is the largest ``k*d`` over the glyphs.
    """
    if hausdorff is not None and not (math.isfinite(hausdorff) and hausdorff > 0):
        return ("ID_ToleranceNonPositive", "hausdorff bound is not a positive finite number")
    if row.get("record") != "entity" or row.get("kind") != "Compound":
        return ("ID_UnsupportedEntity", "row is not a text Compound")
    glyphs = row["params"].get("members") or []
    strokes = [glyph for glyph in glyphs if _is_stroke_glyph(glyph)]
    outlines = [glyph for glyph in glyphs if not _is_stroke_glyph(glyph)]
    parts = []
    for chosen, run in ((outlines, _linearize_outlines), (strokes, _linearize_strokes)):
        if chosen:
            part = run(chosen, hausdorff)
            if isinstance(part, tuple):
                return part
            parts.append(part)
    if not parts:
        return ("ID_UnsupportedEntity", "row has no glyphs")
    bound = max(part["bound"] for part in parts)
    noded = any(part["noded"] for part in parts)
    out: dict[str, Any] = {
        "wkt": parts[0]["wkt"] if len(parts) == 1 else "GEOMETRYCOLLECTION (" + ", ".join(p["wkt"] for p in parts) + ")",
        "hausdorff": None if noded else bound,
        "contourHausdorff": bound,
        "noded": noded,
    }
    for part in parts:
        for key in ("polygons", "lines"):
            if key in part:
                out[key] = part[key]
    if row.get("lenient"):
        # The bound is to the record; what lenient left out of it travels with the WKT.
        out["lenient"] = row["lenient"]
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Linearize text carrier JSON lines to MULTIPOLYGON WKT.")
    parser.add_argument("records", type=Path, help="JSON lines from dxf_extract.py")
    parser.add_argument("--hausdorff", type=float, default=None, help="world Hausdorff bound")
    args = parser.parse_args(argv)
    if not args.records.is_file():
        print(f"not a file: {args.records}", file=sys.stderr)
        return 2
    for line in args.records.read_text(encoding="utf-8").splitlines():
        row = json.loads(line)
        if row.get("record") != "entity":
            continue
        out = linearize_row(row, args.hausdorff)
        handle = row["provenance"]["handle"]
        if isinstance(out, tuple):
            out = {"decline": out[0], "reason": out[1]}
        print(json.dumps({"handle": handle, **out}, allow_nan=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
