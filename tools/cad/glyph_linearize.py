#!/usr/bin/env python3
"""Text carrier record to a linear MULTIPOLYGON, with a stated Hausdorff bound.

Input is one row written by ``text_glyphs.run_record``: a Compound of
glyph members, each a Ring plus one Compound of Chord and Bezier spans per
contour. Output is WKT in world coordinates, exterior rings
counter-clockwise and holes clockwise, the GIS convention. The source
orientation in the record is read, not rewritten.

Flattening is uniform in the parameter. A Bezier of degree p with control
points P_i is cut into ``n = ceil(sqrt(p*(p-1)*M / (8*d)))`` chords, where
``M = max |P_i - 2*P_(i+1) + P_(i+2)|`` (Wang). Every chord is then within
``d`` of its curve piece, in local units, so the polyline is within the
Hausdorff bound ``k*d`` of the placed contour, where ``k`` is the product
of the link scales (``tolerance.json``, sagitta).

``d`` comes from the record's sagitta tolerance, or from ``hausdorff``, a
world bound that is divided by ``k``. A record with neither declines as
ID_ToleranceKindUnsupported.

Fill is the nonzero rule over all contours of the text together. A
contour is a polygon boundary when the winding number changes between
zero and nonzero across it: zero outside is a shell, zero inside is a
hole, and a contour with nonzero on both sides is not a boundary. Winding
numbers and the crossing test are exact rational arithmetic on the
flattened vertices. Contours that cross or touch after flattening decline
as ID_NonzeroOverlapNotYet; this slice does not node them.

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
    """Chords needed so a uniform polyline is within ``d`` of the Bezier."""
    degree = len(points) - 1
    second = 0.0
    for a, b, c in zip(points, points[1:], points[2:]):
        second = max(second, math.hypot(a[0] - 2 * b[0] + c[0], a[1] - 2 * b[1] + c[1]))
    if second == 0.0:
        return 1
    return max(1, math.ceil(math.sqrt(degree * (degree - 1) * second / (8.0 * d))))


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


def _box(ring: list[Point]) -> tuple[float, float, float, float]:
    xs = [p[0] for p in ring]
    ys = [p[1] for p in ring]
    return (min(xs), min(ys), max(xs), max(ys))


def _boxes_apart(a: tuple, b: tuple) -> bool:
    return a[2] < b[0] or b[2] < a[0] or a[3] < b[1] or b[3] < a[1]


def _rings_meet(first: list[Point], second: list[Point]) -> bool:
    for a, b in zip(first, first[1:] + first[:1]):
        for c, d in zip(second, second[1:] + second[:1]):
            if _segments_meet(a, b, c, d):
                return True
    return False


def _self_meets(ring: list[Point]) -> bool:
    count = len(ring)
    edges = list(zip(ring, ring[1:] + ring[:1]))
    for i in range(count):
        for j in range(i + 1, count):
            if j == i + 1 or (i == 0 and j == count - 1):
                continue
            if _segments_meet(*edges[i], *edges[j]):
                return True
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


def _glyph_contours(glyph: dict[str, Any], d_world: float | None) -> list[list[Point]] | Decline:
    members = glyph["params"].get("members") if glyph["kind"] == "Compound" else None
    if not members or members[0]["kind"] != "Ring" or len(members) < 2:
        return ("ID_UnsupportedEntity", "member is not a glyph outline")
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


def linearize_row(row: dict[str, Any], hausdorff: float | None = None) -> dict[str, Any] | Decline:
    """A text carrier row as ``{"wkt", "hausdorff", "polygons"}``, or a decline.

    ``hausdorff`` is a world bound. Without it the record's sagitta is used
    and the reported bound is the largest ``k*d`` over the glyphs.
    """
    if hausdorff is not None and not (math.isfinite(hausdorff) and hausdorff > 0):
        return ("ID_ToleranceNonPositive", "hausdorff bound is not a positive finite number")
    if row.get("record") != "entity" or row.get("kind") != "Compound":
        return ("ID_UnsupportedEntity", "row is not a text Compound")
    rings: list[list[Point]] = []
    bound = 0.0
    for glyph in row["params"]["members"]:
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
    boxes = [_box(ring) for ring in rings]
    for i, ring in enumerate(rings):
        if _self_meets(ring):
            return ("ID_NonzeroOverlapNotYet", "a flattened contour meets itself")
        for j in range(i + 1, len(rings)):
            if not _boxes_apart(boxes[i], boxes[j]) and _rings_meet(ring, rings[j]):
                return ("ID_NonzeroOverlapNotYet", "two flattened contours meet")

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
    return {
        "wkt": "MULTIPOLYGON (" + ", ".join(polygons) + ")",
        "hausdorff": bound,
        "polygons": len(polygons),
    }


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
