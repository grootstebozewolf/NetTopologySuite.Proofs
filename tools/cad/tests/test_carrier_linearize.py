"""Every carrier record to WKT: checked against ezdxf's own flattening of the same placed entity."""

from __future__ import annotations

import math
import random

import ezdxf
import pytest
import shapely
from ezdxf import path as ezpath
from ezdxf.entities import LWPolyline
from ezdxf.math import BSpline, Matrix44

import carrier_linearize
import dxf_extract
from test_extract_totality import _grid, _random_doc, _source, _whole_insert

_BOUND = 0.01  # world Hausdorff bound asked of the linearizer
_FINE = 0.0005  # ezdxf's flattening distance for the reference curve


def _placed(doc, entities, m, out: list, stack: tuple[str, ...] = ()) -> None:
    """Every drawn entity with its source handle and the matrix that places it."""
    for entity in entities:
        kind = entity.dxftype()
        if kind == "ENDBLK":
            continue
        if kind != "INSERT":
            out.append((kind, _source(entity), entity, m))
            continue
        for copy in _grid(entity):
            if not _whole_insert(doc, copy, stack):
                _placed(doc, doc.blocks.get(copy.dxf.name), copy.matrix44() @ m, out, stack + (copy.dxf.name,))


def _reference(entity, m):
    """ezdxf's flattening of the placed entity, as shapely lines (a hatch: its boundary paths).

    Arcs and bulges go through ezdxf's Bezier approximation with 16 segments per quarter
    circle, so its own error (about 1e-6 here) stays far below the bound under test; with
    the default single segment it is about 3e-4 of the radius. ``from_hatch`` has no such
    setting, so each hatch boundary is rebuilt as a polyline with the same vertices.
    """
    if entity.dxftype() == "HATCH":
        paths = []
        for boundary in entity.paths:
            outline = LWPolyline.new(
                dxfattribs={"elevation": entity.dxf.elevation.z, "extrusion": entity.dxf.extrusion}
            )
            outline.set_points(list(boundary.vertices), format="xyb")
            outline.closed = True
            paths.append(ezpath.make_path(outline, segments=16))
    else:
        paths = [ezpath.make_path(entity, segments=16)]
    lines = []
    for p in paths:
        points = [(v.x, v.y) for v in p.transform(m).flattening(_FINE)]
        lines.append(shapely.LineString(points))
    return shapely.MultiLineString(lines)


def _as_lines(wkt: str):
    shape = shapely.from_wkt(wkt)
    return shape.boundary if shape.geom_type == "MultiPolygon" else shape


@pytest.mark.slow
@pytest.mark.parametrize("wide", [False, True])
@pytest.mark.parametrize("seed", range(60))
def test_every_record_is_within_its_bound_of_ezdxfs_flattening(seed: int, wide: bool) -> None:
    doc = _random_doc(random.Random(seed), wide=wide)
    seen: list[str] = []
    rows = dxf_extract.extract_document(doc, file_id="lin", on_considered=seen.append)
    drawn: list = []
    _placed(doc, doc.modelspace(), Matrix44(), drawn)
    pool: dict[tuple[str, str], list] = {}
    for kind, source, entity, m in drawn:
        pool.setdefault((kind, source), []).append((entity, m))

    checked = 0
    for kind, row in zip(seen, rows):
        if row["record"] != "entity":
            continue
        out = carrier_linearize.linearize_record(row, hausdorff=_BOUND)
        assert not isinstance(out, tuple), (kind, out)
        if out.get("noded"):
            continue  # the merged boundary is not the flattened contours
        ours = _as_lines(out["wkt"])
        candidates = pool[(kind, row["provenance"]["handle"])]
        distances = [ours.hausdorff_distance(_reference(entity, m)) for entity, m in candidates]
        best = min(range(len(distances)), key=distances.__getitem__)
        # Both lie within their own bound of the same curve.
        assert distances[best] <= out["hausdorff"] + _FINE + 1e-9, (kind, distances[best])
        candidates.pop(best)
        checked += 1
    assert checked or not any(row["record"] == "entity" for row in rows)


def _row(kind: str, params: dict, links=None) -> dict:
    return {
        "record": "entity",
        "kind": kind,
        "placement": {"links": links or [], "s": 1},
        "params": params,
        "tolerance": {"kind": "sagitta", "d": 0.01},
        "provenance": {"handle": "x"},
    }


def test_arc_runs_counter_clockwise_across_zero_and_honours_the_sagitta() -> None:
    row = _row("Arc", {"center": [1, 2], "radius": 3, "startAngle": 300, "endAngle": 40, "angleUnit": "degree"})
    out = carrier_linearize.linearize_record(row)
    points = list(shapely.from_wkt(out["wkt"]).coords)
    assert points[0] == pytest.approx((1 + 3 * math.cos(math.radians(300)), 2 + 3 * math.sin(math.radians(300))))
    assert points[-1] == pytest.approx((1 + 3 * math.cos(math.radians(40)), 2 + 3 * math.sin(math.radians(40))))
    assert all(math.dist(p, (1, 2)) == pytest.approx(3) for p in points)
    # The arc passes angle 0 (x = 4), not angle 180.
    assert max(x for x, _y in points) == pytest.approx(4, abs=0.01)
    worst = max(3 - math.dist(((a[0] + b[0]) / 2, (a[1] + b[1]) / 2), (1, 2)) for a, b in zip(points, points[1:]))
    assert 0 < worst <= 0.01
    assert out["hausdorff"] == 0.01


@pytest.mark.parametrize("seed", range(20))
def test_bspline_spans_reproduce_the_curve(seed: int) -> None:
    rng = random.Random(seed)
    degree = rng.choice([2, 3])
    count = rng.randint(degree + 2, 9)
    controls = [(rng.uniform(0, 10), rng.uniform(0, 10)) for _ in range(count)]
    # Interior knots, none repeated more often than the degree.
    pool = [k for k in (0.2, 0.35, 0.5, 0.7, 0.85) for _ in range(degree)]
    inner = sorted(rng.sample(pool, count - degree - 1))
    knots = [0.0] * (degree + 1) + inner + [1.0] * (degree + 1)
    spans = carrier_linearize.bezier_spans(degree, controls, knots)
    curve = BSpline(controls, order=degree + 1, knots=knots)
    for t in [k / 37 for k in range(38)]:
        expected = curve.point(t)
        # Find the span holding t and its local parameter.
        edges = sorted(set(knots))
        index = max(i for i in range(len(edges) - 1) if edges[i] <= t) if t < 1 else len(edges) - 2
        local = (t - edges[index]) / (edges[index + 1] - edges[index])
        from glyph_linearize import bezier_point

        assert bezier_point(spans[index], local) == pytest.approx((expected.x, expected.y), abs=1e-9)


def test_bspline_with_a_break_or_decreasing_knots_declines() -> None:
    controls = [[0, 0], [1, 2], [3, 1], [4, 0], [5, 2], [6, 0]]
    broken = _row("BSpline", {"degree": 2, "controlPoints": controls, "weights": [1] * 6, "knots": [0, 0, 0, 0.5, 0.5, 0.5, 1, 1, 1]})
    assert carrier_linearize.linearize_record(broken)[0] == "ID_DegenerateEntity"
    backwards = _row("BSpline", {"degree": 2, "controlPoints": controls, "weights": [1] * 6, "knots": [0, 0, 0, 0.7, 0.3, 0.5, 1, 1, 1]})
    assert carrier_linearize.linearize_record(backwards)[1] == "B-spline knots decrease or span nothing"


def test_other_kinds_decline() -> None:
    bad = _row("BSpline", {"degree": 3, "controlPoints": [[0, 0], [1, 2], [3, 1], [4, 0]], "weights": [1, -2, 1, 1], "knots": [0, 0, 0, 0, 1, 1, 1, 1]})
    assert carrier_linearize.linearize_record(bad) == ("ID_DegenerateEntity", "B-spline weights are not positive")
    assert carrier_linearize.linearize_record(_row("Spiral", {}))[0] == "ID_UnsupportedEntity"
    # The extractor's default tolerance states no chord height: a curve declines...
    loose = _row("Arc", {"center": [0, 0], "radius": 1, "startAngle": 0, "endAngle": 90})
    loose["tolerance"] = {"kind": "sourceDefault"}
    assert carrier_linearize.linearize_record(loose)[0] == "ID_ToleranceKindUnsupported"
    # ...but a Chord is exact and needs none.
    line = _row("Chord", {"start": [0, 0], "end": [1, 0]})
    line["tolerance"] = {"kind": "sourceDefault"}
    assert carrier_linearize.linearize_record(line) == {"wkt": "LINESTRING (0 0, 1 0)", "hausdorff": 0.0}


def test_evenodd_and_nonzero_hatch_regions_differ_where_contours_nest() -> None:
    square = lambda x, s: [(x, x), (x + s, x), (x + s, x + s), (x, x + s)]

    def contour(points):
        return [{"kind": "Chord", "start": list(a), "end": list(b), "bulge": 0} for a, b in zip(points, points[1:] + points[:1])]

    for rule, area in (("evenodd", 100 - 16), ("nonzero", 100)):
        row = _row("Ring", {"windingRule": rule, "contours": [contour(square(0, 10)), contour(square(3, 4))], "orientation": ["ccw", "ccw"]})
        out = carrier_linearize.linearize_record(row)
        assert shapely.from_wkt(out["wkt"]).area == pytest.approx(area)
        # Chords only: exact, so the bound is 0.
        assert out["hausdorff"] == 0.0 and out["noded"] is False


def test_cli_writes_one_line_per_record(tmp_path, capsys) -> None:
    doc = ezdxf.new("R2018")
    doc.modelspace().add_circle((0, 0), 2)
    doc.modelspace().add_point((1, 1))
    dxf = tmp_path / "c.dxf"
    doc.saveas(dxf)
    records = tmp_path / "c.jsonl"
    assert dxf_extract.main([str(dxf), str(records)]) == 0
    assert carrier_linearize.main([str(records), "--hausdorff", "0.001"]) == 0
    (line,) = capsys.readouterr().out.splitlines()
    import json

    out = json.loads(line)
    ring = shapely.from_wkt(out["wkt"])
    assert ring.is_closed and ring.length == pytest.approx(4 * math.pi, rel=1e-3)


def test_angle_units_other_than_degree_and_radian_decline() -> None:
    for unit in ("grad", "dms", "surveyor"):
        arc = _row("Arc", {"center": [0, 0], "radius": 1, "startAngle": 0, "endAngle": 50, "angleUnit": unit})
        assert carrier_linearize.linearize_record(arc) == ("ID_UnsupportedEntity", f"arc angles in {unit}")
    radians = _row("Arc", {"center": [0, 0], "radius": 1, "startAngle": 0, "endAngle": math.pi / 2, "angleUnit": "radian"})
    end = list(shapely.from_wkt(carrier_linearize.linearize_record(radians)["wkt"]).coords)[-1]
    assert end == pytest.approx((0, 1))


def test_zero_sweep_arc_declines_and_a_whole_turn_is_a_circle() -> None:
    zero = _row("Arc", {"center": [0, 0], "radius": 1, "startAngle": 30, "endAngle": 30})
    assert carrier_linearize.linearize_record(zero) == ("ID_DegenerateEntity", "an arc of zero sweep")
    whole = _row("Arc", {"center": [0, 0], "radius": 1, "startAngle": 0, "endAngle": 360})
    ring = shapely.from_wkt(carrier_linearize.linearize_record(whole)["wkt"])
    coords = list(ring.coords)
    assert coords[0] == pytest.approx(coords[-1]) and len(coords) > 4
    assert all(math.hypot(x, y) == pytest.approx(1) for x, y in coords)


@pytest.mark.parametrize(
    "row",
    [
        _row("Compound", {"members": []}),
        _row("BulgePolyline", {"closed": False, "segments": []}),
        _row("BSpline", {"degree": 3, "controlPoints": [[0, 0], [1, 2], [3, 1], [4, 0]], "weights": [1] * 4}),
        _row("Ring", {"windingRule": "nonzero", "contours": []}),
        _row("Chord", {"start": [0, 0]}),
        _row("Arc", {"center": "x", "radius": 1, "startAngle": 0, "endAngle": 1}),
        {"record": "entity", "kind": "Circle"},
    ],
)
def test_malformed_records_decline_instead_of_raising(row) -> None:
    out = carrier_linearize.linearize_record(row)
    assert isinstance(out, tuple) and out[0].startswith("ID_")


def test_cli_survives_a_bad_row(tmp_path, capsys) -> None:
    import json

    good = _row("Chord", {"start": [0, 0], "end": [1, 0]})
    lines = [json.dumps(_row("Compound", {"members": []})), "{not json", json.dumps(good)]
    records = tmp_path / "mixed.jsonl"
    records.write_text("\n".join(lines), encoding="utf-8")
    assert carrier_linearize.main([str(records)]) == 0
    out = [json.loads(line) for line in capsys.readouterr().out.splitlines()]
    assert [("decline" in o, "wkt" in o) for o in out] == [(True, False), (True, False), (False, True)]


def test_bspline_clamping_is_checked_and_equal_weights_are_polynomial() -> None:
    controls = [[0, 0], [1, 2], [3, 1], [4, 0]]
    unclamped = _row("BSpline", {"degree": 3, "controlPoints": controls, "weights": [1] * 4, "knots": [0, 1, 2, 3, 4, 5, 6, 7]})
    assert carrier_linearize.linearize_record(unclamped)[0] == "ID_UnclampedKnots"
    short = _row("BSpline", {"degree": 3, "controlPoints": controls, "weights": [1] * 4, "knots": [0, 0, 0, 1, 1, 1]})
    assert carrier_linearize.linearize_record(short)[0] == "ID_UnclampedKnots"
    plain = _row("BSpline", {"degree": 3, "controlPoints": controls, "weights": [1] * 4, "knots": [0, 0, 0, 0, 1, 1, 1, 1]})
    scaled = _row("BSpline", {"degree": 3, "controlPoints": controls, "weights": [2.5] * 4, "knots": [0, 0, 0, 0, 1, 1, 1, 1]})
    nearly = _row("BSpline", {"degree": 3, "controlPoints": controls, "weights": [1, 1 + 5e-10, 1, 1], "knots": [0, 0, 0, 0, 1, 1, 1, 1]})
    reference = carrier_linearize.linearize_record(plain)["wkt"]
    assert carrier_linearize.linearize_record(scaled)["wkt"] == reference
    assert carrier_linearize.linearize_record(nearly)["wkt"] == reference


def test_angle_step_cuts_arcs_and_reports_the_matching_bound() -> None:
    arc = _row("Arc", {"center": [0, 0], "radius": 10, "startAngle": 0, "endAngle": 90})
    arc["tolerance"] = {"kind": "angleStep", "alpha": 10, "angleUnit": "degree", "direction": "ccw-ocs"}
    out = carrier_linearize.linearize_record(arc)
    points = list(shapely.from_wkt(out["wkt"]).coords)
    steps = [math.atan2(b[1], b[0]) - math.atan2(a[1], a[0]) for a, b in zip(points, points[1:])]
    assert max(steps) <= math.radians(10) + 1e-12 and len(steps) in (9, 10)
    assert out["hausdorff"] == pytest.approx(10 * (1 - math.cos(math.radians(5))))
    bezier = _row("Bezier", {"degree": 2, "controlPoints": [[0, 0], [1, 2], [2, 0]]})
    bezier["tolerance"] = arc["tolerance"]
    assert carrier_linearize.linearize_record(bezier)[0] == "ID_ToleranceKindUnsupported"


def test_full_circle_keeps_three_segments_at_any_tolerance() -> None:
    circle = _row("Circle", {"center": [0, 0], "radius": 1})
    ring = shapely.from_wkt(carrier_linearize.linearize_record(circle, hausdorff=5.0)["wkt"])
    assert len(ring.coords) == 4 and shapely.Polygon(ring).area > 0


@pytest.mark.parametrize("seed", range(30))
def test_ring_fast_path_agrees_with_exact_noding(seed: int) -> None:
    """Nested, non-meeting contours: the winding fast path and full noding fill the same region."""
    import nonzero_node

    rng = random.Random(seed)
    def contour(x, y, size, clockwise):
        corners = [(x, y), (x + size, y), (x + size, y + size), (x, y + size)]
        corners = corners[::-1] if clockwise else corners
        return [{"kind": "Chord", "start": list(a), "end": list(b), "bulge": 0} for a, b in zip(corners, corners[1:] + corners[:1])]
    contours = [contour(0, 0, 20, rng.random() < 0.5)]
    for _ in range(rng.randint(1, 4)):
        size = rng.uniform(1, 4)
        contours.append(contour(rng.uniform(1, 15), rng.uniform(1, 15), size, rng.random() < 0.5))
    for rule in ("nonzero", "evenodd"):
        row = _row("Ring", {"windingRule": rule, "contours": contours, "orientation": ["ccw"] * len(contours)})
        rings = [[tuple(seg["start"]) for seg in c] for c in contours]
        out = carrier_linearize.linearize_record(row)
        if isinstance(out, tuple) or out["noded"]:
            continue  # contours that touch take the noded path
        exact = nonzero_node.nonzero_polygons(rings, rule)
        expected = shapely.MultiPolygon([shapely.Polygon([(float(x), float(y)) for x, y in s], [[(float(x), float(y)) for x, y in h] for h in hs]) for s, hs in exact])
        assert shapely.from_wkt(out["wkt"]).symmetric_difference(expected).area == pytest.approx(0, abs=1e-9)


def test_lenient_notes_travel_with_the_wkt() -> None:
    """The bound is to the record; what lenient left out of the record is not dropped."""
    doc = ezdxf.new("R2018")
    doc.modelspace().add_lwpolyline([(0, 0), (5, 0), (5, 3)], dxfattribs={"const_width": 0.8, "thickness": 2})
    doc.modelspace().add_lwpolyline([(0, 0), (5, 0), (5, 3)])
    wide, plain = dxf_extract.extract_document(doc, mode="lenient", file_id="notes")
    out = carrier_linearize.linearize_record(wide, _BOUND)
    assert out["wkt"] == "LINESTRING (0.0 0.0, 5.0 0.0, 5.0 3.0)"
    assert out["lenient"] == [{"ignored": "thickness", "value": 2.0}, {"ignored": "width", "value": 0.8}]
    assert "lenient" not in carrier_linearize.linearize_record(plain, _BOUND)


def _ellipse_row(center, major, ratio, start, end) -> dict:
    return _row("Ellipse", {
        "center": list(center), "majorAxis": list(major), "ratio": ratio,
        "startParam": start, "endParam": end, "angleUnit": "radian", "direction": "ccw-ocs",
    })


@pytest.mark.parametrize("seed", range(40))
def test_ellipse_arcs_are_within_their_bound_of_ezdxfs_ellipse(seed: int) -> None:
    """Partial arcs (including ones that wrap past 2 pi, end < start) against ezdxf's own ellipse,
    and the bound against the exact curve sampled densely."""
    from ezdxf.math import ConstructionEllipse

    rng = random.Random(seed)
    center = (rng.uniform(-50, 50), rng.uniform(-50, 50))
    angle, length = rng.uniform(0, 2 * math.pi), rng.uniform(0.5, 40)
    major = (length * math.cos(angle), length * math.sin(angle))
    ratio = rng.uniform(0.05, 1.0)
    start, end = rng.uniform(-7, 7), rng.uniform(-7, 7)
    d = rng.choice([0.001, 0.01, 0.1])
    row = _ellipse_row(center, major, ratio, start, end)
    out = carrier_linearize.linearize_record(row, hausdorff=d)
    assert 0 < out["hausdorff"] <= d
    ours = shapely.from_wkt(out["wkt"])

    theirs = ConstructionEllipse(
        center=(*center, 0), major_axis=(*major, 0), ratio=ratio, start_param=start, end_param=end
    )
    reference = shapely.LineString([(v.x, v.y) for v in theirs.flattening(_FINE / 10)])
    assert ours.hausdorff_distance(reference) <= out["hausdorff"] + _FINE / 10 + 1e-9

    # The exact curve, sampled densely: every chord stays within the bound.
    sweep = (end - start) % (2 * math.pi)
    nx, ny = -ratio * major[1], ratio * major[0]
    dense = [
        (center[0] + major[0] * math.cos(t) + nx * math.sin(t), center[1] + major[1] * math.cos(t) + ny * math.sin(t))
        for t in (start + sweep * k / 20000 for k in range(20001))
    ]
    assert ours.hausdorff_distance(shapely.LineString(dense)) <= out["hausdorff"] + 1e-6 * length


def test_ellipse_step_count_is_the_least_that_meets_the_bound() -> None:
    points, bound = carrier_linearize.ellipse_points((0, 0), (10, 0), 0.5, 0.0, math.pi, 0.01)
    count = len(points) - 1
    assert bound <= 0.01 < 10 * (math.pi / (count - 1)) ** 2 / 8
    # A whole ellipse is closed and keeps three segments at any tolerance.
    row = _ellipse_row((0, 0), (1, 0), 0.5, 0.0, 2 * math.pi)
    coarse = carrier_linearize.linearize_record(row, hausdorff=100.0)
    ring = shapely.from_wkt(coarse["wkt"])
    assert ring.is_closed and len(ring.coords) == 4


def test_ellipse_runs_counter_clockwise_about_its_major_axis() -> None:
    """From the major axis end (t = 0) a quarter turn reaches the minor axis end, to the left."""
    row = _ellipse_row((0, 0), (0, 4), 0.5, 0.0, math.pi / 2)  # major axis points up
    coords = shapely.from_wkt(carrier_linearize.linearize_record(row, hausdorff=0.01)["wkt"]).coords
    assert coords[0] == pytest.approx((0, 4))
    assert coords[-1] == pytest.approx((-2, 0))  # the minor axis, a quarter turn CCW from up


@pytest.mark.parametrize(
    ("params", "reason"),
    [
        ({"ratio": 0.0}, "an ellipse with no area"),
        ({"majorAxis": [0, 0]}, "an ellipse with no area"),
        ({"endParam": 1.0}, "an ellipse arc of zero sweep"),
        ({"ratio": math.nan}, "a non-finite ellipse number"),
    ],
)
def test_degenerate_ellipses_decline(params: dict, reason: str) -> None:
    row = _ellipse_row((0, 0), (2, 0), 0.5, 1.0, 2.0)
    row["params"].update(params)
    assert carrier_linearize.linearize_record(row, hausdorff=0.01) == ("ID_DegenerateEntity", reason)


def test_ellipse_ignores_an_angle_step() -> None:
    row = _ellipse_row((0, 0), (2, 0), 0.5, 0.0, 1.0)
    row["tolerance"] = {"kind": "angleStep", "alpha": 5, "angleUnit": "degree", "direction": "ccw-ocs"}
    assert carrier_linearize.linearize_record(row)[0] == "ID_ToleranceKindUnsupported"


_S = math.sqrt(0.5)
# A whole circle of radius 2 about (1, -1): the standard 9-point degree-2 NURBS.
_CIRCLE = {
    "degree": 2,
    "controlPoints": [[1 + 2 * x, -1 + 2 * y] for x, y in [(1, 0), (1, 1), (0, 1), (-1, 1), (-1, 0), (-1, -1), (0, -1), (1, -1), (1, 0)]],
    "weights": [1, _S, 1, _S, 1, _S, 1, _S, 1],
    "knots": [0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 4],
}


@pytest.mark.parametrize("d", [0.1, 0.01, 0.0001])
def test_rational_circle_vertices_are_on_the_circle(d: float) -> None:
    """A rational quadratic draws a true circle: every vertex lies on it, every chord's sagitta is within the bound."""
    out = carrier_linearize.linearize_record(_row("BSpline", _CIRCLE), hausdorff=d)
    assert 0 < out["hausdorff"] <= d
    coords = list(shapely.from_wkt(out["wkt"]).coords)
    assert coords[0] == pytest.approx(coords[-1])
    for x, y in coords:
        assert math.hypot(x - 1, y + 1) == pytest.approx(2, abs=1e-12)
    sagittas = [2 - math.hypot((a[0] + b[0]) / 2 - 1, (a[1] + b[1]) / 2 + 1) for a, b in zip(coords, coords[1:])]
    assert max(sagittas) <= out["hausdorff"] + 1e-12
    # No more than twice the chords the circle itself needs at this bound.
    needed = math.ceil(2 * math.pi / (2 * math.acos(1 - d / 2)))
    assert len(coords) - 1 <= 2 * needed


@pytest.mark.parametrize("seed", range(40))
def test_rational_bsplines_are_within_their_bound_of_ezdxfs_curve(seed: int) -> None:
    from ezdxf.math import BSpline as EzBSpline

    rng = random.Random(seed)
    degree = rng.choice([2, 3, 4])
    count = rng.randint(degree + 1, degree + 6)
    controls = [[rng.uniform(-20, 20), rng.uniform(-20, 20)] for _ in range(count)]
    weights = [rng.choice([1.0, rng.uniform(0.05, 20)]) for _ in range(count)]
    weights[0] = 1.0
    weights[rng.randrange(count)] = rng.uniform(2, 20)  # surely rational
    interior = sorted(rng.uniform(0, 1) for _ in range(count - degree - 1))
    knots = [0.0] * (degree + 1) + interior + [1.0] * (degree + 1)
    d = rng.choice([0.001, 0.01, 0.1])
    params = {"degree": degree, "controlPoints": controls, "weights": weights, "knots": knots}
    out = carrier_linearize.linearize_record(_row("BSpline", params), hausdorff=d)
    assert not isinstance(out, tuple), out
    assert 0 <= out["hausdorff"] <= d
    curve = EzBSpline([(x, y, 0) for x, y in controls], order=degree + 1, knots=knots, weights=weights)
    dense = shapely.LineString([(v.x, v.y) for v in curve.points([k / 20000 for k in range(20001)])])
    assert shapely.from_wkt(out["wkt"]).hausdorff_distance(dense) <= out["hausdorff"] + 1e-6 * 40


def test_a_rational_dxf_spline_reaches_wkt() -> None:
    doc = ezdxf.new("R2018")
    spline = doc.modelspace().add_rational_spline(
        [(0, 0), (1, 2), (3, 2), (4, 0)], weights=[1, 3, 0.5, 1], degree=3
    )
    (row,) = dxf_extract.extract_document(doc, file_id="nurbs", tolerance={"kind": "sagitta", "d": 0.01})
    assert row["kind"] == "BSpline" and row["params"]["weights"] == [1, 3, 0.5, 1]
    out = carrier_linearize.linearize_record(row)
    reference = shapely.LineString([(v.x, v.y) for v in spline.construction_tool().points([k / 5000 for k in range(5001)])])
    assert shapely.from_wkt(out["wkt"]).hausdorff_distance(reference) <= out["hausdorff"] + 1e-6
