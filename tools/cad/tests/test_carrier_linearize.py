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
    assert carrier_linearize.linearize_record(backwards)[1] == "B-spline knots decrease"


def test_rational_bspline_and_other_kinds_decline() -> None:
    rational = _row("BSpline", {"degree": 3, "controlPoints": [[0, 0], [1, 2], [3, 1], [4, 0]], "weights": [1, 2, 1, 1], "knots": [0, 0, 0, 0, 1, 1, 1, 1]})
    assert carrier_linearize.linearize_record(rational)[1].startswith("rational B-spline")
    assert carrier_linearize.linearize_record(_row("Spiral", {}))[0] == "ID_UnsupportedEntity"
    loose = _row("Chord", {"start": [0, 0], "end": [1, 0]})
    loose["tolerance"] = {"kind": "sourceDefault"}
    assert carrier_linearize.linearize_record(loose)[0] == "ID_ToleranceKindUnsupported"


def test_evenodd_and_nonzero_hatch_regions_differ_where_contours_nest() -> None:
    square = lambda x, s: [(x, x), (x + s, x), (x + s, x + s), (x, x + s)]

    def contour(points):
        return [{"kind": "Chord", "start": list(a), "end": list(b), "bulge": 0} for a, b in zip(points, points[1:] + points[:1])]

    for rule, area in (("evenodd", 100 - 16), ("nonzero", 100)):
        row = _row("Ring", {"windingRule": rule, "contours": [contour(square(0, 10)), contour(square(3, 4))], "orientation": ["ccw", "ccw"]})
        out = carrier_linearize.linearize_record(row)
        assert shapely.from_wkt(out["wkt"]).area == pytest.approx(area)
        assert out["hausdorff"] == 0.01 and out["noded"] is False


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
