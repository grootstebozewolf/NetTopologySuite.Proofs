"""Exact nonzero-winding noding, against shapely and against the winding number itself."""

from __future__ import annotations

import random
from fractions import Fraction
from pathlib import Path

import pytest
import shapely

import glyph_linearize
import nonzero_node


def _sq(x: float, y: float, s: float) -> list[tuple[float, float]]:
    return [(x, y), (x + s, y), (x + s, y + s), (x, y + s)]


_DIAMOND = [(0, 2), (1, 3), (2, 2), (1, 1)]  # clockwise


def _shape(rings) -> shapely.MultiPolygon:
    as_float = lambda ring: [(float(x), float(y)) for x, y in ring]
    return shapely.MultiPolygon(
        [shapely.Polygon(as_float(shell), [as_float(hole) for hole in holes]) for shell, holes in nonzero_node.nonzero_polygons(rings)]
    )


@pytest.mark.parametrize(
    ("rings", "polygons", "holes", "area"),
    [
        ([_sq(0, 0, 2), _sq(1, 1, 2)], 1, 0, 7),
        ([_sq(0, 0, 2), _sq(1, 1, 2)[::-1]], 2, 0, 6),
        ([[(0, 1), (3, 1), (3, 2), (0, 2)], [(1, 0), (2, 0), (2, 3), (1, 3)]], 1, 0, 5),
        ([_sq(0, 0, 1), _sq(1, 0, 1)], 1, 0, 2),
        ([_sq(0, 0, 1), _sq(1, 1, 1)], 2, 0, 2),
        ([[(0, 0), (2, 2), (2, 0), (0, 2)]], 2, 0, 2),
        ([_sq(0, 0, 4), _sq(1, 1, 1)], 1, 0, 16),
        ([_sq(0, 0, 4), _sq(1, 1, 1)[::-1]], 1, 1, 15),
        ([_sq(0, 0, 4), _DIAMOND], 1, 1, 14),
        ([_sq(0, 0, 4), _DIAMOND[::-1]], 1, 0, 16),
        ([_sq(0, 0, 1), _sq(0, 0, 1)], 1, 0, 1),
        ([_sq(0, 0, 1), _sq(0, 0, 1)[::-1]], 0, 0, 0),
        ([_sq(0, 0, 6), _sq(1, 1, 4)[::-1], [(-1, 2.5), (7, 2.5), (7, 3.5), (-1, 3.5)]], 1, 2, 26),
        ([_sq(0, 0, 6), _sq(1, 1, 4)[::-1], _sq(2, 2, 2), _sq(2.5, 2.5, 1)[::-1]], 2, 2, 20 + 3),
    ],
)
def test_known_arrangements(rings, polygons, holes, area) -> None:
    shape = _shape(rings)
    assert shape.is_valid
    assert len(shape.geoms) == polygons
    assert sum(len(p.interiors) for p in shape.geoms) == holes
    assert shape.area == area
    for polygon in shape.geoms:
        assert polygon.exterior.is_ccw
        assert not any(ring.is_ccw for ring in polygon.interiors)


def test_crossing_point_is_exact() -> None:
    ((shell, holes),) = nonzero_node.nonzero_polygons([[(0, 0), (3, 0), (0, 1)], [(0, 0), (1, 0), (1, 3)][::-1][::-1]])
    assert not holes
    # Edge (3,0)-(0,1) meets edge (1,0)-(1,3) at (1, 2/3), which no float holds.
    assert (Fraction(1), Fraction(2, 3)) in shell


def _float_winding(rings, point) -> int:
    return sum(glyph_linearize.winding(ring, point) for ring in rings)


@pytest.mark.parametrize("seed", range(12))
def test_random_rings_match_the_winding_number_and_shapely(seed: int) -> None:
    rng = random.Random(seed)
    rings = []
    for _ in range(rng.randint(2, 6)):
        cx, cy = rng.uniform(0, 10), rng.uniform(0, 10)
        if rng.random() < 0.5:
            ring = _sq(cx, cy, rng.uniform(1, 6))
        else:
            ring = [(cx + rng.uniform(-4, 4), cy + rng.uniform(-4, 4)) for _ in range(rng.randint(3, 6))]
        rings.append(ring if rng.random() < 0.6 else ring[::-1])
    shape = _shape(rings)
    assert shape.is_valid
    # Membership is the winding number, wherever the probe is clear of every edge.
    lines = shapely.MultiLineString([ring + ring[:1] for ring in rings])
    checked = 0
    for _ in range(400):
        point = (rng.uniform(-5, 16), rng.uniform(-5, 16))
        if lines.distance(shapely.Point(point)) < 1e-6:
            continue
        assert shape.contains(shapely.Point(point)) == (_float_winding(rings, point) != 0), point
        checked += 1
    assert checked > 350
    # With every ring counter-clockwise, nonzero fill is the plain union.
    simple = [ring for ring in rings if shapely.Polygon(ring).is_valid]
    ccw = [ring if shapely.LinearRing(ring).is_ccw else ring[::-1] for ring in simple]
    if ccw:
        union = shapely.unary_union([shapely.Polygon(ring) for ring in ccw])
        assert _shape(ccw).area == pytest.approx(union.area, rel=1e-12)


def test_shapely_requirement_is_an_exact_pin() -> None:
    text = (Path(__file__).resolve().parents[1] / "requirements.txt").read_text(encoding="utf-8")
    assert "shapely==2.2.0\n" in text
