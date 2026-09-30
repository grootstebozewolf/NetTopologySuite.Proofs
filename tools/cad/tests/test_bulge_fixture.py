"""Locked R2000 LWPOLYLINE fixture: ezdxf flatten vs the carrier arc."""

from __future__ import annotations

import hashlib
import json
import math

import pytest
from jsonschema import Draft202012Validator

import dxf_extract
from fixtures.gen_lwpolyline_mixed_bulges import (
    DXF_PATH,
    JSON_PATH,
    render,
)

# Samples are at most this far apart. Distance-to-set is 1-Lipschitz, so the
# continuous Hausdorff is at most the sampled value plus half this gap.
SAMPLE_SPACING = 1e-4

DXF_SHA256 = "c446729ede1fcf952718dc3e7ef5f5c5d3e8471a4254036048f59a7394f4d74a"
JSON_SHA256 = "ce74601f2f8fbef0ee4f5a3c84803ba1f22afa9e000fc058055fe34d8120bcbc"

SCHEMA = json.loads(dxf_extract.SCHEMA_PATH.read_text(encoding="utf-8"))
VALIDATOR = Draft202012Validator(SCHEMA)


def test_fixture_files_are_byte_stable() -> None:
    dxf, ref = render()
    assert hashlib.sha256(DXF_PATH.read_bytes()).hexdigest() == DXF_SHA256
    assert hashlib.sha256(JSON_PATH.read_bytes()).hexdigest() == JSON_SHA256
    assert hashlib.sha256(dxf).hexdigest() == DXF_SHA256
    assert hashlib.sha256(ref).hexdigest() == JSON_SHA256


def _circle(start: list[float], end: list[float], bulge: float) -> tuple[float, float, float, float, float]:
    """Centre and radius from the chord and bulge.

    θ = 4 atan(b), R = c / (2 sin(|θ|/2)), centre = M + sign(θ) N R cos(θ/2),
    where N is the left unit normal of the directed chord.
    """
    theta = 4.0 * math.atan(bulge)
    dx = end[0] - start[0]
    dy = end[1] - start[1]
    chord = math.hypot(dx, dy)
    half = abs(theta) / 2.0
    radius = chord / (2.0 * math.sin(half))
    mid_x = (start[0] + end[0]) / 2.0
    mid_y = (start[1] + end[1]) / 2.0
    nx = -dy / chord
    ny = dx / chord
    sign = 1.0 if theta > 0.0 else -1.0
    offset = sign * radius * math.cos(half)
    center_x = mid_x + nx * offset
    center_y = mid_y + ny * offset
    start_angle = math.atan2(start[1] - center_y, start[0] - center_x)
    return center_x, center_y, radius, start_angle, theta


def _dist_point_arc(
    point: tuple[float, float],
    start: tuple[float, float],
    end: tuple[float, float],
    circle: tuple[float, float, float, float, float],
) -> float:
    cx, cy, radius, start_angle, sweep = circle
    angle = math.atan2(point[1] - cy, point[0] - cx)
    if sweep >= 0.0:
        delta = (angle - start_angle) % math.tau
    else:
        delta = (start_angle - angle) % math.tau
    if delta <= abs(sweep):
        return abs(math.hypot(point[0] - cx, point[1] - cy) - radius)
    return min(math.dist(point, start), math.dist(point, end))


def _dist_point_segment(
    point: tuple[float, float],
    a: tuple[float, float],
    b: tuple[float, float],
) -> float:
    vx = b[0] - a[0]
    vy = b[1] - a[1]
    length2 = vx * vx + vy * vy
    if length2 == 0.0:
        return math.dist(point, a)
    t = ((point[0] - a[0]) * vx + (point[1] - a[1]) * vy) / length2
    t = max(0.0, min(1.0, t))
    return math.hypot(point[0] - (a[0] + t * vx), point[1] - (a[1] + t * vy))


def _sample_polyline(points: list[tuple[float, float]]) -> list[tuple[float, float]]:
    out = [points[0]]
    for a, b in zip(points, points[1:]):
        steps = max(1, math.ceil(math.dist(a, b) / SAMPLE_SPACING))
        for i in range(1, steps + 1):
            t = i / steps
            out.append((a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t))
    return out


def _sample_arc(circle: tuple[float, float, float, float, float]) -> list[tuple[float, float]]:
    cx, cy, radius, start_angle, sweep = circle
    steps = max(1, math.ceil(abs(sweep) * radius / SAMPLE_SPACING))
    return [
        (
            cx + radius * math.cos(start_angle + sweep * i / steps),
            cy + radius * math.sin(start_angle + sweep * i / steps),
        )
        for i in range(steps + 1)
    ]


def _hausdorff(
    polyline: list[list[float]],
    start: list[float],
    end: list[float],
    bulge: float,
) -> float:
    points = [(float(p[0]), float(p[1])) for p in polyline]
    circle = _circle(start, end, bulge)
    a = (float(start[0]), float(start[1]))
    b = (float(end[0]), float(end[1]))
    sampled_line = _sample_polyline(points)
    to_arc = max(_dist_point_arc(p, a, b, circle) for p in sampled_line)
    segments = list(zip(points, points[1:]))
    to_line = max(
        min(_dist_point_segment(q, u, v) for u, v in segments) for q in _sample_arc(circle)
    )
    return max(to_arc, to_line)


def test_bulge_arcs_match_ezdxf_flatten_within_sagitta() -> None:
    locked = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert locked["ezdxf"] == "1.4.4"
    assert locked["flattening"] == {"distance": 0.01, "segments": 4}
    sagitta = locked["sagitta"]
    assert sagitta == locked["flattening"]["distance"]

    rows = dxf_extract.extract_path(DXF_PATH, mode="strict")
    assert rows
    assert all(row["record"] == "entity" for row in rows)
    for row in rows:
        VALIDATOR.validate(row)
    polys = [row for row in rows if row["kind"] == "BulgePolyline"]
    assert len(polys) == len(locked["polylines"]) == 2

    open_bulges = [seg["bulge"] for seg in polys[0]["params"]["segments"]]
    closed_bulges = [seg["bulge"] for seg in polys[1]["params"]["segments"]]
    assert open_bulges == pytest.approx([0.0, 1.0, -0.5])
    assert polys[0]["params"]["closed"] is False
    assert closed_bulges == pytest.approx([0.0, 0.4, -1.0, 0.0])
    assert polys[1]["params"]["closed"] is True

    gap = SAMPLE_SPACING / 2.0
    for poly, spec in zip(polys, locked["polylines"]):
        assert poly["params"]["closed"] is spec["closed"]
        arcs = [seg for seg in poly["params"]["segments"] if seg["kind"] == "Arc"]
        assert len(arcs) == len(spec["arcs"])
        assert any(seg["kind"] == "Chord" for seg in poly["params"]["segments"])
        for seg, arc in zip(arcs, spec["arcs"]):
            assert seg["bulge"] == pytest.approx(arc["bulge"])
            assert seg["bulge"] != 0.0
            distance = _hausdorff(arc["points"], seg["start"], seg["end"], seg["bulge"])
            assert distance + gap <= sagitta
