"""Locked R2000 LWPOLYLINE fixture: ezdxf flatten vs the carrier arc."""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path

import ezdxf
import pytest
from jsonschema import Draft202012Validator

import dxf_extract
from fixtures.gen_lwpolyline_mixed_bulges import (
    DXF_PATH,
    JSON_PATH,
    render,
)

# Roundoff on these radii sits near 1e-15. This is not the sagitta.
FLOAT_EPS = 1e-12

DXF_SHA256 = "d73d7da28b8de3ba9b10c7bbc2a38d793b5903059d1c2e9c4eec195bd90a0504"
JSON_SHA256 = "74ab9acb256bbd99b2689b11532fbb9b40f22cbed33cd6ab0462b14509c216b7"

SCHEMA = json.loads(dxf_extract.SCHEMA_PATH.read_text(encoding="utf-8"))
VALIDATOR = Draft202012Validator(SCHEMA)


def test_ezdxf_requirement_is_exact_pin() -> None:
    text = (Path(__file__).resolve().parents[1] / "requirements.txt").read_text(encoding="utf-8")
    assert "ezdxf==1.4.4\n" in text


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


def test_bulge_arcs_match_ezdxf_flatten_within_sagitta() -> None:
    locked = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert locked["ezdxf"] == "1.4.4"
    sagitta = locked["sagitta"]
    assert locked["flattening"] == {"distance": sagitta}
    assert sagitta == locked["flattening"]["distance"]

    rows = dxf_extract.extract_path(DXF_PATH, mode="strict")
    assert rows
    assert all(row["record"] == "entity" for row in rows)
    for row in rows:
        VALIDATOR.validate(row)
    polys = [row for row in rows if row["kind"] == "BulgePolyline"]
    assert len(polys) == len(locked["polylines"]) == 2

    open_bulges = [seg["bulge"] for seg in polys[0]["params"]["segments"]]
    closed_segments = polys[1]["params"]["segments"]
    closed_bulges = [seg["bulge"] for seg in closed_segments]
    assert open_bulges == pytest.approx([0.0, 1.0, -0.5])
    assert polys[0]["params"]["closed"] is False
    assert closed_bulges == pytest.approx([0.0, 0.4, -1.0, 0.25])
    assert polys[1]["params"]["closed"] is True

    drawing = ezdxf.readfile(DXF_PATH)
    closed_entity = next(e for e in drawing.modelspace() if e.dxftype() == "LWPOLYLINE" and e.closed)
    vertices = list(closed_entity.get_points("xyb"))
    last = closed_segments[-1]
    assert last["kind"] == "Arc"
    assert last["bulge"] == pytest.approx(vertices[-1][2])
    assert last["bulge"] != pytest.approx(vertices[0][2])
    assert last["start"] == pytest.approx([vertices[-1][0], vertices[-1][1]])
    assert last["end"] == pytest.approx([vertices[0][0], vertices[0][1]])

    for poly, spec in zip(polys, locked["polylines"]):
        assert poly["params"]["closed"] is spec["closed"]
        arcs = [seg for seg in poly["params"]["segments"] if seg["kind"] == "Arc"]
        assert len(arcs) == len(spec["arcs"])
        assert any(seg["kind"] == "Chord" for seg in poly["params"]["segments"])
        for seg, arc in zip(arcs, spec["arcs"]):
            assert seg["bulge"] == pytest.approx(arc["bulge"])
            points = [(float(p[0]), float(p[1])) for p in arc["points"]]
            circle = _circle(seg["start"], seg["end"], seg["bulge"])
            a = (float(seg["start"][0]), float(seg["start"][1]))
            b = (float(seg["end"][0]), float(seg["end"][1]))
            for point in points:
                assert _dist_point_arc(point, a, b, circle) <= FLOAT_EPS
            for left, right in zip(points, points[1:]):
                mid = ((left[0] + right[0]) / 2.0, (left[1] + right[1]) / 2.0)
                assert _dist_point_arc(mid, a, b, circle) <= sagitta
