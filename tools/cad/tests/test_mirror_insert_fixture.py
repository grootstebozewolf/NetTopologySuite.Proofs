"""Locked mirrored INSERT of an arc: reflection negates orientation, then Hausdorff."""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

import dxf_extract
from fixtures.gen_mirror_insert_arc import DXF_PATH, JSON_PATH, render

FLOAT_EPS = 1e-12

DXF_SHA256 = "d6a3e0217b4f0e30c8fdcae74dffc7f03491d65272d89cc21d6e573566bf5eef"
JSON_SHA256 = "88b23670de9bdc7dd0f5a699c481e4797ba98ec29f08e9116d473f439b501d06"

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


def _apply(point: tuple[float, float], link: dict) -> tuple[float, float]:
    """Reflect, then uniform scale, then rotate, then translate."""
    x, y = point
    if link["reflect"]:
        x = -x
    scale = link["scale"]
    x *= scale
    y *= scale
    angle = math.radians(link["rotate"])
    cosine, sine = math.cos(angle), math.sin(angle)
    rotated_x = cosine * x - sine * y
    rotated_y = sine * x + cosine * y
    return rotated_x + link["translate"][0], rotated_y + link["translate"][1]


def _cross(a: tuple[float, float], b: tuple[float, float]) -> float:
    return a[0] * b[1] - a[1] * b[0]


def _signed_delta_deg(start: float, end: float) -> float:
    delta = (end - start) % 360.0
    if delta > 180.0:
        delta -= 360.0
    return delta


def _dist_point_arc(
    point: tuple[float, float],
    center: tuple[float, float],
    radius: float,
    start_angle: float,
    sweep: float,
    start: tuple[float, float],
    end: tuple[float, float],
) -> float:
    angle = math.atan2(point[1] - center[1], point[0] - center[0])
    if sweep >= 0.0:
        delta = (angle - start_angle) % math.tau
    else:
        delta = (start_angle - angle) % math.tau
    if delta <= abs(sweep):
        return abs(math.hypot(point[0] - center[0], point[1] - center[1]) - radius)
    return min(math.dist(point, start), math.dist(point, end))


def test_reflection_negates_orientation_and_matches_placed_arc() -> None:
    locked = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert locked["ezdxf"] == "1.4.4"
    assert locked["xscale"] == -1
    sagitta = locked["sagitta"]
    assert locked["flattening"] == {"distance": sagitta}

    rows = dxf_extract.extract_path(DXF_PATH, mode="strict")
    assert len(rows) == 1
    row = rows[0]
    VALIDATOR.validate(row)
    assert row["record"] == "entity"
    assert row["kind"] == "Arc"
    assert row["provenance"]["blockPath"] == [locked["block"]]
    assert row["placement"]["s"] == -1
    link = row["placement"]["links"][0]
    assert link["reflect"] is True
    assert link["scale"] == pytest.approx(1)
    assert link["rotate"] == pytest.approx(0)
    assert link["translate"] == pytest.approx(locked["insert"])

    params = row["params"]
    assert params["direction"] == "ccw-ocs"
    assert params["angleUnit"] == "degree"
    assert params["radius"] == pytest.approx(locked["radius"])
    assert params["startAngle"] == pytest.approx(locked["startAngle"])
    assert params["endAngle"] == pytest.approx(locked["endAngle"])
    local_center = (params["center"][0], params["center"][1])
    radius = params["radius"]
    start_deg = params["startAngle"]
    end_deg = params["endAngle"]
    delta_theta = end_deg - start_deg
    assert delta_theta > 0

    def local_point(degrees: float) -> tuple[float, float]:
        radians = math.radians(degrees)
        return (
            local_center[0] + radius * math.cos(radians),
            local_center[1] + radius * math.sin(radians),
        )

    local_start = local_point(start_deg)
    local_end = local_point(end_deg)
    world_center = _apply(local_center, link)
    world_start = _apply(local_start, link)
    world_end = _apply(local_end, link)
    world_radius = radius * link["scale"]

    sign = row["placement"]["s"]
    local_cross = _cross(
        (local_start[0] - local_center[0], local_start[1] - local_center[1]),
        (local_end[0] - local_center[0], local_end[1] - local_center[1]),
    )
    world_cross = _cross(
        (world_start[0] - world_center[0], world_start[1] - world_center[1]),
        (world_end[0] - world_center[0], world_end[1] - world_center[1]),
    )
    # #918: s = -1 negates Δθ, the winding value, and σ before checking.
    world_delta = _signed_delta_deg(
        math.degrees(math.atan2(world_start[1] - world_center[1], world_start[0] - world_center[0])),
        math.degrees(math.atan2(world_end[1] - world_center[1], world_end[0] - world_center[0])),
    )
    assert world_delta == pytest.approx(sign * delta_theta)
    winding = 0.5 * local_cross
    assert 0.5 * world_cross == pytest.approx(sign * winding)
    sigma = math.copysign(1.0, local_cross)
    assert math.copysign(1.0, world_cross) == sign * sigma

    points = [(float(p[0]), float(p[1])) for p in locked["points"]]
    assert math.dist(points[0], world_start) <= FLOAT_EPS
    assert math.dist(points[-1], world_end) <= FLOAT_EPS
    start_angle = math.atan2(world_start[1] - world_center[1], world_start[0] - world_center[0])
    sweep = math.radians(sign * delta_theta)
    for point in points:
        assert _dist_point_arc(point, world_center, world_radius, start_angle, sweep, world_start, world_end) <= FLOAT_EPS
    for left, right in zip(points, points[1:]):
        mid = ((left[0] + right[0]) / 2.0, (left[1] + right[1]) / 2.0)
        assert _dist_point_arc(mid, world_center, world_radius, start_angle, sweep, world_start, world_end) <= sagitta
        turn = _signed_delta_deg(
            math.degrees(math.atan2(left[1] - world_center[1], left[0] - world_center[0])),
            math.degrees(math.atan2(right[1] - world_center[1], right[0] - world_center[0])),
        )
        chord_sagitta = world_radius * (1.0 - math.cos(math.radians(abs(turn)) / 2.0))
        assert chord_sagitta <= sagitta
