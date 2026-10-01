"""Locked TrueType lowercase e: fontTools spans versus FreeType."""

from __future__ import annotations

import hashlib
import json
from fractions import Fraction
from pathlib import Path

import freetype
from fontTools.pens.recordingPen import RecordingPen
from fontTools.ttLib import TTFont
from jsonschema import Draft202012Validator

import dxf_extract
from fixtures.gen_truetype_e import JSON_PATH, TTF_PATH, glyph_spans, render

TTF_SHA256 = "0f7de5d9741a277b29a9054f6cdf46a17790746894e827befa0268ba75e5cb76"
JSON_SHA256 = "14e7a1435709e13ab5cf31b2d5d4bc0049252b3d20b74df97af0362a29f6115a"

SCHEMA = json.loads(dxf_extract.SCHEMA_PATH.read_text(encoding="utf-8"))
VALIDATOR = Draft202012Validator(SCHEMA)
_LOAD = freetype.FT_LOAD_NO_SCALE | freetype.FT_LOAD_NO_HINTING | freetype.FT_LOAD_NO_BITMAP
# Fixed rational samples of each quadratic. The same probes classify at 4, 8, 16, and 32.
_FLATTEN_STEPS = 8
_INK = (400, 500)
_COUNTER = (400, 350)
_OUTSIDE = (0, 0)


def test_font_requirements_are_exact_pins() -> None:
    text = (Path(__file__).resolve().parents[1] / "requirements.txt").read_text(encoding="utf-8")
    assert "fonttools==4.66.1\n" in text
    assert "freetype-py==2.5.1\n" in text


def test_fixture_files_are_byte_stable() -> None:
    ttf, payload = render()
    assert hashlib.sha256(TTF_PATH.read_bytes()).hexdigest() == TTF_SHA256
    assert hashlib.sha256(JSON_PATH.read_bytes()).hexdigest() == JSON_SHA256
    assert hashlib.sha256(ttf).hexdigest() == TTF_SHA256
    assert hashlib.sha256(payload.encode()).hexdigest() == JSON_SHA256


def _freetype_spans(path: Path) -> list[list[tuple[tuple[int, int], tuple[int, int], tuple[int, int]]]]:
    face = freetype.Face(str(path))
    face.load_char("e", _LOAD)
    outline = face.glyph.outline
    contours: list[list[tuple[tuple[int, int], tuple[int, int], tuple[int, int]]]] = []
    current: dict[str, tuple[int, int] | None] = {"at": None}

    def move_to(point, _ctx) -> None:
        contours.append([])
        current["at"] = (point.x, point.y)

    def line_to(point, _ctx) -> None:
        raise AssertionError(f"FreeType line span {(point.x, point.y)}")

    def conic_to(control, point, _ctx) -> None:
        start = current["at"]
        assert start is not None
        contours[-1].append((start, (control.x, control.y), (point.x, point.y)))
        current["at"] = (point.x, point.y)

    def cubic_to(_a, _b, _point, _ctx) -> None:
        raise AssertionError("FreeType cubic span")

    outline.decompose(
        context=None,
        move_to=move_to,
        line_to=line_to,
        conic_to=conic_to,
        cubic_to=cubic_to,
    )
    return contours


def _fonttools_spans(path: Path) -> list[list[tuple[tuple[int, int], tuple[int, int], tuple[int, int]]]]:
    """Quadratic spans from the glyf, including implied on-curve midpoints."""
    font = TTFont(path)
    pen = RecordingPen()
    font.getGlyphSet()["e"].draw(pen)
    contours: list[list[tuple[tuple[int, int], tuple[int, int], tuple[int, int]]]] = []
    current: tuple[int, int] | None = None
    for op, args in pen.value:
        if op == "moveTo":
            contours.append([])
            point = args[0]
            current = (int(point[0]), int(point[1]))
        elif op == "qCurveTo":
            assert current is not None
            points = [(int(x), int(y)) for x, y in args]
            for index in range(len(points) - 1):
                control = points[index]
                nxt = points[index + 1]
                end = nxt if index == len(points) - 2 else ((control[0] + nxt[0]) // 2, (control[1] + nxt[1]) // 2)
                contours[-1].append((current, control, end))
                current = end
        elif op in ("closePath", "endPath"):
            continue
        else:
            raise AssertionError(op)
    return contours


def _shoelace(spans: list[tuple[tuple[int, int], tuple[int, int], tuple[int, int]]]) -> int:
    points = [start for start, _control, _end in spans]
    total = 0
    for (x1, y1), (x2, y2) in zip(points, points[1:] + points[:1]):
        total += x1 * y2 - x2 * y1
    return total


def test_e_is_nonzero_ring_of_quadratic_nurbs_and_the_hole_winds_opposite() -> None:
    record = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    VALIDATOR.validate(record)
    assert record["kind"] == "Compound"
    ring, outer_member, hole_member = record["params"]["members"]
    assert ring["kind"] == "Ring"
    assert ring["params"]["windingRule"] == "nonzero"
    assert ring["params"]["orientation"] == ["cw", "ccw"]
    assert outer_member["kind"] == "Compound"
    assert hole_member["kind"] == "Compound"

    expanded = glyph_spans()
    freetype_spans = _freetype_spans(TTF_PATH)
    fonttools_spans = _fonttools_spans(TTF_PATH)
    assert freetype_spans == fonttools_spans == expanded
    assert len(freetype_spans) == 2
    for spans in (freetype_spans, fonttools_spans):
        outer_area = _shoelace(spans[0])
        hole_area = _shoelace(spans[1])
        assert outer_area < 0
        assert hole_area > 0
        assert outer_area * hole_area < 0

    font = TTFont(TTF_PATH)
    glyf = font["glyf"]["e"]
    coords, _ends, _flags = glyf.getCoordinates(font["glyf"])
    stored = {(int(x), int(y)) for x, y in coords}

    for contour, spans, chords in zip(
        (outer_member, hole_member),
        freetype_spans,
        ring["params"]["contours"],
        strict=True,
    ):
        members = contour["params"]["members"]
        assert len(members) == len(spans) == len(chords)
        for member, span, chord in zip(members, spans, chords):
            assert member["kind"] == "Bezier"
            assert member["params"]["degree"] == 2
            assert member["params"]["weights"] == [1, 1, 1]
            assert member["params"]["knots"] == [0, 0, 0, 1, 1, 1]
            assert member["params"]["controlPoints"] == [[x, y] for x, y in span]
            assert chord == {
                "kind": "Chord",
                "start": [span[0][0], span[0][1]],
                "end": [span[2][0], span[2][1]],
                "bulge": 0,
            }
    implied = [span[2] for span in freetype_spans[0] + freetype_spans[1] if span[2] not in stored]
    assert implied


def _quad(p0: tuple[Fraction, Fraction], p1: tuple[Fraction, Fraction], p2: tuple[Fraction, Fraction], t: Fraction) -> tuple[Fraction, Fraction]:
    u = 1 - t
    return (
        u * u * p0[0] + 2 * u * t * p1[0] + t * t * p2[0],
        u * u * p0[1] + 2 * u * t * p1[1] + t * t * p2[1],
    )


def _flatten(member: dict) -> list[tuple[Fraction, Fraction]]:
    """Polygon of one contour. The closing vertex is the first sample, not a duplicate."""
    polygon: list[tuple[Fraction, Fraction]] = []
    for bezier in member["params"]["members"]:
        raw = bezier["params"]["controlPoints"]
        assert len(raw) == 3
        points = [(Fraction(x), Fraction(y)) for x, y in raw]
        for step in range(_FLATTEN_STEPS):
            polygon.append(_quad(points[0], points[1], points[2], Fraction(step, _FLATTEN_STEPS)))
    return polygon


def _on_segment(a: tuple[Fraction, Fraction], b: tuple[Fraction, Fraction], p: tuple[Fraction, Fraction]) -> bool:
    cross = (b[0] - a[0]) * (p[1] - a[1]) - (b[1] - a[1]) * (p[0] - a[0])
    if cross != 0:
        return False
    return min(a[0], b[0]) <= p[0] <= max(a[0], b[0]) and min(a[1], b[1]) <= p[1] <= max(a[1], b[1])


def _nonzero_winding(contours: list[list[tuple[Fraction, Fraction]]], point: tuple[int, int]) -> int:
    """Dan Sunday winding. A probe on a flattened edge is rejected."""
    probe = (Fraction(point[0]), Fraction(point[1]))
    total = 0
    for polygon in contours:
        count = len(polygon)
        for index in range(count):
            start = polygon[index]
            end = polygon[(index + 1) % count]
            assert not _on_segment(start, end, probe)
            cross = (end[0] - start[0]) * (probe[1] - start[1]) - (end[1] - start[1]) * (probe[0] - start[0])
            if start[1] <= probe[1] < end[1] and cross > 0:
                total += 1
            elif start[1] > probe[1] >= end[1] and cross < 0:
                total -= 1
    return total


def test_sample_winding_is_nonzero_in_the_ink_and_zero_in_the_counter_and_outside() -> None:
    record = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    _ring, outer, hole = record["params"]["members"]
    contours = [_flatten(outer), _flatten(hole)]
    assert _nonzero_winding(contours, _INK) == -1
    assert _nonzero_winding(contours, _COUNTER) == 0
    assert _nonzero_winding(contours, _OUTSIDE) == 0
