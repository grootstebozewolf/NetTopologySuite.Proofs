"""Locked TrueType lowercase e: fontTools spans versus FreeType."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

import freetype
from fontTools.ttLib import TTFont
from jsonschema import Draft202012Validator

import dxf_extract
from fixtures.gen_truetype_e import JSON_PATH, TTF_PATH, glyph_spans, render

TTF_SHA256 = "4a700442e3ad99aa44455ac927ab1f8fab8c8d791a273a44d0779a447c5e046c"
JSON_SHA256 = "48bf0d46c34bb513e4cea44c136c32d361c2495dd1bd500e22f8a97cceb4b9d9"

SCHEMA = json.loads(dxf_extract.SCHEMA_PATH.read_text(encoding="utf-8"))
VALIDATOR = Draft202012Validator(SCHEMA)
_LOAD = freetype.FT_LOAD_NO_SCALE | freetype.FT_LOAD_NO_HINTING | freetype.FT_LOAD_NO_BITMAP


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
    assert outer_member["kind"] == "Compound"
    assert hole_member["kind"] == "Compound"

    expanded = glyph_spans()
    reference = _freetype_spans(TTF_PATH)
    assert reference == expanded
    assert len(reference) == 2

    font = TTFont(TTF_PATH)
    glyf = font["glyf"]["e"]
    coords, _ends, _flags = glyf.getCoordinates(font["glyf"])
    stored = {(int(x), int(y)) for x, y in coords}

    for contour, spans, chords in zip(
        (outer_member, hole_member),
        reference,
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
    implied = [span[2] for span in reference[0] + reference[1] if span[2] not in stored]
    assert implied
    assert _shoelace(reference[0]) > 0
    assert _shoelace(reference[1]) < 0
