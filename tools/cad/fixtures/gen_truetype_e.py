"""Locked TrueType lowercase e: two contours, implied on-curve midpoints.

fontTools reads the glyf points. Consecutive off-curve points expand to an
on-curve midpoint, and each quadratic span is one single-span unit-weight
MkNurbs (schema kind Bezier). The ring winding rule is nonzero. FreeType's
decomposed outline is the reference for those spans.

The outer contour is clockwise and the hole is counterclockwise, in y-up
font units, so the counter is empty under the nonzero rule.
"""

from __future__ import annotations

import io
import json
from pathlib import Path

from fontTools.fontBuilder import FontBuilder
from fontTools.pens.ttGlyphPen import TTGlyphPen

HERE = Path(__file__).resolve().parent
TTF_PATH = HERE / "truetype_e.ttf"
JSON_PATH = HERE / "truetype_e.json"

# 2000-01-01 as a TrueType seconds-since-1904 timestamp. Fixed so two saves match.
_TT_STAMP = 3029529600
_KNOTS = [0, 0, 0, 1, 1, 1]
_WEIGHTS = [1, 1, 1]

# (x, y, on_curve). Each contour is closed back to its first on-curve point.
# TrueType, y-up: the outer contour travels clockwise and the hole counterclockwise.
_OUTER = [
    (100, 700, False),
    (700, 700, False),
    (700, 200, True),
    (400, 80, False),
    (100, 80, False),
    (100, 200, True),
]
_HOLE = [
    (250, 250, False),
    (400, 250, False),
    (550, 300, True),
    (550, 450, False),
    (250, 450, False),
    (250, 300, True),
]


def _quads(start: tuple[int, int], points: list[tuple[int, int]]) -> list[tuple[tuple[int, int], tuple[int, int], tuple[int, int]]]:
    """Off-curve points, then the destination on-curve point. Start is the previous on-curve point."""
    spans = []
    current = start
    for index in range(len(points) - 1):
        control = points[index]
        nxt = points[index + 1]
        if index < len(points) - 2:
            end = ((control[0] + nxt[0]) // 2, (control[1] + nxt[1]) // 2)
        else:
            end = nxt
        spans.append((current, control, end))
        current = end
    return spans


def expand_contour(points: list[tuple[int, int, bool]]) -> list[tuple[tuple[int, int], tuple[int, int], tuple[int, int]]]:
    """Rotate so the contour ends on-curve, then expand implied midpoints."""
    ons = [on for _, _, on in points]
    if not any(ons):
        raise ValueError("contour has no on-curve point")
    rotate = ons.index(True) + 1
    rotated = points[rotate:] + points[:rotate]
    xy = [(x, y) for x, y, _ in rotated]
    on_flags = [on for _, _, on in rotated]
    spans: list[tuple[tuple[int, int], tuple[int, int], tuple[int, int]]] = []
    current = xy[-1]
    rest = list(zip(xy, on_flags))
    while rest:
        next_on = next(i for i, (_, on) in enumerate(rest) if on) + 1
        chunk = [pt for pt, _ in rest[:next_on]]
        if next_on == 1:
            raise ValueError("line span is not a quadratic")
        spans.extend(_quads(current, chunk))
        current = chunk[-1]
        rest = rest[next_on:]
    return spans


def glyph_spans() -> list[list[tuple[tuple[int, int], tuple[int, int], tuple[int, int]]]]:
    return [expand_contour(_OUTER), expand_contour(_HOLE)]


def _draw(pen: TTGlyphPen, points: list[tuple[int, int, bool]]) -> None:
    first = next(i for i, (_, _, on) in enumerate(points) if on)
    x, y, _ = points[first]
    pen.moveTo((x, y))
    # Walk from the point after the first on-curve, and close on that same point.
    ordered = points[first + 1 :] + points[: first + 1]
    chunk: list[tuple[int, int]] = []
    for x, y, on in ordered:
        chunk.append((x, y))
        if on:
            pen.qCurveTo(*chunk)
            chunk = []
    pen.endPath()


def build_glyph():
    pen = TTGlyphPen(None)
    _draw(pen, _OUTER)
    _draw(pen, _HOLE)
    return pen.glyph()


def ttf_bytes() -> bytes:
    glyph = build_glyph()
    empty = TTGlyphPen(None).glyph()
    fb = FontBuilder(1000, isTTF=True)
    fb.updateHead(created=_TT_STAMP, modified=_TT_STAMP)
    fb.setupGlyphOrder([".notdef", "e"])
    fb.setupCharacterMap({ord("e"): "e"})
    fb.setupGlyf({".notdef": empty, "e": glyph})
    # Left side bearing equals xMin, so FreeType's unscaled outline matches the stored points.
    fb.setupHorizontalMetrics({".notdef": (600, 0), "e": (800, 100)})
    fb.setupHorizontalHeader(ascent=900, descent=-100)
    fb.setupOS2()
    fb.setupPost()
    fb.setupNameTable(
        {
            "familyName": "CarrierE",
            "styleName": "Regular",
            "uniqueFontIdentifier": "CarrierE-Regular",
            "fullName": "CarrierE Regular",
            "psName": "CarrierE-Regular",
            "version": "Version 1.000",
        }
    )
    buf = io.BytesIO()
    fb.save(buf)
    return buf.getvalue()


def _entity(kind: str, params: dict) -> dict:
    return {
        "record": "entity",
        "kind": kind,
        "placement": {"links": [], "s": 1},
        "params": params,
        "units": {"linear": "fontUnit", "angle": "degree", "angdir": 0, "angbase": 0.0},
        "tolerance": {"kind": "sourceDefault"},
        "dimension": {"space": "2d"},
        "provenance": {
            "format": "TrueType",
            "version": "glyf",
            "handle": "e",
            "layer": "",
            "blockPath": [],
            "fileId": "truetype-e",
        },
    }


def _bezier(span: tuple[tuple[int, int], tuple[int, int], tuple[int, int]]) -> dict:
    return _entity(
        "Bezier",
        {
            "degree": 2,
            "controlPoints": [[x, y] for x, y in span],
            "weights": list(_WEIGHTS),
            "knots": list(_KNOTS),
        },
    )


def _ring(contours: list[list[tuple[tuple[int, int], tuple[int, int], tuple[int, int]]]]) -> dict:
    rings = []
    for spans in contours:
        segments = []
        for start, _control, end in spans:
            segments.append(
                {
                    "kind": "Chord",
                    "start": [start[0], start[1]],
                    "end": [end[0], end[1]],
                    "bulge": 0,
                }
            )
        rings.append(segments)
    return _entity("Ring", {"windingRule": "nonzero", "contours": rings})


def carrier_record() -> dict:
    contours = glyph_spans()
    return _entity(
        "Compound",
        {
            "members": [
                _ring(contours),
                _entity("Compound", {"members": [_bezier(span) for span in contours[0]]}),
                _entity("Compound", {"members": [_bezier(span) for span in contours[1]]}),
            ]
        },
    )


def json_bytes() -> bytes:
    return json.dumps(carrier_record(), allow_nan=False, indent=2) + "\n"


def render() -> tuple[bytes, bytes]:
    return ttf_bytes(), json_bytes()


def write() -> None:
    ttf, payload = render()
    TTF_PATH.write_bytes(ttf)
    JSON_PATH.write_text(payload, encoding="utf-8")


if __name__ == "__main__":
    write()
