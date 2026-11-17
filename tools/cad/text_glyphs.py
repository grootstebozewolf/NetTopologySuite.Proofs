#!/usr/bin/env python3
"""Text entity to glyph outlines, as CAD carrier records.

One text entity is one carrier row. A resolved text is a Compound with one
member per inked glyph. A glyph member is the ``truetype_e`` fixture shape:
a Compound of one Ring (chord skeleton, nonzero winding, source orientation)
and one Compound per contour. A contour member is a Chord for a line span
and a Bezier for a curve span: degree 2 from glyf, degree 3 from CFF.
Outline numbers stay in font units and source order. Nothing is flipped.

Placement, local to world, per glyph: the pen advance in font units, then
the text link (insert point, rotation, scale ``height / capHeight``), then
the entity links the caller already holds. Backward text reflects. Upside
down text reflects and adds a half turn. Both together are a half turn.

Alignment moves the anchor inside the pen link. Left is the pen origin.
Center and right are the centre and right edge of the ink, from exact
Bezier extents. Baseline is 0, top is the cap height, middle is half the
cap height, bottom is the hhea descent, and the DXF ``Middle`` alignment
is the middle of cap height and descent at the ink centre. ``aligned``
puts the ink between two baseline points: rotation and scale come from
those points, and the stated height and rotation are not used. ``fit``
keeps the height, so it is a similarity only when the ink already spans
the two points. These follow ezdxf's text2path, the DXF reference reader.

``TextRun`` is the format-neutral input. ``dxf_text_run`` reads an ezdxf
TEXT, which also serves DWG once a reference converter has produced the
DXF entity model. ``dgn_text_run`` takes the fields of a DGN type 17 text
element as a reference reader reports them, in master units and degrees.

Named declines: ID_NotSimilarityPlacement for a width factor other than 1
or a nonzero oblique angle; ID_DegenerateEntity for non-finite or
non-positive numbers and zero-area contours; ID_TextEntity for everything
this slice does not resolve (no font for the style, a stroke font, a
missing glyph, no cap height, an unknown alignment, a DGN justification
other than left baseline, a contour of fewer than three spans, text with
no ink).

Advance is hmtx only. Kerning and shaping are not applied. fontTools (MIT)
reads the outlines; its code is not ported.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

_EPS = 1e-9
_QUAD_KNOTS = [0, 0, 0, 1, 1, 1]
_CUBIC_KNOTS = [0, 0, 0, 0, 1, 1, 1, 1]
OUTLINE_SUFFIXES = (".ttf", ".otf", ".ttc")

Decline = tuple[str, str]
Point = tuple[float, float]
# ("L", p0, p1) | ("Q", p0, c, p1) | ("C", p0, c1, c2, p1)
Span = tuple


@dataclass(frozen=True)
class TextRun:
    """One line of text, left baseline at ``insert``. ``height`` is the cap height."""

    text: str
    font: Path
    height: float
    insert: tuple[float, float]
    rotation: float = 0.0
    width_factor: float = 1.0
    oblique: float = 0.0
    backward: bool = False
    upside_down: bool = False
    halign: str = "left"  # left | center | right
    valign: str = "baseline"  # baseline | bottom | middle | top | cap-descent-middle
    span_to: tuple[float, float] | None = None  # second baseline point
    span_mode: str | None = None  # aligned | fit


def _pt(point: Any) -> Point:
    return (float(point[0]), float(point[1]))


def _outline_pen(glyph_set: Any) -> Any:
    from fontTools.pens.basePen import BasePen

    class _SpanPen(BasePen):
        """Records spans per contour. Components are decomposed by BasePen."""

        def __init__(self) -> None:
            super().__init__(glyph_set)
            self.contours: list[list[Span]] = []
            self._start: Point | None = None

        def _line(self, end: Point) -> None:
            start = _pt(self._getCurrentPoint())
            if start != end:
                self.contours[-1].append(("L", start, end))

        def _moveTo(self, pt: Any) -> None:
            self.contours.append([])
            self._start = _pt(pt)

        def _lineTo(self, pt: Any) -> None:
            self._line(_pt(pt))

        def _qCurveToOne(self, pt1: Any, pt2: Any) -> None:
            start = _pt(self._getCurrentPoint())
            self.contours[-1].append(("Q", start, _pt(pt1), _pt(pt2)))

        def _curveToOne(self, pt1: Any, pt2: Any, pt3: Any) -> None:
            start = _pt(self._getCurrentPoint())
            self.contours[-1].append(("C", start, _pt(pt1), _pt(pt2), _pt(pt3)))

        def _closePath(self) -> None:
            if self._start is not None:
                self._line(self._start)

        def _endPath(self) -> None:
            # An outline contour is closed whether or not the source says so.
            self._closePath()

    return _SpanPen()


def glyph_contours(font: Any, glyph_name: str) -> list[list[Span]]:
    """Spans of one glyph in font units, contours and spans in source order."""
    glyph_set = font.getGlyphSet()
    pen = _outline_pen(glyph_set)
    glyph_set[glyph_name].draw(pen)
    return [contour for contour in pen.contours if contour]


def cap_height(font: Any) -> float | None:
    """OS/2 sCapHeight, else the top of H. None when the font states neither."""
    os2 = font["OS/2"] if "OS/2" in font else None
    stated = getattr(os2, "sCapHeight", 0) if os2 is not None else 0
    if stated and stated > 0:
        return float(stated)
    name = (font.getBestCmap() or {}).get(ord("H"))
    if name is None:
        return None
    tops = [point[1] for contour in glyph_contours(font, name) for span in contour for point in span[1:]]
    if not tops or max(tops) <= 0:
        return None
    return float(max(tops))


def _axis_extent(values: list[float]) -> tuple[float, float]:
    """Exact range of one coordinate of a Bezier span, from its control values."""
    low, high = min(values[0], values[-1]), max(values[0], values[-1])
    roots: list[float] = []
    if len(values) == 3:
        a, b, c = values
        if a - 2 * b + c != 0:
            roots.append((a - b) / (a - 2 * b + c))
    elif len(values) == 4:
        a, b, c, d = values
        qa, qb, qc = -a + 3 * b - 3 * c + d, 2 * (a - 2 * b + c), b - a
        if qa == 0:
            if qb != 0:
                roots.append(-qc / qb)
        else:
            disc = qb * qb - 4 * qa * qc
            if disc >= 0:
                root = math.sqrt(disc)
                roots.extend(((-qb + root) / (2 * qa), (-qb - root) / (2 * qa)))
    for t in roots:
        if 0 < t < 1:
            work = list(values)
            while len(work) > 1:
                work = [(1 - t) * u + t * v for u, v in zip(work, work[1:])]
            low, high = min(low, work[0]), max(high, work[0])
    return low, high


def ink_extent(placed: list[tuple[float, list[list[Span]]]]) -> tuple[float, float]:
    """Left and right edge of the ink, in font units, pen advance included."""
    lows, highs = [], []
    for pen_x, contours in placed:
        for contour in contours:
            for span in contour:
                low, high = _axis_extent([point[0] for point in span[1:]])
                lows.append(pen_x + low)
                highs.append(pen_x + high)
    return min(lows), max(highs)


def _anchor(run: TextRun, font: Any, cap: float, ink: tuple[float, float]) -> tuple[float, float] | Decline:
    """The font-unit point that lands on the insert point."""
    if run.span_mode is not None:
        return (ink[0], 0.0)
    xs = {"left": 0.0, "center": (ink[0] + ink[1]) / 2, "right": ink[1]}
    descent = float(font["hhea"].descent)
    ys = {
        "baseline": 0.0,
        "top": cap,
        "middle": cap / 2,
        "bottom": descent,
        "cap-descent-middle": (cap + descent) / 2,
    }
    if run.halign not in xs or run.valign not in ys:
        return ("ID_TextEntity", f"unknown text alignment {run.halign} {run.valign}")
    return (xs[run.halign], ys[run.valign])


def _span_placement(run: TextRun, cap: float, ink: tuple[float, float]) -> tuple[float, float] | Decline:
    """Rotation and scale for ``aligned`` and ``fit``, or the stated ones."""
    scale = run.height / cap
    if run.span_mode is None:
        return (run.rotation, scale)
    if run.span_mode not in ("aligned", "fit") or run.span_to is None:
        return ("ID_TextEntity", f"unknown text alignment {run.span_mode}")
    dx, dy = run.span_to[0] - run.insert[0], run.span_to[1] - run.insert[1]
    length = math.hypot(dx, dy)
    if not math.isfinite(length) or length <= _EPS or ink[1] - ink[0] <= _EPS:
        return ("ID_DegenerateEntity", "aligned text has no length")
    rotation = math.degrees(math.atan2(dy, dx))
    stretch = length / (ink[1] - ink[0])
    if run.span_mode == "aligned":
        return (rotation, stretch)
    if not math.isclose(stretch, scale, rel_tol=1e-9, abs_tol=_EPS):
        return ("ID_NotSimilarityPlacement", "fit text stretches the width only")
    return (rotation, scale)


def _entity(
    kind: str,
    params: dict[str, Any],
    links: list[dict[str, Any]],
    ctx: dict[str, Any],
) -> dict[str, Any]:
    sign = 1
    for link in links:
        if link["reflect"]:
            sign = -sign
    return {
        "record": "entity",
        "kind": kind,
        "placement": {"links": links, "s": sign},
        "params": params,
        "units": ctx["units"],
        "tolerance": ctx["tolerance"],
        "dimension": ctx["dimension"],
        "provenance": ctx["provenance"],
    }


def _span_entity(span: Span, links: list[dict[str, Any]], ctx: dict[str, Any]) -> dict[str, Any]:
    points = [[x, y] for x, y in span[1:]]
    if span[0] == "L":
        return _entity("Chord", {"start": points[0], "end": points[1]}, links, ctx)
    degree = 2 if span[0] == "Q" else 3
    return _entity(
        "Bezier",
        {
            "degree": degree,
            "controlPoints": points,
            "weights": [1] * (degree + 1),
            "knots": list(_QUAD_KNOTS if degree == 2 else _CUBIC_KNOTS),
        },
        links,
        ctx,
    )


def _glyph_member(
    contours: list[list[Span]],
    links: list[dict[str, Any]],
    ctx: dict[str, Any],
) -> dict[str, Any] | Decline:
    skeleton = []
    orientation = []
    for contour in contours:
        if len(contour) < 3:
            return ("ID_TextEntity", "glyph contour of fewer than three spans")
        area = 0.0
        chords = []
        for span in contour:
            (x1, y1), (x2, y2) = span[1], span[-1]
            area += x1 * y2 - x2 * y1
            chords.append({"kind": "Chord", "start": [x1, y1], "end": [x2, y2], "bulge": 0})
        if abs(area) <= _EPS:
            return ("ID_DegenerateEntity", "glyph contour of zero area")
        orientation.append("ccw" if area > 0 else "cw")
        skeleton.append(chords)
    ring = _entity(
        "Ring",
        {"windingRule": "nonzero", "contours": skeleton, "orientation": orientation},
        links,
        ctx,
    )
    members = [ring]
    for contour in contours:
        spans = [_span_entity(span, links, ctx) for span in contour]
        members.append(_entity("Compound", {"members": spans}, links, ctx))
    return _entity("Compound", {"members": members}, links, ctx)


def _text_link(run: TextRun, rotation: float, scale: float) -> dict[str, Any]:
    if run.upside_down:
        rotation += 180.0
    return {
        "translate": [float(run.insert[0]), float(run.insert[1])],
        "rotate": rotation,
        "scale": scale,
        "reflect": run.backward != run.upside_down,
    }


def run_record(
    run: TextRun,
    *,
    links: list[dict[str, Any]],
    units: dict[str, Any],
    tolerance: dict[str, Any],
    dimension: dict[str, Any],
    provenance: dict[str, Any],
) -> dict[str, Any] | Decline:
    """One Compound carrier entity for the run, or a decline id and reason.

    ``links`` are the entity links outside the text (OCS, block inserts),
    local to world.
    """
    from fontTools.ttLib import TTFont

    numbers = (run.height, run.insert[0], run.insert[1], run.rotation, run.width_factor, run.oblique)
    if not all(math.isfinite(float(value)) for value in numbers) or run.height <= _EPS:
        return ("ID_DegenerateEntity", "text height, insert, or angle is not a positive finite number")
    if not math.isclose(run.width_factor, 1.0, rel_tol=1e-9, abs_tol=_EPS):
        return ("ID_NotSimilarityPlacement", "text width factor is not 1")
    if abs(run.oblique) > _EPS:
        return ("ID_NotSimilarityPlacement", "text oblique angle is not 0")
    font = TTFont(run.font, fontNumber=0, lazy=True)
    try:
        if "glyf" not in font and "CFF " not in font and "CFF2" not in font:
            return ("ID_TextEntity", "font has no glyf or CFF outlines")
        cap = cap_height(font)
        if cap is None:
            return ("ID_TextEntity", "font states no cap height")
        cmap = font.getBestCmap() or {}
        advances = font["hmtx"].metrics
        ctx = {"units": units, "tolerance": tolerance, "dimension": dimension, "provenance": provenance}
        placed: list[tuple[float, list[list[Span]]]] = []
        pen_x = 0.0
        for char in run.text:
            name = cmap.get(ord(char))
            if name is None:
                return ("ID_TextEntity", f"font has no glyph for U+{ord(char):04X}")
            contours = glyph_contours(font, name)
            if contours:
                placed.append((pen_x, contours))
            pen_x += float(advances[name][0])
        if not placed:
            return ("ID_TextEntity", "text has no inked glyph")
        ink = ink_extent(placed)
        anchor = _anchor(run, font, cap, ink)
        if len(anchor) == 2 and isinstance(anchor[0], str):
            return anchor
        turn = _span_placement(run, cap, ink)
        if isinstance(turn[0], str):
            return turn
        text_link = _text_link(run, turn[0], turn[1])
        members = []
        for pen_x, contours in placed:
            advance = {
                "translate": [pen_x - anchor[0], 0.0 - anchor[1]],
                "rotate": 0.0,
                "scale": 1.0,
                "reflect": False,
            }
            member = _glyph_member(contours, [advance, text_link] + links, ctx)
            if isinstance(member, tuple):
                return member
            members.append(member)
    finally:
        font.close()
    return _entity("Compound", {"members": members}, list(links), ctx)


def resolve_font(name: str, fonts: Mapping[str, Path | str]) -> Path | Decline:
    """Look a source font name up, by file name, ignoring case."""
    key = Path(name.replace("\\", "/")).name.casefold()
    if not key:
        return ("ID_TextEntity", "text style names no font")
    table = {str(k).casefold(): Path(v) for k, v in fonts.items()}
    path = table.get(key)
    if path is None:
        if not key.endswith(OUTLINE_SUFFIXES):
            return ("ID_TextEntity", f"{key} is not an outline font")
        return ("ID_TextEntity", f"no font file given for {key}")
    return path


# Groups 72 and 73. Aligned (3) and fit (5) span two points instead.
_DXF_HALIGN = {0: "left", 1: "center", 2: "right", 3: "left", 4: "center", 5: "left"}
_DXF_VALIGN = {0: "baseline", 1: "bottom", 2: "middle", 3: "top"}


def dxf_text_run(entity: Any, doc: Any, fonts: Mapping[str, Path | str]) -> TextRun | Decline:
    """A DXF TEXT (ezdxf entity) as a run. DWG shares this entity model."""
    dxf = entity.dxf
    halign = int(dxf.get("halign", 0))
    valign = int(dxf.get("valign", 0)) if halign <= 2 else 0
    if halign not in _DXF_HALIGN or valign not in _DXF_VALIGN:
        return ("ID_TextEntity", f"unknown text alignment {halign} {valign}")
    style = doc.styles.get(str(dxf.get("style", "Standard")))
    font = resolve_font(str(style.dxf.get("font", "")) if style is not None else "", fonts)
    if isinstance(font, tuple):
        return font
    flags = int(dxf.get("text_generation_flag", 0))
    insert = dxf.insert
    # Group 11 is the anchor for every alignment except left baseline.
    second = dxf.get("align_point", insert)
    span_mode = {3: "aligned", 5: "fit"}.get(halign)
    if span_mode is None and (halign, valign) != (0, 0):
        insert = second
    return TextRun(
        halign=_DXF_HALIGN[halign],
        valign="cap-descent-middle" if halign == 4 else _DXF_VALIGN[valign],
        span_to=(float(second[0]), float(second[1])) if span_mode else None,
        span_mode=span_mode,
        text=entity.plain_text(),
        font=font,
        height=float(dxf.get("height", 0.0)),
        insert=(float(insert[0]), float(insert[1])),
        rotation=float(dxf.get("rotation", 0.0)),
        width_factor=float(dxf.get("width", 1.0)),
        oblique=float(dxf.get("oblique", 0.0)),
        backward=bool(flags & 2),
        upside_down=bool(flags & 4),
    )


def dgn_text_run(element: Mapping[str, Any], fonts: Mapping[Any, Path | str]) -> TextRun | Decline:
    """A DGN type 17 text element as a run.

    ``element`` holds ``text``, ``origin`` (left baseline, master units),
    ``rotation`` (degrees CCW), ``height`` and ``width`` (character size in
    master units), and ``font`` (the DGN font number). ``fonts`` maps a
    font number to an outline font file. Unequal height and width is not a
    similarity.
    """
    if int(element.get("type", 17)) != 17:
        return ("ID_TextEntity", "not a DGN type 17 text element")
    if int(element.get("justification", 0)) != 0 and element.get("justification") != "left-baseline":
        return ("ID_TextEntity", "text alignment is not left baseline")
    number = element.get("font")
    path = fonts.get(number, fonts.get(str(number)))
    if path is None:
        return ("ID_TextEntity", f"no font file given for DGN font {number}")
    height = float(element["height"])
    width = float(element.get("width", height))
    origin = element["origin"]
    return TextRun(
        text=str(element["text"]),
        font=Path(path),
        height=height,
        insert=(float(origin[0]), float(origin[1])),
        rotation=float(element.get("rotation", 0.0)),
        width_factor=width / height if math.isfinite(height) and height > _EPS else 1.0,
    )
