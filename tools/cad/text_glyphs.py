#!/usr/bin/env python3
"""Text entity to glyph outlines, as CAD carrier records.

One text entity is one carrier row. A resolved text is a Compound with one
member per inked glyph. A glyph member is the ``truetype_e`` fixture shape:
a Compound of one Ring (chord skeleton, nonzero winding, source orientation)
and one Compound per contour. A contour member is a Chord for a line span
and a Bezier for a curve span: degree 2 from glyf, degree 3 from CFF.
Outline numbers stay in font units and source order. Nothing is flipped.
A contour that encloses no area (real fonts carry two-point leftovers)
fills nothing under the winding rule and is left out of the glyph.

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

``TextBlock`` is plain multiline text (DXF MTEXT without inline codes).
Baselines step down by ``5/3`` of the cap height times the line spacing
factor. The box runs from the cap top of the first line to the baseline
of the last, and each line is as wide as its advances. The attachment
point picks the box corner, edge, or centre that lands on the insert
point. A line wider than a stated column width would wrap, and declines.

``TextRun`` is the format-neutral input. ``dxf_text_run`` reads an ezdxf
TEXT, which also serves DWG once a reference converter has produced the
DXF entity model. ``dgn_text_run`` takes the fields of a DGN type 17 text
element as a reference reader reports them, in master units and degrees.

Named declines: ID_NotSimilarityPlacement for a width factor other than 1
or a nonzero oblique angle; ID_DegenerateEntity for non-finite or
non-positive numbers and a glyph whose contours all enclose no area; ID_TextEntity for everything
this slice does not resolve (no font for the style, a
missing glyph, no cap height, an unknown alignment, MTEXT inline codes,
columns, a wrapping line or top-to-bottom flow, a DGN justification
other than left baseline, a text with no ink).

A font file ending in ``.shx`` or ``.shp`` is a stroke font
(``stroke_glyphs``). Its glyph member is a Compound of open BulgePolyline
strokes, chords and true arcs, with no Ring. Its cap height and descent
are the font's ``above`` and ``below``, and a character advances by its
pen travel. Centre, right, aligned and fit need ink extents, which this
slice does not compute for strokes, so they decline; MTEXT attachment
uses advances and works.

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


@dataclass(frozen=True)
class TextBlock:
    """Plain lines under one font. ``insert`` is the attachment point."""

    lines: tuple[str, ...]
    font: Path
    height: float
    insert: tuple[float, float]
    rotation: float = 0.0
    halign: str = "left"  # left | center | right
    valign: str = "top"  # top | middle | bottom
    line_spacing: float = 1.0
    column_width: float = 0.0


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


def _anchor(run: TextRun, descent: float, cap: float, ink: tuple[float, float]) -> tuple[float, float] | Decline:
    """The font-unit point that lands on the insert point."""
    if run.span_mode is not None:
        return (ink[0], 0.0)
    xs = {"left": 0.0, "center": (ink[0] + ink[1]) / 2, "right": ink[1]}
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


def _on_curve(span: Span, t: float) -> Point:
    """De Casteljau on a span's control points."""
    work = list(span[1:])
    while len(work) > 1:
        work = [((1 - t) * a[0] + t * b[0], (1 - t) * a[1] + t * b[1]) for a, b in zip(work, work[1:])]
    return work[0]


def _glyph_member(
    contours: list[list[Span]],
    links: list[dict[str, Any]],
    ctx: dict[str, Any],
) -> dict[str, Any] | Decline:
    skeleton = []
    orientation = []
    kept: list[list[Span]] = []
    for contour in contours:
        # Span end points. A contour of one or two spans, or one whose end
        # points enclose no area, also gets on-curve points at t = 1/2, then
        # at quarters; those are exact in binary and lie on the source curve.
        chords: list[dict[str, Any]] = []
        area = 0.0
        for pieces in (1, 2, 4):
            points = [
                _on_curve(span, step / pieces) for span in contour for step in range(pieces)
            ]
            points = [p for p, q in zip(points, points[-1:] + points[:-1]) if p != q]
            area = sum(x1 * y2 - x2 * y1 for (x1, y1), (x2, y2) in zip(points, points[1:] + points[:1]))
            if len(points) >= 3 and abs(area) > _EPS:
                chords = [
                    {"kind": "Chord", "start": [x1, y1], "end": [x2, y2], "bulge": 0}
                    for (x1, y1), (x2, y2) in zip(points, points[1:] + points[:1])
                ]
                break
        if not chords:
            # Encloses nothing at every refinement, so it fills nothing: left out.
            continue
        kept.append(contour)
        orientation.append("ccw" if area > 0 else "cw")
        skeleton.append(chords)
    if not kept:
        return ("ID_DegenerateEntity", "glyph has no contour with area")
    ring = _entity(
        "Ring",
        {"windingRule": "nonzero", "contours": skeleton, "orientation": orientation},
        links,
        ctx,
    )
    members = [ring]
    for contour in kept:
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


class _OutlineFace:
    """A TrueType or CFF font. A glyph payload is its contours."""

    def __init__(self, path: Path) -> None:
        from fontTools.ttLib import TTFont

        self.font = TTFont(path, fontNumber=0, lazy=True)
        self.cap = cap_height(self.font)
        self.descent = float(self.font["hhea"].descent)
        self.cmap = self.font.getBestCmap() or {}
        self.advances = self.font["hmtx"].metrics

    def refusal(self) -> Decline | None:
        if "glyf" not in self.font and "CFF " not in self.font and "CFF2" not in self.font:
            return ("ID_TextEntity", "font has no glyf or CFF outlines")
        if self.cap is None:
            return ("ID_TextEntity", "font states no cap height")
        return None

    def line(self, text: str) -> tuple[list, float] | Decline:
        """Inked glyphs of one line with their pen positions, and the line advance."""
        placed: list[tuple[float, float, list[list[Span]]]] = []
        pen_x = 0.0
        for char in text:
            name = self.cmap.get(ord(char))
            if name is None:
                return ("ID_TextEntity", f"font has no glyph for U+{ord(char):04X}")
            contours = glyph_contours(self.font, name)
            if contours:
                placed.append((pen_x, 0.0, contours))
            pen_x += float(self.advances[name][0])
        return (placed, pen_x)

    def extent(self, placed: list) -> tuple[float, float] | Decline:
        return ink_extent([(x, contours) for x, _y, contours in placed])

    def member(self, payload: Any, links: list[dict[str, Any]], ctx: dict[str, Any]) -> dict[str, Any] | Decline:
        return _glyph_member(payload, links, ctx)

    def close(self) -> None:
        self.font.close()


class _StrokeFace:
    """An SHX or SHP stroke font. A glyph payload is its pen strokes."""

    def __init__(self, path: Path) -> None:
        import stroke_glyphs

        self.font = stroke_glyphs.StrokeFont(path)
        self.cap = self.font.cap
        self.descent = self.font.descent

    def refusal(self) -> Decline | None:
        if self.cap <= 0:
            return ("ID_TextEntity", "font states no cap height")
        return None

    def line(self, text: str) -> tuple[list, float] | Decline:
        return self.font.line(text)

    def extent(self, placed: list) -> tuple[float, float] | Decline:
        return ("ID_TextEntity", "ink alignment of a stroke font")

    def member(self, payload: Any, links: list[dict[str, Any]], ctx: dict[str, Any]) -> dict[str, Any] | Decline:
        strokes = [_entity("BulgePolyline", {"closed": False, "segments": stroke}, links, ctx) for stroke in payload]
        return _entity("Compound", {"members": strokes}, links, ctx)

    def close(self) -> None:
        pass


def _open_face(path: Path) -> Any:
    """The face for a font file, or a decline."""
    try:
        if str(path).lower().endswith((".shx", ".shp")):
            face: Any = _StrokeFace(path)
        else:
            face = _OutlineFace(path)
    except Exception as error:  # an unreadable font is a refusal, not a crash
        return ("ID_TextEntity", f"font file is not readable: {type(error).__name__}")
    refusal = face.refusal()
    if refusal is not None:
        face.close()
        return refusal
    return face


def _pen_link(x: float, y: float) -> dict[str, Any]:
    return {"translate": [x, y], "rotate": 0.0, "scale": 1.0, "reflect": False}


def block_record(
    block: TextBlock,
    *,
    links: list[dict[str, Any]],
    units: dict[str, Any],
    tolerance: dict[str, Any],
    dimension: dict[str, Any],
    provenance: dict[str, Any],
) -> dict[str, Any] | Decline:
    """One Compound carrier entity for the block, or a decline id and reason."""
    numbers = (block.height, block.insert[0], block.insert[1], block.rotation, block.line_spacing, block.column_width)
    if not all(math.isfinite(float(value)) for value in numbers) or block.height <= _EPS or block.line_spacing <= _EPS:
        return ("ID_DegenerateEntity", "text height, insert, angle, or spacing is not a positive finite number")
    shifts = {"left": 0.0, "center": 0.5, "right": 1.0}
    drops = {"top": 0.0, "middle": 0.5, "bottom": 1.0}
    if block.halign not in shifts or block.valign not in drops:
        return ("ID_TextEntity", f"unknown text alignment {block.halign} {block.valign}")
    face = _open_face(block.font)
    if isinstance(face, tuple):
        return face
    try:
        cap = face.cap
        ctx = {"units": units, "tolerance": tolerance, "dimension": dimension, "provenance": provenance}
        scale = block.height / cap
        pitch = cap * 5.0 / 3.0 * block.line_spacing
        depth = cap + pitch * (len(block.lines) - 1)
        text_link = {
            "translate": [float(block.insert[0]), float(block.insert[1])],
            "rotate": block.rotation,
            "scale": scale,
            "reflect": False,
        }
        members = []
        for index, text in enumerate(block.lines):
            line = face.line(text)
            if isinstance(line[0], str):
                return line
            placed, width = line
            if block.column_width > _EPS and width * scale > block.column_width * (1 + 1e-9):
                return ("ID_TextEntity", "a line is wider than the column and would wrap")
            dx = -shifts[block.halign] * width
            dy = drops[block.valign] * depth - cap - pitch * index
            for pen_x, pen_y, payload in placed:
                member = face.member(payload, [_pen_link(pen_x + dx, pen_y + dy), text_link] + links, ctx)
                if isinstance(member, tuple):
                    return member
                members.append(member)
    finally:
        face.close()
    if not members:
        return ("ID_TextEntity", "text has no inked glyph")
    return _entity("Compound", {"members": members}, list(links), ctx)


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
    numbers = (run.height, run.insert[0], run.insert[1], run.rotation, run.width_factor, run.oblique)
    if not all(math.isfinite(float(value)) for value in numbers) or run.height <= _EPS:
        return ("ID_DegenerateEntity", "text height, insert, or angle is not a positive finite number")
    if not math.isclose(run.width_factor, 1.0, rel_tol=1e-9, abs_tol=_EPS):
        return ("ID_NotSimilarityPlacement", "text width factor is not 1")
    if abs(run.oblique) > _EPS:
        return ("ID_NotSimilarityPlacement", "text oblique angle is not 0")
    face = _open_face(run.font)
    if isinstance(face, tuple):
        return face
    try:
        cap = face.cap
        ctx = {"units": units, "tolerance": tolerance, "dimension": dimension, "provenance": provenance}
        line = face.line(run.text)
        if isinstance(line[0], str):
            return line
        placed = line[0]
        if not placed:
            return ("ID_TextEntity", "text has no inked glyph")
        # Only centre, right, aligned and fit look at the ink.
        ink = (0.0, 0.0)
        if run.span_mode is not None or run.halign != "left":
            ink = face.extent(placed)
            if isinstance(ink[0], str):
                return ink
        anchor = _anchor(run, face.descent, cap, ink)
        if isinstance(anchor[0], str):
            return anchor
        turn = _span_placement(run, cap, ink)
        if isinstance(turn[0], str):
            return turn
        text_link = _text_link(run, turn[0], turn[1])
        members = []
        for pen_x, pen_y, payload in placed:
            member = face.member(payload, [_pen_link(pen_x - anchor[0], pen_y - anchor[1]), text_link] + links, ctx)
            if isinstance(member, tuple):
                return member
            members.append(member)
    finally:
        face.close()
    return _entity("Compound", {"members": members}, list(links), ctx)


def resolve_font(name: str, fonts: Mapping[str, Path | str]) -> Path | Decline:
    """Look a source font name up, by file name, ignoring case."""
    key = Path(name.replace("\\", "/")).name.casefold()
    if not key:
        return ("ID_TextEntity", "text style names no font")
    if "." not in key:
        # A style font without an extension is a compiled shape font.
        key += ".shx"
    table = {str(k).casefold(): Path(v) for k, v in fonts.items()}
    path = table.get(key)
    if path is None:
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


def dxf_mtext_block(entity: Any, doc: Any, fonts: Mapping[str, Path | str]) -> TextBlock | Decline:
    """A DXF MTEXT (ezdxf entity) as a plain block. DWG shares this entity model."""
    from ezdxf.tools.text import fast_plain_mtext, has_inline_formatting_codes

    dxf = entity.dxf
    content = str(entity.text)
    if has_inline_formatting_codes(content):
        return ("ID_TextEntity", "MTEXT inline formatting codes")
    if entity.has_columns:
        return ("ID_TextEntity", "MTEXT columns")
    if int(dxf.get("flow_direction", 1)) == 3:
        return ("ID_TextEntity", "MTEXT top-to-bottom flow")
    attachment = int(dxf.get("attachment_point", 1))
    if not 1 <= attachment <= 9:
        return ("ID_TextEntity", f"unknown text alignment {attachment}")
    style = doc.styles.get(str(dxf.get("style", "Standard")))
    font = resolve_font(str(style.dxf.get("font", "")) if style is not None else "", fonts)
    if isinstance(font, tuple):
        return font
    # MTEXT has no width factor or oblique of its own. The style's apply.
    if not math.isclose(float(style.dxf.get("width", 1.0)), 1.0, rel_tol=1e-9, abs_tol=_EPS):
        return ("ID_NotSimilarityPlacement", "text style width factor is not 1")
    if abs(float(style.dxf.get("oblique", 0.0))) > _EPS:
        return ("ID_NotSimilarityPlacement", "text style oblique angle is not 0")
    if dxf.hasattr("text_direction"):
        direction = dxf.text_direction
        if abs(float(direction[2])) > _EPS:
            return ("ID_TiltedPlacement", "MTEXT text direction leaves the plane")
        rotation = math.degrees(math.atan2(float(direction[1]), float(direction[0])))
    else:
        rotation = float(dxf.get("rotation", 0.0))
    insert = dxf.insert
    lines = fast_plain_mtext(content.replace("\\~", " "), split=True)
    return TextBlock(
        lines=tuple(lines),
        font=font,
        height=float(dxf.get("char_height", 0.0)),
        insert=(float(insert[0]), float(insert[1])),
        rotation=rotation,
        halign=("left", "center", "right")[(attachment - 1) % 3],
        valign=("top", "middle", "bottom")[(attachment - 1) // 3],
        line_spacing=float(dxf.get("line_spacing_factor", 1.0)),
        column_width=float(dxf.get("width", 0.0)),
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
    if element.get("justification", 0) not in (0, "left-baseline"):
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
