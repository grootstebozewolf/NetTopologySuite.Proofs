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
keeps the height and stretches the glyphs between the two points. These follow ezdxf's text2path, the DXF reference reader.

``TextBlock`` is multiline text (DXF MTEXT). A line is as tall as its
tallest word, and the next line starts ``5/3`` of that height times the
line spacing factor lower. The box runs from the cap top of the first
line to the baseline of the last. It is as wide as the column width, or
as the widest line when none is stated. With a column width, a line
breaks at the last space that still fits, and the spaces at the break
are dropped; a single word wider than the column overflows. A paragraph
is set left, centre or right in the box, by its own alignment or else by
the attachment point, which also picks the box point that lands on the
insert point.

MTEXT inline codes are read by ezdxf's parser. Colour is ignored: the
carrier has none. A height change scales the word inside its pen link. A
paragraph alignment of left, centre, right or justified is applied, with
the paragraph's first-line, left and right indents. Underline and
strike-through are drawn as described below. Every other code declines
by name: stacked text, overline, tracking, and distributed paragraphs
(ezdxf's own layout engine cannot do those either).

Paragraph layout follows ezdxf's engine (``ezdxf.tools.text_layout``),
read from its source: indents and tab stops are multiples of the cap
height; the first line starts at left + first-line indent; a justified
line spreads its spare width evenly over the spaces after its last tab
stop, except the paragraph's last line. A tab moves the next word to the
next stop beyond it: explicit stops first (``r`` and ``c`` mark right and
centre stops) that lie inside the column, then default left stops every
four cap heights after the last of them; with no stop left it is a
space. Tabs work on left and justified lines; on centred and right lines
a tab is a space. Words joined without a space, or by a non-breaking
space, never break apart: such a group overflows the column instead.
Two ezdxf details are matched on purpose: centred and right lines fit
strictly (``<``, where left lines use ``<=``), and a justified line never
stretches its first cell or the cell at its last tab stop.

One ezdxf behaviour is not matched. On a centred or right line, ezdxf
turns a tab that does not fit into a space that starts the next line
(sometimes leaving an empty line). Here a tab or space at a break
belongs to neither line. The differential test against ezdxf's engine
skips such cases by name.

Underline and strike-through are filled bars whose band comes from the
font: ``post.underlinePosition`` is the top of the underline and
``underlineThickness`` its height; ``OS/2.yStrikeoutPosition`` is the top
of the strike-through and ``yStrikeoutSize`` its height. A bar spans the
advances of the marked words and of the marked spaces between them, and
is not slanted by an oblique angle. It winds like the font's outer
contours, read from the largest contour of a plain letter (the spec
convention, clockwise for glyf and counter-clockwise for CFF, is only
the fallback), so where it crosses a descender the nonzero fill adds
rather than cancels. Overline
declines: no font table states where it goes. A stroke font states no
bands either, so a marked stroke-font word declines. TEXT carries the
same marks as the ``%%u`` and ``%%k`` toggles; ``%%o`` declines.

A font switch (``\f``) needs its own font file from the font map: a
regular face by family name, a bold or italic face as ``family|b1|i0``.
The word is scaled so its cap height matches, whatever the font's units.
Without that file the text declines; a bold face is never faked from the
regular one.

``TextRun`` is the format-neutral input. ``dxf_text_run`` reads an ezdxf
TEXT, which also serves DWG once a reference converter has produced the
DXF entity model. ``dgn_text_run`` takes the fields of a DGN type 17 text
element as a reference reader reports them, in master units and degrees.

A width factor ``w`` and an oblique angle are applied to the glyph
numbers, not to the placement: ``x`` becomes ``w * (x + y * tan(oblique))``
for control points, chord ends and pen positions. That is exact for
chords and Beziers, so the placement stays a similarity and the record
needs no new link kind. Fit alignment is the width factor that makes the
ink span its two points. A stroke glyph with an arc cannot be stretched
or slanted into another circular arc and declines.

Named declines: ID_NotSimilarityPlacement for an arc in a stretched or
slanted stroke font; ID_DegenerateEntity for non-finite or
non-positive numbers and a glyph whose contours all enclose no area; ID_TextEntity for everything
this slice does not resolve (no font for the style, a
missing glyph, no cap height, an unknown alignment, the MTEXT codes named
above, columns or top-to-bottom flow, a DGN justification
other than left baseline, a text with no ink).

A font file ending in ``.shx`` or ``.shp`` is a stroke font
(``stroke_glyphs``). Its glyph member is a Compound of open BulgePolyline
strokes, chords and true arcs, with no Ring. Its cap height and descent
are the font's ``above`` and ``below``, and a character advances by its
pen travel. Centre, right, aligned and fit use the exact reach of the
strokes, arcs included.

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
    # Per character of ``text``: the decorations on it, "u" underline, "s" strike-through.
    marks: tuple[str, ...] | None = None


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
    width_factor: float = 1.0
    oblique: float = 0.0
    # Optional rich form, used instead of ``lines``. A paragraph is
    # ``(align or None, items)`` and an item is ``(kind, text, rel)`` or
    # ``(kind, text, rel, font)``: kind is word, space (a break point) or
    # nbsp, ``rel`` is the item's cap height over ``height``, and ``font``
    # is a font file for that item when it is not the block's. A fifth
    # entry ``(width factor, oblique degrees)`` overrides the block's, and
    # a sixth holds its marks: "u" underline, "s" strike-through.
    paragraphs: tuple[tuple[str | None, tuple[tuple, ...]], ...] | None = None


def _plain_paragraphs(lines: tuple[str, ...]) -> tuple:
    """Each line is a paragraph; every space is a break point."""
    out = []
    for line in lines:
        items: list[tuple[str, str, float]] = []
        for index, word in enumerate(line.split(" ")):
            if index:
                items.append(("space", " ", 1.0))
            if word:
                items.append(("word", word, 1.0))
        out.append((None, tuple(items)))
    return tuple(out)


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
    return (rotation, stretch if run.span_mode == "aligned" else scale)


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
        # (bottom, top) of each decoration band, in font units, when the font states it.
        self.bands: dict[str, tuple[float, float]] = {}
        if "post" in self.font and self.font["post"].underlineThickness > 0:
            top = float(self.font["post"].underlinePosition)
            self.bands["u"] = (top - float(self.font["post"].underlineThickness), top)
        os2 = self.font["OS/2"] if "OS/2" in self.font else None
        if os2 is not None and getattr(os2, "yStrikeoutSize", 0) > 0:
            top = float(os2.yStrikeoutPosition)
            self.bands["s"] = (top - float(os2.yStrikeoutSize), top)
        self.outer_clockwise = self._outer_clockwise()

    def _outer_clockwise(self) -> bool:
        """How this font winds a filled outer contour, read from its own glyphs.

        The largest contour of a plain letter is an outer one. The spec
        convention (clockwise in glyf, counter-clockwise in CFF) is only
        the fallback, since fonts do not all follow it.
        """
        for char in "HIlLoOx":
            name = self.cmap.get(ord(char))
            if name is None:
                continue
            try:
                contours = glyph_contours(self.font, name)
            except Exception:
                continue
            areas = [
                sum(a[1][0] * b[1][1] - b[1][0] * a[1][1] for a, b in zip(contour, contour[1:] + contour[:1]))
                for contour in contours
            ]
            if areas and max(abs(area) for area in areas) > _EPS:
                return max(areas, key=abs) < 0
        return "glyf" in self.font

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

    def sheared(self, payload: Any, width: float, lean: float) -> Any:
        # An affine image of a Bezier is the Bezier of the mapped control points.
        return [
            [(span[0],) + tuple((width * (x + y * lean), y) for x, y in span[1:]) for span in contour]
            for contour in payload
        ]

    def member(self, payload: Any, links: list[dict[str, Any]], ctx: dict[str, Any]) -> dict[str, Any] | Decline:
        return _glyph_member(payload, links, ctx)

    def bar(self, mark: str, length: float) -> list[list[Span]] | Decline:
        """A decoration band as one glyph contour from x = 0 to ``length``."""
        if mark not in self.bands:
            name = {"u": "underline", "s": "strike-through"}[mark]
            return ("ID_TextEntity", f"font states no {name} position")
        low, high = self.bands[mark]
        corners = [(0.0, low), (0.0, high), (length, high), (length, low)]
        if not self.outer_clockwise:
            corners.reverse()
        return [[("L", a, b) for a, b in zip(corners, corners[1:] + corners[:1])]]

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
        import stroke_glyphs

        return stroke_glyphs.ink_x_extent(placed)

    def sheared(self, payload: Any, width: float, lean: float) -> Any:
        # A stretched or slanted circular arc is not a circular arc.
        if any(segment["kind"] == "Arc" for stroke in payload for segment in stroke):
            return ("ID_NotSimilarityPlacement", "arc in a stretched or slanted stroke font")

        def move(point: list[float]) -> list[float]:
            return [width * (point[0] + point[1] * lean), point[1]]

        return [
            [{**segment, "start": move(segment["start"]), "end": move(segment["end"])} for segment in stroke]
            for stroke in payload
        ]

    def member(self, payload: Any, links: list[dict[str, Any]], ctx: dict[str, Any]) -> dict[str, Any] | Decline:
        strokes = [_entity("BulgePolyline", {"closed": False, "segments": stroke}, links, ctx) for stroke in payload]
        return _entity("Compound", {"members": strokes}, links, ctx)

    def bar(self, mark: str, length: float) -> list[list[Span]] | Decline:
        name = {"u": "underline", "s": "strike-through"}[mark]
        return ("ID_TextEntity", f"a stroke font states no {name} position")

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


def _shape_numbers(width: float, oblique: float) -> tuple[float, float] | Decline:
    """Width factor and the tangent of the oblique angle, or a decline."""
    if not (math.isfinite(width) and math.isfinite(oblique)) or width <= _EPS or abs(oblique) >= 85.0:
        return ("ID_DegenerateEntity", "text width factor or oblique angle is out of range")
    return (width, math.tan(math.radians(oblique)))


def _shaped_line(face: Any, text: str, width: float, lean: float) -> tuple[list, float] | Decline:
    """A line with the width factor and oblique lean applied to its geometry.

    ``x`` becomes ``width * (x + y * lean)`` and ``y`` stays, for the pen
    positions and for every glyph number. The placement stays a similarity.
    """
    line = face.line(text)
    if isinstance(line[0], str) or (width == 1.0 and lean == 0.0):
        return line
    placed = []
    for pen_x, pen_y, payload in line[0]:
        shaped = face.sheared(payload, width, lean)
        if isinstance(shaped, tuple):
            return shaped
        placed.append((width * (pen_x + pen_y * lean), pen_y, shaped))
    return (placed, line[1] * width)


def _tab_stops(stops: tuple, cap: float) -> list[tuple[float, str]] | Decline:
    """Explicit tab stops in layout units, as ``(position, kind)``; kind is left, right or center.

    MTEXT writes a stop as a number (left), or ``r`` or ``c`` then a number,
    in multiples of the cap height.
    """
    out: list[tuple[float, str]] = []
    for stop in stops:
        kind = "left"
        if isinstance(stop, str):
            kind = {"r": "right", "c": "center"}.get(stop[:1], "")
            try:
                value = float(stop[1:])
            except ValueError:
                kind = ""
            if not kind:
                return ("ID_TextEntity", f"unknown MTEXT tab stop {stop}")
        else:
            value = float(stop)
        if not math.isfinite(value):
            return ("ID_DegenerateEntity", "MTEXT tab stop is not finite")
        out.append((value * cap, kind))
    return out


def _next_stop(
    stops: list[tuple[float, str]], indent: float, start: float, advance: float, avail: float | None
) -> float | None:
    """Where a group after a tab starts, or None when no stop applies.

    Stops are measured from the paragraph's left edge, so a line indented by
    ``indent`` sees them ``indent`` earlier, and only stops inside the line
    count. The first stop in list order that the group can reach is taken.
    With a column, ``stops`` already holds the default stops; without one,
    default left stops every four cap heights follow the last explicit stop.
    """
    candidates = [(pos - indent, kind) for pos, kind in stops]
    if avail is None:
        step = _DEFAULT_TAB[0]
        last = stops[-1][0] if stops else 0.0
        n = math.floor(last / step) + 1
        while n * step - indent <= start + advance + step:
            candidates.append((n * step - indent, "left"))
            n += 1
    for pos, kind in candidates:
        if pos <= 0 or (avail is not None and pos > avail + _EPS):
            continue
        if kind == "left" and pos > start:
            return pos
        if kind == "center" and pos > start + advance / 2:
            return pos - advance / 2
        if kind == "right" and pos > start + advance:
            return pos - advance
    return None


# The default tab step in layout units, set per block (four cap heights).
_DEFAULT_TAB = [0.0]


def _mark_runs(cells: list[tuple[float, float, str, Any, float]]) -> list[tuple[str, float, float, Any, float]]:
    """Merge touching marked cells into bars.

    A cell is ``(x, advance, marks, face, fit)`` in one line's coordinates;
    a bar is ``(mark, x, length, face, fit)`` and needs one face and fit.
    """
    bars: list[tuple[str, float, float, Any, float]] = []
    for mark in ("u", "s"):
        run: list[Any] | None = None
        for x, advance, marks, face, fit in cells:
            if mark not in marks:
                run = None
                continue
            if run is not None and run[3] is face and run[4] == fit and abs(run[1] + run[2] - x) <= _EPS:
                run[2] += advance
                continue
            run = [mark, x, advance, face, fit]
            bars.append(run)  # type: ignore[arg-type]
    return [tuple(bar) for bar in bars if bar[2] > _EPS]  # type: ignore[misc]


def _bar_members(
    bars: list[tuple[str, float, float, Any, float]],
    x0: float,
    y0: float,
    outer: list[dict[str, Any]],
    ctx: dict[str, Any],
) -> list[dict[str, Any]] | Decline:
    """Glyph-shaped members for the bars of one line. ``outer`` is the text link and what follows it."""
    members = []
    for mark, x, length, face, fit in bars:
        contour = face.bar(mark, length / fit)
        if isinstance(contour, tuple):
            return contour
        pen = _pen_link(x0 + x, y0)
        pen["scale"] = fit
        member = _glyph_member(contour, [pen] + outer, ctx)
        if isinstance(member, tuple):
            return member
        members.append(member)
    return members


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
    faces: dict[Path, Any] = {Path(block.font): face}
    try:
        cap = face.cap
        ctx = {"units": units, "tolerance": tolerance, "dimension": dimension, "provenance": provenance}
        scale = block.height / cap
        column = block.column_width / scale if block.column_width > _EPS else 0.0
        text_link = {
            "translate": [float(block.insert[0]), float(block.insert[1])],
            "rotate": block.rotation,
            "scale": scale,
            "reflect": False,
        }
        _DEFAULT_TAB[0] = 4.0 * cap
        paragraphs = block.paragraphs if block.paragraphs is not None else _plain_paragraphs(block.lines)
        # A laid-out line. Cell and mark x values are relative to the line start.
        laid: list[dict[str, Any]] = []
        for paragraph in paragraphs:
            align, items = paragraph[0], paragraph[1]
            props = paragraph[2] if len(paragraph) > 2 else (0.0, 0.0, 0.0, ())
            justify = align == "justified"
            if align is not None and align not in shifts and not justify:
                return ("ID_TextEntity", f"unknown text alignment {align}")
            share = 0.0 if justify else shifts[align if align is not None else block.halign]
            # Indents and tab stops are multiples of the block's cap height.
            indent_first, indent_left, indent_right = (cap * value for value in props[:3])
            stops = _tab_stops(props[3], cap)
            if isinstance(stops, tuple):
                return stops
            if column:
                # As ezdxf: explicit stops inside the column, then default left stops every
                # four cap heights after the last of them, all inside the column.
                stops = [stop for stop in stops if stop[0] < column]
                after = stops[-1][0] if stops else 0.0
                step = 4.0 * cap
                stops += [(k * step, "left") for k in range(1, int(column // step) + 2) if after < k * step < column]
            # Tabs are honoured on left and justified lines; elsewhere a tab is a space.
            tabbing = share == 0.0
            first = True

            def open_line() -> dict[str, Any]:
                indent = indent_left + (indent_first if first else 0.0)
                avail = column - indent - indent_right if column else None
                if avail is not None and avail <= _EPS:
                    avail = _EPS
                return {
                    "share": share, "indent": indent, "right": indent_right, "avail": avail,
                    "width": 0.0, "tallest": 0.0, "cells": [], "marked": [], "glue": [],
                    "anchor": None, "justify": justify, "last": False,
                }

            line = open_line()
            waiting: list[tuple[float, float, str, Any, float]] = []  # spaces not yet committed
            pending_tab: tuple[float, float, str, Any, float] | None = None

            def close_line() -> None:
                nonlocal line, first
                laid.append(line)
                first = False
                line = open_line()

            def commit_spaces() -> None:
                for space_advance, space_rel, space_marks, space_face, space_fit, *_tab in waiting:
                    if space_marks:
                        line["marked"].append((line["width"], space_advance, space_marks, space_face, space_fit))
                    line["glue"].append(line["width"])
                    line["width"] += space_advance
                    line["tallest"] = max(line["tallest"], space_rel)
                    if line["anchor"] is None:
                        # ezdxf never stretches a line's first cell.
                        line["anchor"] = line["width"]
                waiting.clear()

            # Measure every item, then cut the paragraph into separators and rigid groups:
            # words joined without a space or by a non-breaking space never break apart.
            sequence: list[Any] = []
            group: list[dict[str, Any]] = []
            for item in items:
                kind, text, rel = item[0], item[1], item[2]
                if not (math.isfinite(rel) and rel > _EPS):
                    return ("ID_DegenerateEntity", "text height is not a positive finite number")
                # A word in another font is scaled so its cap height matches.
                own = Path(item[3]) if len(item) > 3 and item[3] is not None else Path(block.font)
                if own not in faces:
                    opened = _open_face(own)
                    if isinstance(opened, tuple):
                        return opened
                    faces[own] = opened
                item_face = faces[own]
                fit = rel * cap / item_face.cap
                shape = _shape_numbers(*(item[4] if len(item) > 4 else (block.width_factor, block.oblique)))
                if isinstance(shape[0], str):
                    return shape
                measured = _shaped_line(item_face, " " if kind != "word" else text, shape[0], shape[1])
                if isinstance(measured[0], str):
                    return measured
                entry = {
                    "kind": kind, "rel": rel, "face": item_face, "fit": fit,
                    "placed": measured[0], "advance": measured[1] * fit,
                    "marks": item[5] if len(item) > 5 else "",
                }
                if kind in ("word", "nbsp"):
                    group.append(entry)
                    continue
                if group:
                    sequence.append(group)
                    group = []
                # On centred and right lines a tab is a space.
                sequence.append(("tab" if kind == "tab" and tabbing else "space", entry))
            if group:
                sequence.append(group)

            for part in sequence:
                if isinstance(part, tuple):
                    sep, entry = part
                    if sep == "space":
                        is_tab = entry["kind"] == "tab"
                        waiting.append((entry["advance"], entry["rel"], entry["marks"], entry["face"], entry["fit"], is_tab))
                    else:
                        # The tab's own width is a space's, used when no stop is left.
                        pending_tab = (entry["advance"], entry["rel"], entry["marks"], entry["face"], entry["fit"])
                    continue
                advance = sum(entry["advance"] for entry in part)
                while True:
                    start = line["width"] + sum(w[0] for w in waiting)
                    locked = False
                    if pending_tab is not None:
                        stop = _next_stop(stops, line["indent"], start, advance, line["avail"])
                        if stop is None:
                            start += pending_tab[0]
                        else:
                            start, locked = stop, True
                    if line["avail"] is None:
                        break
                    if tabbing and start + advance <= line["avail"] * (1 + 1e-9):
                        break
                    # ezdxf tests centred and right lines strictly.
                    if not tabbing and start + advance < line["avail"] * (1 - 1e-12):
                        break
                    if line["cells"] and (waiting or pending_tab is not None):
                        # Break at the space or tab before this group. Spaces at the break belong
                        # to neither line; a tab carries over and is tried again on the new line.
                        waiting.clear()
                        close_line()
                        continue
                    if pending_tab is not None:
                        # A tab and group that do not fit an empty line: ezdxf drops the tab.
                        pending_tab = None
                        continue
                    # Alone on its line: it overflows.
                    break
                commit_spaces()
                if pending_tab is not None:
                    gap = start - line["width"]
                    if pending_tab[2] and gap > _EPS:
                        line["marked"].append((line["width"], gap, pending_tab[2], pending_tab[3], pending_tab[4]))
                    if not locked:
                        line["glue"].append(line["width"])
                    line["tallest"] = max(line["tallest"], pending_tab[1])
                    pending_tab = None
                x = start
                for entry in part:
                    if entry["kind"] == "nbsp":
                        # A non-breaking space does not break, but it does stretch in a justified line.
                        line["glue"].append(x)
                    else:
                        line["cells"].append((x, entry["fit"], entry["placed"], entry["face"]))
                    if entry["marks"]:
                        line["marked"].append((x, entry["advance"], entry["marks"], entry["face"], entry["fit"]))
                    line["tallest"] = max(line["tallest"], entry["rel"])
                    x += entry["advance"]
                line["width"] = x
                if locked or line["anchor"] is None:
                    # Stretching starts after the last tab-stop cell, or else after the first cell.
                    line["anchor"] = x
            # A paragraph's last space is dropped like a line-breaking one, as ezdxf does;
            # any spaces before it stay in its width.
            if waiting:
                waiting.pop()
            commit_spaces()
            if not line["tallest"]:
                line["tallest"] = items[-1][2] if items else 1.0
            line["last"] = True
            laid.append(line)

        box = column if column else max(line["indent"] + line["width"] + line["right"] for line in laid)
        left = -shifts[block.halign] * box
        baselines = []
        top = 0.0
        for line in laid:
            baselines.append(top - cap * line["tallest"])
            top -= cap * line["tallest"] * 5.0 / 3.0 * block.line_spacing
        depth = -baselines[-1]
        members = []
        for line, baseline in zip(laid, baselines):
            avail = line["avail"] if line["avail"] is not None else box - line["indent"] - line["right"]
            cells, marked = line["cells"], line["marked"]
            if line["justify"] and not line["last"]:
                # Spread the spare width over the glue after the last tab stop, as ezdxf does.
                anchor = line["anchor"] if line["anchor"] is not None else 0.0
                glue = [x for x in line["glue"] if x >= anchor - _EPS]
                spare = avail - line["width"]
                if glue and spare > _EPS:
                    step = spare / len(glue)
                    moved = lambda x: x + step * sum(1 for g in glue if g < x - _EPS)
                    cells = [(moved(x), fit, placed, face) for x, fit, placed, face in cells]
                    marked = [
                        (moved(x), advance + (step if any(abs(g - x) <= _EPS for g in glue) else 0.0), marks, face, fit)
                        for x, advance, marks, face, fit in marked
                    ]
            x0 = left + line["indent"] + (avail - line["width"]) * line["share"]
            y0 = baseline + drops[block.valign] * depth
            bars = _bar_members(_mark_runs(marked), x0, y0, [text_link] + links, ctx)
            if isinstance(bars, tuple):
                return bars
            members.extend(bars)
            for cell_x, fit, placed, item_face in cells:
                for pen_x, pen_y, payload in placed:
                    pen = _pen_link(x0 + cell_x + fit * pen_x, y0 + fit * pen_y)
                    pen["scale"] = fit
                    member = item_face.member(payload, [pen, text_link] + links, ctx)
                    if isinstance(member, tuple):
                        return member
                    members.append(member)
    finally:
        for opened in faces.values():
            opened.close()
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
    shape = _shape_numbers(run.width_factor, run.oblique)
    if isinstance(shape[0], str):
        return shape
    width_factor, lean = shape
    face = _open_face(run.font)
    if isinstance(face, tuple):
        return face
    try:
        cap = face.cap
        ctx = {"units": units, "tolerance": tolerance, "dimension": dimension, "provenance": provenance}
        if run.span_mode == "fit":
            # Fit keeps the height and takes the width factor that makes the ink span the two points.
            natural = _shaped_line(face, run.text, 1.0, lean)
            if isinstance(natural[0], str):
                return natural
            if not natural[0]:
                return ("ID_TextEntity", "text has no inked glyph")
            reach = face.extent(natural[0])
            span = math.dist(run.insert, run.span_to) if run.span_to is not None else 0.0
            if not math.isfinite(span) or span <= _EPS or reach[1] - reach[0] <= _EPS:
                return ("ID_DegenerateEntity", "aligned text has no length")
            width_factor = span / ((reach[1] - reach[0]) * run.height / cap)
        line = _shaped_line(face, run.text, width_factor, lean)
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
        if run.marks and any(run.marks):
            marked = []
            pen = 0.0
            for char, marks in zip(run.text, run.marks):
                single = _shaped_line(face, char, width_factor, lean)
                if isinstance(single[0], str):
                    return single
                if marks:
                    marked.append((pen, single[1], marks, face, 1.0))
                pen += single[1]
            bars = _bar_members(_mark_runs(marked), -anchor[0], -anchor[1], [text_link] + links, ctx)
            if isinstance(bars, tuple):
                return bars
            members.extend(bars)
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


def text_marks(raw: str) -> tuple[str, tuple[str, ...]] | Decline:
    """TEXT content as plain text and per-character marks from the %%u and %%k toggles."""
    import re

    from ezdxf.tools.text import plain_text

    text = ""
    marks: list[str] = []
    state = ""
    at = 0
    def plain(piece: str) -> str:
        # %%% is a literal percent sign.
        return "%".join(plain_text(part) for part in piece.split("%%%"))

    for match in re.finditer(r"%%%|%%[uUkKoO]", raw):
        if match.group() == "%%%":
            continue
        chunk = plain(raw[at : match.start()])
        text += chunk
        marks.extend([state] * len(chunk))
        code = match.group()[2].lower()
        if code == "o":
            return ("ID_TextEntity", "TEXT overline: no font table states where it goes")
        flag = "u" if code == "u" else "s"
        state = state.replace(flag, "") if flag in state else "".join(sorted(state + flag))
        at = match.end()
    chunk = plain(raw[at:])
    text += chunk
    marks.extend([state] * len(chunk))
    return (text, tuple(marks))


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
    content = text_marks(str(dxf.get("text", "")))
    if isinstance(content[0], str) and len(content) == 2 and isinstance(content[1], str):
        return content
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
        text=content[0],
        marks=content[1] if any(content[1]) else None,
        font=font,
        height=float(dxf.get("height", 0.0)),
        insert=(float(insert[0]), float(insert[1])),
        rotation=float(dxf.get("rotation", 0.0)),
        width_factor=float(dxf.get("width", 1.0)),
        oblique=float(dxf.get("oblique", 0.0)),
        backward=bool(flags & 2),
        upside_down=bool(flags & 4),
    )


def resolve_face(face: Any, fonts: Mapping[str, Path | str]) -> Path | Decline:
    """An MTEXT ``\\f`` font face as a font file.

    A regular face is looked up by family name, then by family plus
    ``.ttf``. A bold or italic face is a different file and is looked up
    only as ``family|b1|i0`` (the flags as written in the code).
    """
    family = str(face.family).casefold()
    table = {str(k).casefold(): Path(v) for k, v in fonts.items()}
    if face.is_bold or face.is_italic:
        keys = [f"{family}|b{int(face.is_bold)}|i{int(face.is_italic)}"]
    else:
        keys = [family, family + ".ttf"]
    for key in keys:
        if key in table:
            return table[key]
    return ("ID_TextEntity", f"no font file given for {keys[0]}")


def _mtext_paragraphs(
    content: str,
    char_height: float,
    fonts: Mapping[str, Path | str] | None = None,
    width_factor: float = 1.0,
    oblique: float = 0.0,
) -> tuple | Decline:
    """MTEXT content as paragraphs of sized words, or the first code this slice refuses."""
    import re

    from ezdxf.enums import MTextLineAlignment, MTextParagraphAlignment
    from ezdxf.tools.text import MTextContext, MTextParser, TokenType

    start = MTextContext()
    start.cap_height = char_height
    start.width_factor = width_factor
    start.oblique = oblique
    aligns = {
        MTextParagraphAlignment.DEFAULT: None,
        MTextParagraphAlignment.LEFT: "left",
        MTextParagraphAlignment.CENTER: "center",
        MTextParagraphAlignment.RIGHT: "right",
        MTextParagraphAlignment.JUSTIFIED: "justified",
    }
    refused = {
        TokenType.STACK: "MTEXT stacked text",
        TokenType.NEW_COLUMN: "MTEXT columns",
        TokenType.WRAP_AT_DIMLINE: "MTEXT dimension line wrap",
    }
    paragraphs: list[tuple[str | None, tuple]] = []
    items: list[tuple] = []
    align: str | None = None
    props: tuple = (0.0, 0.0, 0.0, ())
    rel = 1.0
    try:
        tokens = list(MTextParser(content, start))
    except Exception as error:
        return ("ID_TextEntity", f"MTEXT content is not readable: {type(error).__name__}")
    for token in tokens:
        ctx = token.ctx
        if token.type in refused:
            return ("ID_TextEntity", refused[token.type])
        if token.type == TokenType.WORD:
            if ctx.overline:
                return ("ID_TextEntity", "MTEXT overline: no font table states where it goes")
            if not math.isclose(ctx.char_tracking_factor, 1.0, rel_tol=1e-9):
                return ("ID_TextEntity", "MTEXT character tracking")
            if ctx.align != MTextLineAlignment.BOTTOM:
                return ("ID_TextEntity", "MTEXT line alignment is not bottom")
            para = ctx.paragraph
            if para.align not in aligns:
                return ("ID_TextEntity", "MTEXT distributed paragraph: ezdxf cannot lay it out either")
            if not all(math.isfinite(float(v)) for v in (para.indent, para.left, para.right)):
                return ("ID_DegenerateEntity", "MTEXT paragraph indent is not finite")
        if char_height > _EPS:
            rel = ctx.cap_height / char_height
        shape = (float(ctx.width_factor), float(ctx.oblique))
        marks = ("u" if ctx.underline else "") + ("s" if ctx.strike_through else "")
        own: Path | None = None
        if ctx.font_face != start.font_face and token.type in (TokenType.WORD, TokenType.SPACE, TokenType.NBSP):
            found = resolve_face(ctx.font_face, fonts or {})
            if isinstance(found, tuple):
                return found
            own = found
        if token.type == TokenType.WORD:
            align = aligns[ctx.paragraph.align]
            para = ctx.paragraph
            props = (float(para.indent), float(para.left), float(para.right), tuple(para.tab_stops or ()))
            word = re.sub(r"\\U\+([0-9A-Fa-f]{4})", lambda m: chr(int(m.group(1), 16)), str(token.data))
            items.append(("word", word, rel, own, shape, marks))
        elif token.type == TokenType.SPACE:
            items.append(("space", " ", rel, own, shape, marks))
        elif token.type == TokenType.NBSP:
            items.append(("nbsp", " ", rel, own, shape, marks))
        elif token.type == TokenType.TABULATOR:
            items.append(("tab", " ", rel, own, shape, marks))
        elif token.type == TokenType.NEW_PARAGRAPH:
            # An empty paragraph keeps a slot as tall as the text around it.
            paragraphs.append((align, tuple(items) if items else (("word", "", rel),), props))
            items = []
    paragraphs.append((align, tuple(items) if items else (("word", "", rel),), props))
    return tuple(paragraphs)


def dxf_mtext_block(entity: Any, doc: Any, fonts: Mapping[str, Path | str]) -> TextBlock | Decline:
    """A DXF MTEXT (ezdxf entity) as a block. DWG shares this entity model."""
    dxf = entity.dxf
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
    # MTEXT starts from the style's width factor and oblique; inline W and Q codes change them.
    style_width = float(style.dxf.get("width", 1.0))
    style_oblique = float(style.dxf.get("oblique", 0.0))
    if dxf.hasattr("text_direction"):
        direction = dxf.text_direction
        if abs(float(direction[2])) > _EPS:
            return ("ID_TiltedPlacement", "MTEXT text direction leaves the plane")
        rotation = math.degrees(math.atan2(float(direction[1]), float(direction[0])))
    else:
        rotation = float(dxf.get("rotation", 0.0))
    insert = dxf.insert
    height = float(dxf.get("char_height", 0.0))
    paragraphs = _mtext_paragraphs(str(entity.text), height, fonts, style_width, style_oblique)
    if paragraphs and isinstance(paragraphs[0], str):
        return paragraphs
    return TextBlock(
        lines=(),
        paragraphs=paragraphs,
        font=font,
        height=height,
        insert=(float(insert[0]), float(insert[1])),
        rotation=rotation,
        halign=("left", "center", "right")[(attachment - 1) % 3],
        valign=("top", "middle", "bottom")[(attachment - 1) // 3],
        line_spacing=float(dxf.get("line_spacing_factor", 1.0)),
        column_width=float(dxf.get("width", 0.0)),
        width_factor=style_width,
        oblique=style_oblique,
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
    if element.get("justification", "left-baseline") != "left-baseline":
        return ("ID_TextEntity", f"{element['justification']} is not read: only left bottom (2)")
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
