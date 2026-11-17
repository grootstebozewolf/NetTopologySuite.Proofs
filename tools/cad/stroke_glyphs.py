#!/usr/bin/env python3
"""SHX and SHP stroke fonts to pen strokes of chords and bulge arcs.

ezdxf (MIT) reads the shape file into shape code lists; its code is not
ported and its renderer, which turns arcs into Beziers, is not used. This
module runs the codes itself and keeps every arc an arc.

A line of text is one pen walk. The pen starts down at the origin, and
each character continues from where the last one stopped, so a
character's advance is its pen travel. Codes: 0 end, 1 pen down, 2 pen
up, 3 and 4 divide and multiply the vector length, 5 and 6 push and pop
the position, 7 a subshape, 8 and 9 displacements, 10 an octant arc, 12
and 13 bulge arcs, 14 the next command is for vertical text only. A byte
above 15 is a vector: length in the high nibble, one of 16 directions in
the low nibble.

A stroke is a run of pen-down segments. A segment is the carrier
``segment``: Chord, or Arc with the source bulge ``tan(sweep / 4)``,
positive counter-clockwise. A bulge arc keeps ``b / 127``. An octant arc
of ``n`` octants has bulge ``tan(n * pi / 16)``, and a full circle is two
half circles, since a bulge segment cannot close on itself.

Declined, by reason: a character with no shape, a fractional arc (code
11, whose reference rendering is itself marked inexact), a position stack
underflow or one deeper than four, and a subshape nested deeper than 16.
"""

from __future__ import annotations

import math
from pathlib import Path
from typing import Any

Decline = tuple[str, str]
Point = tuple[float, float]

VEC_X = (1, 1, 1, 0.5, 0, -0.5, -1, -1, -1, -1, -1, -0.5, 0, 0.5, 1, 1)
VEC_Y = (0, 0.5, 1, 1, 1, 1, 1, 0.5, 0, -0.5, -1, -1, -1, -1, -1, -0.5)
STROKE_SUFFIXES = (".shx", ".shp")


class _Refused(Exception):
    pass


class StrokeFont:
    """A shape font: cap height, descent, and the pen walk of a line."""

    def __init__(self, path: Path) -> None:
        from ezdxf.fonts import shapefile

        self._file = shapefile.readfile(str(path))
        if not self._file.is_font:
            raise ValueError("shape file is not a font")
        self.cap = float(self._file.above)
        self.descent = -float(self._file.below)

    def line(self, text: str) -> tuple[list[tuple[float, float, list[list[dict[str, Any]]]]], float] | Decline:
        """Per inked character: its start position and its strokes relative to that start."""
        walk = _Walk(self._file)
        placed = []
        try:
            for char in text:
                if ord(char) not in self._file.shapes:
                    return ("ID_TextEntity", f"font has no shape for U+{ord(char):04X}")
                origin = walk.at
                walk.strokes = []
                walk.down = True
                walk.run(ord(char), 0)
                walk.lift()
                if walk.strokes:
                    placed.append((origin[0], origin[1], _relative(walk.strokes, origin)))
        except _Refused as refused:
            return ("ID_TextEntity", str(refused))
        return (placed, walk.at[0])


def segment_x_extent(segment: dict[str, Any]) -> tuple[float, float]:
    """Exact left and right reach of a chord or bulge arc."""
    (sx, sy), (ex, ey) = segment["start"], segment["end"]
    low, high = min(sx, ex), max(sx, ex)
    bulge = segment["bulge"]
    if segment["kind"] != "Arc" or not bulge:
        return low, high
    # Centre: off the chord midpoint by (1 - b^2) / (4 b) along the chord's left normal.
    offset = (1.0 - bulge * bulge) / (4.0 * bulge)
    cx = (sx + ex) / 2.0 - offset * (ey - sy)
    cy = (sy + ey) / 2.0 + offset * (ex - sx)
    radius = math.hypot(sx - cx, sy - cy)
    start = math.atan2(sy - cy, sx - cx)
    sweep = 4.0 * math.atan(abs(bulge))
    for angle, reach in ((0.0, cx + radius), (math.pi, cx - radius)):
        # How far the arc must turn from its start, in its own direction, to face ``angle``.
        turned = (angle - start) % (2 * math.pi) if bulge > 0 else (start - angle) % (2 * math.pi)
        if turned < sweep:
            low, high = min(low, reach), max(high, reach)
    return low, high


def ink_x_extent(placed: list[tuple[float, float, list[list[dict[str, Any]]]]]) -> tuple[float, float]:
    """Left and right edge of the strokes of a line, pen positions included."""
    lows, highs = [], []
    for pen_x, _pen_y, strokes in placed:
        for stroke in strokes:
            for segment in stroke:
                low, high = segment_x_extent(segment)
                lows.append(pen_x + low)
                highs.append(pen_x + high)
    return min(lows), max(highs)


def _relative(strokes: list[list[dict[str, Any]]], origin: Point) -> list[list[dict[str, Any]]]:
    def shift(point: list[float]) -> list[float]:
        return [point[0] - origin[0], point[1] - origin[1]]

    return [
        [{**segment, "start": shift(segment["start"]), "end": shift(segment["end"])} for segment in stroke]
        for stroke in strokes
    ]


class _Walk:
    def __init__(self, shape_file: Any) -> None:
        self.file = shape_file
        self.at: Point = (0.0, 0.0)
        self.length = 1.0
        self.down = True
        self.stack: list[Point] = []
        self.strokes: list[list[dict[str, Any]]] = []
        self.open: list[dict[str, Any]] = []

    def lift(self) -> None:
        if self.open:
            self.strokes.append(self.open)
            self.open = []

    def jump(self, to: Point) -> None:
        self.lift()
        self.at = to

    def draw(self, to: Point, bulge: float = 0.0) -> None:
        if not self.down:
            self.jump(to)
            return
        if to != self.at:
            kind = "Arc" if bulge else "Chord"
            self.open.append({"kind": kind, "start": list(self.at), "end": list(to), "bulge": bulge})
        self.at = to

    def move(self, dx: float, dy: float, bulge: float = 0.0) -> None:
        self.draw((self.at[0] + dx * self.length, self.at[1] + dy * self.length), bulge)

    def octant_arc(self, radius: float, spec: int) -> None:
        clockwise = spec < 0
        spec = abs(spec)
        start, span = (spec >> 4) & 0xF, (spec & 0xF) or 8
        turn = -1.0 if clockwise else 1.0
        radius *= self.length
        angle = start * math.pi / 4
        centre = (self.at[0] - radius * math.cos(angle), self.at[1] - radius * math.sin(angle))

        def on_circle(octants: float) -> Point:
            a = angle + turn * octants * math.pi / 4
            return (centre[0] + radius * math.cos(a), centre[1] + radius * math.sin(a))

        if span == 8:
            began = self.at
            self.draw(on_circle(4), turn)
            self.draw(began, turn)
        else:
            self.draw(on_circle(span), turn * math.tan(span * math.pi / 16))

    def run(self, number: int, depth: int) -> None:
        if depth > 16:
            raise _Refused("subshape nesting is deeper than 16")
        if number not in self.file.shapes:
            raise _Refused(f"font has no subshape {number}")
        codes = self.file.get_codes(number)
        index = 0
        skip = False
        while index < len(codes):
            code = codes[index]
            index += 1
            # ``skip`` is set by code 14 and hides exactly the next command, arguments included.
            hidden, skip = skip, False
            if code == 0:
                return
            if code > 15:
                if not hidden:
                    self.move(VEC_X[code & 0xF] * (code >> 4), VEC_Y[code & 0xF] * (code >> 4))
            elif code == 1:
                if not hidden:
                    self.down = True
            elif code == 2:
                if not hidden:
                    self.down = False
                    self.lift()
            elif code in (3, 4):
                factor = codes[index]
                index += 1
                if not hidden:
                    if factor == 0:
                        raise _Refused("vector length scaled by zero")
                    self.length = self.length / factor if code == 3 else self.length * factor
            elif code == 5:
                if not hidden:
                    if len(self.stack) >= 4:
                        raise _Refused("position stack is deeper than four")
                    self.stack.append(self.at)
            elif code == 6:
                if not hidden:
                    if not self.stack:
                        raise _Refused("position stack underflow")
                    self.jump(self.stack.pop())
            elif code == 7:
                sub = codes[index]
                index += 1
                if not hidden:
                    self.run(sub, depth + 1)
            elif code == 8:
                dx, dy = codes[index], codes[index + 1]
                index += 2
                if not hidden:
                    self.move(dx, dy)
            elif code == 9:
                while True:
                    dx, dy = codes[index], codes[index + 1]
                    index += 2
                    if dx == 0 and dy == 0:
                        break
                    if not hidden:
                        self.move(dx, dy)
            elif code == 10:
                radius, spec = codes[index], codes[index + 1]
                index += 2
                if not hidden:
                    if radius == 0:
                        raise _Refused("octant arc of zero radius")
                    self.octant_arc(radius, spec)
            elif code == 11:
                raise _Refused("fractional arc (shape code 11)")
            elif code == 12:
                dx, dy, bulge = codes[index], codes[index + 1], codes[index + 2]
                index += 3
                if not hidden:
                    self.move(dx, dy, bulge / 127.0)
            elif code == 13:
                while True:
                    dx, dy = codes[index], codes[index + 1]
                    if dx == 0 and dy == 0:
                        index += 2
                        break
                    bulge = codes[index + 2]
                    index += 3
                    if not hidden:
                        self.move(dx, dy, bulge / 127.0)
            elif code == 14:
                skip = True
            elif code == 15:
                raise _Refused("unknown shape code 15")
