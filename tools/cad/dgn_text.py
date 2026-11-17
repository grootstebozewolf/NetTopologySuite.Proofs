#!/usr/bin/env python3
"""DGN V7 text elements to CAD carrier JSON lines.

Reads the element stream of a 2D DGN V7 design file and writes one row
per graphic element. A type 17 text element whose font number maps to an
outline font becomes a Compound of glyph outlines through
``text_glyphs``. Every other graphic element is ``ID_UnsupportedEntity``
with its type number, and a text element without a font is
``ID_TextEntity``; this reader is the text slice only. Deleted elements
and the non-graphic types 8, 9, 10 and 66 are not considered entities.

Layout, per element: a level byte, a type byte (bit 7 is deleted), a
count of 16-bit words that follow, a 24-byte range, and four header
words. A 2D text element then holds font (1 byte), justification (1),
length and height multipliers (int32 each), rotation (int32, 1/360000
degree counter-clockwise), origin x and y (int32 units of resolution),
a character count, an enter-data field count, and the characters. An
int32 is stored as two little-endian words, high word first.

The type 9 control element gives subunits per master unit and units of
resolution per subunit (int32 at 1112 and 1116), the unit names (1120),
the 3D flag (bit 6 of byte 1214), and the global origin (VAX D doubles
at 1240 and 1248, in units of resolution). A coordinate in master units
is ``(raw - origin) / (uor * subunits)``. A character size in master
units is ``multiplier * 6 / 1000 / (uor * subunits)``.

Only justification code 2 (left bottom) is read, with the stored origin
as the left baseline point; any other code declines by name, since
whether the origin then moves with the justification is not settled
here. The height is read as the cap height. Unequal length and height is
a width factor, applied to the glyph numbers. Text stored as 16-bit
characters (the ``0xFF 0xFD`` prefix) declines by name rather than being
decoded as latin-1. A 3D file declines every text as ID_ThreeDNotYet. A V8 file
is not an element stream and is refused.

OGR's DGN driver (MIT) is the reference reader in the tests; its code is
not ported.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import struct
import sys
from pathlib import Path
from typing import Any, Iterator, Mapping

import text_glyphs

NON_GRAPHIC_TYPES = frozenset({8, 9, 10, 66})
_V8_MAGIC = bytes.fromhex("d0cf11e0")


def _int32(data: bytes, offset: int) -> int:
    return struct.unpack("<i", bytes((data[offset + 2], data[offset + 3], data[offset], data[offset + 1])))[0]


def vax_double(data: bytes, offset: int) -> float:
    """VAX D floating point: four little-endian words, sign and exponent in the first."""
    words = struct.unpack("<4H", data[offset : offset + 8])
    exponent = (words[0] >> 7) & 0xFF
    if exponent == 0:
        return 0.0
    fraction = (1 << 55) | ((words[0] & 0x7F) << 48) | (words[1] << 32) | (words[2] << 16) | words[3]
    value = fraction / float(1 << 56) * 2.0 ** (exponent - 128)
    return -value if words[0] & 0x8000 else value


def elements(data: bytes) -> Iterator[tuple[int, bytes]]:
    """Byte offset and raw bytes of each element, up to the end marker."""
    offset = 0
    while offset + 4 <= len(data):
        if data[offset] == 0xFF and data[offset + 1] == 0xFF:
            return
        size = (data[offset + 2] + data[offset + 3] * 256) * 2 + 4
        if offset + size > len(data):
            raise ValueError(f"element at byte {offset} runs past the end of the file")
        yield offset, data[offset : offset + size]
        offset += size


def control(raw: bytes) -> dict[str, Any]:
    """Units, global origin and dimension from the type 9 control element."""
    if len(raw) < 1264:
        raise ValueError("control element is too short")
    subunits = _int32(raw, 1112)
    uor = _int32(raw, 1116)
    if subunits <= 0 or uor <= 0:
        raise ValueError("control element states no working units")
    name = raw[1120:1122].decode("latin-1").strip().lower()
    return {
        "per_master": float(subunits * uor),
        "origin": (vax_double(raw, 1240), vax_double(raw, 1248)),
        "three_d": bool(raw[1214] & 0x40),
        "unit": name or "unitless",
    }


def text_element(raw: bytes, tcb: Mapping[str, Any]) -> dict[str, Any]:
    """The fields of a 2D type 17 element, in master units and degrees."""
    count = raw[58]
    if len(raw) < 60 + count:
        raise ValueError("text element is shorter than its character count")
    per_master = tcb["per_master"]
    size = 6.0 / 1000.0 / per_master
    return {
        "type": 17,
        "font": raw[36],
        "justificationCode": raw[37],
        # Only code 2 (left bottom) is read: the origin is then the left baseline point.
        "justification": "left-baseline" if raw[37] == 2 else f"DGN justification code {raw[37]}",
        "wide": raw[60:62] == b"\xff\xfd",
        "width": _int32(raw, 38) * size,
        "height": _int32(raw, 42) * size,
        "rotation": _int32(raw, 46) / 360000.0,
        "origin": [
            (_int32(raw, 50) - tcb["origin"][0]) / per_master,
            (_int32(raw, 54) - tcb["origin"][1]) / per_master,
        ],
        "text": raw[60 : 60 + count].decode("latin-1"),
    }


def extract_bytes(
    data: bytes,
    *,
    fonts: Mapping[Any, Path | str] | None = None,
    tolerance: dict[str, Any] | None = None,
    file_id: str = "unnamed",
) -> list[dict[str, Any]]:
    """Carrier rows and declines for the graphic elements of a V7 file."""
    if data[:4] == _V8_MAGIC:
        raise ValueError("DGN V8 is not an element stream and is not read")
    stream = list(elements(data))
    if not stream or stream[0][1][1] & 0x7F != 9:
        raise ValueError("not a DGN V7 design file: the first element is not type 9")
    tcb = control(stream[0][1])
    units = {"linear": tcb["unit"], "angle": "degree", "angdir": 0, "angbase": 0.0}
    tol = tolerance if tolerance is not None else {"kind": "sourceDefault"}
    rows: list[dict[str, Any]] = []
    for offset, raw in stream:
        kind = raw[1] & 0x7F
        if raw[1] & 0x80 or kind in NON_GRAPHIC_TYPES:
            continue
        provenance = {
            "format": "DGN",
            "version": "V7",
            "handle": str(offset),
            "layer": str(raw[0] & 0x3F),
            "blockPath": [],
            "fileId": file_id,
        }

        def decline(decline_id: str, reason: str, name: str | None = None) -> None:
            row = {"record": "decline", "id": decline_id, "provenance": provenance, "reason": reason}
            if name is not None:
                row["name"] = name
            rows.append(row)

        if kind != 17:
            decline("ID_UnsupportedEntity", f"unsupported DGN type {kind}", f"DGN type {kind}")
            continue
        if tcb["three_d"]:
            decline("ID_ThreeDNotYet", "text in a 3D design file")
            continue
        if not fonts:
            decline("ID_TextEntity", "ID_TextEntity")
            continue
        element = text_element(raw, tcb)
        if element["wide"]:
            decline("ID_TextEntity", "DGN 16-bit text (0xFF 0xFD) is not read")
            continue
        run = text_glyphs.dgn_text_run(element, fonts)
        if isinstance(run, tuple):
            decline(run[0], run[1])
            continue
        row = text_glyphs.run_record(
            run,
            links=[],
            units=units,
            tolerance=tol,
            dimension={"space": "2d"},
            provenance=provenance,
        )
        if isinstance(row, tuple):
            decline(row[0], row[1])
        else:
            rows.append(row)
    return rows


def extract_path(
    path: Path,
    *,
    fonts: Mapping[Any, Path | str] | None = None,
    tolerance: dict[str, Any] | None = None,
    file_id: str | None = None,
) -> list[dict[str, Any]]:
    data = path.read_bytes()
    return extract_bytes(
        data,
        fonts=fonts,
        tolerance=tolerance,
        file_id=file_id if file_id is not None else hashlib.sha256(data).hexdigest(),
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Extract DGN V7 text into CAD carrier JSON lines.")
    parser.add_argument("dgn", type=Path)
    parser.add_argument("output", type=Path, nargs="?", help="JSON lines path, or stdout if omitted")
    parser.add_argument(
        "--font",
        action="append",
        default=[],
        metavar="NUMBER=PATH",
        help="outline font for a DGN font number; repeatable",
    )
    parser.add_argument("--file-id", default=None)
    args = parser.parse_args(argv)
    fonts: dict[int, Path] = {}
    for item in args.font:
        number, sep, font_path = item.partition("=")
        if not sep or not number.isdigit() or not Path(font_path).is_file():
            print(f"bad font: {item}", file=sys.stderr)
            return 2
        fonts[int(number)] = Path(font_path)
    if not args.dgn.is_file():
        print(f"not a file: {args.dgn}", file=sys.stderr)
        return 2
    try:
        rows = extract_path(args.dgn, fonts=fonts, file_id=args.file_id)
    except ValueError as error:
        print(str(error), file=sys.stderr)
        return 2
    lines = "".join(json.dumps(row, allow_nan=False, separators=(",", ":")) + "\n" for row in rows)
    if args.output is None:
        sys.stdout.write(lines)
    else:
        args.output.write_text(lines, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
