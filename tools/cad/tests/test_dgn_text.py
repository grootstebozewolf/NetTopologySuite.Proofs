"""DGN V7 text elements: this reader against OGR's DGN driver, then glyph outlines."""

from __future__ import annotations

import json
import math
import re
import struct
from pathlib import Path

import pyogrio
import pytest
import shapely
from jsonschema import Draft202012Validator
from pyogrio.raw import read

import dgn_text
import dxf_extract
import glyph_linearize
from test_text_glyphs import _ADVANCE, _CAP, _place, ttf  # noqa: F401

VALIDATOR = Draft202012Validator(json.loads(dxf_extract.SCHEMA_PATH.read_text(encoding="utf-8")))
_SEED = Path(pyogrio.__file__).parent / "gdal_data"
# seed_2d.dgn: 10 subunits per master unit, 12 units of resolution per subunit.
_PER_MASTER = 120
# Units of resolution, chosen so heights and coordinates are exact in master units.
_TEXTS = [
    {"level": 5, "font": 41, "just": 2, "length": 70000, "height": 70000, "rotation": 30.0, "x": 123456, "y": -65432, "text": "el e"},
    {"level": 12, "font": 41, "just": 2, "length": 2000, "height": 2000, "rotation": -90.0, "x": 0, "y": 600, "text": "l"},
    {"level": 3, "font": 7, "just": 2, "length": 1000, "height": 2000, "rotation": 0.0, "x": 10, "y": 20, "text": "squeezed"},
]


def _put32(value: int) -> bytes:
    raw = struct.pack("<i", value)
    return bytes((raw[2], raw[3], raw[0], raw[1]))


def _element(kind: int, level: int, body: bytes, *, deleted: bool = False) -> bytes:
    if len(body) % 2:
        body += b"\0"
    size = 36 + len(body)
    header = bytes((level, kind | (0x80 if deleted else 0))) + struct.pack("<H", size // 2 - 2)
    return header + bytes(24) + struct.pack("<HHHH", 0, (size - 32) // 2, 0, 0) + body


def _text(spec: dict, **kwargs) -> bytes:
    body = (
        bytes((spec["font"], spec["just"]))
        + _put32(spec["length"])
        + _put32(spec["height"])
        + _put32(round(spec["rotation"] * 360000))
        + _put32(spec["x"])
        + _put32(spec["y"])
        + bytes((len(spec["text"]), 0))
        + spec["text"].encode("latin-1")
    )
    return _element(17, spec["level"], body, **kwargs)


def _design(seed: str = "seed_2d.dgn") -> bytes:
    data = (_SEED / seed).read_bytes()
    end = next(offset for offset, _ in reversed(list(dgn_text.elements(data)))) + len(list(dgn_text.elements(data))[-1][1])
    line = _element(3, 9, _put32(0) + _put32(0) + _put32(1200) + _put32(1200))
    gone = _text({**_TEXTS[0], "text": "gone"}, deleted=True)
    return data[:end] + b"".join(_text(spec) for spec in _TEXTS[:2]) + line + gone + _text(_TEXTS[2]) + b"\xff\xff"


@pytest.fixture(scope="module")
def dgn(tmp_path_factory: pytest.TempPathFactory) -> Path:
    path = tmp_path_factory.mktemp("dgn") / "labels.dgn"
    path.write_bytes(_design())
    return path


def test_pyogrio_requirement_is_an_exact_pin() -> None:
    text = (Path(__file__).resolve().parents[1] / "requirements.txt").read_text(encoding="utf-8")
    assert "pyogrio==0.13.0\n" in text


def test_text_fields_match_the_ogr_dgn_driver(dgn: Path) -> None:
    meta, _fid, geometry, fields = read(dgn, sql="SELECT *, OGR_STYLE FROM elements", sql_dialect="OGRSQL")
    table = dict(zip(meta["fields"], (column.tolist() for column in fields)))
    ogr = [
        (text, level, shapely.from_wkb(wkb), style)
        for kind, text, level, wkb, style in zip(table["Type"], table["Text"], table["Level"], geometry, table["OGR_STYLE"])
        if kind == 17
    ]
    data = dgn.read_bytes()
    stream = list(dgn_text.elements(data))
    tcb = dgn_text.control(stream[0][1])
    mine = [
        (raw[0] & 0x3F, dgn_text.text_element(raw, tcb))
        for _offset, raw in stream
        if raw[1] == 17
    ]
    assert len(ogr) == len(mine) == 3
    for (text, level, point, style), (my_level, element), spec in zip(ogr, mine, _TEXTS):
        assert (element["text"], my_level) == (text, level) == (spec["text"], spec["level"])
        assert element["origin"] == pytest.approx([point.x, point.y], rel=1e-12)
        # OGR prints the angle as int(rotation + 0.5), which truncates toward zero.
        angle = int(re.search(r"a:(-?[0-9]+)", style).group(1)) if "a:" in style else 0
        assert math.trunc(element["rotation"] + 0.5) == angle
        assert element["rotation"] == spec["rotation"]
        assert element["height"] == pytest.approx(float(re.search(r"s:([0-9.]+)g", style).group(1)))
        assert element["height"] == pytest.approx(spec["height"] * 6 / 1000 / _PER_MASTER)
        assert (element["font"], element["justificationCode"]) == (spec["font"], spec["just"])


def test_vax_double_decodes_known_values() -> None:
    assert dgn_text.vax_double(bytes(8), 0) == 0.0
    # 1.0 is 0.5 * 2^1: exponent 129, zero fraction. -3.0 is -0.75 * 2^2.
    assert dgn_text.vax_double(struct.pack("<4H", 129 << 7, 0, 0, 0), 0) == 1.0
    assert dgn_text.vax_double(struct.pack("<4H", 0x8000 | (130 << 7) | 0x40, 0, 0, 0), 0) == -3.0


def test_rows_account_for_every_graphic_element(dgn: Path, ttf: Path) -> None:
    rows = dgn_text.extract_path(dgn, fonts={41: ttf}, file_id="labels")
    for row in rows:
        VALIDATOR.validate(row)
    assert [row["record"] for row in rows] == ["entity", "entity", "decline", "decline"]
    assert (rows[2]["id"], rows[2]["name"]) == ("ID_UnsupportedEntity", "DGN type 3")
    assert rows[3]["id"] == "ID_TextEntity" and "font 7" in rows[3]["reason"]
    label, stem = rows[0], rows[1]
    assert label["provenance"] == {
        "format": "DGN",
        "version": "V7",
        "handle": label["provenance"]["handle"],
        "layer": "5",
        "blockPath": [],
        "fileId": "labels",
    }
    assert label["units"]["linear"] == "ft"
    assert stem["provenance"]["layer"] == "12"
    assert len(label["params"]["members"]) == 3

    # 70000 units of resolution is 3.5 master units of cap height.
    glyph = label["params"]["members"][1]
    text_link = glyph["placement"]["links"][1]
    assert text_link["scale"] == pytest.approx(3.5 / _CAP)
    assert text_link["rotate"] == pytest.approx(30)
    origin = dgn_text.text_element(_text(_TEXTS[0]), dgn_text.control(dgn.read_bytes()[:1536]))["origin"]
    assert text_link["translate"] == pytest.approx(origin)
    assert glyph["placement"]["links"][0]["translate"] == [_ADVANCE["e"], 0]
    foot = _place((100, 0), glyph["placement"]["links"])
    top = _place((100, 700), glyph["placement"]["links"])
    assert math.dist(foot, top) == pytest.approx(3.5)

    out = glyph_linearize.linearize_row(label, hausdorff=0.001)
    assert out["polygons"] == 3


def test_squeezed_text_declines_only_for_its_missing_glyphs(dgn: Path, ttf: Path) -> None:
    # Length half the height is a width factor of 0.5, applied to the glyphs. The font has no "s".
    rows = dgn_text.extract_path(dgn, fonts={41: ttf, 7: ttf})
    assert (rows[3]["id"], rows[3]["reason"]) == ("ID_TextEntity", "font has no glyph for U+0073")


def test_text_without_fonts_declines(dgn: Path) -> None:
    rows = dgn_text.extract_path(dgn)
    assert [row["id"] for row in rows] == ["ID_TextEntity", "ID_TextEntity", "ID_UnsupportedEntity", "ID_TextEntity"]


def test_three_d_file_declines_text_and_v8_is_refused(ttf: Path) -> None:
    rows = dgn_text.extract_bytes(_design("seed_3d.dgn"), fonts={41: ttf, 7: ttf})
    assert [row["id"] for row in rows if row["provenance"]["layer"] in ("5", "12", "3")] == ["ID_ThreeDNotYet"] * 3
    with pytest.raises(ValueError, match="V8"):
        dgn_text.extract_bytes(bytes.fromhex("d0cf11e0a1b11ae1") + bytes(600))
    with pytest.raises(ValueError, match="type 9"):
        dgn_text.extract_bytes(_text(_TEXTS[0]) + b"\xff\xff")


def test_cli_writes_json_lines(dgn: Path, ttf: Path, capsys, tmp_path: Path) -> None:
    assert dgn_text.main([str(dgn), "--font", f"41={ttf}"]) == 0
    rows = [json.loads(line) for line in capsys.readouterr().out.splitlines()]
    assert [row["record"] for row in rows] == ["entity", "entity", "decline", "decline"]
    assert dgn_text.main([str(dgn), "--font", "arial=nowhere.ttf"]) == 2
    v8 = tmp_path / "v8.dgn"
    v8.write_bytes(bytes.fromhex("d0cf11e0a1b11ae1") + bytes(600))
    assert dgn_text.main([str(v8)]) == 2


def test_other_justification_and_wide_text_decline_by_name(ttf: Path) -> None:
    data = (_SEED / "seed_2d.dgn").read_bytes()
    stream = list(dgn_text.elements(data))
    end = stream[-1][0] + len(stream[-1][1])
    centred = _text({**_TEXTS[1], "just": 7})
    wide = bytearray(_text({**_TEXTS[1], "text": "ab"}))
    wide[60:62] = b"\xff\xfd"
    rows = dgn_text.extract_bytes(data[:end] + centred + bytes(wide) + b"\xff\xff", fonts={41: ttf})
    assert [(row["id"], row["reason"]) for row in rows] == [
        ("ID_TextEntity", "DGN justification code 7 is not read: only left bottom (2)"),
        ("ID_TextEntity", "DGN 16-bit text (0xFF 0xFD) is not read"),
    ]
