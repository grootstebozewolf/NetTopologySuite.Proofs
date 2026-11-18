"""Underline and strike-through as filled bars from the font's own bands."""

from __future__ import annotations

import io
import math
from pathlib import Path

import freetype
import pytest
import shapely
from fontTools.ttLib import TTFont

import glyph_linearize
import text_glyphs
from test_text_glyphs import _ADVANCE, _CAP, _DGN_CTX, _doc, _otf_bytes, _place, _rows, _ttf_bytes

# The underline band crosses the foot of every stem: top 50, thickness 100.
_UNDER_TOP, _UNDER_THICK = 50, 100
_STRIKE_TOP, _STRIKE_SIZE = 400, 60


def _banded(raw: bytes, path: Path) -> Path:
    font = TTFont(io.BytesIO(raw))
    font["post"].underlinePosition = _UNDER_TOP
    font["post"].underlineThickness = _UNDER_THICK
    font["OS/2"].yStrikeoutPosition = _STRIKE_TOP
    font["OS/2"].yStrikeoutSize = _STRIKE_SIZE
    font.save(str(path))
    return path


@pytest.fixture(scope="module")
def banded(tmp_path_factory: pytest.TempPathFactory) -> Path:
    return _banded(_ttf_bytes(), tmp_path_factory.mktemp("bands") / "carriertext.ttf")


@pytest.fixture(scope="module")
def banded_cff(tmp_path_factory: pytest.TempPathFactory) -> Path:
    return _banded(_otf_bytes(), tmp_path_factory.mktemp("bands") / "carriertext.otf")


def _bars(row: dict) -> list[dict]:
    """Members whose contour sits on a decoration band."""
    bands = {(-_UNDER_THICK + _UNDER_TOP, _UNDER_TOP), (_STRIKE_TOP - _STRIKE_SIZE, _STRIKE_TOP)}
    out = []
    for member in row["params"]["members"]:
        chords = member["params"]["members"][1]["params"]["members"]
        if any(c["kind"] != "Chord" for c in chords):
            continue
        ys = {point for c in chords for point in (c["params"]["start"][1], c["params"]["end"][1])}
        if len(member["params"]["members"]) == 2 and len(chords) == 4 and tuple(sorted(ys)) in bands:
            out.append(member)
    return out


def _band(member: dict) -> tuple[list[list[float]], list[dict]]:
    chords = member["params"]["members"][1]["params"]["members"]
    return [c["params"]["start"] for c in chords], member["placement"]["links"]


def test_band_centre_is_freetypes_underline_position(banded: Path) -> None:
    face = text_glyphs._open_face(banded)
    low, high = face.bands["u"]
    face.close()
    reference = freetype.Face(str(banded))
    assert (low + high) / 2 == pytest.approx(reference.underline_position, abs=0.5)
    assert high - low == reference.underline_thickness


def test_mtext_underline_spans_marked_words_and_the_spaces_between(banded: Path) -> None:
    doc = _doc()
    doc.modelspace().add_mtext(r"l {\Ll l}l", dxfattribs={"style": "GLYPH", "char_height": 7, "insert": (0, 0)})
    (row,) = _rows(doc, {"carriertext.ttf": banded})
    (bar,) = _bars(row)
    # Four l glyphs ("l", "l", "l" and the unmarked "l" after the brace) and one bar.
    assert len(row["params"]["members"]) == 5
    corners, links = _band(bar)
    # One bar from the second l through the space to the end of the third l: 300 + 250 + 300.
    assert corners == [[0, -50], [0, 50], [850, 50], [850, -50]]
    assert links[0]["translate"] == pytest.approx([_ADVANCE["l"] + _ADVANCE["space"], -_CAP])
    assert bar["params"]["members"][0]["params"]["orientation"] == ["cw"]


def test_underline_is_filled_with_the_glyph_it_crosses(banded: Path) -> None:
    doc = _doc()
    doc.modelspace().add_mtext(r"\Ll", dxfattribs={"style": "GLYPH", "char_height": 7})
    (row,) = _rows(doc, {"carriertext.ttf": banded})
    out = glyph_linearize.linearize_row(row, hausdorff=1e-4)
    assert out["noded"] is True and out["polygons"] == 1
    shape = shapely.from_wkt(out["wkt"])
    k = 7 / _CAP
    # Stem 100..200 x 0..700 and bar 0..300 x -50..50 overlap in 100..200 x 0..50.
    assert shape.area == pytest.approx((100 * 700 + 300 * 100 - 100 * 50) * k * k)
    overlap = _place((150, 25), row["params"]["members"][0]["placement"]["links"])
    assert shape.contains(shapely.Point(overlap))


def test_bar_winds_like_the_fonts_own_outer_contours(banded_cff: Path) -> None:
    # The test CFF font draws its blob clockwise, against the CFF convention. The bar follows the font.
    doc = _doc("carriertext.otf")
    doc.modelspace().add_mtext(r"\Lo", dxfattribs={"style": "GLYPH", "char_height": 7})
    (row,) = _rows(doc, {"carriertext.otf": banded_cff})
    (bar,) = _bars(row)
    (blob,) = [m for m in row["params"]["members"] if m is not bar]
    assert bar["params"]["members"][0]["params"]["orientation"] == ["cw"]
    assert blob["params"]["members"][0]["params"]["orientation"] == ["cw"]
    out = glyph_linearize.linearize_row(row, hausdorff=1e-4)
    shape = shapely.from_wkt(out["wkt"])
    k = 7 / _CAP
    bar_area = 700 * 100 * k * k
    alone = shapely.from_wkt(glyph_linearize.linearize_row({**row, "params": {"members": [blob]}}, hausdorff=1e-4)["wkt"])
    rect = shapely.Polygon([_place(p, bar["placement"]["links"]) for p in [(0, -50), (700, -50), (700, 50), (0, 50)]])
    assert shape.area == pytest.approx(alone.union(rect).area, rel=1e-6)
    assert shape.area < alone.area + bar_area


def test_text_percent_codes_toggle_underline_and_strike(banded: Path) -> None:
    assert text_glyphs.text_marks("a%%ub%%kc%%ud%%k%%%e") == ("abcd%e", ("", "u", "su", "s", "", ""))
    assert text_glyphs.text_marks("%%Ux%%d")[1] == ("u", "u")
    assert text_glyphs.text_marks("%%ox")[0] == "ID_TextEntity"

    doc = _doc()
    doc.modelspace().add_text("l%%k l%%k", height=7, rotation=90, dxfattribs={"style": "GLYPH", "insert": (10, 20)})
    (row,) = _rows(doc, {"carriertext.ttf": banded})
    (bar,) = _bars(row)
    corners, links = _band(bar)
    # Strike from the space through the second l: 250 + 300 long, band 340..400.
    assert corners == [[0, 340], [0, 400], [550, 400], [550, 340]]
    assert _place((0, 400), links) == pytest.approx((10 - 400 * 7 / _CAP, 20 + 300 * 7 / _CAP))


def test_bar_follows_alignment_and_width_but_not_the_slant(banded: Path) -> None:
    doc = _doc()
    attribs = {"style": "GLYPH", "halign": 2, "align_point": (0, 0), "width": 2, "oblique": 30}
    doc.modelspace().add_text("%%ull", height=7, dxfattribs=attribs)
    (row,) = _rows(doc, {"carriertext.ttf": banded})
    (bar,) = _bars(row)
    corners, links = _band(bar)
    # Advance 600 at width 2 is 1200; the band stays upright.
    assert corners == [[0, -50], [0, 50], [1200, 50], [1200, -50]]
    # Right alignment: the ink right edge (second stem, 300 + 200, slanted and doubled) is the anchor.
    ink_right = 2 * (300 + 200 + 700 * math.tan(math.radians(30)))
    assert links[0]["translate"][0] == pytest.approx(-ink_right)


def test_underline_breaks_with_the_line_and_drops_the_break_space(banded: Path) -> None:
    doc = _doc()
    doc.modelspace().add_mtext(r"\Lll ll", dxfattribs={"style": "GLYPH", "char_height": 7, "width": 7.0})
    (row,) = _rows(doc, {"carriertext.ttf": banded})
    bars = _bars(row)
    assert [_band(b)[0][2][0] for b in bars] == [600, 600]
    assert [b["placement"]["links"][0]["translate"][1] for b in bars] == pytest.approx([-_CAP, -_CAP - _CAP * 5 / 3])


def test_stroke_font_and_bandless_font_decline(banded: Path, tmp_path: Path) -> None:
    from test_stroke_glyphs import _SHP

    shp = tmp_path / "carrierstroke.shp"
    shp.write_bytes(_SHP)
    out = text_glyphs.run_record(
        text_glyphs.TextRun(text="L", font=shp, height=7.0, insert=(0.0, 0.0), marks=("u",)), **_DGN_CTX
    )
    assert out == ("ID_TextEntity", "a stroke font states no underline position")
