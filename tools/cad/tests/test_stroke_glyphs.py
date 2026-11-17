"""SHX/SHP stroke fonts: pen strokes against ezdxf's shape renderer, then carrier rows."""

from __future__ import annotations

import json
import math
from pathlib import Path

import pytest
import shapely
from ezdxf.fonts import shapefile
from jsonschema import Draft202012Validator

import dxf_extract
import glyph_linearize
import stroke_glyphs
import text_glyphs
from test_text_glyphs import _DGN_CTX, _doc, _place

VALIDATOR = Draft202012Validator(json.loads(dxf_extract.SCHEMA_PATH.read_text(encoding="utf-8")))
_ABOVE, _BELOW = 21, 7
# A font written for this test. L, O, D advance by 18, 26 and 16; space by 10.
_SHP = b"""*0,4,CARRIERSTROKE
21,7,0,0

*32,5,spc
2,8,(10,0),0

*76,16,L
2,8,(0,21),1,8,(0,-21),8,(12,0),2,8,(6,0),0

*79,13,O
2,8,(20,10),1,10,(10,000),2,8,(6,-10),0

*68,13,D
1,8,(0,21),12,(0,-21,-127),2,8,(16,0),0

*99,24,c
3,2,2,9,(0,16),(16,0),(0,0),1,10,(8,-042),5,02C,6,4,2,14,8,(-5,-5),2,8,(4,-12),0

*80,7,P
7,76,1,044,2,04C,0

*81,12,Q
2,8,(0,10),1,13,(10,10,40),(10,-10,40),(0,0),2,8,(4,-10),0

*102,7,f
11,(0,125,0,10,044),0

*112,4,p
6,0

*113,3,q
7,113,0
"""


@pytest.fixture(scope="module")
def shp(tmp_path_factory: pytest.TempPathFactory) -> Path:
    path = tmp_path_factory.mktemp("stroke") / "carrierstroke.shp"
    path.write_bytes(_SHP)
    return path


def _row(font: Path, text: str, *, height: float = float(_ABOVE), **run) -> dict:
    row = text_glyphs.run_record(
        text_glyphs.TextRun(text=text, font=font, height=height, insert=(0.0, 0.0), **run), **_DGN_CTX
    )
    assert isinstance(row, dict), row
    VALIDATOR.validate(row)
    return row


def _ezdxf_lines(text: str) -> shapely.MultiLineString:
    font = shapefile.shp_load(_SHP)
    path = shapefile.render_shapes([ord(c) for c in text], font.get_codes, stacked=False)
    lines = [[(v.x, v.y) for v in sub.flattening(1e-4)] for sub in path.sub_paths()]
    return shapely.MultiLineString([line for line in lines if len(line) > 1])


def test_metrics_and_advances() -> None:
    font = stroke_glyphs.StrokeFont.__new__(stroke_glyphs.StrokeFont)
    font._file = shapefile.shp_load(_SHP)
    placed, width = font.line("L O")
    assert [(x, y) for x, y, _ in placed] == [(0, 0), (28, 0)]
    assert width == 18 + 10 + 26


def test_strokes_keep_lines_as_chords_and_arcs_as_bulges(shp: Path) -> None:
    row = _row(shp, "LODQ")
    ell, oh, dee, queue = row["params"]["members"]
    assert [m["kind"] for m in ell["params"]["members"]] == ["BulgePolyline"]
    (stroke,) = ell["params"]["members"]
    assert stroke["params"] == {
        "closed": False,
        "segments": [
            {"kind": "Chord", "start": [0, 21], "end": [0, 0], "bulge": 0},
            {"kind": "Chord", "start": [0, 0], "end": [12, 0], "bulge": 0},
        ],
    }
    # A full octant circle is two counter-clockwise half circles.
    halves = oh["params"]["members"][0]["params"]["segments"]
    assert [(s["kind"], s["bulge"]) for s in halves] == [("Arc", 1.0), ("Arc", 1.0)]
    assert halves[0]["start"] == [20, 10] and halves[0]["end"] == pytest.approx([0, 10])
    assert halves[1]["end"] == [20, 10]
    # D closes with a clockwise half circle: source bulge -127/127.
    up, back = dee["params"]["members"][0]["params"]["segments"]
    assert (back["kind"], back["bulge"], back["start"], back["end"]) == ("Arc", -1.0, [0, 21], [0, 0])
    assert [s["bulge"] for s in queue["params"]["members"][0]["params"]["segments"]] == [40 / 127, 40 / 127]
    pens = [m["placement"]["links"][0]["translate"] for m in row["params"]["members"]]
    assert pens == [[0, 0], [18, 0], [44, 0], [60, 0]]
    assert ell["placement"]["links"][1]["scale"] == 1.0


def test_scale_octant_span_stack_subshape_and_vertical_only_codes(shp: Path) -> None:
    row = _row(shp, "cP")
    cee, pee = row["params"]["members"]
    (stroke,) = cee["params"]["members"]
    arc, tail = stroke["params"]["segments"]
    # Half scale: the pen is moved to (8,8); radius 4, clockwise from octant 4 through two octants.
    assert arc["start"] == [8, 8]
    assert arc["end"] == pytest.approx([12, 12])
    assert arc["bulge"] == pytest.approx(-math.tan(math.pi / 8))
    # The 02C vector draws one unit down at half scale, then the pushed position is restored.
    assert (tail["kind"], tail["end"]) == ("Chord", pytest.approx([12, 11]))
    # Code 14 hides the (-5,-5) move, so c stops at (16,0) and P starts there.
    assert pee["placement"]["links"][0]["translate"] == pytest.approx([16, 0])
    # P is the L subshape, then a diagonal stroke from where L stopped.
    assert len(pee["params"]["members"]) == 2
    assert pee["params"]["members"][1]["params"]["segments"][0]["start"] == [18, 0]


@pytest.mark.parametrize("text", ["L", "O", "D", "Q", "LODQ cP", "c"])
def test_linearized_strokes_follow_the_ezdxf_renderer(shp: Path, text: str) -> None:
    out = glyph_linearize.linearize_row(_row(shp, text), hausdorff=1e-4)
    mine = shapely.from_wkt(out["wkt"])
    assert out["lines"] == len(mine.geoms)
    # ezdxf draws arcs as cubic Beziers, so agreement is to its approximation error.
    assert mine.hausdorff_distance(_ezdxf_lines(text)) < 5e-3


def test_arc_flattening_stays_on_the_circle_within_the_sagitta() -> None:
    points = glyph_linearize.arc_points((10.0, 0.0), (-10.0, 0.0), 1.0, 0.01) + [(-10.0, 0.0)]
    assert all(math.hypot(x, y) == pytest.approx(10) for x, y in points)
    assert all(y >= -1e-9 for _, y in points)
    worst = max(10 - math.hypot((a[0] + b[0]) / 2, (a[1] + b[1]) / 2) for a, b in zip(points, points[1:]))
    assert 0 < worst <= 0.01
    clockwise = glyph_linearize.arc_points((10.0, 0.0), (-10.0, 0.0), -1.0, 0.01)
    assert all(y <= 1e-9 for _, y in clockwise)
    assert len(glyph_linearize.arc_points((10.0, 0.0), (-10.0, 0.0), 1.0, 1e9)) == 1


def test_dxf_text_and_mtext_with_a_stroke_style(shp: Path) -> None:
    doc = _doc("CarrierStroke.SHP")
    msp = doc.modelspace()
    msp.add_text("LO", height=7, rotation=90, dxfattribs={"style": "GLYPH", "insert": (10, 20), "valign": 3, "align_point": (10, 20)})
    msp.add_mtext(r"L\PLO", dxfattribs={"style": "GLYPH", "char_height": 7, "insert": (0, 0), "attachment_point": 3})
    msp.add_text("LO", height=7, dxfattribs={"style": "GLYPH", "halign": 1, "align_point": (10, 20)})
    text, mtext, centred = dxf_extract.extract_document(doc, fonts={"carrierstroke.shp": shp}, file_id="stroke")
    for row in (text, mtext, centred):
        VALIDATOR.validate(row)
    ell = text["params"]["members"][0]
    assert ell["placement"]["links"][1]["scale"] == pytest.approx(7 / _ABOVE)
    # Top alignment: the cap top of L, rotated 90 degrees, sits on the align point.
    assert _place((0, _ABOVE), ell["placement"]["links"]) == pytest.approx((10, 20))
    assert _place((12, 0), ell["placement"]["links"]) == pytest.approx((10 + 7, 20 + 4))
    # Top right attachment: the second line "LO" is 44 wide and one pitch down.
    last = mtext["params"]["members"][-1]
    assert last["placement"]["links"][0]["translate"] == pytest.approx([18 - 44, -_ABOVE - _ABOVE * 5 / 3])
    # Centre: L reaches 0..12 and O, from pen 18, reaches 18..38, so the ink centre is 19.
    assert _place((19, 0), centred["params"]["members"][0]["placement"]["links"]) == pytest.approx((10, 20))
    out = glyph_linearize.linearize_row(text, hausdorff=0.001)
    assert out["wkt"].startswith("MULTILINESTRING ((") and out["lines"] == 2


@pytest.mark.parametrize(
    ("text", "reason"),
    [("f", "fractional arc"), ("p", "underflow"), ("q", "deeper than 16"), ("Lx", "U+0078"), (" ", "no inked glyph")],
)
def test_named_stroke_declines(shp: Path, text: str, reason: str) -> None:
    out = text_glyphs.run_record(
        text_glyphs.TextRun(text=text, font=shp, height=7.0, insert=(0.0, 0.0)), **_DGN_CTX
    )
    assert out[0] == "ID_TextEntity" and reason in out[1]


def test_unreadable_font_file_declines(tmp_path: Path) -> None:
    bad = tmp_path / "broken.shx"
    bad.write_bytes(b"not a shape file")
    out = text_glyphs.run_record(text_glyphs.TextRun(text="L", font=bad, height=7.0, insert=(0.0, 0.0)), **_DGN_CTX)
    assert out[0] == "ID_TextEntity" and "not readable" in out[1]


def test_stroke_ink_reach_follows_the_arcs(shp: Path) -> None:
    # D: a clockwise half circle from (0,21) to (0,0) bulges right to x = 10.5.
    half = {"kind": "Arc", "start": [0, 21], "end": [0, 0], "bulge": -1.0}
    assert stroke_glyphs.segment_x_extent(half) == pytest.approx((0, 10.5))
    assert stroke_glyphs.segment_x_extent({**half, "bulge": 1.0}) == pytest.approx((-10.5, 0))
    # A shallow arc between the same points stays near its chord: sagitta = b * chord / 2.
    shallow = stroke_glyphs.segment_x_extent({**half, "bulge": -0.1})
    assert shallow == pytest.approx((0, 0.1 * 21 / 2))
    # Three quarters of a circle about (1,1), radius sqrt 2: it passes angle 0 but not angle pi.
    wide = {"kind": "Arc", "start": [0, 0], "end": [0, 2], "bulge": math.tan(3 * math.pi / 8)}
    assert stroke_glyphs.segment_x_extent(wide) == pytest.approx((0, 1 + math.sqrt(2)))
    assert stroke_glyphs.segment_x_extent({**wide, "bulge": -wide["bulge"]}) == pytest.approx((-1 - math.sqrt(2), 0))

    doc = _doc("carrierstroke.shp")
    msp = doc.modelspace()
    msp.add_text("D", height=21, dxfattribs={"style": "GLYPH", "halign": 2, "align_point": (50, 5)})
    msp.add_text("LD", height=999, dxfattribs={"style": "GLYPH", "halign": 3, "insert": (0, 0), "align_point": (0, 57)})
    right, aligned = dxf_extract.extract_document(doc, fonts={"carrierstroke.shp": shp}, file_id="stroke")
    dee = right["params"]["members"][0]
    assert _place((10.5, 0), dee["placement"]["links"]) == pytest.approx((50, 5))
    # Aligned: ink runs from 0 to 18 + 10.5 = 28.5 and is fitted to a span of 57, straight up.
    link = aligned["params"]["members"][0]["placement"]["links"][1]
    assert (link["scale"], link["rotate"]) == pytest.approx((2.0, 90.0))
    assert _place((10.5, 0), aligned["params"]["members"][1]["placement"]["links"]) == pytest.approx((0, 57))
