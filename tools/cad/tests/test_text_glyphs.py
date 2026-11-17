"""Text entities to glyph outlines: DXF, DWG through the converter seam, and DGN."""

from __future__ import annotations

import io
import json
import math
from pathlib import Path

import ezdxf
import freetype
import pytest
from fontTools.fontBuilder import FontBuilder
from fontTools.pens.t2CharStringPen import T2CharStringPen
from fontTools.pens.ttGlyphPen import TTGlyphPen
from fontTools.ttLib import TTFont
from jsonschema import Draft202012Validator

import dxf_extract
import text_glyphs
from fixtures.gen_truetype_e import TTF_PATH, build_glyph, glyph_spans

SCHEMA = json.loads(dxf_extract.SCHEMA_PATH.read_text(encoding="utf-8"))
VALIDATOR = Draft202012Validator(SCHEMA)
_LOAD = freetype.FT_LOAD_NO_SCALE | freetype.FT_LOAD_NO_HINTING | freetype.FT_LOAD_NO_BITMAP
_STAMP = 3029529600
_CAP = 700
_ADVANCE = {"e": 800, "l": 300, "space": 250}
_NAMES = {
    "familyName": "CarrierText",
    "styleName": "Regular",
    "uniqueFontIdentifier": "CarrierText-Regular",
    "fullName": "CarrierText Regular",
    "psName": "CarrierText-Regular",
    "version": "Version 1.000",
}
# Clockwise in y-up font units, like the e outer contour.
_STEM = [(100, 0), (100, 700), (200, 700), (200, 0)]
# A clockwise cubic blob with one straight side.
_BLOB = [
    ("moveTo", [(100, 0)]),
    ("curveTo", [(0, 200), (0, 500), (100, 700)]),
    ("curveTo", [(300, 800), (500, 800), (600, 700)]),
    ("curveTo", [(700, 500), (700, 200), (600, 0)]),
    ("closePath", []),
]


def _finish(fb: FontBuilder, order: list[str], cmap: dict[int, str], metrics: dict) -> bytes:
    fb.setupHorizontalMetrics(metrics)
    fb.setupHorizontalHeader(ascent=900, descent=-100)
    fb.setupOS2(sCapHeight=_CAP)
    fb.setupPost()
    fb.setupNameTable(_NAMES)
    buf = io.BytesIO()
    fb.save(buf)
    return buf.getvalue()


def _ttf_bytes() -> bytes:
    stem = TTGlyphPen(None)
    stem.moveTo(_STEM[0])
    for point in _STEM[1:]:
        stem.lineTo(point)
    stem.closePath()
    empty = TTGlyphPen(None).glyph()
    fb = FontBuilder(1000, isTTF=True)
    fb.updateHead(created=_STAMP, modified=_STAMP)
    order = [".notdef", "space", "e", "l"]
    fb.setupGlyphOrder(order)
    cmap = {ord(" "): "space", ord("e"): "e", ord("l"): "l"}
    fb.setupCharacterMap(cmap)
    fb.setupGlyf({".notdef": empty, "space": TTGlyphPen(None).glyph(), "e": build_glyph(), "l": stem.glyph()})
    metrics = {".notdef": (600, 0), "space": (_ADVANCE["space"], 0), "e": (_ADVANCE["e"], 100), "l": (_ADVANCE["l"], 100)}
    return _finish(fb, order, cmap, metrics)


def _otf_bytes() -> bytes:
    def charstring(ops: list) -> object:
        pen = T2CharStringPen(700, None)
        for op, args in ops:
            getattr(pen, op)(*args)
        return pen.getCharString()

    fb = FontBuilder(1000, isTTF=False)
    fb.updateHead(created=_STAMP, modified=_STAMP)
    order = [".notdef", "o"]
    fb.setupGlyphOrder(order)
    cmap = {ord("o"): "o"}
    fb.setupCharacterMap(cmap)
    fb.setupCFF("CarrierText-Regular", {}, {".notdef": charstring([]), "o": charstring(_BLOB)}, {})
    return _finish(fb, order, cmap, {".notdef": (600, 0), "o": (700, 0)})


@pytest.fixture(scope="module")
def ttf(tmp_path_factory: pytest.TempPathFactory) -> Path:
    path = tmp_path_factory.mktemp("fonts") / "carriertext.ttf"
    path.write_bytes(_ttf_bytes())
    return path


@pytest.fixture(scope="module")
def otf(tmp_path_factory: pytest.TempPathFactory) -> Path:
    path = tmp_path_factory.mktemp("fonts") / "carriertext.otf"
    path.write_bytes(_otf_bytes())
    return path


def _freetype_spans(path: Path, char: str) -> list[list[tuple]]:
    face = freetype.Face(str(path))
    face.load_char(char, _LOAD)
    contours: list[list[tuple]] = []
    at: list[tuple[float, float]] = [(0.0, 0.0)]

    def xy(point) -> tuple[float, float]:
        return (float(point.x), float(point.y))

    def move_to(point, _ctx) -> None:
        contours.append([])
        at[0] = xy(point)

    def line_to(point, _ctx) -> None:
        if xy(point) != at[0]:
            contours[-1].append(("L", at[0], xy(point)))
        at[0] = xy(point)

    def conic_to(control, point, _ctx) -> None:
        contours[-1].append(("Q", at[0], xy(control), xy(point)))
        at[0] = xy(point)

    def cubic_to(c1, c2, point, _ctx) -> None:
        contours[-1].append(("C", at[0], xy(c1), xy(c2), xy(point)))
        at[0] = xy(point)

    face.glyph.outline.decompose(context=None, move_to=move_to, line_to=line_to, conic_to=conic_to, cubic_to=cubic_to)
    return contours


def _closed(contours: list[list[tuple]]) -> list[list[tuple]]:
    """FreeType leaves the closing line implicit. Add it when it has length."""
    out = []
    for contour in contours:
        spans = list(contour)
        if spans[-1][-1] != spans[0][1]:
            spans.append(("L", spans[-1][-1], spans[0][1]))
        out.append(spans)
    return out


def _doc(font_file: str = "carriertext.ttf"):
    doc = ezdxf.new("R2010")
    doc.header["$INSUNITS"] = 4
    doc.styles.add("GLYPH", font=font_file)
    return doc


def _rows(doc, fonts, **kwargs) -> list[dict]:
    rows = dxf_extract.extract_document(doc, fonts=fonts, file_id="text", **kwargs)
    for row in rows:
        VALIDATOR.validate(row)
    return rows


def _apply(point, link) -> tuple[float, float]:
    """Reflect, then uniform scale, then rotate, then translate."""
    x, y = point
    if link["reflect"]:
        x = -x
    x, y = x * link["scale"], y * link["scale"]
    angle = math.radians(link["rotate"])
    return (
        math.cos(angle) * x - math.sin(angle) * y + link["translate"][0],
        math.sin(angle) * x + math.cos(angle) * y + link["translate"][1],
    )


def _place(point, links) -> tuple[float, float]:
    for link in links:
        point = _apply(point, link)
    return point


def test_locked_e_matches_the_freetype_checked_fixture_spans() -> None:
    font = TTFont(TTF_PATH)
    got = text_glyphs.glyph_contours(font, "e")
    want = [[("Q",) + tuple((float(x), float(y)) for x, y in span) for span in contour] for contour in glyph_spans()]
    assert got == want


@pytest.mark.parametrize("char", ["e", "l"])
def test_truetype_spans_match_freetype(ttf: Path, char: str) -> None:
    font = TTFont(ttf)
    name = font.getBestCmap()[ord(char)]
    assert text_glyphs.glyph_contours(font, name) == _closed(_freetype_spans(ttf, char))


def test_cff_spans_are_cubics_and_match_freetype(otf: Path) -> None:
    font = TTFont(otf)
    got = text_glyphs.glyph_contours(font, "o")
    assert [span[0] for span in got[0]] == ["C", "C", "C", "L"]
    assert got == _closed(_freetype_spans(otf, "o"))


def test_cap_height_is_stated_or_declined(ttf: Path) -> None:
    assert text_glyphs.cap_height(TTFont(ttf)) == _CAP
    assert text_glyphs.cap_height(TTFont(TTF_PATH)) is None


def test_text_without_fonts_still_declines(ttf: Path) -> None:
    doc = _doc()
    doc.modelspace().add_text("el", height=3.5, dxfattribs={"style": "GLYPH"})
    (row,) = _rows(doc, None)
    assert (row["record"], row["id"]) == ("decline", "ID_TextEntity")


def test_dxf_text_is_a_compound_of_placed_glyph_outlines(ttf: Path) -> None:
    doc = _doc()
    doc.modelspace().add_text(
        "el e", height=3.5, rotation=30, dxfattribs={"style": "GLYPH", "insert": (10, 20), "layer": "LABELS"}
    )
    (row,) = _rows(doc, {"CarrierText.TTF": ttf})
    assert (row["record"], row["kind"]) == ("entity", "Compound")
    assert row["placement"] == {"links": [], "s": 1}
    assert row["provenance"]["format"] == "DXF"
    assert row["provenance"]["layer"] == "LABELS"
    assert row["units"]["linear"] == "millimeter"
    glyphs = row["params"]["members"]
    assert len(glyphs) == 3
    pens = [g["placement"]["links"][0]["translate"][0] for g in glyphs]
    assert pens == [0, _ADVANCE["e"], _ADVANCE["e"] + _ADVANCE["l"] + _ADVANCE["space"]]
    for glyph in glyphs:
        advance, text_link = glyph["placement"]["links"]
        assert (advance["scale"], advance["rotate"], advance["reflect"]) == (1, 0, False)
        assert text_link == {"translate": [10, 20], "rotate": 30, "scale": 3.5 / _CAP, "reflect": False}

    e, stem, _ = glyphs
    ring, outer, hole = e["params"]["members"]
    assert ring["kind"] == "Ring"
    assert ring["params"]["windingRule"] == "nonzero"
    assert ring["params"]["orientation"] == ["cw", "ccw"]
    assert [m["kind"] for m in outer["params"]["members"]] == ["Bezier"] * 4
    assert [m["kind"] for m in hole["params"]["members"]] == ["Bezier"] * 4
    quad = outer["params"]["members"][0]
    assert quad["params"]["degree"] == 2
    assert quad["params"]["knots"] == [0, 0, 0, 1, 1, 1]
    assert quad["placement"] == e["placement"]

    stem_ring, stem_contour = stem["params"]["members"]
    assert stem_ring["params"]["orientation"] == ["cw"]
    chords = stem_contour["params"]["members"]
    assert [m["kind"] for m in chords] == ["Chord"] * 4
    assert [m["params"]["start"] for m in chords] == [list(p) for p in _STEM]

    # The stem's top-left corner, placed through the chain, against the closed form.
    scale = 3.5 / _CAP
    local = ((_ADVANCE["e"] + 100) * scale, 700 * scale)
    turn = math.radians(30)
    want = (
        10 + math.cos(turn) * local[0] - math.sin(turn) * local[1],
        20 + math.sin(turn) * local[0] + math.cos(turn) * local[1],
    )
    assert _place((100, 700), stem["placement"]["links"]) == pytest.approx(want)
    assert math.dist(_place((100, 0), stem["placement"]["links"]), _place((100, 700), stem["placement"]["links"])) == pytest.approx(3.5)


def test_cff_text_is_cubic_beziers(otf: Path) -> None:
    doc = _doc("carriertext.otf")
    doc.modelspace().add_text("o", height=7, dxfattribs={"style": "GLYPH"})
    (row,) = _rows(doc, {"carriertext.otf": otf})
    ring, contour = row["params"]["members"][0]["params"]["members"]
    assert ring["params"]["orientation"] == ["cw"]
    kinds = [(m["kind"], m["params"].get("degree")) for m in contour["params"]["members"]]
    assert kinds == [("Bezier", 3)] * 3 + [("Chord", None)]
    assert contour["params"]["members"][0]["params"]["knots"] == [0, 0, 0, 0, 1, 1, 1, 1]


@pytest.mark.parametrize(
    ("flags", "reflect", "rotate", "sign"),
    [(2, True, 0, -1), (4, True, 180, -1), (6, False, 180, 1)],
)
def test_backward_and_upside_down_are_reflection_and_half_turn(ttf: Path, flags, reflect, rotate, sign) -> None:
    doc = _doc()
    doc.modelspace().add_text("l", height=7, dxfattribs={"style": "GLYPH", "text_generation_flag": flags})
    (row,) = _rows(doc, {"carriertext.ttf": ttf})
    glyph = row["params"]["members"][0]
    text_link = glyph["placement"]["links"][1]
    assert (text_link["reflect"], text_link["rotate"]) == (reflect, rotate)
    assert glyph["placement"]["s"] == sign
    x, y = _place((100, 700), glyph["placement"]["links"])
    assert (x, y) == pytest.approx((-1 if flags & 2 else 1, -7 if flags & 4 else 7))


def test_text_in_a_mirrored_insert_and_negative_extrusion_composes(ttf: Path) -> None:
    doc = _doc()
    block = doc.blocks.new("TAG")
    block.add_text("l", height=7, dxfattribs={"style": "GLYPH", "insert": (0, 0, 2)})
    msp = doc.modelspace()
    msp.add_blockref("TAG", (5, 6, 1), dxfattribs={"xscale": -2, "yscale": 2, "zscale": 2})
    msp.add_text("l", height=7, dxfattribs={"style": "GLYPH", "extrusion": (0, 0, -1)})
    placed, flipped = _rows(doc, {"carriertext.ttf": ttf})
    assert placed["provenance"]["blockPath"] == ["TAG"]
    assert placed["dimension"] == {"space": "2d+elevation", "elevation": 3}
    assert placed["placement"]["s"] == -1
    glyph = placed["params"]["members"][0]
    assert len(glyph["placement"]["links"]) == 3
    assert glyph["placement"]["s"] == -1
    assert _place((100, 700), glyph["placement"]["links"]) == pytest.approx((5 - 2, 6 + 14))
    assert flipped["placement"]["s"] == -1
    assert flipped["params"]["members"][0]["placement"]["links"][-1]["reflect"] is True


@pytest.mark.parametrize(
    ("attribs", "text", "decline", "reason"),
    [
        ({"width": 0.8}, "l", "ID_NotSimilarityPlacement", "width factor"),
        ({"oblique": 15}, "l", "ID_NotSimilarityPlacement", "oblique"),
        ({"halign": 5, "align_point": (5, 0)}, "ll", "ID_NotSimilarityPlacement", "fit text"),
        ({"halign": 3, "align_point": (0, 0)}, "ll", "ID_DegenerateEntity", "no length"),
        ({}, "lx", "ID_TextEntity", "U+0078"),
        ({}, "  ", "ID_TextEntity", "no inked glyph"),
    ],
)
def test_named_text_declines(ttf: Path, attribs, text, decline, reason) -> None:
    doc = _doc()
    attribs = {"style": "GLYPH", "height": 7, **attribs}
    doc.modelspace().add_text(text, dxfattribs=attribs)
    (row,) = _rows(doc, {"carriertext.ttf": ttf})
    assert (row["record"], row["id"]) == ("decline", decline)
    assert reason in row["reason"]


# "ll": stems at pen 0 and 300, ink from x = 100 to x = 500. hhea descent is -100.
@pytest.mark.parametrize(
    ("halign", "valign", "anchor"),
    [
        (1, 0, (300, 0)),
        (2, 0, (500, 0)),
        (0, 3, (0, _CAP)),
        (0, 2, (0, _CAP / 2)),
        (0, 1, (0, -100)),
        (1, 3, (300, _CAP)),
        (2, 1, (500, -100)),
        (4, 0, (300, (_CAP - 100) / 2)),
        (4, 3, (300, (_CAP - 100) / 2)),
    ],
)
def test_alignment_puts_the_anchor_on_the_align_point(ttf: Path, halign, valign, anchor) -> None:
    doc = _doc()
    attribs = {"style": "GLYPH", "insert": (-99, -99), "align_point": (10, 20), "halign": halign, "valign": valign}
    doc.modelspace().add_text("ll", height=7, rotation=30, dxfattribs=attribs)
    (row,) = _rows(doc, {"carriertext.ttf": ttf})
    first, second = row["params"]["members"]
    assert first["placement"]["links"][1]["scale"] == pytest.approx(7 / _CAP)
    assert _place(anchor, first["placement"]["links"]) == pytest.approx((10, 20))
    assert _place((anchor[0] - 300, anchor[1]), second["placement"]["links"]) == pytest.approx((10, 20))


def test_right_alignment_uses_the_curve_extent_not_the_control_points(otf: Path) -> None:
    # The right side of o runs (600,700) (700,500) (700,200) (600,0): it peaks at x = 675.
    assert text_glyphs._axis_extent([600, 700, 700, 600]) == (600, 675)
    assert text_glyphs._axis_extent([0, 100, 0]) == (0, 50)
    doc = _doc("carriertext.otf")
    doc.modelspace().add_text("o", height=7, dxfattribs={"style": "GLYPH", "halign": 2, "align_point": (10, 20)})
    (row,) = _rows(doc, {"carriertext.otf": otf})
    glyph = row["params"]["members"][0]
    assert _place((675, 0), glyph["placement"]["links"]) == pytest.approx((10, 20))


def test_aligned_text_spans_two_baseline_points(ttf: Path) -> None:
    doc = _doc()
    attribs = {"style": "GLYPH", "insert": (10, 20), "align_point": (10, 60), "halign": 3, "valign": 2}
    doc.modelspace().add_text("ll", height=999, rotation=45, dxfattribs=attribs)
    (row,) = _rows(doc, {"carriertext.ttf": ttf})
    first, second = row["params"]["members"]
    text_link = first["placement"]["links"][1]
    assert text_link["rotate"] == pytest.approx(90)
    assert text_link["scale"] == pytest.approx(40 / 400)
    assert _place((100, 0), first["placement"]["links"]) == pytest.approx((10, 20))
    assert _place((200, 0), second["placement"]["links"]) == pytest.approx((10, 60))


def test_fit_text_is_kept_when_the_ink_already_fits(ttf: Path) -> None:
    doc = _doc()
    # Height 7 gives scale 0.01, and the ink is 400 units wide.
    attribs = {"style": "GLYPH", "insert": (10, 20), "align_point": (14, 20), "halign": 5}
    doc.modelspace().add_text("ll", height=7, dxfattribs=attribs)
    (row,) = _rows(doc, {"carriertext.ttf": ttf})
    second = row["params"]["members"][1]
    assert _place((200, 0), second["placement"]["links"]) == pytest.approx((14, 20))


def test_stroke_font_missing_font_and_missing_cap_height_decline(ttf: Path) -> None:
    doc = _doc("txt.shx")
    doc.styles.add("OTHER", font="other.ttf")
    doc.styles.add("NOCAP", font="e.ttf")
    msp = doc.modelspace()
    msp.add_text("l", height=7, dxfattribs={"style": "GLYPH"})
    msp.add_text("l", height=7, dxfattribs={"style": "OTHER"})
    msp.add_text("e", height=7, dxfattribs={"style": "NOCAP"})
    rows = _rows(doc, {"carriertext.ttf": ttf, "e.ttf": TTF_PATH})
    assert [row["id"] for row in rows] == ["ID_TextEntity"] * 3
    assert "not an outline font" in rows[0]["reason"]
    assert "no font file given" in rows[1]["reason"]
    assert "cap height" in rows[2]["reason"]


def test_segment_count_on_text_keeps_the_compound_rule(ttf: Path) -> None:
    doc = _doc()
    doc.modelspace().add_text("l", height=7, dxfattribs={"style": "GLYPH"})
    (row,) = _rows(doc, {"carriertext.ttf": ttf}, tolerance={"kind": "segmentCount", "n": 8})
    assert row["id"] == "ID_ToleranceKindUnsupported"
    (row,) = _rows(doc, {"carriertext.ttf": ttf}, tolerance={"kind": "sagitta", "d": 0.01})
    assert row["params"]["members"][0]["tolerance"] == {"kind": "sagitta", "d": 0.01}


def _saved(tmp_path: Path, name: str) -> Path:
    doc = _doc()
    doc.modelspace().add_text("el", height=3.5, rotation=30, dxfattribs={"style": "GLYPH", "insert": (10, 20)})
    path = tmp_path / name
    doc.saveas(path)
    return path


def test_dwg_goes_through_the_converter_and_keeps_the_entity_model(tmp_path: Path, ttf: Path, monkeypatch) -> None:
    from ezdxf.addons import odafc

    dxf = _saved(tmp_path, "label.dxf")
    dwg = tmp_path / "label.dwg"
    dwg.write_bytes(b"AC1024 stand-in; the converter is the reader")
    seen: list[str] = []

    def readfile(filename, *args, **kwargs):
        seen.append(str(filename))
        return ezdxf.readfile(dxf)

    monkeypatch.setattr(odafc, "readfile", readfile)
    fonts = {"carriertext.ttf": ttf}
    (from_dwg,) = dxf_extract.extract_path(dwg, fonts=fonts, file_id="label")
    (from_dxf,) = dxf_extract.extract_path(dxf, fonts=fonts, file_id="label")
    VALIDATOR.validate(from_dwg)
    assert seen == [str(dwg)]
    assert json.dumps(from_dwg).count('"format": "DWG"') == json.dumps(from_dxf).count('"format": "DXF"') > 0
    assert json.loads(json.dumps(from_dwg).replace('"format": "DWG"', '"format": "DXF"')) == from_dxf


def test_cli_takes_font_files(tmp_path: Path, ttf: Path, capsys) -> None:
    dxf = _saved(tmp_path, "label.dxf")
    assert dxf_extract.main([str(dxf), "--font", f"carriertext.ttf={ttf}"]) == 0
    (line,) = capsys.readouterr().out.splitlines()
    assert json.loads(line)["kind"] == "Compound"
    assert dxf_extract.main([str(dxf), "--font", "carriertext.ttf=/no/such/font.ttf"]) == 2


_DGN_CTX = {
    "links": [],
    "units": {"linear": "meter", "angle": "degree", "angdir": 0, "angbase": 0.0},
    "tolerance": {"kind": "sourceDefault"},
    "dimension": {"space": "2d"},
    "provenance": {"format": "DGN", "version": "V8", "handle": "4711", "layer": "12", "blockPath": [], "fileId": "label"},
}


def test_dgn_text_element_yields_the_same_outlines_as_dxf(tmp_path: Path, ttf: Path) -> None:
    element = {"type": 17, "text": "el", "origin": [10, 20], "rotation": 30, "height": 3.5, "width": 3.5, "font": 41}
    run = text_glyphs.dgn_text_run(element, {41: ttf})
    assert isinstance(run, text_glyphs.TextRun)
    row = text_glyphs.run_record(run, **_DGN_CTX)
    VALIDATOR.validate(row)
    assert row["provenance"]["format"] == "DGN"
    (from_dxf,) = dxf_extract.extract_path(_saved(tmp_path, "label.dxf"), fonts={"carriertext.ttf": ttf})

    def shape(entity: dict):
        members = entity["params"].get("members")
        if members is not None:
            return (entity["kind"], entity["placement"], [shape(m) for m in members])
        return (entity["kind"], entity["placement"], entity["params"])

    assert shape(row) == shape(from_dxf)


def test_dgn_named_declines(ttf: Path) -> None:
    base = {"type": 17, "text": "l", "origin": [0, 0], "height": 2.0, "width": 2.0, "font": 41}
    squeezed = text_glyphs.dgn_text_run({**base, "width": 1.5}, {41: ttf})
    assert text_glyphs.run_record(squeezed, **_DGN_CTX)[0] == "ID_NotSimilarityPlacement"
    flat = text_glyphs.dgn_text_run({**base, "height": 0.0, "width": 0.0}, {41: ttf})
    assert text_glyphs.run_record(flat, **_DGN_CTX)[0] == "ID_DegenerateEntity"
    odd = text_glyphs.TextRun(text="l", font=ttf, height=2.0, insert=(0.0, 0.0), halign="diagonal")
    assert text_glyphs.run_record(odd, **_DGN_CTX)[0] == "ID_TextEntity"
    assert text_glyphs.dgn_text_run(base, {})[0] == "ID_TextEntity"
    assert text_glyphs.dgn_text_run({**base, "justification": 7}, {41: ttf})[0] == "ID_TextEntity"
    assert text_glyphs.dgn_text_run({**base, "type": 16}, {41: ttf})[0] == "ID_TextEntity"


_PITCH = _CAP * 5 / 3


def _mtext_rows(ttf: Path, content: str, **attribs) -> list[dict]:
    doc = _doc()
    attribs = {"style": "GLYPH", "char_height": 7, "insert": (10, 20, 4), **attribs}
    doc.modelspace().add_mtext(content, dxfattribs=attribs)
    return _rows(doc, {"carriertext.ttf": ttf})


def test_mtext_lines_step_down_by_five_thirds_of_the_cap_height(ttf: Path) -> None:
    (row,) = _mtext_rows(ttf, r"le\P\Pl\~l", rotation=90)
    assert row["kind"] == "Compound"
    assert row["dimension"] == {"space": "2d+elevation", "elevation": 4}
    glyphs = row["params"]["members"]
    pens = [v for g in glyphs for v in g["placement"]["links"][0]["translate"]]
    assert pens == pytest.approx(
        [0, -_CAP, _ADVANCE["l"], -_CAP, 0, -_CAP - 2 * _PITCH, _ADVANCE["l"] + _ADVANCE["space"], -_CAP - 2 * _PITCH]
    )
    text_link = glyphs[0]["placement"]["links"][1]
    assert text_link == {"translate": [10, 20], "rotate": 90, "scale": 7 / _CAP, "reflect": False}
    # The cap top of the first stem is the top-left attachment point; rotated 90 degrees, x runs up.
    assert _place((0, _CAP), glyphs[0]["placement"]["links"]) == pytest.approx((10, 20))
    assert _place((100, 0), glyphs[0]["placement"]["links"]) == pytest.approx((10 + 7, 20 + 1))


@pytest.mark.parametrize(
    ("attachment", "corner"),
    [
        (1, (0, 0)),
        (2, (0.5, 0)),
        (3, (1, 0)),
        (4, (0, 0.5)),
        (5, (0.5, 0.5)),
        (6, (1, 0.5)),
        (7, (0, 1)),
        (8, (0.5, 1)),
        (9, (1, 1)),
    ],
)
def test_mtext_attachment_point_is_a_box_point(ttf: Path, attachment, corner) -> None:
    # Two lines: "lll" is 900 wide and "l" is 300 wide. The box is cap + pitch deep.
    (row,) = _mtext_rows(ttf, r"lll\Pl", attachment_point=attachment)
    first, last = row["params"]["members"][0], row["params"]["members"][-1]
    depth = _CAP + _PITCH
    # Line-local points that must land on the insert point, per line width.
    top_line = (corner[0] * 900, _CAP - corner[1] * depth)
    bottom_line = (corner[0] * 300, _CAP + _PITCH - corner[1] * depth)
    assert _place(top_line, first["placement"]["links"]) == pytest.approx((10, 20))
    assert _place(bottom_line, last["placement"]["links"]) == pytest.approx((10, 20))


def test_mtext_text_direction_wins_over_rotation(ttf: Path) -> None:
    (row,) = _mtext_rows(ttf, "l", rotation=10, text_direction=(0, -2, 0))
    assert row["params"]["members"][0]["placement"]["links"][1]["rotate"] == pytest.approx(-90)
    (tilted,) = _mtext_rows(ttf, "l", text_direction=(1, 0, 1))
    assert tilted["id"] == "ID_TiltedPlacement"


@pytest.mark.parametrize(
    ("content", "attribs", "decline", "reason"),
    [
        (r"{\fArial|b1;l}", {}, "ID_TextEntity", "inline formatting"),
        (r"\H2x;l", {}, "ID_TextEntity", "inline formatting"),
        ("lll", {"width": 0.05}, "ID_TextEntity", "would wrap"),
        ("l", {"flow_direction": 3}, "ID_TextEntity", "top-to-bottom"),
        ("l^Il", {}, "ID_TextEntity", "U+0009"),
        (r"\P ", {}, "ID_TextEntity", "no inked glyph"),
    ],
)
def test_named_mtext_declines(ttf: Path, content, attribs, decline, reason) -> None:
    (row,) = _mtext_rows(ttf, content, **attribs)
    assert (row["record"], row["id"]) == ("decline", decline)
    assert reason in row["reason"]


def test_mtext_fits_a_wide_enough_column_and_scales_line_spacing(ttf: Path) -> None:
    # "lll" is 900 units, 9 drawing units at height 7.
    (row,) = _mtext_rows(ttf, r"lll\Pl", width=9.0, line_spacing_factor=1.5)
    last = row["params"]["members"][-1]
    assert last["placement"]["links"][0]["translate"] == pytest.approx([0, -_CAP - 1.5 * _PITCH])


def test_mtext_style_stretch_is_not_a_similarity(ttf: Path) -> None:
    doc = _doc()
    doc.styles.get("GLYPH").dxf.width = 0.8
    doc.modelspace().add_mtext("l", dxfattribs={"style": "GLYPH", "char_height": 7})
    (row,) = _rows(doc, {"carriertext.ttf": ttf})
    assert row["id"] == "ID_NotSimilarityPlacement"


def test_mtext_without_fonts_still_declines_and_linearizes_with_them(ttf: Path) -> None:
    import glyph_linearize

    doc = _doc()
    doc.modelspace().add_mtext(r"el\Ple", dxfattribs={"style": "GLYPH", "char_height": 7})
    (declined,) = _rows(doc, None)
    assert declined["id"] == "ID_TextEntity"
    (row,) = _rows(doc, {"carriertext.ttf": ttf})
    out = glyph_linearize.linearize_row(row, hausdorff=0.01)
    assert out["polygons"] == 4
