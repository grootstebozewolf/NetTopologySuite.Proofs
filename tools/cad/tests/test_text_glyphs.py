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
        ({"oblique": 89}, "l", "ID_DegenerateEntity", "out of range"),
        ({"halign": 5, "align_point": (0, 0)}, "ll", "ID_DegenerateEntity", "no length"),
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
    assert "no font file given for txt.shx" in rows[0]["reason"]
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
    squeezed = text_glyphs.run_record(text_glyphs.dgn_text_run({**base, "width": 1.5}, {41: ttf}), **_DGN_CTX)
    stem = squeezed["params"]["members"][0]["params"]["members"][1]["params"]["members"]
    assert [m["params"]["start"] for m in stem] == [[75, 0], [75, 700], [150, 700], [150, 0]]
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
        (r"{\fArial|b1;l}", {}, "ID_TextEntity", "no font file given for arial|b1|i0"),
        (r"{\fArial;l}", {}, "ID_TextEntity", "no font file given for arial"),
        (r"\Sl/l;", {}, "ID_TextEntity", "no underline thickness for a fraction bar"),
        (r"\Q10;\Sl^ l;", {}, "ID_TextEntity", "stacked text with an oblique angle"),
        (r"\Ll\l", {}, "ID_TextEntity", "font states no underline position"),
        (r"\Ol\o", {}, "ID_TextEntity", "overline"),
        (r"\T1.5;l", {}, "ID_TextEntity", "tracking"),
        (r"\pxqd;l", {}, "ID_TextEntity", "distributed"),
        (r"l\U+00B0", {}, "ID_TextEntity", "U+00B0"),
        ("l", {"flow_direction": 3}, "ID_TextEntity", "top-to-bottom"),
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


def test_mtext_takes_the_style_width_and_inline_width_and_oblique(ttf: Path) -> None:
    doc = _doc()
    doc.styles.get("GLYPH").dxf.width = 0.8
    doc.modelspace().add_mtext(r"ll{\W2;l}{\Q45;l}", dxfattribs={"style": "GLYPH", "char_height": 7})
    (row,) = _rows(doc, {"carriertext.ttf": ttf})
    # Advances 240, 240, then 600 at width 2; the braces end that, so the leaning one is 0.8 wide again.
    assert [pen[0] for pen in _pens(row)] == pytest.approx([0, 240, 480, 1080])
    starts = lambda glyph: [m["params"]["start"] for m in glyph["params"]["members"][1]["params"]["members"]]
    narrow, _, wide, leaning = row["params"]["members"]
    assert starts(narrow) == [[80, 0], [80, 700], [160, 700], [160, 0]]
    assert starts(wide) == [[200, 0], [200, 700], [400, 700], [400, 0]]
    flat = [v for point in starts(leaning) for v in point]
    assert flat == pytest.approx([80, 0, 0.8 * (100 + 700), 700, 0.8 * (200 + 700), 700, 160, 0])
    assert all(g["placement"]["links"][1]["scale"] == pytest.approx(7 / _CAP) for g in row["params"]["members"])


def test_mtext_without_fonts_still_declines_and_linearizes_with_them(ttf: Path) -> None:
    import glyph_linearize

    doc = _doc()
    doc.modelspace().add_mtext(r"el\Ple", dxfattribs={"style": "GLYPH", "char_height": 7})
    (declined,) = _rows(doc, None)
    assert declined["id"] == "ID_TextEntity"
    (row,) = _rows(doc, {"carriertext.ttf": ttf})
    out = glyph_linearize.linearize_row(row, hausdorff=0.01)
    assert out["polygons"] == 4


def test_two_span_and_one_span_contours_get_an_on_curve_skeleton() -> None:
    ctx = {key: _DGN_CTX[key] for key in ("units", "tolerance", "dimension", "provenance")}
    # A lens: two quadratics between the same two points. Its end points alone enclose nothing.
    lens = [("Q", (0.0, 0.0), (50.0, 80.0), (100.0, 0.0)), ("Q", (100.0, 0.0), (50.0, -80.0), (0.0, 0.0))]
    member = text_glyphs._glyph_member([lens], [], ctx)
    VALIDATOR.validate(member)
    ring, contour = member["params"]["members"]
    assert ring["params"]["orientation"] == ["cw"]
    assert [c["start"] for c in ring["params"]["contours"][0]] == [[0, 0], [50, 40], [100, 0], [50, -40]]
    assert len(contour["params"]["members"]) == 2
    # A teardrop: one cubic that starts and ends at the same point.
    drop = [("C", (0.0, 0.0), (120.0, 120.0), (-120.0, 120.0), (0.0, 0.0))]
    member = text_glyphs._glyph_member([drop], [], ctx)
    VALIDATOR.validate(member)
    assert member["params"]["members"][0]["params"]["orientation"] == ["ccw"]
    assert len(member["params"]["members"][0]["params"]["contours"][0]) == 4
    flat = [("L", (0.0, 0.0), (10.0, 0.0)), ("L", (10.0, 0.0), (0.0, 0.0))]
    assert text_glyphs._glyph_member([flat], [], ctx)[0] == "ID_DegenerateEntity"
    # Next to a real contour, the retraced line is left out: it fills nothing.
    member = text_glyphs._glyph_member([lens, flat], [], ctx)
    VALIDATOR.validate(member)
    assert len(member["params"]["members"]) == 2
    assert member["params"]["members"][0]["params"]["orientation"] == ["cw"]


def test_style_font_without_an_extension_is_a_shape_font(ttf: Path) -> None:
    assert text_glyphs.resolve_font("txt", {"TXT.SHX": ttf}) == ttf
    assert "txt.shx" in text_glyphs.resolve_font("txt", {})[1]


def _pens(row: dict) -> list[list[float]]:
    return [glyph["placement"]["links"][0]["translate"] for glyph in row["params"]["members"]]


def test_mtext_wraps_at_the_last_space_that_fits(ttf: Path) -> None:
    # At height 7 one drawing unit is 100 font units. "ll" is 600 wide and a space 250.
    (row,) = _mtext_rows(ttf, "ll ll  ll", width=15.0)
    flat = [v for pen in _pens(row) for v in pen]
    assert flat == pytest.approx([0, -_CAP, 300, -_CAP, 850, -_CAP, 1150, -_CAP, 0, -_CAP - _PITCH, 300, -_CAP - _PITCH])
    # Top right: the box is the column, and each line ends at its right edge.
    (row,) = _mtext_rows(ttf, "ll ll  ll", width=15.0, attachment_point=3)
    xs = [pen[0] for pen in _pens(row)]
    assert xs == pytest.approx([-1450, -1150, -600, -300, -600, -300])
    # Without a width nothing wraps.
    (row,) = _mtext_rows(ttf, "ll ll  ll")
    assert {pen[1] for pen in _pens(row)} == {-_CAP}


def test_mtext_long_word_overflows_and_nbsp_does_not_break(ttf: Path) -> None:
    (row,) = _mtext_rows(ttf, "lll", width=0.05)
    assert {pen[1] for pen in _pens(row)} == {-_CAP}
    (row,) = _mtext_rows(ttf, r"ll\~ll ll", width=12.0)
    ys = [pen[1] for pen in _pens(row)]
    assert ys == pytest.approx([-_CAP] * 4 + [-_CAP - _PITCH] * 2)


def test_mtext_height_change_scales_the_word_and_its_line(ttf: Path) -> None:
    (row,) = _mtext_rows(ttf, r"l{\H2x;l}l\Pl")
    small, big, after, below = row["params"]["members"]
    assert [g["placement"]["links"][0]["scale"] for g in (small, big, after, below)] == [1, 2, 1, 1]
    # The first line is two caps tall; the doubled l advances by 600.
    flat = [v for pen in _pens(row) for v in pen]
    assert flat == pytest.approx([0, -2 * _CAP, 300, -2 * _CAP, 900, -2 * _CAP, 0, -2 * _PITCH - _CAP])
    top = _place((100, 700), big["placement"]["links"])
    foot = _place((100, 0), big["placement"]["links"])
    assert math.dist(top, foot) == pytest.approx(14)
    assert top[1] == pytest.approx(20)


def test_mtext_paragraph_alignment_and_colour(ttf: Path) -> None:
    (row,) = _mtext_rows(ttf, r"\pxqc;{\C1;l}\P\pxqr;l\P\pxql;l", width=10.0)
    assert [pen[0] for pen in _pens(row)] == pytest.approx([350, 700, 0])
    # A paragraph alignment overrides the attachment's, inside the same box.
    (row,) = _mtext_rows(ttf, r"\pxql;l", width=10.0, attachment_point=3)
    assert _pens(row)[0][0] == pytest.approx(-1000)


def test_mtext_font_switch_takes_its_own_file_and_matches_cap_height(ttf: Path, otf: Path, tmp_path: Path) -> None:
    from test_stroke_glyphs import _SHP

    shp = tmp_path / "carrierstroke.shp"
    shp.write_bytes(_SHP)
    fonts = {"carriertext.ttf": ttf, "Other": otf, "other|b1|i0": otf, "CarrierStroke.shp": shp}
    doc = _doc()
    msp = doc.modelspace()
    for content in (r"l{\fOther|b0|i0|c0|p34;o}l", r"l{\fOther|b1|i0;o}l", r"l{\fCarrierStroke.shp;L L}l", r"{\fOther|b0|i1;o}"):
        msp.add_mtext(content, dxfattribs={"style": "GLYPH", "char_height": 7})
    regular, bold, stroke, italic = _rows(doc, fonts)
    for row in (regular, bold):
        assert [pen[0] for pen in _pens(row)] == pytest.approx([0, 300, 1000])
        cubic = row["params"]["members"][1]["params"]["members"][1]["params"]["members"][0]
        assert cubic["params"]["degree"] == 3
    # The stroke font is 21 units tall, so it is scaled by 700 / 21; L advances 18, its space 10.
    fit = _CAP / 21
    ell = stroke["params"]["members"][1]
    assert ell["params"]["members"][0]["kind"] == "BulgePolyline"
    assert ell["placement"]["links"][0]["scale"] == pytest.approx(fit)
    assert [pen[0] for pen in _pens(stroke)] == pytest.approx([0, 300, 300 + 28 * fit, 300 + 46 * fit])
    assert math.dist(_place((0, 21), ell["placement"]["links"]), _place((0, 0), ell["placement"]["links"])) == pytest.approx(7)
    assert (italic["id"], italic["reason"]) == ("ID_TextEntity", "no font file given for other|b0|i1")


def test_width_factor_and_oblique_shape_the_glyph_not_the_placement(ttf: Path) -> None:
    import glyph_linearize
    import shapely

    def row(**attribs) -> dict:
        doc = _doc()
        doc.modelspace().add_text("el", height=7, dxfattribs={"style": "GLYPH", **attribs})
        (out,) = _rows(doc, {"carriertext.ttf": ttf})
        return out

    plain, wide, leaning = row(), row(width=1.6), row(oblique=20)
    lean = math.tan(math.radians(20))
    for shaped in (wide, leaning):
        assert shaped["placement"] == plain["placement"]
        assert shaped["params"]["members"][0]["placement"]["links"][1] == plain["params"]["members"][0]["placement"]["links"][1]
    # The pen advance takes the width factor; the lean leaves it alone.
    assert [pen[0] for pen in _pens(wide)] == pytest.approx([0, 1.6 * _ADVANCE["e"]])
    assert [pen[0] for pen in _pens(leaning)] == [0, _ADVANCE["e"]]
    # Every Bezier control point is mapped, so the curve is the mapped curve.
    quad = lambda r: r["params"]["members"][0]["params"]["members"][1]["params"]["members"][0]["params"]["controlPoints"]
    for (x, y), (wx, wy), (lx, ly) in zip(quad(plain), quad(wide), quad(leaning)):
        assert (wx, wy) == pytest.approx((1.6 * x, y))
        assert (lx, ly) == pytest.approx((x + y * lean, y))
    # A stretch scales the filled area by the width factor; a lean keeps it.
    area = lambda r: shapely.from_wkt(glyph_linearize.linearize_row(r, hausdorff=1e-4)["wkt"]).area
    assert area(wide) == pytest.approx(1.6 * area(plain), rel=1e-4)
    assert area(leaning) == pytest.approx(area(plain), rel=1e-4)
    assert leaning["params"]["members"][0]["params"]["members"][0]["params"]["orientation"] == ["cw", "ccw"]


def test_fit_text_stretches_the_ink_between_its_two_points(ttf: Path) -> None:
    doc = _doc()
    # "ll" has ink from 100 to 500. At height 7 that is 4 units; the span is 10 units, straight up.
    attribs = {"style": "GLYPH", "insert": (10, 20), "align_point": (10, 30), "halign": 5, "width": 99}
    doc.modelspace().add_text("ll", height=7, dxfattribs=attribs)
    (row,) = _rows(doc, {"carriertext.ttf": ttf})
    first, second = row["params"]["members"]
    link = first["placement"]["links"][1]
    assert (link["scale"], link["rotate"]) == pytest.approx((7 / _CAP, 90))
    stem = [m["params"]["start"] for m in first["params"]["members"][1]["params"]["members"]]
    assert stem == [[250, 0], [250, 700], [500, 700], [500, 0]]
    assert _place((250, 0), first["placement"]["links"]) == pytest.approx((10, 20))
    assert _place((500, 0), second["placement"]["links"]) == pytest.approx((10, 30))
    assert _place((250, 700), first["placement"]["links"]) == pytest.approx((10 - 7, 20))
