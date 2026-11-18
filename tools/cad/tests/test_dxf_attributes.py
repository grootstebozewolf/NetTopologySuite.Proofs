"""Block attributes: ATTRIBs attached to an INSERT, and ATTDEFs inside the block."""

from __future__ import annotations

from pathlib import Path

import ezdxf
import pytest

import dxf_extract
from test_text_glyphs import _CAP, VALIDATOR, _place, ttf  # noqa: F401


def _doc():
    doc = ezdxf.new("R2018")
    doc.styles.add("GLYPH", font="carriertext.ttf")
    block = doc.blocks.new("TAG")
    block.add_line((0, 0), (1, 0))
    block.add_attdef("NAME", (0, 1), dxfattribs={"height": 7, "style": "GLYPH"})
    block.add_attdef("CONST", (0, 3), text="l", dxfattribs={"height": 7, "style": "GLYPH", "flags": 2})
    return doc


def _rows(doc, ttf: Path) -> list[dict]:
    rows = dxf_extract.extract_document(doc, fonts={"carriertext.ttf": ttf}, file_id="attrib")
    for row in rows:
        VALIDATOR.validate(row)
    return rows


def test_attached_attribs_are_placed_in_the_inserts_space_not_the_blocks(ttf: Path) -> None:
    doc = _doc()
    insert = doc.modelspace().add_blockref("TAG", (10, 20), dxfattribs={"rotation": 90, "xscale": 2, "yscale": 2})
    attrib = insert.add_attrib("NAME", "l", (3, 4), dxfattribs={"height": 7, "style": "GLYPH", "rotation": 30})
    line, template, const, name = _rows(doc, ttf)
    assert line["kind"] == "Chord" and line["provenance"]["blockPath"] == ["TAG"]
    assert (template["id"], template["reason"]) == (
        "ID_TextEntity",
        "ATTDEF is an attribute template; the INSERT's ATTRIB is drawn",
    )
    # The constant ATTDEF is block geometry: placed through the INSERT (rotated 90, scaled 2).
    stem = const["params"]["members"][0]
    # Stem foot: block point (1, 3); scaled by 2 and turned 90 degrees, (-6, 2); plus (10, 20).
    assert _place((100, 0), stem["placement"]["links"]) == pytest.approx((4, 22))
    # The ATTRIB is already in the INSERT's space: only its own text link places it.
    assert name["provenance"]["blockPath"] == ["TAG"]
    links = name["params"]["members"][0]["placement"]["links"]
    assert len(links) == 2
    assert links[1]["translate"] == pytest.approx([3, 4]) and links[1]["rotate"] == pytest.approx(30)
    assert (attrib.dxf.insert.x, attrib.dxf.insert.y) == pytest.approx((3, 4))


def test_attribs_of_a_nested_insert_take_only_the_outer_links(ttf: Path) -> None:
    doc = _doc()
    outer = doc.blocks.new("OUTER")
    inner = outer.add_blockref("TAG", (0, 0))
    inner.add_attrib("NAME", "l", (1, 1), dxfattribs={"height": 7, "style": "GLYPH"})
    doc.modelspace().add_blockref("OUTER", (100, 0), dxfattribs={"xscale": -1})
    rows = _rows(doc, ttf)
    name = rows[-1]
    assert name["provenance"]["blockPath"] == ["OUTER", "TAG"]
    links = name["params"]["members"][0]["placement"]["links"]
    # Pen, text link, then the mirrored OUTER insert; not the TAG insert.
    assert len(links) == 3 and links[2]["reflect"] is True
    assert name["placement"]["s"] == -1
    assert _place((0, 0), links) == pytest.approx((100 - 1, 1))


def test_invisible_attrib_declines_and_multiline_attrib_is_mtext(ttf: Path) -> None:
    doc = _doc()
    insert = doc.modelspace().add_blockref("TAG", (0, 0))
    insert.add_attrib("NAME", "l", (0, 0), dxfattribs={"height": 7, "style": "GLYPH", "flags": 1})
    multi = insert.add_attrib("NAME", "", (0, 0), dxfattribs={"height": 7, "style": "GLYPH"})
    mtext = doc.modelspace().add_mtext(r"l\Pl", dxfattribs={"char_height": 7, "style": "GLYPH", "insert": (5, 5)})
    multi.embed_mtext(mtext)
    doc.modelspace().delete_entity(mtext)
    *_block, hidden, lines = _rows(doc, ttf)
    assert (hidden["id"], hidden["reason"]) == ("ID_TextEntity", "invisible ATTRIB is not drawn")
    assert lines["kind"] == "Compound"
    pens = [g["placement"]["links"][0]["translate"] for g in lines["params"]["members"]]
    assert [round(p[1], 6) for p in pens] == pytest.approx([-_CAP, -_CAP - _CAP * 5 / 3])


def test_without_fonts_attribs_are_still_counted(ttf: Path) -> None:
    doc = _doc()
    insert = doc.modelspace().add_blockref("TAG", (0, 0))
    insert.add_attrib("NAME", "l", (0, 0))
    rows = dxf_extract.extract_document(doc, file_id="attrib")
    # LINE, two ATTDEFs and the ATTRIB: nothing is dropped.
    assert [r.get("kind", r.get("id")) for r in rows] == ["Chord", "ID_TextEntity", "ID_TextEntity", "ID_TextEntity"]
