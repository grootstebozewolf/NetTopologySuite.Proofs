"""MTEXT columns: flow between columns as in ezdxf's layout engine."""

from __future__ import annotations

import random
from pathlib import Path

import pytest
from ezdxf.render.abstract_mtext_renderer import column_heights
from ezdxf.tools import text_layout as tl

from test_text_glyphs import _CAP, _doc, _pens, _rows, ttf  # noqa: F401

# At char height 7 one drawing unit is 100 font units. "l" advances 300, a space 250.
_L, _SPACE, _PITCH = 300, 250, _CAP * 5 / 3


def _static(font: Path, parts: list[str], width: float, gutter: float, height: float, **attribs) -> dict:
    doc = _doc()
    doc.modelspace().add_mtext_static_columns(
        parts, width=width, gutter_width=gutter, height=height,
        dxfattribs={"style": "GLYPH", "char_height": 7, "insert": (0, 0), **attribs},
    )
    (row,) = _rows(doc, {"carriertext.ttf": font})
    return row


def _xy(row: dict) -> list[tuple[float, float]]:
    return [(round(pen[0], 6), round(pen[1], 6)) for pen in _pens(row)]


def _flat(points) -> list[float]:
    return [v for point in points for v in point]


def test_lines_fill_a_column_then_start_the_next(ttf: Path) -> None:
    # Height 20 holds two lines (bottoms at 7 and 7 + 11.67); the third starts column two.
    row = _static(ttf, [r"l\Pl\Pl\Pl"], width=10, gutter=2, height=20)
    assert _flat(_xy(row)) == pytest.approx(
        _flat([(0, -_CAP), (0, -_CAP - _PITCH), (1200, -_CAP), (1200, -_CAP - _PITCH)])
    )


def test_column_break_and_overflow_columns(ttf: Path) -> None:
    # Two static columns; the break sends "l" to column two; the overflow opens a third.
    row = _static(ttf, ["l", r"l\Pl\Pl"], width=10, gutter=2, height=20)
    assert [x for x, _y in _xy(row)] == pytest.approx([0, 1200, 1200, 2400])


def test_column_break_without_columns_opens_one_as_wide_as_the_text(ttf: Path) -> None:
    doc = _doc()
    doc.modelspace().add_mtext(r"l\Nl", dxfattribs={"style": "GLYPH", "char_height": 7, "width": 10.0})
    (row,) = _rows(doc, {"carriertext.ttf": ttf})
    assert _flat(_xy(row)) == pytest.approx([0, -_CAP, 1000, -_CAP])
    doc = _doc()
    doc.modelspace().add_mtext(r"l\Nl", dxfattribs={"style": "GLYPH", "char_height": 7})
    (row,) = _rows(doc, {"carriertext.ttf": ttf})
    assert (row["id"], row["reason"]) == ("ID_TextEntity", "MTEXT column break without a width")


def test_attachment_uses_the_box_of_all_columns(ttf: Path) -> None:
    # Bottom right: the box is 3 columns (10 + 2 + 10 + 2 + 10 = 34 units) by the column height 12,
    # and each line is set right in its own column.
    row = _static(ttf, ["l", "l", "l"], width=10, gutter=2, height=12, attachment_point=9)
    assert [x for x, _y in _xy(row)] == pytest.approx([-3400 + 700, -2200 + 700, -1000 + 700])
    assert [y for _x, y in _xy(row)] == pytest.approx([1200 - _CAP] * 3)


def test_a_line_taller_than_its_column_declines(ttf: Path) -> None:
    row = _static(ttf, ["l"], width=10, gutter=2, height=5)
    assert (row["id"], row["reason"]) == ("ID_TextEntity", "an MTEXT line is taller than its column")


# --- differential against ezdxf's layout engine -----------------------------------------


class _Recorder(tl.ContentRenderer):
    def __init__(self, index: int, log: dict) -> None:
        self.index, self.log = index, log

    def render(self, left, bottom, right, top, m=None) -> None:
        self.log[self.index] = (left, bottom)

    def line(self, *args, **kwargs) -> None:
        pass


@pytest.mark.slow
@pytest.mark.parametrize("seed", range(40))
def test_word_positions_match_ezdxf_across_columns(ttf: Path, seed: int) -> None:
    rng = random.Random(seed)
    width, gutter = rng.choice([9.0, 14.0, 20.0]), rng.choice([0.0, 2.0, 5.5])
    paragraphs = []
    for _ in range(rng.randint(1, 6)):
        words = [rng.randint(1, 3) for _ in range(rng.randint(1, 5))]
        paragraphs.append((words, rng.random() < 0.2))  # (word sizes, column break before)
    paragraphs[0] = (paragraphs[0][0], False)
    manual = rng.random() < 0.5
    heights = [rng.choice([13.0, 21.5, 31.0]) for _ in range(rng.randint(1, 3))]

    content = ""
    for number, (words, brk) in enumerate(paragraphs):
        if number:
            content += r"\N" if brk else r"\P"
        content += " ".join("l" * size for size in words)

    doc = _doc()
    attribs = {"style": "GLYPH", "char_height": 7, "insert": (0, 0)}
    if manual:
        entity = doc.modelspace().add_mtext_dynamic_manual_height_columns(
            content, width=width, gutter_width=gutter, heights=heights, dxfattribs=attribs
        )
    else:
        entity = doc.modelspace().add_mtext_static_columns(
            [content], width=width, gutter_width=gutter, height=heights[0], dxfattribs=attribs
        )
    (row,) = _rows(doc, {"carriertext.ttf": ttf})
    if row["record"] == "decline":
        assert row["reason"] == "an MTEXT line is taller than its column"
        return

    # ezdxf: the same cells, in font units, through the engine's columns and paragraphs.
    log: dict[int, tuple[float, float]] = {}
    layout = tl.Layout(width=width * 100)
    for height in column_heights(entity.columns):
        layout.append_column(width=width * 100, height=None if height is None else height * 100, gutter=gutter * 100)
    count = 0
    for number, (words, brk) in enumerate(paragraphs):
        if brk:
            layout.next_column()
        cells = []
        for k, size in enumerate(words):
            if k:
                cells.append(tl.Space(width=_SPACE))
            cells.append(tl.Text(width=size * _L, height=_CAP, renderer=_Recorder(count, log)))
            count += 1
        paragraph = tl.Paragraph(align=tl.ParagraphAlignment.LEFT, line_spacing=1)
        paragraph.append_content(cells)
        layout.append_paragraphs([paragraph])
    layout.place(0, 0)
    layout.render()

    pens = _pens(row)
    mine, at = [], 0
    for words, _brk in paragraphs:
        for size in words:
            mine.append(pens[at])
            at += size
    for index, (x, y) in enumerate(mine):
        left, bottom = log[index]
        assert x == pytest.approx(left)
        # ezdxf spaces lines by 1.667 cap heights, here by 5/3: a few units over a column.
        assert y == pytest.approx(bottom, rel=2e-4, abs=1.0)
