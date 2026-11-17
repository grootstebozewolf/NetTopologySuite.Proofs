"""MTEXT paragraph layout: justified lines, indents and tab stops.

The layout is checked in closed form, and against ezdxf's own layout
engine (``ezdxf.tools.text_layout``) fed the same word widths.
"""

from __future__ import annotations

import random
from pathlib import Path

import pytest
from ezdxf.render.abstract_mtext_renderer import make_default_tab_stops, make_tab_stops
from ezdxf.tools import text_layout as tl

from test_text_glyphs import _CAP, _mtext_rows, _pens, ttf  # noqa: F401

# At char height 7 one drawing unit is 100 font units. "l" advances 300, a space 250.
_L, _SPACE = 300, 250


def _xs(row: dict) -> list[float]:
    return [round(pen[0], 6) for pen in _pens(row)]


def _ys(row: dict) -> list[float]:
    return [round(pen[1], 6) for pen in _pens(row)]


def test_justified_line_spreads_its_spaces_but_not_the_last_line(ttf: Path) -> None:
    (row,) = _mtext_rows(ttf, r"\pxqj;ll ll ll ll", width=15.0)
    # Line one holds "ll ll" (1450 of 1500): its one space grows by 50. Line two is the last: left as is.
    assert _xs(row) == [0, 300, 900, 1200, 0, 300, 850, 1150]


def test_first_left_and_right_indents(ttf: Path) -> None:
    # Left 2 caps, first line 3 caps more, right 1 cap; the column is 6000 units.
    (row,) = _mtext_rows(ttf, r"\pxql,l2,r1,i3;ll ll ll", width=60.0)
    assert _xs(row) == [3500, 3800, 4350, 4650, 1400, 1700]
    assert _ys(row)[4] < _ys(row)[0]
    (row,) = _mtext_rows(ttf, r"\pxqr,r1;l", width=20.0)
    assert _xs(row) == [2000 - 700 - 300]


def test_tab_stops_left_right_centre_and_default(ttf: Path) -> None:
    (row,) = _mtext_rows(ttf, "l^Il")
    assert _xs(row) == [0, 4 * _CAP]
    (row,) = _mtext_rows(ttf, r"\pxt1,r6,c10;l^Il^Il^Il")
    # Left stop 700; right stop 4200 ends the next l there; centre stop 7000 centres the last.
    assert _xs(row) == [0, 700, 4200 - _L, 7000 - _L / 2]
    # On a centred line a tab is a space.
    (row,) = _mtext_rows(ttf, r"\pxqc;l^Il")
    assert _xs(row) == [0, _L + _SPACE]
    # Stops count from the paragraph's left edge, not from the indented line start.
    (row,) = _mtext_rows(ttf, r"\pxql,l1,t2;l^Il")
    assert _xs(row) == [700, 1400]


# --- differential against ezdxf's layout engine -----------------------------------------


class _Recorder(tl.ContentRenderer):
    def __init__(self, index: int, log: dict) -> None:
        self.index, self.log = index, log

    def render(self, left, bottom, right, top, m=None) -> None:
        self.log[self.index] = (left, bottom)

    def line(self, *args, **kwargs) -> None:
        pass


def _ezdxf_layout(tokens, align, indent, stops, column):
    """Word left edges and line numbers from ezdxf for the same widths, in font units."""
    log: dict[int, tuple[float, float]] = {}
    cells = []
    words = 0
    for kind, size in tokens:
        if kind == "word":
            cells.append(tl.Text(width=size * _L, height=_CAP, renderer=_Recorder(words, log)))
            words += 1
        elif kind == "space":
            cells.append(tl.Space(width=_SPACE))
        elif kind == "nbsp":
            cells.append(tl.NonBreakingSpace(width=_SPACE))
        else:
            cells.append(tl.Tabulator(width=_SPACE))
    defaults = make_default_tab_stops(_CAP, column)
    tab_stops = make_tab_stops(_CAP, column, stops, defaults) if stops else defaults
    first, left, right = indent
    paragraph = tl.Paragraph(
        align=align,
        indent=((left + first) * _CAP, left * _CAP, right * _CAP),
        line_spacing=1,
        tab_stops=tab_stops,
    )
    paragraph.append_content(cells)
    layout = tl.Layout(width=column)
    layout.append_column()
    layout.append_paragraphs([paragraph])
    layout.place(0, 0)
    layout.render()
    # A known divergence: on a centred or right line ezdxf turns a tab that does not fit into a
    # space that starts the next line (and can leave an empty line). We drop it, like any
    # separator at a break.
    carried = align in (tl.ParagraphAlignment.CENTER, tl.ParagraphAlignment.RIGHT) and (
        any(line._cells and isinstance(line._cells[0].cell, tl.Glue) for line in paragraph._lines)
        or any(not line._cells for line in paragraph._lines)
    )
    bottoms = sorted({bottom for _x, bottom in log.values()}, reverse=True)
    return [(round(log[i][0], 6), bottoms.index(log[i][1])) for i in range(words)], carried


_ALIGNS = {"l": tl.ParagraphAlignment.LEFT, "j": tl.ParagraphAlignment.JUSTIFIED, "r": tl.ParagraphAlignment.RIGHT, "c": tl.ParagraphAlignment.CENTER}


@pytest.mark.parametrize("seed", range(60))
def test_word_positions_match_ezdxfs_layout_engine(ttf: Path, seed: int) -> None:
    rng = random.Random(seed)
    tokens = [("word", rng.randint(1, 3))]
    for _ in range(rng.randint(1, 9)):
        tokens.append((rng.choice(["space", "space", "space", "nbsp", "tab"]), 0))
        tokens.append(("word", rng.randint(1, 3)))
    code = rng.choice("ljrc")
    indent = (rng.choice([0, 0, 1, 2]), rng.choice([0, 0, 1]), rng.choice([0, 0, 1]))
    stops = rng.choice([(), (), (1.5, "r4", "c6.5"), (2, 5)])
    # Real drawings leave room for a word after the indents.
    column = (indent[0] + indent[1] + indent[2]) * _CAP + rng.choice([1000, 1800, 2600, 4000])

    props = f"\\pxq{code},i{indent[0]},l{indent[1]},r{indent[2]}" + "".join(
        f",t{stop}" if isinstance(stop, (int, float)) else f",t{stop}" for stop in stops
    )
    text = props + ";" + "".join(
        "l" * size if kind == "word" else {"space": " ", "nbsp": "\\~", "tab": "^I"}[kind] for kind, size in tokens
    )
    (row,) = _mtext_rows(ttf, text, width=column / 100)
    assert row["record"] == "entity", row

    # Our word left edges: the pen of each word's first glyph.
    pens = _pens(row)
    ys = sorted({round(pen[1], 6) for pen in pens}, reverse=True)
    mine, at = [], 0
    for kind, size in tokens:
        if kind == "word":
            mine.append((round(pens[at][0], 6), ys.index(round(pens[at][1], 6))))
            at += size
    theirs, carried = _ezdxf_layout(tokens, _ALIGNS[code], indent, stops, column)
    if carried:
        pytest.skip("ezdxf carried a tab into the next line as a space (known divergence)")
    assert mine == pytest.approx(theirs), text
