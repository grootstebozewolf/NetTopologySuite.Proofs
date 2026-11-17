"""MTEXT stacked text: ezdxf's Fraction cell, with a filled bar from the font's underline."""

from __future__ import annotations

from pathlib import Path

import pytest
import shapely
from ezdxf.tools import text_layout as tl

import glyph_linearize
from test_text_decorations import _UNDER_THICK, banded  # noqa: F401
from test_text_glyphs import _CAP, _doc, _rows

_L = 300  # advance of "l" at the 700-unit cap


def _row(font: Path, content: str, name: str = "carriertext.ttf") -> dict:
    doc = _doc(name)
    doc.modelspace().add_mtext(content, dxfattribs={"style": "GLYPH", "char_height": 7, "insert": (0, 0)})
    (row,) = _rows(doc, {name: font})
    return row


def _flat(points) -> list[float]:
    return [float(v) for point in points for v in point]


def _pen(member: dict) -> list[float]:
    return member["placement"]["links"][0]["translate"]


def _corners(member: dict) -> list[list[float]]:
    return [c["params"]["start"] for c in member["params"]["members"][1]["params"]["members"]]


def test_horizontal_fraction_stacks_centred_with_a_filled_bar(banded: Path) -> None:
    row = _row(banded, r"\Sl/ll;")
    top, bottom, extra, bar = row["params"]["members"]
    # Cell: 2.4 caps tall, as wide as "ll". The line is as tall as the cell.
    base = -2.4 * _CAP
    assert _pen(top) == pytest.approx([(600 - _L) / 2, base + 1.4 * _CAP])
    assert _flat([_pen(bottom), _pen(extra)]) == pytest.approx([0, base, _L, base])
    # The bar runs across the cell at mid-height, as thick as the underline (100).
    assert _pen(bar) == pytest.approx([0, base])
    half = _UNDER_THICK / 2
    assert _flat(_corners(bar)) == pytest.approx([0, 840 + half, 600, 840 + half, 600, 840 - half, 0, 840 - half])
    assert bar["params"]["members"][0]["params"]["orientation"] == ["cw"]


def test_diagonal_fraction_sets_the_parts_corner_to_corner(banded: Path) -> None:
    row = _row(banded, r"\Sll#l;")
    first, second, bottom, bar = row["params"]["members"]
    base = -2.0 * _CAP
    assert _flat([_pen(first), _pen(second), _pen(bottom)]) == pytest.approx([0, base + _CAP, _L, base + _CAP, 600, base])
    # The diagonal is centred where the top part ends, half the smaller side either way.
    xs = [corner[0] for corner in _corners(bar)]
    ys = [corner[1] for corner in _corners(bar)]
    assert (min(xs) + max(xs)) / 2 == pytest.approx(600)
    assert (min(ys) + max(ys)) / 2 == pytest.approx(700)


def test_tolerance_stack_has_no_bar_and_an_empty_part_is_fine(banded: Path) -> None:
    row = _row(banded, r"\Sl^ l;")
    assert len(row["params"]["members"]) == 2
    row = _row(banded, r"\Sl/;")
    assert len(row["params"]["members"]) == 2  # the top part and the bar
    # No stacking character: ezdxf sets a plain word.
    row = _row(banded, r"\Sll;")
    assert _flat(_pen(m) for m in row["params"]["members"]) == pytest.approx([0, -_CAP, _L, -_CAP])


class _Recorder(tl.ContentRenderer):
    def __init__(self, name: str, log: dict) -> None:
        self.name, self.log = name, log

    def render(self, left, bottom, right, top, m=None) -> None:
        self.log[self.name] = (left, bottom)

    def line(self, x1, y1, x2, y2, m=None) -> None:
        self.log["bar"] = ((x1, y1), (x2, y2))


@pytest.mark.parametrize(
    ("content", "stacking", "top_w", "bottom_w"),
    [
        (r"\Sl/ll;", tl.Stacking.LINE, 300, 600),
        (r"\Sll#l;", tl.Stacking.SLANTED, 600, 300),
        # DXF caret encoding needs a space after a "^" stack mark; the parser drops it.
        (r"\Sl^ ll;", tl.Stacking.OVER, 300, 600),
    ],
)
def test_parts_and_bar_match_ezdxfs_fraction_cell(banded: Path, content, stacking, top_w, bottom_w) -> None:
    log: dict = {}
    fraction = tl.Fraction(
        top=tl.Text(top_w, _CAP, renderer=_Recorder("top", log)),
        bottom=tl.Text(bottom_w, _CAP, renderer=_Recorder("bottom", log)),
        stacking=stacking,
        renderer=_Recorder("cell", log),
    )
    fraction.place(0, fraction.total_height)
    fraction.render()
    row = _row(banded, content)
    members = row["params"]["members"]
    base = -fraction.total_height
    # Our pens are relative to the cell's baseline; ezdxf's parts are placed by their bottoms.
    top_glyphs = 1 if top_w == 300 else 2
    assert _pen(members[0])[0] == pytest.approx(log["top"][0])
    assert _pen(members[0])[1] - base == pytest.approx(log["top"][1])
    assert _pen(members[top_glyphs])[0] == pytest.approx(log["bottom"][0])
    assert _pen(members[top_glyphs])[1] - base == pytest.approx(log["bottom"][1])
    if stacking == tl.Stacking.OVER:
        assert "bar" not in log and len(members) == 3
        return
    corners = _corners(members[-1])
    centre_line = [((corners[0][0] + corners[3][0]) / 2, (corners[0][1] + corners[3][1]) / 2),
                   ((corners[1][0] + corners[2][0]) / 2, (corners[1][1] + corners[2][1]) / 2)]
    assert _flat(centre_line) == pytest.approx(_flat(log["bar"]))


def test_fraction_in_a_stroke_font_draws_its_bar_as_a_stroke(tmp_path: Path) -> None:
    from test_stroke_glyphs import _SHP

    shp = tmp_path / "carrierstroke.shp"
    shp.write_bytes(_SHP)
    row = _row(shp, r"\SL/L;", name="carrierstroke.shp")
    *_parts, bar = row["params"]["members"]
    (stroke,) = bar["params"]["members"]
    assert stroke["kind"] == "BulgePolyline"
    (segment,) = stroke["params"]["segments"]
    # Stroke cap 21: the cell is 50.4 tall, the bar at 25.2 across the 18-wide L advance.
    assert (segment["start"], segment["end"]) == (pytest.approx([0, 25.2]), pytest.approx([18, 25.2]))


def test_fraction_row_linearizes_to_valid_polygons(banded: Path) -> None:
    out = glyph_linearize.linearize_row(_row(banded, r"l \Sl/ll; l"), hausdorff=0.001)
    shape = shapely.from_wkt(out["wkt"])
    assert shape.is_valid and out["polygons"] == 6
