"""Text carrier rows to MULTIPOLYGON WKT: Hausdorff bound and nonzero fill."""

from __future__ import annotations

import json
import math
from pathlib import Path

import freetype
import pytest

import dxf_extract
import glyph_linearize
import text_glyphs
from test_text_glyphs import _ADVANCE, _CAP, _DGN_CTX, _doc, otf, ttf  # noqa: F401


def _row(font: Path, text: str, *, height: float = 7.0, tolerance: dict | None = None, **run) -> dict:
    ctx = dict(_DGN_CTX)
    if tolerance is not None:
        ctx["tolerance"] = tolerance
    row = text_glyphs.run_record(text_glyphs.TextRun(text=text, font=font, height=height, insert=(0.0, 0.0), **run), **ctx)
    assert isinstance(row, dict), row
    return row


def _polygons(wkt: str) -> list[list[list[tuple[float, float]]]]:
    assert wkt.startswith("MULTIPOLYGON (((") and wkt.endswith(")))")
    polygons = []
    for body in wkt[len("MULTIPOLYGON (((") : -3].split(")), (("):
        rings = []
        for ring in body.split("), ("):
            points = [tuple(float(v) for v in pair.split()) for pair in ring.split(", ")]
            assert points[0] == points[-1]
            rings.append(points[:-1])
        polygons.append(rings)
    return polygons


def _area(ring: list[tuple[float, float]]) -> float:
    return sum(x1 * y2 - x2 * y1 for (x1, y1), (x2, y2) in zip(ring, ring[1:] + ring[:1])) / 2


def _filled(polygons, point) -> bool:
    return any(
        glyph_linearize.winding(rings[0], point) != 0
        and all(glyph_linearize.winding(hole, point) == 0 for hole in rings[1:])
        for rings in polygons
    )


def _dist_to_ring(point, ring) -> float:
    best = math.inf
    px, py = point
    for (ax, ay), (bx, by) in zip(ring, ring[1:] + ring[:1]):
        dx, dy = bx - ax, by - ay
        t = max(0.0, min(1.0, ((px - ax) * dx + (py - ay) * dy) / (dx * dx + dy * dy)))
        best = min(best, math.hypot(px - ax - t * dx, py - ay - t * dy))
    return best


def test_wang_count_is_the_closed_form() -> None:
    quad = [(0.0, 0.0), (50.0, 100.0), (100.0, 0.0)]
    # p = 2, M = |P0 - 2 P1 + P2| = 200, n = ceil(sqrt(2*200 / (8*d))).
    assert glyph_linearize.wang_count(quad, 1.0) == math.ceil(math.sqrt(50))
    assert glyph_linearize.wang_count(quad, 1e9) == 1
    assert glyph_linearize.wang_count([(0.0, 0.0), (1.0, 1.0), (2.0, 2.0)], 1e-6) == 1


def test_stem_is_one_rectangle_with_the_placed_area(ttf: Path) -> None:
    out = glyph_linearize.linearize_row(_row(ttf, "l", rotation=30), hausdorff=0.01)
    (rings,) = _polygons(out["wkt"])
    assert out["polygons"] == 1 and len(rings) == 1 and len(rings[0]) == 4
    scale = 7.0 / _CAP
    assert _area(rings[0]) == pytest.approx(100 * 700 * scale * scale)


def test_e_is_a_ccw_shell_with_a_cw_hole_within_the_bound(ttf: Path) -> None:
    bound = 0.005
    row = _row(ttf, "e")
    out = glyph_linearize.linearize_row(row, hausdorff=bound)
    assert out["hausdorff"] == bound
    ((shell, hole),) = _polygons(out["wkt"])
    assert _area(shell) > 0 > _area(hole)

    glyph = row["params"]["members"][0]
    links = glyph["placement"]["links"]
    worst = 0.0
    for contour, ring in zip(glyph["params"]["members"][1:], (shell, hole)):
        for span in contour["params"]["members"]:
            control = [tuple(p) for p in span["params"]["controlPoints"]]
            for step in range(201):
                point = glyph_linearize.bezier_point(control, step / 200)
                for link in links:
                    point = glyph_linearize._apply(point, link)
                worst = max(worst, _dist_to_ring(point, ring))
    assert 0 < worst <= bound

    coarse = glyph_linearize.linearize_row(row, hausdorff=bound * 100)
    assert len(coarse["wkt"]) < len(out["wkt"])


def test_record_sagitta_scales_to_the_world_bound(ttf: Path) -> None:
    row = _row(ttf, "e", tolerance={"kind": "sagitta", "d": 2.0})
    out = glyph_linearize.linearize_row(row)
    assert out["hausdorff"] == pytest.approx(2.0 * 7.0 / _CAP)
    same = glyph_linearize.linearize_row(row, hausdorff=out["hausdorff"])
    flat = lambda wkt: [v for rings in _polygons(wkt) for ring in rings for point in ring for v in point]
    assert flat(same["wkt"]) == pytest.approx(flat(out["wkt"]))
    untold = glyph_linearize.linearize_row(_row(ttf, "e"))
    assert untold[0] == "ID_ToleranceKindUnsupported"
    assert glyph_linearize.linearize_row(row, hausdorff=0.0)[0] == "ID_ToleranceNonPositive"


@pytest.mark.parametrize("run", [{}, {"backward": True}, {"upside_down": True}, {"rotation": 135.0}])
def test_gis_orientation_survives_reflection(ttf: Path, run: dict) -> None:
    out = glyph_linearize.linearize_row(_row(ttf, "el e", **run), hausdorff=0.01)
    polygons = _polygons(out["wkt"])
    assert [len(rings) for rings in polygons] == [2, 1, 2]
    for rings in polygons:
        assert _area(rings[0]) > 0
        assert all(_area(hole) < 0 for hole in rings[1:])


@pytest.mark.parametrize(("font_name", "char"), [("ttf", "e"), ("otf", "o")])
def test_fill_agrees_with_the_freetype_rasterizer(request, font_name: str, char: str) -> None:
    font = request.getfixturevalue(font_name)
    ppem = 100
    face = freetype.Face(str(font))
    face.set_pixel_sizes(0, ppem)
    face.load_char(char, freetype.FT_LOAD_RENDER | freetype.FT_LOAD_NO_HINTING)
    bitmap = face.glyph.bitmap
    left, top = face.glyph.bitmap_left, face.glyph.bitmap_top

    # One font unit is ppem / unitsPerEm pixels.
    out = glyph_linearize.linearize_row(_row(font, char, height=_CAP * ppem / 1000), hausdorff=0.01)
    polygons = _polygons(out["wkt"])
    ink = paper = 0
    for row in range(bitmap.rows):
        for col in range(bitmap.width):
            coverage = bitmap.buffer[row * bitmap.pitch + col]
            centre = (left + col + 0.5, top - row - 0.5)
            if coverage == 255:
                assert _filled(polygons, centre), centre
                ink += 1
            elif coverage == 0:
                assert not _filled(polygons, centre), centre
                paper += 1
    assert ink > 500 and paper > (500 if char == "e" else 50)


def test_overlapping_glyphs_decline_instead_of_being_noded(ttf: Path) -> None:
    row = _row(ttf, "ll")
    row["params"]["members"][1]["placement"]["links"][0]["translate"][0] = 50.0
    assert glyph_linearize.linearize_row(row, hausdorff=0.01)[0] == "ID_NonzeroOverlapNotYet"


def test_same_direction_nested_contour_is_not_a_boundary(ttf: Path) -> None:
    row = _row(ttf, "e")
    glyph = row["params"]["members"][0]
    hole = glyph["params"]["members"][2]
    for span in hole["params"]["members"]:
        span["params"]["controlPoints"].reverse()
    hole["params"]["members"].reverse()
    out = glyph_linearize.linearize_row(row, hausdorff=0.01)
    ((shell,),) = _polygons(out["wkt"])
    assert _area(shell) > 0


def test_other_rows_decline() -> None:
    chord = {"record": "entity", "kind": "Chord", "params": {"start": [0, 0], "end": [1, 0]}}
    assert glyph_linearize.linearize_row(chord, hausdorff=0.1)[0] == "ID_UnsupportedEntity"
    plain = {"record": "entity", "kind": "Compound", "params": {"members": [chord]}}
    assert glyph_linearize.linearize_row(plain, hausdorff=0.1)[0] == "ID_UnsupportedEntity"


def test_cli_runs_dxf_text_to_wkt(tmp_path: Path, ttf: Path, capsys) -> None:
    doc = _doc()
    msp = doc.modelspace()
    msp.add_text("el e", height=3.5, rotation=30, dxfattribs={"style": "GLYPH", "insert": (10, 20)})
    msp.add_line((0, 0), (1, 1))
    dxf = tmp_path / "label.dxf"
    doc.saveas(dxf)
    records = tmp_path / "label.jsonl"
    assert dxf_extract.main([str(dxf), str(records), "--font", f"carriertext.ttf={ttf}"]) == 0
    assert glyph_linearize.main([str(records), "--hausdorff", "0.001"]) == 0
    text, line = [json.loads(out) for out in capsys.readouterr().out.splitlines()]
    assert text["polygons"] == 3 and text["hausdorff"] == 0.001
    assert text["wkt"].startswith("MULTIPOLYGON (((")
    xs = [x for rings in _polygons(text["wkt"]) for ring in rings for x, _ in ring]
    assert min(xs) < 10 < max(xs)
    assert line["decline"] == "ID_UnsupportedEntity"
