"""In-memory DXF fixtures for the CAD carrier extractor."""

from __future__ import annotations

import json
import math
from pathlib import Path

import ezdxf
import pytest
from jsonschema import Draft202012Validator

import dxf_extract

SCHEMA = json.loads(dxf_extract.SCHEMA_PATH.read_text(encoding="utf-8"))
VALIDATOR = Draft202012Validator(SCHEMA)

BLK = "MIR"
BAD = "SHEAR"


def _doc() -> ezdxf.document.Drawing:
    doc = ezdxf.new("R2010")
    doc.header["$INSUNITS"] = 6
    doc.header["$AUNITS"] = 0
    doc.header["$ANGDIR"] = 0
    doc.header["$ANGBASE"] = 0.0
    mirror = doc.blocks.new(BLK)
    mirror.add_line((0, 0), (2, 0))
    shear = doc.blocks.new(BAD)
    shear.add_line((0, 0), (1, 0))
    msp = doc.modelspace()
    msp.add_lwpolyline(
        [(0, 0, 0), (1, 0, 1), (1, 1, -1), (0, 1, 0.4), (0, 2, 0)],
        format="xyb",
    )
    msp.add_lwpolyline([(0, 0), (1, 0), (1, 1), (0, 1)], close=True)
    msp.add_arc((0, 0), radius=2, start_angle=0, end_angle=90)
    msp.add_circle((1, 1), radius=3)
    msp.add_ellipse(center=(0, 0), major_axis=(4, 0), ratio=1)
    msp.add_ellipse(center=(0, 0), major_axis=(4, 0), ratio=0.5)
    msp.add_blockref(BAD, (0, 0), dxfattribs={"xscale": 2, "yscale": 1})
    msp.add_blockref(BLK, (5, 6), dxfattribs={"xscale": -1, "yscale": 1})
    # An OCS entity: its -Z extrusion is a reflection. (A LINE stores world coordinates.)
    tilted = msp.add_circle((2, 0), radius=1)
    tilted.dxf.extrusion = (0, 0, -1)
    msp.add_line((0, 0, 0), (1, 0, 1))
    msp.add_text("hi", dxfattribs={"insert": (0, 0)})
    msp.add_hatch()
    msp.add_point((0, 0))
    bezier = msp.add_spline()
    bezier.control_points = [(0, 0), (1, 2), (3, 2), (4, 0)]
    bezier.dxf.degree = 3
    bezier.knots = [0, 0, 0, 0, 1, 1, 1, 1]
    fit = msp.add_spline([(0, 0), (1, 1), (2, 0)])
    periodic = msp.add_spline()
    periodic.control_points = [(0, 0), (1, 0), (1, 1), (0, 1)]
    periodic.dxf.degree = 3
    periodic.knots = [0, 0, 0, 0, 1, 1, 1, 1]
    periodic.dxf.flags = periodic.PERIODIC
    loose = msp.add_spline()
    loose.control_points = [(0, 0), (1, 2), (3, 2), (4, 0)]
    loose.dxf.degree = 3
    loose.knots = [0, 0, 0, 0.25, 0.75, 1, 1, 1]
    return doc


def fixture_cases() -> list[tuple[str, ezdxf.document.Drawing, str]]:
    """In-test drawings the schema CLI rechecks. Pytest still validates in-process."""
    angdir = ezdxf.new("R2010")
    angdir.header["$INSUNITS"] = 6
    angdir.header["$AUNITS"] = 0
    angdir.header["$ANGDIR"] = 1
    angdir.header["$ANGBASE"] = 45.0
    angdir.modelspace().add_arc((0, 0), radius=2, start_angle=10, end_angle=80)
    raw = ezdxf.new("R2010")
    raw.modelspace().add_arc((1, 2), radius=3, start_angle=350, end_angle=10)
    return [
        ("main-strict", _doc(), "strict"),
        ("main-lenient", _doc(), "lenient"),
        ("angdir1", angdir, "strict"),
        ("raw-end", raw, "strict"),
    ]


def _rows(mode: str) -> list[dict]:
    doc = _doc()
    return dxf_extract.extract_document(doc, mode=mode, file_id="fixture")


def _by_handle(rows: list[dict]) -> dict[str, dict]:
    return {row["provenance"]["handle"]: row for row in rows}


@pytest.fixture(scope="module")
def drawing() -> ezdxf.document.Drawing:
    return _doc()


def test_schema_is_draft_2020_12() -> None:
    Draft202012Validator.check_schema(SCHEMA)
    assert "ID_NonzeroOverlapNotYet" in SCHEMA["$defs"]["declineId"]["enum"]
    assert dxf_extract.OVERLAP_DETECTED is False


@pytest.mark.parametrize("mode", ["strict", "lenient"])
def test_every_output_validates_and_accounts(mode: str) -> None:
    rows = _rows(mode)
    assert rows
    for row in rows:
        VALIDATOR.validate(row)
    records = [r for r in rows if r["record"] == "entity"]
    declines = [r for r in rows if r["record"] == "decline"]
    assert len(rows) == len(records) + len(declines)
    # 17 modelspace entities, minus the similarity INSERT, plus its one LINE.
    assert len(rows) == 17
    assert all(r["id"] != "ID_NonzeroOverlapNotYet" for r in declines)


def test_mixed_bulge_polyline_keeps_source_bulges() -> None:
    rows = _rows("strict")
    poly = next(
        r for r in rows if r["record"] == "entity" and r["kind"] == "BulgePolyline" and not r["params"]["closed"]
    )
    bulges = [seg["bulge"] for seg in poly["params"]["segments"]]
    assert bulges == pytest.approx([0.0, 1.0, -1.0, 0.4])
    assert [seg["kind"] for seg in poly["params"]["segments"]] == ["Chord", "Arc", "Arc", "Arc"]


def test_extractor_does_not_reverse_contour_orientation() -> None:
    squares = {
        "cw": [(0, 0), (0, 1), (1, 1), (1, 0)],
        "ccw": [(0, 0), (1, 0), (1, 1), (0, 1)],
    }
    for name, points in squares.items():
        doc = ezdxf.new("R2010")
        doc.modelspace().add_lwpolyline(points, close=True)
        for mode in ("strict", "lenient"):
            rows = dxf_extract.extract_document(doc, mode=mode, file_id="fixture")
            assert len(rows) == 1
            row = rows[0]
            VALIDATOR.validate(row)
            if mode == "lenient":
                assert row["kind"] == "Ring"
                assert row["params"]["windingRule"] == "nonzero"
                assert row["params"]["orientation"] == ["cw" if name == "cw" else "ccw"]
                segments = row["params"]["contours"][0]
            else:
                assert row["kind"] == "BulgePolyline"
                assert row["params"]["closed"] is True
                segments = row["params"]["segments"]
            assert [tuple(seg["start"]) for seg in segments] == [(float(x), float(y)) for x, y in points]
            area = 0.0
            for seg in segments:
                x1, y1 = seg["start"]
                x2, y2 = seg["end"]
                area += x1 * y2 - x2 * y1
            assert area < 0 if name == "cw" else area > 0


def test_closed_polyline_is_ring_only_when_lenient() -> None:
    strict = _rows("strict")
    lenient = _rows("lenient")
    closed = [
        r
        for r in strict
        if r["record"] == "entity" and r["kind"] == "BulgePolyline" and r["params"]["closed"]
    ]
    assert len(closed) == 1
    assert len(closed[0]["params"]["segments"]) == 4
    rings = [r for r in lenient if r["record"] == "entity" and r["kind"] == "Ring"]
    assert len(rings) == 1
    assert rings[0]["params"]["windingRule"] == "nonzero"
    assert rings[0]["params"]["orientation"] == ["ccw"]
    assert len(rings[0]["params"]["contours"]) == 1
    assert len(rings[0]["params"]["contours"][0]) == 4
    assert not any(r["record"] == "entity" and r["kind"] == "Ring" for r in strict)


def test_arc_and_circle() -> None:
    rows = _rows("lenient")
    arc = next(r for r in rows if r["record"] == "entity" and r["kind"] == "Arc" and r["params"].get("angleUnit") == "degree")
    assert arc["params"]["radius"] == pytest.approx(2)
    assert arc["params"]["startAngle"] == pytest.approx(0)
    assert arc["params"]["endAngle"] == pytest.approx(90)
    assert arc["params"]["direction"] == "ccw-ocs"
    circle = next(r for r in rows if r["record"] == "entity" and r["kind"] == "Circle")
    assert circle["params"]["radius"] == pytest.approx(3)
    assert circle["units"]["linear"] == "meter"
    assert circle["tolerance"] == {"kind": "sourceDefault"}
    assert circle["dimension"] == {"space": "2d"}
    assert circle["placement"]["s"] == 1


def test_ellipse_modes() -> None:
    for mode, ratio1_kind in (("strict", None), ("lenient", "Arc")):
        rows = _rows(mode)
        ell = [r for r in rows if r["record"] == "decline" and r["id"] == "ID_EllipseNotYet"]
        arcs = [
            r
            for r in rows
            if r["record"] == "entity"
            and r["kind"] == "Arc"
            and r["params"].get("angleUnit") == "radian"
        ]
        if ratio1_kind is None:
            assert len(ell) == 2
            assert arcs == []
        else:
            assert len(ell) == 1
            assert len(arcs) == 1
            assert arcs[0]["params"]["radius"] == pytest.approx(4)
            assert arcs[0]["params"]["direction"] == "ccw-ocs"
            assert "frameAngle" in arcs[0]["params"]


def test_insert_nonuniform_declines_and_mirror_sign() -> None:
    rows = _rows("strict")
    bad = next(r for r in rows if r["record"] == "decline" and r["id"] == "ID_NotSimilarityPlacement")
    assert bad["provenance"]["blockPath"] == []
    mirrored = [
        r
        for r in rows
        if r["record"] == "entity" and r["provenance"]["blockPath"] == [BLK]
    ]
    assert len(mirrored) == 1
    assert mirrored[0]["kind"] == "Chord"
    assert mirrored[0]["placement"]["s"] == -1
    assert mirrored[0]["placement"]["links"][0]["reflect"] is True
    assert mirrored[0]["placement"]["links"][0]["scale"] == pytest.approx(1)
    assert mirrored[0]["placement"]["links"][0]["translate"] == pytest.approx([5, 6])


def test_extrusion_negative_z_is_a_reflection() -> None:
    rows = _rows("strict")
    reflected = [
        r
        for r in rows
        if r["record"] == "entity"
        and r["kind"] == "Circle"
        and r["placement"]["s"] == -1
        and r["provenance"]["blockPath"] == []
    ]
    assert len(reflected) == 1
    assert reflected[0]["placement"]["links"][0]["reflect"] is True


def test_text_hatch_point_and_spline_declines() -> None:
    rows = _rows("lenient")
    ids = [r["id"] for r in rows if r["record"] == "decline"]
    assert "ID_TextEntity" in ids
    assert "ID_HatchRegion" in ids
    assert "ID_ThreeDNotYet" in ids
    assert "ID_FitPointSpline" in ids
    assert "ID_PeriodicSpline" in ids
    assert "ID_UnclampedKnots" in ids
    unknown = next(r for r in rows if r["record"] == "decline" and r["id"] == "ID_UnsupportedEntity")
    assert unknown["name"] == "POINT"
    bezier = next(r for r in rows if r["record"] == "entity" and r["kind"] == "Bezier")
    assert bezier["params"]["degree"] == 3
    assert len(bezier["params"]["controlPoints"]) == 4
    assert bezier["params"]["weights"] == [1, 1, 1, 1]
    assert bezier["params"]["knots"] == [0, 0, 0, 0, 1, 1, 1, 1]


def test_cli_jsonl_matches_library(tmp_path: Path) -> None:
    path = tmp_path / "sample.dxf"
    _doc().saveas(path)
    out = tmp_path / "out.jsonl"
    assert dxf_extract.main([str(path), str(out), "--mode", "lenient", "--file-id", "fixture"]) == 0
    lines = out.read_text(encoding="utf-8").splitlines()
    rows = [json.loads(line) for line in lines]
    assert rows == _rows("lenient")
    for row in rows:
        VALIDATOR.validate(row)


def test_tolerance_nonpositive_and_kind() -> None:
    assert dxf_extract.parse_tolerance("sagitta:0") == "ID_ToleranceNonPositive"
    assert dxf_extract.parse_tolerance("count:0") == "ID_ToleranceNonPositive"
    assert dxf_extract.parse_tolerance("angle:-1") == "ID_ToleranceNonPositive"
    stepped = dxf_extract.parse_tolerance("angle:5")
    assert stepped["direction"] == "ccw-ocs"
    assert stepped["alpha"] == pytest.approx(5)
    doc = ezdxf.new("R2010")
    doc.modelspace().add_line((0, 0), (1, 0))
    rows = dxf_extract.extract_document(
        doc,
        mode="strict",
        tolerance={"kind": "angleStep", "alpha": 5.0, "angleUnit": "degree"},
        file_id="fixture",
    )
    assert rows[0]["record"] == "decline"
    assert rows[0]["id"] == "ID_ToleranceKindUnsupported"
    arc_doc = ezdxf.new("R2010")
    arc_doc.modelspace().add_arc((0, 0), radius=1, start_angle=0, end_angle=45)
    arc_rows = dxf_extract.extract_document(
        arc_doc,
        mode="strict",
        tolerance={"kind": "angleStep", "alpha": 5.0, "angleUnit": "degree"},
        file_id="fixture",
    )
    assert arc_rows[0]["record"] == "entity"
    assert arc_rows[0]["tolerance"]["kind"] == "angleStep"
    assert arc_rows[0]["tolerance"]["direction"] == "ccw-ocs"
    VALIDATOR.validate(arc_rows[0])
    cw = ezdxf.new("R2010")
    cw.header["$ANGDIR"] = 1
    cw.header["$ANGBASE"] = 90.0
    cw.modelspace().add_arc((0, 0), radius=1, start_angle=0, end_angle=45)
    cw_rows = dxf_extract.extract_document(
        cw,
        mode="strict",
        tolerance={"kind": "angleStep", "alpha": 5.0, "angleUnit": "degree"},
        file_id="fixture",
    )
    assert cw_rows[0]["tolerance"]["direction"] == "ccw-ocs"
    assert cw_rows[0]["tolerance"]["alpha"] == pytest.approx(5)
    assert cw_rows[0]["params"]["direction"] == "ccw-ocs"
    assert cw_rows[0]["units"]["angdir"] == 1
    VALIDATOR.validate(cw_rows[0])


def test_tilted_extrusion_and_unknown_unit() -> None:
    doc = ezdxf.new("R2010")
    circle = doc.modelspace().add_circle((0, 0), 1)
    circle.dxf.extrusion = (1, 0, 0)
    rows = dxf_extract.extract_document(doc, mode="strict", file_id="fixture")
    assert rows[0]["id"] == "ID_TiltedPlacement"
    doc.header["$INSUNITS"] = 99
    rows = dxf_extract.extract_document(doc, mode="lenient", file_id="fixture")
    assert rows[0]["id"] == "ID_UnknownUnit"
    doc.header["$INSUNITS"] = 0
    doc.header["$ANGDIR"] = 7
    doc.header["$ANGBASE"] = 33.0
    rows = dxf_extract.extract_document(doc, mode="strict", file_id="fixture")
    assert rows[0]["id"] == "ID_TiltedPlacement"
    assert rows[0]["id"] != "ID_AngleConventionUnknown"


@pytest.mark.parametrize("mode", ["strict", "lenient"])
@pytest.mark.parametrize("bulge", [math.nan, math.inf, -math.inf])
def test_nonfinite_bulge_declines_in_both_modes(mode: str, bulge: float) -> None:
    doc = ezdxf.new("R2010")
    doc.modelspace().add_lwpolyline([(0, 0, bulge), (1, 0, 0)], format="xyb")
    rows = dxf_extract.extract_document(doc, mode=mode, file_id="fixture")
    assert len(rows) == 1
    assert rows[0]["record"] == "decline"
    assert rows[0]["id"] == "ID_DegenerateEntity"
    VALIDATOR.validate(rows[0])


def test_odd_angdir_and_angbase_match_the_arc_and_do_not_decline() -> None:
    def one(angdir: int, angbase: float) -> dict:
        doc = ezdxf.new("R2010")
        doc.header["$INSUNITS"] = 6
        doc.header["$AUNITS"] = 0
        doc.header["$ANGDIR"] = angdir
        doc.header["$ANGBASE"] = angbase
        doc.modelspace().add_arc((0, 0), radius=2, start_angle=10, end_angle=80)
        rows = dxf_extract.extract_document(doc, mode="strict", file_id="fixture")
        assert len(rows) == 1
        assert rows[0]["record"] == "entity"
        assert rows[0].get("id") != "ID_AngleConventionUnknown"
        VALIDATOR.validate(rows[0])
        return rows[0]

    plain = one(0, 0.0)
    odd = one(7, 33.0)
    plain_body = {key: value for key, value in plain.items() if key != "units"}
    odd_body = {key: value for key, value in odd.items() if key != "units"}
    assert plain_body == odd_body
    assert {key: value for key, value in plain["units"].items() if key not in ("angdir", "angbase")} == {
        key: value for key, value in odd["units"].items() if key not in ("angdir", "angbase")
    }
    assert odd["units"]["angdir"] == 7
    assert odd["units"]["angbase"] == pytest.approx(33)
    assert odd["params"]["direction"] == "ccw-ocs"
    assert odd["params"]["startAngle"] == pytest.approx(10)
    assert odd["params"]["endAngle"] == pytest.approx(80)


def test_angdir_does_not_rewrite_stored_arc() -> None:
    def one(angdir: int, angbase: float) -> dict:
        doc = ezdxf.new("R2010")
        doc.header["$INSUNITS"] = 6
        doc.header["$AUNITS"] = 0
        doc.header["$ANGDIR"] = angdir
        doc.header["$ANGBASE"] = angbase
        doc.modelspace().add_arc((0, 0), radius=2, start_angle=10, end_angle=80)
        rows = dxf_extract.extract_document(doc, mode="strict", file_id="fixture")
        assert len(rows) == 1
        VALIDATOR.validate(rows[0])
        return rows[0]

    ccw = one(0, 0.0)
    cw = one(1, 45.0)
    assert ccw["params"]["direction"] == "ccw-ocs"
    assert ccw["params"]["startAngle"] == pytest.approx(10)
    assert ccw["params"]["endAngle"] == pytest.approx(80)
    ccw_body = {key: value for key, value in ccw.items() if key != "units"}
    cw_body = {key: value for key, value in cw.items() if key != "units"}
    assert ccw_body == cw_body
    assert {key: value for key, value in ccw["units"].items() if key not in ("angdir", "angbase")} == {
        key: value for key, value in cw["units"].items() if key not in ("angdir", "angbase")
    }
    assert ccw["units"]["angdir"] == 0
    assert ccw["units"]["angbase"] == pytest.approx(0)
    assert cw["units"]["angdir"] == 1
    assert cw["units"]["angbase"] == pytest.approx(45)


def test_angdir_does_not_rewrite_ellipse_params() -> None:
    def one(angdir: int, angbase: float) -> dict:
        doc = ezdxf.new("R2010")
        doc.header["$ANGDIR"] = angdir
        doc.header["$ANGBASE"] = angbase
        ell = doc.modelspace().add_ellipse(center=(0, 0), major_axis=(4, 0), ratio=1)
        ell.dxf.start_param = 0.2
        ell.dxf.end_param = 1.2
        rows = dxf_extract.extract_document(doc, mode="lenient", file_id="fixture")
        assert len(rows) == 1
        VALIDATOR.validate(rows[0])
        return rows[0]

    ccw = one(0, 0.0)
    cw = one(1, 30.0)
    assert ccw["params"]["direction"] == "ccw-ocs"
    assert ccw["params"]["angleUnit"] == "radian"
    assert ccw["params"]["startAngle"] == pytest.approx(0.2)
    assert ccw["params"]["endAngle"] == pytest.approx(1.2)
    ccw_body = {key: value for key, value in ccw.items() if key != "units"}
    cw_body = {key: value for key, value in cw.items() if key != "units"}
    assert ccw_body == cw_body
    assert cw["units"]["angdir"] == 1
    assert cw["units"]["angbase"] == pytest.approx(30)


def _hatch(style: int):
    doc = ezdxf.new("R2010")
    hatch = doc.modelspace().add_hatch()
    hatch.dxf.hatch_style = style
    hatch.paths.add_polyline_path([(0, 0, 0), (4, 0, 0), (4, 4, 0), (0, 4, 0)], is_closed=True)
    # Clockwise hole. Source order is kept.
    hatch.paths.add_polyline_path([(1, 1, 0), (1, 2, 0), (2, 2, 0), (2, 1, 0)], is_closed=True)
    return doc


def test_entire_area_hatch_declines() -> None:
    """Style 2 fills the island too; nonzero over these paths (island wound against the
    outer one) would make it a hole, so the hatch declines rather than claim nonzero."""
    for mode in ("strict", "lenient"):
        (row,) = dxf_extract.extract_document(_hatch(2), mode=mode, file_id="fixture")
        assert (row["record"], row["id"]) == ("decline", "ID_HatchRegion")


def test_hatch_boundary_is_a_ring_and_is_not_flipped() -> None:
    for style, rule in ((0, "evenodd"),):
        for mode in ("strict", "lenient"):
            rows = dxf_extract.extract_document(_hatch(style), mode=mode, file_id="fixture")
            assert len(rows) == 1
            row = rows[0]
            VALIDATOR.validate(row)
            assert row["kind"] == "Ring"
            assert row["params"]["windingRule"] == rule
            assert row["params"]["orientation"] == ["ccw", "cw"]
            outer, hole = row["params"]["contours"]
            assert [tuple(seg["start"]) for seg in outer] == [(0.0, 0.0), (4.0, 0.0), (4.0, 4.0), (0.0, 4.0)]
            assert [tuple(seg["start"]) for seg in hole] == [(1.0, 1.0), (1.0, 2.0), (2.0, 2.0), (2.0, 1.0)]


def test_hatch_arc_edge_keeps_clockwise_bulge() -> None:
    doc = ezdxf.new("R2010")
    hatch = doc.modelspace().add_hatch()
    hatch.dxf.hatch_style = 0
    edge = hatch.paths.add_edge_path()
    edge.add_arc((0, 0), radius=1, start_angle=0, end_angle=180, ccw=False)
    edge.add_line((-1, 0), (0, 1))
    edge.add_line((0, 1), (1, 0))
    rows = dxf_extract.extract_document(doc, mode="strict", file_id="fixture")
    assert len(rows) == 1
    row = rows[0]
    VALIDATOR.validate(row)
    assert row["kind"] == "Ring"
    first = row["params"]["contours"][0][0]
    assert first["kind"] == "Arc"
    assert first["start"] == pytest.approx([1.0, 0.0])
    assert first["end"] == pytest.approx([-1.0, 0.0])
    assert first["bulge"] == pytest.approx(-1.0)
    assert first["bulge"] < 0


def test_hatch_without_a_boundary_still_declines() -> None:
    doc = ezdxf.new("R2010")
    doc.modelspace().add_hatch()
    outermost = ezdxf.new("R2010")
    hatch = outermost.modelspace().add_hatch()
    hatch.dxf.hatch_style = 1
    hatch.paths.add_polyline_path([(0, 0), (1, 0), (1, 1), (0, 1)], is_closed=True)
    spline = ezdxf.new("R2010")
    edged = spline.modelspace().add_hatch()
    path = edged.paths.add_edge_path()
    path.add_ellipse(center=(0, 0), major_axis=(1, 0), ratio=0.5)
    path.add_line((1, 0), (0, 0))
    path.add_line((0, 0), (0, 1))
    for drawing in (doc, outermost, spline):
        rows = dxf_extract.extract_document(drawing, mode="lenient", file_id="fixture")
        assert len(rows) == 1
        assert rows[0]["record"] == "decline"
        assert rows[0]["id"] == "ID_HatchRegion"
        VALIDATOR.validate(rows[0])


def test_polyline_chain_is_a_compound_in_source_order() -> None:
    doc = ezdxf.new("R2010")
    doc.modelspace().add_polyline2d([(0, 0, 0), (0, 1, -0.5), (1, 1, 0)], format="xyb", close=True)
    doc.modelspace().add_polyline3d([(0, 0, 0), (1, 0, 1), (0, 1, 2)])
    rows = dxf_extract.extract_document(doc, mode="strict", file_id="fixture")
    assert len(rows) == 2
    chain, declined = rows
    VALIDATOR.validate(chain)
    VALIDATOR.validate(declined)
    assert chain["kind"] == "Compound"
    assert declined["id"] == "ID_ThreeDNotYet"
    members = chain["params"]["members"]
    assert [member["kind"] for member in members] == ["Chord", "BulgePolyline", "Chord"]
    assert members[0]["params"]["start"] == [0.0, 0.0]
    assert members[0]["params"]["end"] == [0.0, 1.0]
    bulge = members[1]["params"]["segments"][0]
    assert bulge["start"] == [0.0, 1.0]
    assert bulge["end"] == [1.0, 1.0]
    assert bulge["bulge"] == pytest.approx(-0.5)
    assert members[2]["params"]["start"] == [1.0, 1.0]
    assert members[2]["params"]["end"] == [0.0, 0.0]


def test_arc_end_before_start_is_kept_raw() -> None:
    doc = ezdxf.new("R2010")
    doc.modelspace().add_arc((1, 2), radius=3, start_angle=350, end_angle=10)
    rows = dxf_extract.extract_document(doc, mode="strict", file_id="fixture")
    assert rows[0]["record"] == "entity"
    assert rows[0]["params"]["startAngle"] == 350
    assert rows[0]["params"]["endAngle"] == 10
    assert rows[0]["params"]["direction"] == "ccw-ocs"
    VALIDATOR.validate(rows[0])


@pytest.mark.parametrize("mode", ["strict", "lenient"])
def test_closed_polyline_repeating_its_first_vertex_drops_the_repeat(mode: str) -> None:
    square = [(0, 0, 0), (4, 0, 0.5), (4, 3, 0), (0, 3, 0)]
    doc = ezdxf.new("R2010")
    msp = doc.modelspace()
    msp.add_lwpolyline(square + [(0, 0, 0)], format="xyb", close=True)
    msp.add_lwpolyline(square, format="xyb", close=True)
    repeated, plain = dxf_extract.extract_document(doc, mode=mode, file_id="fixture")
    for row in (repeated, plain):
        VALIDATOR.validate(row)
    assert repeated["record"] == "entity"
    assert repeated["params"] == plain["params"]
    contour = repeated["params"]["contours"][0] if mode == "lenient" else repeated["params"]["segments"]
    assert len(contour) == 4
    assert contour[1]["kind"] == "Arc"


@pytest.mark.parametrize(
    "points",
    [
        # A bulge on the repeat would be an arc of no length.
        [(0, 0, 0), (4, 0, 0), (4, 3, 0), (0, 0, 0.3)],
        # A repeat inside the polyline is not the closing vertex.
        [(0, 0, 0), (4, 0, 0), (4, 0, 0), (4, 3, 0)],
    ],
)
def test_other_zero_length_segments_still_decline(points) -> None:
    doc = ezdxf.new("R2010")
    doc.modelspace().add_lwpolyline(points, format="xyb", close=True)
    (row,) = dxf_extract.extract_document(doc, mode="strict", file_id="fixture")
    assert (row["record"], row["id"]) == ("decline", "ID_DegenerateEntity")


def test_closed_2d_polyline_and_hatch_path_repeating_the_first_vertex() -> None:
    doc = ezdxf.new("R2010")
    msp = doc.modelspace()
    msp.add_polyline2d([(0, 0), (4, 0), (4, 3), (0, 0)], close=True)
    hatch = msp.add_hatch()
    hatch.paths.add_polyline_path([(0, 0, 0), (4, 0, 0), (4, 3, 0), (0, 0, 0)], is_closed=True)
    polyline, ring = dxf_extract.extract_document(doc, mode="strict", file_id="fixture")
    VALIDATOR.validate(polyline)
    VALIDATOR.validate(ring)
    assert len(polyline["params"]["members"]) == 3
    assert len(ring["params"]["contours"][0]) == 3


@pytest.mark.parametrize("mode", ["strict", "lenient"])
def test_polyline_width_declines_instead_of_drawing_a_hairline(mode: str) -> None:
    doc = ezdxf.new("R2018")
    msp = doc.modelspace()
    msp.add_lwpolyline([(0, 0), (5, 0), (5, 3)], dxfattribs={"const_width": 0.8}, close=True)
    msp.add_lwpolyline([(0, 0, 0.0, 1.0, 0.0), (5, 0, 0.0, 0.0, 0.0)], format="xyseb")
    msp.add_polyline2d([(0, 0), (5, 0)], dxfattribs={"default_start_width": 0.5, "default_end_width": 0.5})
    tapered = msp.add_polyline2d([(0, 0), (5, 0), (5, 2)])
    tapered.vertices[1].dxf.end_width = 0.3
    msp.add_lwpolyline([(0, 0), (5, 0)], dxfattribs={"const_width": 0.0})
    rows = dxf_extract.extract_document(doc, mode=mode, file_id="width")
    for row in rows:
        VALIDATOR.validate(row)
    *banded, plain = rows
    assert [(r["id"], r["name"]) for r in banded] == [
        ("ID_UnsupportedEntity", "LWPOLYLINE"),
        ("ID_UnsupportedEntity", "LWPOLYLINE"),
        ("ID_UnsupportedEntity", "POLYLINE"),
        ("ID_UnsupportedEntity", "POLYLINE"),
    ]
    assert all(r["reason"] == "polyline width: drawn as a filled band, not a curve" for r in banded)
    assert plain["record"] == "entity"


def test_thickness_declines_as_3d_for_every_kind() -> None:
    doc = ezdxf.new("R2018")
    doc.styles.add("GLYPH", font="carriertext.ttf")
    msp = doc.modelspace()
    msp.add_line((0, 0), (1, 0), dxfattribs={"thickness": 3})
    msp.add_circle((0, 0), 1, dxfattribs={"thickness": -2})
    msp.add_arc((0, 0), 1, 0, 90, dxfattribs={"thickness": 0.5})
    msp.add_lwpolyline([(0, 0), (1, 0)], dxfattribs={"thickness": 1})
    msp.add_text("l", dxfattribs={"thickness": 1, "style": "GLYPH", "height": 7})
    msp.add_line((0, 0), (1, 0), dxfattribs={"thickness": 0})
    seen: list[str] = []
    rows = dxf_extract.extract_document(doc, file_id="thick", fonts={"carriertext.ttf": "unused.ttf"}, on_considered=seen.append)
    for row in rows:
        VALIDATOR.validate(row)
    *thick, flat = rows
    assert [r["id"] for r in thick] == ["ID_ThreeDNotYet"] * 5
    assert all(r["reason"] == "thickness extrudes the entity in Z" for r in thick)
    assert flat["kind"] == "Chord"
    # Still one row per considered entity.
    assert seen == ["LINE", "CIRCLE", "ARC", "LWPOLYLINE", "TEXT", "LINE"]


def test_world_coordinate_entities_ignore_their_extrusion() -> None:
    """LINE and SPLINE store world coordinates: a -Z or tilted extrusion moves nothing (as in ezdxf)."""
    from ezdxf import path as ezpath

    doc = ezdxf.new("R2018")
    msp = doc.modelspace()
    entities = [
        msp.add_line((1, 2), (3, 2), dxfattribs={"extrusion": (0, 0, -1)}),
        msp.add_line((1, 2), (3, 2), dxfattribs={"extrusion": (0, 1, 1)}),
        msp.add_open_spline([(1, 2), (2, 3), (3, 2), (4, 3)], dxfattribs={"extrusion": (0, 0, -1)}),
    ]
    rows = dxf_extract.extract_document(doc, file_id="wcs")
    for entity, row in zip(entities, rows):
        VALIDATOR.validate(row)
        assert row["record"] == "entity" and row["placement"] == {"links": [], "s": 1}
        first = row["params"].get("start") or row["params"]["controlPoints"][0]
        reference = next(iter(ezpath.make_path(entity).control_vertices()))
        assert first == pytest.approx([reference.x, reference.y])


def test_normal_plane_entities_with_a_minus_z_normal_decline() -> None:
    doc = ezdxf.new("R2018")
    msp = doc.modelspace()
    msp.add_mtext("x", dxfattribs={"extrusion": (0, 0, -1)})
    msp.add_ellipse((0, 0), (2, 0), 1.0, dxfattribs={"extrusion": (0, 0, -1)})
    rows = dxf_extract.extract_document(doc, mode="lenient", file_id="normal")
    assert [(r["id"], r["reason"]) for r in rows] == [
        ("ID_UnsupportedEntity", "MTEXT with a -Z extrusion is drawn mirrored about its anchor; not read"),
        ("ID_UnsupportedEntity", "ELLIPSE with a -Z extrusion is drawn mirrored about its anchor; not read"),
    ]


def test_invisible_entities_and_fitted_polylines_decline() -> None:
    doc = ezdxf.new("R2018")
    msp = doc.modelspace()
    msp.add_line((0, 0), (1, 0), dxfattribs={"invisible": 1})
    doc.blocks.new("B").add_line((0, 0), (1, 0))
    msp.add_blockref("B", (0, 0), dxfattribs={"invisible": 1})
    for flag in (2, 4):  # curve-fit, spline-fit
        fitted = msp.add_polyline2d([(0, 0), (1, 1), (2, 0)])
        fitted.dxf.flags |= flag
    rows = dxf_extract.extract_document(doc, file_id="vis")
    for row in rows:
        VALIDATOR.validate(row)
    assert [(r["id"], r["name"], r["reason"]) for r in rows] == [
        ("ID_UnsupportedEntity", "LINE", "invisible: not drawn"),
        ("ID_UnsupportedEntity", "INSERT", "invisible: not drawn"),
        ("ID_UnsupportedEntity", "POLYLINE", "curve-fit or spline-fit polyline: its drawn vertices are not read"),
        ("ID_UnsupportedEntity", "POLYLINE", "curve-fit or spline-fit polyline: its drawn vertices are not read"),
    ]


@pytest.mark.parametrize("seed", range(40))
def test_elevation_is_ezdxfs_world_z(seed: int) -> None:
    """World z through nested inserts with zscale and -Z extrusions, against ezdxf's own placement."""
    import random

    from ezdxf.math import Matrix44

    rng = random.Random(seed)
    doc = ezdxf.new("R2018")
    inner = doc.blocks.new("IN")
    inner.add_circle((1, 1, rng.uniform(-5, 5)), 1, dxfattribs={"extrusion": (0, 0, rng.choice([1, -1]))})
    outer = doc.blocks.new("OUT")
    outer.add_blockref(
        "IN", (2, 3, rng.uniform(-5, 5)),
        dxfattribs={"zscale": rng.choice([1, 2, -0.5]), "extrusion": (0, 0, rng.choice([1, -1]))},
    )
    top = doc.modelspace().add_blockref(
        "OUT", (0, 0, rng.uniform(-5, 5)),
        dxfattribs={"zscale": rng.choice([1, 3, -1]), "extrusion": (0, 0, rng.choice([1, -1]))},
    )
    (row,) = dxf_extract.extract_document(doc, file_id="z")
    circle = next(iter(inner))
    inner_ref = next(iter(outer))
    m = inner_ref.matrix44() @ top.matrix44()
    (world,) = m.transform_vertices([circle.ocs().to_wcs(circle.dxf.center)])
    expected = row["dimension"].get("elevation", 0.0)
    assert expected == pytest.approx(world.z, abs=1e-9)


def test_attached_attribs_are_considered_without_fonts() -> None:
    """An INSERT's ATTRIBs were never visited; they are considered entities now."""
    doc = ezdxf.new("R2018")
    block = doc.blocks.new("TAG")
    block.add_line((0, 0), (1, 0))
    block.add_attdef("T", (0, 1))
    insert = doc.modelspace().add_blockref("TAG", (0, 0))
    insert.add_attrib("T", "v", (0, 1))
    seen: list[str] = []
    rows = dxf_extract.extract_document(doc, file_id="attrib", on_considered=seen.append)
    assert seen == ["LINE", "ATTDEF", "ATTRIB"]
    assert [r.get("kind", r.get("id")) for r in rows] == ["Chord", "ID_TextEntity", "ID_TextEntity"]


def _ids(rows: list[dict]) -> list[tuple[str, str]]:
    return [(row.get("kind") or row["id"], row["provenance"]["handle"]) for row in rows]


@pytest.mark.parametrize(
    "attribs",
    [{"xscale": 2, "yscale": 1}, {"extrusion": (0, 1, 1)}],
    ids=["stretched", "tilted"],
)
def test_a_declined_insert_keeps_its_attribs(attribs: dict) -> None:
    """A stretched title block declines, but its attribute text is still considered."""
    doc = ezdxf.new("R2018")
    doc.blocks.new("TITLE").add_line((0, 0), (10, 0))
    insert = doc.modelspace().add_blockref("TITLE", (0, 0), dxfattribs=attribs)
    a = insert.add_attrib("NAME", "plan", (1, 1))
    b = insert.add_attrib("DATE", "2026", (1, 2))
    seen: list[str] = []
    rows = dxf_extract.extract_document(doc, file_id="title", on_considered=seen.append)
    assert seen == ["INSERT", "ATTRIB", "ATTRIB"]
    assert rows[0]["record"] == "decline"
    assert _ids(rows[1:]) == [("ID_TextEntity", a.dxf.handle), ("ID_TextEntity", b.dxf.handle)]
    assert [row["provenance"]["blockPath"] for row in rows[1:]] == [["TITLE"], ["TITLE"]]


@pytest.mark.parametrize("block", ["EMPTY", "LOOP"])
def test_empty_and_cyclic_inserts_keep_their_attribs(block: str) -> None:
    doc = ezdxf.new("R2018")
    doc.blocks.new("EMPTY")
    doc.blocks.new("LOOP").add_blockref("LOOP", (0, 0))
    insert = doc.modelspace().add_blockref(block, (0, 0))
    insert.add_attrib("T", "v", (0, 1))
    seen: list[str] = []
    rows = dxf_extract.extract_document(doc, file_id="kept", on_considered=seen.append)
    # LOOP: the outer INSERT is entered once; the INSERT inside it is the cyclic one.
    assert seen == ["INSERT", "ATTRIB"]
    assert rows[0]["id"] == "ID_DegenerateEntity"


def test_an_invisible_insert_declines_its_attribs() -> None:
    doc = ezdxf.new("R2018")
    doc.blocks.new("B").add_line((0, 0), (1, 0))
    insert = doc.modelspace().add_blockref("B", (0, 0), dxfattribs={"invisible": 1})
    insert.add_attrib("T", "v", (0, 1))
    rows = dxf_extract.extract_document(doc, file_id="hidden")
    assert [(row["id"], row["reason"]) for row in rows] == [
        ("ID_UnsupportedEntity", "invisible: not drawn"),
        ("ID_UnsupportedEntity", "attribute of an invisible or malformed INSERT: not drawn"),
    ]


def test_extrusion_fails_closed_for_types_not_known_to_be_ocs_or_world() -> None:
    """A type is placed under its extrusion only when it is listed as OCS or world."""
    assert not (dxf_extract.OCS_TYPES & dxf_extract.WORLD_TYPES)
    doc = ezdxf.new("R2018")
    doc.modelspace().add_point((1, 2), dxfattribs={"extrusion": (0, 0, -1)})
    doc.modelspace().add_point((1, 2), dxfattribs={"extrusion": (0, 1, 1)})
    rows = dxf_extract.extract_document(doc, file_id="unknown")
    assert [(row["id"], row["reason"]) for row in rows] == [
        ("ID_UnsupportedEntity", "POINT with a -Z extrusion: not known to be OCS or world coordinates"),
        ("ID_TiltedPlacement", "extrusion is not +/- Z"),
    ]


def test_every_record_type_has_a_stated_coordinate_system(monkeypatch) -> None:
    """A newly mapped type that is in no list is declined under -Z, not mirrored."""
    monkeypatch.setattr(dxf_extract, "WORLD_TYPES", frozenset({"SPLINE"}))  # forget LINE
    doc = ezdxf.new("R2018")
    doc.modelspace().add_line((0, 0), (1, 0), dxfattribs={"extrusion": (0, 0, -1)})
    rows = dxf_extract.extract_document(doc, file_id="forgot")
    assert rows[0]["record"] == "decline"


class _Fake:
    """An entity whose stored values ezdxf did not validate (as a loaded file can hold)."""

    def __init__(self, **values):
        self.dxf = self
        self._values = values

    def get(self, key, default=None):
        if key not in self._values:
            raise ezdxf.lldxf.const.DXFAttributeError(key)
        return self._values[key]


def test_malformed_invisible_and_thickness_do_not_read_as_drawn() -> None:
    assert dxf_extract._invisible(_Fake()) is False
    assert dxf_extract._invisible(_Fake(invisible="x")) is None
    assert dxf_extract._thickness(_Fake()) == 0.0
    assert math.isnan(dxf_extract._thickness(_Fake(thickness="x")))


def test_a_declined_minsert_cell_names_its_cell() -> None:
    doc = ezdxf.new("R2018")
    doc.blocks.new("B").add_line((0, 0), (1, 0))
    insert = doc.modelspace().add_blockref("B", (0, 0), dxfattribs={"xscale": 2, "yscale": 1})
    insert.grid(size=(1, 2), spacing=(5, 5))
    rows = dxf_extract.extract_document(doc, file_id="cells")
    assert [row["reason"] for row in rows] == [
        "xscale != yscale (MINSERT cell B#0)",
        "xscale != yscale (MINSERT cell B#1)",
    ]


# Each of the totality oracle's named restorations, with its rows spelled out by hand
# rather than by the oracle's copy of the extractor's decisions.
def _restoration(case: str):
    doc = ezdxf.new("R2018", setup=True)
    msp = doc.modelspace()
    doc.blocks.new("B").add_line((0, 0), (1, 0))
    if case == "ATTDEF":
        block = doc.blocks.new("D")
        block.add_line((0, 0), (1, 0))
        block.add_attdef("C", (0, 1), text="c", dxfattribs={"flags": 2})  # constant
        block.add_attdef("V", (0, 2), text="v")  # a template
        msp.add_blockref("D", (0, 0))
        return doc, [("Chord", "LINE"), ("ID_TextEntity", "ATTDEF"), ("ID_TextEntity", "ATTDEF")]
    if case == "stretched":
        msp.add_blockref("B", (0, 0), dxfattribs={"xscale": 2, "yscale": 1})
        return doc, [("ID_NotSimilarityPlacement", "INSERT")]
    if case == "tilted":
        msp.add_blockref("B", (0, 0), dxfattribs={"extrusion": (0, 1, 1)})
        return doc, [("ID_TiltedPlacement", "INSERT")]
    if case == "empty":
        doc.blocks.new("E")
        msp.add_blockref("E", (0, 0))
        return doc, [("ID_DegenerateEntity", "INSERT")]
    if case == "cyclic":
        loop = doc.blocks.new("L")
        loop.add_line((0, 0), (1, 1))
        loop.add_blockref("L", (2, 2))
        msp.add_blockref("L", (0, 0))
        return doc, [("Chord", "LINE"), ("ID_DegenerateEntity", "INSERT")]
    if case == "DIMENSION":
        msp.add_linear_dim(base=(0, 3), p1=(0, 0), p2=(5, 0)).render()
        return doc, [("ID_DimensionEntity", "DIMENSION")]
    if case == "LEADER":
        msp.add_leader([(0, 0), (2, 2), (4, 2)])
        return doc, [("ID_DimensionEntity", "LEADER")]
    raise AssertionError(case)


@pytest.mark.parametrize("case", ["ATTDEF", "stretched", "tilted", "empty", "cyclic", "DIMENSION", "LEADER"])
def test_restorations_by_hand(case: str) -> None:
    doc, expected = _restoration(case)
    seen: list[str] = []
    rows = dxf_extract.extract_document(doc, file_id=case, on_considered=seen.append)
    assert [(row.get("kind") or row["id"], kind) for row, kind in zip(rows, seen)] == expected
