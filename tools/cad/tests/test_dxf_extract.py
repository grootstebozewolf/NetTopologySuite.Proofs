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
    tilted = msp.add_line((0, 0), (1, 0))
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
        and r["kind"] == "Chord"
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
    line = doc.modelspace().add_line((0, 0), (1, 0))
    line.dxf.extrusion = (1, 0, 0)
    rows = dxf_extract.extract_document(doc, mode="strict", file_id="fixture")
    assert rows[0]["id"] == "ID_TiltedPlacement"
    doc.header["$INSUNITS"] = 99
    rows = dxf_extract.extract_document(doc, mode="lenient", file_id="fixture")
    assert rows[0]["id"] == "ID_UnknownUnit"
    doc.header["$INSUNITS"] = 0
    doc.header["$ANGDIR"] = 7
    rows = dxf_extract.extract_document(doc, mode="strict", file_id="fixture")
    assert rows[0]["id"] == "ID_AngleConventionUnknown"


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


def test_arc_end_before_start_is_kept_raw() -> None:
    doc = ezdxf.new("R2010")
    doc.modelspace().add_arc((1, 2), radius=3, start_angle=350, end_angle=10)
    rows = dxf_extract.extract_document(doc, mode="strict", file_id="fixture")
    assert rows[0]["record"] == "entity"
    assert rows[0]["params"]["startAngle"] == 350
    assert rows[0]["params"]["endAngle"] == 10
    assert rows[0]["params"]["direction"] == "ccw-ocs"
    VALIDATOR.validate(rows[0])


def test_scratch_gate_must_fail():
    assert False, "scratch: gate fail-path probe"
