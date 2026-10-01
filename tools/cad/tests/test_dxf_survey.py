"""DXF survey cross-check against the extractor and the carrier schema."""

from __future__ import annotations

import inspect
import json
from pathlib import Path

from jsonschema import Draft202012Validator

import dxf_extract

ROOT = Path(__file__).resolve().parents[1]
SURVEY_PATH = ROOT / "survey" / "dxf.json"
SCHEMA_PATH = ROOT / "survey" / "survey.schema.json"

REQUIRED_TRAPS = {
    "R12 POLYLINE/VERTEX vs R2000 LWPOLYLINE",
    "OCS and extrusion via the arbitrary-axis algorithm",
    "stored angles in degrees CCW, with $ANGDIR/$ANGBASE display-only",
    "bulge sign",
    "ELLIPSE params vs angles",
    "SPLINE flags (closed, periodic, rational)",
    "INSERT scale, rotation and column/row arrays",
    "$INSUNITS=0 unitless",
}


def _one_sentence(note: str) -> None:
    assert "\n" not in note
    assert note.endswith(".")
    assert note.count(".") == 1
    assert "DXF Reference" in note


def test_dxf_survey_cross_checks() -> None:
    schema = json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))
    Draft202012Validator.check_schema(schema)
    survey = json.loads(SURVEY_PATH.read_text(encoding="utf-8"))
    Draft202012Validator(schema).validate(survey)

    carrier = json.loads(dxf_extract.SCHEMA_PATH.read_text(encoding="utf-8"))
    kinds = set(carrier["$defs"]["kind"]["enum"])
    declines = set(carrier["$defs"]["declineId"]["enum"])

    names = [row["entity"] for row in survey["entities"]]
    assert len(names) == len(set(names))
    assert set(names) == set(dxf_extract.HANDLED_ENTITIES)

    traps: set[str] = set()
    for row in survey["entities"]:
        _one_sentence(row["note"])
        assert row["groupCodes"]
        assert "\n" not in row["convention"]
        traps.update(row["traps"])
        if "kind" in row:
            assert row["kind"] in kinds
        if "declineId" in row:
            assert row["declineId"] in declines
        for decline_id in row.get("declineIds", []):
            assert decline_id in declines
        assert "kind" in row or "declineId" in row

    header_source = inspect.getsource(dxf_extract._header_units)
    header_names = []
    for row in survey["headers"]:
        _one_sentence(row["note"])
        traps.update(row.get("traps", []))
        header_names.append(row["name"])
        assert row["name"] in dxf_extract.READ_HEADERS or row["name"] in dxf_extract.IGNORED_HEADERS
    assert len(header_names) == len(set(header_names))

    for name in dxf_extract.READ_HEADERS:
        assert name in header_source
    for name in dxf_extract.IGNORED_HEADERS:
        assert name not in header_source

    assert REQUIRED_TRAPS <= traps
    _one_sentence(survey["dwg"]["note"])
    assert "Open Design Alliance" in survey["dwg"]["note"]
    assert "libredwg" in survey["dwg"]["note"]
    assert "R12 through R2018" in survey["dwg"]["note"]
