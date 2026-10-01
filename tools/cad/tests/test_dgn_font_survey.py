"""DGN and font surveys against the shared survey schema."""

from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator

import dxf_extract

ROOT = Path(__file__).resolve().parents[1]
SCHEMA_PATH = ROOT / "survey" / "survey.schema.json"

DGN_TRAPS = {
    "V7 vs V8 arcs",
    "rotated elliptical-arc parameters",
    "cell placement",
}
FONT_TRAPS = {
    "implied on-curve midpoint",
    "TrueType quadratic vs CFF cubic",
}


def _one_sentence(note: str) -> None:
    assert "\n" not in note
    assert note.endswith(".")
    assert note.count(".") == 1


def _load(name: str) -> dict:
    schema = json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))
    Draft202012Validator.check_schema(schema)
    survey = json.loads((ROOT / "survey" / name).read_text(encoding="utf-8"))
    Draft202012Validator(schema).validate(survey)
    return survey


def test_dgn_survey_names_the_format_traps() -> None:
    survey = _load("dgn.json")
    carrier = json.loads(dxf_extract.SCHEMA_PATH.read_text(encoding="utf-8"))
    kinds = set(carrier["$defs"]["kind"]["enum"])
    declines = set(carrier["$defs"]["declineId"]["enum"])
    traps: set[str] = set()
    for row in survey["entities"]:
        _one_sentence(row["note"])
        assert "Bentley MicroStation DGN" in row["note"]
        assert "groupCodes" not in row
        traps.update(row["traps"])
        if "kind" in row:
            assert row["kind"] in kinds
        if "declineId" in row:
            assert row["declineId"] in declines
    assert traps == DGN_TRAPS
    assert survey["headers"] == []


def test_font_survey_names_curves_units_and_the_implied_point() -> None:
    survey = _load("font.json")
    carrier = json.loads(dxf_extract.SCHEMA_PATH.read_text(encoding="utf-8"))
    kinds = set(carrier["$defs"]["kind"]["enum"])
    traps: set[str] = set()
    for row in survey["entities"]:
        _one_sentence(row["note"])
        assert "groupCodes" not in row
        assert row["kind"] in kinds
        traps.update(row["traps"])
    assert traps == FONT_TRAPS
    assert survey["headers"][0]["name"] == "unitsPerEm"
    _one_sentence(survey["headers"][0]["note"])
    assert "OpenType Specification, head" in survey["headers"][0]["note"]
    glyf = next(row for row in survey["entities"] if row["entity"] == "glyf")
    assert "OpenType Specification, glyf" in glyf["note"]
    charstring = next(row for row in survey["entities"] if row["entity"] == "CharString")
    assert "Adobe Technical Note 5177" in charstring["note"]
