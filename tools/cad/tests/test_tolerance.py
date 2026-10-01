"""Tolerance-conversion record against the carrier schema and the extractor."""

from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator

import dxf_extract

ROOT = Path(__file__).resolve().parents[1]
RECORD_PATH = ROOT / "tolerance.json"
SCHEMA_PATH = ROOT / "tolerance.schema.json"

HAUSDORFF = {
    "sagitta": "k*d",
    "segmentCount": "r*(1-cos(abs(deltaTheta)/(2*n)))",
    "angleStep": "r*(1-cos(alpha/2))",
}

SAMPLES = {
    "sagitta": {"kind": "sagitta", "d": 0.01},
    "segmentCount": {"kind": "segmentCount", "n": 8},
    "angleStep": {
        "kind": "angleStep",
        "alpha": 5.0,
        "angleUnit": "degree",
        "direction": "ccw-ocs",
    },
    "sourceDefault": {"kind": "sourceDefault"},
}


def _one_sentence(note: str) -> None:
    assert "\n" not in note
    assert note.endswith(".")
    assert note.count(".") == 1
    assert "The CAD carrier record" in note


def _tolerance_consts(carrier: dict) -> list[str]:
    return [branch["properties"]["kind"]["const"] for branch in carrier["$defs"]["tolerance"]["oneOf"]]


def test_tolerance_conversion_record() -> None:
    schema = json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))
    Draft202012Validator.check_schema(schema)
    record = json.loads(RECORD_PATH.read_text(encoding="utf-8"))
    Draft202012Validator(schema).validate(record)

    carrier = json.loads(dxf_extract.SCHEMA_PATH.read_text(encoding="utf-8"))
    kinds = carrier["$defs"]["kind"]["enum"]
    declines = set(carrier["$defs"]["declineId"]["enum"])
    consts = _tolerance_consts(carrier)

    rows = record["conversions"]
    names = [row["kind"] for row in rows]
    assert names == consts
    assert set(names) == set(consts)

    by_kind = {row["kind"]: row for row in rows}
    assert by_kind["sagitta"]["placement"] == "scales"
    assert by_kind["segmentCount"]["placement"] == "invariant"
    assert by_kind["angleStep"]["placement"] == "invariant"
    assert by_kind["sourceDefault"]["placement"] == "unstated"
    assert by_kind["sourceDefault"]["hausdorff"] is None

    for kind, formula in HAUSDORFF.items():
        assert by_kind[kind]["hausdorff"] == formula

    for row in rows:
        _one_sentence(row["note"])
        if row["placement"] == "invariant":
            assert row["declineId"] == "ID_ToleranceKindUnsupported"
            assert row["declineId"] in declines
            assert set(row["geometryKinds"]) == set(dxf_extract.CIRCULAR_KINDS)
        else:
            assert "declineId" not in row
            assert row["geometryKinds"] == kinds
        for geometry in row["geometryKinds"]:
            assert geometry in kinds
        for geometry in kinds:
            got = dxf_extract._tolerance_ok(geometry, SAMPLES[row["kind"]])
            if geometry in row["geometryKinds"]:
                assert got is None
            else:
                assert got == "ID_ToleranceKindUnsupported"
