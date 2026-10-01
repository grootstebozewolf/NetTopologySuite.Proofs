"""Locked IFC clothoid alignment segment, checked with IfcOpenShell."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

import ifcopenshell
from jsonschema import Draft202012Validator

import dxf_extract
from fixtures.gen_ifc_clothoid import IFC_PATH, JSON_PATH, render

IFC_SHA256 = "6a0879a45799797482daf46d839986ecda31ce195701a1e6ed8b9a5bfcf91f5d"
JSON_SHA256 = "4b5831da925bfa60e1be1b460ddf3c1b83cba008d99ff72c8959d218ad2b922c"

SCHEMA = json.loads(dxf_extract.SCHEMA_PATH.read_text(encoding="utf-8"))
VALIDATOR = Draft202012Validator(SCHEMA)


def test_ifcopenshell_requirement_is_an_exact_pin() -> None:
    text = (Path(__file__).resolve().parents[1] / "requirements.txt").read_text(encoding="utf-8")
    assert "ifcopenshell==0.8.5\n" in text


def test_ifc_clothoid_matches_ifcopenshell_and_is_byte_stable() -> None:
    ifc, payload = render()
    assert hashlib.sha256(IFC_PATH.read_bytes()).hexdigest() == IFC_SHA256
    assert hashlib.sha256(JSON_PATH.read_bytes()).hexdigest() == JSON_SHA256
    assert hashlib.sha256(ifc).hexdigest() == IFC_SHA256
    assert hashlib.sha256(payload).hexdigest() == JSON_SHA256

    model = ifcopenshell.open(IFC_PATH)
    segment = model.by_type("IfcAlignmentHorizontalSegment")
    clothoid = model.by_type("IfcClothoid")
    assert len(segment) == 1
    assert len(clothoid) == 1
    assert segment[0].PredefinedType == "CLOTHOID"
    assert segment[0].StartRadiusOfCurvature is None
    assert segment[0].EndRadiusOfCurvature == 100.0
    assert segment[0].SegmentLength == 25.0
    assert segment[0].StartDirection == 0.0
    assert tuple(segment[0].StartPoint.Coordinates) == (0.0, 0.0)
    assert clothoid[0].ClothoidConstant == 50.0

    record = json.loads(payload)
    VALIDATOR.validate(record)
    assert record["kind"] == "Spiral"
    assert record["params"]["family"] == "clothoid"
    source = record["params"]["source"]
    assert source["predefinedType"] == segment[0].PredefinedType
    assert source["segmentLength"] == segment[0].SegmentLength
    assert source["endRadiusOfCurvature"] == segment[0].EndRadiusOfCurvature
    assert source["clothoidConstant"] == clothoid[0].ClothoidConstant
    assert source["startRadiusOfCurvature"] is None
    note = source["note"]
    assert note.count(".") == 1 and note.endswith(".")
    assert "IfcAlignmentHorizontalSegment" in note
    assert "IFC4X3" in note
