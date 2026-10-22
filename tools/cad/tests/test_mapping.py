"""The year-0 source-to-carrier mapping."""

from __future__ import annotations

import json
import re
from pathlib import Path

from jsonschema import Draft202012Validator

ROOT = Path(__file__).resolve().parents[3]
MAPPING_PATH = ROOT / "tools" / "cad" / "mapping.json"
MAPPING_SCHEMA_PATH = ROOT / "tools" / "cad" / "mapping.schema.json"
CARRIER_SCHEMA_PATH = ROOT / "tools" / "cad" / "carrier.schema.json"

CLAIM_ID = re.compile(r'"claimId"\s*:\s*"([^"]+)"')


def _registry_claim_ids() -> set[str]:
    found: set[str] = set()
    for folder in ("theories", "theories-flocq", "eval"):
        for path in (ROOT / folder).rglob("*.v"):
            found.update(CLAIM_ID.findall(path.read_text(encoding="utf-8", errors="replace")))
    return found


def test_mapping_validates_and_kinds_and_claim_ids_resolve() -> None:
    schema = json.loads(MAPPING_SCHEMA_PATH.read_text(encoding="utf-8"))
    Draft202012Validator.check_schema(schema)
    mapping = json.loads(MAPPING_PATH.read_text(encoding="utf-8"))
    Draft202012Validator(schema).validate(mapping)

    kinds = set(json.loads(CARRIER_SCHEMA_PATH.read_text(encoding="utf-8"))["$defs"]["kind"]["enum"])
    registry = _registry_claim_ids()
    assert "0007-arc-linearize" in registry

    seen: set[tuple[str, str]] = set()
    for row in mapping["rows"]:
        key = (row["source"]["format"], row["source"]["entity"])
        assert key not in seen
        seen.add(key)
        if row["kind"] is not None:
            assert row["kind"] in kinds
        if row["claimId"] is not None:
            assert row["claimId"] in registry
        if row["linearizer"] == "arc_linearizes":
            assert row["egg"] == "MkCirc"
        if "declineId" in row:
            assert row["declineId"] in set(json.loads(CARRIER_SCHEMA_PATH.read_text(encoding="utf-8"))["$defs"]["declineId"]["enum"])
            assert row["kind"] is None
    assert "0007-clothoid-linearize" in registry
    assert "0007-bezier-linearize" not in registry
    by_source = {(row["source"]["format"], row["source"]["entity"]): row for row in mapping["rows"]}
    assert by_source[("DXF", "closed LWPOLYLINE")]["kind"] == "Ring"
    assert by_source[("DXF", "2D POLYLINE chain")]["kind"] == "Compound"
    assert by_source[("TrueType", "quadratic Bezier span")]["claimId"] is None
    clothoid = by_source[("IFC", "clothoid alignment segment")]
    assert clothoid["linearizer"] == "clothoid_linearizes"
    assert clothoid["claimId"] is None
    for name in ("Bloss curve", "sine curve", "cosine curve"):
        assert by_source[("IFC", name)]["declineId"] == "ID_SpiralFamilyUnsupported"
