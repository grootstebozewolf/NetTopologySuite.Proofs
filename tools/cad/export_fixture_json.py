#!/usr/bin/env python3
"""Write one JSON file per record from the in-test DXF drawings.

The cad-carrier workflow runs ``check-jsonschema`` on this directory.
``test_every_output_validates_and_accounts`` still checks the same
records in-process with the jsonschema library.

Assisted-by: Cursor Grok 4.7
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import dxf_extract
from fixtures.gen_ifc_clothoid import json_bytes
from tests.test_dxf_extract import fixture_cases


def write_records(dest: Path) -> int:
    dest.mkdir(parents=True, exist_ok=True)
    count = 0
    for name, doc, mode in fixture_cases():
        rows = dxf_extract.extract_document(doc, mode=mode, file_id="fixture")
        for index, row in enumerate(rows):
            path = dest / f"{name}-{index:02d}.json"
            path.write_text(
                json.dumps(row, allow_nan=False, separators=(",", ":")) + "\n",
                encoding="utf-8",
            )
            count += 1
    (dest / "ifc-clothoid.json").write_bytes(json_bytes())
    return count + 1


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: export_fixture_json.py DEST", file=sys.stderr)
        return 2
    dest = Path(argv[1])
    count = write_records(dest)
    print(f"wrote {count} records to {dest}")
    return 0 if count else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
