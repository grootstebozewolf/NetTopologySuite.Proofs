#!/usr/bin/env python3
"""CI guard: CONTEXT.md generated region matches a fresh generate."""

from __future__ import annotations

import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))

from gen_sqlmm_named_fields import (  # noqa: E402
    CONTEXT,
    extract_region,
    generated_body,
)


def main() -> int:
    try:
        fresh = generated_body()
        with open(CONTEXT, encoding="utf-8") as fh:
            committed = extract_region(fh.read())
    except SystemExit as exc:
        print(f"[sqlmm-named-fields] FAIL: {exc}")
        return 1
    if fresh != committed:
        print("[sqlmm-named-fields] FAIL: CONTEXT.md region != regenerated")
        print("Run: python3 scripts/gen_sqlmm_named_fields.py")
        return 1
    print("[sqlmm-named-fields] OK: CONTEXT.md generated region matches")
    return 0


if __name__ == "__main__":
    sys.exit(main())
