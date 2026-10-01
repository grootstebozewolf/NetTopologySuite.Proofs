#!/usr/bin/env python3
"""Cite-or-cut: prose that restates a Qed/QEX theorem must cite it.

Standing guard for #846. A markdown line that says a registered outcome
is QED or QEX (or the retired dual “Owner already retired #508”) must
carry that theorem's `Module.v : name` citation or a `claimId`.

Scan: CONTEXT.md plus every path in docs/gated-prose-docs.txt.
Exit 0 if every restatement cites; exit 1 and print the hits otherwise.
"""

from __future__ import annotations

import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

RESTATE = re.compile(
    r"(?:\bstay(?:s)?\s+QEX\b|\bstay(?:s)?\s+QED\b"
    r"|\bOwner already retired\s+#508\b)",
    re.IGNORECASE,
)
CITE = re.compile(
    r"[A-Za-z0-9_./-]+\.v\s*:\s*[A-Za-z0-9_']+|claimId\s*`[^`]+`"
)


def scan_paths() -> list[str]:
    paths = [os.path.join(ROOT, "CONTEXT.md")]
    gate = os.path.join(ROOT, "docs", "gated-prose-docs.txt")
    if os.path.isfile(gate):
        with open(gate, encoding="utf-8", errors="replace") as fh:
            for raw in fh:
                line = raw.split("#", 1)[0].strip()
                if line:
                    paths.append(os.path.join(ROOT, line))
    return paths


def main() -> int:
    hits: list[str] = []
    for path in scan_paths():
        if not os.path.isfile(path):
            continue
        rel = os.path.relpath(path, ROOT)
        with open(path, encoding="utf-8", errors="replace") as fh:
            for i, raw in enumerate(fh, 1):
                if not RESTATE.search(raw):
                    continue
                if CITE.search(raw):
                    continue
                hits.append(f"{rel}:{i}: {raw.rstrip()}")
    if hits:
        print("[cite-or-cut] FAIL: restatement without claimId / Module.v : name")
        for h in hits:
            print(h)
        print(f"[cite-or-cut] {len(hits)} uncited restatement(s)")
        return 1
    print("[cite-or-cut] OK: every QED/QEX restatement cites its theorem")
    return 0


if __name__ == "__main__":
    sys.exit(main())
