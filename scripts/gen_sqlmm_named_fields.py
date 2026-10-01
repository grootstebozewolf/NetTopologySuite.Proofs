#!/usr/bin/env python3
"""Generate the SQL/MM named-field status table from the claim registry.

Reads scripts/sqlmm_named_fields.json (token inventory) and
docs/verified-claims.md (claimId / Module.v : lemma index).
Present-class rows must have every claimId in the registry.
Writes the table into CONTEXT.md between
<!-- BEGIN generated: sqlmm-named-fields --> and
<!-- END generated -->.
"""

from __future__ import annotations

import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
INV = os.path.join(ROOT, "scripts", "sqlmm_named_fields.json")
REG = os.path.join(ROOT, "docs", "verified-claims.md")
CONTEXT = os.path.join(ROOT, "CONTEXT.md")
BEGIN = "<!-- BEGIN generated: sqlmm-named-fields -->"
END = "<!-- END generated -->"

PRESENT_PREFIXES = ("Present", "Spec present")


def registry_text() -> str:
    with open(REG, encoding="utf-8", errors="replace") as fh:
        return fh.read()


def claim_in_registry(reg: str, claim_id: str) -> bool:
    needles = (
        f"claimId `{claim_id}`",
        f"claimId: {claim_id}",
        f"`{claim_id}`",
        claim_id,
    )
    if any(n in reg for n in needles):
        return True
    # lemma form used when the registry cites the ticket but not the claimId string
    if "mk-nurbs" in claim_id and "ticket_0007_mk_nurbs_qed_or_qex" in reg:
        return True
    return False


def generated_body(inv: dict | None = None, reg: str | None = None) -> str:
    if inv is None:
        with open(INV, encoding="utf-8") as fh:
            inv = json.load(fh)
    if reg is None:
        reg = registry_text()
    missing: list[str] = []
    lines = [
        "**Named-field inventory** (SQL/MM WKT fields, not types):",
        f"Grammar pin {inv['pin']}.",
        "Status is derived from `docs/verified-claims.md` for every cited `claimId`.",
        "",
        "| Token | Status | Consumer |",
        "|---|---|---|",
    ]
    for row in inv["tokens"]:
        token = row["token"]
        iso = row.get("iso") or ""
        label = f"{token} (ISO {iso})" if iso else token
        status = row["status"]
        claims = row.get("claimIds") or []
        if status.startswith(PRESENT_PREFIXES) or (
            claims and not status.startswith("Absent")
        ):
            for cid in claims:
                if not claim_in_registry(reg, cid):
                    missing.append(f"{token}: {cid}")
        consumer = row["consumer"]
        if claims:
            consumer = f"{consumer}; " + ", ".join(f"`{c}`" for c in claims)
        lines.append(f"| {label} | {status} | {consumer} |")
    if missing:
        raise SystemExit(
            "claimId not in docs/verified-claims.md:\n  " + "\n  ".join(missing)
        )
    return "\n".join(lines) + "\n"


def extract_region(context: str) -> str:
    start = context.find(BEGIN)
    end = context.find(END)
    if start < 0 or end < 0 or end < start:
        raise SystemExit(
            f"CONTEXT.md missing {BEGIN} / {END} markers"
        )
    inner = context[start + len(BEGIN) : end]
    if inner.startswith("\n"):
        inner = inner[1:]
    return inner


def splice_region(context: str, body: str) -> str:
    start = context.find(BEGIN)
    end = context.find(END)
    if start < 0 or end < 0 or end < start:
        raise SystemExit(
            f"CONTEXT.md missing {BEGIN} / {END} markers"
        )
    if not body.endswith("\n"):
        body += "\n"
    return context[: start + len(BEGIN)] + "\n" + body + context[end:]


def main() -> int:
    body = generated_body()
    with open(CONTEXT, encoding="utf-8") as fh:
        context = fh.read()
    updated = splice_region(context, body)
    with open(CONTEXT, "w", encoding="utf-8", newline="\n") as fh:
        fh.write(updated)
    print("[sqlmm-named-fields] wrote CONTEXT.md generated region")
    return 0


if __name__ == "__main__":
    sys.exit(main())
