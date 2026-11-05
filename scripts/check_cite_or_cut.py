#!/usr/bin/env python3
# =============================================================================
# scripts/check_cite_or_cut.py
# -----------------------------------------------------------------------------
# Cite-or-cut (#846 / #931, sharpened for #1007). A gated markdown line that
# says a registered outcome stays QED or QEX must cite that theorem's
# claimId. Otherwise cut the sentence.
#
# Rule shape is the #846 guard, not a new prose classifier:
#   * Scan CONTEXT.md plus every path in docs/gated-prose-docs.txt.
#   * A line is a restatement only when it matches one of:
#       stays QED / stays QEX     (also "stay Qed")
#       Owner already retired #508
#     There is no similarity check against theorem text.
#
# Which claimId is required comes from the registries:
#   * docs/verified-claims.md — a line that carries exactly one claimId
#     binds each `Module.v : name` on that line to that id.
#     `claimId: none` does not bind.
#   * docs/claim-statements.json — each result's proof name binds
#     `basename(proof_module) : proof` to that claim's claimId.
# The first `Module.v : name` on the restatement line is the headline.
#   * exactly one registered claimId → the line must cite that id
#   * several → the line must cite one of them; any other known claimId
#     on the line also passes (a shared headline is not disambiguated)
#   * none, but the line has `Module.v : name` → historical #846 citation
#     stands, because there is no claimId to demand
#   * none and no `Module.v : name` → fail: missing claimId
# A claimId token that is not in either registry does not count.
#
# Citation forms: claimId `id`, claimId: `id`, claimId: id.
#
# Exit 0 ok, 1 hits, 2 usage / registry / selftest error.
#
# Residual false-positive / false-negative risks (no NLP, on purpose):
#   * The trigger is the #846 phrase list. "is QED" without "stays" is
#     not a restatement. A repo-wide scan is not done; eval/README.md
#     "CircGamma stays QEX" lines sit outside the gate file.
#   * The first `Module.v : name` is the headline. A later citation on
#     the same line does not choose the claimId.
#   * An ambiguous headline passes when any known claimId is on the line,
#     including one that belongs to a sibling fact.
#   * A headline with no registry binding still passes on `Module.v : name`
#     alone (claimId: none, or a theorem that never sits on a one-claimId
#     registry line).
#
# License: BSD-3-Clause (see LICENSE)
# AI assistance disclosure: AI-drafted; human review pending.
# =============================================================================

from __future__ import annotations

import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

RESTATE = re.compile(
    r"(?:\bstay(?:s)?\s+QEX\b|\bstay(?:s)?\s+QED\b"
    r"|\bOwner already retired\s+#508\b)",
    re.IGNORECASE,
)
MOD = re.compile(
    r"(?<![\w./-])([A-Za-z0-9_./-]+)\.v\s*:\s*([A-Za-z0-9_']+)"
)
CID = re.compile(
    r"claimId\s*`([^`]+)`"
    r"|claimId\s*:\s*`([^`]+)`"
    r"|claimId\s*:\s*([A-Za-z0-9][A-Za-z0-9._-]*)"
)


def claim_ids(line: str) -> list[str]:
    out: list[str] = []
    for match in CID.finditer(line):
        tok = next(g for g in match.groups() if g).strip()
        if tok.lower() == "none":
            continue
        out.append(tok)
    return out


def headline(line: str) -> tuple[str, str] | None:
    match = MOD.search(line)
    if not match:
        return None
    return os.path.basename(match.group(1)), match.group(2)


def bind_verified_claims(text: str, thm_map: dict, known: set[str]) -> None:
    for line in text.splitlines():
        ids = list(dict.fromkeys(claim_ids(line)))
        for cid in ids:
            known.add(cid)
        if len(ids) != 1:
            continue
        for mod, name in MOD.findall(line):
            thm_map.setdefault((os.path.basename(mod), name), set()).add(ids[0])


def bind_claim_statements(data: dict, thm_map: dict, known: set[str]) -> None:
    for claim in data.get("claims", []):
        cid = claim.get("claimId")
        if not cid or cid == "none":
            continue
        known.add(cid)
        proof_mod = os.path.basename(claim.get("proof_module") or "")
        if proof_mod.endswith(".v"):
            proof_mod = proof_mod[:-2]
        for result in claim.get("results") or []:
            proof = result.get("proof")
            if proof_mod and proof:
                thm_map.setdefault((proof_mod, proof), set()).add(cid)


def load_registry() -> tuple[dict, set[str]]:
    vc_path = os.path.join(ROOT, "docs", "verified-claims.md")
    js_path = os.path.join(ROOT, "docs", "claim-statements.json")
    if not os.path.isfile(vc_path):
        print(f"[cite-or-cut] FAIL: missing {vc_path}", file=sys.stderr)
        raise SystemExit(2)
    if not os.path.isfile(js_path):
        print(f"[cite-or-cut] FAIL: missing {js_path}", file=sys.stderr)
        raise SystemExit(2)
    thm_map: dict = {}
    known: set[str] = set()
    with open(vc_path, encoding="utf-8", errors="replace") as fh:
        bind_verified_claims(fh.read(), thm_map, known)
    try:
        with open(js_path, encoding="utf-8") as fh:
            data = json.load(fh)
    except json.JSONDecodeError as exc:
        print(f"[cite-or-cut] FAIL: {js_path}: {exc}", file=sys.stderr)
        raise SystemExit(2) from exc
    bind_claim_statements(data, thm_map, known)
    if not known:
        print("[cite-or-cut] FAIL: claim registry has no claimIds", file=sys.stderr)
        raise SystemExit(2)
    return thm_map, known


def judge(line: str, thm_map: dict, known: set[str]) -> str | None:
    """Return a failure reason, or None when the line is not a hit."""
    if not RESTATE.search(line):
        return None
    cited = [cid for cid in claim_ids(line) if cid in known]
    head = headline(line)
    expected = thm_map.get(head, set()) if head else set()
    if len(expected) == 1:
        eid = next(iter(expected))
        if eid in cited:
            return None
        mod, name = head
        return (
            f"missing claimId `{eid}` "
            f"(headline `{mod}.v : {name}`)"
        )
    if len(expected) > 1:
        # A shared headline is not disambiguated: any known claimId passes.
        if cited:
            return None
        mod, name = head
        cands = ", ".join(f"`{c}`" for c in sorted(expected))
        return (
            f"missing claimId "
            f"(headline `{mod}.v : {name}` is registered as {cands})"
        )
    if cited or head:
        return None
    unknown = [cid for cid in claim_ids(line) if cid not in known]
    if unknown:
        shown = ", ".join(f"`{c}`" for c in unknown)
        return f"missing claimId ({shown} is not in the claim registry)"
    return "missing claimId (no registered claimId and no `Module.v : name`)"


def scan_paths() -> list[str]:
    paths = ["CONTEXT.md"]
    gate = os.path.join(ROOT, "docs", "gated-prose-docs.txt")
    if os.path.isfile(gate):
        with open(gate, encoding="utf-8", errors="replace") as fh:
            for raw in fh:
                line = raw.split("#", 1)[0].strip()
                if line and line not in paths:
                    paths.append(line)
    return paths


def selftest(thm_map: dict, known: set[str]) -> None:
    fake_map = {
        ("Foo", "bar"): {"aaa"},
        ("Foo", "shared"): {"aaa", "bbb"},
    }
    fake_known = {"aaa", "bbb", "ccc"}
    cases = [
        ("thing stays QEX (`Foo.v : bar`).", "missing claimId `aaa`"),
        ("thing stays QEX (claimId `aaa`; `Foo.v : bar`).", None),
        ("thing stays QEX (`Foo.v : shared`).", "missing claimId"),
        ("thing stays QEX (claimId `ccc`; `Foo.v : shared`).", None),
        ("thing stays QEX (`Foo.v : unknown`).", None),
        ("thing stays QEX.", "missing claimId"),
        ("thing stays QEX (claimId `not-real`).", "not in the claim registry"),
        ("no restatement (`Foo.v : bar`).", None),
        ("Owner already retired #508", "missing claimId"),
        ("stay Qed as hardening (`Oracle.v : thing`).", None),
    ]
    for line, expect in cases:
        got = judge(line, fake_map, fake_known)
        if expect is None:
            if got is not None:
                raise SystemExit(f"[cite-or-cut] selftest fail: {line!r} -> {got}")
        elif got is None or expect not in got:
            raise SystemExit(
                f"[cite-or-cut] selftest fail: {line!r} -> {got!r}, want {expect!r}"
            )
    sample = (
        "| `Foo.v : bar` | meaning (claimId `aaa`) stays out of this sample |\n"
        "topic: x · claimId: bbb · witness: none\n"
        "claimId: none does not bind (`Foo.v : ignored`)\n"
    )
    parsed: dict = {}
    parsed_known: set[str] = set()
    bind_verified_claims(sample, parsed, parsed_known)
    if parsed.get(("Foo", "bar")) != {"aaa"}:
        raise SystemExit(f"[cite-or-cut] selftest bind fail: {parsed}")
    if ("Foo", "ignored") in parsed:
        raise SystemExit("[cite-or-cut] selftest bound claimId: none")
    if "bbb" not in parsed_known or "aaa" not in parsed_known:
        raise SystemExit(f"[cite-or-cut] selftest known fail: {parsed_known}")
    # The real registry must resolve the two headlines this guard cites.
    if thm_map.get(("SqlMmSignedTag", "ticket_sqlmm_factory_emit_qed_or_qex")) != {
        "0007-sqlmm-signed-tag"
    }:
        raise SystemExit("[cite-or-cut] selftest: emit ticket is not uniquely bound")
    if thm_map.get(("IntakeSpiralJtsMap", "ticket_0007_intake_spiral_qed_or_qex")) != {
        "0007-intake-spiral"
    }:
        raise SystemExit("[cite-or-cut] selftest: spiral ticket is not uniquely bound")
    if "0007-sqlmm-signed-tag" not in known:
        raise SystemExit("[cite-or-cut] selftest: registry missing a known claimId")


def main() -> int:
    thm_map, known = load_registry()
    try:
        selftest(thm_map, known)
    except SystemExit as exc:
        if exc.code not in (0, None):
            print(exc, file=sys.stderr)
            return 2
        raise
    if "--selftest" in sys.argv[1:]:
        print(
            f"[cite-or-cut] selftest ok "
            f"({len(known)} claimIds, {len(thm_map)} theorem bindings)"
        )
        return 0

    hits: list[str] = []
    checked = 0
    for rel in scan_paths():
        path = os.path.join(ROOT, rel)
        if not os.path.isfile(path):
            continue
        with open(path, encoding="utf-8", errors="replace") as fh:
            for i, raw in enumerate(fh, 1):
                reason = judge(raw, thm_map, known)
                if reason is None:
                    if RESTATE.search(raw):
                        checked += 1
                    continue
                checked += 1
                snippet = raw.strip()
                if len(snippet) > 220:
                    snippet = snippet[:217] + "..."
                hits.append(f"{rel}:{i}: {reason}\n    {snippet}")
    if hits:
        print("[cite-or-cut] FAIL: restatement without its registered claimId")
        print("Cite that claimId on the same line, or cut the sentence.")
        for hit in hits:
            print(hit)
        print(f"[cite-or-cut] {len(hits)} uncited restatement(s)")
        return 1
    print(
        "[cite-or-cut] OK: every QED/QEX restatement cites its registered "
        f"claimId ({checked} restatement line(s), {len(known)} known claimIds)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
