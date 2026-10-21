#!/usr/bin/env python3
"""Statement/proof split guard (claim statements pinned by hash).

A cited claim's statement lives in a statements-only module (`*Stmt.v`):
Definitions of the statement Props and the objects they mention, no proofs.
The proof module proves exactly that constant (`Theorem t : Stmt.claim.`),
so a refactor cannot weaken a cited statement without this gate noticing.
Pattern inspired by the Comparator statement/solution split and
formalization.yaml v0.4 (openai/math@1581d4cb, ideas only).

Registry: docs/claim-statements.json.  For every registered claim:

  stmt.hash       sha256 of the statement module's code (comments stripped,
                  whitespace collapsed) equals `statement_sha256`.  A drift
                  fails; if the change is intended, update the hash together
                  with the claim row (`--hash FILE` prints the value).
  stmt.pure       the statement module has no Lemma/Theorem/Proof/Qed/
                  Admitted/Axiom/Parameter/Hypothesis/Variable/Conjecture/
                  Defined/Admit, and defines each cited constant as
                  `Definition <c> : Prop :=`.
  proof.exact     the proof module states `Theorem|Lemma <proof> : <Stmt>.<c>.`
                  verbatim, and carries `Print Assumptions <proof>.` (the build
                  job's axioms audit checks that output against the allowlist).
  project         both modules are registered in _CoqProject.full.
  row             the claimId and a `<proof module> : <proof>` citation of the
                  main result appear in docs/verified-claims.md.
  meta            scope is main|supporting|witness; review.status is in the
                  v0.4 enum; regime `cond` needs non-empty
                  literature_dependencies, each with a named source.
  orphan          every theories*/ *Stmt.v file is registered.

Exit 0 = all registered claims hold.  Exit 1 = drift or a malformed entry.
Build-independent (no .vo, no rocq), so it runs in `make ci-guards`.
"""

import hashlib
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REGISTRY = os.path.join(ROOT, "docs", "claim-statements.json")
CLAIMS_DOC = os.path.join(ROOT, "docs", "verified-claims.md")
PROJECT = os.path.join(ROOT, "_CoqProject.full")
LANES = ("theories", "theories-flocq")

SCOPES = {"main", "supporting", "witness"}
REVIEW = {"unchecked", "agent-reviewed", "self-assessed", "peer-reviewed",
          "author-verified"}
FORBIDDEN = re.compile(
    r"(?<![\w'.])(Lemma|Theorem|Corollary|Proposition|Fact|Remark|Example|"
    r"Proof|Qed|Admitted|Defined|Abort|Axiom|Axioms|Parameter|Parameters|"
    r"Hypothesis|Hypotheses|Variable|Variables|Conjecture|Admit|admit)(?![\w'])")


def strip_comments(text):
    out, depth, k = [], 0, 0
    while k < len(text):
        if text.startswith("(*", k):
            depth += 1
            k += 2
        elif text.startswith("*)", k) and depth:
            depth -= 1
            k += 2
        else:
            if not depth:
                out.append(text[k])
            k += 1
    return "".join(out)


def code_of(path):
    with open(path, encoding="utf-8") as fh:
        return " ".join(strip_comments(fh.read()).split())


def statement_hash(path):
    return hashlib.sha256(code_of(path).encode("utf-8")).hexdigest()


def registered_modules():
    mods = set()
    with open(PROJECT, encoding="utf-8", errors="replace") as fh:
        for raw in fh:
            line = raw.split("#", 1)[0].strip()
            if line.endswith(".v"):
                mods.add(line)
    return mods


def check_claim(c, mods, doc, errs):
    cid = c.get("claimId", "?")

    def err(rule, msg):
        errs.append("[claim-statements] %s %s: %s" % (rule, cid, msg))

    for key in ("claimId", "statement_module", "statement_sha256",
                "proof_module", "regime", "results", "review"):
        if key not in c:
            err("meta", "missing field `%s`" % key)
            return
    stmt_rel, proof_rel = c["statement_module"], c["proof_module"]
    stmt_path = os.path.join(ROOT, stmt_rel)
    proof_path = os.path.join(ROOT, proof_rel)
    for rel, path in ((stmt_rel, stmt_path), (proof_rel, proof_path)):
        if not os.path.isfile(path):
            err("project", "%s does not exist" % rel)
            return
        if rel not in mods:
            err("project", "%s is not registered in _CoqProject.full" % rel)

    got = statement_hash(stmt_path)
    if got != c["statement_sha256"]:
        err("stmt.hash", "%s drifted (sha256 %s, registry pins %s). If the "
            "change is intended, update statement_sha256 and the claim row in "
            "the same PR." % (stmt_rel, got, c["statement_sha256"]))

    stmt_code = code_of(stmt_path)
    for m in FORBIDDEN.finditer(stmt_code):
        err("stmt.pure", "%s contains `%s`; statement modules hold "
            "Definitions only" % (stmt_rel, m.group(1)))
    stmt_mod = os.path.splitext(os.path.basename(stmt_rel))[0]

    proof_code = code_of(proof_path)
    if not re.search(r"Require Import[^.]*\b%s\b" % re.escape(stmt_mod), proof_code):
        err("proof.exact", "%s does not import %s" % (proof_rel, stmt_mod))
    seen_main = False
    for r in c["results"]:
        scope, const, proof = r.get("scope"), r.get("statement"), r.get("proof")
        if scope not in SCOPES:
            err("meta", "scope `%s` not in %s" % (scope, sorted(SCOPES)))
        seen_main |= scope == "main"
        if not const or not proof:
            err("meta", "result needs `statement` and `proof`")
            continue
        if not const.startswith(stmt_mod + "."):
            err("meta", "statement `%s` is not qualified by %s" % (const, stmt_mod))
            continue
        short = const[len(stmt_mod) + 1:]
        if not re.search(r"(?<![\w'.])Definition %s : Prop :=" % re.escape(short),
                         stmt_code):
            err("stmt.pure", "%s does not define `Definition %s : Prop :=`"
                % (stmt_rel, short))
        if not re.search(r"(?<![\w'.])(Theorem|Lemma) %s : %s\s*\." % (
                re.escape(proof), re.escape(const)), proof_code):
            err("proof.exact", "%s must state `Theorem %s : %s.` verbatim"
                % (proof_rel, proof, const))
        if not re.search(r"Print Assumptions %s\s*\." % re.escape(proof), proof_code):
            err("proof.exact", "%s lacks `Print Assumptions %s.`" % (proof_rel, proof))
        if scope == "main":
            cite = "`%s : %s`" % (os.path.basename(proof_rel), proof)
            if cite not in doc:
                err("row", "docs/verified-claims.md does not cite %s" % cite)
    if not seen_main:
        err("meta", "no result with scope `main`")
    if "`%s`" % cid not in doc:
        err("row", "docs/verified-claims.md does not mention claimId `%s`" % cid)

    status = (c.get("review") or {}).get("status")
    if status not in REVIEW:
        err("meta", "review.status `%s` not in %s" % (status, sorted(REVIEW)))
    deps = c.get("literature_dependencies", [])
    if c["regime"] == "cond":
        if not deps:
            err("meta", "regime `cond` needs literature_dependencies with sources")
        for d in deps:
            if not (isinstance(d, dict) and d.get("statement") and d.get("source")):
                err("meta", "literature dependency needs `statement` and `source`")
    if not isinstance(c.get("fidelity_divergences", []), list):
        err("meta", "fidelity_divergences must be a list")


def main(argv):
    if argv[:1] == ["--hash"] and len(argv) == 2:
        print(statement_hash(argv[1]))
        return 0
    if not os.path.isfile(REGISTRY):
        print("[claim-statements] registry missing: docs/claim-statements.json")
        return 1
    with open(REGISTRY, encoding="utf-8") as fh:
        reg = json.load(fh)
    with open(CLAIMS_DOC, encoding="utf-8", errors="replace") as fh:
        doc = fh.read()
    mods = registered_modules()
    errs = []
    claims = reg.get("claims", [])
    ids = [c.get("claimId") for c in claims]
    for dup in sorted({i for i in ids if ids.count(i) > 1}):
        errs.append("[claim-statements] meta %s: duplicate claimId" % dup)
    for c in claims:
        check_claim(c, mods, doc, errs)
    listed = {c.get("statement_module") for c in claims}
    for lane in LANES:
        base = os.path.join(ROOT, lane)
        for fn in sorted(os.listdir(base)) if os.path.isdir(base) else []:
            rel = "%s/%s" % (lane, fn)
            if fn.endswith("Stmt.v") and rel not in listed:
                errs.append("[claim-statements] orphan %s: statement module not "
                            "in docs/claim-statements.json" % rel)
    if errs:
        print("\n".join(errs))
        return 1
    print("[claim-statements] %d claim(s), %d result(s); statements match their pins."
          % (len(claims), sum(len(c.get("results", [])) for c in claims)))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
