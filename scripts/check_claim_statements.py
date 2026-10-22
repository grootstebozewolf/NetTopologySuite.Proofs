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
  proof.pure      the proof module (comments stripped) has no Admitted /
                  admit / Axiom / Parameter / Hypothesis / Variable /
                  Context / Conjecture / Abort, in any spelling (one-line
                  `Proof. Admitted.`, `Local Axiom`, `#[local] Axiom`).  The
                  statement module additionally may not open a Section or a
                  Context.

Exit 0 = all registered claims hold.  Exit 1 = drift or a malformed entry.
The default mode is build-independent (no .vo, no rocq) and runs in
`make ci-guards`.

`--elaborate` (needs the built .vo files; CI runs it in the rocq-flocq job
right after the corpus compile) generates a Rocq probe per claim under
.claim-probe/ and checks what the kernel says, not what the text says:

  elab.type       `Check (proof : Stmt.c)` compiles, and the printed type of
                  `proof` (Printing All, fully qualified) is literally
                  `<Stmt>.c`.  A Section Hypothesis turns it into `H -> c`
                  and fails here.
  elab.assume     `Print Assumptions proof` lists only the three allowlisted
                  axioms by their fully qualified Stdlib names.  A one-line
                  `Proof. Admitted.` shows up as an undotted axiom `proof`, a
                  `Local Axiom` as `NTS.Proofs.<M>.<name>`; both fail.  Any
                  unparsed line in the block fails closed.
  elab.hash       the elaborated statement is pinned: `Print` (Printing All,
                  fully qualified) of every statement constant and of every
                  NTS.Proofs definition they reach, transitively, hashed into
                  `elaborated_sha256`.  An imported Notation that changes
                  what the conjunction means, or an edit to `on_arc` upstream, leaves
                  the source hash unchanged and changes this one.
                  `--elaborate --print-hash` prints the value.

ROCQ_CMD overrides the rocq launcher (default `rocq`), e.g.
`ROCQ_CMD="docker run --rm -v $PWD:/workspace -w /workspace IMG rocq"`.
"""

import hashlib
import json
import os
import re
import shlex
import subprocess
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
    r"Hypothesis|Hypotheses|Variable|Variables|Conjecture|Admit|admit|"
    r"Section|Context)(?![\w'])")
# In a proof module these never stand in for a proof of a pinned claim.
PROOF_FORBIDDEN = re.compile(
    r"(?<![\w'.])(Admitted|admit|give_up|Abort|Axiom|Axioms|Parameter|"
    r"Parameters|Hypothesis|Hypotheses|Variable|Variables|Context|"
    r"Conjecture)(?![\w'])")
# Fully qualified names of docs/axiom-allowlist.txt, as Rocq 9.2 prints them.
ALLOWED_AXIOMS = {
    "ClassicalDedekindReals.sig_not_dec":
        "Stdlib.Reals.ClassicalDedekindReals.sig_not_dec",
    "ClassicalDedekindReals.sig_forall_dec":
        "Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec",
    "FunctionalExtensionality.functional_extensionality_dep":
        "Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep",
}
PROBE_DIR = os.path.join(ROOT, ".claim-probe")
NAME_RE = re.compile(r"NTS\.Proofs(?:\.[A-Za-z_][\w']*)+")


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
                "elaborated_sha256", "proof_module", "regime", "results", "review"):
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
    for m in PROOF_FORBIDDEN.finditer(proof_code):
        err("proof.pure", "%s contains `%s`; a pinned claim's proof module "
            "may not use it" % (proof_rel, m.group(1)))
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


# ---------------------------------------------------------------------------
# --elaborate: kernel-level checks on the built .vo files.
# ---------------------------------------------------------------------------

def logical_name(rel):
    lane, fn = rel.split("/", 1)
    mod = os.path.splitext(fn)[0]
    return ("NTS.Proofs.Flocq." if lane == "theories-flocq" else "NTS.Proofs.") + mod


def project_flags():
    flags = []
    with open(PROJECT, encoding="utf-8", errors="replace") as fh:
        for raw in fh:
            toks = shlex.split(raw.split("#", 1)[0])
            if toks and toks[0] in ("-Q", "-R") and len(toks) >= 3:
                flags += toks[:3]
    return flags


def run_probe(name, body):
    os.makedirs(PROBE_DIR, exist_ok=True)
    os.chmod(PROBE_DIR, 0o777)   # CI: the container's rocq user writes .vo
    path = os.path.join(PROBE_DIR, "%s.v" % name)
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(body)
    rel = os.path.relpath(path, ROOT)
    cmd = shlex.split(os.environ.get("ROCQ_CMD", "rocq")) + ["c"] + \
        project_flags() + [rel]
    p = subprocess.run(cmd, cwd=ROOT, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, universal_newlines=True)
    return p.returncode, p.stdout


def mark(tag):
    return 'Goal True. idtac "@@%s". Abort.\n' % tag


def sections(out):
    """Split probe output on @@ markers -> {tag: text}."""
    res, cur, buf = {}, None, []
    for line in out.splitlines():
        if line.startswith("@@"):
            if cur is not None:
                res[cur] = "\n".join(buf)
            cur, buf = line[2:].strip(), []
        elif cur is not None:
            buf.append(line)
    if cur is not None:
        res[cur] = "\n".join(buf)
    return res


def norm(text):
    return " ".join(text.split())


def parse_assumptions(text):
    """-> (axioms, problems).  Fail closed on anything unrecognised."""
    axioms, problems = [], []
    lines = [l for l in text.splitlines() if l.strip()]
    if not lines:
        return axioms, ["empty Print Assumptions output"]
    if norm(lines[0]) == "Closed under the global context" and len(lines) == 1:
        return axioms, problems
    if lines[0].strip() != "Axioms:":
        return axioms, ["unexpected Print Assumptions header `%s`" % lines[0]]
    for l in lines[1:]:
        if l[:1].isspace():
            continue          # continuation of the previous axiom's type
        m = re.match(r"^([A-Za-z_][\w'.]*)\s+:(\s|$)", l)
        if m:
            axioms.append(m.group(1))
        else:
            problems.append("unparsed line in Axioms block: `%s`" % l)
    return axioms, problems


def head(*mods):
    return "".join("Require %s.\n" % m for m in mods) + (
        "Set Printing All.\nSet Printing Fully Qualified.\n"
        "Set Printing Width 100000.\n")


def elaborated_closure(cid, stmt_ln, consts, errs):
    """Print every statement constant and every NTS.Proofs name it reaches."""
    seen, frontier, prints, rnd = set(), list(consts), {}, 0
    while frontier:
        rnd += 1
        if rnd > 64:
            errs.append("[claim-statements] elab.hash %s: closure did not "
                        "converge" % cid)
            return None
        body = head(stmt_ln)          # the statement alone, not the proof
        for c in frontier:
            body += mark("DEF %s" % c) + "Print %s.\n" % c
        rc, out = run_probe("Closure_%s_%d" % (re.sub(r"\W", "_", cid), rnd),
                            body)
        if rc != 0:
            errs.append("[claim-statements] elab.hash %s: closure probe failed "
                        "(rc %d):\n%s" % (cid, rc, out[-2000:]))
            return None
        sec = sections(out)
        seen.update(frontier)
        nxt = set()
        for c in frontier:
            txt = sec.get("DEF %s" % c)
            if txt is None:
                errs.append("[claim-statements] elab.hash %s: no Print output "
                            "for %s" % (cid, c))
                return None
            prints[c] = norm(txt)
            nxt.update(n for n in NAME_RE.findall(txt) if n not in seen)
        frontier = sorted(nxt)
    blob = "\n".join("%s\n%s" % (c, prints[c]) for c in sorted(prints))
    return hashlib.sha256(blob.encode("utf-8")).hexdigest(), len(prints)


def elaborate_claim(c, errs, print_hash):
    cid = c.get("claimId", "?")
    stmt_rel, proof_rel = c["statement_module"], c["proof_module"]
    stmt_ln, proof_ln = logical_name(stmt_rel), logical_name(proof_rel)
    stmt_mod = os.path.splitext(os.path.basename(stmt_rel))[0]

    def err(rule, msg):
        errs.append("[claim-statements] %s %s: %s" % (rule, cid, msg))

    consts = ["%s.%s" % (stmt_ln, r["statement"][len(stmt_mod) + 1:])
              for r in c["results"]]
    got = elaborated_closure(cid, stmt_ln, consts, errs)
    if got is not None:
        h, n = got
        if print_hash:
            print("%s %s (%d constants)" % (cid, h, n))
        elif h != c.get("elaborated_sha256"):
            err("elab.hash", "elaborated statement drifted (sha256 %s over %d "
                "constants, registry pins %s). An imported Notation or an "
                "upstream definition changed what the statement means. If "
                "intended, update elaborated_sha256 and the claim row."
                % (h, n, c.get("elaborated_sha256")))
    if print_hash:
        return
    body = head(stmt_ln, proof_ln)
    for i, r in enumerate(c["results"]):
        short = r["statement"][len(stmt_mod) + 1:]
        fq_stmt = "%s.%s" % (stmt_ln, short)
        fq_proof = "%s.%s" % (proof_ln, r["proof"])
        body += mark("TYPE %d" % i) + "Check %s.\n" % fq_proof
        body += mark("CONV %d" % i) + "Check (%s : %s).\n" % (fq_proof, fq_stmt)
        body += mark("PA %d" % i) + "Print Assumptions %s.\n" % fq_proof
    body += mark("END")
    rc, out = run_probe("Claim_%s" % re.sub(r"\W", "_", cid), body)
    if rc != 0:
        err("elab.type", "probe failed to compile (rc %d); a proof whose type "
            "is not convertible to its statement fails here:\n%s"
            % (rc, out[-2000:]))
        return
    sec = sections(out)
    for i, r in enumerate(c["results"]):
        short = r["statement"][len(stmt_mod) + 1:]
        fq_stmt = "%s.%s" % (stmt_ln, short)
        fq_proof = "%s.%s" % (proof_ln, r["proof"])
        typ = norm(sec.get("TYPE %d" % i, ""))
        want = "%s : %s" % (fq_proof, fq_stmt)
        if typ != want:
            err("elab.type", "`%s` has elaborated type `%s`, not exactly `%s` "
                "(a Section Hypothesis/Variable or extra premise changes it)"
                % (r["proof"], typ, fq_stmt))
        axioms, problems = parse_assumptions(sec.get("PA %d" % i, ""))
        for p in problems:
            err("elab.assume", "%s: %s" % (r["proof"], p))
        allowed = set(ALLOWED_AXIOMS.values())
        for a in axioms:
            if a not in allowed:
                err("elab.assume", "`%s` depends on `%s`, which is not an "
                    "allowlisted axiom (an Admitted proof prints as an "
                    "undotted axiom; a Local Axiom as NTS.Proofs.*)"
                    % (r["proof"], a))


def elaborate_main(argv):
    print_hash = "--print-hash" in argv
    with open(REGISTRY, encoding="utf-8") as fh:
        reg = json.load(fh)
    with open(os.path.join(ROOT, "docs", "axiom-allowlist.txt"),
              encoding="utf-8") as fh:
        listed = {l.strip() for l in fh if l.strip() and not l.startswith("#")}
    errs = []
    if listed != set(ALLOWED_AXIOMS):
        errs.append("[claim-statements] elab.assume: docs/axiom-allowlist.txt "
                    "(%s) differs from the guard's pinned set; update both "
                    "together" % sorted(listed))
    for c in reg.get("claims", []):
        elaborate_claim(c, errs, print_hash)
    if errs:
        print("\n".join(errs))
        return 1
    if not print_hash:
        print("[claim-statements] --elaborate: %d claim(s) checked against the "
              "kernel (exact types, allowlisted assumptions, elaborated pins)."
              % len(reg.get("claims", [])))
    return 0


def main(argv):
    if argv[:1] == ["--elaborate"]:
        return elaborate_main(argv[1:])
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
