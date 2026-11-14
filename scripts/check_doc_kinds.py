#!/usr/bin/env python3
# =============================================================================
# scripts/check_doc_kinds.py
# -----------------------------------------------------------------------------
# Typed-doc ratchet. Replaces the net-line-count-only md-prose ratchet
# (check_md_prose_ratchet.sh, #1007). The ratchet is on what goes wrong
# (drift, sprawl, stale conclusions), not on volume.
#
# Every tracked *.md starts with a doc-kind header (an HTML comment, so it
# does not render):
#
#   <!-- doc-kind: guide -->                      how-tos, README, AGENTS.md
#   <!-- doc-kind: ledger -->                     verified-claims.md, eval/README.md
#   <!-- doc-kind: finding                        dated, append-only history
#   date: 2026-11-14
#   Provenance: <commit sha in this repo's history>
#   Theorems: `Mod.v : name`, `Other.v : name2`   (or: none — <reason>)
#   Supersedes: docs/old-finding.md               (optional, repeatable)
#   -->
#
# STATE checks (whole tree, every run):
#   header      every tracked or untracked-unignored *.md has a valid header.
#   anchors     in guide and ledger docs, every `Mod.v : name` resolves to a
#               definition in a tracked .v file, and every bare `Mod.v` /
#               `dir/Mod.v` / `Mod.v:LINE` names a tracked .v file (a path
#               whose first directory is not in this repo, e.g. Flocq's
#               `Pff/Pff2Flocq.v`, is external and skipped). Tokens that do
#               not resolve on purpose are declared in
#               docs/doc-anchor-baseline.txt as `path<TAB>token<TAB>reason`,
#               reason one of `planned` (a module not written yet),
#               `external` (another repo), `dead` (drift not yet fixed). A
#               listed token that resolves or is gone fails until its line is
#               deleted. Findings are not re-anchored at HEAD: they are
#               checked once, when added.
#   same-PR     AGENTS.md's header carries `doc-kinds-sha256:` = sha256 of
#               the HASHED files (this script, check_ledger_assumptions.py,
#               .github/workflows/doc-kinds.yml), and AGENTS.md has a
#               `- Doc kinds (` bullet describing them.
#
# DIFF checks (PR diff vs base; skipped on push / no base):
#   finding immutable  a file that is `finding` at base may only be renamed
#               unchanged, or gain `> Superseded-by: <path>` lines. Edits and
#               deletions fail. Supersede with a new finding instead.
#   new finding  date is YYYY-MM-DD; Provenance is a commit that is an
#               ancestor of HEAD; every Theorems anchor resolves in the tree
#               being merged; the body has a SUMMARY or OUTCOME line; every
#               Supersedes target is a finding at HEAD carrying
#               `> Superseded-by: <this file>`.
#   superseded-by  every added `> Superseded-by: X` names a finding at HEAD
#               whose Supersedes lists this file.
#   baseline    a line added to docs/doc-anchor-baseline.txt with reason
#               `dead` fails: fix the anchor. `dead` lines only shrink. (The
#               diff that creates the file is the bootstrap and may add them.)
#   same-PR     when a HASHED file differs from base, the AGENTS.md
#               `- Doc kinds (` bullet must differ too (whitespace-only
#               edits do not count). Bumping the hash alone fails.
#   guide budget  net non-blank lines <= 0 over guide and ledger files.
#               Exempt (reported): header lines; `|` table rows; claim rows
#               in ledgers (`|` rows and `topic: … claimId:` stamps); the
#               `## Status (YYYY-MM-DD):` line in docs/thm13-priest-route.md;
#               `> Superseded-by:` pointer lines. Findings are not counted.
#
# Migration: a file whose base version has no header may gain one in the
# same PR without the finding-only rules; such legacy findings carry
# `Provenance: pre-ratchet`. `pre-ratchet` is refused on any finding that
# is new in the diff.
#
# Override (PR only): label `ratchet-override` plus a line
# `Ratchet-Override-Reason: <text>` in the PR body turns every failure into
# a warning. The label without a reason fails. Read from $GITHUB_EVENT_PATH.
#
# Usage:
#   check_doc_kinds.py [BASE]   BASE default: $DOC_KINDS_BASE, else
#                               origin/$GITHUB_BASE_REF, else origin/main
#   check_doc_kinds.py --selftest   fixture repo in a temp dir
#   check_doc_kinds.py --print-hash value for AGENTS.md's header
#
# Exit: 0 ok/skip · 1 violation · 2 usage / git error / selftest failure.
#
# License: BSD-3-Clause (see LICENSE)
# AI assistance disclosure: AI-drafted; human review pending.
# =============================================================================

import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile

TAG = "[doc-kinds]"
KINDS = ("finding", "ledger", "guide")
LEDGER_ROW_FILES = {"docs/verified-claims.md", "eval/README.md"}
ROUTE_STATUS = {
    "docs/thm13-priest-route.md": re.compile(r"^## Status \(\d{4}-\d{2}-\d{2}\): \S"),
}
TOPIC_CLAIM = re.compile(r"^topic:\s+\S.*\bclaimId\s*:")
SUPERSEDED_BY = re.compile(r"^>\s*\**Superseded-by:?\**:?\s*(.+?)\s*$")
SUMMARY_LINE = re.compile(r"^\W*(SUMMARY|OUTCOME)\b", re.M)
DATE = re.compile(r"^\d{4}-\d{2}-\d{2}$")
SHA = re.compile(r"^[0-9a-f]{7,40}$")
ANCHOR = re.compile(r"`([A-Za-z0-9_]+\.v)\s*:\s*([A-Za-z0-9_'{},]+)`")
FILE_REF = re.compile(r"`((?:[\w.-]+/)*)([A-Za-z0-9_]+\.v)(?::\d+(?:-\d+)?)?`")
DEF = re.compile(
    r"^\s*(?:#\[[^\]]*\]\s*)?(?:(?:Local|Global|Program|Polymorphic|"
    r"Monomorphic|Private)\s+)*(?:Theorem|Lemma|Corollary|Definition|Fact|"
    r"Example|Property|Remark|Proposition|Inductive|CoInductive|Fixpoint|"
    r"CoFixpoint|Record|Structure|Class|Instance|Let|Variant|Axiom|Parameter|"
    r"Conjecture|Hypothesis|Variable|Notation|Ltac|Module|Section)\s+"
    r"([A-Za-z_][\w']*)", re.M)
CTOR = re.compile(r"\|\s*([A-Za-z_][\w']*)\s*(?::|\n|\||\.)")
FIELD = re.compile(r"[{;]\s*([A-Za-z_][\w']*)\s*:")
BASELINE = "docs/doc-anchor-baseline.txt"
HASHED = ("scripts/check_doc_kinds.py", "scripts/check_ledger_assumptions.py",
          ".github/workflows/doc-kinds.yml")
BULLET = "- Doc kinds ("
OVERRIDE_LABEL = "ratchet-override"
OVERRIDE_REASON = re.compile(r"^Ratchet-Override-Reason:\s*(\S.*)$", re.M)


# --------------------------------------------------------------------------
# git / io helpers (all relative to `root`)
# --------------------------------------------------------------------------
def git(root, *args, check=True):
    p = subprocess.run(["git", *args], cwd=root, stdout=subprocess.PIPE,
                       stderr=subprocess.PIPE, universal_newlines=True,
                       errors="replace")
    if check and p.returncode != 0:
        raise RuntimeError("git %s: %s" % (" ".join(args), p.stderr.strip()))
    return p.stdout if check else (p.returncode, p.stdout)


def show(root, rev, path):
    rc, out = git(root, "show", "%s:%s" % (rev, path), check=False)
    return out if rc == 0 else None


def read(root, path):
    try:
        with open(os.path.join(root, path), encoding="utf-8",
                  errors="replace") as fh:
            return fh.read()
    except OSError:
        return None


def md_files(root):
    out = git(root, "ls-files", "--cached", "--others", "--exclude-standard",
              "--", "*.md")
    return sorted(p for p in set(out.split("\n")) if p and
                  os.path.isfile(os.path.join(root, p)))


# --------------------------------------------------------------------------
# header
# --------------------------------------------------------------------------
class Header:
    def __init__(self, kind, fields, nlines):
        self.kind, self.fields, self.nlines = kind, fields, nlines

    def get(self, key):
        return self.fields.get(key.lower(), [])


def parse_header(text):
    """-> (Header, None) or (None, error)."""
    if text is None:
        return None, "unreadable"
    lines = text.split("\n")
    m = re.match(r"^<!--\s*doc-kind:\s*([a-z]+)\s*(-->)?\s*$", lines[0])
    if not m:
        return None, "first line is not `<!-- doc-kind: <kind> ... -->`"
    kind = m.group(1)
    if kind not in KINDS:
        return None, "unknown doc-kind `%s` (want %s)" % (kind, "|".join(KINDS))
    fields = {}
    n = 1
    if not m.group(2):
        while True:
            if n >= len(lines):
                return None, "header comment is not closed with `-->`"
            ln = lines[n].strip()
            n += 1
            if ln == "-->":
                break
            fm = re.match(r"^([A-Za-z][\w-]*):\s*(.*)$", ln)
            if not fm:
                return None, "header line %d is not `Key: value`: %r" % (n, ln)
            fields.setdefault(fm.group(1).lower(), []).append(fm.group(2).strip())
    return Header(kind, fields, n), None


# --------------------------------------------------------------------------
# symbol index (build-free) for anchors
# --------------------------------------------------------------------------
TOP_DIRS = set()


def symbol_index(root, rev=None):
    """{basename.v: {path: set(names)}} from tracked .v files (at rev, or
    the working tree when rev is None)."""
    if rev is None:
        paths = [p for p in git(root, "ls-files", "--", "*.v").split("\n") if p]
    else:
        paths = [p for p in git(root, "ls-tree", "-r", "--name-only", rev)
                 .split("\n") if p.endswith(".v")]
    files = git(root, "ls-files") if rev is None else \
        git(root, "ls-tree", "-r", "--name-only", rev)
    TOP_DIRS.update(p.split("/", 1)[0] for p in files.split("\n") if "/" in p)
    idx = {}
    for p in paths:
        src = read(root, p) if rev is None else show(root, rev, p)
        if src is None:
            continue
        names = set(DEF.findall(src))
        names.update(CTOR.findall(src))
        names.update(FIELD.findall(src))
        idx.setdefault(os.path.basename(p), {})[p] = names
    return idx


def expand(name):
    if "{" not in name:
        return [name]
    stem, rest = name.split("{", 1)
    opts, tail = rest.split("}", 1) if "}" in rest else (rest, "")
    return [stem + o.strip() + tail for o in opts.split(",")]


def dead_anchors(text, idx):
    """-> list of dead anchor tokens (deduplicated, in order)."""
    dead = []
    for m in ANCHOR.finditer(text):
        base, name = m.group(1), m.group(2)
        if name.isdigit():
            if base not in idx:
                dead.append(m.group(0))
            continue
        paths = idx.get(base)
        if not paths:
            dead.append(m.group(0))
            continue
        for nm in expand(name):
            if not any(nm in s for s in paths.values()):
                dead.append("`%s : %s`" % (base, nm))
    for m in FILE_REF.finditer(text):
        top = m.group(1).split("/", 1)[0]
        if top and top not in TOP_DIRS:
            continue          # another project's path (Flocq, Stdlib, ...)
        if m.group(2) not in idx:
            dead.append(m.group(0))
    seen, out = set(), []
    for d in dead:
        if d not in seen:
            seen.add(d)
            out.append(d)
    return out


BASELINE_REASONS = ("planned", "external", "dead")


def parse_baseline(txt, errs=None):
    """-> {(path, token): reason}."""
    out = {}
    for i, ln in enumerate((txt or "").split("\n"), 1):
        if not ln.strip() or ln.startswith("#"):
            continue
        parts = ln.split("\t")
        if len(parts) != 3 or parts[2] not in BASELINE_REASONS:
            if errs is not None:
                errs.append("anchor: %s:%d is not `path<TAB>token<TAB>%s`"
                            % (BASELINE, i, "|".join(BASELINE_REASONS)))
            continue
        out[(parts[0], parts[1])] = parts[2]
    return out


def load_baseline(root, errs=None):
    return parse_baseline(read(root, BASELINE), errs)


def scripts_hash(root, rev=None):
    h = hashlib.sha256()
    for p in HASHED:
        txt = read(root, p) if rev is None else show(root, rev, p)
        h.update(p.encode())
        h.update(b"\0")
        h.update((txt or "").encode())
        h.update(b"\0")
    return h.hexdigest()


def agents_bullet(text):
    """The AGENTS.md `- Doc kinds (` list item, whitespace-normalised, or
    None. The item runs until the next line that is not indented."""
    lines = (text or "").split("\n")
    for i, ln in enumerate(lines):
        if ln.startswith(BULLET):
            item = [ln]
            for nxt in lines[i + 1:]:
                if not nxt.startswith("  ") or not nxt.strip():
                    break
                item.append(nxt)
            return " ".join(" ".join(item).split())
    return None


def same_pr_check(root, base, errs):
    if all(show(root, base, p) is None for p in HASHED):
        return                      # bootstrap: nothing to compare against
    changed = [p for p in HASHED if show(root, base, p) != show(root, "HEAD", p)]
    if not changed:
        return
    old_b = agents_bullet(show(root, base, "AGENTS.md"))
    new_b = agents_bullet(show(root, "HEAD", "AGENTS.md"))
    if new_b is None or old_b == new_b:
        errs.append("same-PR: %s changed but AGENTS.md's `%s…` bullet did "
                    "not; describe the change there in this PR (bumping "
                    "`doc-kinds-sha256` alone is not enough)"
                    % (", ".join(changed), BULLET))


# --------------------------------------------------------------------------
# state checks
# --------------------------------------------------------------------------
def state_checks(root, errs, notes, hashed=True):
    headers = {}
    for p in md_files(root):
        h, err = parse_header(read(root, p))
        if err:
            errs.append("header: %s: %s" % (p, err))
            continue
        headers[p] = h
        if h.kind == "finding":
            for key in ("date", "provenance", "theorems"):
                if not h.get(key):
                    errs.append("header: %s: finding lacks `%s:`" % (p, key.capitalize()))
    idx = symbol_index(root)
    baseline = load_baseline(root, errs)
    live = set()
    for p, h in sorted(headers.items()):
        if h.kind == "finding":
            continue
        for tok in dead_anchors(read(root, p), idx):
            live.add((p, tok))
            if (p, tok) not in baseline:
                errs.append("anchor: %s: %s does not resolve to a tracked "
                            ".v definition" % (p, tok))
    for p, tok in sorted(set(baseline) - live):
        errs.append("anchor: %s lists %s\t%s, which no longer dangles; "
                    "delete that line" % (BASELINE, p, tok))
    if baseline:
        by = {}
        for v in baseline.values():
            by[v] = by.get(v, 0) + 1
        notes.append("anchors: %s declared non-resolving in %s" % (
            ", ".join("%d %s" % (n, k) for k, n in sorted(by.items())), BASELINE))
    if hashed:
        if agents_bullet(read(root, "AGENTS.md")) is None:
            errs.append("same-PR: AGENTS.md has no `%s` bullet describing "
                        "the doc-kinds checks" % BULLET)
        agents = headers.get("AGENTS.md")
        want = scripts_hash(root)
        got = agents.get("doc-kinds-sha256") if agents else []
        if got != [want]:
            errs.append("same-PR: AGENTS.md header `doc-kinds-sha256:` is %s, "
                        "want %s. A change to %s must update AGENTS.md's "
                        "description of it in the same PR, then the hash "
                        "(`--print-hash`)." % (got[0] if got else "missing",
                                               want, " / ".join(HASHED)))
    return headers


# --------------------------------------------------------------------------
# diff checks
# --------------------------------------------------------------------------
def classify(path, body, in_header):
    if not body:
        return "blank"
    if in_header:
        return "header"
    if SUPERSEDED_BY.match(body):
        return "superseded-by"
    if path in LEDGER_ROW_FILES and (body.startswith("|") or TOPIC_CLAIM.match(body)):
        return "claim-registry"
    pat = ROUTE_STATUS.get(path)
    if pat is not None and pat.match(body):
        return "route-status"
    if body.startswith("|"):
        return "table"
    return "prose"


def norm_target(ref, here):
    """`> Superseded-by: [x](../y.md)` / `docs/y.md` -> repo path."""
    m = re.search(r"\]\(([^)#\s]+)", ref) or re.search(r"`([^`]+)`", ref)
    t = m.group(1) if m else ref.split()[0]
    if t.startswith("/"):
        return t.lstrip("/")
    cand = os.path.normpath(os.path.join(os.path.dirname(here), t))
    return cand if not t.startswith(("docs/", "tests/", "tools/")) else os.path.normpath(t)


def changed_files(root, base):
    out = git(root, "diff", "--name-status", "-M", base, "HEAD", "--",
              ":(glob)**/*.md")
    res = []
    for ln in out.split("\n"):
        if not ln:
            continue
        parts = ln.split("\t")
        st = parts[0]
        if st.startswith("R"):
            res.append((st, parts[1], parts[2]))
        elif st[0] == "A":
            res.append(("A", None, parts[1]))
        elif st[0] == "D":
            res.append(("D", parts[1], None))
        else:
            res.append((st[0], parts[1], parts[1]))
    return res


def hunks(root, base, old, new):
    """Yield (sign, old_ln, new_ln, body) for -U0 diff of one file pair."""
    args = ["diff", "-U0", "-M", base, "HEAD", "--"]
    args += [p for p in {old, new} if p]
    out = git(root, *args)
    o = n = 0
    for ln in out.split("\n"):
        hm = re.match(r"^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@", ln)
        if hm:
            o, n = int(hm.group(1)), int(hm.group(2))
            continue
        if ln.startswith(("+++", "---", "diff ", "index ", "similarity",
                          "rename ", "new file", "deleted file")):
            continue
        if ln.startswith("+"):
            yield "+", None, n, ln[1:].strip()
            n += 1
        elif ln.startswith("-"):
            yield "-", o, None, ln[1:].strip()
            o += 1


def is_ancestor(root, sha):
    rc, _ = git(root, "cat-file", "-e", "%s^{commit}" % sha, check=False)
    if rc != 0:
        return False
    rc, _ = git(root, "merge-base", "--is-ancestor", sha, "HEAD", check=False)
    return rc == 0


def validate_new_finding(root, path, h, text, head_idx, head_hdrs, errs):
    date = h.get("date")
    if len(date) != 1 or not DATE.match(date[0]):
        errs.append("finding: %s: `date:` must be one YYYY-MM-DD" % path)
    prov = h.get("provenance")
    if len(prov) != 1 or not SHA.match(prov[0]):
        errs.append("finding: %s: `Provenance:` must be one commit sha "
                    "(`pre-ratchet` is for migrated legacy files only)" % path)
    elif not is_ancestor(root, prov[0]):
        errs.append("finding: %s: Provenance %s is not a commit in HEAD's "
                    "history (fetch full history, or pin a merged commit)"
                    % (path, prov[0]))
    thms = " ".join(h.get("theorems"))
    if re.match(r"^none\b\W*\S", thms):
        pass
    elif not ANCHOR.search(thms):
        errs.append("finding: %s: `Theorems:` lists no `Mod.v : name` "
                    "(or write `none — <reason>`)" % path)
    else:
        for tok in dead_anchors(thms, head_idx):
            errs.append("finding: %s: Theorems anchor %s does not resolve in "
                        "the tree being merged" % (path, tok))
    body = "\n".join(text.split("\n")[h.nlines:])
    if not SUMMARY_LINE.search(body):
        errs.append("finding: %s: body has no `SUMMARY ok/warn/bug` or "
                    "`OUTCOME` line" % path)
    for tgt in h.get("supersedes"):
        t = norm_target(tgt, path)
        th = head_hdrs.get(t)
        if th is None or th.kind != "finding":
            errs.append("supersedes: %s: Supersedes target %s is not a "
                        "finding at HEAD" % (path, t))
            continue
        ptrs = [norm_target(m.group(1), t) for m in
                (SUPERSEDED_BY.match(ln.strip()) for ln in
                 read(root, t).split("\n")) if m]
        if path not in ptrs:
            errs.append("supersedes: %s supersedes %s, which lacks the "
                        "pointer line `> Superseded-by: %s`" % (path, t, path))


def diff_checks(root, base, head_hdrs, errs, notes):
    same_pr_check(root, base, errs)
    old_txt = show(root, base, BASELINE)
    old_bl = parse_baseline(old_txt)
    new_bl = parse_baseline(show(root, "HEAD", BASELINE))
    if old_txt is None and new_bl:
        notes.append("baseline: %s is new in this diff (bootstrap); its "
                     "`dead` lines are accepted once" % BASELINE)
        new_bl = {}
    for key, why in sorted(new_bl.items()):
        if why == "dead" and old_bl.get(key) != "dead":
            errs.append("baseline: %s gains `%s\t%s\tdead`; fix the anchor "
                        "instead (dead entries only shrink)" % ((BASELINE,) + key))
    head_idx = None
    added = deleted = 0
    per_file = {}
    exempt = {}
    for st, old, new in changed_files(root, base):
        base_h = parse_header(show(root, base, old))[0] if old else None
        head_txt = show(root, "HEAD", new) if new else None
        head_h = parse_header(head_txt)[0] if new else None
        legacy = old is not None and base_h is None   # migration: no header at base

        if base_h is not None and base_h.kind == "finding":
            if st == "D":
                errs.append("finding: %s deleted; findings are append-only "
                            "(supersede it instead)" % old)
                continue
            if head_h is None or head_h.kind != "finding":
                errs.append("finding: %s changed kind; findings are "
                            "immutable after merge" % new)
            for sign, _o, _n, body in hunks(root, base, old, new):
                if sign == "+" and SUPERSEDED_BY.match(body):
                    continue
                if not body:
                    continue
                errs.append("finding: %s is immutable after merge; only "
                            "`> Superseded-by: <path>` lines may be added "
                            "(got %s%r)" % (new or old, sign, body[:80]))
                break
        elif head_h is not None and head_h.kind == "finding" and not legacy:
            if head_idx is None:
                head_idx = symbol_index(root, "HEAD")
            validate_new_finding(root, new, head_h, head_txt, head_idx,
                                 head_hdrs, errs)

        # pointer lines added anywhere must be answered by Supersedes.
        if new and head_h is not None:
            for sign, _o, _n, body in hunks(root, base, old, new):
                m = SUPERSEDED_BY.match(body) if sign == "+" else None
                if not m:
                    continue
                t = norm_target(m.group(1), new)
                th = head_hdrs.get(t)
                sup = [norm_target(s, t) for s in th.get("supersedes")] if th else []
                if th is None or th.kind != "finding" or new not in sup:
                    errs.append("superseded-by: %s points at %s, which is not "
                                "a finding listing `Supersedes: %s`"
                                % (new, t, new))

        # budget: guides and ledgers only.
        if (base_h and base_h.kind == "finding") or \
           (head_h and head_h.kind == "finding"):
            continue
        bn = base_h.nlines if base_h else 0
        hn = head_h.nlines if head_h else 0
        # A legacy file gaining its header: its first line(s) are header.
        for sign, o, n, body in hunks(root, base, old, new):
            in_hdr = (n is not None and n <= hn) or (o is not None and o <= bn)
            kind = classify(new or old, body, in_hdr)
            if kind == "prose":
                key = new or old
                a, d = per_file.get(key, (0, 0))
                per_file[key] = (a + 1, d) if sign == "+" else (a, d + 1)
                if sign == "+":
                    added += 1
                else:
                    deleted += 1
            elif kind != "blank":
                exempt[kind] = exempt.get(kind, 0) + 1

    if exempt:
        notes.append("exempt: " + ", ".join("%d %s" % (v, k) for k, v in
                                            sorted(exempt.items())))
    net = added - deleted
    if per_file:
        w = max(len(f) for f in per_file)
        rows = ["  %-*s  +%-4d -%-4d net %+d" % (w, f, a, d, a - d)
                for f, (a, d) in sorted(per_file.items())]
        rows.append("  %-*s  +%-4d -%-4d net %+d" % (w, "total", added, deleted, net))
        notes.append("guide/ledger prose lines vs %s:\n%s" % (base, "\n".join(rows)))
    if net > 0:
        errs.append("budget: guide/ledger prose grew by %+d non-blank lines. "
                    "Shrink other guides in this PR, or record it as a "
                    "`doc-kind: finding` (dated, Provenance, Theorems, "
                    "SUMMARY) if it is history rather than a guide." % net)


# --------------------------------------------------------------------------
# override
# --------------------------------------------------------------------------
def override_reason(errs):
    path = os.environ.get("GITHUB_EVENT_PATH")
    if not path or not os.path.isfile(path):
        return None
    try:
        with open(path, encoding="utf-8") as fh:
            ev = json.load(fh)
    except (OSError, ValueError):
        return None
    pr = ev.get("pull_request") or {}
    labels = {l.get("name") for l in pr.get("labels") or []}
    if OVERRIDE_LABEL not in labels:
        return None
    m = OVERRIDE_REASON.search(pr.get("body") or "")
    if not m:
        errs.append("override: label `%s` is set but the PR body has no "
                    "`Ratchet-Override-Reason: <why>` line" % OVERRIDE_LABEL)
        return None
    return m.group(1).strip()


# --------------------------------------------------------------------------
# driver
# --------------------------------------------------------------------------
def resolve_base(root, argv):
    if os.environ.get("DOC_KINDS_BASE"):
        return os.environ["DOC_KINDS_BASE"]
    if argv:
        return argv[0]
    if os.environ.get("GITHUB_BASE_REF"):
        return "origin/" + os.environ["GITHUB_BASE_REF"]
    return "origin/main"


def base_commit(root, ref):
    rc, _ = git(root, "rev-parse", "--verify", "%s^{commit}" % ref, check=False)
    if rc != 0 and ref.startswith("origin/"):
        git(root, "fetch", "--no-tags", "--depth=1", "origin",
            ref[len("origin/"):], check=False)
        rc, _ = git(root, "rev-parse", "--verify", "%s^{commit}" % ref, check=False)
    if rc != 0:
        return None
    rc, mb = git(root, "merge-base", ref, "HEAD", check=False)
    if rc == 0 and mb.strip():
        return mb.strip()
    return git(root, "rev-parse", ref).strip()


def run(root, argv, hashed=True, event=None, out=print):
    errs, notes = [], []
    head_hdrs = state_checks(root, errs, notes, hashed=hashed)
    reason = None
    if os.environ.get("GITHUB_EVENT_NAME") == "push" and event is None:
        notes.append("push event: diff checks skipped (the PR ran them)")
    else:
        ref = resolve_base(root, argv)
        b = base_commit(root, ref)
        if b is None:
            if os.environ.get("GITHUB_EVENT_NAME") == "pull_request":
                errs.append("cannot resolve base ref %s" % ref)
            else:
                notes.append("no base ref %s: diff checks skipped" % ref)
        elif b == git(root, "rev-parse", "HEAD").strip():
            notes.append("HEAD is the base: no diff to check")
        else:
            diff_checks(root, b, head_hdrs, errs, notes)
        reason = override_reason(errs)
    for n in notes:
        out("%s %s" % (TAG, n))
    if errs and reason:
        for e in errs:
            out("%s WARN (overridden) %s" % (TAG, e))
        out("%s OVERRIDE: %s" % (TAG, reason))
        return 0
    if errs:
        for e in errs:
            out("%s FAIL %s" % (TAG, e))
        return 1
    out("%s OK" % TAG)
    return 0


# --------------------------------------------------------------------------
# selftest: a throwaway repo per case
# --------------------------------------------------------------------------
V_SRC = "Theorem good_thm : True.\nProof. exact I. Qed.\n"
GUIDE = "<!-- doc-kind: guide -->\n# G\n\nCites `Foo.v : good_thm`.\n"
LEDGER = "<!-- doc-kind: ledger -->\n# L\n\n| `Foo.v : good_thm` | m | 3 |\n"
OLD_FINDING = ("<!-- doc-kind: finding\ndate: 2026-01-01\nProvenance: pre-ratchet\n"
               "Theorems: `Foo.v : good_thm`\n-->\n# Old\n\nC2 holds.\n")


AGENTS = ("<!-- doc-kind: guide -->\n# A\n\n- Doc kinds (`x`): rule one.\n"
          "  More of rule one.\n- Other bullet.\n")


def finding(prov, thm="`Foo.v : good_thm`", summary=True, sup=None):
    s = ("<!-- doc-kind: finding\ndate: 2026-11-14\nProvenance: %s\n"
         "Theorems: %s\n" % (prov, thm))
    if sup:
        s += "Supersedes: %s\n" % sup
    s += "-->\n# Finding\n\nBody.\n"
    if summary:
        s += "\nSUMMARY ok=1 warn=0 bug=0\n"
    return s


def selftest():
    def mk_repo(d, files):
        git(d, "init", "-q", "-b", "main")
        git(d, "config", "user.email", "t@example.invalid")
        git(d, "config", "user.name", "t")
        write(d, files)
        git(d, "add", "-A")
        git(d, "commit", "-qm", "base")
        git(d, "branch", "base")
        return git(d, "rev-parse", "HEAD").strip()

    def write(d, files):
        for p, t in files.items():
            fp = os.path.join(d, p)
            if t is None:
                os.remove(fp)
                continue
            os.makedirs(os.path.dirname(fp) or d, exist_ok=True)
            with open(fp, "w") as fh:
                fh.write(t)

    base_files = {
        "theories/Foo.v": V_SRC,
        "docs/guide.md": GUIDE,
        "docs/verified-claims.md": LEDGER,
        "docs/old.md": OLD_FINDING,
        BASELINE: "# b\n",
        HASHED[0]: "# v1\n",
        "AGENTS.md": AGENTS,
    }
    # (name, change(sha_of_base) -> files, expect_rc, must_contain)
    cases = [
        ("valid finding", lambda s: {"docs/new-2026-11.md": finding(s)}, 0, None),
        ("finding without Provenance",
         lambda s: {"docs/new.md": finding(s).replace("Provenance: %s\n" % s, "")},
         1, "lacks `Provenance:`"),
        ("finding with unknown Provenance",
         lambda s: {"docs/new.md": finding("deadbeefdeadbeef")}, 1, "not a commit"),
        ("finding with pre-ratchet Provenance",
         lambda s: {"docs/new.md": finding("pre-ratchet")}, 1, "must be one commit"),
        ("lookalike: Provenance in body, not header",
         lambda s: {"docs/new.md": "<!-- doc-kind: guide -->\n# x\nProvenance: %s\nmore\n" % s},
         1, "budget"),
        ("finding without SUMMARY",
         lambda s: {"docs/new.md": finding(s, summary=False)}, 1, "SUMMARY"),
        ("finding with dead theorem",
         lambda s: {"docs/new.md": finding(s, thm="`PassesThrough_b64.v : nope`")},
         1, "Theorems anchor"),
        ("no header", lambda s: {"docs/bare.md": "# bare\n"}, 1, "first line"),
        ("guide grows", lambda s: {"docs/guide.md": GUIDE + "One more line.\n"},
         1, "budget"),
        ("guide grows by a table row only",
         lambda s: {"docs/guide.md": GUIDE + "| a | b |\n"}, 0, None),
        ("dead anchor in a guide",
         lambda s: {"docs/guide.md": GUIDE.replace("good_thm", "gone_thm")},
         1, "anchor: docs/guide.md"),
        ("dead file ref in a guide",
         lambda s: {"docs/guide.md": GUIDE.replace("Cites", "See `PassesThrough_b64.v`; cites")},
         1, "PassesThrough_b64.v"),
        ("external library path is not an anchor",
         lambda s: {"docs/guide.md": GUIDE.replace("Cites", "See `Pff/Pff2Flocq.v:65`; cites")},
         0, None),
        ("planned module declared in baseline",
         lambda s: {"docs/guide.md": GUIDE.replace("Cites", "Plan `KdTree.v`; cites"),
                    BASELINE: "docs/guide.md\t`KdTree.v`\tplanned\n"}, 0, None),
        ("bootstrap baseline may hold dead entries",
         lambda s: {"docs/guide.md": GUIDE.replace("good_thm", "gone_thm"),
                    BASELINE: "docs/guide.md\t`Foo.v : gone_thm`\tdead\n"},
         0, None),
        ("new dead anchor baselined as dead",
         lambda s: {"docs/guide.md": GUIDE.replace("good_thm", "gone_thm"),
                    BASELINE: "# b\ndocs/guide.md\t`Foo.v : gone_thm`\tdead\n"},
         1, "dead entries only shrink"),
        ("stale baseline entry",
         lambda s: {BASELINE: "docs/guide.md\t`Foo.v : good_thm`\tdead\n"},
         1, "no longer dangles"),
        ("check script changes, AGENTS bullet does not",
         lambda s: {HASHED[0]: "# v2\n"}, 1, "bumping"),
        ("check script changes, only the hash line moves",
         lambda s: {HASHED[0]: "# v2\n",
                    "AGENTS.md": AGENTS.replace("<!-- doc-kind: guide -->",
                                                "<!-- doc-kind: guide\ndoc-kinds-sha256: 0\n-->")},
         1, "bumping"),
        ("check script changes, bullet re-wrapped only",
         lambda s: {HASHED[0]: "# v2\n",
                    "AGENTS.md": AGENTS.replace("rule one.\n  More", "rule\n  one. More")},
         1, "bumping"),
        ("check script changes with the bullet",
         lambda s: {HASHED[0]: "# v2\n",
                    "AGENTS.md": AGENTS.replace("rule one.", "rule two.")}, 0, None),
        ("bullet edited, scripts unchanged",
         lambda s: {"AGENTS.md": AGENTS.replace("rule one.", "rule two.")}, 0, None),
        ("over-claim lookalike: ledger row with dead theorem",
         lambda s: {"docs/verified-claims.md": LEDGER + "| `Foo.v : bad_thm` | m | 0 |\n"},
         1, "anchor: docs/verified-claims.md"),
        ("ledger row append is free",
         lambda s: {"docs/verified-claims.md": LEDGER + "| `Foo.v : good_thm` | m2 | 3 |\n"},
         0, None),
        ("merged finding edited",
         lambda s: {"docs/old.md": OLD_FINDING.replace("C2 holds.", "C2 is false.")},
         1, "immutable"),
        ("merged finding deleted", lambda s: {"docs/old.md": None}, 1, "append-only"),
        ("merged finding renamed unchanged",
         lambda s: {"docs/old.md": None, "docs/history/old.md": OLD_FINDING}, 0, None),
        ("supersession with pointer",
         lambda s: {"docs/new.md": finding(s, sup="docs/old.md"),
                    "docs/old.md": OLD_FINDING + "\n> Superseded-by: docs/new.md\n"},
         0, None),
        ("supersession without pointer",
         lambda s: {"docs/new.md": finding(s, sup="docs/old.md")}, 1, "lacks the pointer"),
        ("pointer without Supersedes",
         lambda s: {"docs/new.md": finding(s),
                    "docs/old.md": OLD_FINDING + "\n> Superseded-by: docs/new.md\n"},
         1, "superseded-by"),
        ("old finding anchor dies later (not re-anchored)",
         lambda s: {"theories/Foo.v": V_SRC.replace("good_thm", "renamed_thm"),
                    "docs/guide.md": GUIDE.replace("good_thm", "renamed_thm"),
                    "docs/verified-claims.md": LEDGER.replace("good_thm", "renamed_thm")},
         0, None),
        ("legacy file gains a header (migration)",
         lambda s: {"docs/legacy.md": "<!-- doc-kind: finding\ndate: 2026-01-01\n"
                    "Provenance: pre-ratchet\nTheorems: none — legacy\n-->\n# L\nx\n"},
         0, None),
    ]
    fails = 0
    for name, change, want_rc, want_msg in cases:
        with tempfile.TemporaryDirectory() as d:
            s = mk_repo(d, {k: v for k, v in base_files.items()
                            if not (name.startswith("bootstrap") and k == BASELINE)})
            # legacy-migration case needs a header-less base file
            if name.startswith("legacy"):
                write(d, {"docs/legacy.md": "# L\nx\n"})
                git(d, "add", "-A")
                git(d, "commit", "-qm", "legacy")
                git(d, "branch", "-f", "base")
                s = git(d, "rev-parse", "HEAD").strip()
            write(d, change(s))
            git(d, "add", "-A")
            git(d, "commit", "-qm", "change")
            lines = []
            env_saved = {k: os.environ.pop(k, None) for k in
                         ("GITHUB_EVENT_NAME", "GITHUB_EVENT_PATH",
                          "DOC_KINDS_BASE", "GITHUB_BASE_REF")}
            try:
                rc = run(d, ["base"], hashed=False, event="selftest",
                         out=lines.append)
            finally:
                for k, v in env_saved.items():
                    if v is not None:
                        os.environ[k] = v
            text = "\n".join(lines)
            ok = rc == want_rc and (want_msg is None or want_msg in text)
            if not ok:
                fails += 1
                print("%s selftest FAIL: %s (rc %d, want %d%s)\n%s"
                      % (TAG, name, rc, want_rc,
                         ", want %r" % want_msg if want_msg else "", text),
                      file=sys.stderr)
    # override parsing
    errs = []
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as fh:
        json.dump({"pull_request": {"labels": [{"name": OVERRIDE_LABEL}],
                                    "body": "x\nRatchet-Override-Reason: b64 record\n"}}, fh)
        ev = fh.name
    old = os.environ.get("GITHUB_EVENT_PATH")
    os.environ["GITHUB_EVENT_PATH"] = ev
    try:
        if override_reason(errs) != "b64 record" or errs:
            fails += 1
            print("%s selftest FAIL: override reason not read" % TAG, file=sys.stderr)
        with open(ev, "w") as fh:
            json.dump({"pull_request": {"labels": [{"name": OVERRIDE_LABEL}],
                                        "body": "no reason"}}, fh)
        errs = []
        if override_reason(errs) is not None or not errs:
            fails += 1
            print("%s selftest FAIL: label without reason accepted" % TAG,
                  file=sys.stderr)
    finally:
        os.unlink(ev)
        if old is None:
            os.environ.pop("GITHUB_EVENT_PATH", None)
        else:
            os.environ["GITHUB_EVENT_PATH"] = old
    if fails:
        return 2
    print("%s selftest ok (%d cases + override)" % (TAG, len(cases)))
    return 0


def main(argv):
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    if argv[:1] == ["--selftest"]:
        return selftest()
    if argv[:1] == ["--print-hash"]:
        print(scripts_hash(root))
        return 0
    rc = selftest()
    if rc:
        return rc
    try:
        return run(root, argv)
    except RuntimeError as e:
        print("%s FAIL git: %s" % (TAG, e), file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
