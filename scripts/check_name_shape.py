#!/usr/bin/env python3
"""Name and lemma shape gate.

A ticket should be able to say "add lemma X" without restating how this
corpus names things.  The conventions live here, as rules the gate enforces
on every Theorem/Lemma/Corollary/Proposition/Fact/Remark in theories/ and
theories-flocq/.  Each failure prints the rule and the fix, so the agent
meeting it needs no other context.

Name rules
  name.hygiene      no `__`, no leading or trailing `_`.
  name.placeholder  no throwaway head: lemma/thm/theorem/aux/helper/tmp/
                    foo/bar/test (optionally numbered).  Say what it proves.
  name.head         start lowercase, unless the name opens with an
                    identifier the statement itself uses (PI_, Point_eq_...,
                    G_notch -> Gnotch_...) or a Stdlib/Flocq scope family
                    (Rmult_, Zfold_, Bfin_, Qcompare_).
  name.unique       a name is declared in at most one file.  Two files
                    proving `point_eq` shadow each other under Require
                    Import; reuse the existing lemma or name the variant.

Shape rules (the name promises a shape; the statement must keep it)
  shape.iff         `..._iff`            states `<->`.
  shape.dec         `..._dec`            is a decision: `{..} + {..}`,
                                         sumbool, `\\/`, decidable or bool.
  shape.neq         `..._neq` / `..._ne` concludes a disequality (`<>`, `~`,
                    (not `..._of_neq`)   False, false).
  shape.unique      `..._unique`         states `=`, `exists!`, `<->` or NoDup.
  shape.exists      `exists_...` /       states `exists` or a sig type.
                    `..._exists`

Existing debt is frozen in docs/name-shape-debt.txt (`rule :: path :: name`,
or `name.unique :: name :: files`).  The gate fails when the tree diverges
from it: a new violation, including a frozen duplicate gaining a file (fix
the name or the statement -- do not list it), or a listed entry that is gone
or shrunk (delete or replace the line; the registry only shrinks).

Exit 0 = tree matches registry.  Exit 1 = diverged.  `--list` prints the
current violations in registry form.
"""

import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REGISTRY = os.path.join(ROOT, "docs", "name-shape-debt.txt")
LANES = ("theories", "theories-flocq")

DECL = re.compile(
    r"(?<![\w'.])(Theorem|Lemma|Corollary|Proposition|Fact|Remark)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*)(.*?)\.(?=\s|$)",
    re.S,
)
# Stdlib/Flocq scope families: Rmult_le_one, Zfold_..., Bfin_val, Qcompare_...
STDLIB_HEAD = re.compile(r"^(R|Z|N|Q|B|Pos|Nat)[a-z0-9]*_")
PLACEHOLDER = re.compile(r"^(lemma|thm|theorem|aux|helper|tmp|foo|bar|test)\d*(_|$)")

HINT = {
    "name.hygiene": "drop the doubled/edge underscore",
    "name.placeholder": "name the lemma after what it proves",
    "name.head": "start lowercase, or open with an identifier the statement uses",
    "name.unique": "reuse the existing lemma, or give the variant a distinct name",
    "shape.iff": "state `<->`, or drop `_iff` from the name",
    "shape.dec": "state a decision ({..}+{..}, \\/, bool), or drop `_dec`",
    "shape.neq": "conclude `<>`/`~`, or rename (`..._of_neq` names a hypothesis)",
    "shape.unique": "state the uniqueness (`=`, `exists!`), or drop `_unique`",
    "shape.exists": "state `exists`, or drop `exists` from the name",
}


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


def split_colon(decl):
    """(binders, statement) split at the first top-level `:`."""
    depth = 0
    for i, ch in enumerate(decl):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif (ch == ":" and depth == 0 and decl[i + 1:i + 2] not in ("=", ":", ">")
              and decl[i - 1:i] != ":"):
            return decl[:i], decl[i + 1:]
    return decl, ""


def conclusion_of(stmt):
    """Text after the last top-level `->` (or after the leading forall)."""
    depth, last, k = 0, 0, 0
    while k < len(stmt) - 1:
        c = stmt[k]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif depth == 0 and stmt[k:k + 2] == "->" and stmt[k - 1:k] != "<":
            last = k + 2
        elif depth == 0 and stmt[k] == "," and last == 0:
            last = k + 1
        k += 1
    return stmt[last:]


def declarations():
    """Yield (relpath, name, binders, statement)."""
    for lane in LANES:
        base = os.path.join(ROOT, lane)
        if not os.path.isdir(base):
            continue
        for fn in sorted(os.listdir(base)):
            if not fn.endswith(".v"):
                continue
            rel = "%s/%s" % (lane, fn)
            with open(os.path.join(base, fn), encoding="utf-8", errors="replace") as fh:
                text = strip_comments(fh.read())
            for m in DECL.finditer(text):
                binders, stmt = split_colon(m.group(3))
                yield rel, m.group(2), binders, " ".join(stmt.split())


def violations(rel, name, binders, stmt):
    concl = conclusion_of(stmt)
    whole = binders + " " + stmt
    if "__" in name or name.startswith("_") or name.endswith("_"):
        yield "name.hygiene"
    if PLACEHOLDER.match(name):
        yield "name.placeholder"
    if name[0].isupper() and not STDLIB_HEAD.match(name):
        head = name.split("_")[0]
        used = set(re.findall(r"[A-Za-z_][\w']*", whole))
        if not any(name == t or name.startswith(t + "_") or head == t.replace("_", "")
                   for t in used if t[0].isupper()):
            yield "name.head"
    if re.search(r"_iff'*$", name) and "<->" not in stmt:
        yield "shape.iff"
    if re.search(r"_dec'*$", name) and not re.search(
            r"\}\s*\+\s*\{|sumbool|\\/|[Dd]ecidable|\bbool\b|\{\s*\w+\s*\}\s*\+", stmt):
        yield "shape.dec"
    if (re.search(r"_(neq|ne)'*$", name) and "_of_" not in name
            and not re.search(r"<>|~|False|\bfalse\b", concl)):
        yield "shape.neq"
    if re.search(r"_unique'*$", name) and not re.search(r"=|exists!|<->|NoDup", stmt):
        yield "shape.unique"
    if (re.search(r"(^exists_|_exists'*$)", name)
            and not re.search(r"\bexists\b|\{\s*\w+\s*(:|\|)|\bsig\b", stmt)):
        yield "shape.exists"


def scan():
    found, homes = set(), {}
    for rel, name, binders, stmt in declarations():
        homes.setdefault(name, set()).add(rel)
        for rule in violations(rel, name, binders, stmt):
            found.add("%s :: %s :: %s" % (rule, rel, name))
    for name, files in homes.items():
        if len(files) > 1:
            found.add("name.unique :: %s :: %s" % (name, " ".join(sorted(files))))
    return sorted(found)


def read_registry():
    if not os.path.exists(REGISTRY):
        return None
    with open(REGISTRY, encoding="utf-8") as fh:
        return sorted({l.strip() for l in fh if l.strip() and not l.startswith("#")})


def main(argv):
    found = scan()
    if "--list" in argv:
        print("\n".join(found))
        return 0
    listed = read_registry()
    if listed is None:
        print("[name-shape] registry missing: docs/name-shape-debt.txt")
        return 1
    new = [e for e in found if e not in listed]
    gone = [e for e in listed if e not in found]
    if not new and not gone:
        print("[name-shape] %d frozen violation(s); registry matches." % len(found))
        return 0
    was = {e.split(" :: ")[1]: set(e.split(" :: ")[2].split())
           for e in listed if e.startswith("name.unique")}
    for e in new:
        rule = e.split(" :: ")[0]
        if rule == "name.unique" and set(e.split(" :: ")[2].split()) < was.get(e.split(" :: ")[1], set()):
            print("[name-shape] SHRUNK, replace the name.unique line with:\n    %s" % e)
            continue
        print("[name-shape] NEW %s\n    fix: %s" % (e, HINT[rule]))
    regrown = {e.split(" :: ")[1] for e in new if e.startswith("name.unique")}
    for e in gone:
        if e.startswith("name.unique") and e.split(" :: ")[1] in regrown:
            continue
        print("[name-shape] FIXED, delete from docs/name-shape-debt.txt:\n    %s" % e)
    if any(not e.startswith("name.unique") or not set(e.split(" :: ")[2].split()) < was.get(e.split(" :: ")[1], set()) for e in new):
        print("\nNew names follow the rules in scripts/check_name_shape.py; the"
              "\nregistry is frozen debt and is never extended.")
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
