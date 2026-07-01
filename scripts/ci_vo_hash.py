#!/usr/bin/env python3
# =============================================================================
# scripts/ci_vo_hash.py
# -----------------------------------------------------------------------------
# THE canonical content hash for the incremental .vo cache, shared by BOTH
# scripts/ci_write_vo_manifest.py (which records it) and
# scripts/ci_invalidate_stale_vo.py (which compares against it).
#
# These two MUST hash identically: the invalidator decides a .v is
# "unchanged" (and ages it so make skips the rebuild) iff its freshly
# computed hash equals the one the manifest recorded on the previous run.
# When the two used different definitions (a full-bytes hash in the writer
# vs a comment-stripped hash in the invalidator, 2026-06..2026-07), EVERY
# file always compared unequal, so the invalidator touched everything and
# the "incremental" PR cache silently degraded to a full rebuild every run.
# Sharing one function here removes that failure mode structurally.
#
# Semantics: Coq comments ((* ... *)) and `#`-comment lines carry no proof
# content, so they are stripped and whitespace is normalized before hashing.
# A comment-only / formatting-only edit therefore does NOT force a rebuild of
# the file or its dependents -- a deliberate, sound speed/accuracy tradeoff
# (Coq semantics are unaffected).  The strip is a simple, non-nested regex;
# the rare semantics-identical edit that slips through only ever causes an
# extra (safe) rebuild, never a skipped one.
#
# _CoqProject flag lines (-Q/-R/-arg ...) are hashed verbatim: a flag change
# can alter compilation semantics with no .v edit, so it must force a full
# rebuild (the callers wipe all artefacts when this hash moves).
# =============================================================================

import hashlib
import re


def source_sha256(path):
    """Content hash of a .v source, ignoring comments and formatting."""
    with open(path, "rb") as fh:
        raw = fh.read()
    text = raw.decode("utf-8", errors="replace")
    # strip # comments (whole line or tail)
    text = re.sub(r"(?m)^[^#]*#.*$|^#.*$", "", text)
    # strip non-nested (* ... *) comments
    text = re.sub(r"\(\*.*?\*\)", "", text, flags=re.DOTALL)
    # normalize whitespace so formatting-only edits hash stably
    text = "\n".join(line.rstrip() for line in text.splitlines() if line.strip())
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def parse_project(path):
    """Return (source_files, flags_hash) from a _CoqProject file.

    Comment text is stripped FIRST: prose comments may end in `.v`
    (e.g. `# ... companion to theories/SpectreExample.v`) and must not be
    mistaken for entries.
    """
    sources, flag_lines = [], []
    with open(path, encoding="utf-8") as fh:
        for raw in fh:
            line = raw.split("#", 1)[0].strip()
            if not line:
                continue
            if line.endswith(".v"):
                sources.append(line)
            else:
                flag_lines.append(line)
    flags_hash = hashlib.sha256("\n".join(flag_lines).encode()).hexdigest()
    return sources, flags_hash
