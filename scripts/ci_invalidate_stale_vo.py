#!/usr/bin/env python3
# =============================================================================
# scripts/ci_invalidate_stale_vo.py
# -----------------------------------------------------------------------------
# Content-addressed staleness pass for the incremental corpus cache.
#
# CI restores theories{,-flocq}/ build artefacts (.vo*, .glob, .aux), the
# per-file Print Assumptions chunks (.palog/), and a manifest
# (.vo-manifest) from the previous successful run.  This script then makes
# GNU make's mtime-based rebuild decisions SOUND against that cache:
#
#   - The manifest records a sha256 per project .v file plus a hash of the
#     _CoqProject.full flag lines (-Q/-R/-arg ...).
#   - Every .v whose hash matches the manifest is aged to a fixed date
#     (2001-01-01) far older than any cached .vo  ->  make skips it.
#   - Every .v that changed or is new is touched to "now"  ->  make
#     rebuilds it and, transitively, everything that depends on it
#     (dependencies come from rocq makefile / coqdep, regenerated fresh
#     every run).
#   - If the flag lines changed, compilation semantics may have changed
#     globally without any .v content change, so ALL artefacts and chunks
#     are wiped  ->  full rebuild.
#   - Artefacts and chunks of files that vanished from the project are
#     deleted, so the audit never sees ghosts of removed files.
#
# Deliberately NOT based on git commit timestamps: rebases can backdate a
# changed file, which would let a timestamp scheme skip rebuilding changed
# sources.  Hashes cannot be fooled that way.
#
# No manifest (cold cache, or a main-branch run that skips the restore)
# means nothing to do: the build is from clean by construction.
#
# Exit codes: 0 on success (including cold cache), 2 on usage/IO errors.
# =============================================================================

import hashlib
import json
import os
import sys

PROJECT = "_CoqProject.full"
MANIFEST = ".vo-manifest"
PALOG_DIR = ".palog"
# 2001-01-01T00:00:00Z -- predates every cached .vo by construction.
OLD_MTIME = 978307200


def parse_project(path):
    """Return (source_files, flags_hash) from a _CoqProject file.

    Comment text is stripped FIRST: prose comments may end in `.v`
    (e.g. `# ... companion to theories/SpectreExample.v`) and must not
    be mistaken for entries.
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


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 16), b""):
            h.update(chunk)
    return h.hexdigest()


def artefacts_of(vfile):
    """All build artefacts rocq makefile produces for one .v source."""
    d, base = os.path.split(vfile)
    stem = base[:-2]
    return [
        os.path.join(d, stem + ext) for ext in (".vo", ".vos", ".vok", ".glob")
    ] + [os.path.join(d, "." + stem + ".aux")]


def palog_of(vfile):
    return os.path.join(PALOG_DIR, vfile + ".log")


def remove_quietly(path):
    try:
        os.remove(path)
        return True
    except FileNotFoundError:
        return False


def main():
    if not os.path.isfile(PROJECT):
        print(f"[invalidate] cannot read {PROJECT}", file=sys.stderr)
        return 2

    sources, flags_hash = parse_project(PROJECT)

    if not os.path.isfile(MANIFEST):
        print("[invalidate] no manifest (cold cache) -- full build from clean.")
        return 0

    with open(MANIFEST, encoding="utf-8") as fh:
        manifest = json.load(fh)

    if manifest.get("flags") != flags_hash:
        print("[invalidate] _CoqProject.full flag lines changed -- wiping all "
              "artefacts for a full rebuild.")
        wiped = 0
        for vfile in set(sources) | set(manifest.get("files", {})):
            for art in artefacts_of(vfile):
                wiped += remove_quietly(art)
            remove_quietly(palog_of(vfile))
        remove_quietly(MANIFEST)
        print(f"[invalidate] wiped {wiped} artefact(s).")
        return 0

    recorded = manifest.get("files", {})
    now = None  # touch with current time (os.utime default)
    unchanged = changed = new = 0

    for vfile in sources:
        if not os.path.isfile(vfile):
            # Listed but missing: the build will fail loudly on its own.
            continue
        if recorded.get(vfile) == sha256_file(vfile):
            os.utime(vfile, (OLD_MTIME, OLD_MTIME))
            unchanged += 1
        else:
            os.utime(vfile, now)
            if vfile in recorded:
                changed += 1
            else:
                new += 1

    # Files that left the project: remove artefacts + chunk so neither
    # make nor the audit ever sees them again.
    current = set(sources)
    removed = 0
    for vfile in recorded:
        if vfile not in current:
            for art in artefacts_of(vfile):
                remove_quietly(art)
            remove_quietly(palog_of(vfile))
            removed += 1

    # Orphan chunks (e.g. from a renamed file) are pruned the same way.
    orphans = 0
    if os.path.isdir(PALOG_DIR):
        for root, _dirs, files in os.walk(PALOG_DIR):
            for name in files:
                chunk = os.path.join(root, name)
                vfile = os.path.relpath(chunk, PALOG_DIR)[: -len(".log")]
                if vfile not in current:
                    remove_quietly(chunk)
                    orphans += 1

    print(f"[invalidate] {unchanged} unchanged (aged), {changed} changed + "
          f"{new} new (touched), {removed} removed from project, "
          f"{orphans} orphan chunk(s) pruned.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
