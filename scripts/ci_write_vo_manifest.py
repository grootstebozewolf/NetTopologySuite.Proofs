#!/usr/bin/env python3
# =============================================================================
# scripts/ci_write_vo_manifest.py
# -----------------------------------------------------------------------------
# Write .vo-manifest: the content-addressed snapshot that makes the next
# run's incremental cache sound.  Records
#   - a sha256 per project .v file (what was actually compiled), and
#   - a hash of the _CoqProject.full flag lines (-Q/-R/-arg ...), whose
#     change must force a full rebuild.
#
# CI runs this ONLY after the build and the axiom audit both pass, and
# saves it in the same cache entry as the .vo files and .palog/ chunks --
# the manifest never blesses artefacts that did not pass the gauntlet.
# scripts/ci_invalidate_stale_vo.py is the consumer.
# =============================================================================

import hashlib
import json
import os
import sys

PROJECT = "_CoqProject.full"
MANIFEST = ".vo-manifest"


def parse_project(path):
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


def main():
    if not os.path.isfile(PROJECT):
        print(f"[manifest] cannot read {PROJECT}", file=sys.stderr)
        return 2
    sources, flags_hash = parse_project(PROJECT)
    manifest = {
        "flags": flags_hash,
        "files": {v: sha256_file(v) for v in sources if os.path.isfile(v)},
    }
    with open(MANIFEST, "w", encoding="utf-8") as fh:
        json.dump(manifest, fh, indent=0, sort_keys=True)
        fh.write("\n")
    print(f"[manifest] recorded {len(manifest['files'])} file hash(es).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
