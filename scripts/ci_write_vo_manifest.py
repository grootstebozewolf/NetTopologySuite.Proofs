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

import json
import os
import sys

# Shared, canonical hash + project parser (see scripts/ci_vo_hash.py).  The
# writer and the invalidator MUST agree bit-for-bit, so both import the same
# `source_sha256`/`parse_project` -- a full-bytes hash here (the historical
# bug) made every file compare "changed" and defeated the incremental cache.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ci_vo_hash import parse_project, source_sha256  # noqa: E402

# Which _CoqProject / manifest this run targets.  Defaults preserve the
# original Flocq-lane behaviour; the Stdlib-only `theories/` lane overrides
# them via CI_VO_PROJECT=_CoqProject and CI_VO_MANIFEST=.vo-manifest-theories.
PROJECT = os.environ.get("CI_VO_PROJECT", "_CoqProject.full")
MANIFEST = os.environ.get("CI_VO_MANIFEST", ".vo-manifest")


def main():
    if not os.path.isfile(PROJECT):
        print(f"[manifest] cannot read {PROJECT}", file=sys.stderr)
        return 2
    sources, flags_hash = parse_project(PROJECT)
    manifest = {
        "flags": flags_hash,
        "files": {v: source_sha256(v) for v in sources if os.path.isfile(v)},
    }
    with open(MANIFEST, "w", encoding="utf-8") as fh:
        json.dump(manifest, fh, indent=0, sort_keys=True)
        fh.write("\n")
    print(f"[manifest] recorded {len(manifest['files'])} file hash(es).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
