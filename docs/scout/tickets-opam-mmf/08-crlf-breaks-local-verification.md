<!-- doc-kind: finding
date: 2026-08-24
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Decide how to stop CRLF breaking local verification

**Type:** task · **Map:** [An MMF release bar for the opam packages](../map-opam-mmf-release-bar.md)
**Blocked by:** nothing — takeable

## Question

The packaging pipeline **cannot be run from a Windows checkout**. There is no
`.gitattributes`, so Git normalises LF to CRLF on checkout, and both
`packaging/*/assemble.sh` and both `MANIFEST` files land with CRLF line
terminators. The observed failures, in order:

1. `bash assemble.sh` → `set: pipefail: invalid option name` — the trailing `\r`
   becomes part of the option name.
2. With the script's line endings stripped, it then fails
   `manifest entry not found in corpus:` with an **empty** name, because every
   MANIFEST path carries a `\r` and matches nothing.

Both packages assemble and build fine once `assemble.sh`, `MANIFEST`, `Makefile`
and `_CoqProject` are CR-stripped into a scratch copy — so this is purely a
line-ending problem, not a packaging bug.

CI is unaffected: it checks out on Linux, where no conversion happens. That is
precisely why this has gone unnoticed, and it means **no maintainer on Windows
has ever been able to verify a package locally** — which is a plausible
contributing cause of six releases shipping without anyone building the
artefact by hand.

Decide:

1. **The fix.** A `.gitattributes` with `*.sh text eol=lf` is the obvious move.
   Decide the full set of paths that must be LF: `*.sh`, `MANIFEST`, `Makefile`,
   `_CoqProject`, `dune`/`dune-project`, and whether `*.v` matters (Rocq accepts
   CRLF, so probably not — but say so rather than leaving it implied).
2. **Whether the scripts should also be defensive.** `assemble.sh` could strip
   `\r` when reading MANIFEST entries, so a bad checkout degrades to a warning
   instead of an empty-name error. Belt and braces, or is the attribute enough?
3. **Whether this becomes a bar line.** "The package assembles and builds from a
   clean checkout on the maintainer's own machine" is a cheap gate that would
   have caught this, and it is the kind of thing the bar exists for. Decide
   whether local reproducibility is a bar requirement or merely nice.
4. **Whether `.gitattributes` needs to exist for the whole repo**, not just
   packaging. The repo has shell scripts elsewhere (`scripts/*.sh`,
   `scripts/check_admitted.sh`, `scripts/validate-claims.sh`); they have the same
   exposure and the same silent-on-CI behaviour.

Note the error message quality is part of the finding: `manifest entry not found
in corpus:` with nothing after the colon is what a `\r` looks like when printed.
Worth deciding whether that message should quote the entry so the next person
sees the problem immediately.
