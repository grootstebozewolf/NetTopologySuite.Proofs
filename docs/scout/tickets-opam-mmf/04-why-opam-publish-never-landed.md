<!-- doc-kind: finding
date: 2026-08-24
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Establish why `opam publish` never landed a package

**Type:** research · **Map:** [An MMF release bar for the opam packages](../map-opam-mmf-release-bar.md)
**Blocked by:** nothing — takeable

## Question

Six releases have shipped and **none** reached the opam archive. The bar now
requires opam-installable, so the mechanism has to be understood before a
checklist can name a gate that would catch this.

Verified starting facts: `released/packages/` in `rocq-prover/opam` has no entry
for either package (`coq-flocq` is present at four versions, confirming the path
convention), an archive-wide code search for all four name spellings returns
zero hits, and `OPAM_PUBLISH_TOKEN` has been configured since 2026-06-24.

Determine which of these happened, with evidence:

1. **The step never ran** — e.g. the release event shape did not match, or the
   job was skipped. The workflow triggers on a release; check whether the June
   tags produced release events of the expected kind.
2. **It ran and took the fallback.** The workflow has a branch that prints
   `::warning::opam publish did not complete` and attaches the tarball instead.
   If this is the path, find out *why* `opam publish` failed — the token's
   scopes, the `--repo` value, the interactive prompts the `yes | script -qec`
   wrapper is trying to feed, or a lint rejection.
3. **PRs were opened and never merged.** Check for pull requests to
   `rocq-prover/opam` from the account, open or closed.

The workflow logs for the 2026-06-24 through 2026-06-28 runs are the primary
evidence; they may have aged out, in which case say so rather than inferring.

Two things to settle beyond the diagnosis:

- **`OPAM_TARGET_REPO` defaults to `coq/opam`**, which redirects to
  `rocq-prover/opam`. Decide whether a redirect is acceptable for a publish
  target or the variable should be set explicitly.
- **The fallback is silent by design** — it warns and succeeds. Decide whether
  that is right. A release job that cannot publish but reports success is
  exactly how six releases went nowhere unnoticed, and the map's standing
  preference is gates over prose.

Note that this ticket is diagnosis only. Fixing the pipeline is execution and
belongs after the bar, not on the map.
