<!-- doc-kind: finding
date: 2026-08-24
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Write the bar

**Type:** grilling · **Map:** [An MMF release bar for the opam packages](../map-opam-mmf-release-bar.md)
**Blocked by:** 01, 02, 03, 04, 05, 07 — the bar is assembled from their answers

## Question

Write the release bar itself: the named checklist, the evidence each line cites,
and where it lives. This is the map's destination, so it is takeable only once
every other ticket has closed — each one supplies a line or the wording of one.

What this ticket must produce:

1. **The checklist**, named, with one line per gate. Expected inputs from the
   closed tickets: the package names and version labels (01), manifest closure
   (02), the version constraints and a tested-on line (03), a publish gate that
   would have caught six silent non-publishes (04), the axiom-footprint line per
   package (05), and description accuracy (07).
2. **Where the bar lives.** Candidates: `packaging/README.md` (next to the thing
   it gates), a `docs/` document of record, or a per-package file. The fork keeps
   its bar in `doc/`; this repo's convention is `docs/<topic>-<yyyy-mm>.md` for
   writeups and `docs/adr/` for decisions. A bar is neither exactly — decide.
3. **What "met" means, and who says so.** A checklist with no verdict line is a
   suggestion. Decide whether the bar carries a `SUMMARY ok/warn/bug` line in the
   house style, and whether any part of it is machine-checked rather than
   attested. Prefer machine-checked wherever the ticket answers allow it.
4. **Whether the two packages clear the bar together or separately.** The map's
   fog notes they have always been tagged minutes apart with nothing requiring
   it, and their axiom lines will differ. Settle it here.
5. **What the bar deliberately does not require.** Write this down. The fork's
   gates are already excluded; the map's Out-of-scope section names more. A bar
   that does not say what it omits invites the reader to assume it covers
   everything.

The pull at this point will be to just cut the releases. That pull is the signal
the map is finished: the bar is the deliverable, and minting is the hand-off.
