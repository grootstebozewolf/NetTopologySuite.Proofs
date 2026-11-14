<!-- doc-kind: finding
date: 2026-08-22
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Open the module-split queue epic

**Type:** task · **Map:** [Retire the epic block #64–#69](../../map-epic-block-64-69.md)
**Blocked by:** [Write the module-split gate](02-module-split-gate-policy-and-guard.md)

## Question

The split campaign stalled after a seven-monolith burst in August 2026 (#464,
#465, #472, #475, plus the earlier `EdgeFaceBridge` / `RelateNodingLineLine` /
`CornerCorridorBridge` work), and its remainder is tracked nowhere — only rows
B2/B3/B5 of `docs/audit-meso-sample-2026-08.md` survive, and no issue enumerates
the twelve files now over 800 lines. Open the clearly-stated new epic that carries
it, so the chore has a home outside this map.

The epic should state:

- The gate from the policy ticket, verbatim, as its entry criterion.
- The current queue with metrics, and the exempt near-miss, so nobody re-argues
  membership.
- The seeded one-per-session cadence.
- That high fan-in is **not** a blocker: the umbrella re-export pattern makes
  importers unable to notice a split, which is precisely why `HotPixel_b64.v`
  being marked "split BLOCKED — 21 reverse deps incl. the oracle extraction path"
  in `docs/audit-meso-sample-2026-08.md` is worth revisiting rather than encoding.
- The two split children that regrew past 800 lines
  (`Intersect_b64_exact_forward_error.v` 1002, `RelateNodingLineLineCollection.v`
  781) as evidence that the ratchet guard is the real deliverable — they drifted
  because nothing watched.

Decide in the ticket whether B2/B3/B5 fold into this epic or stay in the audit
doc's queue.

## Resolution

**Closed 2026-08-22. The epic is open as #506 — *Module split campaign: retire
the gated monoliths, one per session*.** It carries the gate as entry criterion,
the queue with metrics, the exempt near-miss, the seeded cadence, the umbrella
pattern per split (including deleting the allowlist line in the same PR), and the
fan-in argument against inheriting `HotPixel_b64.v`'s "BLOCKED" verdict.

**The B-row decision: none of them fold in — and two were misfiled.** Checking
their premises rather than their wording changed the answer:

- **B2** — *satisfied by side effect.* `theories/CornerCorridorBridge.v` is now
  **138 lines** (was 2144) and the self-contained `sample_*` worked example the
  row wanted extracted lives in `theories/BaseToTipSample.v` (513 lines), moved
  during the C-3e / `BaseToTipHeadline` splits. The row read open only because
  its *named* deliverable, `CornerCorridorBridgeExample.v`, never appeared. Row
  updated in `docs/audit-meso-sample-2026-08.md`.
- **B5** — *unblocked, and still real.* It was gated on B2 ("rows citing
  to-be-moved lemmas would orphan on extraction"); B2 has happened, so nothing
  can orphan. Both headlines are still at **0** `verified-claims.md` rows. Row
  updated, and cross-referenced to #503 — the same class of gap, and #503 already
  asks whether the reverse check (Qed artefact → claims row) deserves a guard.
  Landing them together is the obvious move.
- **B3** — host-lane promotion into `_CoqProject` is build-lane hygiene, not
  split work. Stays where it is, untouched.

So the epic stays about splitting, which is what keeps its entry criterion
meaningful. The audit doc keeps its own queue, now honest about which rows are
live.

**One consequence for the map:** ticket 10's blocker is no longer this ticket but
the epic it created — the resync waits for #506's queue to *empty*, not merely for
the epic to exist.
