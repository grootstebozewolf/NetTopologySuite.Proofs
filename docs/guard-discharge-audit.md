<!-- doc-kind: finding
date: 2026-07-05
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Guard-discharge audit — issue #66 round 2, item 1

**Status.** Written 2026-07-04. Scope: this track's ownership
(`HotPixel_b64*`, `PassesThrough_b64*`, `SnapRounding_b64*`,
`OverlayBridgeUnconditional.v`, `WalkResidualDischarge.v`).

**Question.** `extract_rings_valid_of_guards` (`OverlayBridgeUnconditional.v`)
replaced the two `euler_characteristic` hypotheses of the banked
`extract_rings_valid` with five geometric/noding guards:

1. `well_noded_darts E` (= `noded_general_position E` + `all_proper_darts
   (darts_of E)` + `vertex_general_position (darts_of E)`)
2. `no_spurs (darts_of E)`
3. `pairwise_no_proper_cross_twin_aware (darts_of E)`
4. `no_horizontal_darts (darts_of E)`
5. `no_foreign_vertex_twin_aware (darts_of E)`

Does the snap-rounding pipeline this track owns already **produce** these
five facts for `E = result_edges op (noded_labeled_graph A B)` on a real
noded arrangement — i.e. can `extract_rings_valid_of_guards` be applied with
zero side conditions, or do the guards remain named hypotheses the caller
must separately discharge? This pins down exactly which regime the C1 width
extension (item 2) needs to cover.

## Per-guard finding

| Guard | Status | Evidence |
|---|---|---|
| 1. `well_noded_darts` (via `noded_general_position`) | **Open — blocked upstream, not this track's file** | `NodedGeneralPosition.v` proves `noded_general_position` is *strictly stronger* than the noder's `fully_intersected` guarantee (needs the extra "non-collinear at shared endpoints" clause, `noncollinear_share_no_proper`). Its own header states the bridge from `fully_intersected` + that side condition onto `noded_general_position` — the "Hobby-side renaming" — is host-lane "cross-lane plumbing" that has **not been done**. This is the single upstream blocker for guards 1 and 3. |
| 2. `no_spurs` | **Not investigated here — combinatorial, not numeric** | `no_spurs D := forall d, In d D -> fstep D d <> twin d` is a pure DCEL face-walk non-degeneracy condition. Nothing in the numeric snap-rounding layer (rounding, hot-pixel exactness) obviously bears on it; establishing it needs its own combinatorial argument, out of scope for a numeric-pipeline audit. |
| 3. `pairwise_no_proper_cross_twin_aware` | **Open — same blocker as guard 1** | `NodedGeneralPosition.noded_gp_twin_aware` derives this directly from `noded_general_position`. Same unresolved bridge as guard 1. (The *non*-twin-aware predicate `pairwise_no_proper_cross` is a dead end: `ExtractFacesBridge.v` machine-checks that `fully_intersected` does NOT imply it, and in fact no non-degenerate edge can ever satisfy it, since a segment always properly crosses its own reversal — precisely why the twin-aware version exists.) |
| 4. `no_horizontal_darts` | **Refuted as a free corollary of noding — Qed witness added** | `no_horizontal_darts D := forall x, In x D -> py (fst x) <> py (snd x)` is a fact about the **snapped** coordinates the noder emits. `theories-flocq/SnapRoundingGuardAudit.v` (`snap_can_introduce_horizontal_dart`) proves `b64_snap_coord` (round-to-nearest-even to the integer grid) can and does turn two distinct y-coordinates into an identical one — the minimal witness is `0` and `1/2`, which both round to `0` (the tie-to-even case). So a horizontal dart in the *output* does not imply a horizontal edge in the *input*; grid-tie coordinates are the generic case post-snap, not a corner case. `no_horizontal_darts` must be checked per noded arrangement, not assumed. |
| 5. `no_foreign_vertex_twin_aware` | **Unresolved — flagged for a follow-on rung** | No witness search performed yet in this pass. Structurally similar in shape to guard 4 (a T-junction-freedom condition on snapped coordinates); a snap-collapse analogous to guard 4's could plausibly place a third point's snapped coordinate exactly on a snapped edge's interior. Not claimed true or false here — left as the next concrete target rather than overclaimed either way. |

## Bottom line for item 2 (C1 width extension)

None of the five guards are unconditionally free corollaries of snap-rounding
for arbitrary input. Two (`no_spurs`, `no_foreign_vertex_twin_aware`) are
simply not yet investigated; two (`well_noded_darts`, `pairwise_no_proper_
cross_twin_aware`) are blocked on a specific, already-identified upstream gap
(`fully_intersected` + non-collinearity ⟹ `noded_general_position`) that is
host-lane, not this track's files; one (`no_horizontal_darts`) is **machine-
checked false** as a free corollary — grid-tie collapses are structural to
snap-rounding, not an edge case.

Practically: `extract_rings_valid_of_guards` is not yet usable on real noded
output with zero side conditions, and won't be until the `noded_general_
position` bridge lands upstream. C1's width extension does not need to
"solve" this — the C1 theorems bound the Liang-Barsky rounded-vs-exact
agreement on already-grid-aligned coordinates and are silent on whether the
*result* arrangement satisfies these five guards. The two problems are
independent; C1 should proceed on its own numeric merits (the exact-integer-
determinant / tie-freeness route from the prior rung) without waiting on
this audit's open items.

## Next steps / open items

- **`no_foreign_vertex_twin_aware`**: run the same witness-search discipline as
  guard 4 — construct (or refute) a snap-rounding configuration where a third
  point's snapped coordinate lands exactly on a snapped edge's interior.
- **`no_spurs`**: scope a combinatorial (non-numeric) investigation of the
  DCEL face-walk condition; likely independent of this track's numeric files.
- **`noded_general_position` bridge** (guards 1, 3): not this track's file —
  flag to whichever track owns `NodedGeneralPosition.v` / the Hobby-side
  `fully_intersected` lineage that the bridge from `fully_intersected` +
  non-collinearity is the concrete blocker.
- **C1 width extension**: once the rounding-tie-freeness lemma lands
  (`PassesThrough_b64_exact_comparator.v`'s open obligation), re-derive
  `b64_passes_through_grid_exact` at `|n| <= 2^22` through `rat_le` first (a
  no-regression check) before widening to `2^25`.

## References

- `theories-flocq/SnapRoundingGuardAudit.v` — Qed witness for guard 4.
- `theories/NodedGeneralPosition.v` — the strengthened predicate and its
  "cross-lane plumbing" note (guards 1, 3).
- `theories-flocq/ExtractFacesBridge.v` — the historical honest negative for
  the non-twin-aware predicate (context for why twin-awareness exists).
- `theories-flocq/OverlayBridgeUnconditional.v` — `extract_rings_valid_of_guards`
  / `extract_rings_valid_holes_of_guards`, the consumer this audit serves.
