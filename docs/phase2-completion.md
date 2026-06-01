# Phase 2 completion: snap-rounding noder + Hobby topological safety

**Status.** Written 2026-06-01 retroactively. Phase 2's deliverables —
the hot-pixel layer, the snap-rounding correctness invariant, the
topological-correctness theorem at the supported level, and Hobby
Theorem 4.1 as a Qed-closed conditional — landed on main across late
May 2026 (milestones 1–4). No completion doc was written at the time;
this artifact closes the documentation gap so the
Phase 0 → Phase 1 → Phase 2 → Phase 3 → Phase 4 retro chain is intact.

The discipline observed for
[`docs/phase0-completion.md`](phase0-completion.md) and
[`docs/phase1-completion.md`](phase1-completion.md) is mirrored here:
current state, what stays open, why this is "Phase 2 complete," future
paths.

## Current state (late May 2026, completion point)

**Shipped, Qed-closed.**

R-side hot-pixel layer ([`theories/HotPixel.v`](../theories/HotPixel.v)):

- `segment_point P0 P1 t := (1-t)·P0 + t·P1` — linear parametrisation.
- `in_hot_pixel` / `hot_pixel_radius scale` — grid-cell containment,
  parameterised by `scale` (half-extent `/(2·scale)`).
- `segment_touches_hot_pixel` — `exists t, in_hot_pixel (segment_point …)`,
  the SPEC the binary64 Liang–Barsky filter decides.

Binary64 hot-pixel + passes-through layer
([`theories-flocq/HotPixel_b64.v`](../theories-flocq/HotPixel_b64.v),
[`theories-flocq/PassesThroughHalfopen_b64.v`](../theories-flocq/PassesThroughHalfopen_b64.v)):

- `b64_liang_barsky_touches` — the Liang–Barsky parameter-interval
  filter over `binary64`, deciding `segment_touches_hot_pixel`.
- `b64_passes_through_hot_pixel` + the tight **half-open** variant
  `b64_passes_through_hot_pixel_halfopen` — the relation that
  snap-rounding preserves, in the half-open convention that makes
  pixel tilings partition the plane.

Snap-rounding correctness invariant
([`theories-flocq/SnapRounding_b64.v`](../theories-flocq/SnapRounding_b64.v)):

- `snap_round` / `b64_snap` — round-to-nearest-grid on coordinates.
- `snap_round_coord_idem`, `snap_round_idempotent`,
  `b64_snap_coord_B2R_idem` — snapping is idempotent (a snapped point is
  its own snap).
- **`b64_snap_round_preserves_passes_through`** — snap-rounding a
  segment preserves the passes-through-hot-pixel relation; the
  load-bearing invariant for milestone 3.
- `b64_snap_round_segment` + `b64_snap_round_segment_correct` —
  segment-level snap with its correctness lemma.

Topological correctness at the supported level
([`theories-flocq/TopologicalCorrectness_b64.v`](../theories-flocq/TopologicalCorrectness_b64.v)):

- `share_hot_pixel` / `b64_share_hot_pixel` — two segments meet the
  same pixel.
- **`b64_snap_round_preserves_shared_hot_pixel`** — snap-rounding
  preserves the share-a-pixel relation between two segments.
- `b64_snap_round_preserves_pixel_cover` — the snapped segment still
  covers every pixel its pre-image did.

Hobby Theorem 4.1 — conditional headline
([`theories-flocq/HobbyTheorem_b64.v`](../theories-flocq/HobbyTheorem_b64.v)):

- `segments_intersect_properly`, `segments_intersect_only_at_endpoints`,
  `fully_intersected`, `snap_round_segments`, `in_snap_region`.
- **`hobby_lemma_4_2`** — Qed-closed (the strip-shaped Minkowski-sum
  predicate, corrected per Hobby p.210; product-sign case split).
- `hobby_lemma_4_3_shared_endpoint` — Qed-closed (snap determinism
  preserves literal endpoint equality).
- **`hobby_theorem_4_1_conditional`** — HEADLINE. Snap-rounding
  preserves "fully intersected" under the Lemma 4.3 premise:

```coq
Theorem hobby_theorem_4_1_conditional :
  forall (A : list (Point * Point)),
    fully_intersected A ->
    (forall s1 s2 : Point * Point,
       segments_intersect_only_at_endpoints s1 s2 ->
       forall sigma1 sigma2 : Point * Point,
         In sigma1 (snap_round_segments [s1]) ->
         In sigma2 (snap_round_segments [s2]) ->
         sigma1 <> sigma2 ->
         segments_intersect_only_at_endpoints sigma1 sigma2) ->
    fully_intersected (snap_round_segments A).
```

Oracle consumer
([`theories-flocq/Validate_binary64_extract.v`](../theories-flocq/Validate_binary64_extract.v)):

- RocqRefRunner modes `PASSES_THROUGH_FILTER` /
  `PASSES_THROUGH_HALFOPEN` extracted — the Liang–Barsky filter and
  its half-open variant are differential-testable against the C# port.

## Open

One piece remains, registered as a Tier-3 deferred proof in
[`docs/admitted-deferred-proofs.txt`](admitted-deferred-proofs.txt):

### `hobby_lemma_4_3_no_proper` (the conditional's premise)

`hobby_theorem_4_1_conditional` is Qed-closed *conditional on* Lemma
4.3. That lemma was refactored into two halves:

- `hobby_lemma_4_3_shared_endpoint` — Qed-closed, trivial.
- **`hobby_lemma_4_3_no_proper`** — the load-bearing piece: snap-rounding
  preserves "no proper intersection" for any pair of properly-disjoint
  segments. Registered `Admitted` with a documented proof structure
  ([`docs/hobby-theorem-proof-structure.md`](hobby-theorem-proof-structure.md)
  §4, §7).

The proof structure is known: use Lemma 4.2's (ξ, η) coordinate
rotation, express the snap displacements as piecewise-linear functions,
and close the no-proper-intersection ordering at snapped endpoints via
the tolerance-square bound `|F_j(ξ) − β_j − γ_j·ξ| < 1/2`. The subtlety
is the rotated coordinate frame's half-open convention (opposite to the
unrotated one — Hobby p.210–211). Estimated scope: **4–6 weeks,
thesis-shaped.** This is the Phase 2 analog of Phase 0's open Stage D
and Phase 1's open coordinate story: a substantial separate engagement,
not chokepoint work. Discharging it closes Hobby 4.1 *unconditionally*.

## Why this is "Phase 2 complete"

Phase 2's chokepoint deliverable is a **verified snap-rounding noder**:
round segment endpoints to a grid such that the topology of
intersections is preserved (Hobby 1999 + Halperin–Packer 2002 ISR).
That deliverable shipped at the supported level, end-to-end:

- **Coq-side**: the hot-pixel filter (milestone 1), the passes-through
  relation + half-open variant (milestone 2), the snap-rounding
  correctness invariant (milestone 3), and the topological-correctness
  theorem (milestone 4) are all Qed-closed; Hobby 4.1 is a Qed-closed
  conditional with Lemma 4.2 closed.
- **Oracle-side**: the two passes-through modes extracted for
  differential testing.

What's open — the `no_proper` half of Lemma 4.3 — is the one
thesis-shaped piece, carried as the conditional's explicit premise
rather than silently assumed. Mirroring
[`docs/soundness-strategy.md`](soundness-strategy.md): there is no
middle ground between the conditional headline as shipped and the full
Hobby magnitude argument that buys meaningful intermediate value.

## Future paths

In rough order of payoff vs. cost:

1. **`hobby_lemma_4_3_no_proper`** — the thesis-shaped piece;
   discharging it closes Hobby 4.1 unconditionally. Reading-unblocked:
   Hobby 1999 §4, Halperin–Packer 2002.
2. **C#-side snap-rounding port** — mirror `b64_snap_round_segment`
   and the passes-through filter into `NetTopologySuite.Robust.*` with
   a RocqRefRunner differential corpus, as Phases 0/1 did.
3. **Phase 3 onward** — planar overlay consumes the noded output. As
   with Phase 1, Phase 3 lands using the supported-level guarantees
   here and does NOT depend on closing (1).

## Audit summary

- **The only `Admitted` is `hobby_lemma_4_3_no_proper`**, registered as
  a Tier-3 deferred proof (theorem is TRUE; proof structure documented;
  work is multi-session). `scripts/check_admitted.sh` enforces the
  registration. No other `Admitted` / `Axiom` / `Parameter`.
- **No silent narrowing of contracts.** Lemma 4.3 is the conditional's
  explicit premise; the corpus does not pretend snap-rounding's
  no-proper preservation is proved when it is the registered IOU.
- **Category C axiom footprint.** `SnapRounding_b64.v`,
  `TopologicalCorrectness_b64.v`, and `HotPixel_b64.v` pull
  `Classical_Prop.classic` transitively via Flocq's round-to-nearest
  (`Rcompare` / `Rle_bool` closure) — intrinsic to any theorem about
  `snap_round`. Tracked in
  [`docs/audit-exceptions.txt`](audit-exceptions.txt) with the
  per-file justification; the same four-axiom baseline Phases 0/1
  carry. `hobby_lemma_4_2` itself avoids `classic` (no Flocq-bridge
  content in its proof).

## Why this doc lands now

Phase 2 worked at the supported level and Phase 3 composed on top of it
(the overlay bridge consumes `fully_intersected (noded_segments A B)`).
The missed ceremony was a `docs/phase2-completion.md` to mirror the
ones for Phase 0 and Phase 1. This doc closes that gap so the
retrospective chain reads linearly when future contributors trace the
history.

---

**AI assistance disclosure:** AI-drafted, human-reviewed.
  Assisted-by: Claude
