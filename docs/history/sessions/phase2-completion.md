# Phase 2 completion: snap-rounding noder + Hobby topological safety

Phase 2 delivers a verified snap-rounding noder: round segment endpoints
to a grid while preserving intersection topology (Hobby 1999 +
Halperin–Packer 2002). Milestones 1–4 landed on main in late May 2026;
Hobby Theorem 4.1 is Qed-closed as a conditional.

## Shipped (Qed-closed)

**Hot-pixel layer** — [`theories/HotPixel.v`](../theories/HotPixel.v),
[`theories-flocq/HotPixel_b64.v`](../theories-flocq/HotPixel_b64.v),
[`theories-flocq/PassesThroughHalfopen_b64.v`](../theories-flocq/PassesThroughHalfopen_b64.v):

- `segment_point` (linear parametrisation), `in_hot_pixel`,
  `segment_touches_hot_pixel` — the R-side spec.
- `b64_liang_barsky_touches` — the binary64 Liang–Barsky filter that
  decides it.
- `b64_passes_through_hot_pixel` + the tight half-open variant (the
  convention under which pixel tilings partition the plane).

**Snap-rounding invariant** —
[`theories-flocq/SnapRounding_b64.v`](../theories-flocq/SnapRounding_b64.v):

- `snap_round` / `b64_snap` with idempotence lemmas.
- `b64_snap_round_preserves_passes_through` — snapping a segment keeps
  the passes-through relation. (Milestone 3.)

**Topological correctness** —
[`theories-flocq/TopologicalCorrectness_b64.v`](../theories-flocq/TopologicalCorrectness_b64.v):

- `b64_snap_round_preserves_shared_hot_pixel` — two segments that share
  a pixel still share one after snapping.
- `b64_snap_round_preserves_pixel_cover`. (Milestone 4.)

**Hobby Theorem 4.1** —
[`theories-flocq/HobbyTheorem_b64.v`](../theories-flocq/HobbyTheorem_b64.v):

- `hobby_lemma_4_2` Qed-closed (the corrected strip-shaped predicate).
- `hobby_theorem_4_1_conditional` — snap-rounding preserves "fully
  intersected", conditional on Lemma 4.3:

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

**Oracle** — RocqRefRunner modes `PASSES_THROUGH_FILTER` /
`PASSES_THROUGH_HALFOPEN` extracted.

## Open

**`hobby_lemma_4_3_no_proper`** — the premise the headline is
conditional on: snap-rounding preserves "no proper intersection" for
properly-disjoint segments. Registered as a deferred proof
([`docs/admitted-deferred-proofs.txt`](admitted-deferred-proofs.txt);
structure in [`hobby-theorem-proof-structure.md`](hobby-theorem-proof-structure.md)
§4, §7). Proof path is known — Lemma 4.2's (ξ, η) rotation, the
piecewise-linear displacement functions, the tolerance-square bound
`|F_j(ξ) − β_j − γ_j·ξ| < 1/2` — but it's a 4–6 week, thesis-shaped
piece. Lemma 4.3's shared-endpoint half (`hobby_lemma_4_3_shared_endpoint`)
is already Qed-closed; discharging `no_proper` makes Hobby 4.1
unconditional.

## What "complete" means here

The noder ships at the supported level: hot-pixel filter, passes-through
relation, snap invariant, and topological correctness are all Qed-closed,
and Hobby 4.1 holds conditional on one named, registered premise. Phase 3
builds on this output (it consumes `fully_intersected (noded_segments A B)`)
and does not need Lemma 4.3 closed first.

## Next

1. `hobby_lemma_4_3_no_proper` — closes Hobby 4.1 unconditionally.
2. C# port of `b64_snap_round_segment` + the passes-through filter, with
   a RocqRefRunner differential corpus (as Phases 0/1 did).

## Audit

- One `Admitted` (`hobby_lemma_4_3_no_proper`), registered as a deferred
  proof and carried as the headline's explicit premise. No other
  `Admitted` / `Axiom` / `Parameter`.
- `SnapRounding_b64.v`, `TopologicalCorrectness_b64.v`, `HotPixel_b64.v`
  pull `Classical_Prop.classic` via Flocq's round-to-nearest — intrinsic
  to any `snap_round` theorem, tracked in
  [`audit-exceptions.txt`](audit-exceptions.txt). `hobby_lemma_4_2`
  itself stays classic-free.
