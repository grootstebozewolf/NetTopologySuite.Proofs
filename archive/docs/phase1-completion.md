# Phase 1 completion: robust segment-pair intersection

**Status.** Written 2026-05-15 after the integer-regime soundness
headline (`b64_intersect_sign_filtered_sound_small_int`) closed and
the .Curve consumer port shipped (PR #11). This document records what
is in the corpus for Phase 1, what stays open, and where the gaps line
up with Phase 0's deferred Stage D work.

## Current state (2026-05-15, completion point)

**Shipped, Qed-closed.**

R-side ([`theories/Intersect.v`](../theories/Intersect.v)):

- `segments_share_point_implies_opposite_sides` — the structural fact:
  if two segments share a point, the cross-product products are
  non-positive.
- `same_side_rejection_is_sound` — corollary: if either product is
  strictly positive, the segments do not share a point.
- **`strict_completeness`** — the partial converse: when both products
  are strictly negative, the segments share an interior point.
  Constructive proof using Cramer's rule (`lerp t C D` for
  `t = cross A B C / (cross A B C - cross A B D)`); side helper
  `div_in_unit_interval` clears the `nra`-through-`Rdiv` issue with an
  inverse-product hint.
- Degenerate / collinear shape lemmas (shared endpoint, full overlap)
  are present as structural facts; the FULL `≤ 0` converse is
  documented as FALSE with an explicit counter-example (collinear
  disjoint segments).

Binary64 layer ([`theories-flocq/Intersect_b64.v`](../theories-flocq/Intersect_b64.v)):

- `b64_intersect_sign_filtered` — five-valued predicate, four calls to
  `b64_orient_sign_filtered` + case dispatch
  (NaN > Uncertain > same-strict-side > zero-degenerate > proper).
- Structural lemmas: decidable equality, totality, 10-way pairwise
  constructor distinctness, NaN propagation in each of four positions.
- `intersect_inputs_int_safe` precondition + four bridges to the
  underlying `orient2d_inputs_int_safe`.
- `BP2P` lift from `BPoint` to R-side `Point` + the polynomial identity
  `cross_R_BP = cross (BP2P …)`.
- **`b64_intersect_sign_filtered_sound_small_int`** — HEADLINE.
  Match-on-five soundness in the integer regime:

```coq
Theorem b64_intersect_sign_filtered_sound_small_int :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_inputs_int_safe P0 P1 Q0 Q1 ->
    match b64_intersect_sign_filtered P0 P1 Q0 Q1 with
    | IntersectNone =>
        ~ exists X, between (BP2P P0) (BP2P P1) X
                /\ between (BP2P Q0) (BP2P Q1) X
    | IntersectPoint =>
        exists X, between (BP2P P0) (BP2P P1) X
              /\ between (BP2P Q0) (BP2P Q1) X
    | IntersectCollinear => True
    | IntersectNan       => True
    | IntersectUncertain => True
    end.
```

C# consumer ([`NetTopologySuite.Curve` PR #11](https://github.com/NetTopologySuite/NetTopologySuite.Curve/pull/11)):

- `Robust.Intersect.RobustLineIntersector.SignFiltered` mirroring the Coq predicate.
- `RocqRefRunner INTERSECT_FILTERED` driver mode + extraction.
- 187 / 187 differential tests bit-equal: 7 deterministic fixtures, 80
  random uniforms, 8 NaN positions, 5 huge-magnitude, 7 integer-regime
  boundary fixtures, 80 random integer fuzz.

**Open.**

Two pieces remain, each parallel to a Phase 0 deferral:

### IntersectCollinear sub-cases (parallel to `IntersectUncertain` in Phase 0)

The predicate returns `IntersectCollinear` when at least one of the
four orientation tests returned `Zero` but the rejection branch didn't
fire.  This covers a family of degenerate configurations:

- Shared endpoint (e.g. `Q0 = P0`)
- T-junction (one endpoint exactly on the other segment's interior)
- Full collinear overlap
- Collinear-but-disjoint segments

The current predicate makes no positive claim about these cases — the
soundness theorem's `IntersectCollinear` branch is `True` by design.
NTS's `RobustLineIntersector` distinguishes these in C# via 1D
projection checks; formalising that disambiguation would be a separate
slice.

This is **exactly the shape** of Phase 0's `IntersectUncertain`
treatment: the predicate honestly declines to commit, and the
soundness theorem respects that.

### Intersection point coordinates (parallel to Stage D in Phase 0)

The current predicate returns only a 5-valued sign — no
`(x, y)` coordinates for the intersection point.  Computing the
coordinates uses Cramer's rule on a linear system over binary64:

```
t   = ((Q0.x - P0.x)*(Q1.y - Q0.y) - (Q0.y - P0.y)*(Q1.x - Q0.x))
    / ((P1.x - P0.x)*(Q1.y - Q0.y) - (P1.y - P0.y)*(Q1.x - Q0.x))
X.x = P0.x + t*(P1.x - P0.x)
X.y = P0.y + t*(P1.y - P0.y)
```

The denominator is the standard 2D cross product (already in the
corpus).  The numerator is structurally similar.  But **`t` involves
division**, which:

1. Is not yet in the Coq corpus — `B64_bridge.v` covers `b64_plus`,
   `b64_minus`, `b64_mult` but no `b64_div`.
2. Does not preserve the integer-regime exactness story: integer
   numerator / integer denominator is generally not an integer, so
   the rounded `b64_div` result differs from the exact rational.

Closing this gap is a multi-session engagement:

- **Path A** — Add `b64_div` to `B64_bridge.v` via Flocq's `Bdiv`,
  derive a forward-error bound, ship intersection point coordinates
  with bounded error.  Substantial — same shape as Phase 0 Stage D in
  cost.
- **Path B** — Restrict to a regime where division is exact (e.g.
  power-of-two denominators).  Very narrow but completely sound.  No
  obvious practical use case in GIS.
- **Path C (current)** — Defer entirely.  The C# consumer ships the
  predicate only; callers needing coordinates use the standard NTS
  `RobustLineIntersector` (which the project's differential tests
  already cover bit-exactly for the orient2d + intersection-test
  path).

The C# side as shipped uses Path C: PR #11 mirrors the predicate
exactly, and `RobustLineIntersector.SignFiltered` returns the 5-valued
sign.  Coordinate computation, when consumers need it, falls through
to standard NTS — unverified against rounding-induced flips, but
production-tested.

## Why this is "Phase 1 complete"

Phase 1's chokepoint deliverable is a **verified intersection
predicate**: decide whether two segments cross, with honest reporting
of degenerate / uncertain inputs.  That deliverable is shipped
end-to-end:

- Coq-side: integer-regime cross_R soundness for both rejection
  (`IntersectNone`) and existence (`IntersectPoint`) directions, plus
  the R-side `strict_completeness` foundation.
- C#-side: predicate ported, 187 / 187 bit-equal differential tests.

What's open — coordinate computation and fine-grained collinear
sub-cases — is parallel to Phase 0's open Stage D: substantial
separate engagements, not Phase 1 chokepoint work.  Mirroring
[`docs/soundness-strategy.md`](soundness-strategy.md)'s consolidation
discussion: there is no "middle ground" between what's shipped and
the full coordinate / sub-case story that would buy meaningful
intermediate value.

## Future paths

In rough order of payoff vs. cost:

1. **IntersectCollinear sub-case lemmas** — medium slice.  The
   simplest sub-case (`all four orient signs Zero ⇒ check 1D overlap`)
   is doable in pure R-arithmetic; extends the predicate's positive
   claims without touching the binary64 layer.
2. **`b64_div` + forward-error analysis** — large slice, comparable to
   Phase 0 Stage D in scope.  Unlocks intersection point coordinates
   for general inputs.
3. **C# side: extended API parity** — port the rest of NTS's
   `LineIntersector` surface (`IsProper`, `IntersectionPoint`, …)
   pending the binary64 coordinate work.
4. **Phase 2 onward** — snap rounding noder
   (Hobby 1999 + Halperin-Packer 2002), planar overlay (DCEL /
   hypermap), etc.  See the Phase 0–7 chokepoint table in
   [`README.md`](../README.md).

## Audit summary

- **No `Admitted`, `Axiom`, `Parameter`** anywhere in `theories/` or
  `theories-flocq/`.  Same 4-axiom corpus baseline as Phase 0.
- **No `Admitted` placeholder for the deferred pieces.**  The open
  items are *absent* from the corpus, not stubbed — exactly the
  same invariant Phase 0 maintained.
- **No silent narrowing of contracts.**  `IntersectCollinear` is `True`
  in the soundness theorem, mirroring `IntersectUncertain`'s
  treatment in `b64_orient_sign_filtered_sound_small_int`.

## 2026-05-16: Scope A first-stage exactness landed

`theories-flocq/Intersect_b64_exact.v` ships:

- Total binary64 projections `b64_intersect_point_x` / `b64_intersect_point_y`
  (return `binary64`, not `option binary64`).
- Safety predicate `intersect_point_inputs_int_safe` (eight `coord_int_safe`
  premises + R-side denominator non-zero).
- Four first-stage bit-exactness lemmas: the two outer orient2d evaluations
  (`qp0`, `qp1`) and the two coordinate differences (`dx`, `dy`) are
  bit-exact integer-valued binary64 under the safety predicate.
- `HasIntersect` typeclass + `BPoint` instance — operations + safety
  predicate only (no soundness field yet); acts as the extension point
  for future curve primitives (arc-arc, arc-segment) per the Phase 4
  audit's "thin leading wire" direction.

What's still deferred under `Future paths` item 2:

- Denominator finite + B2R non-zero (mechanical, needs the
  `b64_round_abs_le_bpow` chain).
- **Scope B**: round-chain identity for the full coordinate computation.
- **Scope C**: forward-error bound
  `|B2R(b64_intersect_point_x ...) − intersect_x_R| ≤ K · max_coord · ε`.

Bit-exact equality `B2R(...) = intersect_x_R(...)` on the integer regime
is *not* a target — Cramer's rule has a division step (`s = qp0 / den`)
that rounds for non-dyadic ratios (e.g. `1/3`), so the equality fails by
counterexample.  Scope C (forward-error bound) is the real downstream
target for callers.
