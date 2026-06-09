# Library audit: snap rounding for Phase 2

**Question.** To formalise a verified snap-rounding noder
(`SnapRoundingNoder_b64` in the project's Phase 0–7 chokepoint table),
what's reusable from Phase 0/1, what would need to be vendored from
companion libraries, and what would need to be built from scratch?

**Decision driver.** The corpus invariant (no `Admitted` / `Axiom` /
`Parameter` in `theories/` or `theories-flocq/`) makes "reuse" much
cheaper than "vendor", and "vendor" much cheaper than "build".  Phase 2
is the first chokepoint where the bulk of the new work is *algorithmic
and combinatorial* rather than *arithmetic* — Phase 0/1 were about
sign correctness of polynomial expressions over binary64; Phase 2 is
about topological correctness of a whole-arrangement transformation.

---

> **Status note (2026-06-09).** This is the 2026-05-15 *scoping* audit
> (reuse/vendor/build sizing); Phase 2 has since largely **landed**, so read
> the estimates below as planning history, not current state:
>
> - **Shipped (Qed-closed):** `HotPixel.v` / `HotPixel_b64.v`,
>   `SnapRounding_b64.v` (snap preserves passes-through; bit-level
>   idempotence), the `PassesThrough_*` family — including the C1
>   grid-exactness reduction and the honest machine-checked *negatives* (the
>   rounded filter is unsound / incomplete / order-asymmetric, the
>   JTS#752/#1133 root) — and `hobby_theorem_4_1_conditional`. See
>   `docs/verified-claims.md` Phase 2.
> - **§2.4's *unconditional* `snap_rounding_topologically_consistent` is NOT
>   what landed.** The Hobby endpoint-preservation lemma it leans on
>   (`hobby_lemma_4_3_no_proper`) was machine-checked **FALSE as stated** —
>   snapping can *manufacture* a proper intersection (two parallel segments
>   collapse onto one grid line). It now sits in the **counterexample**
>   registry, and the topological-consistency result lands only in
>   *conditional* form. `hobby_lemma_4_2` is Qed-closed. See
>   `docs/hobby-lemma-4-3-no-proper-refutation.md` and
>   `docs/admitted-counterexamples.txt`.

---

## 0. What snap rounding is, and why NTS needs it

**Input.** A finite set `S = {s_1, ..., s_n}` of line segments in the
plane.  Endpoints may have arbitrary real-valued (or, in practice,
binary64-valued) coordinates.  Segments may cross arbitrarily.

**Goal.** Produce an output set `S'` of segments such that:

1. **Quantised vertices.** Every endpoint of every output segment lies
   on a fixed integer grid (the "hot pixel" grid at resolution `r`).
2. **Topological faithfulness.** Two input segments that cross at point
   `X` share an output vertex at the hot pixel containing `X`.
3. **Bounded displacement.** Every output vertex is within
   `√2 / (2r)` of its corresponding input feature (endpoint or
   intersection).
4. **Termination + finite size.** `|S'|` is `O(n + k)` where `k` is
   the number of intersections.

The output is **topologically consistent**: an overlay or planar
subdivision algorithm consuming `S'` will not encounter near-degenerate
intersections that flip sign under further rounding.  This is exactly
what gates Phase 3 (`OverlayNG_b64`) — overlay needs noded input or
it produces non-manifold output.

**Algorithm sketch (Hobby 1999).**

1. Compute every pairwise intersection of segments in `S`.
2. A "hot pixel" is a unit-grid square centred on an integer point
   that contains an input endpoint or a computed intersection.
3. For each input segment, find the sequence of hot pixels it
   passes through (its **passes-through set**).
4. Replace each input segment with the polyline that visits its
   passes-through hot pixels in order, snapped to the pixel centres.

**Iterated Snap Rounding (Halperin & Packer 2002).** Plain snap
rounding has a subtle defect: an output segment can come arbitrarily
close to a *non-incident* hot pixel (one its input segment didn't
originally pass through) without entering it, producing a numerically
fragile result.  ISR re-runs the snap-rounding step until every
output segment maintains a minimum distance from every non-incident
hot pixel.

**Why NTS uses this.** `SnapRoundingNoder` is a core upstream NTS
class.  Overlay (`OverlayNG`) and most planar-set algorithms require
its output's topological consistency.  Without it, a finite-precision
intersection computation can produce two "intersection points" that
should geometrically be one — and downstream overlay then produces a
non-manifold mess.

---

## 1. What's in Phase 0 / Phase 1 that we reuse

Phase 0/1 give us the **pointwise primitives** snap rounding needs:

### 1.1 Orientation predicate (Phase 0)

`b64_orient_sign_filtered` in `theories-flocq/Orientation_b64.v`.

Used inside snap rounding for:
- "Is point P on segment Q0Q1?" (orient = Zero plus a between test).
- "Do segments AB and CD cross?" (composed in Phase 1's
  `b64_intersect_sign_filtered`).
- "Which side of the segment AB does hot pixel center P lie on?"
  (Stage A filter case).

**Integer-regime cross_R soundness** (`b64_orient_sign_filtered_sound_small_int`)
applies directly: snap-rounding outputs have integer-valued
coordinates by construction, so every orientation test in the
*output* phase is in the proved-sound regime.

### 1.2 Intersection predicate (Phase 1)

`b64_intersect_sign_filtered` in `theories-flocq/Intersect_b64.v`.

Used inside snap rounding for:
- The initial step of computing input-segment intersections.  In the
  general (non-integer) regime this is *not* proved sound — the
  `IntersectCollinear` and `IntersectUncertain` branches make no
  positive claim.
- Hot-pixel computation: every intersection point feeds a hot pixel.
- After snapping: re-verifying that the output is consistent (in the
  integer regime, soundness holds).

### 1.3 BPoint + integer regime predicates

`coord_int_safe`, `intersect_inputs_int_safe`, `orient2d_inputs_int_safe`.

Snap rounding's output is by construction integer-valued.  These
predicates carry the soundness story for output verification.

### 1.4 R-side machinery

`theories/Intersect.v`'s `strict_completeness` + `Intersect.v` /
`Segment.v` / `Orientation.v` lemmas.

These are usable for the *mathematical model* of snap rounding —
defining what topological consistency means in pure ℝ — without ever
touching binary64.  The binary64 implementation correctness then
follows from the integer-regime soundness above.

---

## 2. What's not in our corpus — the genuine Phase 2 scope

Nearly everything *snap-rounding-specific*.  Phase 0/1 give us the
operations; Phase 2 builds the algorithm and the topological theorems.

### 2.1 Hot pixel data structure

A `HotPixel` is an integer grid centre `(cx, cy)` with an implicit
half-side `1/(2r)` for some chosen resolution `r`.  Predicates:

- `point_in_hot_pixel : Point → HotPixel → Prop` — `|p.x - cx| ≤ 1/(2r)`
  and similarly for `y`.
- `segment_intersects_pixel : Segment → HotPixel → Prop` —
  geometric: any point of the segment is inside the pixel.
- Decision procedures for both, in binary64 (the algorithmic versions
  the C# consumer will call) and ℝ (the abstract model).

**Effort:** ~1 week.  Mostly straightforward set-theoretic work; the
decision procedures need careful magnitude bookkeeping but no new
arithmetic primitives.

### 2.2 The pass-through relation

Given a segment `s = (P, Q)` and a hot pixel `H`, `passes_through s H`
holds iff `s` enters `H`.  For the snap-rounding output to be correct,
this relation needs:

- A decision procedure (yes/no) callable in the algorithm.
- A soundness theorem against the geometric definition.
- A bounded-cost computation: for a segment in a grid of resolution
  `r` over a `K × K` extent, the pass-through count is `O(K · r)`
  (visits each cell once via a digital-line-traversal algorithm).

**Effort:** ~2 weeks.  The digital-line algorithm (Bresenham-style)
is well-studied; lifting it to a correctness proof against the
geometric definition is the work.

### 2.3 The snap-rounding algorithm itself

```
Input:  S = {s_1, ..., s_n} segments.
Output: S' = snap-rounded segments.

1. C := pairwise-intersection-points(S)             (* uses Phase 1 *)
2. P := endpoints(S) ∪ C
3. H := {hot_pixel_containing(p) | p ∈ P}           (* the hot set *)
4. for each s ∈ S:
       H_s := {h ∈ H | passes_through s h}         (* in order along s *)
       emit segment-chain through centres(H_s)
5. return chain of emitted segments.
```

The algorithm itself is straightforward.  Proving it correct is not.

**Effort:** ~3 weeks for the implementation + structural lemmas.

### 2.4 Topological correctness theorem (the hard one)

```coq
Theorem snap_rounding_topologically_consistent :
  forall (S : list Segment),
    well_formed S ->
    let S' := snap_round S in
    (forall s1 s2 ∈ S, share_point s1 s2 ->
       exists v ∈ vertices(S'), v ∈ s1' ∩ s2'
       where s1', s2' are the snapped versions) /\
    no_spurious_intersections S'.
```

This is where the bulk of the formalisation work lives.  Hobby 1999's
proof relies on a clever geometric argument about the convex hull of
each segment's pass-through pixels.  Formalising it requires:

- A precise notion of "topological consistency" for segment
  arrangements.
- Either a formalisation of Hobby's hull argument, or a different
  proof strategy (induction on the algorithm steps).
- Careful handling of edge cases — collinear input segments,
  overlapping endpoints, degenerate intersections.

**Effort:** ~6-10 weeks.  This is the major thesis-shaped piece.

### 2.5 Bounded-displacement theorem

```coq
Theorem snap_rounding_displacement :
  forall (S : list Segment) (s ∈ S) (v ∈ vertices(snapped s)),
    exists (feature : InputFeature S),
      distance v feature <= √2 / (2 * r).
```

Easier than topological consistency; mostly a triangle-inequality
argument plus the hot-pixel definition.

**Effort:** ~1-2 weeks.

### 2.6 ISR refinement (Halperin & Packer)

The iterated variant.  Proves that after sufficient iterations
(provably at most `O(n)`), the output guarantees minimum separation
between non-incident features.

**Effort:** ~3-5 weeks.  Builds on plain snap rounding; smaller scope.

### 2.7 C# consumer and differential testing

`Robust.SnapRound.SnapRoundingNoder` mirroring the Coq predicate.
Differential testing against the Coq-extracted reference via a new
`NODE` mode in `RocqRefRunner`.

**Effort:** ~1-2 weeks once the Coq side is shipped (the pattern is
established from Phase 0 / Phase 1).

---

## 3. What's not in Flocq, and why that's fine

Flocq is about floating-point error bounds.  Snap rounding is about
**combinatorial topology of integer-grid arrangements**.  These are
disjoint mathematical domains; we shouldn't expect Flocq to have any
direct contribution.

The Flocq pieces we *do* use are inherited via Phase 0/1: the binary64
orientation and intersection predicates.  Snap rounding's quantised
output puts everything into the integer regime where those predicates
are proved sound on the nose.

---

## 4. No turnkey vendor target

No public Coq formalisation of snap rounding appears to exist as of
2026-05-15.  Related work in computational geometry / formal methods:

- **CGAL's snap-rounded arrangements** (C++, not formalised).
- **Halperin & Packer 2002 ISR** is the canonical paper.
- **Boldo / Melquiond** have published Flocq-based formalisations of
  numerical algorithms, but the closest topics are interval arithmetic
  and FMA — not arrangement topology.
- **Pichardie et al.** have formalised some computational-geometry
  algorithms (convex hull, polygon clipping) in Coq, but not snap
  rounding to our knowledge.

Phase 2 is greenfield in the formal-methods sense.

---

## 5. Reuse / vendor / build call

| Component | Action | Effort | Notes |
|---|---|---|---|
| `b64_orient_sign_filtered` | **Reuse** (Phase 0) | — | Direct: hot-pixel containment, segment side tests |
| `b64_intersect_sign_filtered` | **Reuse** (Phase 1) | — | Direct: compute input intersections |
| Integer-regime soundness theorems | **Reuse** | — | Output is integer-valued, so Phase 0/1 soundness covers post-snap verification |
| R-side `cross`, `between`, `strict_completeness` | **Reuse** | — | Abstract model of snap rounding |
| `HotPixel` record + containment predicates | **Build** | ~1 wk | New abstraction; trivial geometry |
| `passes_through` decision procedure | **Build** | ~2 wks | Digital-line traversal + soundness proof |
| Snap-rounding algorithm `snap_round` | **Build** | ~3 wks | Coq `Definition` + structural lemmas |
| Topological correctness theorem | **Build** | ~6-10 wks | **The major thesis-shaped piece** |
| Bounded-displacement theorem | **Build** | ~1-2 wks | Mostly triangle inequality |
| ISR refinement | **Build** | ~3-5 wks | Optional / second-iteration improvement |
| C# `Robust.SnapRound.SnapRoundingNoder` | **Build** | ~1-2 wks | Mirrors the Coq predicate, RocqRefRunner `NODE` mode |

**Total Phase 2 scope:** 4–7 months focused work.  This is
qualitatively larger than Phase 0 (~3 weeks) or Phase 1 (~1 week) —
the bulk is the topological correctness theorem, which is genuinely
research-shaped.

---

## 6. First-slice scope: what to ship next

The natural first slice mirrors Phase 0's opening move
(`Validate_binary64.v` + `Orientation_b64.v`) and Phase 1's
(`Intersect_b64.v` predicate + structural lemmas).

**Phase 2 first slice: `HotPixel.v` and `HotPixel_b64.v`.**

Build the foundational data structure and decision procedures:

- `theories/HotPixel.v` — abstract R-side model:
  - `Record HotPixel := { hp_cx : Z; hp_cy : Z }` (integer-centred).
  - `point_in_hot_pixel : Point → HotPixel → Prop` (containment).
  - `Lemma point_in_hot_pixel_dec` — decidability over R.
  - `Lemma hot_pixels_disjoint` — distinct hot pixels do not overlap
    (modulo boundary).
- `theories-flocq/HotPixel_b64.v` — binary64 layer:
  - `b64_point_in_hot_pixel : BPoint → HotPixel → bool`.
  - Soundness against the R-side model in the integer-regime input.
  - Structural lemmas (decidability, totality, NaN safety).

This gives a Qed-closed foundation to build on, ships in 1-2 sessions,
and validates the integer-regime soundness pattern transfers cleanly
to grid-quantised geometry.

After that, slice 2 is `passes_through`, slice 3 is the algorithm,
and the topological theorem is the multi-session engagement that
defines Phase 2's character.

---

## 7. Audit summary

- **Reused from Phase 0/1:** orientation, intersection, integer-regime
  soundness, R-side `between` / `cross` machinery.  Substantial — Phase
  2 doesn't redo any pointwise predicate work.
- **Vendored:** nothing; no turnkey target exists.
- **Built:** hot-pixel data structure, pass-through relation, algorithm,
  topological correctness theorem, bounded displacement, ISR refinement.
- **Character of the work:** combinatorial / topological, not arithmetic.
  The bulk is the topological correctness theorem — genuinely
  research-shaped, 6-10 weeks for a focused engagement.
- **Corpus invariant:** maintained throughout.  No `Admitted` / `Axiom`
  / `Parameter` planned for any slice.

Phase 2 is a **multi-month engagement**, qualitatively different from
Phase 0/1.  Whether to commit to it now (as a thesis-scale piece of
work) or queue it behind smaller follow-ons is a strategic call —
Phase 1 left two natural follow-ons (`b64_div` + intersection point
coordinates, IntersectCollinear sub-cases) that fit between Phase 0/1
and Phase 2 in size.
