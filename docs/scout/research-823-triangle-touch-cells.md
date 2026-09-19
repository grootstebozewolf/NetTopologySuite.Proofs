# Research — #823 Classify triangle-touch's 6 remaining DE-9IM cells

Child of map #822. Read-only research ticket: classify IB/IE/BI/BE/EI/EB
for the shared-edge touch regime (`triangles_touch_on_shared_edge`,
`theories/RelateNGTouch.v`) against the ADR-0003 **specification** tier
(open interior, `0 < gtri`). No `.v` files were written or modified.

## Headline finding

**The question is already answered on `main`, Qed, and the answer is
happier than the II precedent suggests.** `theories/RelateNGTouchEdgeCells.v`
(`touch_edge_pair_ogc_gtri_cells`, landed via #593) proves all nine gtri
cells for a frozen witness pair `A=(0,0)(1,0)(0,1)`,
`B=(1,0)(1,1)(0,1)`, matching OGC `FF2F11212`:

| Cell | Value | Witness lemma |
|---|---|---|
| II | F | `touch_ii_empty` |
| IB | F | `touch_ib_empty` |
| IE | 2 | `touch_ie_dim2` |
| BI | F | `touch_bi_empty` |
| BB | 1 | `touch_bb_dim1` |
| BE | 1 | `touch_be_dim1` |
| EI | 2 | `touch_ei_dim2` |
| EB | 1 | `touch_eb_dim1` |
| EE | 2 | `touch_ee_dim2` |

This is Qed for one concrete pair (the same witness-instance style used by
`RelateNGDisjointCells.v`, `RelateNGOverlapCells.v`, `RelateNGContainsCells.v`
— none of the four bar-2 modules states a `forall`-quantified nine-cell
theorem over the whole regime). The research task below is: for each of
the six cells, is the *general* (any touching pair) claim (a) an
unconditional constant, (b) a constant needing a named guard, or (c) not a
fixed constant at all — and does the II guard story recur?

## Key generalizable lemma: `touch_int_ext_exclusion`

```coq
(* theories/RelateNGTouch.v:200 *)
Lemma touch_int_ext_exclusion :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy p,
    triangles_touch_on_shared_edge (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
                                   (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) ->
    0 < gtri ax ay bx by_ cx cy p ->
    gtri dx dy ex ey fx fy p < 0.
```

This is **already fully general** (`forall` over all six vertices and the
witness point `p`), proved by pure algebra (`nra` case-bash over the 18
`shares_edge`/`opposite_sides` disjuncts) — no CCW hypothesis, no
`ring_complement`, no `ray_avoids_vertices`. It never touches `point_set`;
it is stated entirely in the `gtri` (specified-interior) vocabulary. This
is the crucial contrast with II: II's *guard* need
(`ring_complement`/`ray_avoids_vertices`, `touch_triangle_pair_ii_cell_via_seam`)
is a property of the **bridge** from parity `point_set` up to `gtri`
(`gtri_point_in_ring_imp_pos`), not a property of `gtri`-vocabulary claims
themselves. `touch_triangle_pair_ii_disjoint_unconditional` already makes
this point for II (the geometric-interior separation is guard-free); the
six remaining cells inherit the same pattern.

## Per-cell classification

### IB — unconditional (a), empty (F)

Direct corollary of `touch_int_ext_exclusion`: if `0 < gtriA p` then
`gtriB p < 0`, hence `gtriB p <> 0`, so `IB := (0<gtriA p) /\ (gtriB p = 0)`
is unconditionally empty for *any* shared-edge touch pair, no guard,
no CCW hypothesis. Witness instance: `touch_ib_empty`.

### BI — unconditional (a), empty (F)

Symmetric to IB (swap A/B roles). `touch_int_ext_exclusion` is stated with
a fixed argument order (`ax..fx` then `dx..fx`); reusing it for the
opposite direction needs `triangles_touch_on_shared_edge` re-established
with A and B swapped. No `triangles_touch_on_shared_edge_sym` lemma exists
in the corpus today, but the predicate's own 9-disjunct/18-case shape is
manifestly symmetric under swapping `(a1,a2,a3)` and `(b1,b2,b3)` (each
`shares_edge`/`opposite_sides` disjunct has a mirror disjunct with the
roles reversed), so a `_sym` companion is a same-technique `nra` case-bash,
not a new mathematical fact. The witness instance (`touch_bi_empty`) is
Qed today via a more manual route (`gtri_nonneg_iff`/`gtri_pos_iff` slack
comparison against `sentinel_A_gs`/`touch_B_gs`), which independently
confirms the value without needing the swap lemma to exist yet.

### IE — unconditional (a), dim-2

Also a direct corollary of `touch_int_ext_exclusion`: for a non-degenerate
triangle, `int(A)` (`0 < gtri A`) is a non-empty open (dim-2) set, and
every point of it lands in `ext(B)` by the same exclusion lemma — so
`IE := int(A) ∩ ext(B) = int(A)` exactly, unconditionally dim-2. Witness
instance: `touch_ie_dim2` (uses a concrete open disk, but the underlying
inclusion is the same guard-free algebraic fact).

### EI — unconditional (a), dim-2

Symmetric to IE; same swap-gap noted under BI (mechanical, not a genuine
proof obstacle). Witness instance: `touch_ei_dim2`.

### BE — unconditional in principle (a), dim-1; general form not yet Qed

`BE := bnd(A) ∩ ext(B)`. Two triangles sharing exactly one full edge, with
third vertices on opposite sides (`opposite_sides`), are convex hulls that
each lie entirely in one closed half-plane bounded by the shared edge's
line — a triangle's two vertices *not* on a given edge's line force the
whole hull onto that vertex's side. So off the shared-edge line, `A` and
`B` cannot meet at all: any point of `bnd(A)` that is not on the shared
edge segment (i.e., on one of A's other two edges, which are non-degenerate
since the triangle is valid) is strictly on A's side of the line and hence
strictly outside B's closed half-plane, i.e., in `ext(B)`. This is the same
"triangle ⊂ half-plane" fact `touch_int_ext_exclusion`'s `nra` case-bash
already exploits internally (`g_sum`, `gsA/gsB/gsC` slacks) — it should
extend by the same technique to a `forall`-quantified `BE` lemma, but no
such general lemma exists in the corpus yet. It is Qed for the frozen
witness (`touch_be_dim1`, using concrete points on A's base edge away from
the shared hypotenuse). No CCW/ring-complement/ray-genericity guard is
needed for this argument either — it is pure convex separation in the
`gtri`/half-plane vocabulary.

### EB — unconditional in principle (a), dim-1; general form not yet Qed

Symmetric to BE (B's non-shared edges lie in `ext(A)`). Same status:
plausible unconditional general lemma by the identical half-plane
argument, Qed today only on the frozen witness (`touch_eb_dim1`).

## Does the II guard story recur for these six?

**No — and that is the interesting negative result.** The
`ring_complement`/`ray_avoids_vertices` guard is specific to lifting the
half-open **computation** tier (`point_set`, ray parity) up to the open
**specification** tier (`0 < gtri`) — it is a property of the bridge
`gtri_point_in_ring_imp_pos`, exercised by II because
`touch_triangle_pair_ii_cell_via_seam` is stated in `point_set` vocabulary
and needs that lift. None of IB/BI/IE/EI/BE/EB, as classified above, ever
crosses that bridge: `touch_int_ext_exclusion` and the half-plane argument
for BE/EB are pure `gtri`-vocabulary facts, so they need no CCW hypothesis
and no `ring_complement`/`ray_avoids_vertices` guard at all. Per ADR-0003's
own framing, all six are provable *unconditionally* at the specified
(open-interior) tier — matching consequence 1 of the ADR ("the nine-cell
capstone becomes tractable... a matrix asserting F is provable").

One caveat: the ADR's context section speculatively described "BI and
side-E\*" as becoming `F` cells once specified against the open interior.
The actual Qed result (`touch_edge_pair_ogc_gtri_cells`, `FF2F11212`) shows
only IB and BI are `F`; IE/EI/BE/EB are **not** `F` — they are dim-2/dim-1
non-empty cells, matching the standard OGC "touching areas along a shared
boundary segment" pattern. The ADR's prose is imprecise on this point; the
Coq result (landed after the ADR, via #593) is the correct account and
this report follows it. (c) genuinely-not-a-constant does not apply to any
of the six: every cell's dimension is a fixed constant for *any*
non-degenerate shared-edge touch pair (dimensionality only depends on
non-degeneracy of the triangles, guaranteed by the touch predicate's
positive-length shared edge and the two non-shared edges).

## Summary table

| Cell | Class | Value | Status |
|---|---|---|---|
| IB | (a) unconditional | F | Direct corollary of `touch_int_ext_exclusion`; witness Qed `touch_ib_empty` |
| BI | (a) unconditional | F | Symmetric corollary; needs a mechanical `_sym` companion (not yet named); witness Qed `touch_bi_empty` |
| IE | (a) unconditional | 2 | Direct corollary of `touch_int_ext_exclusion`; witness Qed `touch_ie_dim2` |
| EI | (a) unconditional | 2 | Symmetric corollary, same swap-gap as BI; witness Qed `touch_ei_dim2` |
| BE | (a) unconditional (argument sketched, general lemma not yet Qed) | 1 | Half-plane / convex-separation argument; witness Qed `touch_be_dim1` |
| EB | (a) unconditional (argument sketched, general lemma not yet Qed) | 1 | Symmetric half-plane argument; witness Qed `touch_eb_dim1` |

No cell in this set requires a guard analogous to
`ring_complement`/`ray_avoids_vertices`, and none is a genuinely
configuration-varying (c) case. The remaining formalization gap is
narrow and mechanical: (1) a `triangles_touch_on_shared_edge` swap/symmetry
lemma to turn `touch_int_ext_exclusion` into its BI/EI mirror without
per-witness slack arithmetic, and (2) a general (`forall`-quantified)
half-plane lemma for BE/EB parallel to `touch_int_ext_exclusion`'s
case-bash. Both are same-technique extensions of code already on `main`,
not new mathematics — consistent with the four bar-2 modules
(`RelateNGDisjointCells.v`, `RelateNGContainsCells.v`,
`RelateNGTouchEdgeCells.v`, `RelateNGOverlapCells.v`) all having proved
their nine cells only per-witness, not `forall`-quantified over the
regime, so generalizing all four regimes' cells is a coherent follow-up,
not specific to touch.

## Sources read

- `theories/RelateNGTouchCells.v` (II/BB/EE, the seam, `gtri_point_in_ring_imp_pos`)
- `theories/RelateNGTouchRED.v` (`touch_triangle_ii_separation_not_unconditional`, the II guard-necessity counterexample)
- `theories/RelateNGTouch.v` (`triangles_touch_on_shared_edge`, `touch_int_ext_exclusion{,_weak}`, `touch_triangle_pair_strict_ii_no_common`)
- `theories/RelateNGTouchEdgeCells.v` (`touch_edge_pair_ogc_gtri_cells`, the actual nine-cell Qed on the frozen witness pair)
- `theories/RelateNGOverlapCells.v`, `theories/RelateNGDisjointCells.v` (parallel witness-based bar-2 pattern for other regimes)
- `docs/adr/ADR-0003-two-tier-interior-spec-parity-computation.md`
- `docs/relate-ng-status.md`, `docs/scout/map-522.md`
