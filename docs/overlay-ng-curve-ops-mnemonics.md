<!-- doc-kind: guide -->
# OverlayNGCurve · ops mnemonics

**Name:** `OverlayNGCurve` (NTSC0001: never `OverlayNGCurved`)

**Homes:**

- Implementation: `NetTopologySuite.Curve` → `CurveGeometryOverlay.OverlayNGCurve`
- Spec algebra: `theories/Overlay.v` (`boolean_op_*_self*`)
- Empirical scorecards: `docs/curve-polygon-self-overlay-guardrails.md`

---

## Four ops

| Sticky | Symbol | Method | Phrase | Self-op |
|--------|--------|--------|--------|---------|
| **CAP** | ∩ | `intersection` | **C**ommon **A**rea of **P**artners — only where both stand | G1 · A ∩ A → A  (I meet myself → me) |
| **CUP** | ∪ | `union` | **C**over **U**nder **P**artners — either side fills the cup | G2 · A ∪ A → A  (double pour → same cup) |
| **SUB** | ∖ | `difference` | **S**ubtract B’s shadow — erase the second from the first | G3 · A ∖ A → ∅  (erase myself → empty) |
| **XOR** | Δ | `symDifference` | e**X**clusive **OR** — keep only what isn’t shared | G4 · A Δ A → ∅  (mirror cancel → empty) |

---

## Phase 0 suite

### Self-ops & empty partner

| Id | Sticky | Phrase | Spec |
|----|--------|--------|------|
| **G1** | CAP self | *I meet myself → me* | A ∩ A → A (same instance / `EqualsExact` curve) |
| **G2** | CUP self | *Double pour → same cup* | A ∪ A → A |
| **G3** | SUB self | *Erase myself → empty* | A ∖ A → ∅ |
| **G4** | XOR self | *Mirror cancel → empty* | A Δ A → ∅ |
| **G5** | Empty partner | *Nothing in the room* | A ∩ ∅ → ∅ · A ∪ ∅ → A · A ∖ ∅ → A · ∅ ∖ A → ∅ |

### Preconditions & policy

| Id | Name | Phrase | Spec |
|----|------|--------|------|
| **V1** | Wound check | *No scrambled shell* | Reject multi-wound / self-crossing structural shells before noding |
| **V2** | Hole nest | *Holes live inside* | Hole rings properly interior to shell (curve-aware envelope) |
| **V3** | Type gate | *Curve path for Curve\** | Lineal/`Curve*` inputs take **OverlayNGCurve** — never silent stock NG only |
| **R1** | Keep the arc | *Retention when representable* | Both CP + result representable as CP → return `CurvePolygon`, not dense `Polygon` |
| **R2** | Honest approx | *Flag when densified* | `Linearize(tol)`+OverlayNG must set approx / document non-exact |
| **F1** | Fast before fat | *Short-circuit before densify* | G1–G5 algebra runs **before** densify/flatten — ratchet vs densify path |

---

## What candidate-complete means (disc-pair overlay relations)

**Definition.** A family `R` of binary relations on closed discs is
**candidate-complete** when every pair of *positive-radius* discs is
classified by `R`:

```
candidate_complete R  :=
  ∀ A B,  0 < r(A) → 0 < r(B) → R A B
```

Domain = positive-radius closed discs. A **row** is one relation on that
domain. This is the classification of *input pairs*, not the exactness of
CAP ∩ / CUP ∪ / SUB ∖ / XOR Δ cells (`overlayng_curve_phase0_exact_cells`).
A complete family can still have inexact op cells (crossing CAP is approx);
an exactness score on listed rows does not make the family complete if
some pair fits no row. The **display** exactness matrix has nine rows
(seven plus T-ext plus T-in shown as covers, not a tenth candidate).
Shares on that board: CAP 8/9 · CUP 9/9 · SUB 8/9 · XOR 8/9. CUP is the
only op still exact on every display row. T-ext CAP is regularized ∅
(R1 unmeetable); T-ext SUB/XOR are off-by-point; T-in SUB/XOR pay V1 pinch.

The seven-row exactness matrix (self · empty partner · disjoint · covers ·
coveredBy · crossing · disc-vs-polygon) contributes **five** relations on
this domain — empty-partner is excluded by positive radii; disc-vs-polygon
is representation, not a disc-pair relation. Those five are
`phase0_relation` (`seven_row_family`). Adding T-ext (TOUCH) is
`eight_row_family`. T-int is covers, not a missing candidate.

Pin: `OverlayTouchRow.candidate_complete`. Headlines (unchanged):
`phase0_relation_complete_hypothesis_refuted` /
`disc_relations_complete_with_touch`. Aliases:
`seven_row_not_candidate_complete` / `eight_row_is_candidate_complete`.

## The missing row: TOUCH (T) — one kiss, no shared flesh

The seven-row family is **not candidate complete**: two externally tangent
discs fit no row — not disjoint (they share the kiss point), neither
covers, and `crossing` demands STRICT |r1 − r2| < d < r1 + r2, which fails
at d = r1 + r2. Refuted Qed:
`OverlayTouchRow.phase0_relation_complete_hypothesis_refuted` /
`seven_row_not_candidate_complete` (witness: unit discs at (0,0) and (2,0),
kiss (1,0); `t_ext_misses_seven_row`).

**T-ext** · External tangency — d = r1 + r2 — the DIMENSION COLLAPSE row:

| Op | Value at the kiss | Qed |
|----|-------------------|-----|
| **CAP** ∩ | exactly the SINGLETON {kiss} — a 2-D ∩ 2-D collapsing to dimension 0; regularized CAP is ∅ (interiors never meet); R1 retention is unmeetable — a point is no CurvePolygon | `ext_cap_singleton` · `ext_cap_interiors_empty` |
| **CUP** ∪ | exact as a set, but the shell SELF-TOUCHES at the kiss — V1 wound-check territory | `ext_kiss_on_both_circles` |
| **SUB** ∖ | the full disc minus ONE point — exact-minus-kiss | `ext_sub_off_by_point` |
| **XOR** Δ | the blob minus ONE point — exact-minus-kiss | `ext_xor_off_by_point` |

**T-int** · Internal tangency — d = |r1 − r2| > 0 — NOT a completeness gap
(the covers/coveredBy row fires: `int_covers` / `t_int_is_covers_not_a_gap`)
but an ANSWER degeneracy: the SUB annulus PINCHES where inner and outer
boundaries meet (`int_kiss_pinch`), and the closed-region crescent misses
its own pinch point (`int_kiss_not_in_crescent`) — V1 again.

**Repaired completeness** (Qed, the hypothesized-complete algorithm): add
ONE relation row — TOUCH := nonempty ∩ with disjoint interiors — and the
eight-row family is candidate-complete over positive discs:

> `candidate_complete eight_row_family` —
> `phase0_relation A B ∨ disks_touch A B` —
> `OverlayTouchRow.disc_relations_complete_with_touch` /
> `eight_row_is_candidate_complete`, by trichotomy of d against
> |r1 − r2| and r1 + r2; the kiss witness is the radial point
> c1 + (r1/d)(c2 − c1).  External tangency IS the touch row
> (`t_ext_is_eight_row_touch`); internal tangency lands in covers.
> The nine-row *display* matrix lists T-in for contrast; it is not a
> tenth candidate.

`DISC_OVERLAY` classified `EXT_TANGENT` / `INT_TANGENT` by exact-Q
discriminant = 0 before the R-side had a spec (generator family E) — this
module supplies the spec the driver was already honouring.

## Memory palace

1. **CAP** ∩ — Common Area of Partners  
2. **CUP** ∪ — Cover Under Partners  
3. **SUB** ∖ — Subtract the second  
4. **XOR** Δ — eXclusive OR (not shared)  
5. **TOUCH** T — one kiss, no shared flesh

**Self:** CAP/CUP keep me · SUB/XOR empty me · **Empty partner (G5)** is the fifth guard · **One kiss (T)** collapses CAP to a point.

---

## Phase 0 implementation map (2026-08)

| Suite id | OverlayNGCurve today |
|----------|----------------------|
| G1–G4 | **Green** when `ReferenceEquals` or `EqualsExact` — short-circuit before flatten |
| G5 | Partially via base `GeometryOverlay` empty cases; Curve path inherits them |
| F1 | **Green** for G1–G4 self-ops (short-circuit before `Flatten`) |
| R1 | **Green** for G1/G2 self (return `Copy()` of curve) |
| R2 | **Open** — densify path still silent (no approx flag) |
| V1–V3 | **Open** — preconditions / dispatch policy not yet enforced |

---

## Id discipline

**This numbering is canonical** for board, tests, and scorecards:

G1 CAP · G2 CUP · G3 SUB · G4 XOR · G5 empty partner · G6 completes · V* · R* · F1.

`docs/curve-polygon-self-overlay-guardrails.md` uses the same ids (no parallel
legacy table).
