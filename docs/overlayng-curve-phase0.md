<!-- doc-kind: guide -->
# OverlayNGCurve Phase 0 — ops mnemonics and the exact-cell kernel (2026-08-15)

topic: overlay
claimId: none
witness: self-ops
mutation-seed: none

(ADR-0004 mint, explicit: this gates table is the Phase 0 **opener**
(`OverlayNGCurve` exact-cell kernel). It stays `claimId: none` / witness
`self-ops` — not stale vs tip. The OverlayTouchRow candidate-complete pin
is a later section: `claimId: laser-ov` (not `laser-ml2`) · witness
`kiss-discs` · mutation-seed `668404`. No oracle-facing micro-kernel
claim is minted on the opener — no `eval/` mirror. The documentation-level
falsifier seed is `self-ops`: the G3/G4 self-cancellations `A ∖ A = ∅`,
`A Δ A = ∅`, whose mutation into G1/G2 keep-laws the crossing probes
would catch. When a board card id is assigned to the opener, the rename +
`eval/ClaimNNN.v` mirror follow in one pass, as for the LEC opener.
ADR-0001 tripwire not needed: Overlay → Distance only; OverlayTouchRow
is a consumer; no Overlay ↔ Jordan / ArcOrient cycle.)

**lane:** overlay · curve-aware overlay algebra
**Module**: [`theories/OverlayNGCurve.v`](../theories/OverlayNGCurve.v)
**Verdict**: **GREEN** — the headline and all eight block lemmas are
Qed-closed; the headline is **axiom-free** (Print Assumptions: closed under
the global context). Pins and probes carry a classical-reals footprint
inside the three-axiom allowlist. No `Admitted`, no new axioms.

**Name gate NTSC0001**: the lane name is `OverlayNGCurve` — never
"OverlayNGCurved".

## The four ops

| Sticky | Symbol | Method | Phrase | Corpus op | Self-op |
|--------|--------|--------|--------|-----------|---------|
| **CAP** | ∩ | `intersection` | Common Area of Partners — only where both stand | `oand` (HeytingOpens) | G1 · A ∩ A → A |
| **CUP** | ∪ | `union` | Cover Under Partners — either side fills the cup | `oor` (HeytingOpens) | G2 · A ∪ A → A |
| **SUB** | ∖ | `difference` | Subtract B's shadow — erase the second from the first | `odiff` (new) | G3 · A ∖ A → ∅ |
| **XOR** | Δ | `symDifference` | eXclusive OR — keep only what isn't shared | `osym` (new) | G4 · A Δ A → ∅ |

The ops live on the `OSet` carrier of `HeytingOpens.v` — the frame of
truth values Ω = O(ℝ²) of the bridge lane — so the overlay algebra and the
spatial-topos lane share one set theory, stated against `osame`/`oincl`
throughout. Memory palace: *CAP/CUP keep me · SUB/XOR empty me · the empty
partner (G5) is the fifth guard.*

## Phase 0 suite → what the corpus proves

| Item | Phrase | Status here |
|------|--------|-------------|
| **G1** · CAP self | I meet myself → me | `g1_cap_self`, Qed |
| **G2** · CUP self | Double pour → same cup | `g2_cup_self`, Qed |
| **G3** · SUB self | Erase myself → empty | `g3_sub_self`, Qed |
| **G4** · XOR self | Mirror cancel → empty | `g4_xor_self`, Qed (axiom-free) |
| **G5** · Empty partner | Nothing in the room | `g5_empty_partner`, Qed (all five laws) |
| **V1** · Wound check | No scrambled shell | engine-side: needs a curve representation layer |
| **V2** · Hole nest | Holes live inside | engine-side: same reason |
| **V3** · Type gate | Curve path for Curve* | engine-side: dispatch policy, not point-set content |
| **R1** · Keep the arc | Retention when representable | engine-side: CurvePolygon representation policy |
| **R2** · Honest approx | Flag when densified | engine-side: result metadata policy |
| **F1** · Fast before fat | Short-circuit before densify | **soundness kernel proved**: the exact cells collapse (headline) |

Instance-level G1 ("same instance / equalsExact") is finer than pointwise
equality and stays engine-side too; what the corpus proves is the
point-set collapse, which is what makes returning the input *correct*.

## Exactness matrix — the provable frontier

Matrix as measured at tip f90dfb42 (approx values are densified vertex
counts, engine measurements):

| case | CAP ∩ | CUP ∪ | SUB ∖ | XOR Δ |
|------|-------|-------|-------|-------|
| self | exact | exact | exact-∅ | exact-∅ |
| empty partner | exact-∅ | exact | exact | exact |
| disjoint | exact-∅ | exact | exact | exact |
| covers | exact | exact | approx 3146 | approx 3146 |
| coveredBy | exact | exact | exact-∅ | approx 3146 |
| crossing | approx 801 | approx 2349 | approx 1575 | approx 3150 |

Exact share: CAP 7/8 · CUP 7/8 · SUB 6/8 · XOR 5/8.

The kernel this lane proves (`overlayng_curve_phase0_exact_cells`): **a
cell is exact precisely when the point-set result collapses to a closed
form over the inputs** — one of A, B, A ∪ B, or ∅:

- **self row** — G1–G4;
- **empty partner row** — G5 (A ∩ ∅ = ∅ · A ∪ ∅ = A · A ∖ ∅ = A ·
  ∅ ∖ A = ∅ · A Δ ∅ = A);
- **disjoint row** — A ∩ B = ∅ · A ∖ B = A · B ∖ A = B · and the
  identity that makes disjoint-XOR exact: **A Δ B = A ∪ B**
  (`disjoint_row_exact`);
- **covers row** (B ⊆ A) — A ∩ B = B · A ∪ B = A (`covers_row_exact`);
- **coveredBy row** (A ⊆ B) — A ∩ B = A · A ∪ B = B · A ∖ B = ∅
  (`coveredby_row_exact`).

That is the F1 soundness argument: in every exact cell the result is
representable by the inputs as given, so the algebra may short-circuit
**before** `CurveOps.linearise` — no arc is ever densified to compute an
answer that was already in hand.

The approx cells are exactly where the collapse **fails**, and the module
witnesses the failure on rational squares (crossing pair [0,2]² × [1,3]²,
covers pair [0,3]² ⊇ [1,2]²):

- crossing CAP is not ∅, CUP is not A, SUB is not A, XOR is not CUP
  (`probe_crossing_cap_not_empty`, `probe_crossing_cup_not_left`,
  `probe_crossing_sub_not_left`, `probe_crossing_xor_not_cup`);
- covers-SUB is neither ∅ nor the outer square — the rim is a genuinely
  new region (`probe_covers_sub_not_empty`, `probe_covers_sub_not_outer`),
  which is why covers-SUB reads approx while covers-CAP/CUP read exact.

So the exact/approx frontier drawn by the headline is tight: every exact
cell collapses, and no probed approx cell does.

## Exact rows instantiated (teaching corollaries)

On the pinned pairs (`pin_disjoint_squares`, `pin_covers_squares`):
`cap_disjoint_squares_empty`, `xor_disjoint_squares_is_cup`,
`cap_covers_squares_is_inner`, `cup_covers_squares_is_outer`.

## Deliberately out of scope on this rung

- V1–V3 validity gates and R1/R2 retention/flagging policy (need a curve
  representation layer the corpus does not define);
- instance-level `equalsExact` (finer than pointwise equality);
- the measured densification counts (801/1575/2349/3146/3150 — engine
  measurements at tip f90dfb42, recorded above verbatim);
- Phase 1+: noding-side correctness (that is the existing
  `OverlayGraph.v` / `OverlayContactSound.v` lane, downstream of this
  algebra).

## Candidate completeness (2026-08-16): REFUTED for the 5-relation matrix, repaired with the TOUCH row

**Module**: [`theories/OverlayTouchRow.v`](../theories/OverlayTouchRow.v) ·
**Verdict**: both halves **GREEN** (Qed, classical-reals trio only).

**Named pin (2026-08-20).** `candidate_complete R` means every pair of
positive-radius closed discs satisfies relation family `R`. Domain =
positive discs; a row = one binary relation on that domain. Distinct from
op-exactness (`overlayng_curve_phase0_exact_cells`: a CAP/CUP/SUB/XOR cell
is exact iff the result collapses to A, B, A∪B or ∅). The seven-row
exactness matrix's *relation content* on this domain is
`seven_row_family` = `phase0_relation` (empty-partner is out of domain;
disc-vs-polygon is representation). The eight-row family is
`eight_row_family` = `phase0_relation ∨ disks_touch` (T-ext only; T-int
is covers). Headlines stay `phase0_relation_complete_hypothesis_refuted`
and `disc_relations_complete_with_touch`; the names
`seven_row_not_candidate_complete` / `eight_row_is_candidate_complete`
are unfolds, not a second headline.
topic: overlay · claimId: laser-ov · witness: kiss-discs · mutation-seed: 668404.

The Phase 0 case matrix at region level (self · disjoint · covers ·
coveredBy · properly-crossing, positive-radius discs) is **not** candidate
complete: `phase0_relation_complete_hypothesis_refuted` exhibits the
externally tangent pair — unit discs at (0,0)/(2,0) — that fits no row,
because `discs_properly_intersect` is deliberately STRICT and tangency
sits exactly on its boundary. The degenerate op values at the kiss are
pinned Qed: CAP collapses to the singleton kiss point
(`ext_cap_singleton`, dimension 0 from a 2-D ∩ 2-D query — the R1
retention boundary case), SUB/XOR are exact-minus-one-point
(`ext_sub_off_by_point` / `ext_xor_off_by_point`), CUP's shell
self-touches (`ext_kiss_on_both_circles`, V1). Internal tangency is not a
gap — covers fires (`int_covers`) — but its SUB annulus pinches
(`int_kiss_pinch`, `int_kiss_not_in_crescent`).

The repair is one new relation row, TOUCH := nonempty intersection with
disjoint interiors, and the completeness theorem is generic:
`disc_relations_complete_with_touch : phase0_relation A B ∨ disks_touch A B`
for all positive discs (trichotomy on d vs |r1 − r2| and r1 + r2; radial
kiss witness c1 + (r1/d)(c2 − c1)). External tangency is exactly the
touch row; internal tangency lands in covers.

`DISC_OVERLAY` already classifies `EXT_TANGENT` / `INT_TANGENT` via the
exact-Q discriminant (generator family E) — the driver was ahead of the
theory; this module supplies the missing R-side spec. No driver/generator
change was needed for this rung.

## The TOUCH pair's DE-9IM (2026-08-16): FF2F01212, cell-sound

**Module**: [`theories/RelateTouchDiscs.v`](../theories/RelateTouchDiscs.v)
· **Verdict**: **GREEN** (Qed; two Reals axioms on the geometry lemmas,
the matrix lemmas closed under the global context).

The same witness pair carried into the relate lane (issue #67): its
DE-9IM matrix is the canonical area/area touches string **FF2F01212**,
and — unlike the lane's hand-specified constant witnesses
(`RelateAreaArea.v`) — every cell is backed by a point-set fact
(`touch_discs_de9im_sound`): the four F-cells are proven empty (the
triangle squeeze at the kiss), BB = 0 is the EXACT singleton {kiss}
(two-line reuse of `ext_cap_singleton`), the three 2-cells each contain
a metric ball, and the two 1-cells are nonempty and ball-free
(`circle_subset_no_ball`, a radial-scale perturbation — dimension ≤ 1;
exact curve-dimension semantics deferred, matching the relate capstone's
own scope). The matrix satisfies OGC `touches` via `pat_touches_1`
(BI = F, BB nonempty). All statements live in the squared metric — no
square roots anywhere in the module.
