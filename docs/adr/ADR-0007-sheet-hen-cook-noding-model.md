# ADR-0007 — The noding constructor is part of the specification: sheet, hen, cook

| Field | Value |
|---------------|--------------------------------------------------------------|
| **Order** | ADR-0007 |
| **Status** | **Accepted** — 2026-09-07 (Joost, BDFL) |
| **Deciders** | Joost (BDFL); proposed by Jeroen Bloemscheer |
| **Date** | 2026-09-05 |
| **Superseded by** | — (none) |

Status lifecycle: *Proposed → Accepted / Rejected → (possibly) Superseded*.

QEX is not acceptance of a missing constructor. BDFL Accepted the sheet/hen/cook frame on 2026-09-07.

---

## Context (self-contained)

Almost every theorem in this corpus is a statement about an arrangement in
which every intersection is already a vertex, every edge is a simple open arc
between two vertices, and two edges meet only at a shared vertex. Noding is
the step that produces such an arrangement. The corpus does not have that
step, and the gap is not visible in the types.

Four places where it is currently assumed rather than produced:

* **Snap-rounding.** `HobbyTheorem_b64.v` takes `fully_intersected` as
  hypothesis and concludes `fully_intersected` of the rounded image. It
  discretises an arrangement that is already noded; it does not build one.
* **The "noding discharge" is not one.** `NodingSeparation_b64.v`'s
  `fully_intersected_snap_of_nodable` discharges that hypothesis — from
  `pairwise_nodable`, which requires every distinct pair to *either share an
  endpoint or be separated*. The case a noder exists for, two pieces properly
  crossing, is excluded by the hypothesis. The file names it correctly as
  "the true precondition". The quantifier moves up one level; it is not
  discharged.
* **Overlay / DE-9IM labelling** assigns each directed edge a location
  relative to the other operand. That is well defined only if the edge does
  not cross the other operand in its interior.
* **Face extraction, winding, dart orbits** need a rotation system at each
  vertex. If two curves cross with no vertex inserted, there is no cyclic
  order at the crossing and the walk is not the boundary of a 2-cell.

There is exactly one existence result of the right shape in the corpus:
`ArcIntersectIVT.chord_crosses_arc_circle_implies_circle_intersection` gives
`exists X, between P Q X /\ inCircle_R … X = 0`. It is consumed by six
modules. Its binary64 realisation, `ArcCircle_b64_compute.v`, says of itself:

> "This is a SUFFICIENT-condition filter: when it returns true, the chord
> crosses the arc's circumcircle; false does NOT imply non-crossing."

and its soundness bridge "rides on the deferred `b64_inCircle`
sign-exactness". So the one place the corpus reaches for the oracle it gets a
half decision procedure whose completeness is undischarged — and it decides
against the *circle*, not the arc, over ℝ, producing no point in the working
number type. For the segment lane, on which Hobby and overlay actually run,
there is no existence result at all.

### Why identity, not just existence

Priest 1991 §7 (doi:10.1109/ARITH.1991.145549, obtained 2026-09-05) already
solves one pair in floating point: given four single-precision points it
decides whether the segment meets the line at a unique point and, if so,
returns the *correctly rounded* intersection in the input precision. That is
a constructor, and its output is representable — unlike Fortune & Van Wyk
1996 (doi:10.1145/231731.231735), whose exact homogeneous integer point has a
bit-length that grows with the degree and composes badly.

Neither solves identity. Priest rounds each pair independently, so two
Euclidean-coincident crossings can land on two different floats.
Fortune & Van Wyk buy identity by comparing exact homogeneous points;
Hobby/snap-rounding buys it by forcing coincidence onto a lattice.

The corpus currently has no notion of vertex identity at all:

```coq
Definition Dart : Type := (Point * Point)%type.   (* theories/Dart.v:50 *)
```

`dart_eq_dec` exists and is genuinely decidable — but it decides equality of
*coordinate pairs*. Two coincident crossings rounded to different floats are
two different darts, and `dart_eq_dec` certifies that they differ. The
decidability is real; it answers the wrong question. There is likewise no
named coordinate envelope: no precision model, scale, lattice or chart
appears in `Overlay.v` or `CurveGeometry.v`.

## Decision

Make the constructor part of the specification, and give identity and the
coordinate envelope their own types.

Fix a **sheet** `S = (O; e₁, e₂)`, an oriented affine plane with an optional
lattice `Λ ⊂ S` (the snap grid). All coordinates are points of `S`. Changing
`S` or `Λ` is a different instance. A constructor runs on **one** sheet.

**Storage.** A finite set `H` of **hens** (identifiers); a bag `P` of points
of `S` with optional Z, M; bags `Θ` of azimuths and `Σ` of scalars; a finite
set `E` of **eggs**, each an interpolant `γ_e : [0,1] → S` of a named class
(chord, circular arc, clothoid, sinusoid, ellipse, Bézier, NURBS) determined
by indices into `P, Θ, Σ`, supporting `γ(t)`, `γ'(t)`, curvature where
defined, `split(t)` and `demote` when the law is a chord. Incidence is a
**chicken**: a triple `(h_src, h_dst, e)`, a directed use of egg `e` between
two hens; its twin reverses orientation. A hen incident to no chicken is
**vacant**. A hen owning a point is a vertex; a hen owning an egg is a curve
piece. There is no `Geometry` subclass in this structure.

**Predicates** are functions on hens and the eggs they use, not objects.
Their value is a sign or a matrix, never a new hen. Evaluation may use exact
integer polynomials, adaptive floating-point, or interval bounds; that is an
implementation choice below the statement.

**Constructors (cook)** are partial functions that allocate hens. The
primitive is the pairwise intersection oracle

```
𝓘(eᵢ, eⱼ) = (p*, tᵢ, tⱼ)   if γᵢ(tᵢ) = γⱼ(tⱼ) = p* ∈ S
          = ∅               if the images are disjoint in S
          = Decline         if no algorithm for this pair on this sheet
```

On success the cook inserts a point-hen `h*` for `p*` (interpolating Z, M if
present), replaces each crossed chicken by two via `split(t)`, and records
incidence of the new chickens on `h*`. Repeat until every pair of leftover
eggs is either disjoint or split at every mutual hit. The result is a graph
`G = (H', C')` whose edges meet only at hens: `G` is noded on `S`.

Priest §7 is `𝓘` for a line and a segment in floating point. Fortune & Van
Wyk is `𝓘` returning a homogeneous integer point of bounded bit-length.

**Empty is not decline.** `∅` after a completed cook is the empty point-set:
dimension −1, identity for union, zero for intersection. `Decline` means `𝓘`
was undefined for this pair, or the inputs do not lie on one sheet. It is not
an empty geometry and not a value in SQL/MM.

**Snap-rounding is a different constructor**: a map `S → Λ` on the hens of
`G`, with a proof that the image stays noded (Hobby 4.1) *under the
hypothesis that `G` was already noded*. It does not replace `𝓘`.
OverlayNGRobust is a sequence of such maps attempted until `G` validates or
the process throws.

**Display is a view**: a function from leftover hens to a wire format (WKT,
WKB, SFA class names, SQL/MM tags). `POINT EMPTY` is a tag the view chooses
for a vacant result whose caller expected a point. The kernel does not store
it.

## What a proof may then claim

On one fixed sheet `S`, with a defined `𝓘` for every egg pair that occurs:

* predicates on `G` refer to the same crossings the constructors inserted;
* `intersects` and `intersection` cannot diverge except by a view rounding
  `p*` into a narrower type;
* `Classical_Prop.classic` is unnecessary for the existence of `p*` — either
  `𝓘` returned it or the cook declined.

That last point is not decoration. Deciding whether a crossing exists is
currently reachable only through predicates whose binary64 realisations carry
`classic` through Flocq's Dedekind reals (measured: `b64_format_B2R`,
`b64_ulp_FLT_0`, and every corpus lemma routed through them). A cook that
either produces `p*` or declines needs no excluded middle to assert the
crossing, because it never asserts one it did not construct.

## Consequences

**What this costs.** Two new types (`hen`, `sheet`) and a discipline that
nothing else mints hens. Every module that reads coordinates out of a dart
needs an egg alongside the hen — `DartAngularOrder.ddir` is the clearest
case, since the rotation system is defined by `γ'`.

**What it does not cost.** The orbit, face and `next` proofs consume
`dart_eq_dec` purely as *a* decidable equality and never inspect the
coordinates inside a dart (`DartFace.v`, `DartNextInjective.v`,
`DartNextRemove.v`). Re-seating `Dart` on a hen identifier leaves those
proofs standing. The move is local, not total.

**What it forbids.** A theorem that assumes `G` is already noded, without
naming which `𝓘` produced it, is a theorem about a different object than the
input the library accepted. `fully_intersected` as a silent premise *is* the
statement that the cook has already run. Under this ADR such a hypothesis
must be visible in the type, in the same way
`fast_expansion_sum_strong_nonoverlap_headline` was made an explicit
hypothesis of `Orient_b64_expansion.v` rather than left propping the chain up
from underneath.

**What remains open.** Identity. Priest does the first half of one pair —
decide, and round correctly. The second half, whether two constructed points
are the same vertex, is not solved by rounding each independently. Under this
ADR the answer is structural rather than numeric: the cook mints hens, so two
coincident crossings get one hen or two by the cook's decision, and that
decision is a fact the arrangement records rather than an accident of the
rounding. Which `𝓘` makes that decision, and on what basis, is not settled
here.

## References

- Priest (1991), *Algorithms for Arbitrary Precision Floating Point
  Arithmetic*, Proc. 10th Symposium on Computer Arithmetic 132–143,
  doi:10.1109/ARITH.1991.145549. §2 faithfulness; §7 the line/segment
  constructor.
- Fortune & Van Wyk (1996), *Static Analysis Yields Efficient Exact Integer
  Arithmetic for Computational Geometry*, ACM TOG 15(3):223–248,
  doi:10.1145/231731.231735. The predicate/constructor split.
- Hobby (1999), *Practical Segment Intersection with Finite Precision
  Output*, Comp. Geom. 13:199–214, doi:10.1016/S0925-7721(99)00021-8.
  Theorem 4.1, under a noded hypothesis.
- Bertolazzi, Bevilacqua & Frego (2020), *Efficient intersection between
  splines of clothoids*, Mathematics and Computers in Simulation
  176:57–72, doi:10.1016/j.matcom.2019.10.001. `I` for the clothoid
  class: tangent triangles, an AABB tree to cull pairs, then a
  curve-level check. It carries the existence-and-uniqueness statement
  the class needs — “if all the conditions (i), (ii) and (iii) are true,
  then the two clothoid arcs C1 and C2 have exactly one and only one
  intersection, which lies in T1 ∩ T2” — the clothoid analogue of
  `chord_hit`. Cited nowhere in the corpus today: it has only the
  papers that BUILD a clothoid (Bertolazzi & Frego 2015,
  doi:10.1002/mma.3114, the G1 fit and the Fresnel expansions), none
  that intersect two of them. A numerical constructor, hence a
  realisation and not a kernel statement.
- `theories-flocq/NodingSeparation_b64.v` — `pairwise_nodable`.
- `theories/Dart.v:50`, `theories/DartNextSpec.v` — the current dart and its
  decidable equality.
- `theories-flocq/ArcCircle_b64_compute.v` — the one-sided filter.

---

## Supporting shapes (addendum, 2026-09-07)

Host-lane vocabulary and ticket-named QED ∨ QEX stops for Joost's
conditional acceptance. Not a noder. Not a `Geometry` subclass. Not a
remint of `CurveSegment` / Exact* zoo types / `Dart` / Hobby.
QEX is not acceptance of a missing constructor. **Status is Accepted** (Joost, BDFL, 2026-09-07).

Modules: `theories/SheetHenCook.v` (sheet / hen / egg / chicken / `𝓘` /
first-cook scope) and `theories/Adr0007NodingEpic.v` (ticket stops).
Registered in `_CoqProject` (host / pure-R / Stdlib lane).

**ADR-0006 coupling.** Testable `𝓘` / cook results sit on the accepted
Oracle line protocol (`docs/adr/ADR-0006-oracle-protocol-is-the-test-surface.md`).
This cut mints no keyword and no second external seam (no FFI pin, no
RocqRefRunner dispatch). The IEEE↔R bridge letter attaches as adapters
on existing keywords (`INTERSECT_FILTERED` / `INTERSECT_POINT_XY` /
`OVERLAY_UNIFIED` / `ORIENT`) — still no new keyword, never FFI or
RocqRefRunner (ADR-0006 Decision 1–2). ADR-0006's Related subsection
points back here. Oracle + IEEE↔R bridge is the test surface for
NodingNG / OverlayNG / RelateNG. Both sides of the cross-link are the
coupling. Status of ADR-0006 stays Accepted.

### Glossary (Accepted law)

The Decision above is the vocabulary. One sheet `S`; hens are minted
identifiers; eggs are interpolants of a named class; chickens are
directed uses of an egg between two hens; cook / `𝓘` returns Hit
`(p*, tᵢ, tⱼ)`, Empty (disjoint images), or Decline (no algorithm).
Empty ≠ Decline. Snap-rounding ≠ `𝓘`. Display is a view. First cook
scope is chord–chord. Identity is structural (`ShareOne` / `MintTwo`).
QEX is not Accept of a missing constructor.

Campaign I / II / Phase B letters below keep every ticket row that
cites a theorem. Prose cites **Parks** once for the three landed
named QEX stops instead of restaging CircGamma / interior-mixed /
bag-loop theater in each paragraph.

### Parks (named QEX, landed)

Three honest stops. Named gaps, not bools. Later letters point here.

| Park | Landed | Ticket | Named gap |
|------|--------|--------|-----------|
| **Γ CircGamma** | #706 @ `da5593a` | `CircularCook.v : ticket_64_circ_gamma_qed_or_qex` | Egg has no `MkCirc` (`CircularCook.v : circ_gamma_mkcirc_missing`); chord-project nlerp misses the reflex principal span (`CircularCook.v : reflex_nlerp_misses_principal`). Sidecar `arc_gamma` is not host Γ. Discharge would need atan2 / Classic or a first-cook expand. |
| **ι interior circular×chord** | #707 @ `1dbc2c2` (joint gate); discharge `SidecarCircInteriorHit.v` | `SidecarCircInterior.v : ticket_0007_iota_gap_qed_or_qex` | `I_ok_mixed` Hit stays gated by `mixed_joint_params`; the interior-params arm does not inhabit that predicate (`SidecarCircInterior.v : interior_mixed_hit_arm_missing`). Sidecar `I_ok_interior` inhabits a locked proper-cross Hit under `interior_span_params` (`SidecarCircInteriorHit.v : locked_interior_I_ok_interior`). Do not drop the joint gate. ι is not μ, not host `I_ok`, not Γ. |
| **ρ bag-loop** | #708 @ `e9d89d6` | `Adr0007NodingEpic.v : ticket_0007_cook_term_qed_or_qex` | `CookLoopBagTerm` missing (`SheetHenCookLoop.v : cook_loop_bag_term_missing`); leftover_quad width conserved (`SheetHenCookLoop.v : leftover_quad_width_conserved`). Pairwise leftover-width + I.8 one-step confluence stay sibling QED. ρ leftover_quad ≠ η Multi bags. |

Do not remint CircGamma, `I_ok_mixed`, or `LoopDischarged`. Do not start
H⊥ / Multi Landed / Phase B done-when / MerkatorBV / `522-n`.

### Acceptance checklist (four prior review conditions)

| # | Condition | Stop | Arm | Lemma |
|---|-----------|------|-----|-------|
| 1 | Identity policy sketch (structural hen minting) | `Adr0007NodingEpic.v : ticket_0007_identity_qed_or_qex` | **QED** — `ShareOne` yields one hen | `SheetHenCook.v : share_one_same_hen` |
| 1b | Numeric `dart_eq_dec` does not decide vertex identity | `Adr0007NodingEpic.v : ticket_0007_dart_eq_qed_or_qex` | **QEX** — coord-pair `=` is not hen `=` | `SheetHenCook.v : coord_eq_not_hen_eq` |
| 2 | Minimal `𝓘` obligations for the segment/chord lane | `Adr0007NodingEpic.v : ticket_0007_chord_chord_qed_or_qex` | **QED** — Hit on unit-square diagonals; Empty on disjoint horizontals; never Decline in scope | `SheetHenCook.v : crossing_witness`, `SheetHenCook.v : disjoint_witness`, `SheetHenCook.v : I_ok_chord_not_decline` |
| 3 | Cross-link to accepted ADR-0006 | header of both modules + this addendum | comment / docs (no second seam) | — |
| 4 | First cook scope = chord–chord only | `Adr0007NodingEpic.v : ticket_0007_qed_or_qex` | **QEX** — clothoid–clothoid missing (508 mirror) | `SheetHenCook.v : clothoid_clothoid_not_first_scope` |
| 4b | Chord–chord inhabits the cook interface | `Adr0007NodingEpic.v : ticket_0007_chord_chord_qed_or_qex` | **QED** | `SheetHenCook.v : first_cook_scope_chord_chord` |
| — | Empty ≠ Decline | `Adr0007NodingEpic.v : ticket_0007_empty_neq_decline_qed_or_qex` | **QED** | `SheetHenCook.v : IEmpty_neq_IDecline` |
| — | “Noded on S” is cook evidence | `Adr0007NodingEpic.v : ticket_0007_noded_cook_qed_or_qex` | **QED** | `SheetHenCook.v : noded_crossing` |
| — | Silent `pairwise_nodable` / `fully_intersected` does not discharge the constructor | `Adr0007NodingEpic.v : ticket_0007_silent_nodable_qed_or_qex` | **QEX** — a proper crossing is the noder's job and is excluded by the shadow | `SheetHenCook.v : crossing_not_nodable_shadow` |
| — | Pairwise interior split + one-step confluence | `Adr0007NodingEpic.v : ticket_0007_pairwise_split_qed_or_qex` | **QED** — leftover-width decrease; leftover bag independent of parent order | `SheetHenCook.v : interior_split_finite_holds`, `SheetHenCook.v : split_step_confluent` |
| — | Bag-level cook loop (term / confl on a leftover bag) | `Adr0007NodingEpic.v : ticket_0007_cook_term_qed_or_qex` | **QEX** — named 508-style gap: `CookLoopBagTerm` missing; leftover_quad width conserved; kiss / share / mint not covered. CRV-TOUCH / `𝓘`-family; not a soft gap | `SheetHenCookLoop.v : cook_loop_bag_term_missing`, `SheetHenCookLoop.v : leftover_quad_width_conserved` |
| — | binary64 / OverlayNGRobust sit on one sheet | `Adr0007NodingEpic.v : ticket_0007_sheet_realiz_qed_or_qex` | **QED** — realization preserves `S`; OverlayNGRobust is a finite snap-sequence, not `𝓘` | `SheetHenCook.v : coord_realization_preserves_sheet`, `SheetHenCook.v : overlay_ng_robust_is_finite_snap_holds`, `SheetHenCook.v : overlay_ng_robust_is_snap_not_I` |
| — | `ddir` migration is one type equation | `Adr0007NodingEpic.v : ticket_0007_chicken_dart_qed_or_qex` | **QED** — `DdirDart` := `(Hen * Hen)` = chicken ends; CoordDart stays the `Dart.v` coordinate-pair story; no third type | `SheetHenCook.v : ddir_migration_one_equation` |
| — | Full-circle Hit carries constructed `(h*, p*, tᵢ, tⱼ)` | `CircularCookHit.v : ticket_64_circ_hit_params_qed_or_qex` | **QED** — locked `(0,0)/(7,0)` r=5; `γ(t)=p*` | `CircularCookHit.v : locked_I_circles_gamma_hit`, `CircularCookHit.v : locked_hit_plus_on_gamma` |
| — | CircularArc γ / CircGamma | `CircularCook.v : ticket_64_circ_gamma_qed_or_qex` | **QEX** — named gap: no `MkCirc` on Egg; nlerp misses reflex principal span; Discharge needs atan2/Classic or first-cook expand; do not fake Discharge | `CircularCook.v : circ_gamma_mkcirc_missing`, `CircularCook.v : reflex_nlerp_misses_principal`, `CircularCook.v : circular_gamma_is_qex` |
| — | Span-restricted γ on CircularArc | `CircularCookSpan.v : circular_arc_gamma_constructed` | **QED** — principal-span interpolant; locked proper arcs keep `p+`, reject `p−` | `CircularCookSpan.v : locked_span_gamma_hit`, `CircularCookSpan.v : arc_gamma_retract` |
| — | Host circular IHit → `try_cook_hit` | `Adr0007NodingEpic.v : ticket_0007_circ_host_cook_qed_or_qex` | **QEX** — circular eggs stay `MkOutOfScope`; host cook declines even on IHit | `SheetHenCook.v : try_cook_hit_circular_hit_none`, `SheetHenCook.v : circular_egg_not_first_cook_scope` |
| — | Circular Hit feeds sidecar `split(t)` | `CircularCookSplit.v : ticket_0007_circ_cook_step_qed_or_qex` | **QED** — locked plus-root leftovers meet at `p+`; CircGamma stays QEX | `CircularCookSplit.v : cooked_circ_plus_try`, `CircularCookSplit.v : cooked_circ_plus_ok` |
| — | Circular Touch / Empty / Decline cook | `CircularCookSplit.v : ticket_0007_circ_cook_scope_qed_or_qex` | **QEX** — kiss is a fenced scope arm, not a CRV-TOUCH procedure | `CircularCookSplit.v : locked_circ_touch_none` |
| — | I.7 MintTwo / `p−` is a second Hit | `CircularCookSplit.v : ticket_0007_circ_mint_two_qed_or_qex` | **QED** — allocation across both radical roots is `MintTwo`; leftovers meet at `p−` | `CircularCookSplit.v : cooked_circ_mint_two_try`, `CircularCookSplit.v : cooked_circ_minus_ok` |
| — | I.7 leftover shared endpoint ≠ kiss | `CircularCookSplit.v : ticket_0007_circ_shared_neq_kiss_qed_or_qex` | **QED** — leftover join is Hit incidence, not Touch | `CircularCookSplit.v : leftover_shared_endpoint_not_touch` |
| — | I.7 MintTwo Empty / Decline / Touch | `CircularCookSplit.v : ticket_0007_circ_mint_two_scope_qed_or_qex` | **QEX** — still allocate no hen | `CircularCookSplit.v : locked_circ_mint_two_touch_none` |
| — | I.1 four-object fence | `CircularCookSplit.v : ticket_0007_i1_fence_qed_or_qex` | **QED** — locked observations; not a type synonym | `CircularCookSplit.v : i1_z_neq_gamma_obs`, `CircularCookSplit.v : i1_sidecar_neq_gloss_obs` |
| — | I.1 Touch ≠ IHit | `CircularCookSplit.v : ticket_0007_touch_neq_ihit_qed_or_qex` | **QED** — kiss Touch ≠ proper-cross Hit on Z and γ | `CircularCookZ.v : IZTouch_neq_IZHit`, `CircularCookHit.v : ICircGTouch_neq_ICircGHit` |
| — | I.1 circular Empty ≠ Decline | `CircularCookSplit.v : ticket_0007_empty_neq_decline_circ_qed_or_qex` | **QED** — locked Empty / Decline fixtures differ | `CircularCookZ.v : IZEmpty_neq_IZDecline`, `CircularCookHit.v : ICircGEmpty_neq_ICircGDecline` |
| — | I.1 chord × circular Decline | `Adr0007NodingEpic.v : ticket_0007_chord_circ_decline_qed_or_qex` | **QED** — mixed pair inhabits `I_ok` as Decline, not a constructed Hit | `SheetHenCook.v : chord_circular_decline_I_ok`, `SheetHenCook.v : chord_circular_hit_not_I_ok` |
| — | I.1 I_gloss / host CircGamma | `CircularCook.v : ticket_0007_i1_gloss_qed_or_qex` | **QEX** — `I_gloss` undefined; `MkCirc` missing; host circular `I_ok` is Decline only | `CircularCook.v : circ_gamma_mkcirc_missing`, `CircularCook.v : circular_gamma_is_qex`, `SheetHenCook.v : circular_decline_I_ok` |
| — | I.2 ∀ Hit soundness | `CircularCookHit.v : ticket_0007_i2_hit_sound_qed_or_qex` | **QED** — `I_circles_gamma` = Hit iff proper disc ∧ `on_full_circle` on both roots; R3 locked witness recovered | `CircularCookHit.v : I_circles_gamma_hit_iff`, `CircularCookHit.v : i2_recovers_locked_r3` |
| — | I.2 not arc membership | `CircularCookHit.v : ticket_0007_i2_arc_scope_qed_or_qex` | **QEX** — γ_full only; CircGamma stays QEX; first cook stays chord–chord | `CircularCook.v : circular_gamma_is_qex`, `CircularCook.v : circular_not_first_cook_scope` |
| — | I.3 ∀ Empty | `CircularCookEmpty.v : ticket_0007_i3_empty_qed_or_qex` | **QED** — `I_circles_gamma` = Empty iff proper pair ∧ γ_full images disjoint on S | `CircularCookEmpty.v : I_circles_gamma_empty_iff`, `CircularCookEmpty.v : i3_recovers_locked_empty` |
| — | I.3 ∀ Decline | `CircularCookEmpty.v : ticket_0007_i3_decline_qed_or_qex` | **QED** — Decline iff not a proper pair (`d=0` or `r≤0`) | `CircularCookEmpty.v : I_circles_gamma_decline_iff` |
| — | I.3 discriminant ≠ image-disjoint | `CircularCookEmpty.v : ticket_0007_i3_disc_neq_image_qed_or_qex` | **QED** — concentric unequal radii are image-disjoint and Decline, not Empty | `CircularCookEmpty.v : concentric_unequal_images_disjoint` |
| — | I.3 not arc membership | `CircularCookEmpty.v : ticket_0007_i3_scope_qed_or_qex` | **QEX** — γ_full only; CircGamma stays QEX; sidecar cook stays locked | `CircularCook.v : circular_gamma_is_qex`, `CircularCook.v : circular_not_first_cook_scope` |
| — | I.8 leftover confluence | `CircularCookConfluence.v : ticket_0007_i8_confluent_qed_or_qex` | **QED** — `leftovers_ab` = `leftovers_ba` on γ_full; circular analogue of `split_step_confluent` | `CircularCookConfluence.v : circ_split_step_confluent` |
| — | I.8 cook bag inhabits leftovers | `CircularCookConfluence.v : ticket_0007_i8_cook_qed_or_qex` | **QED** — `cook_circ_root` leftovers are that bag; locked plus/minus recovered | `CircularCookConfluence.v : cook_circ_root_is_leftovers_ab`, `CircularCookConfluence.v : i8_recovers_locked_plus` |
| — | I.8 one-step ≠ bag loop | `CircularCookConfluence.v : ticket_0007_i8_neq_bag_qed_or_qex` | **QED** — confluence is one Hit-split; `cook_loop` stays obligation | `CircularCookConfluence.v : i8_one_step_not_bag_loop`, `SheetHenCook.v : cook_loop_is_obligation` |
| — | I.8 not arc / not bag discharge | `CircularCookConfluence.v : ticket_0007_i8_scope_qed_or_qex` | **QEX** — γ_full only; CircGamma stays QEX; bag loop stays QEX | `CircularCook.v : circular_gamma_is_qex`, `SheetHenCook.v : cook_loop_is_obligation` |
| — | I.9 classifier hens are tags | `CircularCookLicense.v : ticket_0007_i9_tags_qed_or_qex` | **QED** — hens 0/1; ∀ IZHit is those tags; `I_CIRCULAR` HIT 0 1 | `CircularCookZ.v : classifier_hens_are_tags`, `CircularCookZ.v : iz_hit_only_tags` |
| — | I.9 Z Hit ⇏ host cook | `CircularCookLicense.v : ticket_0007_i9_not_host_cook_qed_or_qex` | **QED** — I_circles_z Hit does not feed `try_cook_hit` and does not expand first cook scope | `CircularCookLicense.v : i9_z_hit_not_try_cook_hit`, `CircularCookLicense.v : i9_z_hit_not_first_cook_scope` |
| — | I.9 Z Hit ⇏ circ_split | `CircularCookLicense.v : ticket_0007_i9_not_circ_split_qed_or_qex` | **QED** — same tags; plus/minus leftovers meet at distinct `p*`; t comes from γ | `CircularCookLicense.v : i9_z_hit_not_circ_split_license` |
| — | I.9 not CircGamma / not scope expand | `CircularCookLicense.v : ticket_0007_i9_scope_qed_or_qex` | **QEX** — CircGamma stays QEX; first cook stays chord–chord | `CircularCook.v : circular_gamma_is_qex`, `CircularCook.v : circular_not_first_cook_scope` |
| — | II.1 span filter as IResult | `CircularCookSpanFilter.v : ticket_0007_ii1_hit_qed_or_qex` | **QED** — arc Hit iff `on_arc_gamma` both; locked `p+` in-span, `p−` out | `CircularCookSpanFilter.v : I_span_root_hit_iff`, `CircularCookSpanFilter.v : ii1_locked_plus_span_hit` |
| — | II.2 split γ_span at in-span t | `CircularCookSpanSplit.v : ticket_0007_ii2_meet_qed_or_qex` | **QED** — leftovers of `arc_gamma` meet at locked `p+`; leftover on parent circle; `p−` stays Empty | `CircularCookSpanSplit.v : cooked_span_plus_meets`, `CircularCookSpanSplit.v : cooked_span_plus_on_parent` |
| — | II.3 I_ok_circ on circular eggs | `CircularCookOkCirc.v : ticket_0007_ii3_hit_qed_or_qex` | **QED** — first glossary-type inhabitant; locked `p+` Hit licenses `span_split` | `CircularCookOkCirc.v : I_ok_circ_hit_iff`, `CircularCookOkCirc.v : ii3_locked_plus_licenses_cook` |
| — | II.4 Campaign-II close / Phase B gaps | `CircularCookCloseII.v : ticket_0007_ii4_inhabitant_qed_or_qex` | **QED** — sidecar `I_ok_circ` inhabitant; leftover meet is ¬Empty | `CircularCookCloseII.v : ii4_sidecar_inhabitant`, `CircularCookCloseII.v : ii4_leftover_meet_not_empty` |
| — | Phase B.1 CircularString concat joints | `CircularCookCsConcat.v : ticket_0007_b1_joint_qed_or_qex` | **QED** — ∀ CS joint is `I_ok_circ` Hit at `(end, 1, 0)`; reuse, no new kernel | `CircularCookCsConcat.v : cs_joint_I_ok_circ`, `CircularCookCsConcat.v : locked_cs_contiguous` |
| — | Phase B mixed LS–CS joints | `SidecarCircMixed.v : ticket_0007_b_mixed_hit_qed_or_qex` | **QED** — ∀ LS–CS / CS–LS joint is `I_ok_mixed` Hit at `(end, 1, 0)` | `SidecarCircMixed.v : ls_cs_joint_I_ok_mixed`, `SidecarCircMixed.v : cs_ls_joint_I_ok_mixed` |
| — | Phase B.2 CompoundCurve member joints | `CircularCookCcConcat.v : ticket_0007_b2_mixed_qed_or_qex` | **QED** — locked mixed LS+CS CC contiguous; mixed joint is `I_ok_mixed` Hit; host `I_ok` stays Decline | `CircularCookCcConcat.v : locked_cc_mixed_contiguous`, `CircularCookCcConcat.v : locked_cc_mixed_I_ok_mixed` |
| — | Phase B.3 CurvePolygon ring closure | `CircularCookCpConcat.v : ticket_0007_b3_closed_qed_or_qex` | **QED** — locked CS / mixed rings closed + contiguous; CS closing `I_ok_circ`; mixed closing `I_ok_mixed` | `CircularCookCpConcat.v : locked_cp_cs_ring_closed`, `CircularCookCpConcat.v : locked_cp_mixed_closing_I_ok_mixed` |
| — | Phase B MultiCurve / MultiSurface bags | `SidecarCircBags.v : ticket_0007_b_bags_inhabit_qed_or_qex` | **QED** — MultiCurve / MultiSurface inhabit as bags of already-Qed CS / CC / CP members; bag ≠ concat | `SidecarCircBags.v : locked_mc_typed_ok`, `SidecarCircBags.v : locked_ms_ok`, `SidecarCircBags.v : bags_not_concat` |
| — | Phase B ι interior circular×chord | `SidecarCircInterior.v : ticket_0007_iota_gap_qed_or_qex` | **QEX** — `I_ok_mixed` Hit is joint-only; interior-params arm missing; do not remint `I_ok_mixed` / CircGamma / host `I_ok` | `SidecarCircInterior.v : interior_mixed_hit_arm_missing`, `SidecarCircInterior.v : I_ok_mixed_interior_hit_false` |
| — | ι interior Hit discharge | `SidecarCircInteriorHit.v : ticket_0007_iota_interior_hit_qed_or_qex` | **QED** — distinct `I_ok_interior` Hit on locked LS×CS / CS×LS; packages `I_ok_mixed_interior_arm`; joint gate stands | `SidecarCircInteriorHit.v : locked_interior_I_ok_interior`, `SidecarCircInteriorHit.v : locked_interior_rev_I_ok_interior` |

Snap-rounding is a different constructor (`SheetHenCook.v : snap_round_neq_I`).
Display is a view (`DisplayView`), not a kernel store.

### Dart := hen-id pair (chicken view) — closed

A later remint reseats `Dart` as a hen-id pair `(h_src, h_dst)` — one
view of a chicken, not a third type. The host-lane equation is
`DdirDart = (Hen * Hen)` (`SheetHenCook.v : ddir_dart_eq_hen_pair`)
with `hen_id_dart_of_chicken c = (ck_src c, ck_dst c)`
(`SheetHenCook.v : hen_id_dart_of_chicken_eq`).
`DartAngularOrder.ddir` then reads `γ'` from the chicken's egg
(`SheetHenCook.v : ddir_reads_chicken_egg`). Orbit / `next` / face
proofs consume `dart_eq_dec` as *a* decidable equality and never
inspect coordinates (`DartFace.v`, `DartNextInjective.v`,
`DartNextRemove.v`); they do not remint. Local `HenIdDart` /
`DdirDart` is that view; it is not a remint of the `Dart.v` coordinate-pair definition.
`CoordDart` stays the current coordinate-pair story
(`SheetHenCook.v : ddir_role_neq_coord_role`). Reviewers of `ddir`
should not invent a third directed-edge type.

### binary64 and OverlayNGRobust sit on a sheet — closed

Points of `S` are affine. The working number type — ℝ in the host lane,
binary64 / Flocq in `theories-flocq/` — is a *coordinate realization* of
those points (`SheetHenCook.v : CoordRealization`,
`SheetHenCook.v : coord_realization_preserves_sheet`,
`SheetHenCook.v : binary64_same_sheet_as_R`). Changing the
number type does not change the sheet origin or basis. A binary64 noder
is `𝓘` realized in that number type on one sheet; it is not a second
sheet and is not discharged here.

OverlayNGRobust is a finite sequence of snap maps `S → Λ` attempted
until noded `G` validates or the process throws. Each attempt is
Hobby-shaped: it assumes `G` was already noded. It is not `𝓘`
(`SheetHenCook.v : overlay_ng_robust_is_finite_snap_holds`,
`SheetHenCook.v : overlay_ng_robust_is_snap_not_I`). Failure to
validate is not `𝓘` Decline and not Empty.

WITNESS topic: overlay · claimId: 0007 · witness: 0007-qed-qex · board: ADR-0007

---

## Accepted (2026-09-07)

**Decision:** Accepted by Joost (BDFL). Vocabulary law for CRV-TOUCH / RGR. Soft gaps (a)(b)(c) closed as checklist rows. Parks Γ / ι / ρ are landed named QEX. Honest remaining opens (FP noder, Hobby, kiss) stay open and do not reopen Status.

## Ready for BDFL (historical, 2026-09-07)

**Accepted** 2026-09-07. This section is retained as the Accept memo archive.
QEX is not acceptance. Supporting shapes are not a noder.

**Joost brief (soft gaps, 2026-09-07).** Former soft gaps (a)(b)(c) are
closed checklist rows: pairwise chord-split finiteness plus one-step
confluence is QED; binary64 / OverlayNGRobust sit on one sheet is QED;
`DdirDart` := `(Hen * Hen)` = chicken ends is QED. The bag-level cook
loop is Parks ρ (named 508-style QEX), not a soft gap. **Accepted**
by Joost (BDFL) 2026-09-07.

### Four prior review conditions — discharged

| # | Condition | Stop | Arm |
|---|-----------|------|-----|
| 1 | Identity policy sketch (structural hen minting) | `ticket_0007_identity_qed_or_qex` | **QED** — `ShareOne` |
| 1b | Numeric `dart_eq_dec` is not vertex identity | `ticket_0007_dart_eq_qed_or_qex` | **QEX** |
| 2 | Minimal chord–chord `𝓘` | `ticket_0007_chord_chord_qed_or_qex` | **QED** — Hit / Empty / never Decline in scope |
| 3 | Cross-link accepted ADR-0006 | module headers + coupling paragraph | Oracle line protocol only; later keyword = adapter, not FFI / RocqRefRunner |
| 4 | First cook scope = chord–chord only | `ticket_0007_qed_or_qex` | **QEX** on clothoid–clothoid |

### Soft gaps closed

Former named soft gaps (a)(b)(c) are checklist rows, not open naming.
**Accepted** 2026-09-07. QEX is not Accept of a missing constructor.

| Former | Stop | Arm | Settled as |
|--------|------|-----|------------|
| (a) Cook termination / confluence on the chord lane | `ticket_0007_pairwise_split_qed_or_qex` | **QED** — pairwise leftover-width split is finite; one Hit-split is confluent | Host-lane close. The bag loop is Parks ρ (`ticket_0007_cook_term_qed_or_qex` **QEX**) — not a soft gap |
| (b) How binary64 / OverlayNGRobust sit on a sheet | `ticket_0007_sheet_realiz_qed_or_qex` | **QED** — realization preserves `S`; OverlayNGRobust is a finite snap-sequence, not `𝓘` | Host-lane close. A binary64 noder, including sheet vs kiss, stays Honest remaining / CRV-TOUCH |
| (c) Chicken vs Dart so `ddir` reviewers do not invent three types | `ticket_0007_chicken_dart_qed_or_qex` | **QED** — `DdirDart` := `(Hen * Hen)` = chicken ends; CoordDart ≠ that role | Host-lane close. Reminting the `Dart.v` coordinate-pair definition is a later letter, not a third type |
| (d) This memo | this section | brief only | Soft gaps closed; **Accepted** 2026-09-07 |

### CRV-TOUCH / RGR (vocabulary law, not kiss)

NTS RGR Board: [board](https://app.notion.com/p/b494beb4c5d04a08886e1169be9b6cb1).
Card Touch for noding (`CRV-TOUCH`, Lane red):
[card](https://app.notion.com/p/3be1c9833b0681f8a944ce851d463236).
Wayfinder: [CRV-TOUCH · wayfinder map](https://app.notion.com/p/3d41c9833b068143b870c30feba956c3).
RGR is the JTS fork branch `feature/sfa-curve-rgr` (fork PR 7).
`CurveSegmentNoder` lives on the Bar 2 stack off that branch, not here.

CRV-TOUCH **assumes** this ADR's vocabulary (sheet, hen, egg, chicken,
cook, `𝓘`, Empty ≠ Decline, view). Accepting this ADR is **out of
scope** of that map. Tickets may record a proposed amendment; they do
not edit this file. Jeroen is Architect on every CRV-TOUCH ticket.
Joost appears only as a note where a ticket proposes an amendment.

Accept as vocabulary law does **not** settle kiss / tangency.

- **Kiss** is external / internal circle tangency and arc–line
  tangency (discriminant zero). Two eggs sharing an endpoint is
  **not** a kiss; the cook already handles that case.
- Three tangency decision procedures stay live on CRV-TOUCH: exact
  rational discriminant, identity by construction, ulp-floored
  window. This ADR does not pick one.
- The kiss spec is written on ℝ² (MerkatorBV `ChordCook.v`; this
  clone's host-lane ℝ² vocabulary is `SheetHenCook.v`). What a
  binary64 sheet owes the kiss is a CRV-TOUCH grilling ticket, not
  a second sheet here.
- Arc cook termination is out of scope here. It belongs to the
  Curve noding / General circular noding sisters, not this Accept.
- An ADR-0006 cook-mode keyword that reports a kiss hen (beyond
  `DISC_OVERLAY` EXT_TANGENT / INT_TANGENT and `ARC_SEGMENT_XY`
  count-1) is a CRV-TOUCH ticket after a prototype. This ADR mints
  no keyword.

### Honest remaining opens (Accept does not close these)

- Identity policy detail beyond `ShareOne` / `MintTwo` (which `𝓘` decides, on what basis). Kiss certificate is the CRV-TOUCH form of this question, not a silent extra hen type.
- A binary64 / floating-point noder (`𝓘` realized in Flocq), including binary64 sheet vs kiss. Not a second sheet. Host-lane “sits on a sheet” is closed above.
- Hobby 4.1 / 4.3. Snap-rounding stays a different constructor under already-noded `G`.
- Parks Γ / ι / ρ — landed named QEX (see Parks). Pairwise leftover-width and I.8 one-step confluence stay sibling QED. **Arc** cook termination is a sister card, not this Accept.
- Later constructive rungs: one Hit `split(t)` step is `ticket_0007_cook_step_qed_or_qex` / `ticket_0007_cook_step_scope_qed_or_qex`; constructed `𝓘` from proper-cross signs is `ticket_0007_constructed_I_qed_or_qex` / `ticket_0007_constructed_I_scope_qed_or_qex` / `ticket_0007_share_constructed_qed_or_qex`. Letters after Accept, not Accept blockers.
- ADR-0006 cook-mode for a kiss hen — CRV-TOUCH, after a prototype.

### Decision requested

**Accept** ADR-0007 as the **vocabulary law** CRV-TOUCH already
assumes: sheet / hen / egg / chicken / cook / `𝓘`, first cook scope
chord–chord, Empty ≠ Decline, identity structural, host lane on ℝ²,
testable results on the ADR-0006 Oracle line protocol (no new
cook-mode keyword in this cut).

Accept does **not** settle kiss / tangency, does **not** pick among
the three tangency decision procedures, and does **not** discharge
binary64-sheet-vs-kiss, arc cook termination, or an ADR-0006
cook-mode. Those stay CRV-TOUCH tickets. CRV-TOUCH does not edit
this ADR.

**Reject** if the constructor-in-the-specification frame is wrong, if
first cook scope must be wider than chord–chord, or if identity must
be numeric rather than structural.

Do not flip the Status line except by this decision. Status stays
**Accepted** by Joost (BDFL) 2026-09-07.

---

## Integer circle–circle seam (2026-09-07)

`CircularCookZ.v : I_circles_z` classifies two integer circles
(Hit / Empty / Touch / Decline) and mints named-root hens; oracle
`I_CIRCULAR` takes integer tokens. Hit is the open squared interval;
internal kiss is Touch. Does not reopen Status.

Full-circle interpolant γ(t) = O + r·(cos 2πt, sin 2πt) and
Hit (h*, p*, tᵢ, tⱼ) live in `CircularCookHit.v`. Locked
`(0,0)/(7,0)` r=5 is QED (`ticket_64_circ_hit_params_qed_or_qex`).
Span-restricted γ on CircularArc is QED in the 4-axiom sidecar
(`CircularCookSpan.v : circular_arc_gamma_constructed`;
`CircularCookSpan.v : locked_span_gamma_hit`). Parks Γ — named
MkCirc + nlerp gap; sidecar `arc_gamma` is not host Γ.
The next letter feeds that circular Hit into a same-shape cook
(`CircularCookSplit.v`); host `try_cook_hit` still declines circular
eggs. Not first cook scope. Not a noder.

### Letter after Accept — one Hit cook step (2026-09-07)

The Decision's first constructive sentence after `𝓘`: on success the cook
inserts a point-hen and replaces each crossed chicken by two via
`split(t)`. That is this letter. It is not the bag-level
repeat-until-noded loop and does not reopen Status.

| Stop | Arm | Lemma |
|------|-----|-------|
| `Adr0007NodingEpic.v : ticket_0007_cook_step_qed_or_qex` | **QED** — crossing chickens share one minted hen after `split(t)` | `SheetHenCook.v : cooked_crossing_try`, `SheetHenCook.v : cooked_crossing_shares`, `SheetHenCook.v : chord_split_left_reparam` |
| `Adr0007NodingEpic.v : ticket_0007_cook_step_scope_qed_or_qex` | **QEX** — Decline / Empty / out-of-scope allocate no hen | `SheetHenCook.v : try_cook_hit_clothoid_none`, `SheetHenCook.v : try_cook_hit_empty_none` |

Witness: `0007-cook-split`. Status stays **Accepted**. Not a remint of leftover-width / pairwise_split. Parks Γ / ι / ρ. 

### Letter after Accept — constructed 𝓘 from proper-cross signs (2026-09-07)

The Decision's `𝓘` is not a hardcoded midpoint. Proper-cross sign
conditions license `Intersect.strict_intersection_point` as `p*` plus
the two open-interval parameters. That constructed Hit recovers the
unit-square witness and cooks. Missing signs do not license the
formula (they are not Decline). Equal constructed `p*` under operand
swap licenses `ShareOne` — the identity basis, not `dart_eq_dec`.
Not a remint of `Intersect`. Not a total `𝓘`. Not the noder loop.
Does not reopen Status.

| Stop | Arm | Lemma |
|------|-----|-------|
| `Adr0007NodingEpic.v : ticket_0007_constructed_I_qed_or_qex` | **QED** — signs on the unit-square diagonals produce the same Hit the cook already splits | `SheetHenCook.v : constructed_hit_I_ok`, `SheetHenCook.v : constructed_hit_crossing_eq`, `SheetHenCook.v : cooked_constructed_crossing` |
| `Adr0007NodingEpic.v : ticket_0007_constructed_I_scope_qed_or_qex` | **QEX** — disjoint horizontals have no proper-cross signs; Empty stays Empty | `SheetHenCook.v : disjoint_not_proper_cross`, `SheetHenCook.v : disjoint_I_ok` |
| `Adr0007NodingEpic.v : ticket_0007_share_constructed_qed_or_qex` | **QED** — operand swap names the same `p*`; `ShareOne` follows | `SheetHenCook.v : constructed_hit_sym_same_p`, `SheetHenCook.v : equal_constructed_p_share` |

Witness: `0007-constructed-I`. Status stays **Accepted**. Parks Γ / ι / ρ.

### Letter after Accept — circular Hit → cook bridge (2026-09-08)

#666 closed chord–chord constructed Hit → cook `split(t)`. The circular
side already had `I_circles_z` / `I_CIRCULAR`, constructed
`(h*, p*, tᵢ, tⱼ)` on locked discs, and principal-span γ. This letter
feeds that circular Hit into a same-shape cook step — leftovers via
`circ_gamma` `split(t)`, incidence on the Hit's hen — without faking
atan2-free host γ and without expanding first cook scope.

The *host* cook (`try_cook_hit`) still declines circular eggs: they
remain `MkOutOfScope`. Touch / kiss is a fenced
QEX arm, not a CRV-TOUCH kiss decision. Not a remint of
`ArcSplitAtNode`. Does not reopen Status.

| Stop | Arm | Lemma |
|------|-----|-------|
| `Adr0007NodingEpic.v : ticket_0007_circ_host_cook_qed_or_qex` | **QEX** — circular IHit does not feed host `try_cook_hit` | `SheetHenCook.v : try_cook_hit_circular_hit_none` |
| `CircularCookSplit.v : ticket_0007_circ_split_qed_or_qex` | **QED** — locked plus-root leftovers meet at `p+` | `CircularCookSplit.v : circ_split_join`, `CircularCookHit.v : locked_hit_plus_on_gamma` |
| `CircularCookSplit.v : ticket_0007_circ_cook_step_qed_or_qex` | **QED** — `I_circles_gamma` Hit cooks; CircGamma stays QEX | `CircularCookSplit.v : cooked_circ_plus_try`, `CircularCookSplit.v : cooked_circ_plus_ok` |
| `CircularCookSplit.v : ticket_0007_circ_cook_scope_qed_or_qex` | **QEX** — Touch / Empty / Decline allocate no hen | `CircularCookSplit.v : locked_circ_touch_none` |

Witness: `0007-circ-cook`. Status stays **Accepted**. Parks Γ / ι / ρ.

### Letter after Accept — I.7 MintTwo / p− (2026-09-08)

#686 cooked the plus-root. Both radical roots are Hits: `p−` is a
second Hit, not optional. Allocation across `p+` and `p−` is
`MintTwo` (`hen_plus`, `hen_minus`). Leftover pieces that share the
split endpoint are Hit incidence, not a kiss. Empty / Decline /
Touch still mint nothing (same QEX fence as #686). Does not pick
among the three CRV-TOUCH tangency procedures (exact-Q / identity /
ulp). Four fences: `I_circles_z` ≠ `I_circles_gamma` ≠ sidecar cook
≠ glossary `𝓘`. Not first cook scope.
Not a noder. Does not reopen Status.

| Stop | Arm | Lemma |
|------|-----|-------|
| `CircularCookSplit.v : ticket_0007_circ_minus_qed_or_qex` | **QED** — locked minus-root leftovers meet at `p−` | `CircularCookSplit.v : cooked_circ_minus_ok`, `CircularCookHit.v : locked_hit_minus_on_gamma` |
| `CircularCookSplit.v : ticket_0007_circ_mint_two_qed_or_qex` | **QED** — Hit allocates `MintTwo`; both roots cook; CircGamma stays QEX | `CircularCookSplit.v : cooked_circ_mint_two_try`, `CircularCookSplit.v : cooked_circ_mint_two_ok` |
| `CircularCookSplit.v : ticket_0007_circ_shared_neq_kiss_qed_or_qex` | **QED** — leftover shared endpoint is Hit incidence, not Touch | `CircularCookSplit.v : leftover_shared_endpoint_not_touch` |
| `CircularCookSplit.v : ticket_0007_circ_mint_two_scope_qed_or_qex` | **QEX** — Empty / Decline / Touch still allocate no hen | `CircularCookSplit.v : locked_circ_mint_two_touch_none` |

Witness: `0007-I.7-mint-two`. Status stays **Accepted**. Parks Γ / ι / ρ.

### Letter after Accept — I.1 Fence (2026-09-09)

#666's honesty fence was prose. This letter closes it as tickets, not
a type synonym. The four objects are pairwise unequal by observation
on the locked `(0,0)/(7,0)` r=5 witness:

1. `I_circles_z` / Oracle `I_CIRCULAR` — Z⁶ classifier; hens 0/1; no t.
2. `I_circles_gamma` — locked full-circle witness with t on γ_full.
3. Sidecar cook (`CircularCookSplit` after #686/#687) — leftovers / `MintTwo`.
4. `I_gloss` — host `I_ok` + CircGamma; undefined while CircGamma is QEX.

Touch ≠ IHit on the circular classifiers. Circular Empty ≠ Decline
(host `IEmpty` ≠ `IDecline` already stands). Chord × circular Decline
inhabits `I_ok` as the honest host arm — not a constructed mixed Hit.
Does not remint `CurveSegment` / Exact* / `Dart` / Hobby /
`ArcSplitAtNode` leftover-width. Does not start I.2–I.3 / I.8–I.10 /
Campaign II / H⊥ / a CRV-TOUCH kiss procedure. Does not reopen Status.

| Stop | Arm | Lemma |
|------|-----|-------|
| `CircularCookSplit.v : ticket_0007_i1_fence_qed_or_qex` | **QED** — six locked pairwise observations | `CircularCookSplit.v : i1_z_neq_gamma_obs`, `CircularCookSplit.v : i1_sidecar_neq_gloss_obs` |
| `CircularCookSplit.v : ticket_0007_touch_neq_ihit_qed_or_qex` | **QED** — kiss Touch ≠ proper-cross Hit | `CircularCookZ.v : IZTouch_neq_IZHit`, `CircularCookHit.v : ICircGTouch_neq_ICircGHit` |
| `CircularCookSplit.v : ticket_0007_empty_neq_decline_circ_qed_or_qex` | **QED** — circular Empty ≠ Decline | `CircularCookZ.v : IZEmpty_neq_IZDecline` |
| `Adr0007NodingEpic.v : ticket_0007_chord_circ_decline_qed_or_qex` | **QED** — mixed Decline inhabits `I_ok` | `SheetHenCook.v : chord_circular_decline_I_ok` |
| `CircularCook.v : ticket_0007_i1_gloss_qed_or_qex` | **QEX** — `I_gloss` undefined while CircGamma is QEX | `CircularCook.v : circular_gamma_is_qex` |

Witness: `0007-I.1-fence`. Status stays **Accepted**. Parks Γ / ι / ρ.

### Letter after Accept — I.2 ∀ Hit soundness (2026-09-09)

#688 ticketed the four-object fence on the locked witness. This letter
drops the lock on the γ classifier: `I_circles_gamma` is Hit iff the
integer proper discriminant and `on_full_circle` on both radical roots
(`p+` and `p−`, γ_full). R3 is the locked `(0,0)/(7,0)` r=5 witness
(`ticket_64_circ_hit_params_qed_or_qex`); I.2 recovers it as an
instance. Not CircularArc span membership. Sidecar cook stays locked
(I.3). Does not remint `CurveSegment` /
Exact* / `Dart` / Hobby / `ArcSplitAtNode` leftover-width. Does not
start I.3 / I.8–I.10 / Campaign II / H⊥ / a CRV-TOUCH kiss procedure.
Does not reopen Status.

| Stop | Arm | Lemma |
|------|-----|-------|
| `CircularCookHit.v : ticket_0007_i2_hit_sound_qed_or_qex` | **QED** — ∀ Hit iff proper disc ∧ `on_full_circle` both roots | `CircularCookHit.v : I_circles_gamma_hit_iff`, `CircularCookHit.v : on_full_circle_both_of_proper` |
| `CircularCookHit.v : ticket_0007_i2_arc_scope_qed_or_qex` | **QEX** — not arc membership; CircGamma stays QEX | `CircularCook.v : circular_gamma_is_qex` |

Witness: `0007-I.2-hit-sound`. Status stays **Accepted**. Parks Γ / ι / ρ.

### Letter after Accept — I.3 ∀ Empty / Decline (2026-09-09)

#689 dropped the lock on Hit. This letter drops it on Empty and Decline
without folding them into I.2's discriminant Hit iff. `ICircGEmpty`
iff the pair is proper and the γ_full images are disjoint on S
(triangle inequality). `ICircGDecline` iff the pair is not proper
(`d=0` or `r≤0`). Discriminant Empty and image-disjoint are different
proofs: concentric unequal radii are image-disjoint and Decline.
Not CircularArc span membership. Sidecar cook stays locked.
Does not remint `CurveSegment` / Exact* /
`Dart` / Hobby / `ArcSplitAtNode` leftover-width. Does not start
I.8–I.10 / Campaign II / H⊥ / a CRV-TOUCH kiss procedure. Does not
reopen Status.

| Stop | Arm | Lemma |
|------|-----|-------|
| `CircularCookEmpty.v : ticket_0007_i3_empty_qed_or_qex` | **QED** — ∀ Empty iff proper ∧ γ_full images disjoint | `CircularCookEmpty.v : I_circles_gamma_empty_iff` |
| `CircularCookEmpty.v : ticket_0007_i3_decline_qed_or_qex` | **QED** — ∀ Decline iff not a proper pair | `CircularCookEmpty.v : I_circles_gamma_decline_iff` |
| `CircularCookEmpty.v : ticket_0007_i3_disc_neq_image_qed_or_qex` | **QED** — concentric unequal radii: disjoint images, Decline | `CircularCookEmpty.v : concentric_unequal_images_disjoint` |
| `CircularCookEmpty.v : ticket_0007_i3_scope_qed_or_qex` | **QEX** — not arc membership; CircGamma stays QEX | `CircularCook.v : circular_gamma_is_qex` |

Witness: `0007-I.3-empty-decline`. Status stays **Accepted**. Parks Γ / ι / ρ.

### Letter after Accept — I.8 one-step leftover confluence (2026-09-09)

#690 dropped the lock on Empty / Decline. This letter drops the cook
lock on leftover *order*: `circ_leftovers_ab` = `circ_leftovers_ba`
on γ_full — the circular analogue of `SheetHenCook.v :
split_step_confluent`. Splitting parent A then B, or B then A,
yields the same leftover bag. Sidecar `cook_circ_root` leftovers
inhabit that bag; the locked plus / minus cooks recover it.
This is not the bag-level repeat-until-noded loop
(Parks ρ). Not leftover-width.
Not CircularArc span membership. Does
not remint `CurveSegment` / Exact* / `Dart` / Hobby /
`ArcSplitAtNode` leftover-width. Does not start I.9–I.10 /
Campaign II / H⊥ / a CRV-TOUCH kiss procedure. Does not reopen
Status.

| Stop | Arm | Lemma |
|------|-----|-------|
| `CircularCookConfluence.v : ticket_0007_i8_confluent_qed_or_qex` | **QED** — ∀ leftovers_ab = leftovers_ba on γ_full | `CircularCookConfluence.v : circ_split_step_confluent` |
| `CircularCookConfluence.v : ticket_0007_i8_cook_qed_or_qex` | **QED** — cook leftovers inhabit the bag; locked plus/minus recovered | `CircularCookConfluence.v : cook_circ_root_is_leftovers_ab` |
| `CircularCookConfluence.v : ticket_0007_i8_neq_bag_qed_or_qex` | **QED** — one-step ≠ bag loop | `CircularCookConfluence.v : i8_one_step_not_bag_loop` |
| `CircularCookConfluence.v : ticket_0007_i8_scope_qed_or_qex` | **QEX** — CircGamma stays QEX; bag loop stays obligation | `CircularCook.v : circular_gamma_is_qex` |

Witness: `0007-I.8-leftover-confluence`. Status stays **Accepted**. Parks Γ / ι / ρ.

### Letter after Accept — I.9 classifier ≠ cook (2026-09-09)

#691 ticketed one-step leftover confluence. This letter tickets the
honesty fence as a license denial: an `I_circles_z` / `I_CIRCULAR`
Hit is tags 0/1, not glossary `(p*, tᵢ, tⱼ)`. That Hit does **not**
license host `try_cook_hit`, sidecar `circ_split`, or
`first_cook_scope` expansion. Plus / minus leftovers on the locked
fixture meet at distinct `p*` — `t` comes from γ, not from the
classifier tags. First cook stays
chord–chord. Does not remint `CurveSegment` / Exact* / `Dart` /
Hobby / `ArcSplitAtNode` leftover-width. Does not start I.10 /
Campaign II / H⊥ / a CRV-TOUCH kiss procedure. Does not reopen
Status.

| Stop | Arm | Lemma |
|------|-----|-------|
| `CircularCookLicense.v : ticket_0007_i9_tags_qed_or_qex` | **QED** — hens are tags 0/1; ∀ IZHit is those tags | `CircularCookZ.v : classifier_hens_are_tags`, `CircularCookZ.v : iz_hit_only_tags` |
| `CircularCookLicense.v : ticket_0007_i9_not_host_cook_qed_or_qex` | **QED** — Z Hit ⇏ `try_cook_hit`; ⇏ first-cook expansion | `CircularCookLicense.v : i9_z_hit_not_try_cook_hit` |
| `CircularCookLicense.v : ticket_0007_i9_not_circ_split_qed_or_qex` | **QED** — same tags; plus/minus leftovers at distinct `p*` | `CircularCookLicense.v : i9_z_hit_not_circ_split_license` |
| `CircularCookLicense.v : ticket_0007_i9_scope_qed_or_qex` | **QEX** — CircGamma stays QEX; first cook stays chord–chord | `CircularCook.v : circular_gamma_is_qex` |

Witness: `0007-I.9-classifier-neq-cook`. Status stays **Accepted**. Parks Γ / ι / ρ.

### Letter after Accept — I.10 Campaign-I close (2026-09-09)

#692 ticketed that a classifier Hit is not a cook license. This
letter closes Campaign I. Sidecar cook exists on a constructed
circular Hit (both radical roots / `MintTwo`). Parks Γ.
`first_cook_scope` stays chord–chord. `I_CIRCULAR` stays a
classifier (tags 0/1). The #666 four-object fence holds by
observation. Campaign II and H⊥ are named parked — not silently
done. No new kernel. Not SQL/MM done. Does not remint
`CurveSegment` / Exact* / `Dart` / Hobby / `ArcSplitAtNode`
leftover-width. Does not start Campaign II / H⊥ / a CRV-TOUCH
kiss procedure. Does not reopen Status.

| Stop | Arm | Lemma |
|------|-----|-------|
| `CircularCookClose.v : ticket_0007_i10_sidecar_qed_or_qex` | **QED** — sidecar cook on constructed circular Hit, both roots | `CircularCookClose.v : i10_sidecar_cook_both_roots`, `CircularCookSplit.v : cooked_circ_mint_two_ok` |
| `CircularCookClose.v : ticket_0007_i10_classifier_qed_or_qex` | **QED** — `I_CIRCULAR` stays tags 0/1; #666 fence holds | `CircularCookClose.v : i10_classifier_stays_tags`, `CircularCookClose.v : i10_fence_holds` |
| `CircularCookClose.v : ticket_0007_i10_host_qed_or_qex` | **QEX** — CircGamma stays QEX; first cook stays chord–chord | `CircularCook.v : circular_gamma_is_qex`, `SheetHenCook.v : first_cook_scope_chord_chord` |
| `CircularCookClose.v : ticket_0007_i10_park_qed_or_qex` | **QEX** — Campaign II and H⊥ named parked; SQL/MM not done | `CircularCookClose.v : campaign_ii_is_parked`, `CircularCookClose.v : hperp_is_parked` |

Witness: `0007-I.10-campaign-i-close`. Status stays **Accepted**. Parks Γ / ι / ρ.

### Letter after Accept — II.1 span filter as IResult (2026-09-09)

I.10 closed Campaign I and named Campaign II parked. This letter
unparks **II.1 only**. A radical root is an **arc** Hit iff
`on_arc_gamma` both — an IResult / Hit|Empty|Decline-style filter
on span γ, not γ_full. Locked `(0,0)/(7,0)` r=5 proper arcs: `p+`
in-span (Hit); `p−` out-of-span (Empty) while still on γ_full
(I.2). Host circular `I_ok` stays
Decline. Span Hit is not host `I_ok`. II.2–II.4, H⊥, and the
SQL/MM Part 3 required-type cathedral (CircularString /
CompoundCurve / CurvePolygon) stay parked. A CircularString
theorem needs concatenation; this is one Arc. Does not remint
`CurveSegment` / Exact* / `Dart` / Hobby / `ArcSplitAtNode`
leftover-width. Does not start II.2–II.4 / H⊥ / a CRV-TOUCH kiss
procedure. Does not reopen Status.

| Stop | Arm | Lemma |
|------|-----|-------|
| `CircularCookSpanFilter.v : ticket_0007_ii1_hit_qed_or_qex` | **QED** — Hit iff `on_arc_gamma` both; locked `p+` inhabits | `CircularCookSpanFilter.v : I_span_root_hit_iff`, `CircularCookSpanFilter.v : ii1_locked_plus_span_hit` |
| `CircularCookSpanFilter.v : ticket_0007_ii1_minus_qed_or_qex` | **QED** — locked `p−` is Empty and still on γ_full | `CircularCookSpanFilter.v : ii1_locked_minus_span_empty`, `CircularCookSpanFilter.v : ii1_minus_full_not_span` |
| `CircularCookSpanFilter.v : ticket_0007_ii1_empty_neq_decline_qed_or_qex` | **QED** — Empty ≠ Decline; invalid controls Decline | `CircularCookSpanFilter.v : ii1_span_empty_neq_decline`, `CircularCookSpanFilter.v : ii1_invalid_decline` |
| `CircularCookSpanFilter.v : ticket_0007_ii1_host_qed_or_qex` | **QEX** — CircGamma stays QEX; first cook stays chord–chord; span Hit ≠ host `I_ok` | `CircularCook.v : circular_gamma_is_qex`, `CircularCookSpanFilter.v : ii1_span_hit_not_host_I_ok` |
| `CircularCookSpanFilter.v : ticket_0007_ii1_park_qed_or_qex` | **QEX** — II.2–II.4 / H⊥ / SQL/MM cathedral parked; II.1 landed | `CircularCookSpanFilter.v : campaign_ii1_is_landed`, `CircularCookSpanFilter.v : campaign_ii2_is_parked` |

Witness: `0007-II.1-span-filter`. Status stays **Accepted**. Parks Γ / ι / ρ.

### Letter after Accept — II.2 split γ_span at in-span t (2026-09-09)

II.1 unparked the span filter and named II.2–II.4 parked. This letter
unparks **II.2 only**. An in-span Hit (`on_arc_gamma` / `I_span_root`
/ locked `p+`) splits each **span** interpolant `arc_gamma` at the
Hit’s in-span `tᵢ` / `tⱼ`. Leftovers meet at `p*` — shared endpoint
is Hit incidence, not a kiss. Leftover γ stays on the parent circle
and on the parent `on_arc_gamma` honesty story. Not γ_full. Not
`circ_split` from `CircularCookSplit`. Locked `p−` stays II.1 Empty
— this letter does not invent a span cook for it. Host circular
`I_ok` stays Decline. Span Hit is not host
`I_ok`. II.3 (`I_ok_circ`), II.4 honesty letter, H⊥, and the SQL/MM
Part 3 required-type cathedral (CircularString / CompoundCurve /
CurvePolygon) stay parked. A CircularString theorem needs
concatenation; this is one Arc split. Does not remint
`CurveSegment` / Exact* / `Dart` / Hobby / `ArcSplitAtNode`
leftover-width. Does not start II.3–II.4 / H⊥ / a CRV-TOUCH kiss
procedure. Does not reopen Status.

| Stop | Arm | Lemma |
|------|-----|-------|
| `CircularCookSpanSplit.v : ticket_0007_ii2_meet_qed_or_qex` | **QED** — leftovers meet at locked `p+`; join is the II.1 Hit, not Empty | `CircularCookSpanSplit.v : cooked_span_plus_meets`, `CircularCookSpanSplit.v : leftover_meet_is_hit_not_kiss` |
| `CircularCookSpanSplit.v : ticket_0007_ii2_honesty_qed_or_qex` | **QED** — leftover γ on the parent circle and parent `on_arc_gamma` | `CircularCookSpanSplit.v : cooked_span_plus_on_parent`, `CircularCookSpanSplit.v : span_split_uses_arc_gamma` |
| `CircularCookSpanSplit.v : ticket_0007_ii2_minus_qed_or_qex` | **QED** — locked `p−` stays Empty; Empty / Decline mint no span cook | `CircularCookSpanSplit.v : cooked_span_minus_none` |
| `CircularCookSpanSplit.v : ticket_0007_ii2_host_qed_or_qex` | **QEX** — CircGamma stays QEX; first cook stays chord–chord; span Hit ≠ host `I_ok` | `CircularCook.v : circular_gamma_is_qex`, `CircularCookSpanSplit.v : ii2_span_hit_not_host_I_ok` |
| `CircularCookSpanSplit.v : ticket_0007_ii2_park_qed_or_qex` | **QEX** — II.3–II.4 / H⊥ / SQL/MM cathedral parked; II.2 landed | `CircularCookSpanSplit.v : campaign_ii2_is_landed`, `CircularCookSpanSplit.v : campaign_ii3_is_parked` |

Witness: `0007-II.2-span-split`. Status stays **Accepted**. Parks Γ / ι / ρ.

### Letter after Accept — II.3 I_ok_circ on EggCircularArc × EggCircularArc (2026-09-09)

II.2 unparked the span split and named II.3–II.4 parked. This letter
unparks **II.3 only**. `I_ok_circ` is the first glossary-type
inhabitant on EggCircularArc × EggCircularArc using sidecar
`arc_gamma` / span filter / span split. Host `I_ok` on circular
eggs stays Decline; span Hit ≠ host `I_ok` until this letter —
an `I_ok_circ` Hit licenses the II.2 cook. Locked `(0,0)/(7,0)`
r=5 proper arcs inhabit Hit at `p+`. Pair-level Empty is a far
quarter of the I.3 `(0,0)/(20,0)` r=5 disjoint circles (the
locked A×B pair is Hit, so per-root `p−` Empty is not pair
Empty). Invalid controls Decline. ∀ Hit / Empty / Decline as a
Prop are definitional; this letter does not mint a computed
classifier. `first_cook_scope` stays
chord–chord. II.4 honesty letter, H⊥, and the SQL/MM Part 3
required-type cathedral (CircularString / CompoundCurve /
CurvePolygon) stay parked. A CircularString theorem needs
concatenation; this is one Arc. Does not remint
`CurveSegment` / Exact* / `Dart` / Hobby / `ArcSplitAtNode`
leftover-width. Does not start II.4 / H⊥ / a CRV-TOUCH kiss
procedure. Does not reopen Status.

| Stop | Arm | Lemma |
|------|-----|-------|
| `CircularCookOkCirc.v : ticket_0007_ii3_hit_qed_or_qex` | **QED** — Hit iff `on_arc_gamma` both; locked `p+` inhabits | `CircularCookOkCirc.v : I_ok_circ_hit_iff`, `CircularCookOkCirc.v : ii3_locked_plus_I_ok_circ` |
| `CircularCookOkCirc.v : ticket_0007_ii3_license_qed_or_qex` | **QED** — `I_ok_circ` Hit licenses `span_split`; leftovers meet at `p+` | `CircularCookOkCirc.v : I_ok_circ_hit_licenses_span_cook`, `CircularCookOkCirc.v : ii3_locked_plus_licenses_cook` |
| `CircularCookOkCirc.v : ticket_0007_ii3_empty_qed_or_qex` | **QED** — locked far pair inhabits Empty; Empty ≠ Decline; pair Hit ≠ per-root Empty | `CircularCookOkCirc.v : ii3_locked_empty`, `CircularCookOkCirc.v : ii3_pair_hit_neq_root_empty` |
| `CircularCookOkCirc.v : ticket_0007_ii3_host_qed_or_qex` | **QEX** — CircGamma stays QEX; first cook stays chord–chord; `I_ok_circ` Hit ≠ host `I_ok` | `CircularCook.v : circular_gamma_is_qex`, `CircularCookOkCirc.v : ii3_I_ok_circ_hit_not_host_I_ok` |
| `CircularCookOkCirc.v : ticket_0007_ii3_park_qed_or_qex` | **QEX** — II.4 / H⊥ / SQL/MM cathedral parked; II.3 landed | `CircularCookOkCirc.v : campaign_ii3_is_landed`, `CircularCookOkCirc.v : campaign_ii4_is_parked` |

Witness: `0007-II.3-I-ok-circ`. Status stays **Accepted**. Parks Γ / ι / ρ.

### Letter after Accept — II.4 Campaign-II close (2026-09-09)

II.3 unparked `I_ok_circ` and named II.4 / H⊥ / SQL/MM parked.
This letter **closes Campaign II**. `I_ok_circ` exists as the
sidecar glossary inhabitant on EggCircularArc × EggCircularArc
(one Arc). `first_cook_scope` stays
chord–chord. Host circular `I_ok` stays Decline. `I_ok_circ`
Hit ≠ host `I_ok`. Leftover shared endpoint is Hit incidence
(= ¬Empty), not a CRV-TOUCH kiss certificate. Not a bag noder
(Parks ρ). H⊥ stays parked.

Phase B SQL/MM Part 3 **required**-type gaps are named so AFK
Phase B can start the smallest required-type 𝓘 cuts:
CircularString (needs concatenation), CompoundCurve, and
CurvePolygon. Not “SQL/MM done”. Not a remint of
`CurveSegment` / Exact* / `Dart` / Hobby / `ArcSplitAtNode`
leftover-width. Does not start Phase B / H⊥ / a CircGamma
remint / a CRV-TOUCH kiss procedure / the Part 3 cathedral.
Does not reopen Status.

| Stop | Arm | Lemma |
|------|-----|-------|
| `CircularCookCloseII.v : ticket_0007_ii4_inhabitant_qed_or_qex` | **QED** — sidecar `I_ok_circ` Hit / Empty / Decline on locked fixtures; one Arc | `CircularCookCloseII.v : ii4_sidecar_inhabitant`, `CircularCookCloseII.v : ii4_inhabitant_is_one_arc` |
| `CircularCookCloseII.v : ticket_0007_ii4_not_kiss_qed_or_qex` | **QED** — leftover meet is Hit and ¬Empty; `I_ok_circ` Hit ≠ host `I_ok` | `CircularCookCloseII.v : ii4_leftover_meet_not_empty`, `CircularCookCloseII.v : ii4_I_ok_circ_hit_not_host_I_ok` |
| `CircularCookCloseII.v : ticket_0007_ii4_host_qed_or_qex` | **QEX** — CircGamma stays QEX; first cook stays chord–chord | `CircularCook.v : circular_gamma_is_qex`, `SheetHenCook.v : first_cook_scope_chord_chord` |
| `CircularCookCloseII.v : ticket_0007_ii4_phase_b_qed_or_qex` | **QEX** — Phase B CS / CC / CP gaps named; bag loop stays obligation; H⊥ parked; SQL/MM not done; Campaign II closed | `CircularCookCloseII.v : phase_b_cs_is_gap`, `CircularCookCloseII.v : ii4_not_bag_noder`, `CircularCookCloseII.v : campaign_ii_is_closed` |

Witness: `0007-II.4-campaign-ii-close`. Status stays **Accepted**. Parks Γ / ι / ρ.

### Letter after Accept — Phase B.1 CircularString concat joints (2026-09-09)

II.4 closed Campaign II and named Phase B SQL/MM Part 3
**required**-type gaps (CircularString / CompoundCurve /
CurvePolygon). This letter unparks **CircularString joints
only**. A CircularString is a sequence of `CircEgg` :=
`CircularArc`. A concat joint is `I_ok_circ` Hit at
`(arc_end a, tᵢ=1, tⱼ=0)` via sidecar `arc_gamma` —
reuse of the II.1–II.3 stack, not a new kernel. Joint
params are not interior (`0<t<1`); the join is concat
incidence (already a hen), not an interior span cook and
not a CRV-TOUCH kiss certificate.

Locked fixture: the V-CS odd_closed 5-control
`CIRCULARSTRING(-5 0, 0 5, 5 0, 0 -5, -5 0)` as two
`CircEgg`. Not a remint of `CircularStringValid.v`.
`first_cook_scope` stays
chord–chord. Host circular `I_ok` stays Decline.
`I_ok_circ` Hit ≠ host `I_ok`. CompoundCurve /
CurvePolygon / H⊥ stay parked. Not a CircGamma remint.
Not “SQL/MM done”. Does not remint `CurveSegment` /
Exact* / `Dart` / Hobby / `ArcSplitAtNode` leftover-width.
Does not start CompoundCurve / CurvePolygon / H⊥ / a
CRV-TOUCH kiss procedure. Does not reopen Status.

| Stop | Arm | Lemma |
|------|-----|-------|
| `CircularCookCsConcat.v : ticket_0007_b1_joint_qed_or_qex` | **QED** — ∀ `cs_joint` is `I_ok_circ` Hit at `(end, 1, 0)`; `CircEgg` = `CircularArc` | `CircularCookCsConcat.v : cs_joint_I_ok_circ` |
| `CircularCookCsConcat.v : ticket_0007_b1_not_interior_qed_or_qex` | **QED** — locked 2-arc CS is contiguous; joint params not interior | `CircularCookCsConcat.v : locked_cs_contiguous`, `CircularCookCsConcat.v : joint_params_not_interior` |
| `CircularCookCsConcat.v : ticket_0007_b1_reuse_qed_or_qex` | **QED** — reuse `I_ok_circ`; no new kernel; joint Hit ≠ host `I_ok` | `CircularCookCsConcat.v : b1_reuse_no_new_kernel`, `CircularCookCsConcat.v : b1_I_ok_circ_hit_not_host_I_ok` |
| `CircularCookCsConcat.v : ticket_0007_b1_host_qed_or_qex` | **QEX** — CircGamma stays QEX; first cook stays chord–chord | `CircularCook.v : circular_gamma_is_qex`, `SheetHenCook.v : first_cook_scope_chord_chord` |
| `CircularCookCsConcat.v : ticket_0007_b1_park_qed_or_qex` | **QEX** — CompoundCurve / CurvePolygon / H⊥ parked; SQL/MM not done; B.1 landed | `CircularCookCsConcat.v : phase_b1_is_landed`, `CircularCookCsConcat.v : phase_b_cc_is_gap` |

Witness: `0007-B.1-cs-concat-joints`. Status stays **Accepted**. Parks Γ / ι / ρ.

### Letter after Accept — Phase B.2 CompoundCurve member joints (2026-09-09)

B.1 unparked CircularString joints and left CompoundCurve /
CurvePolygon named as Phase B gaps. This letter unparks
**CompoundCurve joints only**. A CompoundCurve is a sequence
of LineString (chords) and CircularString (`CircEgg`)
members joined head to tail — the SQL/MM Part 3
required-type reading already used in II.4 / B.1 fences.
Not a remint of `CurveSegment`. Not the Koc C¹ clothoid
assembly.

Reuse, not a new kernel:

* LS–LS joint is host `I_ok` Hit at `(ce_p1, tᵢ=1, tⱼ=0)`
  via `chord_eval` (first cook).
* CS–CS member joint is `I_ok_circ` Hit at `(arc_end, tᵢ=1,
  tⱼ=0)` via B.1 `cs_joint` / sidecar `arc_gamma`.
* Mixed LS–CS joint is sidecar `I_ok_mixed` Hit at
  `(ce_p1, tᵢ=1, tⱼ=0)` via `SidecarCircMixed.v`. Host
  `I_ok` mixed stays Decline (I.1 fence). `I_ok_mixed` Hit
  ≠ host `I_ok`. Concat incidence is already a hen, not an
  interior span cook and not a CRV-TOUCH kiss certificate.

Locked mixed fixture (type-distinct inhabitant):
`COMPOUNDCURVE((-5 0, 5 0), CIRCULARSTRING(5 0, 0 -5, -5 0))`.
`first_cook_scope` stays
chord–chord. Host circular `I_ok` stays Decline.
`phase_b_compound_curve_status` is **Landed** (mixed LS–CS
inhabits `I_ok_mixed`, not host `I_ok`). Letter B.2 landed
(`PhaseB2Landed`) ≠ SQL/MM done / Phase B done-when.
CurvePolygon / H⊥ stay parked. Parks ι. Not a
CircGamma remint. Not “SQL/MM done”.
Does not remint `CurveSegment` / Exact* / `Dart` / Hobby /
`ArcSplitAtNode` leftover-width / `CompoundCurveKoc*`.
Does not start CurvePolygon / H⊥ / a CRV-TOUCH kiss
procedure. Does not reopen Status.

| Stop | Arm | Lemma |
|------|-----|-------|
| `CircularCookCcConcat.v : ticket_0007_b2_mixed_qed_or_qex` | **QED** — locked mixed LS+CS CC is contiguous; mixed joint is `I_ok_mixed` Hit; host `I_ok` stays Decline | `CircularCookCcConcat.v : locked_cc_mixed_contiguous`, `CircularCookCcConcat.v : locked_cc_mixed_I_ok_mixed` |
| `CircularCookCcConcat.v : ticket_0007_b2_reuse_qed_or_qex` | **QED** — ∀ LS–LS joint is host `I_ok` Hit; ∀ CS–CS member joint reuses `I_ok_circ`; ∀ mixed joint reuses `I_ok_mixed`; no new kernel | `CircularCookCcConcat.v : ls_joint_I_ok`, `CircularCookCcConcat.v : cc_cs_cs_joint_I_ok_circ`, `CircularCookCcConcat.v : cc_mixed_ls_cs_I_ok_mixed` |
| `CircularCookCcConcat.v : ticket_0007_b2_not_interior_qed_or_qex` | **QED** — locked mixed / LS–LS / CS–CS CCs are contiguous; joint params not interior | `CircularCookCcConcat.v : locked_cc_ls_ls_contiguous`, `CircularCookCcConcat.v : joint_params_not_interior` |
| `CircularCookCcConcat.v : ticket_0007_b2_host_qed_or_qex` | **QEX** — CircGamma stays QEX; first cook stays chord–chord; mixed Hit is not host `I_ok` | `CircularCook.v : circular_gamma_is_qex`, `SheetHenCook.v : first_cook_scope_chord_chord` |
| `CircularCookCcConcat.v : ticket_0007_b2_park_qed_or_qex` | **QEX** — CurvePolygon / H⊥ / interior mixed cook parked; SQL/MM not done; B.2 letter landed; CC required-type Landed (`I_ok_mixed`, not host `I_ok`) | `CircularCookCcConcat.v : phase_b2_is_landed`, `CircularCookCcConcat.v : phase_b_cc_is_landed`, `CircularCookCcConcat.v : phase_b_cp_is_gap` |

Witness: `0007-B.2-cc-member-joints`. Status stays **Accepted**. Parks Γ / ι / ρ.

### Letter after Accept — Phase B.3 CurvePolygon ring closure (2026-09-09)

B.2 unparked CompoundCurve joints and left ring closure as
CurvePolygon. This letter unparks **CurvePolygon rings only**.
A CurvePolygon ring is a closed CircularString or a closed
CompoundCurve — the SQL/MM Part 3 required-type reading
already used in II.4 / B.1 / B.2 fences. The carrier is B.2
`CompoundCurveMembers` that is contiguous and closed (last
member joins first). A one-member `[CcCS arcs]` is a CS ring.
A mixed / multi-member list is a CC ring. Not a remint of
`CurveSegment` / `CurveGeometry.CurvePolygon`.

Reuse, not a new kernel:

* Sequential member joints stay B.2.
* CS–CS closing is `I_ok_circ` Hit at `(arc_end, tᵢ=1, tⱼ=0)`
  via B.1 `cs_joint` / sidecar `arc_gamma`.
* LS–LS closing is host `I_ok` Hit at `(ce_p1, tᵢ=1, tⱼ=0)`
  via `chord_eval` (first cook).
* Mixed closing is sidecar `I_ok_mixed` Hit at
  `(arc_end, tᵢ=1, tⱼ=0)` via `SidecarCircMixed.v`. Host
  `I_ok` mixed stays Decline (I.1 fence). `I_ok_mixed` Hit
  ≠ host `I_ok`. Ring-close incidence is already a hen, not
  an interior span cook and not a CRV-TOUCH kiss certificate.

Locked CS-ring fixture:
`CURVEPOLYGON((CIRCULARSTRING(-5 0, 0 5, 5 0, 0 -5, -5 0)))`.
Locked mixed-ring fixture:
`CURVEPOLYGON((COMPOUNDCURVE((-5 0, 5 0), CIRCULARSTRING(5 0, 0 -5, -5 0))))`.
`first_cook_scope` stays
chord–chord. Host circular `I_ok` stays Decline.
`phase_b_curve_polygon_status` is **Landed** (mixed LS–CS
closing inhabits `I_ok_mixed`, not host `I_ok`).
`phase_b_compound_curve_status` is **Landed**. Phase B stays
**Open** — letter B.3 landed (`PhaseB3Landed`) ≠ SQL/MM done
/ Phase B done-when. Letter enum vs required-type stay
distinct.
H⊥ stays parked. Parks Γ / ρ. Not a CircGamma remint. Not
“SQL/MM done” (cathedral / Multi / optional Part 3 types).
Does not remint `CurveSegment` / Exact* / `Dart` / Hobby /
`ArcSplitAtNode` leftover-width / the CompoundCurveKoc family.
Does not start H⊥ / a CRV-TOUCH kiss procedure. Does not
reopen Status.

| Stop | Arm | Lemma |
|------|-----|-------|
| `CircularCookCpConcat.v : ticket_0007_b3_closed_qed_or_qex` | **QED** — locked CS / mixed rings are closed + contiguous; CS closing is `I_ok_circ`; mixed closing is `I_ok_mixed` Hit; host `I_ok` stays Decline | `CircularCookCpConcat.v : locked_cp_cs_ring_closed`, `CircularCookCpConcat.v : locked_cp_mixed_closing_I_ok_mixed` |
| `CircularCookCpConcat.v : ticket_0007_b3_reuse_qed_or_qex` | **QED** — closing joints reuse B.1 `I_ok_circ`, B.2 host `I_ok`, and `I_ok_mixed`; `CpRing` is B.2 members; no new kernel | `CircularCookCpConcat.v : cp_closing_cs_cs_I_ok_circ`, `CircularCookCpConcat.v : cp_closing_mixed_cs_ls_I_ok_mixed` |
| `CircularCookCpConcat.v : ticket_0007_b3_not_interior_qed_or_qex` | **QED** — closing params not interior; locked hole-free CPs inhabit | `CircularCookCpConcat.v : locked_cp_cs_ok`, `CircularCookCpConcat.v : joint_params_not_interior` |
| `CircularCookCpConcat.v : ticket_0007_b3_host_qed_or_qex` | **QEX** — CircGamma stays QEX; first cook stays chord–chord; mixed closing Hit is not host `I_ok` | `CircularCook.v : circular_gamma_is_qex`, `SheetHenCook.v : first_cook_scope_chord_chord` |
| `CircularCookCpConcat.v : ticket_0007_b3_park_qed_or_qex` | **QEX** — H⊥ / CircGamma remint / bag-noder / interior mixed cook parked; SQL/MM not done; B.3 letter landed; CP / CC required-type Landed (`I_ok_mixed`, not host `I_ok`); Phase B Open | `CircularCookCpConcat.v : phase_b3_is_landed`, `CircularCookCpConcat.v : phase_b_cp_is_landed`, `CircularCookCpConcat.v : phase_b_is_open` |

Witness: `0007-B.3-cp-ring-closure`. Status stays **Accepted**. Parks Γ / ι / ρ.

### Letter after Accept — Phase B mixed LS–CS joints (2026-09-10)

B.2 / B.3 proved same-kind joints Hit and left mixed LS–CS
as host `I_ok` Decline (I.1). That Decline is the
out-of-scope / `MkOutOfScope` fence, not missing geometry at
a contiguous endpoint. This letter cuts the smallest honest
Hit: sidecar `I_ok_mixed` on `ChordEgg` × `CircEgg` at
`(p, tᵢ=1, tⱼ=0)` via host `chord_eval` and sidecar
`arc_gamma`. Joint params are not interior. Concat incidence
is already a hen. 
`first_cook_scope` stays chord–chord. Host mixed `I_ok`
stays Decline. `I_ok_mixed` Hit ≠ host `I_ok`. Parks ι. Not a CircGamma remint.
Not “SQL/MM done”. Does not expand first cook to
circular×chord interiors. Does not start H⊥ / a CRV-TOUCH
kiss procedure / a bag noder / MultiCurve. Does not reopen
Status.

| Stop | Arm | Lemma |
|------|-----|-------|
| `SidecarCircMixed.v : ticket_0007_b_mixed_hit_qed_or_qex` | **QED** — ∀ LS–CS / CS–LS joint is `I_ok_mixed` Hit at `(end, 1, 0)`; host `I_ok` mixed stays Decline | `SidecarCircMixed.v : ls_cs_joint_I_ok_mixed`, `SidecarCircMixed.v : cs_ls_joint_I_ok_mixed` |
| `SidecarCircMixed.v : ticket_0007_b_mixed_license_qed_or_qex` | **QED** — Hit licenses already-hen concat incidence; joint params not interior | `SidecarCircMixed.v : I_ok_mixed_hit_licenses_joint_hen`, `SidecarCircMixed.v : locked_mixed_ls_cs_I_ok_mixed` |
| `SidecarCircMixed.v : ticket_0007_b_mixed_host_qed_or_qex` | **QEX** — CircGamma stays QEX; first cook stays chord–chord; interior mixed cook parked; `I_ok_mixed` Hit ≠ host `I_ok` | `CircularCook.v : circular_gamma_is_qex`, `SheetHenCook.v : first_cook_scope_chord_chord` |
| `SidecarCircMixed.v : ticket_0007_b_mixed_park_qed_or_qex` | **QEX** — interior mixed cook / H⊥ / CircGamma remint / bag noder parked; SQL/MM not done; mixed letter landed | `SidecarCircMixed.v : mixed_letter_is_landed`, `SidecarCircMixed.v : mixed_interior_cook_is_parked` |

Witness: `0007-B-mixed-ls-cs-joints`. Status stays **Accepted**. Parks Γ / ι / ρ.

### Letter after Accept — Phase B MultiCurve / MultiSurface bags (2026-09-10)

B.1–B.3 plus mixed sidecar Hit inhabit CS / CC / CP joints.
This letter unparks **Multi as bags only**. MultiCurve is a
bag of already-Qed Curve members (CircularString /
CompoundCurve). MultiSurface is a bag of already-Qed Surface
members (CurvePolygon). Members need not be contiguous —
that is the bag vs sequence distinction, not the bag-level
cook loop (Parks ρ). Membership
and optional shared-endpoint pairwise joints reuse existing
`I_ok` / `I_ok_circ` / `I_ok_mixed`. No new kernel.

`first_cook_scope` stays
chord–chord. Host mixed `I_ok` stays Decline. Parks ι.
Multi required-type
stays **Gap** (optional Part 3). Phase B stays **Open**.
Letter landed ≠ cathedral Landed / Phase B done-when /
SQL/MM done. Not a CircGamma remint. Does not start H⊥ /
a CRV-TOUCH kiss procedure / a bag noder. Does not reopen
Status.

| Stop | Arm | Lemma |
|------|-----|-------|
| `SidecarCircBags.v : ticket_0007_b_bags_inhabit_qed_or_qex` | **QED** — locked MultiCurve / MultiSurface inhabit as bags; far MultiCurve is bag-ok and not contiguous | `SidecarCircBags.v : locked_mc_typed_ok`, `SidecarCircBags.v : locked_ms_ok`, `SidecarCircBags.v : bags_not_concat` |
| `SidecarCircBags.v : ticket_0007_b_bags_reuse_qed_or_qex` | **QED** — membership joints reuse `I_ok` / `I_ok_circ` / `I_ok_mixed`; optional pair reuses `I_ok_mixed`; no new kernel | `SidecarCircBags.v : bags_cs_member_joint_I_ok_circ`, `SidecarCircBags.v : bags_cc_member_joint_I_ok_mixed`, `SidecarCircBags.v : bags_optional_pair_I_ok_mixed` |
| `SidecarCircBags.v : ticket_0007_b_bags_host_qed_or_qex` | **QEX** — CircGamma stays QEX; first cook stays chord–chord; host mixed `I_ok` Decline; interior mixed cook parked | `CircularCook.v : circular_gamma_is_qex`, `SheetHenCook.v : first_cook_scope_chord_chord` |
| `SidecarCircBags.v : ticket_0007_b_bags_park_qed_or_qex` | **QEX** — bag noder / H⊥ / CircGamma remint / SQL/MM cathedral parked; Multi required-type Gap; Phase B Open; bags letter landed | `SidecarCircBags.v : bags_letter_is_landed`, `SidecarCircBags.v : multi_required_is_gap`, `SidecarCircBags.v : bags_cathedral_is_not_landed` |

Witness: `0007-B-bags`. Status stays **Accepted**. Parks Γ / ι / ρ.

### Letter after Accept — ι interior circular×chord (2026-09-10)

Sidecar `I_ok_mixed` already inhabits the μ LS–CS / CS–LS joint
at `(end, t=1, t=0)` (`SidecarCircMixed.v`). That Hit is concat
incidence, not an interior proper-cross. `mixed_joint_params` is
`(1,0)` or `(0,1)`; `interior_span_params` is `0<ti<1 ∧ 0<tj<1`.
Those fences are incompatible
(`SidecarCircMixed.v : mixed_joint_params_not_interior`).

**QEX** (discharged). An interior `I_ok_mixed` Hit is not
available without reminting `I_ok_mixed`'s Hit arm, expanding
`first_cook_scope` to circular×chord, or reminting CircGamma /
host `I_ok`. Named gap, not a bool:

1. `I_ok_mixed` Hit is gated by `mixed_joint_params`. Any Hit
   therefore has `~ interior_span_params`
   (`SidecarCircInterior.v : I_ok_mixed_hit_is_joint_params`).
2. The would-be interior arm (`on_chord ∧ on_arc_gamma ∧
   interior_span_params`) does not inhabit `I_ok_mixed`
   (`SidecarCircInterior.v : interior_arm_not_I_ok_mixed`).
3. Host mixed `I_ok` Hit stays False; first cook stays
   chord–chord. Host CircGamma stays QEX.

ι is not μ. ι is not host `I_ok`. ι is not Γ. Letter landed ≠
interior cook Landed / Phase B done-when / cathedral Landed /
Multi required-type Landed. ADR-0007 stays Accepted.

| Stop | Arm | Lemma |
|------|-----|-------|
| `SidecarCircInterior.v : ticket_0007_iota_gap_qed_or_qex` | **QEX** — `I_ok_mixed` Hit is joint-only; interior arm missing | `SidecarCircInterior.v : interior_mixed_hit_arm_missing`, `SidecarCircInterior.v : I_ok_mixed_interior_hit_false` |
| `SidecarCircInterior.v : ticket_0007_iota_mu_qed_or_qex` | **QED** — μ joint still inhabits `I_ok_mixed` at `(end, 1, 0)` and is not interior | `SidecarCircInterior.v : iota_mu_joint_not_interior` |
| `SidecarCircInterior.v : ticket_0007_iota_host_qed_or_qex` | **QEX** — CircGamma stays QEX; first cook stays chord–chord; host mixed `I_ok` Decline | `CircularCook.v : circular_gamma_is_qex`, `SheetHenCook.v : first_cook_scope_chord_chord` |
| `SidecarCircInterior.v : ticket_0007_iota_park_qed_or_qex` | **QEX** — interior cook / H⊥ / bag noder / cathedral parked; Phase B Open; ι letter landed | `SidecarCircInterior.v : iota_letter_is_landed`, `SidecarCircInterior.v : iota_interior_cook_is_parked` |

Witness: `0007-iota-interior-mixed`. Status stays **Accepted**. Parks Γ / ι / ρ.

### Letter after Accept — Γ CircGamma core-slice stop (2026-09-10)

Host CircGamma (Γ) is the 3-axiom interpolant `γ : [0,1] → S` on
`CircularArc` that would flip `circular_gamma_status` to
`CircGammaDischarged` and let `I_gloss` become defined. The sidecar
already has span-restricted `arc_gamma` (`CircularCookSpan.v`) —
that is **not** host Γ. This letter is the honest QED∨QEX stop.

**QEX** (discharged). Discharge is not available without atan2 /
`Classical_Prop.classic` (sidecar `circ_gamma` / `arc_gamma`) or
without expanding `Egg` / `first_cook_scope`. Named gap, not a
bool:

1. `Egg` has no `MkCirc` constructor — circular eggs are only
   `MkOutOfScope` (`CircularCook.v : circular_egg_only_out_of_scope`).
2. Chord-project nlerp, the natural 3-axiom interpolant, misses the
   principal span on the reflex fixture start `(1,0)` → mid `(−1,0)`
   → end `(0,1)` (`CircularCook.v : reflex_nlerp_misses_principal`).
   Piecewise nlerp through mid is not total (that half is antipodal).
3. Campaign tickets couple `CircGammaDischarged` with
   `first_cook_scope` circular–circular. This letter does not expand
   first cook. ADR-0007 stays Accepted.

`I_gloss` stays undefined (`CircularCook.v : ticket_0007_i1_gloss_qed_or_qex`).
Host circular `I_ok` stays Decline. `I_ok_circ` / `I_ok_mixed` Hit
is not host `I_ok`. Do not rename sidecar `arc_gamma` as host
CircGamma. Do not fake Discharge.

| Stop | Arm | Lemma |
|------|-----|-------|
| `CircularCook.v : ticket_64_circ_gamma_qed_or_qex` | **QEX** — `MkCirc` missing; nlerp misses reflex principal span; first cook stays chord–chord | `CircularCook.v : circ_gamma_mkcirc_missing`, `CircularCook.v : reflex_nlerp_misses_principal` |
| `CircularCook.v : ticket_0007_i1_gloss_qed_or_qex` | **QEX** — `I_gloss` undefined; `MkCirc` missing; host circular `I_ok` is Decline only | `CircularCook.v : circ_gamma_mkcirc_missing`, `SheetHenCook.v : circular_decline_I_ok` |
| `CircularCook.v : ticket_0007_gamma_nlerp_qed_or_qex` | **QEX** — nlerp misses principal span; piecewise nlerp degenerate on the same fixture | `CircularCook.v : reflex_nlerp_misses_principal`, `CircularCook.v : reflex_piecewise_nlerp_degenerate` |

Witness: `0007-Gamma-circgamma`. Status stays **Accepted**. Parks Γ / ι / ρ.

### Letter after Accept — ρ bag-loop named QEX (2026-09-10)

Pairwise leftover-width decrease and one-step confluence are
already QED (`ticket_0007_pairwise_split_qed_or_qex` / I.8).
This letter is the **bag** loop, not that pairwise step and
not η Multi bags (`SidecarCircBags`).

QED would flip `cook_loop_status` to `LoopDischarged` with a
real termination + confluence theorem on leftover bags. That
needs a bag-term measure covering kiss / ShareOne / MintTwo
cycles — not available without a CRV-TOUCH prototype.

QEX (this letter): named 508-style gap, not a bool.

1. `CookLoopBagTerm` does not inhabit. `leftover_width` is
   pairwise on `[t0,t1]`. The leftover_quad bag-sum is
   conserved (`leftover_quad_width ti tj = 1+1`).
2. Empty / Decline allocate no leftover split. ShareOne
   ignores leftover_width. MintTwo may increase hen
   cardinality while leftover_width of `[0,1]` stays 1.
3. I.8 one-step confluence does not flip `LoopDischarged`.
   Arc cook termination is a sister card.

Do **not** fake Discharge. Do **not** collapse I.8 into
bag-loop Discharge. Host CircGamma stays QEX.
`first_cook_scope` stays chord–chord. Does not remint
`I_ok_mixed` / CircGamma / leftover_width. Does not start
H⊥ / a CRV-TOUCH kiss procedure / Multi Landed / Phase B
done-when / SQL/MM cathedral. Does not reopen Status.

| Stop | Arm | Lemma |
|------|-----|-------|
| `Adr0007NodingEpic.v : ticket_0007_cook_term_qed_or_qex` | **QEX** — `LoopObligation`; `CookLoopBagTerm` missing; leftover_quad width conserved; pairwise split stays sibling QED | `SheetHenCookLoop.v : cook_loop_bag_term_missing`, `SheetHenCookLoop.v : leftover_quad_width_conserved` |
| `SheetHenCookLoop.v : ticket_0007_rho_gap_qed_or_qex` | **QEX** — named missing constructor + conserved bag-sum | `SheetHenCookLoop.v : leftover_quad_width_conserved` |
| `SheetHenCookLoop.v : ticket_0007_rho_cycles_qed_or_qex` | **QEX** — Empty / Decline mint nothing; ShareOne ignores width; MintTwo is not a width bound | `SheetHenCookLoop.v : no_hit_no_leftover_split`, `SheetHenCookLoop.v : mint_two_not_width_bound` |
| `SheetHenCookLoop.v : ticket_0007_rho_neq_pairwise_qed_or_qex` | **QED** — pairwise + one-step confluence hold; `cook_loop` stays obligation | `SheetHenCookLoop.v : pairwise_qed_not_bag_discharge` |
| `SheetHenCookLoop.v : ticket_0007_rho_scope_qed_or_qex` | **QEX** — leftover_quad is one Hit-split; arc term stays sister; first cook stays chord–chord | `SheetHenCookLoop.v : leftover_quad_is_one_hit`, `SheetHenCookLoop.v : arc_cook_term_is_sister` |

Witness: `0007-rho-bag-loop`. Status stays **Accepted**. Parks Γ / ι / ρ.

### Letter after Accept — NodingNG (chord) (2026-09-11)

North star: RelateNG + NodingNG + SQL/MM Part 3, non-big-OOP. This
letter is the **product face** for the Accepted chord lane: NodingNG
= `𝓘` + cook on one sheet. It packages `SheetHenCook` inhabitance —
it is not a remint of that vocabulary, not OverlayNG, not RelateNG,
not a DCEL kernel, and not a `Geometry` subclass.

**QED.** Two chord eggs on one sheet, an `𝓘` result, and one cook
step yield `NodedOnSheet` evidence. Empty ≠ Decline. Snap ≠ `𝓘`.
Identity is structural (`ShareOne` / `MintTwo`). A locked two-pair
bag (Hit cook + Empty no-mint) is still pairwise / one-step.

**QEX.** The full repeat-until-noded bag loop stays obligation.
Parks ρ — `CookLoopBagTerm` missing; leftover_quad width conserved.
Do not fake `LoopDischarged`. First cook stays chord–chord.
Shewchuk A–D / Hobby / Priest / Jordan are not dependencies.

Status stays **Accepted**. Parks Γ / ι / ρ.

| Stop | Arm | Lemma |
|------|-----|-------|
| `NodingNG.v : ticket_0007_nodingng_chord_qed_or_qex` | **QED** — chord `𝓘` + one cook step (or locked two-pair bag) yields `NodedOnSheet`; Empty ≠ Decline; snap ≠ `𝓘`; `ShareOne` / `MintTwo` structural | `NodingNG.v : nodingng_chord_inhabits`, `NodingNG.v : nodingng_crossing_hit_cooks`, `NodingNG.v : nodingng_locked_bag_inhabits` |
| `NodingNG.v : ticket_0007_nodingng_rho_qed_or_qex` | **QEX** — NodingNG chord is pairwise / one-step, not `LoopDischarged`; Parks ρ | `SheetHenCookLoop.v : cook_loop_bag_term_missing`, `SheetHenCookLoop.v : leftover_quad_width_conserved` |
| `NodingNG.v : ticket_0007_nodingng_scope_qed_or_qex` | **QEX** — first cook stays chord–chord; circular / clothoid stay out of scope | `SheetHenCook.v : first_cook_scope_chord_chord`, `SheetHenCook.v : circular_egg_not_first_cook_scope` |

Witness: `0007-nodingng-chord`. Status stays **Accepted**. Parks Γ / ι / ρ.

### Letter after Accept — OverlayNG (sheet) (2026-09-11)

North star: RelateNG + NodingNG + OverlayNG + SQL/MM Part 3, non-big-OOP.
This letter is the **product face** for Accepted OverlayNGRobust: OverlayNG
= a finite snap-sequence on one sheet. It packages `SheetHenCook`
inhabitance — it is not a remint of that vocabulary, not `𝓘`, not cook,
not NodingNG, not OverlayNGCurve Phase-0 point-set algebra (G1–G5),
not RelateNG, not Shewchuk A–D, not Hobby 4.1 Discharge, not Jordan,
not a DCEL kernel, and not a `Geometry` subclass.

**QED.** Snap maps `S → Λ` attempted until validate or give up inhabit
a finite snap-sequence ≠ `𝓘` on the same sheet as ℝ realization.
Hobby-shaped: `G` was already noded (`NodingNG.v : nodingng_crossing_noded`;
`SheetHenCook.v : noded_crossing`). Failure to validate is not
`𝓘` Decline and not Empty.

**QEX.** Full Hobby 4.1 “image stays noded” / unconditional overlay
correctness stay Honest remaining. Named missing constructor, not a
bool. Do not fake Hobby 4.1 Discharge.

Status stays **Accepted**. Parks Γ / ι / ρ.

| Stop | Arm | Lemma |
|------|-----|-------|
| `OverlayNG.v : ticket_0007_overlayng_sheet_qed_or_qex` | **QED** — finite snap-sequence ≠ `𝓘`; same-sheet realization; not NodingNG / OverlayNGCurve / RelateNG / Shewchuk / Jordan / DCEL | `OverlayNG.v : overlayng_sheet_inhabits`, `OverlayNG.v : overlayng_is_finite_snap`, `OverlayNG.v : overlayng_snap_neq_I`, `OverlayNG.v : overlayng_same_sheet_as_R` |
| `OverlayNG.v : ticket_0007_overlayng_assumes_noded_qed_or_qex` | **QED** — locked run assumes `NodingNG.v : nodingng_crossing_noded` on the same sheet; Hobby-shaped finite snap; not `𝓘` + cook | `OverlayNG.v : overlayng_assumes_noded_crossing`, `OverlayNG.v : overlayng_assumes_nodingng_face`, `OverlayNG.v : overlayng_locked_run_is_finite_snap`, `NodingNG.v : nodingng_crossing_noded` |
| `OverlayNG.v : ticket_0007_overlayng_hobby41_qed_or_qex` | **QEX** — Hobby 4.1 image-stays-noded / unconditional overlay correctness stay Honest remaining; do not fake Discharge | `OverlayNG.v : overlayng_hobby41_missing`, `OverlayNG.v : overlayng_unconditional_missing` |

Witness: `0007-overlayng-sheet`. Status stays **Accepted**. Parks Γ / ι / ρ.

### Letter after Accept — RelateNG (face) (2026-09-11)

North star: RelateNG + NodingNG + OverlayNG + SQL/MM Part 3, non-big-OOP.
This letter is the **product face** for Accepted DE-9IM / RelateNG
chord-lane facts. It packages existing lemmas by name — it is not a
remint of the RelateNG* / RelateNoding* zoo, not NodingNG, not OverlayNG
snap, not Shewchuk A–D / Hobby / Priest, not full unconditional Jordan,
not #522 leftover remint / T-junction wire complete /
`geom_de9im_pointset` nine-cell, not SQL/MM cathedral / Multi Landed,
not a DCEL kernel, and not a `Geometry` subclass.

**QED.** Matrix/witness surface (`im_unsupported_no_predicate`,
contains ↔ transpose within) + honesty decline
(`relate_unsupported_no_predicate`) + the locked 67-c parallel-unit
exterior-row pin on the same chords NodingNG Empty-noded
(`NodedOnSheet`). Triangle shared-edge touch and prepared-cache
short-circuit stay cited siblings.

**QEX.** Completeness is false; T-junction fill stays unsupported.
Full Jordan true-region, S15l+ multi-geom leftovers, and ticket 523
ISO `?` stay named missing constructors. `cell_none_iff_empty` is the
Coq emptiness side (Qed) — do not fake 523 closed. Do not mint `522-n`.

Status stays **Accepted**. Parks Γ / ι / ρ.

| Stop | Arm | Lemma |
|------|-----|-------|
| `RelateNGFace.v : ticket_0007_relateng_face_qed_or_qex` | **QED** — DE-9IM matrix/witness + honesty decline + 67-c line×line pin on NodingNG-noded chords; not NodingNG / OverlayNG snap / Shewchuk / DCEL | `RelateNGFace.v : relateng_face_inhabits`, `RelateNGFace.v : relateng_honesty_decline`, `RelateNGFace.v : relateng_locked_line_line_pin`, `RelateNGFace.v : relateng_consumes_nodingng` |
| `RelateNGFace.v : ticket_0007_relateng_complete_qed_or_qex` | **QEX** — completeness false; T-junction fill stays `im_unsupported`; do not mint `522-n` | `RelateNGComplete.v : triangle_pair_regime_ccw_incomplete`, `RelateNGDisjoint.v : relate_tjunction_pair_no_predicate` |
| `RelateNGFace.v : ticket_0007_relateng_parks_qed_or_qex` | **QEX** — full Jordan true-region, S15l+ multi-geom, ticket 523 ISO `?`; `cell_none_iff_empty` stays Coq emptiness | `RelateNGFace.v : relateng_jordan_true_region_missing`, `RelateCurveAlphabet.v : question_mark_not_iso_result`, `RelateCurveMatrix.v : cell_none_iff_empty` |

Witness: `0007-relateng-face`. Status stays **Accepted**. Parks Γ / ι / ρ.

### Letter after Accept — IEEE↔R oracle bridge (2026-09-11)

North star: NodingNG / OverlayNG / RelateNG product faces + SQL/MM
Part 3, non-big-OOP. This letter is the **product face** for the
two-way IEEE binary64 ↔ ℝ bridge the Oracle (ADR-0006 Accepted line
protocol) uses to generate tests against those faces. It packages
existing bridges — `SheetHenCook.CoordRealization` /
`binary64_same_sheet_as_R` / `coord_realization_preserves_sheet`,
`Validate_binary64_bridge.B2R_bp` / `map_B2R_bp`, `B64_bridge` /
`B64_lib` round-trip helpers, `Orient_b64_exact.coord_int_safe` —
and does not remint them.

**QED.** IEEE→ℝ (`B2R` / `B2R_bp`) then `round` is identity; ℝ→IEEE
(`ieee_of_Z` / `binary_normalize`) recovers `IZR` on the integer
window (`|m| ≤ 2⁵³` finite, `|m| ≤ 2²⁵` int-safe). Same sheet as ℝ
realization. Bridge ≠ `𝓘` / ≠ cook / ≠ OverlayNG snap. Locked
NodingNG Hit (unit-square diagonals) and RelateNG 67-c parallel
chords decode.

**QEX.** Full FP noder; unrestricted round-trip outside the safe
regime; kiss on the binary64 sheet. Honest remaining. Named missing
constructors, not bools. Do not fake Discharge. Shewchuk A–D /
Hobby / full Jordan stay off the critical path.

Oracle generators attach as adapters on existing keywords
(`INTERSECT_FILTERED`, `INTERSECT_POINT_XY`, `OVERLAY_UNIFIED`,
`ORIENT`). No new keyword. No second seam. ADR-0006 Status stays
**Accepted**. ADR-0007 Status stays **Accepted**. Parks Γ / ι / ρ.

| Stop | Arm | Lemma |
|------|-----|-------|
| `IeeeRBridge.v : ticket_0007_ieee_bridge_qed_or_qex` | **QED** — two-way B2R/round inhabitant; same-sheet realization; ≠ cook / ≠ `𝓘` / ≠ OverlayNG snap; NodingNG Hit + 67-c points decode | `IeeeRBridge.v : ieee_bridge_inhabits`, `IeeeRBridge.v : ieee_to_R_round_id`, `IeeeRBridge.v : ieee_of_Z_B2R`, `IeeeRBridge.v : ieee_same_sheet_as_R` |
| `IeeeRBridge.v : ticket_0007_ieee_bridge_fp_noder_qed_or_qex` | **QEX** — full FP noder stays Honest remaining; bridge is not a cook | `IeeeRBridge.v : ieee_fp_noder_missing`, `IeeeRBridge.v : ieee_bridge_neq_cook` |
| `IeeeRBridge.v : ticket_0007_ieee_bridge_unrestricted_qed_or_qex` | **QEX** — unrestricted round-trip and kiss on the binary64 sheet stay Honest remaining | `IeeeRBridge.v : ieee_unrestricted_missing`, `IeeeRBridge.v : ieee_kiss_on_b64_missing` |

Witness: `0007-ieee-oracle-bridge`. Status stays **Accepted**. Parks Γ / ι / ρ.

### Letter after Accept — clothoid egg sidecar (2026-09-11)

Cook-axis sidecar: clothoid as an EggClass on the ADR-0007 vocabulary.
Host already has `EggClothoid` / `MkOutOfScope EggClothoid`,
`clothoid_clothoid_not_first_scope`, `clothoid_decline_I_ok`. Prefer
`SidecarClothoid*` over reminting host cook. Existing clothoid corpus
is metric / relate / buffer research — package what is already Qed;
do not remint Fresnel / Halley as noding. One locked fixture. Do not
ship Campaign I–II.

**QED.** Sidecar egg packaging + host Decline + locked unit-square
chord-seed reuse (`RelateClothoid.v : clothoid_chord_proper_cross_share`).
Demote-to-chord is NodingNG / host first cook, not a clothoid Hit.

**QEX.** Clothoid×clothoid is not first cook (checklist 4). Named
missing constructors: no `MkClothoid` on `Egg`; no `I_ok` Hit arm.
Do not fake first-cook expand or `LoopDischarged`. Parks Γ / ι / ρ
cited once.

Status stays **Accepted**. ADR-0006 Status stays **Accepted**.

| Stop | Arm | Lemma |
|------|-----|-------|
| `SidecarClothoidEgg.v : ticket_0007_clothoid_egg_qed_or_qex` | **QED** — EggClothoid packaging; host Decline; locked chord-seed; demote is NodingNG first cook | `SidecarClothoidEgg.v : sidecar_clothoid_egg_inhabits`, `SidecarClothoidEgg.v : sidecar_clothoid_chord_seed`, `SidecarClothoidEgg.v : sidecar_clothoid_host_decline` |
| `SidecarClothoidEgg.v : ticket_0007_clothoid_not_first_cook_qed_or_qex` | **QEX** — clothoid×clothoid stays out of first cook; `MkClothoid` / Hit-arm missing | `SheetHenCook.v : clothoid_clothoid_not_first_scope`, `SidecarClothoidEgg.v : sidecar_clothoid_mkclothoid_missing`, `SidecarClothoidEgg.v : sidecar_clothoid_hit_arm_missing` |
| `SidecarClothoidEgg.v : ticket_0007_clothoid_parks_qed_or_qex` | **QEX** — Campaign I–II / Fresnel-as-noding / bag loop parked; Parks Γ / ι / ρ | `SidecarClothoidEgg.v : sidecar_clothoid_letter_is_landed`, `SheetHenCook.v : cook_loop_is_obligation` |

Witness: `0007-clothoid-egg`. Status stays **Accepted**. Parks Γ / ι / ρ.

### Letter after Accept — ι interior Hit discharge (2026-09-11)

Parks ι (#707 @ `1dbc2c2`) already landed as **QEX**: sidecar
`I_ok_mixed` Hit is gated by `mixed_joint_params`; the
interior-params arm does not inhabit
(`SidecarCircInterior.v : interior_mixed_hit_arm_missing`).
That gate is the μ joint story. This letter does **not** remint
`I_ok_mixed`, drop the joint gate, remint CircGamma, or expand
host `I_ok` / `first_cook_scope`.

**QED.** A distinct sidecar predicate `I_ok_interior` packages
the already-named `I_ok_mixed_interior_arm`
(`valid_arc ∧ on_chord ∧ on_arc_gamma ∧ interior_span_params`).
Locked MixLsCs / MixCsLs inhabit Hit on Campaign II
`span_arc_A` × a horizontal chord through `p+`
(`SidecarCircInteriorHit.v : locked_interior_I_ok_interior`).
That Hit does not inhabit `I_ok_mixed`. μ still inhabits
`I_ok_mixed` and is not interior.

**QEX.** Host CircGamma stays QEX. First cook stays chord–chord.
Host mixed `I_ok` is Decline. Host interior cook / H⊥ / bag
noder / SQL/MM cathedral stay parked. `I_ok_mixed` still has
no interior-params arm.

Status stays **Accepted**. ADR-0006 Status stays **Accepted**.
Parks Γ / ι / ρ cited once; the ι row records this progress.

| Stop | Arm | Lemma |
|------|-----|-------|
| `SidecarCircInteriorHit.v : ticket_0007_iota_interior_hit_qed_or_qex` | **QED** — locked MixLsCs / MixCsLs inhabit `I_ok_interior` at `interior_span_params`; packages the named interior arm | `SidecarCircInteriorHit.v : locked_interior_I_ok_interior`, `SidecarCircInteriorHit.v : locked_interior_rev_I_ok_interior` |
| `SidecarCircInteriorHit.v : ticket_0007_iota_interior_not_mixed_qed_or_qex` | **QED** — `I_ok_interior` Hit is not `I_ok_mixed`; `mixed_joint_params` gate stands; μ is not interior | `SidecarCircInteriorHit.v : locked_interior_not_I_ok_mixed`, `SidecarCircInterior.v : interior_mixed_hit_arm_missing` |
| `SidecarCircInteriorHit.v : ticket_0007_iota_interior_host_qed_or_qex` | **QEX** — CircGamma stays QEX; first cook stays chord–chord; host mixed `I_ok` Decline; host interior cook parked | `CircularCook.v : circular_gamma_is_qex`, `SheetHenCook.v : first_cook_scope_chord_chord` |
| `SidecarCircInteriorHit.v : ticket_0007_iota_interior_park_qed_or_qex` | **QEX** — host interior cook / H⊥ / bag noder / cathedral parked; Phase B Open; letter landed ≠ host cook Landed | `SidecarCircInteriorHit.v : iota_interior_hit_letter_is_landed`, `SidecarCircInterior.v : iota_interior_cook_is_parked` |

Witness: `0007-iota-interior-discharge`. Status stays **Accepted**. Parks Γ / ι / ρ.

### Letter after Accept — NURBS egg sidecar (2026-09-11)

Cook-axis sidecar: NURBS as an EggClass on the ADR-0007 vocabulary.
Host already has `EggNurbs` / `MkOutOfScope EggNurbs`. This letter
adds the missing Decline / not-first-cook host lemmas
(`nurbs_nurbs_not_first_scope`, `nurbs_decline_I_ok`) and packages
them. Prefer `SidecarNurbs*` over reminting host cook. Existing
NURBS corpus is metric / length research — package what is already
Qed; do not remint #508 length / Cox-de-Boor as noding. One locked
fixture. Do not ship a NURBS×NURBS noder or Campaign I–II.

**QED.** Sidecar egg packaging + host Decline + locked unit-square
demoted-chord seed (`RelateLineLine.v : line_line_proper_cross_geom`).
Demote-to-chord is NodingNG / host first cook, not a NURBS Hit.
Golden quarter stays a metric cite.

**QEX.** NURBS×NURBS is not first cook (checklist 4). Named
missing constructors: no `MkNurbs` on `Egg`; no `I_ok` Hit arm.
Do not fake first-cook expand or `LoopDischarged`. Parks Γ / ι / ρ
cited once (ι row already records #717 discharge).

Status stays **Accepted**. ADR-0006 Status stays **Accepted**.

| Stop | Arm | Lemma |
|------|-----|-------|
| `SidecarNurbsEgg.v : ticket_0007_nurbs_egg_qed_or_qex` | **QED** — EggNurbs packaging; host Decline; locked demoted-chord seed; demote is NodingNG first cook; length stays metric | `SidecarNurbsEgg.v : sidecar_nurbs_egg_inhabits`, `SidecarNurbsEgg.v : sidecar_nurbs_chord_seed`, `SidecarNurbsEgg.v : sidecar_nurbs_host_decline` |
| `SidecarNurbsEgg.v : ticket_0007_nurbs_not_first_cook_qed_or_qex` | **QEX** — NURBS×NURBS stays out of first cook; `MkNurbs` / Hit-arm missing | `SheetHenCook.v : nurbs_nurbs_not_first_scope`, `SidecarNurbsEgg.v : sidecar_nurbs_mknurbs_missing`, `SidecarNurbsEgg.v : sidecar_nurbs_hit_arm_missing` |
| `SidecarNurbsEgg.v : ticket_0007_nurbs_parks_qed_or_qex` | **QEX** — Campaign I–II / length-as-noding / Cox-de-Boor / bag loop parked; Parks Γ / ι / ρ | `SidecarNurbsEgg.v : sidecar_nurbs_letter_is_landed`, `SheetHenCook.v : cook_loop_is_obligation` |

Witness: `0007-nurbs-egg`. Status stays **Accepted**. Parks Γ / ι / ρ.
