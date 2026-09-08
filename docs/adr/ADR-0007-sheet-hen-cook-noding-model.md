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
RocqRefRunner dispatch). A later keyword, if one is ever wanted, attaches
as an Oracle adapter (ADR-0006 Decision 1–2: line protocol + own
compilation unit + driver print) — never as FFI or RocqRefRunner.
ADR-0006's Related subsection points back here. Both sides of the
cross-link are the coupling. Status of ADR-0006 stays Accepted.

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
| — | Bag-level cook loop (term / confl on a leftover bag) | `Adr0007NodingEpic.v : ticket_0007_cook_term_qed_or_qex` | **QEX** — documented CRV-TOUCH / `𝓘`-family deferral, not a named soft gap | `SheetHenCook.v : cook_loop_is_obligation` |
| — | binary64 / OverlayNGRobust sit on one sheet | `Adr0007NodingEpic.v : ticket_0007_sheet_realiz_qed_or_qex` | **QED** — realization preserves `S`; OverlayNGRobust is a finite snap-sequence, not `𝓘` | `SheetHenCook.v : coord_realization_preserves_sheet`, `SheetHenCook.v : overlay_ng_robust_is_finite_snap_holds`, `SheetHenCook.v : overlay_ng_robust_is_snap_not_I` |
| — | `ddir` migration is one type equation | `Adr0007NodingEpic.v : ticket_0007_chicken_dart_qed_or_qex` | **QED** — `DdirDart` := `(Hen * Hen)` = chicken ends; CoordDart stays the `Dart.v` coordinate-pair story; no third type | `SheetHenCook.v : ddir_migration_one_equation` |
| — | Full-circle Hit carries constructed `(h*, p*, tᵢ, tⱼ)` | `CircularCookHit.v : ticket_64_circ_hit_params_qed_or_qex` | **QED** — locked `(0,0)/(7,0)` r=5; `γ(t)=p*` | `CircularCookHit.v : locked_I_circles_gamma_hit`, `CircularCookHit.v : locked_hit_plus_on_gamma` |
| — | CircularArc γ / CircGamma | `CircularCook.v : ticket_64_circ_gamma_qed_or_qex` | **QEX** — 3-axiom host has no atan2-free interpolant; do not fake Discharge | `CircularCook.v : circular_gamma_is_qex` |
| — | Span-restricted γ on CircularArc | `CircularCookSpan.v : circular_arc_gamma_constructed` | **QED** — principal-span interpolant; locked proper arcs keep `p+`, reject `p−` | `CircularCookSpan.v : locked_span_gamma_hit`, `CircularCookSpan.v : arc_gamma_retract` |
| — | Host circular IHit → `try_cook_hit` | `Adr0007NodingEpic.v : ticket_0007_circ_host_cook_qed_or_qex` | **QEX** — circular eggs stay `MkOutOfScope`; host cook declines even on IHit | `SheetHenCook.v : try_cook_hit_circular_hit_none`, `SheetHenCook.v : circular_egg_not_first_cook_scope` |
| — | Circular Hit feeds sidecar `split(t)` | `CircularCookSplit.v : ticket_0007_circ_cook_step_qed_or_qex` | **QED** — locked plus-root leftovers meet at `p+`; CircGamma stays QEX | `CircularCookSplit.v : cooked_circ_plus_try`, `CircularCookSplit.v : cooked_circ_plus_ok` |
| — | Circular Touch / Empty / Decline cook | `CircularCookSplit.v : ticket_0007_circ_cook_scope_qed_or_qex` | **QEX** — kiss is a fenced scope arm, not a CRV-TOUCH procedure | `CircularCookSplit.v : locked_circ_touch_none` |

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

**Decision:** Accepted by Joost (BDFL). Vocabulary law for CRV-TOUCH / RGR. Soft gaps (a)(b)(c) closed as checklist rows. Honest remaining opens (FP noder, Hobby, bag loop, kiss) stay open and do not reopen Status.

## Ready for BDFL (historical, 2026-09-07)

**Accepted** 2026-09-07. This section is retained as the Accept memo archive.
QEX is not acceptance. Supporting shapes are not a noder.

**Joost brief (soft gaps, 2026-09-07).** Former soft gaps (a)(b)(c) are
closed checklist rows: pairwise chord-split finiteness plus one-step
confluence is QED; binary64 / OverlayNGRobust sit on one sheet is QED;
`DdirDart` := `(Hen * Hen)` = chicken ends is QED. The bag-level cook
loop is a documented CRV-TOUCH / `𝓘`-family QEX under Honest remaining
opens, not a named soft gap. **Accepted** by Joost (BDFL) 2026-09-07.

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
| (a) Cook termination / confluence on the chord lane | `ticket_0007_pairwise_split_qed_or_qex` | **QED** — pairwise leftover-width split is finite; one Hit-split is confluent | Host-lane close. The bag loop is `ticket_0007_cook_term_qed_or_qex` **QEX** (CRV-TOUCH / `𝓘`-family), listed under Honest remaining opens — not a soft gap |
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
- The repeat-until-noded **bag** loop (termination + confluence) on the chord lane — `ticket_0007_cook_term_qed_or_qex` QEX / CRV-TOUCH. Pairwise width decrease and one-step confluence are discharged QED, not this item. **Arc** cook termination is a sister card, not this Accept.
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
`CircularCookSpan.v : locked_span_gamma_hit`). Host CircGamma stays
QEX (`CircularCook.v : ticket_64_circ_gamma_qed_or_qex`;
`CircularCook.v : circular_gamma_is_qex`) — remaining obligation is
an atan2-free interpolant on the 3-axiom host.
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

Witness: `0007-cook-split`. Status stays **Accepted**. Not a remint of leftover-width / pairwise_split. Host CircGamma stays QEX.

### Letter after Accept — constructed 𝓘 from proper-cross signs (2026-09-07)

The Decision's `𝓘` is not a hardcoded midpoint. Proper-cross sign
conditions license `Intersect.strict_intersection_point` as `p*` plus
the two open-interval parameters. That constructed Hit recovers the
unit-square witness and cooks. Missing signs do not license the
formula (they are not Decline). Equal constructed `p*` under operand
swap licenses `ShareOne` — the identity basis, not `dart_eq_dec`.
Not a remint of `Intersect`. Not a total `𝓘`. Not the noder loop.
Does not reopen Status. Host CircGamma stays QEX.

| Stop | Arm | Lemma |
|------|-----|-------|
| `Adr0007NodingEpic.v : ticket_0007_constructed_I_qed_or_qex` | **QED** — signs on the unit-square diagonals produce the same Hit the cook already splits | `SheetHenCook.v : constructed_hit_I_ok`, `SheetHenCook.v : constructed_hit_crossing_eq`, `SheetHenCook.v : cooked_constructed_crossing` |
| `Adr0007NodingEpic.v : ticket_0007_constructed_I_scope_qed_or_qex` | **QEX** — disjoint horizontals have no proper-cross signs; Empty stays Empty | `SheetHenCook.v : disjoint_not_proper_cross`, `SheetHenCook.v : disjoint_I_ok` |
| `Adr0007NodingEpic.v : ticket_0007_share_constructed_qed_or_qex` | **QED** — operand swap names the same `p*`; `ShareOne` follows | `SheetHenCook.v : constructed_hit_sym_same_p`, `SheetHenCook.v : equal_constructed_p_share` |

Witness: `0007-constructed-I`. Status stays **Accepted**.

### Letter after Accept — circular Hit → cook bridge (2026-09-08)

#666 closed chord–chord constructed Hit → cook `split(t)`. The circular
side already had `I_circles_z` / `I_CIRCULAR`, constructed
`(h*, p*, tᵢ, tⱼ)` on locked discs, and principal-span γ. This letter
feeds that circular Hit into a same-shape cook step — leftovers via
`circ_gamma` `split(t)`, incidence on the Hit's hen — without faking
atan2-free host γ and without expanding first cook scope.

The *host* cook (`try_cook_hit`) still declines circular eggs: they
remain `MkOutOfScope`. CircGamma stays QEX. Touch / kiss is a fenced
QEX arm, not a CRV-TOUCH kiss decision. Not a remint of
`ArcSplitAtNode`. Does not reopen Status.

| Stop | Arm | Lemma |
|------|-----|-------|
| `Adr0007NodingEpic.v : ticket_0007_circ_host_cook_qed_or_qex` | **QEX** — circular IHit does not feed host `try_cook_hit` | `SheetHenCook.v : try_cook_hit_circular_hit_none` |
| `CircularCookSplit.v : ticket_0007_circ_split_qed_or_qex` | **QED** — locked plus-root leftovers meet at `p+` | `CircularCookSplit.v : circ_split_join`, `CircularCookHit.v : locked_hit_plus_on_gamma` |
| `CircularCookSplit.v : ticket_0007_circ_cook_step_qed_or_qex` | **QED** — `I_circles_gamma` Hit cooks; CircGamma stays QEX | `CircularCookSplit.v : cooked_circ_plus_try`, `CircularCookSplit.v : cooked_circ_plus_ok` |
| `CircularCookSplit.v : ticket_0007_circ_cook_scope_qed_or_qex` | **QEX** — Touch / Empty / Decline allocate no hen | `CircularCookSplit.v : locked_circ_touch_none` |

Witness: `0007-circ-cook`. Status stays **Accepted**. Host CircGamma stays QEX.
