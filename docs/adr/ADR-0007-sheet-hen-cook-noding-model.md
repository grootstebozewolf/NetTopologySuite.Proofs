# ADR-0007 — The noding constructor is part of the specification: sheet, hen, cook

| Field | Value |
|---------------|--------------------------------------------------------------|
| **Order** | ADR-0007 |
| **Status** | **Proposed** — supporting shapes landed; Ready for BDFL |
| **Deciders** | Joost (BDFL); proposed by Jeroen Bloemscheer |
| **Date** | 2026-09-05 |
| **Superseded by** | — (none) |

Status lifecycle: *Proposed → Accepted / Rejected → (possibly) Superseded*.

QEX is not acceptance. These supporting shapes do not close the ADR.

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
QEX is not BDFL accept. **Status stays Proposed.**

Modules: `theories/SheetHenCook.v` (sheet / hen / egg / chicken / `𝓘` /
first-cook scope) and `theories/Adr0007NodingEpic.v` (ticket stops).
Registered in `_CoqProject` (host / pure-R / Stdlib lane).

**ADR-0006 coupling.** Testable `𝓘` / cook results sit on the accepted
Oracle line protocol (`docs/adr/ADR-0006-oracle-protocol-is-the-test-surface.md`).
This cut mints no keyword and no second external seam (no FFI pin, no
RocqRefRunner dispatch). A later keyword, if one is ever wanted, attaches
as an Oracle adapter (ADR-0006 Decision 1–2: line protocol + own
compilation unit + driver print) — never as FFI or RocqRefRunner.
Comment + this cross-link is the coupling.

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
| — | Cook termination / confluence on the chord lane | `Adr0007NodingEpic.v : ticket_0007_cook_term_qed_or_qex` | **QEX** — pairwise interior split is finite; the bag loop stays an `𝓘`-family obligation | `SheetHenCook.v : interior_split_finite_holds`, `SheetHenCook.v : cook_loop_is_obligation` |

Snap-rounding is a different constructor (`SheetHenCook.v : snap_round_neq_I`).
Display is a view (`DisplayView`), not a kernel store.

### Dart := hen-id pair (chicken view)

A later remint reseats `Dart` as a hen-id pair `(h_src, h_dst)` — one
view of a chicken, not a third type. `DartAngularOrder.ddir` then reads
`γ'` from the chicken's egg. Orbit / `next` / face proofs consume
`dart_eq_dec` as *a* decidable equality and never inspect coordinates
(`DartFace.v`, `DartNextInjective.v`, `DartNextRemove.v`); they do not
remint. Local `HenIdDart` (`SheetHenCook.v : hen_id_dart_of_chicken`)
is that view; it is not a remint of `Dart.v:50`. Reviewers of
`ddir` should not invent a third directed-edge type.

### binary64 and OverlayNGRobust sit on a sheet

Points of `S` are affine. The working number type — ℝ in the host lane,
binary64 / Flocq in `theories-flocq/` — is a *coordinate realization* of
those points (`SheetHenCook.v : CoordRealization`,
`SheetHenCook.v : coord_realization_preserves_sheet`). Changing the
number type does not change the sheet origin or basis. A binary64 noder
is `𝓘` realized in that number type on one sheet; it is not a second
sheet and is not discharged here.

OverlayNGRobust is a finite sequence of snap maps `S → Λ` attempted
until noded `G` validates or the process throws. Each attempt is
Hobby-shaped: it assumes `G` was already noded. It is not `𝓘`
(`SheetHenCook.v : overlay_ng_robust_is_snap_not_I`). Failure to
validate is not `𝓘` Decline and not Empty.

WITNESS topic: overlay · claimId: 0007 · witness: 0007-qed-qex · board: ADR-0007

---

## Ready for BDFL (2026-09-07)

Status stays **Proposed**. This section is the Accept / Reject memo.
QEX is not acceptance. Supporting shapes are not a noder.

### Four prior review conditions — discharged

| # | Condition | Stop | Arm |
|---|-----------|------|-----|
| 1 | Identity policy sketch (structural hen minting) | `ticket_0007_identity_qed_or_qex` | **QED** — `ShareOne` |
| 1b | Numeric `dart_eq_dec` is not vertex identity | `ticket_0007_dart_eq_qed_or_qex` | **QEX** |
| 2 | Minimal chord–chord `𝓘` | `ticket_0007_chord_chord_qed_or_qex` | **QED** — Hit / Empty / never Decline in scope |
| 3 | Cross-link accepted ADR-0006 | module headers + coupling paragraph | Oracle line protocol only; later keyword = adapter, not FFI / RocqRefRunner |
| 4 | First cook scope = chord–chord only | `ticket_0007_qed_or_qex` | **QEX** on clothoid–clothoid |

### Soft gaps this cut names

| Soft gap | Where |
|----------|-------|
| (a) Cook termination / confluence as an explicit chord-lane obligation | `ticket_0007_cook_term_qed_or_qex` — pairwise split finite (QED lemma); bag loop remains an `𝓘`-family obligation (QEX) |
| (b) How binary64 / OverlayNGRobust sit on a sheet | paragraph above + `coord_realization_preserves_sheet` / `overlay_ng_robust_is_snap_not_I` |
| (c) Chicken vs Dart so `ddir` reviewers do not invent three types | paragraph above: `Dart` := hen-id pair = chicken view |
| (d) This memo | this section |

### Honest remaining opens (Accept does not close these)

- Identity policy detail beyond `ShareOne` / `MintTwo` (which `𝓘` decides, on what basis).
- A binary64 / floating-point noder (`𝓘` realized in Flocq). Not a second sheet.
- Hobby 4.1 / 4.3. Snap-rounding stays a different constructor under already-noded `G`.
- The repeat-until-noded bag loop (termination + confluence). Pairwise width decrease is not that discharge.
- Later constructive rungs (one Hit `split(t)` step; constructed `𝓘` from proper-cross signs) are letters after Accept, not Accept blockers.

### Decision requested

**Accept** ADR-0007 as the specification of the noding constructor
(sheet / hen / egg / chicken / cook / `𝓘`) with first cook scope
chord–chord, Empty ≠ Decline, identity structural, testable results on
the ADR-0006 Oracle line protocol.

**Reject** if the constructor-in-the-specification frame is wrong, if
first cook scope must be wider than chord–chord, or if identity must
be numeric rather than structural.

Do not flip the Status line except by this decision.
