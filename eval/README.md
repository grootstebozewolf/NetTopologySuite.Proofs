# nts-eval micro units

Self-contained Rocq units for the `nts-eval` micro-kernel harness.

Each file embeds a `(* WITNESS {"claimId":"…", …} *)` marker so static
matching can bind the formal lemma to the claim id without loading the full
`_CoqProject.full` dependency cone.

| claimId | topic | File | Lemma |
|--------:|-------|------|-------|
| `65-a` | `buffer` | [`Claim65a.v`](Claim65a.v) | `flat_endcap_is_diameter_segment` |
| `65-b` | `buffer` | [`Claim65b.v`](Claim65b.v) | `round_endcap_is_forward_semicircle` |
| `65-c` | `buffer` | [`Claim65c.v`](Claim65c.v) | `offset_artifacts_within_envelope` **ABORTED** |
| `65-d` | `buffer` | [`Claim65d.v`](Claim65d.v) | `miter_clipped_at_limit_distance` |
| `65-e` | `buffer` | [`Claim65e.v`](Claim65e.v) | `square_endcap_is_diameter_square` |
| `67-a` | `relate` | [`Claim67a.v`](Claim67a.v) | `unit_square_self_relate_de9im_eq` |
| `67-b` | `relate` | [`Claim67b.v`](Claim67b.v) | `boundary_op_eq_relateng_boundary_graph` |
| `68-a` | `mesh` | [`Claim68a.v`](Claim68a.v) | `delaunay_edge_iff_empty_circumcircle` |
| `69-a` | `oracle` | [`Claim69a.v`](Claim69a.v) | `w1_w5_coverage_table_complete` |
| `423-a` | `metric` | [`Claim423a.v`](Claim423a.v) | `directed_discrete_hausdorff_max_min` |
| `423-b` | `metric` | [`Claim423b.v`](Claim423b.v) | `discrete_frechet_min_coupling` |
| `424-a` | `hull` | [`Claim424a.v`](Claim424a.v) | `minimum_bounding_triangle_exists` |
| `425-a` | `coverage` | [`Claim425a.v`](Claim425a.v) | `coverage_gap_overlap_cleaner_valid` |
| `9004-c` | `construct` | [`Claim9004c.v`](Claim9004c.v) | `mic_unit_square` |
| `9004-d` | `construct` | [`Claim9004d.v`](Claim9004d.v) | `cell_achievable_radius_bound` |
| `9005-a` | `teaching` | [`Claim9005a.v`](Claim9005a.v) | `pia_triangle_three_touch` |
| `64-i-circular` | `core` | [`Claim64iCircular.v`](Claim64iCircular.v) | `locked_I_circles_z_hit` |
| `64-circ-z-partition` | `core` | [`Claim64circZPartition.v`](Claim64circZPartition.v) | `I_circles_z_hit_iff` |

Production home for 65-a (Green/Qed: full biconditional — flat endcap =
perpendicular diameter segment `p ± r·J(t)`, with the rational witness pins
and the two mismatch probes): `theories/BufferEndcapDiameter.v` (same
WITNESS tag; sqrt-free `m = vmag ein` normaliser). The unit here carries
the self-contained m = 1 proof plus the pins.

Production home for 65-b (Green/Qed: full biconditional — round endcap =
forward semicircle, the frame image of the unit half-circle
`q = E + d·(a·unit_perp + b·unit_dir)`, `a² + b² = 1`, `b ≥ 0`, plus the
signed apex pin and the diameter-endpoint seam pins):
`theories/BufferEndcapSemicircle.v` (same WITNESS tag). The unit here
carries the self-contained unit-tangent proof plus the pins.

**65-c is ABORTED (disproven), not Green.** The naive claim that every raw
offset-graph artifact of `G` at distance `d` (mitre joins included) lies
inside `Envelope(G).expandBy(d)` is refuted by the rational sharp corner
`(0,0)→(1,0)→(1/2,1/10)`, `d = 1`, default `mitreLimit = 5`: the mitre
apex has `x = −4 − 10·|eout| < −4 < −1` (strictly left of the expanded
box), and even the limit radius `L·d = 5` exceeds the box's max reach
about the corner (`dist_sq ≤ 4 + (11/10)² < 25`). No production repair;
the positive theorem is `Abort`ed and
`offset_artifacts_within_envelope_aborted` is Qed. Round-join-only
variants remain bounded; the general claim does not hold.

Production home for 65-d (Green/Qed: when unrestricted `miter_apex`
overshoots the limit sphere of radius `L·d`, `L ≥ 1`, the ray-scale
`limited_miter_apex` is at squared distance `(L·d)²` and on the segment
from the corner through the unrestricted apex):
`theories/BufferMiterClip.v` (same WITNESS tag; core `ray_scale_to_radius`).
The unit here carries the self-contained proof plus the rational
right-angle witness pins. (Board plan text said “65-b”; that id is already
Green as round endcap.)

Production home for 65-e (Green/Qed: full biconditional — square endcap
= U-shaped boundary of the forward square on the flat diameter, three
segment equivalences over the trio's shared J(t)-frame, all linear, plus
the both-corners signed forward pin and the corpus sq_corner bridge):
`theories/BufferEndcapSquare.v` (same WITNESS tag). The unit here
carries the self-contained unit-tangent proof plus the pins.

Production home for 67-a (Green/Qed: classical strata + rational unit-square
self-relate / OGC equal DE-9IM): `theories/RelateNGMatrixEqual.v` (same WITNESS tag).

Production home for 67-b (Green/Qed: rectangle core + rational unit-square
witness): `theories/RelateNGBoundaryGraph.v` (same WITNESS tag).

Production home for 67-c (Green/Qed: no-share line×line exterior-row
true-dim IE=1 / EI=1 / BE=0 / EB=0 / EE=2 on parallel unit segments):
`theories/RelateNodingLineLineExtPinned.v` (WITNESS 67-c, topic: relate).
No eval mirror; the theory is the pin. Chunk S15l; leftovers stay S15l+.

Production home for 68-a (full witness cluster, shared helpers):
`theories/DelaunayEdgeEmptyCircle.v` (also tagged with the same WITNESS).

Production home for 69-a (Green/Qed by TABLE REPAIR: the SQL/MM + SFA
oracle-mode checklist W1–W5 closes over the repaired table — is_ring =
closed AND no_pinch as witness obligations, the mis-tabled
"closed ⇒ pinch-free" row and its pinched-ring refutation kept Qed as
hardening): `theories/OracleCurveChecklist.v` (same WITNESS tag).

Production home for 423-a (Green/Qed: directed discrete Hausdorff =
attained max-min — cover + attain spec on nonempty lists, four Rmin/Rmax
list inductions, plus nonnegativity): `theories/HausdorffDiscrete.v`
(same WITNESS tag). The unit here carries the self-contained version
plus the rational pins (pair example 1/1; asymmetric 4/9 direction
killers).

Production home for 423-b (Green/Qed: discrete Fréchet = min over
monotone couplings of the max leash — lower bound by induction on the
coupling derivation, attainment by nested list induction constructing
the optimal two-frogs walk, plus nonnegativity):
`theories/FrechetDiscrete.v` (same WITNESS tag). The unit here carries
the self-contained version plus the rational pins (identical 0 with the
diagonal coupling exhibited; reversal 9; crossing pairing refuted;
Fréchet 9 > Hausdorff 4 on the 423-a witness).

Production home for 425-a (Green/Qed: witness-scoped cleaner soundness —
3-cell open-interior-disjoint partition of the rational two-cell overlap
coverage, same-union up to boundary null sets):
`theories/CoverageGapOverlapCleaner.v` (same WITNESS tag).

Production home for 424-a (Green/Qed: witness-scoped existence of a
bounding triangle of the unit-square vertices with Euclidean area 2,
candidate T₀ = △(0,0)(2,0)(0,2)): `theories/MinimumBoundingTriangle.v`
(same WITNESS tag). Universal ∀-finite-P existence and unrestricted
area lower bound deferred.

Production home for 424-b (Green/Qed: H-CV exact extrema — CIRCLE_5
cardinals on-circle, upper semicircle keeps north / rejects south,
disc + single-arc are the PR #8 CurveExact cell, CompoundCurve is not):
`theories/HullExactExtrema.v` (WITNESS 424-b, topic: hull). No eval
mirror; the theory is the pin. H-CC leftover stays JTS #6.

Production home for 9004-c (Green/Qed: the disk centre (1/2,1/2), radius
1/2 is a maximum inscribed disk of [0,1]² — containment plus the
maximiser over ALL centres and radii, via the horizontal probe points
(ox' ± r', oy')): `theories/MaximumInscribedCircle.v` (same WITNESS tag;
board #9004 / epic #813, Zhai et al. 2026 "Polycenter"). The unit here
carries the self-contained proof, the four side-midpoint on-circle pins,
and the two mismatch probes (same radius off-centre escapes the left
wall; radius 3/5 has no admissible centre). Polycenter cell subdivision
and the achievable-radius bound (9004-d) deferred.

Production home for 64-i-circular (integer circle–circle discriminant +
hen mint; locked Hit 0 1; kiss is Touch): `theories/CircularCookZ.v`.
Oracle `I_CIRCULAR`.

Production home for 64-circ-z-partition (Hit ↔ `|r1−r2|² < d² < (r1+r2)²`
on positive radii; Empty / Touch / Decline against the same squared
tests; locked internal kiss `(0,0)` r=5 vs `(3,0)` r=2 is Touch):
`theories/CircularCookZ.v`. Oracle `I_CIRCULAR` takes integer tokens.
I.9 (`0007-I.9-classifier-neq-cook`) tickets that a Z Hit is tags
0/1 and is not a cook license: `theories/CircularCookLicense.v`.

Production home for 64-circ-hit-params (full-circle γ : [0,1] → S;
locked Hit carries constructed `(h*, p*, tᵢ, tⱼ)` with `γ(t)=p*`;
CircGamma on CircularArc stays QEX): `theories/CircularCookHit.v`.
4-axiom atan2 lane; no micro-kernel twin (radical `p*` + atan2 cone).

Production home for 64-circ-span-gamma (span-restricted γ on
`valid_arc` CircularArc; locked proper arcs keep radical `p+` and
reject `p−`; host CircGamma stays QEX): `theories/CircularCookSpan.v`.
4-axiom atan2 sidecar; no micro-kernel twin (atan2 / `arc_center` cone).

Production home for 0007-circ-cook (circular Hit feeds a same-shape
`split(t)` cook on locked discs; host `try_cook_hit` still declines
circular eggs; CircGamma stays QEX; Touch is a fenced QEX arm):
`theories/CircularCookSplit.v` (sidecar) and
`theories/Adr0007NodingEpic.v` (host QEX). 4-axiom atan2 sidecar;
no micro-kernel twin (atan2 / radical `p*` cone).

Production home for 0007-I.7-mint-two (`p−` is a second Hit;
allocation across `p+` and `p−` is `MintTwo`; leftover shared
endpoint ≠ kiss; Empty / Decline / Touch still mint nothing):
`theories/CircularCookSplit.v`. 4-axiom atan2 sidecar; no
micro-kernel twin (atan2 / radical `p*` cone).

Production home for 0007-I.1-fence (four objects pairwise unequal
by locked observation, not a type synonym; Touch ≠ IHit; circular
Empty ≠ Decline; chord × circular Decline inhabits `I_ok`;
`I_gloss` stays QEX): `theories/CircularCookSplit.v` (fence /
Touch / Empty tickets), `theories/Adr0007NodingEpic.v` (mixed
Decline), `theories/CircularCook.v` (`I_gloss` QEX). Sidecar
4-axiom atan2; host tickets atan2-free.

Production home for 0007-I.2-hit-sound (`I_circles_gamma` Hit iff
proper discriminant ∧ `on_full_circle` on both radical roots;
γ_full, not CircularArc span; R3 locked witness recovered;
CircGamma stays QEX): `theories/CircularCookHit.v`. 4-axiom atan2
lane; sidecar cook stays locked.

Production home for 0007-I.3-empty-decline (`I_circles_gamma` Empty
iff proper pair ∧ γ_full images disjoint on S; Decline iff not a
proper pair (`d=0` or `r≤0`); discriminant Empty ≠ image-disjoint
on concentric unequal radii; CircGamma stays QEX):
`theories/CircularCookEmpty.v`. 4-axiom atan2 lane; sidecar cook
stays locked.

Production home for 0007-I.8-leftover-confluence (`circ_leftovers_ab`
= `circ_leftovers_ba` on γ_full; circular analogue of
`split_step_confluent`; cook leftovers inhabit that bag; one-step
≠ bag loop; CircGamma stays QEX):
`theories/CircularCookConfluence.v`. 4-axiom atan2 sidecar; not
leftover-width. Campaign I close is I.10.

Production home for 0007-I.9-classifier-neq-cook (`I_circles_z` /
`I_CIRCULAR` Hit is tags 0/1, not glossary `(p*, tᵢ, tⱼ)`; Z Hit
⇏ host `try_cook_hit` / `circ_split` / first-cook expansion;
CircGamma stays QEX): `theories/CircularCookLicense.v`. 4-axiom
atan2 sidecar. Campaign I close is I.10.

Production home for 0007-I.10-campaign-i-close (sidecar cook on
constructed circular Hit, both roots; host CircGamma stays QEX;
`first_cook_scope` stays chord–chord; `I_CIRCULAR` stays a
classifier; #666 fence holds; Campaign II and H⊥ named parked;
no new kernel; not SQL/MM done):
`theories/CircularCookClose.v`. 4-axiom atan2 sidecar.

Production home for 0007-II.1-span-filter (radical root is an arc
Hit iff `on_arc_gamma` both; IResult filter on span γ, not γ_full;
locked `p+` Hit, `p−` Empty; host CircGamma stays QEX; II.2–II.4 /
H⊥ / SQL/MM cathedral stay parked):
`theories/CircularCookSpanFilter.v`. 4-axiom atan2 sidecar.

Production home for 0007-II.2-span-split (split `arc_gamma` at
in-span `t`; leftovers meet at locked `p+`; leftover on parent
circle; locked `p−` stays Empty / no invented span cook; host
CircGamma stays QEX; II.3–II.4 / H⊥ / SQL/MM cathedral stay
parked): `theories/CircularCookSpanSplit.v`. 4-axiom atan2 sidecar.

Production home for 0007-II.3-I-ok-circ (first glossary-type
inhabitant `I_ok_circ` on EggCircularArc × EggCircularArc via
sidecar `arc_gamma`; locked `p+` Hit licenses `span_split`;
locked far pair inhabits Empty; host CircGamma stays QEX;
II.4 / H⊥ / SQL/MM cathedral stay parked):
`theories/CircularCookOkCirc.v`. 4-axiom atan2 sidecar.

Production home for 0007-II.4-campaign-ii-close (Campaign II
close letter; sidecar `I_ok_circ` inhabitant; host CircGamma
stays QEX; `first_cook_scope` stays chord–chord; H⊥ parked;
not a bag noder; Phase B SQL/MM Part 3 required-type gaps
named — CircularString / CompoundCurve / CurvePolygon; not
SQL/MM done): `theories/CircularCookCloseII.v`. 4-axiom
atan2 sidecar.

Production home for 0007-B.1-cs-concat-joints (Phase B.1
CircularString concat joints; CS is a sequence of `CircEgg`;
joint is `I_ok_circ` Hit at `(end, t=1, t=0)` via sidecar
`arc_gamma`; joint params not interior; locked 2-arc V-CS
odd_closed fixture; host CircGamma stays QEX; CompoundCurve /
CurvePolygon / H⊥ parked; not SQL/MM done; no new kernel):
`theories/CircularCookCsConcat.v`. 4-axiom atan2 sidecar.

Production home for 0007-B.2-cc-member-joints (Phase B.2
CompoundCurve member joints; CC is a sequence of LineString
chords and CircularString `CircEgg` members; LS–LS joint is
host `I_ok` Hit at `(end, t=1, t=0)`; CS–CS member joint
reuses `I_ok_circ`; mixed LS–CS joint is host `I_ok` Decline
(I.1); locked mixed fixture; host CircGamma stays QEX;
CurvePolygon / H⊥ parked; not SQL/MM done; CC required-type
Gap (mixed LS–CS host Decline; letter B.2 landed ≠
required-type Landed); no new
kernel): `theories/CircularCookCcConcat.v`. 4-axiom atan2
sidecar.

Production home for 0007-B.3-cp-ring-closure (Phase B.3
CurvePolygon ring closure; CP ring is a closed CircularString
or closed CompoundCurve — B.2 members contiguous and closed,
last joins first; CS–CS closing reuses `I_ok_circ`; mixed
closing is host `I_ok` Decline (I.1); locked CS-ring and
mixed-ring fixtures; host CircGamma stays QEX; H⊥ /
CircGamma remint / bag-noder parked; not SQL/MM done; CP / CC
required-type Gap (mixed LS–CS host Decline); Phase B Open
(letter B.3 landed ≠ required-type Landed / done-when); no new
kernel): `theories/CircularCookCpConcat.v`. 4-axiom atan2
sidecar.

Production home for 64-naa-res (constructor ⇒ affine circle–circle
resultant root under `circles_properly_intersect`; not the converse
and not a Bézout/degree proof): `theories/CircleCircleResultant.v`.
3-axiom; no micro-kernel twin.

Production home for 9004-d (Green/Qed: the cell pruning bound behind
Polycenter / JTS Cell.getMaxDistance — an empty radius achievable at any
point of a square cell of centre c, half-side h is at most
dist(c, X) + √2·h for every obstacle X; two triangle steps plus the cell
circumradius dist_sq ≤ 2h²): `theories/CellRadiusBound.v` (same WITNESS
tag; also carries the centre-shift Lipschitz lemmas, radius
monotonicity, and per-cell corollaries on both the empty and inscribed
duals). The unit here is fully self-contained (local Lagrange-identity
triangle inequality) with the corner circumradius-equality pin, the
3 ≤ 2 + √2 slack pin, and the mismatch probe refuting the slack-free
misreading (empty radius 3 at (−1,0) beats centre clearance 2).
Subdivision recursion and tolerance loop deferred.

**9005-a has NO production home, by design** (Green/Qed, teaching-only):
the board card's paper (Garcia-Castellanos & Lombardo 2007, poles of
inaccessibility) is SPHERICAL, and plane MIC/LEC ≠ spherical PIA — a
`theories/` cite would be false ancestry (see
`docs/library-footnotes.md`). The unit teaches the paper's DEFINITIONAL
signature planarly: the PIA of the three-point shoreline A=(0,0),
B=(4,0), C=(0,4) over the closed triangle is the hypotenuse midpoint
(2,2) with clearance √8, equidistant (squared distance exactly 8) from
ALL THREE shoreline points — the exactly-three-closest-points signature.
Maximality is the rational nearest-vertex case split. Pins: the three
equidistance equalities; probes: the centroid cannot support the PIA
radius (clearance² 32/9 at A — PIA ≠ mass centre), and the hypotenuse
drift (3,1) drops clearance² to 2. Production twins named after
`theories/LargestEmptyCircle.v`; the spherical gap stays open on the
board.

## Re-run

```text
# micro-kernel static match (Rocq optional):
#   source = eval/Claim65a.v | eval/Claim65b.v | eval/Claim65c.v | eval/Claim65d.v | eval/Claim65e.v | eval/Claim67a.v | eval/Claim67b.v | eval/Claim68a.v | eval/Claim69a.v | eval/Claim423a.v | eval/Claim423b.v | eval/Claim424a.v | eval/Claim425a.v | eval/Claim9004c.v | eval/Claim9004d.v | eval/Claim9005a.v | eval/Claim64iCircular.v | eval/Claim64circZPartition.v
# full compile (needs Rocq / nts-eval switch):
rocq compile eval/Claim65a.v
rocq compile eval/Claim65b.v
rocq compile eval/Claim65c.v
rocq compile eval/Claim65d.v
rocq compile eval/Claim65e.v
rocq compile eval/Claim67a.v
rocq compile eval/Claim67b.v
rocq compile eval/Claim68a.v
rocq compile eval/Claim69a.v
rocq compile eval/Claim423a.v
rocq compile eval/Claim423b.v
rocq compile eval/Claim424a.v
rocq compile eval/Claim425a.v
rocq compile eval/Claim9004c.v
rocq compile eval/Claim9004d.v
rocq compile eval/Claim9005a.v
rocq compile eval/Claim64iCircular.v
rocq compile eval/Claim64circZPartition.v
```
