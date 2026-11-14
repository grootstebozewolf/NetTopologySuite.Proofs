<!-- doc-kind: finding
date: 2026-11-08
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Directed approximation — cheap first step (2026-11)

Experiment: factor the b64 passes-through completeness and the chord-approx
overlay lemma through one shared definition; if both proofs shrink, the
abstraction is real. Toolchain: Rocq 9.2.0 + Flocq 4.2.2, built via
`Makefile.gen` (no CI run id; local build).

Files: `theories/DirectedApprox.v` (defs + composition lemmas, pure Prop),
`theories-flocq/DirectedApprox_b64.v`, `theories/ArcOverlayDirected.v`.
No `Admitted`/`Axiom`.

## Definitions

`over_on D spec comp` (spec ⇒ comp), `under_on` (comp ⇒ spec), `exact_on`
(both = gap 0), `gap_within d eps D spec comp` (every accepted point is within
eps of a spec point). Proved: `exact_iff_over_under`, `over_trans`,
`under_trans`, `gap_trans` (bounds add), `over_/under_ {and,or}`,
`over_not_of_under` and `under_not_of_over` (**negation flips direction**),
`over_diff` (A∖B over needs A over **and B under**), and the counterexample
`over_diff_needs_under` (A over, B over ⇏ A∖B over).

## Does it shrink the two proofs? No.

* **b64.** `pt_over_on_int_safe` is `b64_passes_through_complete_on_grid`
  verbatim and `pt_exact_on_tight` is `b64_passes_through_grid_exact`; the
  instantiation is a rename. The real mechanism of the b64 completeness proof
  is *monotone rounding* (`round_le`: x ≤ y ⇒ round x ≤ round y), which is
  specific to rounded comparisons and not shared with the chord argument.
  `pt_not_under_globally` (the "failure is a result" statement) is a
  five-line corollary of `b64_passes_through_compute_unsound`.
* **Chord.** `arc_overlay_correct_chord_approx` is **not** an inclusion. It
  says chord-op results are within `max_sagitta` of an arc curve *given*
  H_A/H_B bridges as hypotheses. That is only the `gap_within` half. It
  factors (`arc_overlay_via_directed`, via `gap_mono_comp` + `gap_or`) but the
  original 4-case split is about the same size. The over/under half of the
  pattern is not stated anywhere for arcs.

## Corrections to the pitch's premises

1. b64 is **not** "provably complete" in general. Completeness is proved on
   the int-safe grid (|n| ≤ 2^25) and exactness on the tight grid
   (|n| ≤ 2^22). Off-grid completeness C2 is still open
   (`PassesThrough_b64_grid_separation.v`, "REMAINING OBLIGATIONS"), and no
   gap bound on the over-acceptance is proved (evidence only).
2. "A chord sits on one side of its arc" fixes direction **per arc**, relative
   to the region: bulge-out arcs make the chord polygon *under*, bulge-in arcs
   make it *over*. A polygon with mixed arcs is neither. (Reasoning only; not
   proved here.) So direction can't be a per-operation constant.

## What is real

The composition algebra is small and correct; the reusable payoff is
`over_diff`/`over_diff_needs_under`: difference and symdifference need an
*under* approximation of B, so an overlay pipeline built from over-only
predicates has no guarantee. That is the static check the pitch wanted, and it
is a statement about connectives, not about the existing proofs.

## Next step if pursued

State the missing half for arcs (arc region ⊆ N_eps(chord region) for
bulge-out, reverse for bulge-in) per arc and combine with `over_diff`; and
prove a gap bound for b64 off-grid. Until one of those exists the framework
has two instances with different halves, not two proofs sharing structure.

## Rung ladder, ordered by risk/cost (added after the biarc question)

Context: the per-arc direction claim is about one arc and its chord, not a
biarc. An S-type biarc (arcs curving in opposite senses) is the smallest
mixed instance. Machinery already present: `in_circular_segment` and
`arc_control_triangle_in_circular_segment` (ArcControlTriangleInSegment.v).

| # | Rung | Cost | Risk | Status |
|---|------|------|------|--------|
| 1 | Region model R=(P u O)\I; no-in => under, no-out => over, mixed => neither (`SignedBulge` in DirectedApprox.v) | tiny | none (pure set logic) | **done** |
| 2 | Concrete S-biarc witness: exhibit o in O\P, i in I n P with `in_circular_segment` on two rational arcs | low-medium | low (rational inCircle arithmetic) | **done** (`ArcSBiarcWitness.v`: `sbiarc_chord_neither`) |
| 3 | Bridge `in_circular_segment` + chord half-plane to O/I membership for one arc | medium | medium | after 2 |
| 4 | Justify R=(P u O)\I from the actual region boundary | high | high (Jordan-class; same wall as WindingNumber.v) | keep as named hypothesis |
| 5 | b64 off-grid completeness C2 / gap bound | high | high (known blocked) | defer |

Rung 1 caveat: the decomposition is an assumption, so rung 1 proves the
logic of direction, not that real regions satisfy it. Rung 4 is what would
discharge it.

Rung 2 result: two semicircles (0,0)-(2,0) bulging below and (2,0)-(4,0)
bulging above, G1 at the join (vertical tangent), P=[0,4]x[0,2]. Proved: both
arcs valid, mids on opposite chord sides, o=(1,-1/2) in seg(a1)\P not in
seg(a2), i=(3,1/2) in seg(a2) and P; hence `sbiarc_chord_neither`. The
decomposition R=(P u seg a1)\seg a2 is still the assumed rung-4 hypothesis;
G1 is noted in the comment, not proved.

SUMMARY ok=5 warn=2 bug=0
