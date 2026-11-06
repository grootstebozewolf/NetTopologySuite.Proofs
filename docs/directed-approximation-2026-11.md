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

SUMMARY ok=3 warn=2 bug=0
