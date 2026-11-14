<!-- doc-kind: finding
date: 2026-11-14
Provenance: e2ddc4d519d4725a5c765f191c32fc5712227d89
Theorems: `OverlayCorrectness.v : overlay_ng_correct_conditional`, `HobbyTheorem_b64.v : hobby_theorem_4_1_conditional`, `ArcOverlay.v : arc_overlay_correct_chord_approx`, `ExtractFacesHoles.v : extract_faces_holes_valid`, `ClothoidHalley.v : clothoid_halley_filtered_corpus_le_four`, `ClothoidHalley_b64.v : b64_clothoid_halley_filtered_corpus_le_four`, `RelateClothoid.v : clothoid_L_unique_on_branch`, `JCTEscapeDescentHolds.v : parity_seam_offring_taut`
-->
# Hypothesis ledger — what the conditionals actually assume (2026-11)

**Question.** "Qed-closed" is true of every `[cond]` row, but a conditional
can push the hard part into a premise. Which premises are discharged, which
are open, and which are false?

**Method.** Each hypothesis of each `[cond]` row of `verified-claims.md` was
read off the source statement (inline premises and Section hypotheses), then
looked up for a discharging, reducing or refuting theorem. The result is
[`hypothesis-ledger.tsv`](hypothesis-ledger.tsv). It is checked by
`scripts/check_hypothesis_ledger.py` (in `make ci-guards`). The script
complements `check_ledger_assumptions.py`: `Print Assumptions` never sees an
inline premise `H -> concl`, which is how two of the defects below passed.

## Coverage at this commit

42 theorems itemised, 57 hypotheses:

| status | count | meaning |
|---|---|---|
| discharged | 10 | a Qed theorem proves it outright |
| reduced | 11 | proved from per-input guards that are themselves open |
| instance | 4 | proved for named instances only (circle, Fresnel, balanced convex) |
| open | 26 | nothing proves or refutes it |
| refuted | 4 | a Qed theorem proves it false |
| circular | 2 | the hypothesis is the conclusion |

30 theorems cited in `[cond]` rows are not itemised yet (the three
PARALLEL TRACK batch rows and the Stage D sibling names). They are listed by
name in the script's `UNAUDITED` set, which may only shrink.

## Defects found

1. **`overlay_ng_correct_conditional` is vacuous (new QEX).** Its H1 states
   `point_in_ring q r <-> geometric_interior_cont q r` for every closed
   simple ring, with no on-edge, horizontal-edge or vertex guard. The notch
   hexagon of `JCT_HorizontalEdgeCounterexample.v` falsifies it:
   `docs/h1-vacuity/OverlayH1ContQEX.v : overlay_H1_refuted`, and
   `overlay_ng_correct_conditional_vacuous` derives `False` from the
   headline's own premise list. The source header calls this H1 "honest,
   satisfiable"; it was satisfiable only before the JCT lane found the
   guards. The fix is cheap: the guarded off-ring seam is proved for taut,
   core-nodup, horizontal-free rings
   (`JCTEscapeDescentHolds.v : parity_seam_offring_taut`), so restating H1
   with those guards discharges it. H2 (universal over every valid graph)
   and H_bridge stay open.
2. **`hobby_theorem_4_1_conditional` is vacuous.** Already machine-checked
   (`docs/h1-vacuity/HobbyHlemma43Check.v : Hlemma43_uninhabitable`), but
   the ledger row still read as a plain conditional headline. Relabelled.
3. **`arc_overlay_correct_chord_approx` was listed as "Unconditional".** It
   takes `H_A_bridge` / `H_B_bridge` as inline premises; the proof is a case
   split on `op`. The source's own §3 says the bridges fail for any polygon
   wider than the sagitta. Retagged `[cond]`; no QEX yet.
4. **`extract_faces_holes_valid` is vacuous on non-empty results.** Its
   `pairwise_no_proper_cross (result_darts …)` premise forces every edge
   degenerate (`ExtractFacesBridge.v : pairwise_darts_of_forces_degenerate`).
   The twin-aware rows are the working form; the row now says so.
5. **The Halley "≤ 4 iterations" headlines are circular.** In both
   `ClothoidHalley.v` and `ClothoidHalley_b64.v` the Section hypothesis
   `H_filtered_corpus_le_four` is the conclusion, over an abstract `Problem`.
   The ledger said "discharged as `H_filtered_corpus_le_four`". Relabelled:
   the bound is golden-vector evidence, not a theorem.
6. **`clothoid_L_unique_on_branch` was tagged `[exact]`** while taking
   `ClothoidFPrimePos` as a premise. Retagged. On `ClothoidResidual.v`:
   `H_deriv` is discharged (`clothoid_f_deriv`, via `lint_leibniz`) and
   `H_fprime_pos` is discharged on `|κL| ≤ 1/2` (`clothoid_fprime_pos`);
   only the full branch `|κL| ≤ π` (`ClothoidFPrimePos`) is open.
   `Azimuth.v`'s comment still calls both Section hypotheses; stale.
7. **Stage D "REFUTED" headline has no kernel refutation.**
   `fast_expansion_sum_strong_nonoverlap_headline` is called refuted in
   source and ledger, but no theorem states its negation:
   `B64_Shewchuk_Thm13_counterexample.v` proves valid inputs and that
   `[256; 1]` fails the predicate, not that `fast_expansion_sum` returns
   `[256; 1]`. Ledger status `open`. It is superseded, so this is a
   labelling gap, not a soundness one.

## Not defects, but worth stating

- The JCT lane's chain of `[cond]` rows (trapped half, level jump, escape
  descent, walk step) is discharged or reduced to three ring guards
  (`ring_taut`, `ring_core_nodup`, `no_horizontal_edges`).
- Several guards exclude common inputs. `no_horizontal_edges` /
  `no_horizontal_darts` exclude every axis-aligned rectangle, and snapping
  can create horizontal darts
  (`SnapRoundingGuardAudit.v : snap_can_introduce_horizontal_dart`). A
  `reduced` status is only as wide as its guards.

## Follow-ups

- Restate H1 of `overlay_ng_correct_conditional` with the off-ring + taut
  guards and discharge it from `parity_seam_offring_taut`.
- QEX for `H_A_bridge` (a chord square with a short arc and a centre point
  far from it), or drop the headline.
- Itemise the 30 `UNAUDITED` names.

SUMMARY ok=32 warn=3 bug=7 — of 42 itemised theorems, 7 were vacuous, circular or mis-tagged (defects 1–6) and 3 carry an unproved "REFUTED" label (defect 7); 26 of 57 hypotheses are open.
