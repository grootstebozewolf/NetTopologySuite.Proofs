<!-- doc-kind: finding
date: 2026-11-14
Provenance: e2ddc4d519d4725a5c765f191c32fc5712227d89
Theorems: `OverlayCorrectness.v : overlay_ng_correct_conditional`, `HobbyTheorem_b64.v : hobby_theorem_4_1_conditional`, `ArcOverlay.v : arc_overlay_correct_chord_approx`, `ExtractFacesHoles.v : extract_faces_holes_valid`, `ClothoidHalley.v : clothoid_halley_filtered_corpus_le_four`, `ClothoidHalley_b64.v : b64_clothoid_halley_filtered_corpus_le_four`, `RelateClothoid.v : clothoid_L_unique_on_branch`, `JCTEscapeDescentHolds.v : parity_seam_offring_taut`, `RingCurvatureModels.v : extract_rings_valid_hyperbolic_of_guards`
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

## Coverage

All 83 theorems cited in conditional rows (`[cond]`, or "cond per entry"
in the batch rows) are itemised: 109 hypotheses. The script's `UNAUDITED`
set is empty. 702 theorems cited in NON-conditional rows have premises but
no ledger lines; they are frozen as debt in
`hypothesis-ledger-premise-baseline.txt` (shrink-only), and any new one
fails the check.

| status | count | meaning |
|---|---|---|
| discharged | 40 | a Qed theorem proves it outright, or it is a decidable input guard |
| reduced | 11 | proved from per-input guards that are themselves open |
| instance | 4 | proved for named instances only (circle, Fresnel, balanced convex) |
| open | 43 | nothing proves or refutes it |
| refuted | 7 | a Qed theorem proves it false |
| circular | 2 | the hypothesis is the conclusion |
| placeholder | 2 | the named Prop is defined as `True`; its content is a comment |

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
   (`JCTEscapeDescentHolds.v : parity_seam_offring_taut`). That alone does
   NOT rescue the headline (PR #1024 review): H2 (`extract` valid on every
   valid topology graph) is false too
   (`docs/h1-vacuity/OverlayGuardedVacuityQEX.v : overlay_H2_refuted`, a
   one-edge graph gives a 2-point ring), and `extract` is a placeholder that
   puts every result edge in one ring. See defect 11 for the restatement.
2. **`hobby_theorem_4_1_conditional` is vacuous.** Already machine-checked
   (`docs/h1-vacuity/HobbyHlemma43Check.v : Hlemma43_uninhabitable`), but
   the ledger row still read as a plain conditional headline. Relabelled.
3. **`arc_overlay_correct_chord_approx` was listed as "Unconditional".** It
   takes `H_A_bridge` / `H_B_bridge` as inline premises; the proof is a case
   split on `op`. The source's own §3 says the bridges fail for any polygon
   wider than the sagitta. Retagged `[cond]`. Follow-up QEX:
   `docs/h1-vacuity/ArcOverlayBridgeQEX.v` refutes both bridges and the
   conclusion on a valid input.
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

8. **The curvature-model corollaries rest on placeholders.**
   `RingCurvatureModels.v : extract_rings_valid_hyperbolic_of_guards` and
   `extract_rings_valid_spherical_hemisphere_of_guards` take
   `beltrami_klein_correspondence` / `gnomonic_correspondence`, both defined
   as `True` with the geometry in a comment. They are the planar guarded
   theorem renamed and prove nothing about curved geometry. Row now says so.
9. **`point_in_ring_correct_jct_cont`'s row called it "non-vacuous"** without
   saying its seam is false at on-edge points
   (`JCT_OnEdgeCounterexample.v : parity_seam_strict_refuted_on_edge`).
   Found by the per-input refutation rule; row fixed.

10. **My own first `curve_region` (this branch) was wrong.** It flipped each
    arc's whole circular segment over the whole geometry. The chord
    approximation runs through the arc midpoint, so the triangle S M E was
    flipped out of the region
    (`docs/h1-vacuity/CurveRegionModelQEX.v : old_model_wrong_in_triangle`),
    and its stated side condition (disjoint segments) does not follow from
    `valid_curve_geometry`. The headline survived (the triangle lies in the
    sagitta band). Fixed: per-ring caps, outer minus holes, union of
    polygons, needing no disjointness.

11. **My first `overlay_ng_correct_guarded` (this branch) was still
    vacuous** (PR #1024 review). It kept H2 and H_bridge universal over all
    topology graphs and the placeholder `extract`: H2 is refuted (defect 1),
    and a universal H_bridge forces an empty result, because the empty graph
    is valid with vacuously correct labels
    (`docs/h1-vacuity/OverlayGuardedVacuityQEX.v : overlay_universal_bridge_forces_empty`).
    Passing it the proved guarded H1 was inert. Restated: at
    `noded_labeled_graph A B` only, over `extract_faces`, with output
    validity proved from the guards of `extract_rings_valid_of_guards`; the
    per-input semantic bridge is the whole open content.
12. **Two holes in this branch's checker** (PR #1024 review). "vacuous"
    matched "non-vacuous"; now negations do not count. And coverage only
    looked at `[cond]` rows, so an `[exact]` row with inline premises and no
    ledger lines -- the ArcOverlay bug -- passed. Now every theorem cited in
    a non-conditional row is checked for source-level premises (top-level
    `->`, open-Section hypotheses); existing debt is frozen in a shrink-only
    baseline. The detector is textual, and `discharged` still trusts its
    evidence anchor; both limits are stated in the script header.

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

Done on this branch: H1 of the overlay headline restated and discharged
(`OverlayCorrectnessGuarded.v : overlay_ng_correct_guarded`); QEX for the arc
bridges and the arc headline's conclusion
(`docs/h1-vacuity/ArcOverlayBridgeQEX.v`) and its region restatement
(`ArcOverlayRegion.v : arc_overlay_region_close`); all names itemised. Open:

- The per-input semantic bridge of `overlay_ng_correct_guarded`, and a noder
  theorem producing its guards.
- Shrink `hypothesis-ledger-premise-baseline.txt` (702 entries).
- Tighten the arc band to the S–M / M–E cap sagitta (about 4×).
- Derive `b64_orient2d_expansion_cc_safe` from the coordinate domain.
- Either formalise the curvature-model correspondences or drop the names.
- Tie `ArcOverlayRegion.v : curve_region` (even-odd per ring) to the
  POINT_IN_CURVE_RING oracle, or prove it equals an arc-aware ray parity.

SUMMARY ok=66 warn=6 bug=12 — of 83 itemised theorems, 11 were vacuous, circular, placeholder-backed or mis-labelled (defects 1–6, 8, 9, 11) and 6 carry an unproved "REFUTED" label (defect 7); defects 10–12 were this branch's own (region model, first guarded headline, checker), fixed; 43 of 109 hypotheses are open; 702 premise-bearing unconditional citations frozen as debt.
