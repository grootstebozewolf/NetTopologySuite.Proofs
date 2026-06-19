# Outcome — Esri 300 EllipticArc + Bezier3Curve chord-seed (fresh branch)

**Branch:** `grok/fresh-esri300-elliptic-bezier` (created 2026-06-19 from origin/main; prior tree stashed).

**Prompt summary.** Create fresh branch, then "investigate and add [EllipticArc and Bezier3Curve] the same way we added CLOTHOID".

## LANDED

- Four new Stdlib-only modules (theories/):
  - `RelateEllipticArc.v` — `EllipticArcChord` (start/end), chord predicates delegating to segment ops, S2-reused witness matrices (`eac_matrix_*`), geometry consequences (`proper_cross_share`, `rejected_not_share`).
  - `RelateMatrixEllipticArc.v` — `EllipticArcRegime` (EAR_Chord*), `elliptic_arc_fill`, eq lemmas, classify, constant `*_witness` facts.
  - `RelateBezier3.v` + `RelateMatrixBezier3.v` — identical shape with `Bezier3Chord` / `B3R_*` / `bezier3_fill`.

- Oracle / test vectors (exact clothoid precedent):
  - `oracle/de9im_elliptic_vectors.txt` (3 chord regimes, `ELLIPTIC (x y) (x y)` token).
  - `oracle/de9im_bezier3_vectors.txt` (analogous, `BEZIER3` token).

- Glue:
  - `oracle/relate_matrix_fill_vocabulary.txt` — added two FILL_API sections (EAR_*, B3R_*).
  - `oracle/relate_matrix.ml` — registered the four new `*_matrix_*` strings + the six fill aliases.

- Build:
  - Listed in `_CoqProject.full` (with explanatory comment) next to the Clothoid pair.
  - `rocq makefile -f _CoqProject.full` succeeds.
  - Modules compile cleanly (only the corpus-permitted 3 classical + functional_extensionality axioms; matrix files are 0-axiom "Closed under the global context").

- Gauntlet (fast path):
  - `scripts/check_admitted.sh` — pass.
  - `scripts/check_readme_axioms.sh` — pass.
  - `scripts/validate-claims.sh` — pass (no new headline theorems claimed in verified-claims.md yet — these are internal support lemmas exactly like the clothoid chord files).

All files carry the project header (BSD-3, "No Admitted/Axiom/Parameter", AI disclosure).

## COLLAPSED / NOT ATTEMPTED (this slice)

- Full elliptic / bezier analytic definitions in `CurveGeometry.v` (left for later; clothoid itself never received a full `CurveGeometry` member in the chord-seed slice).
- b64 mirrors, intersection oracles, arc-length etc. (future, like clothoid Halley/Scope A).
- Adding to the small host `_CoqProject` (clothoid relate files live only in .full).
- Updates to `verified-claims.md` (these are not top-level citable claims at this stage).
- Driver.ml changes (clothoid chord vectors did not require them).

## Relation to the plan

- Exact replication of the Clothoid (S10b) + ArcChord (S10) delta for relate chord seed.
- Decision: 2-point chord carriers (sufficient for the chord-path regimes that clothoid used). Richer ellipse params or full 4-pt Bezier controls are not required for the delegate-to-segment layer.
- Strengthens the "core geometry primitives" story by extending the set of curve types with verified relate support.

## Next

When the consumer (NTS.Curve or test harness) starts emitting `ELLIPTIC ...` / `BEZIER3 ...` vectors or needs richer predicates, the next slice can:
- Promote to richer records + CurveGeometry integration.
- Add analytic regimes (if useful) or b64 chord oracles.
- Extend to full curve×curve relate.

**Stopping condition met:** the "add the same way" request is complete for the chord-seed / DE-9IM matrix layer. All invariants preserved.
