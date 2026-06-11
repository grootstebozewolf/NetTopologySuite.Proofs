# Session prompt — `extract_rings_valid` R5, slice 3i: the bridge discharge

**Status: PROMPT (not yet executed).** Written 2026-06-11, immediately after
slice 3h (`theories/ExtractFacesHoles.v`, with-holes emission + fidelity).
Outcome doc to be written by the executing session, per the Red/Green
template (`docs/FOR-AI-AGENTS.md`).

---

## Goal

Re-point the registered deferred proof
`theories-flocq/OverlayBridge.v : extract_rings_valid` (the registry's ONLY
live entry, `docs/admitted-deferred-proofs.txt`) onto the face extractor:
derive the three structural hypotheses of
`ExtractFaces.extract_faces_valid` / `ExtractFacesHoles.extract_faces_holes_valid`
from the noder's `fully_intersected` guarantee — the second "What remains"
item of `docs/extract-faces.md`.

## Environment

`noded_segments`, `noded_labeled_graph`, `fully_intersected` and the
deferred statement itself live in **`theories-flocq/`** — this session needs
the Flocq-buildable container (`Dockerfile`, Rocq 9.1.1 + Flocq 4.2.2) or
the host fallback **including step 4** (`docs/development-environment.md`).
Confirm `make -f Makefile.gen theories-flocq/OverlayBridge.vo` builds before
writing anything.

## Grep-first state (verified 2026-06-11)

- `OverlayBridge.extract_rings_valid` (line ~486): quantifies over
  `extract op (noded_labeled_graph A B)` under
  `fully_intersected (noded_segments A B)`. NOTE: `extract` here is still
  `OverlayGraph.extract` — the naive flatten that
  `ExtractFlattenCounterexample.extract_unordered_not_valid` refutes. The
  re-point therefore has TWO parts: (a) hypothesis discharge, (b) restating
  the obligation over `extract_faces` / `extract_faces_holes` (per slice 3g's
  header, which already declares the supersession).
- `HobbyTheorem_b64.fully_intersected` (line 75): distinct segments satisfy
  `~ properly_intersect \/ (shared endpoint)`. **The disjunction is the
  crux**: endpoint-sharing pairs are unconstrained beyond that.
- Targets to derive, for `D := result_darts op (noded_labeled_graph A B)`:
  1. `pairwise_no_proper_cross D` (`RingSimple.v:47` — requires
     `~ properly_intersect` OUTRIGHT for all distinct pairs);
  2. `forall v, fan_ok (outgoing v D)` (per-vertex angular general position);
  3. `no_short_faces D` (`ExtractFaces.v:245` — every face period ≥ 3).

## RED — predicted negatives (attempt FIRST, in this order)

The disjunct analysis suggests `fully_intersected` alone is **too weak** for
hypotheses 2 and 3:

- **R1 (bigon):** two distinct segments with the SAME endpoint pair satisfy
  `fully_intersected` (they share endpoints) but create a 2-dart face —
  refuting `fully_intersected -> no_short_faces`. Construct the concrete
  witness (two parallel "duplicate" segments, e.g. `((0,0),(1,0))` twice
  cannot work — they must be DISTINCT segments, so use a bigon of two
  distinct arcs of darts, e.g. the same endpoints reached by different
  segment records if the type permits, else two segments sharing both
  endpoints). If the witness lands, register nothing — state it as a
  Qed'd negative (`fully_intersected_not_no_short_faces`), corpus style.
- **R2 (fan collision):** two endpoint-sharing segments leaving a shared
  vertex at the SAME azimuth (collinear overlap of different lengths) —
  `fully_intersected` permits it (shared endpoint disjunct) but `fan_ok`
  fails. Same treatment.
- **R3 (proper-cross from the twin side):** check whether
  `pairwise_no_proper_cross D` needs an endpoint-sharing ⟹ ¬proper lemma
  (likely TRUE and provable: proper intersection is interior-interior;
  grep `segments_intersect_properly` consumers for an existing bridge —
  `Intersect.v` / `RingSimple.v` may already carry it).

## GREEN — deliverables (stop at the first genuine tangent)

- **D1.** `fully_intersected -> pairwise_no_proper_cross` for the dart set
  (expected TRUE; the endpoint-sharing disjunct collapses via R3's lemma;
  the twin-pair case needs "a segment does not properly cross its own
  reversal"). Host-side route available: prove over abstract segment lists
  in `theories/` (both predicates are pure-R; `fully_intersected` would
  need restating host-side or factoring out of `HobbyTheorem_b64` — prefer
  RESTATING + a flocq-side equivalence lemma over moving definitions).
- **D2.** The honest strengthened bridge: define the missing input
  (`no_duplicate_geometry` / `no_bigons` — exact shape to be discovered
  from R1/R2's witnesses) and prove
  `fully_intersected /\ <missing> -> fan_ok-per-vertex /\ no_short_faces`,
  OR (if the derivation collapses) leave hypotheses 2-3 as named inputs and
  document why — either way the registry entry's discharge plan is updated
  to the true dependency structure.
- **D3.** The re-point: restate the deferred obligation over
  `extract_faces_holes` (slice 3h) with D1/D2's bridge composed in front —
  `extract_rings_valid_faces : valid A -> valid B ->
  fully_intersected (noded_segments A B) -> <missing, if any> ->
  <nesting-oracle spec> -> forall poly In poly (extract_faces_holes ...) ->
  valid_polygon poly`. If D1-D3 all land, update
  `docs/admitted-deferred-proofs.txt`'s entry: the original
  `extract_rings_valid` stays Admitted ONLY if the naive-`extract` shape is
  retained for the RED record — otherwise follow the registry's
  comes-off-when-proved rule and consult the proof-structure doc §11 before
  touching the entry. ONE registry change maximum, with Joost-visible
  rationale.

## REFACTOR

Full gauntlet (container build, `audit_axioms` on a sequential log,
`check_admitted`, `check_readme_axioms`, `validate-claims` — use the
PRINTED claims count in the commit message). Update
`docs/extract-faces.md` "What remains" item 2 and the
`audit-rgr-comparison.md` running log. Outcome doc per template.

## Stopping conditions

- FULL SUCCESS: D1-D3 landed; registry updated (or explicitly left, with
  rationale); outcome doc written.
- TANGENT-STOP: R1/R2 witnesses land but D2's strengthened bridge stalls →
  commit the negatives + D1 alone (still real progress: the bridge's true
  shape is then machine-checked), document the wall precisely.
- COLLAPSE: if even D1 stalls on the twin/collinear case for >1/3 of the
  budget, stop and write the collapse note — the orthogonal-decomposition
  toolkit (`CurveJoinClassify.v` §1-2) and `Intersect.v`'s proper-cross
  lemmas are the first places to look before declaring the wall.

## Budget

1-3 deliverables; estimate 1 session for R1-R3 + D1, a second for D2-D3
(×1.5 for unknowns). Do not attempt R4 (Euler) or the analytic
`hole_inside_outer` seam in this session — they are separate squares
(`audit-rgr-comparison.md` §8).
