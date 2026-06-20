# Issue #67 S15h–k retro — matrix fold, dimension pinning, relate-matrix capstone

2026-06-20. Four slices on branch `claude/issue-67-s15k-pipeline-capstone`.
Commits `c32977a` (S15h), `0e545ea` (S15i), `83cab3e` (S15j), `1890298` (S15k);
docs prose `86ac426`. Living triage:
[`docs/issue-67-relateng-triage.md`](../../issue-67-relateng-triage.md).

## What landed

| Slice | § | Main deliverables (`RelateNodingLineLine.v`) |
|---|---|---|
| **S15h** | §16 | Per-pair 9-cell bridges: `classify_disjoint_test10_empty_meet_rows`, `classify_disjoint_paper_test10_exterior_rows`, `classify_disjoint_line_de9im_pointset_test10`; Share vs Touches IB (`classify_share_int_bnd_touches_vs_interior`, `classify_share_endpoint_only_touches_ib`); regime pointset packaging (`classify_proper_cross_line_de9im_pointset`, `classify_collinear_overlap_line_de9im_pointset`); no-share BE/EB via endpoint exteriority (`separated_segments_endpoint_exterior_be_eb`) |
| **S15i** | §17–§18 | `matrix_dim_join` algebra (`line_collection_cell_ok_dim_join`, `line_collection_de9im_pointset_join`); cross-product fold (`line_collection_matrix_fold`, `line_collection_matrix_fold_segsB`); `line_collection_matrix_fold_sound`; collection row extraction (`line_collection_de9im_pointset_implies_rows`); test-10 full 9-cell capstone (`line_collection_test10_de9im_pointset`) |
| **S15j** | §19 | `line_cell_ok_pinned` / `line_cell_true_dim`; forward bridge `line_cell_ok_pinned_implies_ok`; II/BB regime pins (`classify_proper_cross_ii_dim_pinned`, `classify_collinear_overlap_ii_dim_pinned`, `classify_disjoint_ii_dim_pinned`, `classify_share_interior_ii_dim_pinned`); Share/Touches gap `line_pair_fill_share_ii_not_pinned_int_bnd_only`; regime exclusivity (`line_pair_regime_disjoint_not_share`, `line_pair_regime_overlap_not_proper_cross`) |
| **S15k** | §20 | Idempotence (`dim_value_join_idem`, `matrix_dim_join_idem`); fold-assign API (`line_pair_matrix_assign`, `line_collection_matrix_fold_assign`, `line_pair_matrix_of_regime`); headlines `line_collection_relate_matrix_fold_sound`, `line_collection_relate_matrix_regime_fold_sound`; per-pair disjoint+bnd_int 9-cell (`classify_disjoint_pair_de9im_pointset_test10`); test-10 pipeline (`line_collection_relate_matrix_test10`, `_intersects`, `_meet_pinned`) |

Corpus: **444** cited theorems (`validate-claims.sh` green). All new modules
0 `Admitted`, standard 3 classical-reals axioms.

## The S15e–g → S15h–k arc (why four slices)

S15g landed existential collection union (`line_collection_cell_ok` as ∃
cross-product witness) and row-level test-10 aggregation, but not:

1. **Per-pair full 9-cell `line_de9im_pointset`** from regime classification
   alone (exterior rows still needed no-share or explicit endpoint-exterior
   hypotheses in S15e).
2. **Pairwise `matrix_dim_join` lift** from per-pair matrices to a collection
   matrix (the `dim_value_join` algebra was present but unused for fold).
3. **Meet-layer dimension pinning** — witness-level `line_cell_ok` does not
   record which dimension is *forced* by geometry (II point vs overlap vs empty).
4. **End-to-end relate-matrix headline** tying pointset spec, fold, and oracle
   matrix for the JTS#1175 test-10 class.

The four slices close that ladder in dependency order: per-pair fill (S15h) →
fold soundness (S15i) → pinning semantics (S15j) → capstone composition (S15k).

## Three things worth carrying forward

**Disjoint exterior rows compose from no-share, not four endpoint hypotheses.**
S15h's `separated_segments_endpoint_exterior_be_eb` derives BE/EB from
`~ segments_share` via endpoint-on-other-segment ⇒ share contradictions. That
lets `classify_disjoint_paper_test10_exterior_rows` chain IE/EI (S15e) + BE/EB
+ EE without the four explicit exterior guards S15e used on single pairs.

**Fold soundness is induction on lists + join closure, not a matrix generator.**
S15i's `line_collection_matrix_fold_sound` reuses S15g's
`line_collection_de9im_pointset_join` at every cons step. The hard lemmas are
list-cons lifting (`line_collection_de9im_pointset_segsA_cons`,
`_segsB_cons`) and the empty-matrix base cases (`matrix_dim_join_empty_left/right`).
Do not attempt to characterize the folded matrix cell-by-cell before proving
pointset soundness — the existential spec is the right target.

**Regime wrapper needs split classify vs de9im hypotheses.** S15k's
`line_collection_relate_matrix_regime_fold_sound` cannot bundle
"classified ⇒ pointset" into one implication: Coq needs `Hclass` to instantiate
`Hregime` at each pair. Pattern: `specialize (Hregime A B C D HinA HinB (Hclass ...))`
then `unfold line_pair_matrix_assign` / `line_pair_matrix_of_regime`.

## Proof hygiene (new checklist items)

- **`repeat split` on `line_de9im_pointset` fails** — the 9-cell spec is a
  nested `split` chain, not a flat conjunction. Use explicit 9-way
  `split; [exact Hii | split; [exact Hib | ...]]` (S15k
  `classify_disjoint_pair_de9im_pointset_test10`).
- **Constant fold needs idempotence, not reflexivity.** Single-element
  `line_collection_matrix_fold_segsB` must `apply Hconst` after
  `matrix_dim_join_empty_right`; multi-element needs `rewrite matrix_dim_join_idem`
  after joining identical matrices (S15k `line_collection_matrix_fold_const`).
- **`line_collection_matrix_fold_const` uses `revert HexA` induction** — tail
  fold and head `fold_segsB` must both rewrite to `m` before idem join.
- **Pinned II: `Some 1` means collinear overlap, `Some 0` means point meet**
  — `line_cell_ok_pinned` is case-split on `DimValue`, not an alias of
  `line_cell_ok`. Forward bridge (`line_cell_ok_pinned_implies_ok`) only covers
  II and BB today; exterior pinning deferred S15l+.

## Calibration

Each slice was one focused § block (~150–250 lines). S15k was mostly
composition — the substantive new proof work was idempotence lemmas, the regime
wrapper, and the explicit 9-cell disjoint+bnd_int bridge. S15j deliberately did
**not** touch `line_pair_fill` or oracle matrices (pinning is a read-only
interpretation layer).

S15h–k closed three items listed as open in the
[S15e–g retro](issue-67-s15e-g-retro.md): pairwise `dim_value_join` fill,
per-pair exterior packaging from regime, and meet-layer cell-dimension pinning
(II/BB only). The Share/Touches fill mismatch is now **documented** (S15j) but
not **resolved** (needs `LPR_Touches` at fill API — S15l+).

## Open items (S15l+)

| Item | Notes |
|---|---|
| Prepared evaluate hook | End-to-end `evaluate(prepare(A),B) = relate(A,B)` once full pipeline exists |
| Exterior-row true-dimension pinning | IE/EI/BE/EB/EE pinning layer; S15j covers II/BB meet cells only |
| `LPR_Touches` regime split at fill API | Share fill assigns point-II oracle; int×bnd contact needs Touches matrix — honest gap from S15j |
| PR #248 merge | S13–S14 prepared cache still pending on `main` |
| Beyond line×line | Area/line/collection noding for full RelateNG ask #4 |

## Session ordering note

S15h (per-pair fill) → S15i (fold soundness) → S15j (pinning) → S15k
(capstone) is strict: S15k's regime wrapper and test-10 headlines import
S15i's fold lemmas and S15h's per-pair pointset bridges; S15k's meet-pinned
corollary imports S15j's `no_share_ii_dim_pinned` / `disjoint_bb_dim_pinned`.
Attempting S15k before S15i would lack `line_collection_matrix_fold_sound`;
attempting S15i before S15h would lack regime-keyed per-pair assign witnesses
for the capstone examples.