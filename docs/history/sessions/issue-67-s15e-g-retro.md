# Issue #67 S15e–g retro — line×line noding exterior rows + collection union

2026-06-20. Three slices on branch `claude/issue-67-s14-prepared-cache-al`.
Commits `39a9017` (S15e–f), `7b92a5d` (S15g). Living triage:
[`docs/issue-67-relateng-triage.md`](../../issue-67-relateng-triage.md).

## What landed

| Slice | § | Main deliverables (`RelateNodingLineLine.v`) |
|---|---|---|
| **S15e** | §12 | OGC exterior rows: `no_share_midpoint_ie_cell`, `no_share_midpoint_ei_cell`, `classify_disjoint_midpoint_ie_ei_cells`; BE/EB endpoint-exterior cells; `segments_bnd_int_bi_cell`; **JTS#1175 negative** `jts1175_no_share_pointset_bi_empty`; `paper_test10_ie_ei_ee_cells` |
| **S15f** | §14 | Collection BI path: `line_collection_bnd_int_contact`, `bnd_int_contact_implies_segments_share`, `jts1175_collection_bi_witness`, `jts1175_no_share_nominated_pair_bi_empty`, `mod2_endpoint_bnd_int_bi_cell`, `classify_disjoint_exterior_be_eb_cells` |
| **S15g** | §15 | Collection union: `line_collection_cell_ok`, `line_collection_de9im_pointset`, `dim_value_join`, `line_collection_pair_cell_sub`, `line_collection_test10_de9im_rows`, `line_collection_test10_intersects`, `line_collection_classify_disjoint_test10_rows` |

Corpus: **422** cited theorems (`validate-claims.sh` green). All new modules
0 `Admitted`, standard 3 classical-reals axioms.

GitHub prose refreshed: [#67](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/67) body + verdict comment; [#69](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/69) umbrella table.

## The JTS#1175 arc (why three slices, not one)

Romanschek test 10 (`ll_matrix_paper_test10`) is **geometrically no-share on a
nominated segment pair** yet **not DE-9IM disjoint** because BI = 0. The corpus
now pins that footprint honestly at three layers:

1. **Single-pair point-set (S15e negative):** `~ segments_share` ⇒ BI cell
   empty (`jts1175_no_share_pointset_bi_empty`). Test-10 BI = 0 is *not*
   derivable from strata on one pair alone.
2. **Single-pair positive limitation (S15f):** bnd×int contact ⇒ share
   (`bnd_int_contact_implies_segments_share`); hence
   `jts1175_no_share_nominated_pair_bi_empty`. A pair that carries BI = 0-dim
   must share geometrically.
3. **Collection cross-product (S15f–g positive):** multi-segment lists with
   bnd×int contact across *some* pair yield BI / IE / EI / EE row witnesses and
   `im_intersects` for the test-10 oracle matrix — matching the jts#1200 fix
   class (line-end enumeration across disjoint components).

The nominated pair vs collection split is the substantive content of these
slices; the exterior-row lemmas are the OGC row infrastructure that makes
test-10 aggregation composable.

## Three things worth carrying forward

**Existential union before max-join fill.** S15g deliberately lands
`line_collection_cell_ok` as “∃ cross-product pair with witness” before attempting
pairwise `dim_value_join` over the full 9-cell matrix. That matches how RelateNG
actually gets witnesses (any contributing segment pair suffices for non-emptiness)
and avoids proving dimension-upgrade lemmas that are false at the witness level
(a dim-0 point witness does not prove a dim-1 cell on the same pair).

**`line_cell_ok` is an iff, not a record.** Extracting witnesses from
`line_bi_point_cell` requires destructuring the `<->` in the second component of
`line_cell_ok`, then applying the forward direction with a `dim_nonempty` side
condition. `destruct Hmeet as [_ [p [Hbnd Hint]]]` on the iff directly fails;
the working pattern is `destruct Hcell as [_ Hiff]; destruct Hiff as [Hto _];
destruct (Hto Hdn) as [p [...]]`.

**Coq hygiene on this file is now a checklist.** Recurring fixes in S15e–g:
- `intros A B C D Hext` on endpoint theorems (not `intros Hext` alone).
- `intro Hbet; apply Hnoshare; apply int_on_*_share` instead of
  `apply no_share_interior_not_on_* with` (instance resolution fails on `C`/`D`).
- `exists A; exists B; exists C; exists D` + explicit `split` bullets (not
  `exists A, B, C, D` / `repeat split; eauto`).
- `destruct B as [bx by]` — `by` is a tactic keyword; use `b_y`.
- Midpoint algebra: `field`, not `ring`, for `/2`.

## Calibration

S15e was started in a prior session and finished green in this one (proof fixes
only). S15f and S15g each fit one focused § block (~80–120 lines). The
**collection union** slice was smaller than feared because the existential model
reuses all S15e pairwise lemmas via `line_collection_pair_cell_sub`.

Pushing required `gh auth git-credential` (HTTPS prompts disabled in the agent
shell). Once configured, `39a9017` and `7b92a5d` both landed on the remote.

## Open items (S15h+)

| Item | Notes |
|---|---|
| Pairwise `dim_value_join` matrix fill | `dim_value_join` algebra is in §15; sound lift from per-pair matrices to collection matrix not yet proved |
| Full IE/EI/BE/EB from `line_pair_fill` alone | Still need exterior hypotheses or all-no-share collection guard |
| Cell-dimension pinning | Jordan/overlay soundness layer; separate from witness selection |
| PR #248 merge | S13–S14 prepared cache still pending on `main` |
| `LPR_Share` vs Touches witness mismatch | Honest gap from S15a header; untouched this cycle |

## Session ordering note

S15e (exterior rows) → S15f (collection BI + nominated-pair gap) → S15g
(existential union + test-10 aggregation) is the correct dependency order.
Attempting S15g before S15f would have lacked `line_collection_bnd_int_contact`
and the negative/positive JTS#1175 story would be incomplete in the docs.