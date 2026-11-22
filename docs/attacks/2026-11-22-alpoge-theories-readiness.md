<!-- doc-kind: finding
date: 2026-11-22
Provenance: 4ca468f
Theorems: `AlpogeSkeleton.v : sixth_batch_all_refined`, `CleanIntegralQED.v : FTC`, `AlpogeSixthBatch.v : RInt_exp_change`
-->
# Alpöge probes → `theories/`: readiness dry run and move plan

Requested: prepare to move the Alpöge work from the probe lane
(`docs/h1-vacuity/`) into `theories/`. Nothing is moved here. This finding
records a dry run and the plan for the move PR. The precedent is #1016
(carry_clean probes → `theories-flocq/`, ticket #1015).

**Dry run.** It was done in a throwaway worktree at `4ca468f`:
1. Copied the 21 files to `theories/` and rewrote `NTS.Proofs.Probes` →
   `NTS.Proofs`.
2. Appended them to `_CoqProject.full`.
3. Built each with `rocq c -Q theories NTS.Proofs`.
4. Ran `scripts/audit_axioms.sh` on every log, then every `make ci-guards`
   gate.

## What moves: 21 modules, Stdlib-only, host lane `theories/`

In dependency order (lines):
1. `LeanSkeletonRebuild` 759
2. `LandauWindowCore` 209
3. `LandauDichotomyQED` 441
4. `LandauWindowRebuilt` 299
5. `FormBRebuilt` 213
6. `WinSeamRebuilt` 199
7. `LandauKeyRebuilt` 404
8. `CoreSliceQED` 358
9. `AlpogeRefineBatch` 527
10. `AlpogeRealsQED` 485
11. `AlpogeRealsQED2` 546
12. `AlpogeDeepStatements` 281
13. `AlpogeRealsQED3` 1076
14. `CleanIntegralQED` 1363
15. `AlpogeIntegralQED` 325
16. `AlpogeFifthBatch` 345
17. `AlpogeSixthBatch` 743
18. `AlpogeSixthCH` 1065
19. `AlpogeSixthCHReals` 165
20. `AlpogeSixthLandau` 1190
21. `AlpogeSkeleton` 374

This is exactly the import closure of `AlpogeSkeleton`. No file imports Flocq,
so the lane is `theories/`. The files go into `_CoqProject.full` only, not
the foundational `_CoqProject` (`make host`), as in #1016.

## Dry-run results

| check | result |
|---|---|
| build under `NTS.Proofs` | **OK**: all 21, in order |
| `audit_axioms.sh` | **OK** on every log (three-axiom allowlist) |
| `check_admitted.sh`, `check_constructor_gate.py`, `check_readme_claims.py`, `check_cite_or_cut.py`, `exception_budget.py`, `check_hypothesis_ledger.py`, `check_readme_axioms.sh` | **pass** |
| `vm_compute` (`AlpogeSkeleton`, `CoreSliceQED`, `LeanSkeletonRebuild`) | allowed; 11 `theories/` files already use it, and the uses are small ledger computations |
| `check_name_shape.py` | **FAIL**: 50 new violations (below) |
| `check_module_split.py` | **FAIL**: `CleanIntegralQED.v` has 1363 lines × 7 dependents ≥ 3210 |
| `check_readme_counts.py` | **FAIL**, expected: README module and theorem counts must be bumped |
| deprecation warnings | 11 × `Local Notation` used as an abbreviation (Rocq 9.2), in `AlpogeSixthBatch` Part C |

## Blocker 1: name-shape gate (50)

The gate covers `theories/` and not the probe lane, so these are new here.
Registering them in `docs/name-shape-debt.txt` is not allowed ("fix the name
or the statement -- do not list it"), so each one is fixed.

**Duplicates with identical statements (14): keep one, import it.**
- `above_gt`, `above_sep`, `abs_of_sq_lt`, `minl_le_d`, `minl_le_mem`,
  `sq_le_inv`, `sq_lt_inv`, `sq_nonneg`: keep the copy in
  `LandauDichotomyQED`; `AlpogeRealsQED3` imports it.
- `Cc_ext`: keep `AlpogeSixthBatch`; `AlpogeSixthLandau` imports it.
- `ksum_perm`: keep `AlpogeFifthBatch`; `AlpogeSixthCH` imports it.
- `level_family_zerofree`: keep `AlpogeRefineBatch`.

**Duplicates with differing statements (13 names): rename the later copy
with a module-specific suffix.**
- `AlpogeRealsQED3`:
  - `avoid` → `avoid_r`
  - `minl_attained` → `minl_attained_r`
  - `minl_cases` → `minl_cases_r`
  - `nearest_equi` → `nearest_equi_r`
  - `on_axis` → `on_axis_r`
  - `split_list` → `split_list_r`
  These are the over-R ports of the Q versions in `LandauDichotomyQED`.
- `AlpogeSixthCH`: `ksum_*` (4) → `rsum_*` / `csum_*` forms; it works over the
  record `CStr`, not the section field.
- `AlpogeSixthCH.abs_le_elim` → `Rabs_le_elim`, a Stdlib-scope head.
- `cnorm_nonneg` and `cnorm_sq`: `AlpogeSixthCHReals` imports
  `AlpogeSixthLandau`'s copies if the statements can be aligned; otherwise
  rename to `cnorm_nonneg_c` and `cnorm_sq_c`.
- `exists_small_eps`: `AlpogeRealsQED` → `exists_small_eps_r`.
- `level_family_sum`: `AlpogeRealsQED` → `level_family_sum_r`.
- `CleanIntegralQED.deriv_nonneg_incr` → `deriv_nonneg_incr_rint`. This is
  the only clash with an existing module (`RealMonotone.v`).

**Capitalised heads (21): lowercase them.**
- `FTC`, `FTC_C1`, `FTC_Lip`, `FTC_value` → `ftc`, `ftc_c1`, `ftc_lip`,
  `ftc_value`.
- `RI_lipschitz` → `riemann_integrable_lipschitz`.
- `E1_term_nonneg` → `e1_term_nonneg`.
- `Lc_cont`, `Lc_lt`, `Lc_neg`, `Lc_posv` → `lc_cont`, `lc_lt`, `lc_neg`,
  `lc_posv`.
- `Cc_ext`, `Cc_nz_norm` → `cc_ext`, `cc_nz_norm`.
- `CDW_*` (8) → `cderiv_within_*`.

**Shape (2):**
- `iteratedDeriv_laplace_exists` must state `exists`, or be renamed
  `iteratedDeriv_laplace_some`.
- `cnorm_pos_ne` must conclude `<>`, or be renamed `cnorm_pos_of_ne`.

Every rename touches the citing files: the ledger strings and `Check`s in
`AlpogeSkeleton.v`, plus the open finding docs. Merged findings stay as they
are, because findings are not re-anchored at HEAD.

## Blocker 2: split `CleanIntegralQED.v` (#1047's library)

Use the umbrella pattern: `CleanIntegralQED.v` stays as a
`Require Export` of the parts, the declaration set is byte-identical, and the
`Print Assumptions` footers move with their declarations. A natural cut follows
its own Parts:
- `CleanIntegralCore.v`, about 915 lines: helpers, tagged partitions,
  `RInt`, linearity, monotonicity, Chasles, `mvt_ge`/`mvt_le`, FTC, change of
  variables and `RIntInf` (Parts 0–6, l.62–914).
- `CleanIntegralApps.v`, about 450 lines: `Lc'`, the window integrals, `Pk`
  and the kernel, `kernel_integral` and `windowHyp_of_rpow_r` (Parts 7–10,
  l.915–1363).

Both parts are below the 1234-line floor. `AlpogeSixthLandau.v` (1190
lines) is in the watch band but under the floor.

## Move PR checklist (after #1046 merges)

1. `git mv` the 21 files from `docs/h1-vacuity/` to `theories/`, and rewrite
   `NTS.Proofs.Probes` → `NTS.Proofs`.
2. Append the 21 files to `_CoqProject.full` in the order above, each with a
   short comment naming the Lean file it mirrors.
3. Apply the name-shape fixes and the `CleanIntegralQED` split above.
4. Remove the 21 entries from `scripts/hunt_probe_smoke.sh`. The other
   probes in that list do not import them.
5. Update the guide `docs/h1-vacuity/README.md`. Guides have a net ≤ 0 prose
   budget, so replace rather than add.
6. Bump the README counts (`check_readme_counts.py`), and the
   `docs/READING-GUIDE.md` counts if they apply.
7. Add `docs/verified-claims.md` rows only if a claimId is minted. The Alpöge
   items are evidence of an external audit, not NTS claims, so the default is
   `claimId: none`.
8. Replace the 11 `Local Notation` abbreviations in `AlpogeSixthBatch` Part C.
9. Run `make ci-guards`, `check_doc_kinds.py`, the `theories/` build and
   `audit_axioms.sh`. Then write a new finding that supersedes this one.

## Open question for the owner

Should these modules be **product** modules at all? They prove facts about an
external Lean development, not NTS or JTS behaviour. CONTRIBUTING asks every
new theorem for "a header comment naming the corresponding NTS module or JTS
algorithm". `CleanIntegralQED`, `AlpogeRealsQED`/`QED2` (clean `exp`/`Lc`/`rpc`)
and the integration tools (`RInt_bounded`, `RInt_exp_change`) are reusable
real analysis, and they fit `theories/` on their own. The audit-specific
files could stay probes. The move PR should state which it is.

## OUTCOME

**Ready, with three mechanical blockers.** The build and axiom audit are clean
under `theories/`. The blockers are 50 name-shape fixes, one module split and
the README counts.

**SUMMARY ok 9 / warn 3 / bug 0.**
