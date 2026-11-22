<!-- doc-kind: finding
date: 2026-11-22
Provenance: 0b70c5f0
Theorems: `AlpogeTopShape.v : shapeWin_from_links_r`, `AlpogeTopShape.v : topDesWin_r`, `AlpogeTopShape.v : link_ex_r`, `AlpogeTopShape.v : link_gl_r`, `AlpogeTopShape.v : designExists_of_choices_r`, `AlpogeSkeleton.v : counts`
-->
# Alpöge main line: TopShape link facts refined

Requested: the `TopShape` link facts. #1048 left them, with `askExp`, as the
deepest assumed inputs under `TopG`. `AlpogeSixthBatch.v` refines `shapeWin`
from three inventory hypotheses (`link_ex`, a bundled `links`, `topDesWin`).
This finding opens that bundle and rebuilds the Lean proofs that wire it.

The work is in `docs/h1-vacuity/AlpogeTopShape.v`. It is within the
three-axiom allowlist (`scripts/audit_axioms.sh` OK), with no `Admitted`.

External subject: mirror `CocoSgt/riemann-hypothesis-lean` @ `7cbf7a0`, read
from source; nothing was built. Readings of Lean types are marked in the
probe. This does not verify RH. The verdict on the external development is
unchanged: **PASS-STATIC / PENDING**.

## What is rebuilt

| Lean | Rocq | what is proved |
|---|---|---|
| `designExists_of_choices` | `designExists_of_choices_r` | Epsilon shrink, `sup`, thin arrow, `TuSize` from `cT ≤ CTu`, `ChosenE` pack. |
| `link_ex` | `link_ex_r` | Subclass projections, `Closed.sub` / `and` / `imp`, `exp 1 ≤ 3`. |
| `link_gl` | `link_gl_r` | `0 < 3`, `0 ≤ 2`, `3 ≤ 3`, Duty projection, `and`/`imp` for `hRk`. |
| `link_eta` | `link_eta_r` | `Rmax` split of the tied-family threshold. |
| `link_g` | `link_g_r` | `of_class` for the record and the Mertens tops. |
| `link_brest` | `link_brest_r` | The Lean proof is the call `bRest_all`. |
| `link_alt` | `link_alt_r` | The Lean proof is the call `theoremS_transport`. |
| `link_irr` | `link_irr_r` | Max threshold and `Closed` algebra. |
| admissible twist | `admissible_twist_link_r` | `of_class` for `DGamSize`, conjunction of the eight inputs, project `.1`. |
| `selection_closed_of_wu_decay` | `selection_closed_r` | Quantifier tidy-up on gap and `miStar`. |
| `smallLevelRankEq` | `small_level_rank_eq_r`, `small_level_at_max` | `Rmax` bounds. |
| `topDesWin` | `topDesWin_r` | Nine-fold `and`, radius shrink, divin/mu wiring into `FamilyClassConnected`. |
| `shapeWin` glue | `shapeWin_from_links_r` | Class inclusions into `TopG`. |

`askExp` is not part of this link. It is left for the next slice.

## Inputs left as hypotheses

- **[Mathlib]:** `exp 1 < 3` (`Real.exp_one_lt_d9` then `norm_num`). The proofs use `exp 1 ≤ 3`.
- **[inventory], replayed only as calls (QEX for this slice):**
  - `bRest_all`
  - `theoremS_transport_link_zero`
  - `sizesRec_at`, inside `rows_extend` (the rpow chain)
  - `linkIRR_of_join_ex` (its own rpow step)
  - `dGamSize_of_dvd` (the `log_minkM` bound)
  - `rank_zero_of_row_conditions`
  - `famGLmin` (`muRank`, `link8`)
  - `divinN_of_hypV`, `muTu_of_tuSize`, `muDGam_of_fact`, `linkMu_of_linkDIV`
- **[inventory], other calls named in the probe:** `large_sup`, `chosenProviso_min`, `closed_rankTiesF_C2S`, `class_of_record`, `designChoices_upN`, `chosenThin_closed`, `minkowski_bound_rat`, `tied_families_of_choice`, `linkEta_closed`, `linkG_concrete5`, `admissible_family_of_inclusion`, `finXRow_of_gap`, `complement_five`, `toRows`/`wire_sel`, and `nRest` (a `TopShape` input, not a link lemma).

These hypotheses are the Lean statements' remaining calls. The statements of the link lemmas are not replaced by weaker ones.

## Ledger

`AlpogeSkeleton.v` cites `shapeWin_from_links_r` on the `TopG` row and `Check`s the fourteen theorems. The counts are unchanged: 53/53 refined and 46 proved over R. The link facts are sub-lemmas of the `TopG` item, not new ledger rows.

## OUTCOME

**QED (refined)** for the closed-class algebra and the wiring above. **QEX** for the arithmetic bodies listed as inventory calls; they stay hypotheses. Alongside them, `askExp` is untouched. The Alpöge verdict is unchanged: **PASS-STATIC / PENDING**.

**SUMMARY ok 14 / warn 0 / bug 0.**
