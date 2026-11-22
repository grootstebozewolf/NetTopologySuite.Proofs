<!-- doc-kind: finding
date: 2026-11-22
Provenance: 0b70c5f0
Theorems: `AlpogeTopShape.v : shapeWin_from_links_r`, `AlpogeTopShape.v : topDesWin_r`, `AlpogeTopShape.v : link_ex_r`, `AlpogeTopShape.v : link_gl_r`, `AlpogeTopShape.v : designExists_of_choices_r`, `AlpogeTopShape.v : selection_closed_r`, `AlpogeTopShape.v : small_level_at_max`, `AlpogeSkeleton.v : counts`
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

A first draft of this probe dropped quantifiers (`rRows_info`, `gap_raw`),
turned `muTu_of_tuSize` and `muDGam_of_fact` into proofs of `True`, and made
`link_alt_r` / `link_brest_r` definitionally identical to one hypothesis.
Those statements are restored below. Where a Lean proof could not be closed,
the missing piece is a named hypothesis and is listed as QEX.

## What is rebuilt

| Lean | Rocq | what is proved |
|---|---|---|
| `designExists_of_choices` | `designExists_of_choices_r` | Epsilon shrink, `sup`, thin arrow. The witness keeps `CH`, `0 ≤ CH`, `hL1`, and `ChosenE` at that `CH`. The eliminator is fed `hL2`. |
| `link_ex` | `link_ex_r` | Subclass projections, `Closed.sub` / `and` / `imp`, `exp 1 ≤ 3`, result `DesignExists 3`. |
| `link_gl` | `link_gl_r` | `0 < 3`, `0 ≤ 2`, `3 ≤ 3`. Conclusion `GLArrow 2 3 2 0` (`LinkGLOBAL Fm 2 CH 3 2 0`). |
| `link_eta` | `link_eta_r` | `Rmax` split. The tied family yields `⟨mt, cover, hecke⟩` at each `i`. |
| `link_g` | `link_g_r` | `of_class` for the record and the Mertens tops. |
| `link_brest` | `link_brest_r` | `bRest_all` applied to its premises. Conclusion `∀ hc, TuSize → DGamSize → RemAt` at `Cabs = 2`. |
| `link_alt` | `link_alt_r` | `ssel`, `residEv_closed_free`, `locTied`, `instTie_of_record`, `one_le_qqI_of_inst`, and `C0 = 3` (`3 ≤ 3`, `0 < 3`, `exp 1 ≤ 3`). |
| `link_irr` | `link_irr_r` | Max threshold, literal `Cs = 6`, and `0 < cIc`. |
| admissible twist | `admissible_twist_link_r` | Eight-way conjunction. `adm2` is `∃ x0, ∀ x ≥ x0, x1 < x → ∀ i`. Level-prime closure is at `WithChN` with literal `3`. |
| `selection_closed_of_wu_decay` | `selection_closed_r` | `gap_raw` keeps `x1 < x`, `sel ≤ x`, and `∀ i`. `rRows_info` keeps `∀ hc, ∃ C _ x0`, the three guards, and `∀ i`, with `C` in `miStar`. |
| `smallLevelRankEq` | `small_level_rank_eq_r`, `small_level_at_max` | `rank_zero` is called at `Rmax (sel) xr`. `le_max_left` / `le_max_right` are `small_level_at_max`. |
| `topDesWin` | `topDesWin_r` | Nine-fold `and`, radius shrink. `muTu` and `muDGam` are passed to `linkMu_of_linkDIV`. |
| `shapeWin` glue | `shapeWin_from_links_r` | Class inclusions into `TopG`, at `Cabs = 2`, `C0 = 3`, `eD = 2`, `eL = 0`. |

`askExp` is not part of this link. It is left for the next slice.

## QEX (named hypotheses)

- **[Mathlib]:** `exp 1 < 3` (`Real.exp_one_lt_d9` then `norm_num`). The proofs use `exp 1 ≤ 3`.
- **[inventory]:** `bRest_all`, `theoremS_transport_link_zero`, `sizesRec_at` (inside `rows_extend`), `linkIRR_of_join_ex`, `dGamSize_of_dvd`, `rank_zero_of_row_conditions`, `famGLmin` (`muRank`, `link8`), `divinN_of_hypV`, `muTu_of_tuSize`, `muDGam_of_fact`, `linkMu_of_linkDIV`, `admissibleLabelWeights_of_greenCuspidalParametrisation`.
- **[inventory], other calls:** `large_sup`, `chosenProviso_min`, `closed_rankTiesF_C2S`, `class_of_record`, `designChoices_upN`, `chosenThin_closed`, `minkowski_bound_rat`, `tied_families_of_choice`, `linkEta_closed`, `linkG_concrete5`, `admissible_family_of_inclusion`, `finXRow_of_gap`, `complement_five`, `toRows`/`wire_sel`, `nRest`, `dGamSize_fact`.

## Deviations that remain

- `fin` is a local inductive with the two `Fin` constructors. Importing `Stdlib.Vectors.Fin` binds the name `R` and hides the reals.
- `D3 c0 A` is `c0 = 3 ∧ Des (WithChN A)`. Lean's `3` is a parameter of the family record. `closed_at_des` uses `3 = 3` to read a `D3 3` fact as a `Des (WithChN A)` fact. `FamilyClassConnected` in `AlpogeDeepStatements.v` has no `Cabs`; `topDesWin_r` projects `ChainTied` out of `LinkPack` and drops `TiedScale`.
- The ignored component of `⟨C, _, x0⟩` is a real `spare` with `spare = spare` in the body, so the binder is not erased. It is not a Lean field.
- `bRest_all`'s row and divisibility premises, and `link_alt`'s `ssel` / `locTied` / `instTie` / `one_le_qqI`, are opaque `Prop`s. The dependency on `TuSize`, `DGamSize`, `CH`, and `C0 = 3` is in the types that are proved.
- `DesignChoices` does not repeat every Lean field (`ThickSetEventually`, `TameDistinct`, `CF = CH`, `CYL ≤ 9`). The `DesignExists` witness does keep `CH`, `0 ≤ CH`, `hL1`, and the `ChosenE` record fields that `chosenE_of_pack` consumes.
- `large_sup` returns two proofs of one `Side` predicate. The proof stores the first and feeds the second to the eliminator.
- `dGamSize_fact` is the reading that `DGamSize` supplies the `FactDGam` tail. `muDGam_of_fact` (`SumLogPrimeFactorsLe.lean:756`) takes that tail and returns `MuDGam`. `DesWin.lean:31` applies it to `hDG`.
- `rank_zero` still hides the non-surjectivity callbacks (`toRows`, `rowsHold0_of`, the selection projections). The surjectivity callback is the one instantiated at `Rmax (sel) xr`.

No candidate NACK. The restored statements are the Lean quantifier order. The items above are unread proofs, not weaker conclusions.

## Ledger

`AlpogeSkeleton.v` cites `shapeWin_from_links_r` on the `TopG` row and `Check`s the theorems, including `small_level_at_max`. The counts are unchanged: 53/53 refined and 46 proved over R. The link facts are sub-lemmas of the `TopG` item, not new ledger rows.

## OUTCOME

**QED (refined)** for the closed-class algebra and the wiring above. **QEX** for the inventory calls and the deviations listed. `askExp` is untouched. The Alpöge verdict is unchanged: **PASS-STATIC / PENDING**.

**SUMMARY ok 14 / warn 0 / bug 0.**
