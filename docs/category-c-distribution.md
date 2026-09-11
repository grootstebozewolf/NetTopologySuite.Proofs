# Category C distribution — the full A/C1/C2 classification pass

**Status**: evidence artifact (machine-generated 2026-08-16); discharges
open input #1 of `docs/category-c-policy.md` §8.
**Update 2026-08-19**: 28 Category A lemmas moved from
`InCircle_b64_exact.v` into `InCircle_b64_exact_refs.v` (Flocq-free,
off `audit-exceptions.txt`). The table row for the remaining file is
35 / 18 A / 17 C1. The TSV remains the 2026-08-16 snapshot.
**Update 2026-08-19 (CI)**: `OrientHybridPackage.v` (#488) was missing
from `audit-exceptions.txt` and is now listed (89 files / 73
`theories-flocq/`). The TSV still does not include that file's nine
PA footers.
**Update 2026-08-20**: Category A lemma `in_hot_pixel_unfold` (plus the
closed-pixel R-side defs) moved from `HotPixel_b64.v` into
`HotPixel_b64_refs.v` (Flocq-free, off `audit-exceptions.txt`). The
table row for the remaining file is 59 / 23 A / 32 C1 / 4 C2. The four
C2 comparison lemmas stay in-file. The TSV remains the 2026-08-16
snapshot.
**Update 2026-08-25**: Five all-C2 `theories/` files left
`audit-exceptions.txt` after a 3-axiom Taylor-envelope proof of
`sin x < x` (`pre_sin_bound` / `SIN_bound` in `ArcLength.v`) replaced
Stdlib `sin_lt_x` (MVT → `classic`): `ArcLength.v`, `ArcArea.v`,
`ArcCentroid.v`, `ArcAreaCentroid.v`, `CurveBufferArea.v`. The six
tainted theorems (`chord_le_arc_length`, `segment_area_nonneg`,
`arc_centroid_offset_le_radius`, `segment_area_factor_pos`,
`segment_centroid_offset_nonneg`, `buffer_arc_area_grows`) are now
allowlist-clean. `ArcChordSubdivision.v` stays listed (atan2 C1);
its `sin_sq_le_sq` is now allowlist via the same envelope. Remaining
C2 on the 2026-08-16 shortlist: 11 flocq + `sin_sq_le_sq`. Exceptions
list: 84 files / 73 `theories-flocq/` / 11 `theories/`. The TSV
remains the 2026-08-16 snapshot.
**Update 2026-08-27**: `Orient_geos968_onsegment_pins.v` (#540) was
missing from `audit-exceptions.txt` and is now listed (85 files / 74
`theories-flocq/`). Three PA footers are C1 via `Bminus`/`Bmult` in
the Ozaki DAG. The TSV still does not include this file.
**Update 2026-09-11**: Chip 2 peeled `NurbsKnotSpans.v` and
`ArcArcQuartic.v` off `audit-exceptions.txt` after a host-lane PA
measurement of all 35 R-side listed files (0 already allowlist-clean).
The atan half-circle instance moved to `NurbsConicExact.v`; the atan2
N-AA headline moved to `ArcSpanAtan2.v`. Remaining list: 108 files /
74 `theories-flocq/` / 33 `theories/` / 1 hunt probe. No Flocq C1 file
can leave while Flocq's binary model is in use. The TSV remains the
2026-08-16 snapshot.
**Update 2026-08-27**: Four HotPixel comparison lemmas
(`b64_le_R_of_true`, `b64_le_complete`, `b64_lt_R_of_true`,
`b64_lt_complete`) left `classic` after a payload split on finite
`B2R` (`± IZR m * bpow e`) replaced `rewrite Bcompare_correct`.
`HotPixel_b64.v` stays on the exceptions list (32 C1). Remaining C2:
7 flocq after HotPixel four. The TSV remains the 2026-08-16 snapshot.
**Data**: [`category-c-distribution.tsv`](category-c-distribution.tsv)
(one row per PA-audited theorem: file, name, category).

## 1. Headline

Across all 88 files on `docs/audit-exceptions.txt`
(72 in `theories-flocq/`, 16 in `theories/`), the per-theorem
audit attributes **1002 Print Assumptions outputs**:

| Category | Count | Share | Meaning |
|---|---|---|---|
| **A** — co-located clean | 362 | 36.1% | No `Classical_Prop.classic`; already satisfies the allowlist, sits in an excepted file |
| **C1** — type-tainted | 618 | 61.7% | `classic` in the STATEMENT's closure; unfixable while the statement names Flocq binary ops / `atan`-lineage definitions |
| **C2** — proof-only | 18 | 1.8% | Statement clean; `classic` enters via the proof — tactical re-proof candidate |
| definition seeds | 4 | 0.4% | Tainted `Definition`s (bodies), the C1 sources for their consumers |

**C1 : C2 = 618 : 18 (≈ 34 : 1).** The May 2026
sample-based guess ("C1 dominates") is confirmed decisively: tactical
re-proof (the C2 lever) can clean at most 18 theorems corpus-wide;
everything else on the list is either already clean (A) or structurally
inherent (C1). The policy choice therefore hinges on Options 2 vs 3, not
on re-proof capacity.

## 2. Method (reproducible)

1. **Per-theorem attribution.** All listed files touched, full lane
   rebuilt with `make -j4 --output-sync=target` (the audit script's own
   convention), each file's contiguous chunk split on its ordered
   `Print Assumptions <name>.` lines — positional zip, zero count
   mismatches across 88 files / 1002 theorems.
2. **Type-vs-proof split.** For every classic-tainted theorem, a probe
   `Definition __probe_X := ltac:(let T := type of X in exact T).` plants
   the STATEMENT as a definition body without referencing the proof
   constant; `Print Assumptions __probe_X` is then exactly the
   statement's closure. `classic` present → C1; absent → C2. 636 probes,
   zero compile failures (the `type of` form needs no statement parsing
   and survives Section-generalized statements).
3. Six names PA-printed by a sibling module's footer were re-homed to
   their declaring module first (see §4).

Category B (trivial-content C1, per policy §4) is a content judgment on
top of C1 and was not attempted mechanically; every type-tainted theorem
is reported as C1.

## 3. The actionable C2 shortlist (18 theorems)

| File | Theorem |
|---|---|
| `theories-flocq/HotPixel_b64.v` | `b64_le_R_of_true` |
| `theories-flocq/HotPixel_b64.v` | `b64_le_complete` |
| `theories-flocq/HotPixel_b64.v` | `b64_lt_R_of_true` |
| `theories-flocq/HotPixel_b64.v` | `b64_lt_complete` |
| `theories-flocq/Intersect_b64.v` | `b64_bpoint_eq_imp_BP2P_eq` |
| `theories-flocq/Intersect_b64.v` | `b64_shared_endpoint_witness_sound` |
| `theories-flocq/PassesThrough_b64_grid_core.v` | `b64_eqb_true_iff_B2R` |
| `theories-flocq/PassesThrough_b64_grid_core.v` | `b64_le_eq_Rle_bool` |
| `theories-flocq/PassesThrough_b64_grid_core.v` | `b64_max_B2R` |
| `theories-flocq/PassesThrough_b64_grid_core.v` | `b64_min_B2R` |
| `theories-flocq/PassesThrough_b64_grid_core.v` | `slab_guard_bridge` |
| `theories/ArcArea.v` | `segment_area_nonneg` |
| `theories/ArcAreaCentroid.v` | `segment_area_factor_pos` |
| `theories/ArcAreaCentroid.v` | `segment_centroid_offset_nonneg` |
| `theories/ArcCentroid.v` | `arc_centroid_offset_le_radius` |
| `theories/ArcChordSubdivision.v` | `sin_sq_le_sq` |
| `theories/ArcLength.v` | `chord_le_arc_length` |
| `theories/CurveBufferArea.v` | `buffer_arc_area_grows` |

Five `theories/` arc files were **all-C2** at the 2026-08-16 snapshot
and left `audit-exceptions.txt` on 2026-08-25 (see the header update):
`theories/ArcArea.v`, `theories/ArcAreaCentroid.v`,
`theories/ArcCentroid.v`, `theories/ArcLength.v`,
`theories/CurveBufferArea.v`. `ArcChordSubdivision.v` stays (atan2 C1).
The four HotPixel flocq-lane C2s (`b64_le_R_of_true` and kin) were the
policy doc's §4 canonical exemplars (`rewrite Bcompare_correct`). They
are now allowlist via the payload split (2026-08-27 update). Remaining
flocq C2: Intersect two + PassesThrough grid five.

Definition seeds: `arc_sweep` (`theories/RelateArcAnalytic.v`), `cascade_h_chain_statement` (`theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v`), `fast_expansion_sum` (`theories-flocq/B64_FastExpansionSum_Shewchuk.v`), `b64_orient2d_expansion` (`theories-flocq/Orient_b64_expansion.v`).

## 4. Finding: the audit's no-footer blind spot (two instances, fixed)

A file with no `Print Assumptions` vernacular produces no auditable
blocks, so `audit_axioms.sh` — which checks blocks, not files — never
sees it at all. The sweep found two instances:

- **`theories-flocq/PassesThrough_b64_grid_gap_kernel.v`** left the
  exceptions list under meso-audit B4 (#465) as "3-axiom, zero classic".
  Its slice-13 ulp lemmas (`b64_ulp_round_le_bpow`, `_unit`) mention
  `b64_round` in their statements — **Category C1, machine-verified
  classic** — while the slice-12 rational-gap lemmas are genuinely clean
  (2-axiom). The five-way split had carried all its footers to sibling
  modules. Fixed: the module now prints its own five leaves and is
  re-listed; the stale "first module to leave the list" claims in the
  file header, umbrella header, `_CoqProject.full`, and the exceptions
  list are corrected.
- **`theories/BufferJoin.v`** was exception-listed but had no footer, so
  its exemption was unverifiable. Fixed: it now prints its seven leaves
  — 5 C1 (atan2 lineage in the statements), 2 clean.

The general rule — **every module prints its own leaves** — is recorded
for the audit's hardening backlog: 37 more footers currently
print from a non-declaring sibling (all inside the already-listed
PassesThrough family, so no third hole today), and a CI check that every
registered `.v` with `Lemma`/`Theorem` content carries at least one
`Print Assumptions` line would close the class.

## 5. Per-file distribution

| File | PA'd | A | C1 | C2 | def |
|---|---|---|---|---|---|
| `theories-flocq/ArcLineIntersect_b64_exact.v` | 45 | 7 | 38 | 0 | 0 |
| `theories-flocq/B64_Expansion_Shewchuk.v` | 3 | 2 | 1 | 0 | 0 |
| `theories-flocq/B64_FastExpansionSum.v` | 22 | 7 | 15 | 0 | 0 |
| `theories-flocq/B64_FastExpansionSum_Shewchuk.v` | 16 | 6 | 9 | 0 | 1 |
| `theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v` | 58 | 25 | 32 | 0 | 1 |
| `theories-flocq/B64_Pff_bridge.v` | 15 | 4 | 11 | 0 | 0 |
| `theories-flocq/B64_Shewchuk_Thm13_counterexample.v` | 12 | 8 | 4 | 0 | 0 |
| `theories-flocq/B64_Shewchuk_Thm13_pathAB.v` | 14 | 0 | 14 | 0 | 0 |
| `theories-flocq/B64_Shewchuk_Thm13_pathA_defect.v` | 1 | 0 | 1 | 0 | 0 |
| `theories-flocq/B64_TwoSum_sterbenz.v` | 8 | 0 | 8 | 0 | 0 |
| `theories-flocq/B64_bridge.v` | 24 | 2 | 22 | 0 | 0 |
| `theories-flocq/B64_lib.v` | 8 | 0 | 8 | 0 | 0 |
| `theories-flocq/B64_nonoverlap_head.v` | 8 | 4 | 4 | 0 | 0 |
| `theories-flocq/B64_pathB_trace_4A.v` | 10 | 1 | 9 | 0 | 0 |
| `theories-flocq/B64_residue_granularity.v` | 10 | 4 | 6 | 0 | 0 |
| `theories-flocq/ClothoidDegenerate_b64.v` | 5 | 2 | 3 | 0 | 0 |
| `theories-flocq/ClothoidHalley_b64.v` | 30 | 17 | 13 | 0 | 0 |
| `theories-flocq/ClothoidResidual_b64_exact.v` | 20 | 12 | 8 | 0 | 0 |
| `theories-flocq/ClothoidScopeA_b64.v` | 4 | 1 | 3 | 0 | 0 |
| `theories-flocq/CurveLineariseGuardBridge.v` | 3 | 0 | 3 | 0 | 0 |
| `theories-flocq/DivRoundPow2_b64.v` | 5 | 1 | 4 | 0 | 0 |
| `theories-flocq/ExtractFacesBridge.v` | 10 | 8 | 2 | 0 | 0 |
| `theories-flocq/HobbyCounterexample_b64.v` | 15 | 1 | 14 | 0 | 0 |
| `theories-flocq/HobbyTheorem_b64.v` | 3 | 1 | 2 | 0 | 0 |
| `theories-flocq/HotPixel_b64.v` | 59 | 23 | 32 | 4 | 0 |
| `theories-flocq/InCircle_b64_exact.v` | 35 | 18 | 17 | 0 | 0 |
| `theories-flocq/Intersect_b64.v` | 21 | 9 | 10 | 2 | 0 |
| `theories-flocq/Intersect_b64_exact_bridge.v` | 4 | 0 | 4 | 0 | 0 |
| `theories-flocq/Intersect_b64_exact_core.v` | 12 | 3 | 9 | 0 | 0 |
| `theories-flocq/Intersect_b64_exact_forward_error.v` | 16 | 0 | 16 | 0 | 0 |
| `theories-flocq/Intersect_b64_exact_round_chain.v` | 20 | 1 | 19 | 0 | 0 |
| `theories-flocq/Intersect_b64_exact_tight.v` | 10 | 0 | 10 | 0 | 0 |
| `theories-flocq/KakeyaOrient2d_b64.v` | 5 | 0 | 5 | 0 | 0 |
| `theories-flocq/KakeyaPerron_b64.v` | 9 | 4 | 5 | 0 | 0 |
| `theories-flocq/NodingSeparation_b64.v` | 14 | 4 | 10 | 0 | 0 |
| `theories-flocq/OrientStratifiedAPF.v` | 20 | 7 | 13 | 0 | 0 |
| `theories-flocq/Orient_b64_R.v` | 5 | 0 | 5 | 0 | 0 |
| `theories-flocq/Orient_b64_dekker_int.v` | 3 | 0 | 3 | 0 | 0 |
| `theories-flocq/Orient_b64_exact.v` | 42 | 17 | 25 | 0 | 0 |
| `theories-flocq/Orient_b64_expansion.v` | 5 | 0 | 4 | 0 | 1 |
| `theories-flocq/Orient_b64_int_safe.v` | 3 | 0 | 3 | 0 | 0 |
| `theories-flocq/Orient_b64_int_safe_coords.v` | 4 | 1 | 3 | 0 | 0 |
| `theories-flocq/Orient_b64_sound.v` | 2 | 0 | 2 | 0 | 0 |
| `theories-flocq/Orient_b64_stage_d.v` | 3 | 0 | 3 | 0 | 0 |
| `theories-flocq/Orient_b64_stage_d_safe.v` | 5 | 1 | 4 | 0 | 0 |
| `theories-flocq/Orient_b64_underflow_recovery.v` | 5 | 3 | 2 | 0 | 0 |
| `theories-flocq/Orient_b64_underflow_unsound.v` | 5 | 3 | 2 | 0 | 0 |
| `theories-flocq/Orientation_b64.v` | 7 | 4 | 3 | 0 | 0 |
| `theories-flocq/OverlayBridge.v` | 18 | 1 | 17 | 0 | 0 |
| `theories-flocq/OverlayBridgeUnconditional.v` | 2 | 0 | 2 | 0 | 0 |
| `theories-flocq/OverlayCorrectness.v` | 3 | 0 | 3 | 0 | 0 |
| `theories-flocq/PassesThroughHalfopen_b64.v` | 8 | 5 | 3 | 0 | 0 |
| `theories-flocq/PassesThroughHalfopen_b64_compute_incomplete.v` | 18 | 8 | 10 | 0 | 0 |
| `theories-flocq/PassesThroughHalfopen_b64_compute_unsound.v` | 12 | 10 | 2 | 0 | 0 |
| `theories-flocq/PassesThrough_b64_compute_asymmetric.v` | 6 | 0 | 6 | 0 | 0 |
| `theories-flocq/PassesThrough_b64_compute_refine.v` | 4 | 2 | 2 | 0 | 0 |
| `theories-flocq/PassesThrough_b64_compute_unsound.v` | 29 | 27 | 2 | 0 | 0 |
| `theories-flocq/PassesThrough_b64_grid_bounds.v` | 16 | 0 | 16 | 0 | 0 |
| `theories-flocq/PassesThrough_b64_grid_complete.v` | 11 | 0 | 11 | 0 | 0 |
| `theories-flocq/PassesThrough_b64_grid_core.v` | 14 | 0 | 9 | 5 | 0 |
| `theories-flocq/PassesThrough_b64_grid_gap_kernel.v` | 5 | 3 | 2 | 0 | 0 |
| `theories-flocq/PassesThrough_b64_grid_separation.v` | 28 | 20 | 8 | 0 | 0 |
| `theories-flocq/PassesThrough_b64_spec_symmetric.v` | 7 | 6 | 1 | 0 | 0 |
| `theories-flocq/RingCurvatureModels.v` | 9 | 5 | 4 | 0 | 0 |
| `theories-flocq/Shewchuk_vs_Z2.v` | 3 | 1 | 2 | 0 | 0 |
| `theories-flocq/SnapRoundingGuardAudit.v` | 5 | 1 | 4 | 0 | 0 |
| `theories-flocq/SnapRoundingScale_b64.v` | 10 | 2 | 8 | 0 | 0 |
| `theories-flocq/SnapRounding_b64.v` | 11 | 2 | 9 | 0 | 0 |
| `theories-flocq/SpectrePassesThroughWitness.v` | 10 | 0 | 10 | 0 | 0 |
| `theories-flocq/TopologicalCorrectness_b64.v` | 5 | 0 | 5 | 0 | 0 |
| `theories-flocq/Validate_binary64.v` | 6 | 5 | 1 | 0 | 0 |
| `theories-flocq/Validate_binary64_bridge.v` | 6 | 3 | 3 | 0 | 0 |
| `theories/AngleBetween.v` | 2 | 0 | 2 | 0 | 0 |
| `theories/ArcArcQuartic.v` | 5 | 4 | 1 | 0 | 0 |
| `theories/ArcArea.v` | 4 | 3 | 0 | 1 | 0 |
| `theories/ArcAreaCentroid.v` | 4 | 2 | 0 | 2 | 0 |
| `theories/ArcCentroid.v` | 4 | 3 | 0 | 1 | 0 |
| `theories/ArcChordLength.v` | 3 | 0 | 3 | 0 | 0 |
| `theories/ArcChordSubdivision.v` | 6 | 2 | 3 | 1 | 0 |
| `theories/ArcLength.v` | 2 | 1 | 0 | 1 | 0 |
| `theories/ArcSpanAtan2.v` | 1 | 0 | 1 | 0 | 0 |
| `theories/ArcSweepCcw.v` | 4 | 0 | 4 | 0 | 0 |
| `theories/Atan2.v` | 2 | 0 | 2 | 0 | 0 |
| `theories/BufferJoin.v` | 7 | 2 | 5 | 0 | 0 |
| `theories/CurveBufferArea.v` | 5 | 4 | 0 | 1 | 0 |
| `theories/InArc.v` | 2 | 0 | 2 | 0 | 0 |
| `theories/InSector.v` | 8 | 0 | 8 | 0 | 0 |
| `theories/RelateArcAnalytic.v` | 5 | 0 | 4 | 0 | 1 |

## 6. What this evidence means for the §7 policy options

- **Option 1** (strict, no concrete-op theorems) would delete 618
  C1 theorems — 62% of the audited surface. The cost the
  policy doc warned about is now quantified.
- **Option 2** (per-theorem registry) would move 622
  entries to a registry while 362 A theorems and (after re-proof)
  up to 18 C2 theorems audit clean. The registry price is now
  known exactly.
- **Option 3** (corrected claim) documents the inheritance; the
  362 A count shows the corpus's own files are far cleaner than
  the file-level list makes them look.

The decision (§8 input 3, README intent) remains the project author's;
inputs 2 and 4 (per-file representative-theorem prose, C# port
dependency audit) remain open.
