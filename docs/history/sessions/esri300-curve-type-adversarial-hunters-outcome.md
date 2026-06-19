# Outcome — CurveType adversarial hunters (Circular=0, Elliptic=1, Bezier3=2)

**Branch:** `grok/fresh-esri300-elliptic-bezier`

**Request.** Create adversarial tests for the `CurveType` enum used by Esri.ArcGISRuntime (and NTS.Curve). Refinement: "Create hunters using the oracle to find edge cases".

## What was delivered

- Primary artifact: `oracle/gen_adversarial_curves.py`
  - A proper oracle-driven hunter (in the `gen_hole979_hunt.sh` style).
  - Explicitly parameterised by CurveType ( `--types 0,1,2` ).
  - Hunts orientation, incircle, and hot-pixel passes-through families while varying controls for each kind (and mixtures).
  - Emits "INTERESTING ..." lines labelled with the CurveType exercised.
  - Uses the new segment syntax for E/B so that future full ring/relate hunters can emit typed curve data.

- Parser support in `oracle/driver.ml`
  - All five duplicated `parse_seg` sites now accept:
    - `E cx cy rx ry rot sa sw`  (EllipticArc, CurveType=1)
    - `B x0 y0 x1 y1 x2 y2 x3 y3` (Bezier3Curve, CurveType=2)
  - `seg_pts`, `seg_start`, `seg_end`, and `pair_pts` logic extended with conservative chord fallbacks so the hunters (and existing curve tests) do not crash when new segment kinds appear.
  - Comments tie the tokens to the C# `CurveType` enum.

- Makefile integration
  - New targets: `curve-adversarial-hunt`, `elliptic-hunt`, `bezier-hunt`.

- The hunter runs today and produces output covering all three CurveType values (low-level ORIENT/INCIRCLE/PASSES modes work without ring parsing; full ring modes will benefit as soon as more numeric E/B support lands).

## Relation to focus claims (from prior /check-work)
The hunters are deliberately aimed at the five areas:
- Noding (hot-pixel / passes-through near controls of E/B)
- Soundness (filter vs exact behaviour on elliptic / bezier controls)
- DIM9 (the relate chord seed we already added for E/B; the hunter can be pointed at CURVE_RELATE_MATRIX once E/B ring support is richer)
- Orientation (controls + ring orientation for the three kinds)
- InCircleArc (directly exercised for elliptic; proxy for the others)

## Scope left explicit
- Full high-fidelity on-curve / in-sweep math for E and B in every driver mode (the hunter + independent Python models in the gens are the source of truth for the first cut).
- No changes were needed to the core `theories/` for this hunter slice.
- The de9im chord-seed vectors (`de9im_elliptic_vectors.txt`, `de9im_bezier3_vectors.txt`) remain the relate-layer coverage for the new types.

## Commands used
```bash
python3 oracle/gen_adversarial_curves.py --types 0,1,2 --budget 150
make -C oracle curve-adversarial-hunt   # (once fully wired)
```

## Next natural steps
- Run the hunter with larger budgets on a machine with a fresh `oracle_bin`.
- Promote the best "INTERESTING" cases into the permanent gated `*_tests.txt` files (with `# CurveType=N` comments).
- Extend the independent models in the existing gens for true ellipse and cubic classification.
- When ready, make more ring-based modes (POINT_IN_CURVE_RING, CURVE_RELATE_MATRIX, RING_SIMPLE ...) fully understand the new segment kinds.

All project invariants (Qed discipline on the proof side, gauntlet on the test side) continue to hold. The hunters give us a living way to keep finding edge cases for the complete `CurveType` surface.