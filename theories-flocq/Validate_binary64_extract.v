(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Validate_binary64_extract
   ----------------------------------------------------------------------------
   Native-float OCaml extraction for the RocqRefRunner binary.

   Extracts the RocqRefRunner kernel surface (kernel functions; see the
   single `Extraction` command at the end of this file for the exact list):
   the Phase 0a simplifier, the Phase 0 orientation family (naive, filtered,
   raw determinant, and the exact full-plane sign `b64_orient2d_exact`),
   Phase 1 intersection, Phase 2 snap rounding / hot pixels, the Phase 3
   overlay labelling core, Phase 4 arc predicates, and the Stage D
   expansion building blocks.

   The companion `oracle/driver.ml` dispatches on a mode line on stdin
   (`SIMPLIFY`, `ORIENT`, ...) and routes the rest of the input through the
   appropriate function.  Producing a single binary lets the C# side
   point one env var (`ROCQ_REF_BIN`) at one path for every mode; the same
   extracted symbols are also linked into `libntsrocq` (oracle/nts_ffi.ml)
   for in-process calls.

   IMPORTANT: this extraction is NOT part of the trusted proof base.
   The Coq proofs in `Validate_binary64.v` stay on Flocq's abstract
   `binary_float` model.  Here we override `Binary.Bplus` / `Bminus`
   / `Bmult` / `Bcompare` with native OCaml `+.` / `-.` / `*.` / `=`
   so the extracted code runs at native speed and is bit-equal with
   .NET `double` under the default IEEE 754 binary64 round-to-nearest-
   even rounding mode.

   Caveat (CompCert + Flocq JAR 2015, sec 3.2):
   On a 32-bit OCaml runtime using the x87 FPU, intermediate results
   are sometimes computed in 80-bit precision and rounded twice -- once
   to 80-bit, then again to 64-bit -- which can diverge by a ULP from
   single-rounded binary64.  Modern 64-bit OCaml on x86-64 (SSE2) and
   on ARM64 is safe.  Run the oracle on the same architecture you fuzz
   the C# port on; both .NET and OCaml are configured for SSE2 / NEON
   round-to-nearest-even by default.

   Constructor stubs `failwith` because nothing in the extracted code
   path explicitly constructs a `B754_finite` value -- the function
   only takes binary64 values in and threads them through native ops.
   ========================================================================== *)

From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import Orientation_b64.
From NTS.Proofs.Flocq Require Import Intersect_b64.
From NTS.Proofs.Flocq Require Import Intersect_b64_exact.
From NTS.Proofs       Require Import OverlayGraph.   (* edge_in_result *)
From NTS.Proofs       Require Import CircularCookZ.  (* I_circles_z — integer discriminant *)
From NTS.Proofs       Require Import HausdorffDiscreteQ.  (* q_ddh_sq / q_hsymm_sq — HAUSDORFF_DIRECTED / HAUSDORFF_SYMM exact rationals *)
From NTS.Proofs.Flocq Require Import HotPixel_b64.    (* b64_snap_coord, b64_one/two/half *)
From NTS.Proofs.Flocq Require Import PassesThrough_b64_compute.
From NTS.Proofs.Flocq Require Import InCircle_b64_compute.   (* b64_inCircle *)
From NTS.Proofs.Flocq Require Import ArcLineIntersect_b64_exact. (* b64_arc_line_intersect_point_x/y *)
From NTS.Proofs.Flocq Require Import B64_Pff_bridge.        (* b64_TwoSum *)
From NTS.Proofs.Flocq Require Import B64_FastExpansionSum.  (* b64_grow_expansion_aux *)
From NTS.Proofs.Flocq Require Import ArcCircle_b64_compute.  (* b64_chord_crosses_arc_circle *)
From NTS.Proofs.Flocq Require Import ArcPixel_b64_compute.   (* b64_arc_passes_through_hot_pixel *)
From NTS.Proofs.Flocq Require Import SnapRoundingScale_b64.  (* b64_snap_coord_scaled (C1 power-of-two grid) *)
From NTS.Proofs.Flocq Require Import Orient_b64_exact_full.  (* b64_orient2d_exact (full-plane exact sign) *)
From NTS.Proofs       Require Import ArcSectorExact.  (* asxq_sector: exact arc sector, replaces atan2 *)
From NTS.Proofs.Flocq Require Import B64_SinPoly B64_Sin.  (* b64_sin, sin_accept_b: S2 proved sine *)
From NTS.Proofs.Flocq Require Import B64_CosPoly B64_Cos.  (* b64_cos: S4 proved cosine *)
From NTS.Proofs.Flocq Require Import B64_ArcPoint.  (* b64_arc_x/y, arc_accept_b: S5 arc point *)
From Flocq Require Import IEEE754.Binary.
From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlBasic.

(* Map Flocq's binary_float inductive to OCaml's native float.            *)
(*                                                                       *)
(* Calling convention: Coq's extraction packs multi-arg constructor args *)
(* into a single OCaml tuple before applying the lambda below, AND       *)
(* erases propositional args (`nan_pl ... = true`, `bounded ... = true`).*)
(* So our lambdas take:                                                  *)
(*   B754_zero      -- 1 curried arg  (sign)                             *)
(*   B754_infinity  -- 1 curried arg  (sign)                             *)
(*   B754_nan       -- 1 tuple arg    (sign, pl)                         *)
(*   B754_finite    -- 1 tuple arg    (sign, mantissa, exponent)         *)
(*                                                                       *)
(* These lambdas only fire if extracted code explicitly constructs a    *)
(* binary_float -- which only `default_nan_b64` does, via B754_nan.      *)
(* The B754_finite branch's failwith is dead in the current extraction. *)
Extract Inductive Binary.binary_float => "float" [
  "(fun _s -> 0.0)"
  "(fun s -> if s then neg_infinity else infinity)"
  "(fun (_s, _pl) -> Float.nan)"
  "(fun (_s, _m, _e) -> failwith ""binary_float B754_finite ctor unused at extraction"")"
]
  "(fun _ -> failwith ""binary_float match unused at extraction"")".

(* Native float ops.  Bplus's leading args after extraction are:         *)
(*   prec, emax, nan_pair_to_nan, mode    (then x, y).                   *)
(* The two `Prec_gt_0` / `Prec_lt_emax` propositions Coq extracts as     *)
(* nothing (proof-irrelevant), so the OCaml signature is 4 prep args     *)
(* + 2 operands -- the lambda below MUST have exactly 4 underscores      *)
(* before `x y` or OCaml type-checking fails against the .mli.           *)
Extract Constant Binary.Bplus    => "fun _ _ _ _ x y -> x +. y".
Extract Constant Binary.Bminus   => "fun _ _ _ _ x y -> x -. y".
Extract Constant Binary.Bmult    => "fun _ _ _ _ x y -> x *. y".
Extract Constant Binary.Bdiv     => "fun _ _ _ _ x y -> x /. y".

(* Bcompare's signature is (prec emax x y).  Returns `None` on NaN,      *)
(* matching the Coq semantics that drive `b64_le`'s NaN-safety.          *)
Extract Constant Binary.Bcompare => "fun _ _ x y ->
  if (x <> x) || (y <> y) then None
  else Some (if x < y then Lt else if x > y then Gt else Eq)".

(* `Babs`: native float absolute value.  Three leading args (prec, emax,  *)
(* nan handler) are erased.                                                *)
Extract Constant Binary.Babs => "fun _ _ _ x -> abs_float x".

(* Coq-side numeric constants (`b64_eps`, `b64_three`, `b64_sixteen`)     *)
(* are defined via Flocq's `binary_normalize`, which under extraction     *)
(* eventually reaches the B754_finite constructor stub above.  Override   *)
(* them with native float literals so the OCaml side picks the exact      *)
(* IEEE 754 binary64 values without going through the failwith path.      *)
(* The Coq computation produces the same values, so downstream            *)
(* arithmetic remains coherent.                                            *)
Extract Constant Orientation_b64.b64_three   => "3.0".
Extract Constant Orientation_b64.b64_sixteen => "16.0".
Extract Constant Orientation_b64.b64_eps     => "ldexp 1.0 (-52)".

(* Constants used by the computational Liang-Barsky predicates.  Their Coq    *)
(* bodies go through `binary_normalize`, which under extraction reaches the    *)
(* B754_finite constructor stub above; override with the exact binary64        *)
(* literals (same pattern as b64_three / b64_sixteen / b64_eps).               *)
Extract Constant HotPixel_b64.b64_one  => "1.0".
Extract Constant HotPixel_b64.b64_two  => "2.0".
Extract Constant HotPixel_b64.b64_half => "0.5".

(* min/max: select an operand.  Map to OCaml's Float.min / Float.max so the    *)
(* extracted t-interval clamp is bit-identical to the previous hand-rolled     *)
(* driver (which used Float.min / Float.max).  On the finite t-bounds reached  *)
(* here these agree with the Coq `if b64_le .. then .. else ..` bodies.        *)
Extract Constant PassesThrough_b64_compute.b64_min => "Float.min".
Extract Constant PassesThrough_b64_compute.b64_max => "Float.max".

(* b64_snap_coord = Bnearbyint mode_NE (round half to even).  Its Coq body     *)
(* constructs binary_floats (B754_finite stub); override with the native       *)
(* round-half-to-even (OCaml 4.14 Float.round is half-AWAY-from-zero, so we     *)
(* implement ties-to-even via floor + parity, exactly as the old driver did).  *)
Extract Constant HotPixel_b64.b64_snap_coord =>
  "(fun x ->
      if x <> x then x
      else if x = infinity || x = neg_infinity then x
      else
        let f = Float.floor x in
        let d = x -. f in
        if d < 0.5 then f
        else if d > 0.5 then f +. 1.0
        else if Float.rem f 2.0 = 0.0 then f else f +. 1.0)".

(* --- Exact full-plane orientation (Orient_b64_exact_full.v) -------------- *)
(* `b64_orient2d_exact` is Z-valued integer arithmetic all the way down       *)
(* (min-exponent alignment, shifted mantissas, a 2x2 integer determinant,     *)
(* Z.sgn), so the whole computation extracts as VERIFIED code over the Coq    *)
(* `z`/`positive` representation -- arbitrary precision by construction, no   *)
(* zarith dependency.  The only parts that cannot extract are the two decode  *)
(* projections `b64_mant` / `b64_exp`: they pattern-match on Flocq's          *)
(* `binary_float`, which this file maps to native `float` (the match stub     *)
(* faults).  Override them with an IEEE 754 bit-level decode that lands on    *)
(* exactly the Flocq `B754_finite` canonical pair:                            *)
(*                                                                            *)
(*   normal    (biased in 1..2046): mant = +/-(2^52 + frac), exp = biased-1075 *)
(*   subnormal (biased = 0, frac<>0): mant = +/-frac,        exp = -1074      *)
(*   zero / infinity / NaN:           mant = 0,              exp = 0          *)
(*                                                                            *)
(* The zero/inf/NaN row is the Coq catch-all (`| _ => 0%Z`).  These two       *)
(* overrides are the unverified surface of the exact path (they are glue,     *)
(* like Bplus above); everything downstream of them is extracted from the     *)
(* Qed-closed development, and `oracle/gen_ffi_parity_tests.py` gates the     *)
(* extracted sign against the independent zarith re-implementation in         *)
(* `oracle/driver.ml` (ORIENT_EXACT) case for case.                           *)
Extract Constant Orient_b64_exact_full.b64_mant =>
"(fun x ->
    if x <> x || x = infinity || x = neg_infinity || x = 0.0 then Z0
    else
      let bits = Int64.bits_of_float x in
      let frac = Int64.logand bits 0xFFFFFFFFFFFFFL in
      let biased =
        Int64.to_int (Int64.logand (Int64.shift_right_logical bits 52) 0x7FFL) in
      let m =
        if biased = 0 then frac else Int64.logor frac 0x10000000000000L in
      let rec pos_of (n : int64) =
        if Int64.equal n 1L then XH
        else
          let q = pos_of (Int64.shift_right_logical n 1) in
          if Int64.equal (Int64.logand n 1L) 1L then XI q else XO q
      in
      if Int64.compare bits 0L < 0 then Zneg (pos_of m) else Zpos (pos_of m))".

Extract Constant Orient_b64_exact_full.b64_exp =>
"(fun x ->
    if x <> x || x = infinity || x = neg_infinity || x = 0.0 then Z0
    else
      let bits = Int64.bits_of_float x in
      let biased =
        Int64.to_int (Int64.logand (Int64.shift_right_logical bits 52) 0x7FFL) in
      let e = if biased = 0 then (-1074) else biased - 1075 in
      let rec pos_of n =
        if n = 1 then XH
        else
          let q = pos_of (n lsr 1) in
          if n land 1 = 1 then XI q else XO q
      in
      if e = 0 then Z0
      else if e > 0 then Zpos (pos_of e)
      else Zneg (pos_of (-e)))".

(* BEGIN b64_sin constants: generated by tests/B64SinConformance/gen_constants.py *)
(* from the B754_finite literals; exact hex floats (the literal ctor is a stub). *)
Extract Constant B64_SinPoly.sp_c0 => "(0x1.0000000000000p+0)".
Extract Constant B64_SinPoly.sp_c1 => "(-0x1.5555555555555p-3)".
Extract Constant B64_SinPoly.sp_c2 => "(0x1.1111111111111p-7)".
Extract Constant B64_SinPoly.sp_c3 => "(-0x1.a01a01a01a01ap-13)".
Extract Constant B64_SinPoly.sp_c4 => "(0x1.71de3a556c734p-19)".
Extract Constant B64_SinPoly.sp_c5 => "(-0x1.ae64567f544e4p-26)".
Extract Constant B64_SinPoly.sp_c6 => "(0x1.6124613a86d09p-33)".
Extract Constant B64_SinPoly.sp_c7 => "(-0x1.ae7f3e733b81fp-41)".
Extract Constant B64_SinPoly.sp_c8 => "(0x1.952c77030ad4ap-49)".
Extract Constant B64_SinPoly.sp_c9 => "(-0x1.2f49b46814157p-57)".
Extract Constant B64_SinPoly.sp_c10 => "(0x1.71b8ef6dcf572p-66)".
Extract Constant B64_CosPoly.cq_c0 => "(0x1.0000000000000p+0)".
Extract Constant B64_CosPoly.cq_c1 => "(-0x1.0000000000000p-1)".
Extract Constant B64_CosPoly.cq_c2 => "(0x1.5555555555555p-5)".
Extract Constant B64_CosPoly.cq_c3 => "(-0x1.6c16c16c16c17p-10)".
Extract Constant B64_CosPoly.cq_c4 => "(0x1.a01a01a01a01ap-16)".
Extract Constant B64_CosPoly.cq_c5 => "(-0x1.27e4fb7789f5cp-22)".
Extract Constant B64_CosPoly.cq_c6 => "(0x1.1eed8eff8d898p-29)".
Extract Constant B64_CosPoly.cq_c7 => "(-0x1.93974a8c07c9dp-37)".
Extract Constant B64_CosPoly.cq_c8 => "(0x1.ae7f3e733b81fp-45)".
Extract Constant B64_CosPoly.cq_c9 => "(-0x1.6827863b97d97p-53)".
Extract Constant B64_CosPoly.cq_c10 => "(0x1.e542ba4020225p-62)".
Extract Constant B64_CosPoly.cq_c11 => "(-0x1.0ce396db7f853p-70)".
Extract Constant B64_Sin.sn_C1 => "(0x1.921fb54442d18p+1)".
Extract Constant B64_Sin.sn_C2 => "(0x1.1a62633145c07p-53)".
Extract Constant B64_Sin.sn_one => "(0x1.0000000000000p+0)".
Extract Constant B64_Sin.sn_two => "(0x1.0000000000000p+1)".
Extract Constant B64_Sin.sn_three => "(0x1.8000000000000p+1)".
Extract Constant B64_Sin.sn_T1 => "(0x1.9240000000000p+0)".
Extract Constant B64_Sin.sn_T3 => "(0x1.2d80000000000p+2)".
Extract Constant B64_Sin.sn_T5 => "(0x1.f680000000000p+2)".
Extract Constant B64_Sin.sn_ten => "(0x1.4000000000000p+3)".
Extract Constant B64_Sin.sn_mten => "(-0x1.4000000000000p+3)".
Extract Constant B64_ArcPoint.ap_cap => "(0x1.0000000000000p+998)".
Extract Constant B64_ArcPoint.ap_mcap => "(-0x1.0000000000000p+998)".
(* END b64_sin constants *)

Extraction Language OCaml.

(* Write the extracted code to `oracle/extracted.ml` (relative to the    *)
(* project root, which is the cwd of the makefile).  The driver in      *)
(* `oracle/driver.ml` consumes the extracted module.                     *)
(*                                                                       *)
(* All RocqRefRunner-facing functions are listed in one call so the      *)
(* dependency closure (BPoint, binary64, b64_le, b64_cross, ...) is      *)
(* emitted exactly once.                                                  *)
Extraction "oracle/extracted.ml"
  greedy_simplify_perp_b64
  b64_orient2d
  b64_orient_sign_naive
  b64_orient_sign_filtered
  b64_intersect_sign_filtered
  b64_intersect_point
  b64_intersect_point_x
  b64_intersect_point_y
  edge_in_result
  b64_passes_through_hot_pixel_compute
  b64_passes_through_hot_pixel_halfopen_compute
  b64_inCircle
  b64_arc_line_intersect_point_x
  b64_arc_line_intersect_point_y
  b64_chord_crosses_arc_circle
  b64_arc_passes_through_hot_pixel
  b64_TwoSum
  b64_grow_expansion_aux
  b64_snap_coord_scaled
  b64_orient2d_exact
  I_circles_z
  q_ddh_sq
  q_hsymm_sq
  asxq_sector
  b64_sin
  b64_cos
  sin_accept_b
  b64_arc_x
  b64_arc_y
  arc_accept_b.
