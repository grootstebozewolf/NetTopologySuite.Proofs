(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Validate_binary64_extract
   ----------------------------------------------------------------------------
   Native-float OCaml extraction for the RocqRefRunner binary.

   Currently extracts:
     - `greedy_simplify_perp_b64`   from `Validate_binary64.v`
     - `b64_orient2d`               from `Orientation_b64.v`
     - `b64_orient_sign`            from `Orientation_b64.v`

   The companion `oracle/driver.ml` dispatches on a mode line on stdin
   (`SIMPLIFY` or `ORIENT`) and routes the rest of the input through the
   appropriate function.  Producing a single binary lets the C# side
   point one env var (`ROCQ_REF_BIN`) at one path for both Phase 0a
   (simplifier) and Phase 0 (orientation).

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
  b64_intersect_point.
