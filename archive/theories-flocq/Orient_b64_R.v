(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Orient_b64_R
   ----------------------------------------------------------------------------
   R-side arithmetic identities for `b64_orient2d`, proved via composition of
   the per-op correctness lifts in `B64_bridge.v`.

   PROOF STATUS
   ============
   In this file (general safe-magnitude regime, `b64_orient2d_safe`):
     - `b64_orient2d_safe P0 P1 Q`         -- bundled no-overflow precondition
                                              for one call to `b64_orient2d`.
     - `b64_orient2d_inputs_safe`          -- magnitude-bounded interface
                                              (Flavour B): `|coord| <= 2^500`
                                              per input + the chain helper
                                              `b64_orient2d_inputs_safe_imp_safe`
                                              that discharges all seven
                                              `b64_safe` premises.
     - `b64_orient2d_antisymmetric_R`      -- swap-args negation.
     - `b64_orient2d_at_P0_R`              -- vertex coincidence Q = P0.
     - `b64_orient2d_at_P1_R`              -- vertex coincidence Q = P1.
     - `b64_orient2d_at_P0_eq_P1_R`        -- degenerate base P0 = P1.

   In `Orient_b64_exact.v` (integer regime, `orient2d_inputs_int_safe`,
   `|coord| <= 2^25` integer-valued):
     - `b64_orient2d_exact_for_small_int`  -- `B2R det = cross_R_BP` on the
                                              nose (bit-exact in the regime).
     - `b64_orient_sign_filtered_sound_small_int`
                                           -- cross_R-valued soundness.
     - `b64_orient2d_cyclic_int_R`, `_cyclic2_int_R`
                                           -- both non-trivial cyclic
                                              permutations.
     - `b64_orient2d_translation_int_R`    -- invariance under integer-valued
                                              translation by (vx, vy).

   So the three classic identities (antisymmetry / cyclic permutation /
   translation invariance) are all complete: antisymmetry in this file
   under the general safe regime, cyclic and translation in
   `Orient_b64_exact.v` under the integer regime.  The general-magnitude
   cyclic/translation cases remain open and would need the same
   forward-error machinery the strategy doc demoted from critical path.

   Why those general-regime cases stay open: the two `b64_orient2d` calls
   in cyclic permutation compute *different* intermediate `b64_minus` and
   `b64_mult` values; lifting via `b64_*_correct` produces nested
   `b64_round(b64_round(...) * b64_round(...))` terms that aren't
   syntactically equal.  In R-arithmetic both identities hold by `ring`;
   in binary64 the accumulated rounding errors don't structurally cancel.
   The integer regime sidesteps the issue entirely by making every
   `b64_round` invocation exact.

   CHORD-PARADIGM SCOPE
   ====================
   Every identity in this file -- antisymmetry, cyclic permutation,
   translation invariance, vertex coincidence -- holds for *chords*: the
   three `BPoint` arguments name a straight triangle, and `cross_R_BP`
   computes its signed area.  See `docs/audit-phase4-curves.md` for the
   strategic stance.  An arc-aware variant (arc-arc orientation, arc-
   point orientation) would live in a parallel `Orient_arc_R.v` with
   its own carrier (e.g. `ArcTriplet` = 3 control points per arc) and
   its own R-side witness; the lemmas here would *not* generalise
   without re-proof.  See the dovetail block at the foot of
   `Orient_b64_exact.v` for the full anticipatory plan.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import Core.

From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import Orientation_b64.
From NTS.Proofs.Flocq Require Import B64_bridge.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* `b64_orient2d_safe P0 P1 Q` -- the seven no-overflow obligations for one   *)
(* call to `b64_orient2d`, one per sub-operation, packaged as a single Prop. *)
(* -------------------------------------------------------------------------- *)

Definition b64_orient2d_safe (P0 P1 Q : BPoint) : Prop :=
  let dx1 := b64_minus (bx P1) (bx P0) in
  let dy1 := b64_minus (by_ Q)  (by_ P0) in
  let dx2 := b64_minus (bx Q)   (bx P0) in
  let dy2 := b64_minus (by_ P1) (by_ P0) in
  let t1  := b64_mult dx1 dy1 in
  let t2  := b64_mult dx2 dy2 in
  b64_safe Rminus (bx P1) (bx P0) /\
  b64_safe Rminus (by_ Q)  (by_ P0) /\
  b64_safe Rminus (bx Q)   (bx P0) /\
  b64_safe Rminus (by_ P1) (by_ P0) /\
  b64_safe Rmult  dx1 dy1 /\
  b64_safe Rmult  dx2 dy2 /\
  b64_safe Rminus t1 t2.

(* -------------------------------------------------------------------------- *)
(* Antisymmetry on the R-side.                                                *)
(*                                                                            *)
(* The two calls `b64_orient2d P0 P1 Q` and `b64_orient2d P0 Q P1` share      *)
(* identical intermediate binary64 values (`dx1`, `dy1`, `dx2`, `dy2`, `t1`,  *)
(* `t2`) -- the only difference is the order of arguments to the outermost   *)
(* `b64_minus`.  At the R-level, `round_NE` is symmetric under negation, so  *)
(* the two R-valued results are exact negatives of each other under the      *)
(* no-overflow preconditions.                                                 *)
(* -------------------------------------------------------------------------- *)

Theorem b64_orient2d_antisymmetric_R :
  forall P0 P1 Q : BPoint,
    b64_orient2d_safe P0 P1 Q ->
    b64_orient2d_safe P0 Q  P1 ->
    Binary.B2R prec emax (b64_orient2d P0 P1 Q)
      = - Binary.B2R prec emax (b64_orient2d P0 Q P1).
Proof.
  intros P0 P1 Q Hsafe1 Hsafe2.
  (* Unpack the seventh conjuncts -- the only ones we need for the proof,    *)
  (* since the outer b64_minus is the only operation whose B2R we compute.   *)
  destruct Hsafe1 as (_ & _ & _ & _ & _ & _ & Sdet1).
  destruct Hsafe2 as (_ & _ & _ & _ & _ & _ & Sdet2).
  (* `b64_orient2d` is defined as `let (t1, t2) := b64_orient2d_terms ... in *)
  (* b64_minus t1 t2`.  Unfold both layers and reduce the let so the goal   *)
  (* contains the same concrete `b64_minus` form that `Sdet1` / `Sdet2`     *)
  (* talk about.                                                             *)
  unfold b64_orient2d, Orientation_b64.b64_orient2d_terms.
  cbn iota.
  (* Lift each outer subtraction to R via b64_minus_correct. *)
  pose proof (b64_minus_correct _ _ Sdet1) as [Hdet1 _].
  pose proof (b64_minus_correct _ _ Sdet2) as [Hdet2 _].
  rewrite Hdet1, Hdet2.
  (* Goal: `round (a - b) = - round (b - a)` for a, b being the two t-values. *)
  (* Pull the negation inside the rounding via `round_NE_opp` (RTL), then    *)
  (* simplify `-(b - a)` to `a - b`.                                         *)
  rewrite <- round_NE_opp.
  rewrite Ropp_minus_distr.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Magnitude-bounded interface (Flavour B).                                  *)
(*                                                                            *)
(* `b64_orient2d_inputs_safe P0 P1 Q` packages the six coord-magnitude       *)
(* obligations (one per coordinate of the three input points) that suffice   *)
(* to discharge every `b64_safe` premise in `b64_orient2d_safe`.  The bound *)
(* `2^500` is comfortably below the overflow threshold; intermediate ops    *)
(* in the orient2d chain go up to ~`2^1003`, still below `2^1024`.           *)
(* -------------------------------------------------------------------------- *)

Definition b64_orient2d_inputs_safe (P0 P1 Q : BPoint) : Prop :=
  b64_coord_safe (bx P0)  /\
  b64_coord_safe (by_ P0) /\
  b64_coord_safe (bx P1)  /\
  b64_coord_safe (by_ P1) /\
  b64_coord_safe (bx Q)   /\
  b64_coord_safe (by_ Q).

Theorem b64_orient2d_inputs_safe_imp_safe :
  forall P0 P1 Q : BPoint,
    b64_orient2d_inputs_safe P0 P1 Q ->
    b64_orient2d_safe P0 P1 Q.
Proof.
  intros P0 P1 Q (HxP0 & HyP0 & HxP1 & HyP1 & HxQ & HyQ).
  unfold b64_orient2d_safe.
  (* The four coordinate-difference safe predicates come straight from      *)
  (* `b64_safe_minus_of_bounded` on each pair.                              *)
  split; [apply b64_safe_minus_of_bounded; assumption|].
  split; [apply b64_safe_minus_of_bounded; assumption|].
  split; [apply b64_safe_minus_of_bounded; assumption|].
  split; [apply b64_safe_minus_of_bounded; assumption|].
  (* The two product safe predicates use `b64_mult_bounded_R`'s precondition:
     each operand is the result of a coord-safe minus, hence bounded by
     `bpow 501` and finite.                                                  *)
  destruct (b64_minus_bounded_R _ _ HxP1 HxP0) as [Bdx1 Fdx1].
  destruct (b64_minus_bounded_R _ _ HyQ  HyP0) as [Bdy1 Fdy1].
  destruct (b64_minus_bounded_R _ _ HxQ  HxP0) as [Bdx2 Fdx2].
  destruct (b64_minus_bounded_R _ _ HyP1 HyP0) as [Bdy2 Fdy2].
  split.
  { (* b64_safe Rmult dx1 dy1 *)
    assert (Hsafe : b64_safe Rmult
                      (b64_minus (bx P1) (bx P0))
                      (b64_minus (by_ Q) (by_ P0))).
    { repeat split; try assumption.
      apply (Rle_lt_trans _ (bpow radix2 1002)).
      - apply b64_round_abs_le_bpow; [unfold emax; lia |].
        rewrite Rabs_mult.
        replace 1002%Z with (501 + 501)%Z by lia.
        rewrite bpow_plus.
        apply Rmult_le_compat; try apply Rabs_pos; assumption.
      - apply bpow_lt. unfold emax. lia. }
    exact Hsafe. }
  split.
  { (* b64_safe Rmult dx2 dy2 *)
    assert (Hsafe : b64_safe Rmult
                      (b64_minus (bx Q) (bx P0))
                      (b64_minus (by_ P1) (by_ P0))).
    { repeat split; try assumption.
      apply (Rle_lt_trans _ (bpow radix2 1002)).
      - apply b64_round_abs_le_bpow; [unfold emax; lia |].
        rewrite Rabs_mult.
        replace 1002%Z with (501 + 501)%Z by lia.
        rewrite bpow_plus.
        apply Rmult_le_compat; try apply Rabs_pos; assumption.
      - apply bpow_lt. unfold emax. lia. }
    exact Hsafe. }
  (* Final outer subtraction: both products are bounded by bpow 1002 and    *)
  (* finite.                                                                *)
  destruct (b64_mult_bounded_R _ _ Fdx1 Fdy1 Bdx1 Bdy1) as [Bt1 Ft1].
  destruct (b64_mult_bounded_R _ _ Fdx2 Fdy2 Bdx2 Bdy2) as [Bt2 Ft2].
  apply (b64_safe_minus_of_products_bounded _ _ Ft1 Ft2 Bt1 Bt2).
Qed.

(* -------------------------------------------------------------------------- *)
(* Vertex coincidence: Q = P0.                                                *)
(*                                                                            *)
(* Mirrors `cross_at_P0_is_collinear` from the R-side `Orientation.v`.  In   *)
(* binary64 the identity is genuine (not a rounded approximation): every     *)
(* product collapses to 0 because one factor is the "self minus" subtraction *)
(* `b64_minus z z` whose B2R is exactly 0.  The outer subtraction is then    *)
(* `0 - 0 = 0`.                                                               *)
(*                                                                            *)
(* Preconditions are `b64_safe Rminus` on the two non-self subtractions      *)
(* (`bx P1 - bx P0`, `by_ P1 - by_ P0`).  Those are the only ones whose      *)
(* magnitude is not trivially zero -- they need a no-overflow guard for the  *)
(* downstream `b64_mult` to be finite.  The other five `b64_safe`-style      *)
(* obligations in the full `b64_orient2d_safe` are trivially discharged when *)
(* Q = P0 (everything is `round 0 = 0`).                                     *)
(* -------------------------------------------------------------------------- *)

Theorem b64_orient2d_at_P0_R :
  forall P0 P1 : BPoint,
    b64_safe Rminus (bx P1) (bx P0) ->
    b64_safe Rminus (by_ P1) (by_ P0) ->
    Binary.B2R prec emax (b64_orient2d P0 P1 P0) = 0.
Proof.
  intros P0 P1 Hdx Hdy.
  pose proof Hdx as Hdx'.  (* keep an unbroken copy for b64_minus_correct *)
  pose proof Hdy as Hdy'.
  destruct Hdx as (FxP1 & FxP0 & _).
  destruct Hdy as (FyP1 & FyP0 & _).
  unfold b64_orient2d, Orientation_b64.b64_orient2d_terms.
  cbn iota.
  (* Self-minus on by_ P0 and bx P0 both give R-zero, finite results. *)
  pose proof (b64_minus_self_R (by_ P0) FyP0) as Hdy1_R.
  pose proof (b64_minus_self_finite (by_ P0) FyP0) as Fdy1.
  pose proof (b64_minus_self_R (bx P0)  FxP0) as Hdx2_R.
  pose proof (b64_minus_self_finite (bx P0)  FxP0) as Fdx2.
  (* Non-self subtractions: finiteness comes from the bridge under the safe  *)
  (* premises accepted as theorem hypotheses.                                 *)
  pose proof (b64_minus_correct _ _ Hdx') as [_ Fdx1].
  pose proof (b64_minus_correct _ _ Hdy') as [_ Fdy2].
  (* Two products: each has an R-zero factor, so B2R = 0 and finite. *)
  pose proof (b64_mult_zero_r_R _ _ Fdx1 Fdy1 Hdy1_R) as Ht1_R.
  pose proof (b64_mult_zero_r_finite _ _ Fdx1 Fdy1 Hdy1_R) as Ft1.
  pose proof (b64_mult_zero_l_R _ _ Fdx2 Fdy2 Hdx2_R) as Ht2_R.
  pose proof (b64_mult_zero_l_finite _ _ Fdx2 Fdy2 Hdx2_R) as Ft2.
  (* Outer b64_minus on two R-zero finite values: B2R = 0. *)
  apply (b64_minus_zeros_R _ _ Ft1 Ft2 Ht1_R Ht2_R).
Qed.

(* -------------------------------------------------------------------------- *)
(* Vertex coincidence: Q = P1.                                                *)
(*                                                                            *)
(* When Q = P1, both `b64_orient2d_terms` components share the same           *)
(* expression -- `b64_mult (b64_minus (bx P1) (bx P0)) (b64_minus (by_ P1)    *)
(* (by_ P0))` -- so the outer subtraction is `b64_minus t t`, which is        *)
(* exactly zero by `b64_minus_self_R`.  Single premise: the product is       *)
(* safe (which, via `b64_mult_correct`, gives the finiteness needed for       *)
(* `b64_minus_self_R`).                                                       *)
(* -------------------------------------------------------------------------- *)

Theorem b64_orient2d_at_P1_R :
  forall P0 P1 : BPoint,
    b64_safe Rmult (b64_minus (bx P1) (bx P0))
                   (b64_minus (by_ P1) (by_ P0)) ->
    Binary.B2R prec emax (b64_orient2d P0 P1 P1) = 0.
Proof.
  intros P0 P1 Hprod.
  pose proof (b64_mult_correct _ _ Hprod) as [_ Fprod].
  unfold b64_orient2d, Orientation_b64.b64_orient2d_terms.
  cbn iota.
  apply b64_minus_self_R.
  exact Fprod.
Qed.

(* -------------------------------------------------------------------------- *)
(* Degenerate base: P0 = P1.                                                  *)
(*                                                                            *)
(* When the two "base" points coincide, the first factor of `t1`              *)
(* (`b64_minus (bx P1) (bx P0)` with P1 = P0) and the second factor of `t2`   *)
(* (`b64_minus (by_ P1) (by_ P0)` with P1 = P0) are both self-subtractions,   *)
(* whose `B2R` is exactly zero.  Each product then collapses via              *)
(* `b64_mult_zero_l_R` / `b64_mult_zero_r_R`, and the outer subtraction is    *)
(* `0 - 0 = 0`.  Mirrors `b64_orient2d_at_P0_R`'s structure, modulo which     *)
(* factor of each product carries the zero.                                   *)
(* -------------------------------------------------------------------------- *)

Theorem b64_orient2d_at_P0_eq_P1_R :
  forall P Q : BPoint,
    b64_safe Rminus (bx Q)  (bx P) ->
    b64_safe Rminus (by_ Q) (by_ P) ->
    Binary.B2R prec emax (b64_orient2d P P Q) = 0.
Proof.
  intros P Q Hdx Hdy.
  pose proof Hdx as Hdx'.
  pose proof Hdy as Hdy'.
  destruct Hdx as (FxQ & FxP & _).
  destruct Hdy as (FyQ & FyP & _).
  unfold b64_orient2d, Orientation_b64.b64_orient2d_terms.
  cbn iota.
  (* Self subtractions on (bx P) and (by_ P): R-zero, finite. *)
  pose proof (b64_minus_self_R (bx P) FxP) as Hdx1_R.
  pose proof (b64_minus_self_finite (bx P) FxP) as Fdx1.
  pose proof (b64_minus_self_R (by_ P) FyP) as Hdy2_R.
  pose proof (b64_minus_self_finite (by_ P) FyP) as Fdy2.
  (* Non-self subtractions: finiteness from b64_minus_correct. *)
  pose proof (b64_minus_correct _ _ Hdy') as [_ Fdy1].
  pose proof (b64_minus_correct _ _ Hdx') as [_ Fdx2].
  (* t1 = b64_mult (zero-left) (...)  ->  zero. *)
  pose proof (b64_mult_zero_l_R _ _ Fdx1 Fdy1 Hdx1_R) as Ht1_R.
  pose proof (b64_mult_zero_l_finite _ _ Fdx1 Fdy1 Hdx1_R) as Ft1.
  (* t2 = b64_mult (...) (zero-right) ->  zero. *)
  pose proof (b64_mult_zero_r_R _ _ Fdx2 Fdy2 Hdy2_R) as Ht2_R.
  pose proof (b64_mult_zero_r_finite _ _ Fdx2 Fdy2 Hdy2_R) as Ft2.
  apply (b64_minus_zeros_R _ _ Ft1 Ft2 Ht1_R Ht2_R).
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                              *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_orient2d_antisymmetric_R.
Print Assumptions b64_orient2d_inputs_safe_imp_safe.
Print Assumptions b64_orient2d_at_P0_R.
Print Assumptions b64_orient2d_at_P1_R.
Print Assumptions b64_orient2d_at_P0_eq_P1_R.
