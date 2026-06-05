(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Validate_binary64_bridge
   ----------------------------------------------------------------------------
   The R-bridge for the binary64 simplifier in `Validate_binary64.v`.

   Splits the soundness obligations of the binary64 simplifier from the
   computational + structural layer, so the structural file does not have
   to pay the four Stdlib classical-reals axioms unless the soundness
   surface is actually consumed.

   PROOF STATUS (this slice)
   =========================
   This slice ships the R-projection wrappers and the per-operation R-side
   bridges in the *integer regime* (every coordinate is an integer-valued
   binary64 with `|coord| <= 2^25`).  In that regime every intermediate
   value in `b64_cross` and `b64_dist_sq` stays inside binary64's 53-bit
   exact-integer window, so rounding never has anything to round and the
   R-side identity holds on the nose.

   Building blocks shipped here:

     - `B2R_bp`           -- BPoint -> Point (R-side projection of one
                             point).
     - `map_B2R_bp`       -- list BPoint -> list Point.
     - `is_finite_bp`     -- both coords are `is_finite` binary64s.
     - `point_int_safe`   -- both coords are `coord_int_safe` (integer-
                             valued binary64 with `|coord| <= 2^25`).
     - `points_int_safe`  -- `Forall point_int_safe` on a list.
     - `dist_sq_R_BP`     -- the R-side squared-distance witness, mirroring
                             `Distance.dist_sq` lifted across `B2R_bp`.
     - `dist_sq_inputs_int_safe`
                          -- the two-input regime predicate.

   Theorems shipped here:

     - `map_B2R_bp_nil`, `map_B2R_bp_cons`
                          -- structural: `map_B2R_bp` commutes with the
                             list constructors.
     - `b64_cross_eq_b64_orient2d`
                          -- the connector lemma: `b64_cross` and
                             `b64_orient2d` are definitionally equal.
                             Both compute the same cross-product formula;
                             `b64_orient2d` factors via an internal
                             `b64_orient2d_terms` let-pair, `b64_cross`
                             does not -- but the final binary64 result
                             is the same and `simpl` discharges the
                             defeq.
     - `b64_cross_exact_for_small_int`
                          -- under `orient2d_inputs_int_safe`,
                             `B2R (b64_cross p0 p1 q) = cross_R_BP p0 p1 q`.
                             Corollary of
                             `b64_orient2d_exact_for_small_int` via the
                             connector lemma.
     - `b64_dist_sq_exact_for_small_int`
                          -- under `dist_sq_inputs_int_safe p q`,
                             `B2R (b64_dist_sq p q) = dist_sq_R_BP p q`.
                             The first dist_sq-specific exactness result
                             in the corpus.  Mirrors the orient2d proof
                             but is structurally simpler: outer op is
                             addition rather than subtraction, and both
                             inner products are squares of the same
                             differences.

   What is *not* shipped (deferred to follow-up slices)
   ----------------------------------------------------
     - The headline `greedy_simplify_perp_b64` soundness theorem:
       relating
         simp_star_perp (B2R eps) (map_B2R_bp pts)
                                  (map_B2R_bp (greedy_simplify_perp_b64
                                                 eps pts))
       under a list-level safety predicate.  Requires inducting over the
       Fixpoint and bridging the binary64 perpendicular-distance check
       (`b64_le (b64_mult c c) (b64_mult (b64_mult eps eps) dist_sq)`)
       to the R-side check
         (cross_R_BP)^2 <= (B2R eps)^2 * dist_sq_R_BP
       step by step.  This slice prepares the building blocks; the
       headline is the next slice's target.
     - Forward-error / round-chain identity outside the integer regime.
       Same story as `Orient_b64_R.v` / `Orient_b64_exact.v`: the
       general-magnitude regime requires Stage B/C/D forward-error
       scaffolding, demoted from critical path on 2026-05-15.
     - `is_finite_bp` consequences (every operation chain stays finite
       under suitable safety predicates).  Trivially derivable from
       `b64_*_correct`'s second projection but deferred until a downstream
       consumer needs it.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Lra.
From Stdlib Require Import List.
Import ListNotations.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Flocq Require Import Core.

From NTS.Proofs        Require Import Distance.
From NTS.Proofs        Require Import Orientation.
From NTS.Proofs.Flocq  Require Import Validate_binary64.
From NTS.Proofs.Flocq  Require Import Orientation_b64.
From NTS.Proofs.Flocq  Require Import B64_bridge.
From NTS.Proofs.Flocq  Require Import B64_lib.
From NTS.Proofs.Flocq  Require Import Orient_b64_R.
From NTS.Proofs.Flocq  Require Import Orient_b64_sound.
From NTS.Proofs.Flocq  Require Import Orient_b64_exact.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* R-projection wrappers.                                                     *)
(* -------------------------------------------------------------------------- *)

(** Project a `BPoint` to its R-valued `Point`.  Records have distinct      *)
(** field names so no implicit coercion exists; this lift is explicit.      *)
Definition B2R_bp (p : BPoint) : Point :=
  mkPoint (Binary.B2R prec emax (bx p))
          (Binary.B2R prec emax (by_ p)).

(** Pointwise lift to lists.  Implemented in terms of `List.map` so the    *)
(** standard list lemmas (`map_nil`, `map_cons`, `map_length`, ...) are     *)
(** directly applicable.                                                    *)
Definition map_B2R_bp (pts : list BPoint) : list Point :=
  map B2R_bp pts.

(** A `BPoint` is finite iff both its coordinates are finite binary64s.   *)
Definition is_finite_bp (p : BPoint) : Prop :=
  Binary.is_finite prec emax (bx p) = true /\
  Binary.is_finite prec emax (by_ p) = true.

(** A `BPoint` is `point_int_safe` iff both its coordinates pass the       *)
(** integer-regime predicate from `Orient_b64_exact.v`.                    *)
Definition point_int_safe (p : BPoint) : Prop :=
  coord_int_safe (bx p) /\ coord_int_safe (by_ p).

(** List-level lift: every point is `point_int_safe`.                       *)
Definition points_int_safe (pts : list BPoint) : Prop :=
  Forall point_int_safe pts.

(* -------------------------------------------------------------------------- *)
(* Structural compatibility lemmas.                                          *)
(* -------------------------------------------------------------------------- *)

Lemma map_B2R_bp_nil : map_B2R_bp [] = [].
Proof. reflexivity. Qed.

Lemma map_B2R_bp_cons :
  forall (p : BPoint) (xs : list BPoint),
    map_B2R_bp (p :: xs) = B2R_bp p :: map_B2R_bp xs.
Proof. reflexivity. Qed.

Lemma map_B2R_bp_length :
  forall (xs : list BPoint), length (map_B2R_bp xs) = length xs.
Proof. intros xs. apply List.length_map. Qed.

(* -------------------------------------------------------------------------- *)
(* b64_cross <-> b64_orient2d connector.                                    *)
(*                                                                            *)
(* `b64_cross` (defined in Validate_binary64.v) and `b64_orient2d` (defined  *)
(* in Orientation_b64.v) compute the same cross-product formula on three    *)
(* BPoints.  They differ syntactically: `b64_orient2d` factors via an       *)
(* internal `b64_orient2d_terms` let-pair, while `b64_cross` is direct.     *)
(* The two are definitionally equal; `cbn` discharges the let.              *)
(* -------------------------------------------------------------------------- *)

Lemma b64_cross_eq_b64_orient2d :
  forall p0 p1 q : BPoint,
    b64_cross p0 p1 q = b64_orient2d p0 p1 q.
Proof.
  intros. unfold b64_cross, b64_orient2d.
  (* b64_orient2d's body destructures `b64_orient2d_terms p0 p1 q` (a Local *)
  (* Definition in Orientation_b64.v, not accessible by name here).  `cbn` *)
  (* unfolds the local def and beta-reduces the let-pair to the direct     *)
  (* `b64_minus (b64_mult ...) (b64_mult ...)` form, matching `b64_cross`. *)
  cbn. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* b64_cross R-side bridge (integer regime).                                 *)
(*                                                                            *)
(* Corollary of `b64_orient2d_exact_for_small_int` via the connector lemma. *)
(* `cross_R_BP` is the R-side witness defined in `Orient_b64_sound.v`.       *)
(* -------------------------------------------------------------------------- *)

Theorem b64_cross_exact_for_small_int :
  forall p0 p1 q : BPoint,
    orient2d_inputs_int_safe p0 p1 q ->
    Binary.B2R prec emax (b64_cross p0 p1 q) = cross_R_BP p0 p1 q.
Proof.
  intros p0 p1 q Hsafe.
  rewrite b64_cross_eq_b64_orient2d.
  apply b64_orient2d_exact_for_small_int. exact Hsafe.
Qed.

(* -------------------------------------------------------------------------- *)
(* dist_sq R-side witness + input regime.                                    *)
(* -------------------------------------------------------------------------- *)

(** R-side squared distance on `BPoint` inputs.  Mirrors                    *)
(** `Distance.dist_sq` lifted across `B2R_bp`: the squared L2 distance      *)
(** between the projected R-points.                                          *)
Definition dist_sq_R_BP (p q : BPoint) : R :=
  let dx := Binary.B2R prec emax (bx p) - Binary.B2R prec emax (bx q) in
  let dy := Binary.B2R prec emax (by_ p) - Binary.B2R prec emax (by_ q) in
  dx * dx + dy * dy.

Definition dist_sq_inputs_int_safe (p q : BPoint) : Prop :=
  coord_int_safe (bx p)  /\
  coord_int_safe (by_ p) /\
  coord_int_safe (bx q)  /\
  coord_int_safe (by_ q).

(* -------------------------------------------------------------------------- *)
(* b64_dist_sq R-side bridge (integer regime).                                *)
(*                                                                            *)
(* Under `dist_sq_inputs_int_safe`, every intermediate value in              *)
(*    b64_plus (b64_mult (b64_minus dx dx)) (b64_mult (b64_minus dy dy))    *)
(* stays inside binary64's 53-bit integer-exactness window:                  *)
(*                                                                            *)
(*   - `bx p - bx q`, `by_ p - by_ q`     : integer in `[-2^26, 2^26]`.    *)
(*   - The two squares                    : integer in `[0, 2^52]`.        *)
(*   - The final sum                      : integer in `[0, 2^53]`.        *)
(*                                                                            *)
(* All three magnitudes are `<= 2^prec = 2^53`, so the corresponding         *)
(* `b64_*_int_exact` lemmas from `Orient_b64_exact.v` apply.                 *)
(* -------------------------------------------------------------------------- *)

Theorem b64_dist_sq_exact_for_small_int :
  forall p q : BPoint,
    dist_sq_inputs_int_safe p q ->
    Binary.B2R prec emax (b64_dist_sq p q) = dist_sq_R_BP p q.
Proof.
  intros p q (Hxp & Hyp & Hxq & Hyq).
  unfold b64_dist_sq, dist_sq_R_BP.
  (* Step 1: each b64_minus is integer-valued in [-2^26, 2^26]. *)
  destruct Hxp as (Fxp & a & HxpR & Hxpb).
  destruct Hxq as (Fxq & c & HxqR & Hxqb).
  destruct Hyp as (Fyp & b & HypR & Hypb).
  destruct Hyq as (Fyq & d & HyqR & Hyqb).
  assert (Hdx_b : (Z.abs (a - c) <= 2 ^ prec)%Z).
  { apply (Z.le_trans _ (2 ^ 26)).
    - replace (2 ^ 26)%Z with (2 ^ 25 + 2 ^ 25)%Z by lia. lia.
    - unfold prec. lia. }
  assert (Hdy_b : (Z.abs (b - d) <= 2 ^ prec)%Z).
  { apply (Z.le_trans _ (2 ^ 26)).
    - replace (2 ^ 26)%Z with (2 ^ 25 + 2 ^ 25)%Z by lia. lia.
    - unfold prec. lia. }
  pose proof (b64_minus_int_exact (bx p)  (bx q)  a c Fxp Fxq HxpR HxqR Hdx_b)
    as (HBdx & Fdx).
  pose proof (b64_minus_int_exact (by_ p) (by_ q) b d Fyp Fyq HypR HyqR Hdy_b)
    as (HBdy & Fdy).
  (* Step 2: each b64_mult of two int-valued diffs is integer in [-2^52, 2^52]. *)
  assert (Hmx_b : (Z.abs ((a - c) * (a - c)) <= 2 ^ prec)%Z).
  { rewrite Z.abs_mul.
    apply (Z.le_trans _ (2 ^ 26 * 2 ^ 26)).
    - apply Z.mul_le_mono_nonneg; try apply Z.abs_nonneg; lia.
    - unfold prec.
      replace (2 ^ 26 * 2 ^ 26)%Z with (2 ^ 52)%Z by lia. lia. }
  assert (Hmy_b : (Z.abs ((b - d) * (b - d)) <= 2 ^ prec)%Z).
  { rewrite Z.abs_mul.
    apply (Z.le_trans _ (2 ^ 26 * 2 ^ 26)).
    - apply Z.mul_le_mono_nonneg; try apply Z.abs_nonneg; lia.
    - unfold prec.
      replace (2 ^ 26 * 2 ^ 26)%Z with (2 ^ 52)%Z by lia. lia. }
  pose proof (b64_mult_int_exact (b64_minus (bx p)  (bx q))
                                 (b64_minus (bx p)  (bx q))
                                 (a - c) (a - c) Fdx Fdx HBdx HBdx Hmx_b)
    as (HBmx & Fmx).
  pose proof (b64_mult_int_exact (b64_minus (by_ p) (by_ q))
                                 (b64_minus (by_ p) (by_ q))
                                 (b - d) (b - d) Fdy Fdy HBdy HBdy Hmy_b)
    as (HBmy & Fmy).
  (* Step 3: final b64_plus of two non-negative ints, each in [0, 2^52]. *)
  assert (Hsum_b : (Z.abs ((a - c) * (a - c) + (b - d) * (b - d)) <= 2 ^ prec)%Z).
  { apply (Z.le_trans _ (2 ^ 52 + 2 ^ 52)).
    - rewrite Z.abs_eq.
      + apply Z.add_le_mono.
        * rewrite <- Z.abs_eq with (n := ((a - c) * (a - c))%Z)
            by (apply Z.square_nonneg).
          rewrite Z.abs_mul.
          apply (Z.le_trans _ (2 ^ 26 * 2 ^ 26)).
          -- apply Z.mul_le_mono_nonneg; try apply Z.abs_nonneg; lia.
          -- replace (2 ^ 26 * 2 ^ 26)%Z with (2 ^ 52)%Z by lia. lia.
        * rewrite <- Z.abs_eq with (n := ((b - d) * (b - d))%Z)
            by (apply Z.square_nonneg).
          rewrite Z.abs_mul.
          apply (Z.le_trans _ (2 ^ 26 * 2 ^ 26)).
          -- apply Z.mul_le_mono_nonneg; try apply Z.abs_nonneg; lia.
          -- replace (2 ^ 26 * 2 ^ 26)%Z with (2 ^ 52)%Z by lia. lia.
      + apply Z.add_nonneg_nonneg; apply Z.square_nonneg.
    - unfold prec.
      replace (2 ^ 52 + 2 ^ 52)%Z with (2 ^ 53)%Z by lia. lia. }
  pose proof (b64_plus_int_exact _ _ ((a - c) * (a - c)) ((b - d) * (b - d))
                                 Fmx Fmy HBmx HBmy Hsum_b)
    as (HBplus & _Fplus).
  (* LHS becomes the integer witness `IZR (...)`. *)
  rewrite HBplus.
  (* RHS still has the B2R coords; substitute them via Hx*R / Hy*R. *)
  rewrite HxpR, HxqR, HypR, HyqR.
  (* Both sides are now polynomial in IZR a, IZR b, IZR c, IZR d.        *)
  (* Push IZR through +, *, - so the goal is a Z-only polynomial.        *)
  rewrite plus_IZR, !mult_IZR, !minus_IZR.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions map_B2R_bp_nil.
Print Assumptions map_B2R_bp_cons.
Print Assumptions map_B2R_bp_length.
Print Assumptions b64_cross_eq_b64_orient2d.
Print Assumptions b64_cross_exact_for_small_int.
Print Assumptions b64_dist_sq_exact_for_small_int.
