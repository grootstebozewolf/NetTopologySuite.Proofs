(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Orient_b64_expansion
   ----------------------------------------------------------------------------
   Slice A Piece 6: orient2d via fast-expansion-sum.

   COMPOSITION
   -----------
   Builds the exact orient2d determinant as a binary64 expansion:
     1. Compute four pairwise differences via b64_minus.
     2. Form two Dekker products (r1, t1) and (r2, t2).
     3. Combine via fast_expansion_sum to get a 4-component expansion.

   The subtraction (a*b - c*d) is folded into the difference computation:
     dx2 := P0.x - Q.x  (instead of Q.x - P0.x)
   so the second Dekker product is the NEGATED second term, and
   fast_expansion_sum directly computes a*b + (-c*d) = a*b - c*d.  No
   negation on Dekker outputs needed.

   PIECE 6 DELIVERABLES
   --------------------
     - `b64_orient2d_expansion`:           the determinant as a list binary64.
     - `b64_orient2d_expansion_safe`:      composite safety predicate.
     - `b64_orient2d_expansion_sum`:       expansion_R = cross_R_BP (Qed).
     - `b64_orient2d_expansion_nonoverlap`: nonoverlap_shewchuk (uses
                                            fast_expansion_sum_nonoverlap_shewchuk
                                            which is currently Admitted/deferred
                                            in B64_FastExpansionSum_Shewchuk.v).
     - `b64_orient2d_expansion_sign_correct`: sign of expansion matches
                                              sign of cross_R_BP.  Composes
                                              the above with the already-Qed-
                                              closed sign_of_expansion_correct_shewchuk.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ============================================================================ *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lra.
From Stdlib Require Import List.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Flocq Require Import Core.

From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import B64_bridge.
From NTS.Proofs.Flocq Require Import B64_lib.
From NTS.Proofs.Flocq Require Import Orient_b64_sound.
From NTS.Proofs.Flocq Require Import B64_Expansion.
From NTS.Proofs.Flocq Require Import B64_Expansion_Shewchuk.
From NTS.Proofs.Flocq Require Import B64_Pff_bridge.
From NTS.Proofs.Flocq Require Import B64_FastExpansionSum.
From NTS.Proofs.Flocq Require Import B64_FastExpansionSum_Shewchuk.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* The expansion definition.                                                  *)
(* -------------------------------------------------------------------------- *)

Definition b64_orient2d_expansion (P0 P1 Q : BPoint) : list binary64 :=
  let dx1 := b64_minus (bx P1) (bx P0) in
  let dy1 := b64_minus (by_ Q)  (by_ P0) in
  let dx2 := b64_minus (bx P0) (bx Q)  in
  let dy2 := b64_minus (by_ P1) (by_ P0) in
  let '(r1, t1) := b64_Dekker dx1 dy1 in
  let '(r2, t2) := b64_Dekker dx2 dy2 in
  fast_expansion_sum (r1 :: t1 :: nil) (r2 :: t2 :: nil).

(* -------------------------------------------------------------------------- *)
(* Safety predicate.                                                          *)
(*                                                                            *)
(* The expansion chains six top-level binary64 ops:                           *)
(*   - 4 b64_minus calls (the diffs).                                         *)
(*   - 2 b64_Dekker calls (each with its own internal safety chain).          *)
(*   - 1 fast_expansion_sum call.                                             *)
(* Each requires its own safety; we conjoin them.                             *)
(*                                                                            *)
(* The Dekker underflow precondition (B2R x * B2R y = 0 or                    *)
(* bpow radix2 ... <= Rabs (B2R x * B2R y)) is needed for Dekker's            *)
(* sum-correctness and nonoverlap; we include it explicitly.                  *)
(* -------------------------------------------------------------------------- *)

Definition b64_orient2d_expansion_diffs_safe (P0 P1 Q : BPoint) : Prop :=
  b64_safe Rminus (bx P1) (bx P0) /\
  b64_safe Rminus (by_ Q)  (by_ P0) /\
  b64_safe Rminus (bx P0) (bx Q)  /\
  b64_safe Rminus (by_ P1) (by_ P0).

(* The differences must be exact (no rounding error) for the expansion's    *)
(* sum to equal cross_R_BP exactly.  This holds in the small-integer        *)
(* regime (via integer-arithmetic exactness already Qed-closed in           *)
(* Orient_b64_exact.v) and under Sterbenz-style preconditions.  Outside     *)
(* those regimes, full Stage D orient2d_exact would need TwoDiff to track  *)
(* the rounding error of each difference as part of the expansion -- a     *)
(* separate slice not in Piece 6's scope.                                   *)
Definition b64_orient2d_expansion_diffs_exact (P0 P1 Q : BPoint) : Prop :=
  Binary.B2R prec emax (b64_minus (bx P1) (bx P0))
    = Binary.B2R prec emax (bx P1) - Binary.B2R prec emax (bx P0) /\
  Binary.B2R prec emax (b64_minus (by_ Q) (by_ P0))
    = Binary.B2R prec emax (by_ Q) - Binary.B2R prec emax (by_ P0) /\
  Binary.B2R prec emax (b64_minus (bx P0) (bx Q))
    = Binary.B2R prec emax (bx P0) - Binary.B2R prec emax (bx Q) /\
  Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0))
    = Binary.B2R prec emax (by_ P1) - Binary.B2R prec emax (by_ P0).

Definition b64_orient2d_expansion_safe (P0 P1 Q : BPoint) : Prop :=
  b64_orient2d_expansion_diffs_safe P0 P1 Q /\
  b64_orient2d_expansion_diffs_exact P0 P1 Q /\
  b64_Dekker_safe (b64_minus (bx P1) (bx P0)) (b64_minus (by_ Q) (by_ P0)) /\
  b64_Dekker_safe (b64_minus (bx P0) (bx Q))  (b64_minus (by_ P1) (by_ P0)) /\
  (Binary.B2R prec emax (b64_minus (bx P1) (bx P0))
     * Binary.B2R prec emax (b64_minus (by_ Q) (by_ P0)) = 0
   \/ bpow radix2 (3 - emax - prec + 2 * prec - 1)
      <= Rabs (Binary.B2R prec emax (b64_minus (bx P1) (bx P0))
               * Binary.B2R prec emax (b64_minus (by_ Q) (by_ P0)))) /\
  (Binary.B2R prec emax (b64_minus (bx P0) (bx Q))
     * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0)) = 0
   \/ bpow radix2 (3 - emax - prec + 2 * prec - 1)
      <= Rabs (Binary.B2R prec emax (b64_minus (bx P0) (bx Q))
               * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0)))) /\
  fast_expansion_sum_safe
    (fst (b64_Dekker (b64_minus (bx P1) (bx P0))
                     (b64_minus (by_ Q) (by_ P0)))
       :: snd (b64_Dekker (b64_minus (bx P1) (bx P0))
                          (b64_minus (by_ Q) (by_ P0))) :: nil)
    (fst (b64_Dekker (b64_minus (bx P0) (bx Q))
                     (b64_minus (by_ P1) (by_ P0)))
       :: snd (b64_Dekker (b64_minus (bx P0) (bx Q))
                          (b64_minus (by_ P1) (by_ P0))) :: nil).

(* -------------------------------------------------------------------------- *)
(* Sum-correctness: expansion_R = cross_R_BP.                                 *)
(*                                                                            *)
(* Composes:                                                                  *)
(*   - b64_minus_correct (4 instances, threading the diffs).                  *)
(*   - b64_Dekker_correct (2 instances, each gives r + t = x * y).            *)
(*   - fast_expansion_sum_correct: expansion_R sum_R = expansion_R e1         *)
(*     + expansion_R e2.                                                      *)
(* -------------------------------------------------------------------------- *)

Theorem b64_orient2d_expansion_sum :
  forall P0 P1 Q : BPoint,
    b64_orient2d_expansion_safe P0 P1 Q ->
    expansion_R (b64_orient2d_expansion P0 P1 Q) = cross_R_BP P0 P1 Q.
Proof.
  intros P0 P1 Q Hsafe.
  unfold b64_orient2d_expansion_safe in Hsafe.
  destruct Hsafe as [_ [Hexact [HDek1 [HDek2 [Hund1 [Hund2 Hfes]]]]]].
  unfold b64_orient2d_expansion_diffs_exact in Hexact.
  destruct Hexact as [HM1 [HM2 [HM3 HM4]]].
  unfold b64_orient2d_expansion.
  destruct (b64_Dekker (b64_minus (bx P1) (bx P0))
                       (b64_minus (by_ Q)  (by_ P0))) as [r1 t1] eqn:HD1.
  destruct (b64_Dekker (b64_minus (bx P0) (bx Q))
                       (b64_minus (by_ P1) (by_ P0))) as [r2 t2] eqn:HD2.
  cbn [fst snd] in Hfes.
  pose proof (fast_expansion_sum_correct
                (r1 :: t1 :: nil) (r2 :: t2 :: nil) Hfes) as Hsum.
  rewrite Hsum.
  cbn [expansion_R].
  pose proof (b64_Dekker_correct (b64_minus (bx P1) (bx P0))
                                  (b64_minus (by_ Q)  (by_ P0))
                                  HDek1 Hund1) as HDC1.
  rewrite HD1 in HDC1.
  cbv beta iota zeta in HDC1.
  pose proof (b64_Dekker_correct (b64_minus (bx P0) (bx Q))
                                  (b64_minus (by_ P1) (by_ P0))
                                  HDek2 Hund2) as HDC2.
  rewrite HD2 in HDC2.
  cbv beta iota zeta in HDC2.
  unfold cross_R_BP.
  rewrite HM1, HM2 in HDC1.
  rewrite HM3, HM4 in HDC2.
  (* HDC1: B2R r1 + B2R t1 = (P1x - P0x) * (Qy - P0y).        *)
  (* HDC2: B2R r2 + B2R t2 = (P0x - Qx) * (P1y - P0y).        *)
  set (A := (Binary.B2R prec emax (bx P1) - Binary.B2R prec emax (bx P0))
            * (Binary.B2R prec emax (by_ Q) - Binary.B2R prec emax (by_ P0)))
    in HDC1 |- *.
  set (B := (Binary.B2R prec emax (bx Q) - Binary.B2R prec emax (bx P0))
            * (Binary.B2R prec emax (by_ P1) - Binary.B2R prec emax (by_ P0)))
    in |- *.
  set (C := (Binary.B2R prec emax (bx P0) - Binary.B2R prec emax (bx Q))
            * (Binary.B2R prec emax (by_ P1) - Binary.B2R prec emax (by_ P0)))
    in HDC2.
  assert (HCB : C = - B).
  { unfold C, B. lra. }
  rewrite HCB in HDC2.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Nonoverlap of the expansion.                                               *)
(*                                                                            *)
(* Each Dekker product is itself nonoverlap_shewchuk as a 2-component         *)
(* expansion (b64_Dekker_nonoverlap gives |t| <= ulp(r)/2, which is           *)
(* strict_succ_b64; the singleton/pair structure satisfies                    *)
(* nonoverlap_strict directly; compress doesn't change nonoverlap if the      *)
(* component is nonzero, and the nonoverlap holds trivially if it is).        *)
(*                                                                            *)
(* fast_expansion_sum_nonoverlap_shewchuk is currently Admitted (Piece 5b);   *)
(* this theorem chains through it, so it's also Admitted/deferred until 5b   *)
(* closes.                                                                    *)
(* -------------------------------------------------------------------------- *)

(* Helper: every 2-component (r, t) from Dekker is nonoverlap_shewchuk. *)
Lemma b64_Dekker_pair_nonoverlap_shewchuk :
  forall x y : binary64,
    b64_Dekker_safe x y ->
    (Binary.B2R prec emax x * Binary.B2R prec emax y = 0
     \/ bpow radix2 (3 - emax - prec + 2 * prec - 1)
        <= Rabs (Binary.B2R prec emax x * Binary.B2R prec emax y)) ->
    let '(r, t) := b64_Dekker x y in
    nonoverlap_shewchuk (r :: t :: nil).
Proof.
  intros x y Hsafe Hund.
  pose proof (b64_Dekker_nonoverlap x y Hsafe Hund) as Hno.
  destruct (b64_Dekker x y) as [r t] eqn:HD.
  cbv beta iota zeta in Hno.
  unfold nonoverlap_shewchuk.
  (* compress [r; t] is either [r; t], [r], [t], or [], depending on zeros. *)
  cbn [compress].
  destruct (Rcompare (Binary.B2R prec emax r) 0) eqn:Hr;
  destruct (Rcompare (Binary.B2R prec emax t) 0) eqn:Ht;
  cbn [nonoverlap_strict]; try exact I; try (split; [|exact I]);
  unfold strict_succ_b64; exact Hno.
Qed.

Theorem b64_orient2d_expansion_nonoverlap :
  forall P0 P1 Q : BPoint,
    b64_orient2d_expansion_safe P0 P1 Q ->
    nonoverlap_shewchuk (b64_orient2d_expansion P0 P1 Q).
Proof.
  intros P0 P1 Q Hsafe.
  unfold b64_orient2d_expansion_safe in Hsafe.
  destruct Hsafe as [_ [_ [HDek1 [HDek2 [Hund1 [Hund2 Hfes]]]]]].
  unfold b64_orient2d_expansion.
  destruct (b64_Dekker (b64_minus (bx P1) (bx P0))
                       (b64_minus (by_ Q)  (by_ P0))) as [r1 t1] eqn:HD1.
  destruct (b64_Dekker (b64_minus (bx P0) (bx Q))
                       (b64_minus (by_ P1) (by_ P0))) as [r2 t2] eqn:HD2.
  cbn [fst snd] in Hfes.
  (* Each Dekker pair is nonoverlap_shewchuk. *)
  pose proof (b64_Dekker_pair_nonoverlap_shewchuk
                (b64_minus (bx P1) (bx P0))
                (b64_minus (by_ Q)  (by_ P0)) HDek1 Hund1) as Hno1.
  rewrite HD1 in Hno1.
  cbv beta iota zeta in Hno1.
  pose proof (b64_Dekker_pair_nonoverlap_shewchuk
                (b64_minus (bx P0) (bx Q))
                (b64_minus (by_ P1) (by_ P0)) HDek2 Hund2) as Hno2.
  rewrite HD2 in Hno2.
  cbv beta iota zeta in Hno2.
  (* Apply fast_expansion_sum_nonoverlap_shewchuk (currently Admitted/deferred). *)
  apply (fast_expansion_sum_nonoverlap_shewchuk
           (r1 :: t1 :: nil) (r2 :: t2 :: nil) Hfes Hno1 Hno2).
Qed.

(* -------------------------------------------------------------------------- *)
(* Sign-correctness: the headline of Piece 6.                                 *)
(*                                                                            *)
(* Composes:                                                                  *)
(*   1. b64_orient2d_expansion_sum: expansion_R = cross_R_BP.                 *)
(*   2. b64_orient2d_expansion_nonoverlap: the expansion is well-formed.      *)
(*   3. sign_of_expansion_correct_shewchuk: under nonoverlap_shewchuk,        *)
(*      sign_of_expansion matches the R-side sign.                            *)
(* -------------------------------------------------------------------------- *)

Definition b64_orient2d_expansion_sign (P0 P1 Q : BPoint) : expansion_sign :=
  sign_of_expansion (b64_orient2d_expansion P0 P1 Q).

Theorem b64_orient2d_expansion_sign_correct :
  forall P0 P1 Q : BPoint,
    b64_orient2d_expansion_safe P0 P1 Q ->
    match b64_orient2d_expansion_sign P0 P1 Q with
    | ExpPos  => 0 < cross_R_BP P0 P1 Q
    | ExpNeg  => cross_R_BP P0 P1 Q < 0
    | ExpZero => cross_R_BP P0 P1 Q = 0
    end.
Proof.
  intros P0 P1 Q Hsafe.
  unfold b64_orient2d_expansion_sign.
  pose proof (b64_orient2d_expansion_nonoverlap P0 P1 Q Hsafe) as Hno.
  pose proof (sign_of_expansion_correct_shewchuk
                (b64_orient2d_expansion P0 P1 Q) Hno) as Hsign.
  pose proof (b64_orient2d_expansion_sum P0 P1 Q Hsafe) as Hsum.
  rewrite Hsum in Hsign.
  exact Hsign.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_orient2d_expansion.
Print Assumptions b64_orient2d_expansion_sum.
Print Assumptions b64_Dekker_pair_nonoverlap_shewchuk.
Print Assumptions b64_orient2d_expansion_nonoverlap.
Print Assumptions b64_orient2d_expansion_sign_correct.
