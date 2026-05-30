(* ============================================================================
   NetTopologySuite.Proofs.Flocq.ArcOrient_b64
   ----------------------------------------------------------------------------
   Phase 4 Session A: binary64 mirror of `inCircle_R`.

   Defines `b64_inCircle_R` (the computable binary64 form of the 4-point
   lifted determinant from `theories/ArcOrient.v:88`) and the sign predicate
   `b64_inCircle_sign` that classifies a query point as inside / outside /
   on the circumscribed circle of three reference points.

   Pattern mirrors the Phase 0 Stage A pattern (`Orient_b64_exact.v`):
   integer-safe coordinate precondition + bit-exact arithmetic at the
   binary64 level + soundness theorem connecting back to the R-side
   `inCircle_R`.

   Bound: `arc_coord_int_safe` uses `|n| <= 2^11`, tighter than Phase 0's
   `coord_int_safe` (2^25) because inCircle_R has DEGREE-4 expansion when
   fully unfolded.  Magnitude analysis:
     - coord differences: |.| <= 2^12
     - degree-2 (squared): |.| <= 2^24
     - sum of two squares: |.| <= 2^25
     - degree-3 (diff*sum_sq): |.| <= 2^37
     - degree-3 difference: |.| <= 2^38
     - degree-4 (diff*degree-3): |.| <= 2^50
     - final sum of two degree-4: |.| <= 2^51 < 2^53 (binary64 prec)
   B = 11 sits comfortably inside the safe envelope.

   Soundness theorem (`b64_inCircle_sign_sound`) is CONDITIONAL on the
   load-bearing `b64_inCircle_R_correct` lemma, which connects the
   binary64 computation to the R-side expression via the chain of
   `b64_*_int_exact` bridge lemmas from `Orient_b64_exact.v`.  Stating
   the conditional theorem in this session lands the structural
   framework + sign decoding; the full algebra chain (~15 bridge-lemma
   applications) is the natural follow-up session.

   Pattern matches the corpus's other conditional headlines:
     - `hobby_theorem_4_1_conditional` (Phase 2 Link 1)
     - `overlay_ng_correct_conditional` (Phase 3 M5 S15)
     - `point_in_ring_correct_jct`     (Phase 5)

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import ZArith.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import Core.

From NTS.Proofs        Require Import Distance.
From NTS.Proofs        Require Import ArcOrient.
From NTS.Proofs.Flocq  Require Import Validate_binary64.
From NTS.Proofs.Flocq  Require Import B64_bridge.
From NTS.Proofs.Flocq  Require Import HotPixel_b64.    (* BP2P, b64_one, ...*)

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  arc_coord_int_safe -- integer-safe precondition for inCircle_R.        *)
(*                                                                            *)
(* Tighter than `coord_int_safe` (2^25) from `Orient_b64_exact.v:363`: the    *)
(* inCircle_R determinant is degree-4 when fully expanded, requiring a       *)
(* coordinate bound of 2^11 for binary64 bit-exact computation of every      *)
(* intermediate.  See file header for the magnitude analysis.                *)
(* -------------------------------------------------------------------------- *)

Definition arc_coord_int_safe (x : binary64) : Prop :=
  Binary.is_finite prec emax x = true /\
  exists n : Z,
    Binary.B2R prec emax x = IZR n /\
    (Z.abs n <= 2 ^ 11)%Z.

Definition inCircle_inputs_int_safe (A B C P : BPoint) : Prop :=
  arc_coord_int_safe (bx A)  /\ arc_coord_int_safe (by_ A) /\
  arc_coord_int_safe (bx B)  /\ arc_coord_int_safe (by_ B) /\
  arc_coord_int_safe (bx C)  /\ arc_coord_int_safe (by_ C) /\
  arc_coord_int_safe (bx P)  /\ arc_coord_int_safe (by_ P).

(* -------------------------------------------------------------------------- *)
(* §2  b64_inCircle_R -- binary64 mirror of inCircle_R.                       *)
(*                                                                            *)
(* Term-by-term match of the R-side definition (ArcOrient.v:88).  Six        *)
(* coordinate differences + three squared-norm intermediates + the final     *)
(* triple-term sum.                                                           *)
(* -------------------------------------------------------------------------- *)

Definition b64_inCircle_R (A B C P : BPoint) : binary64 :=
  let ax := b64_minus (bx A) (bx P) in
  let ay := b64_minus (by_ A) (by_ P) in
  let bx' := b64_minus (bx B) (bx P) in
  let by' := b64_minus (by_ B) (by_ P) in
  let cx := b64_minus (bx C) (bx P) in
  let cy := b64_minus (by_ C) (by_ P) in
  let na := b64_plus (b64_mult ax ax) (b64_mult ay ay) in
  let nb := b64_plus (b64_mult bx' bx') (b64_mult by' by') in
  let nc := b64_plus (b64_mult cx cx) (b64_mult cy cy) in
  (* ax * (by' * nc - cy * nb)
     - ay * (bx' * nc - cx * nb)
     + na  * (bx' * cy - cx * by') *)
  let row_a := b64_mult ax
                 (b64_minus (b64_mult by' nc) (b64_mult cy nb)) in
  let row_b := b64_mult ay
                 (b64_minus (b64_mult bx' nc) (b64_mult cx nb)) in
  let row_c := b64_mult na
                 (b64_minus (b64_mult bx' cy) (b64_mult cx by')) in
  b64_plus (b64_minus row_a row_b) row_c.

(* -------------------------------------------------------------------------- *)
(* §3  Sign predicate.                                                        *)
(* -------------------------------------------------------------------------- *)

Inductive InCircleSign : Type :=
  | ICS_Pos        (* P strictly inside circumscribed circle of (A, B, C) *)
  | ICS_Neg        (* P strictly outside *)
  | ICS_Zero       (* P on circle, or degenerate (A, B, C) *)
  | ICS_Nan        (* non-finite intermediate (overflow / NaN) *).

(* Decision procedure: classify the inCircle_R sign at the binary64 level.
   The `Rcompare` route through `b64_compare` mirrors `b64_orient_sign` in
   `Orientation_b64.v`. *)
Definition b64_inCircle_sign (A B C P : BPoint) : InCircleSign :=
  let s := b64_inCircle_R A B C P in
  match b64_compare s (Binary.B754_zero prec emax false) with
  | Some Gt => ICS_Pos
  | Some Lt => ICS_Neg
  | Some Eq => ICS_Zero
  | None    => ICS_Nan
  end.

(* -------------------------------------------------------------------------- *)
(* §4  Conditional soundness.                                                 *)
(*                                                                            *)
(* The load-bearing fact `b64_inCircle_R_correct` is captured as a Section    *)
(* Variable so the structural decoding theorem can land in this session       *)
(* without the full ~15-step `b64_*_int_exact` chain.  Pattern matches        *)
(* `hobby_theorem_4_1_conditional` etc.: thesis-shaped gap stated as a        *)
(* named hypothesis, structural composition proved Qed-closed.                *)
(*                                                                            *)
(* Discharging `b64_inCircle_R_correct` is the natural follow-up session:    *)
(* mechanical chain of `b64_minus_int_exact` + `b64_mult_int_exact` +         *)
(* `b64_plus_int_exact` applications with arithmetic side conditions          *)
(* discharged from `arc_coord_int_safe`'s 2^11 bound.                         *)
(* -------------------------------------------------------------------------- *)

Section InCircleConditional.

  (* Load-bearing hypothesis: the binary64 computation realises the R-side
     determinant exactly under arc_coord_int_safe inputs. *)
  Variable b64_inCircle_R_correct :
    forall A B C P : BPoint,
      inCircle_inputs_int_safe A B C P ->
      Binary.B2R prec emax (b64_inCircle_R A B C P)
        = inCircle_R (BP2P A) (BP2P B) (BP2P C) (BP2P P) /\
      Binary.is_finite prec emax (b64_inCircle_R A B C P) = true.

  (* Helper: rewrite `b64_compare` to `Rcompare` under finiteness. *)
  Lemma b64_compare_zero :
    forall d : binary64,
      Binary.is_finite prec emax d = true ->
      b64_compare d (Binary.B754_zero prec emax false)
        = Some (Rcompare (Binary.B2R prec emax d) 0).
  Proof.
    intros d Fd.
    assert (Fz : Binary.is_finite prec emax
                   (Binary.B754_zero prec emax false) = true) by reflexivity.
    unfold b64_compare.
    rewrite (Binary.Bcompare_correct prec emax _ _ Fd Fz).
    replace (Binary.B2R prec emax (Binary.B754_zero prec emax false))
      with 0 by reflexivity.
    reflexivity.
  Qed.

  Theorem b64_inCircle_sign_sound :
    forall A B C P : BPoint,
      inCircle_inputs_int_safe A B C P ->
      match b64_inCircle_sign A B C P with
      | ICS_Pos  => 0 < inCircle_R (BP2P A) (BP2P B) (BP2P C) (BP2P P)
      | ICS_Neg  => inCircle_R (BP2P A) (BP2P B) (BP2P C) (BP2P P) < 0
      | ICS_Zero => inCircle_R (BP2P A) (BP2P B) (BP2P C) (BP2P P) = 0
      | ICS_Nan  => True
      end.
  Proof.
    intros A B C P Hsafe.
    pose proof (b64_inCircle_R_correct A B C P Hsafe) as [HB2R Hfin].
    unfold b64_inCircle_sign.
    rewrite (b64_compare_zero _ Hfin).
    rewrite HB2R.
    destruct (Rcompare _ 0) eqn:Ecmp.
    - apply Rcompare_Eq_inv in Ecmp. exact Ecmp.
    - apply Rcompare_Lt_inv in Ecmp. exact Ecmp.
    - apply Rcompare_Gt_inv in Ecmp. exact Ecmp.
  Qed.

  (* Directional corollaries -- handy for callers that pattern-match on
     the constructor name. *)
  Corollary b64_inCircle_sign_pos_sound :
    forall A B C P : BPoint,
      inCircle_inputs_int_safe A B C P ->
      b64_inCircle_sign A B C P = ICS_Pos ->
      0 < inCircle_R (BP2P A) (BP2P B) (BP2P C) (BP2P P).
  Proof.
    intros A B C P Hsafe Heq.
    pose proof (b64_inCircle_sign_sound A B C P Hsafe) as H.
    rewrite Heq in H. exact H.
  Qed.

  Corollary b64_inCircle_sign_neg_sound :
    forall A B C P : BPoint,
      inCircle_inputs_int_safe A B C P ->
      b64_inCircle_sign A B C P = ICS_Neg ->
      inCircle_R (BP2P A) (BP2P B) (BP2P C) (BP2P P) < 0.
  Proof.
    intros A B C P Hsafe Heq.
    pose proof (b64_inCircle_sign_sound A B C P Hsafe) as H.
    rewrite Heq in H. exact H.
  Qed.

  Corollary b64_inCircle_sign_zero_sound :
    forall A B C P : BPoint,
      inCircle_inputs_int_safe A B C P ->
      b64_inCircle_sign A B C P = ICS_Zero ->
      inCircle_R (BP2P A) (BP2P B) (BP2P C) (BP2P P) = 0.
  Proof.
    intros A B C P Hsafe Heq.
    pose proof (b64_inCircle_sign_sound A B C P Hsafe) as H.
    rewrite Heq in H. exact H.
  Qed.

End InCircleConditional.

(* -------------------------------------------------------------------------- *)
(* §5  Stand-alone structural lemmas (no conditional hypothesis).             *)
(* -------------------------------------------------------------------------- *)

(* The sign predicate is exhaustive on its constructors. *)
Lemma b64_inCircle_sign_cases :
  forall A B C P : BPoint,
    b64_inCircle_sign A B C P = ICS_Pos \/
    b64_inCircle_sign A B C P = ICS_Neg \/
    b64_inCircle_sign A B C P = ICS_Zero \/
    b64_inCircle_sign A B C P = ICS_Nan.
Proof.
  intros A B C P. unfold b64_inCircle_sign.
  destruct (b64_compare _ _) as [[]|]; auto.
Qed.

(* arc_coord_int_safe implies finiteness (the first conjunct of int_safe). *)
Lemma arc_coord_int_safe_is_finite :
  forall x : binary64,
    arc_coord_int_safe x ->
    Binary.is_finite prec emax x = true.
Proof.
  intros x [Hfin _]. exact Hfin.
Qed.

(* arc_coord_int_safe implies a magnitude bound on B2R. *)
Lemma arc_coord_int_safe_B2R_bound :
  forall x : binary64,
    arc_coord_int_safe x ->
    Rabs (Binary.B2R prec emax x) <= IZR (2 ^ 11).
Proof.
  intros x [_ [n [HxR Hbnd]]].
  rewrite HxR, <- abs_IZR.
  apply IZR_le. exact Hbnd.
Qed.

(* Symmetry-flavour: arc_coord_int_safe is closed under swapping signs of
   the integer witness (trivially -- the bound is on Z.abs). *)
Lemma arc_coord_int_safe_witness_unique_abs :
  forall (x : binary64) (n m : Z),
    Binary.B2R prec emax x = IZR n ->
    Binary.B2R prec emax x = IZR m ->
    n = m.
Proof.
  intros x n m Hn Hm.
  apply eq_IZR. rewrite <- Hn, <- Hm. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_compare_zero.
Print Assumptions b64_inCircle_sign_sound.
Print Assumptions b64_inCircle_sign_pos_sound.
Print Assumptions b64_inCircle_sign_neg_sound.
Print Assumptions b64_inCircle_sign_zero_sound.
Print Assumptions b64_inCircle_sign_cases.
Print Assumptions arc_coord_int_safe_is_finite.
Print Assumptions arc_coord_int_safe_B2R_bound.
Print Assumptions arc_coord_int_safe_witness_unique_abs.
