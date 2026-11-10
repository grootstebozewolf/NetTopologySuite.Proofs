(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Orient_b64_stage_d_cc
   ----------------------------------------------------------------------------
   Stage D rebuilt on carry_clean.  Supersedes the conditional
   `b64_orient_sign_exact_sound` / `b64_orient_sign_stage_d_sound`
   (Orient_b64_stage_d.v), which take the REFUTED
   `fast_expansion_sum_strong_nonoverlap_headline` as a hypothesis.  Nothing
   here mentions that headline, directly or through a lemma that takes it.

   DECODERS
     b64_orient_sign_exact_cc     sign of carry_clean (fast_expansion_sum ...)
     b64_orient_sign_stage_d_cc   Stage A filter; on Uncertain / Nan, the
                                  carry_clean exact decoder.  Same shape as
                                  b64_orient_sign_stage_d, only the fallback
                                  changes.

   RESULTS
     b64_orient_sign_exact_cc_sound
        the exact path is sound vs cross_R_BP on the coordinate domain
        |coord| <= 2^507 (orient2d_inputs_cc_domain) under Stage D's safety
        predicate minus fast_expansion_sum_safe (now derived).  No integer
        regime: this is the orient2d soundness headline of the rebuild.
     b64_orient_sign_stage_d_cc_sound
        the full decoder, under the integer regime (for the filter path, as
        before) and the same expansion safety.  The domain is implied by the
        integer regime (int_safe_cc_domain: 2^25 <= 2^507).
     b64_orient_sign_stage_d_cc_tiny_regime_decisive
        the tiny-regime decisiveness carries over.

   topic: binary64
   claimId: orient2d-stage-d-carry-clean
   witness: b64_orient_sign_exact_cc_sound

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra List.
From Flocq Require Import IEEE754.Binary Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 Orient_b64_sound
     Orient_b64_exact Orientation_b64 B64_Expansion Orient_b64_expansion
     Orient_b64_stage_d Orient_b64_expansion_cc.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Exact decoder on carry_clean.                                              *)
(* -------------------------------------------------------------------------- *)

Definition b64_orient_sign_exact_cc (P0 P1 Q : BPoint) : orient_sign_robust :=
  expansion_sign_to_orient_robust (b64_orient2d_expansion_cc_sign P0 P1 Q).

Theorem b64_orient_sign_exact_cc_sound :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_cc_domain P0 P1 Q ->
    b64_orient2d_expansion_cc_safe P0 P1 Q ->
    match b64_orient_sign_exact_cc P0 P1 Q with
    | OrientRPos       => 0 < cross_R_BP P0 P1 Q
    | OrientRNeg       => cross_R_BP P0 P1 Q < 0
    | OrientRZero      => cross_R_BP P0 P1 Q = 0
    | OrientRNan       => True
    | OrientRUncertain => True
    end.
Proof.
  intros P0 P1 Q Hd Hs.
  unfold b64_orient_sign_exact_cc, expansion_sign_to_orient_robust.
  pose proof (b64_orient2d_expansion_cc_sign_correct P0 P1 Q Hs Hd) as H.
  destruct (b64_orient2d_expansion_cc_sign P0 P1 Q); exact H.
Qed.

(* The exact decoder never declines. *)
Lemma b64_orient_sign_exact_cc_definite :
  forall P0 P1 Q,
    b64_orient_sign_exact_cc P0 P1 Q <> OrientRNan
    /\ b64_orient_sign_exact_cc P0 P1 Q <> OrientRUncertain.
Proof.
  intros P0 P1 Q. unfold b64_orient_sign_exact_cc, expansion_sign_to_orient_robust.
  destruct (b64_orient2d_expansion_cc_sign P0 P1 Q); split; discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Full Stage D decoder: filter, then carry_clean exact fallback.            *)
(* -------------------------------------------------------------------------- *)

Definition b64_orient_sign_stage_d_cc (P0 P1 Q : BPoint) : orient_sign_robust :=
  match b64_orient_sign_filtered P0 P1 Q with
  | OrientRPos       => OrientRPos
  | OrientRNeg       => OrientRNeg
  | OrientRZero      => OrientRZero
  | OrientRUncertain => b64_orient_sign_exact_cc P0 P1 Q
  | OrientRNan       => b64_orient_sign_exact_cc P0 P1 Q
  end.

Lemma coord_int_safe_cc_domain :
  forall c, coord_int_safe c -> coord_in_cc_domain c.
Proof.
  intros c (Fc & n & Hn & Hb). split; [ exact Fc | ].
  rewrite Hn, <- abs_IZR.
  apply Rle_trans with (bpow radix2 25).
  - rewrite <- IZR_Zpower by lia. apply IZR_le. exact Hb.
  - apply bpow_le. unfold orient2d_cc_coord_exp. lia.
Qed.

Lemma int_safe_cc_domain :
  forall P0 P1 Q, orient2d_inputs_int_safe P0 P1 Q -> orient2d_inputs_cc_domain P0 P1 Q.
Proof.
  intros P0 P1 Q (H1 & H2 & H3 & H4 & H5 & H6).
  repeat split; apply coord_int_safe_cc_domain; assumption.
Qed.

Theorem b64_orient_sign_stage_d_cc_sound :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_int_safe P0 P1 Q ->
    b64_orient2d_expansion_cc_safe P0 P1 Q ->
    match b64_orient_sign_stage_d_cc P0 P1 Q with
    | OrientRPos       => 0 < cross_R_BP P0 P1 Q
    | OrientRNeg       => cross_R_BP P0 P1 Q < 0
    | OrientRZero      => cross_R_BP P0 P1 Q = 0
    | OrientRNan       => True
    | OrientRUncertain => True
    end.
Proof.
  intros P0 P1 Q Hint Hs.
  unfold b64_orient_sign_stage_d_cc.
  pose proof (b64_orient_sign_filtered_sound_small_int P0 P1 Q Hint) as Hfilt.
  pose proof (b64_orient_sign_exact_cc_sound P0 P1 Q (int_safe_cc_domain P0 P1 Q Hint) Hs)
    as Hexact.
  destruct (b64_orient_sign_filtered P0 P1 Q);
    [ exact Hfilt | exact Hfilt | exact Hfilt | exact Hexact | exact Hexact ].
Qed.

Theorem b64_orient_sign_stage_d_cc_tiny_regime_decisive :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_tiny_int_safe P0 P1 Q ->
    cross_R_BP P0 P1 Q <> 0 ->
    b64_orient_sign_stage_d_cc P0 P1 Q <> OrientRUncertain.
Proof.
  intros P0 P1 Q Htiny Hnz.
  pose proof (b64_orient_sign_filtered_tiny_regime_decisive P0 P1 Q Htiny Hnz) as HnotU.
  unfold b64_orient_sign_stage_d_cc.
  destruct (b64_orient_sign_filtered P0 P1 Q) eqn:Hf; try congruence.
  exact (proj2 (b64_orient_sign_exact_cc_definite P0 P1 Q)).
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_orient_sign_exact_cc_sound.
Print Assumptions b64_orient_sign_exact_cc_definite.
Print Assumptions int_safe_cc_domain.
Print Assumptions b64_orient_sign_stage_d_cc_sound.
Print Assumptions b64_orient_sign_stage_d_cc_tiny_regime_decisive.
