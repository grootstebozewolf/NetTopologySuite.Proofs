(* ==========================================================================
   Orient_b64_robust.v
   --------------------------------------------------------------------------
   A FAST orientation predicate that is SOUND over the entire binary64 plane.

   The Shewchuk Stage-A float filter `b64_orient_sign_filtered` is fast but
   only proven sound for integer coordinates |coord| <= 2^25; the adversarial
   sweep (oracle/adversarial_tests.txt) shows it COMMITS a wrong `OrientRZero`
   just past that boundary (its `Some Eq => OrientRZero` branch trusts a
   float-zero determinant with no error-bound guard), and float arithmetic
   overflows to NaN past the DD band entirely.

   `b64_orient_robust` is the adaptive fix: trust the filter's committed
   Pos/Neg, but route Zero / Uncertain / Nan -- which includes EVERY
   out-of-band overflow case and the unguarded float-zero case -- to the
   EXACT bignum route `b64_orient2d_exact` (proven sound over ALL finite
   binary64 by `b64_orient2d_exact_sound`).

   Soundness over the entire plane (`b64_orient_robust_sound`) is then:
     - Zero / Uncertain / Nan branches: UNCONDITIONAL, via the exact route;
     - Pos / Neg branches: under the single named hypothesis
       `filter_forward_sound` -- the Stage-A forward-error bound (the filter's
       committed sign is correct).  That bound holds on the no-overflow band
       and is the deferred general-soundness obligation; crucially it is
       DISCHARGEABLE on the integer regime from the existing
       `b64_orient_sign_filtered_sound_small_int`, giving an UNCONDITIONAL
       corollary there.

   So the only residual gap for full-plane soundness is the filter's
   forward-error on its committed cases -- not the expansion-arithmetic
   Theorem 13, and not the unguarded-zero / overflow cases (handled here).
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia.
From Flocq Require Import IEEE754.Binary.
From NTS.Proofs.Flocq Require Import Validate_binary64 Orientation_b64
                                      Orient_b64_R Orient_b64_sound
                                      Orient_b64_exact Orient_b64_exact_full.

Open Scope R_scope.

(* Map the exact predicate's Z verdict (= Z.sgn det in {-1,0,1}) to a sign. *)
Definition robust_from_exact (z : Z) : orient_sign_robust :=
  if Z.eqb z 1 then OrientRPos
  else if Z.eqb z (-1) then OrientRNeg
  else OrientRZero.

Definition b64_orient_robust (P0 P1 Q : BPoint) : orient_sign_robust :=
  match b64_orient_sign_filtered P0 P1 Q with
  | OrientRPos => OrientRPos
  | OrientRNeg => OrientRNeg
  | OrientRZero | OrientRUncertain | OrientRNan =>
      robust_from_exact (b64_orient2d_exact P0 P1 Q)
  end.

(* The filter's committed signs are correct -- the Stage-A forward-error
   obligation (holds on the no-overflow band; deferred in general). *)
Definition filter_forward_sound (P0 P1 Q : BPoint) : Prop :=
  (b64_orient_sign_filtered P0 P1 Q = OrientRPos -> 0 < cross_R_BP P0 P1 Q) /\
  (b64_orient_sign_filtered P0 P1 Q = OrientRNeg -> cross_R_BP P0 P1 Q < 0).

(* The exact verdict is a sign: in {1, 0, -1}. *)
Lemma b64_orient2d_exact_trichotomy : forall P0 P1 Q : BPoint,
  b64_orient2d_exact P0 P1 Q = 1%Z \/
  b64_orient2d_exact P0 P1 Q = 0%Z \/
  b64_orient2d_exact P0 P1 Q = (-1)%Z.
Proof.
  intros P0 P1 Q. unfold b64_orient2d_exact.
  destruct (Z.sgn_spec (b64_orient2d_intdet P0 P1 Q)) as [[_ H]|[[_ H]|[_ H]]];
    auto.
Qed.

(* --------------------------------------------------------------------------
   Full-plane soundness: the robust verdict's sign matches the true sign,
   for ALL finite binary64, under the filter forward-error hypothesis (which
   only constrains the Pos/Neg committed cases).
   -------------------------------------------------------------------------- *)
Theorem b64_orient_robust_sound : forall P0 P1 Q : BPoint,
  all_finite P0 P1 Q ->
  filter_forward_sound P0 P1 Q ->
  (b64_orient_robust P0 P1 Q = OrientRPos -> 0 < cross_R_BP P0 P1 Q) /\
  (b64_orient_robust P0 P1 Q = OrientRNeg -> cross_R_BP P0 P1 Q < 0) /\
  (b64_orient_robust P0 P1 Q = OrientRZero -> cross_R_BP P0 P1 Q = 0).
Proof.
  intros P0 P1 Q Hfin [Hfp Hfn].
  pose proof (b64_orient2d_exact_sound P0 P1 Q Hfin) as [HEp [HEn HEz]].
  pose proof (b64_orient2d_exact_trichotomy P0 P1 Q) as Htri.
  unfold b64_orient_robust.
  destruct (b64_orient_sign_filtered P0 P1 Q) eqn:Ef.
  - (* OrientRPos: trusted *)
    repeat split; intro H';
      first [ apply Hfp; (reflexivity || exact Ef) | discriminate ].
  - (* OrientRNeg: trusted *)
    repeat split; intro H';
      first [ apply Hfn; (reflexivity || exact Ef) | discriminate ].
  - (* OrientRZero -> exact fallback *)
    unfold robust_from_exact; destruct Htri as [Hx|[Hx|Hx]]; rewrite Hx;
      repeat split; intro H';
      first [ apply (proj2 HEp); exact Hx
            | apply (proj2 HEn); exact Hx
            | apply (proj2 HEz); exact Hx
            | discriminate ].
  - (* OrientRNan -> exact fallback (identical) *)
    unfold robust_from_exact; destruct Htri as [Hx|[Hx|Hx]]; rewrite Hx;
      repeat split; intro H';
      first [ apply (proj2 HEp); exact Hx
            | apply (proj2 HEn); exact Hx
            | apply (proj2 HEz); exact Hx
            | discriminate ].
  - (* OrientRUncertain -> exact fallback (identical) *)
    unfold robust_from_exact; destruct Htri as [Hx|[Hx|Hx]]; rewrite Hx;
      repeat split; intro H';
      first [ apply (proj2 HEp); exact Hx
            | apply (proj2 HEn); exact Hx
            | apply (proj2 HEz); exact Hx
            | discriminate ].
Qed.

(* --------------------------------------------------------------------------
   Integer regime: the forward-error hypothesis is dischargeable from the
   existing Stage-A integer soundness, so the robust predicate is
   UNCONDITIONALLY sound there.
   -------------------------------------------------------------------------- *)
Lemma filter_forward_sound_small_int : forall P0 P1 Q : BPoint,
  orient2d_inputs_int_safe P0 P1 Q -> filter_forward_sound P0 P1 Q.
Proof.
  intros P0 P1 Q Hsafe.
  pose proof (b64_orient_sign_filtered_sound_small_int P0 P1 Q Hsafe) as H.
  unfold filter_forward_sound; split; intro Ef; rewrite Ef in H; exact H.
Qed.

Corollary b64_orient_robust_sound_small_int : forall P0 P1 Q : BPoint,
  all_finite P0 P1 Q ->
  orient2d_inputs_int_safe P0 P1 Q ->
  (b64_orient_robust P0 P1 Q = OrientRPos -> 0 < cross_R_BP P0 P1 Q) /\
  (b64_orient_robust P0 P1 Q = OrientRNeg -> cross_R_BP P0 P1 Q < 0) /\
  (b64_orient_robust P0 P1 Q = OrientRZero -> cross_R_BP P0 P1 Q = 0).
Proof.
  intros P0 P1 Q Hfin Hsafe.
  apply b64_orient_robust_sound; [ exact Hfin | apply filter_forward_sound_small_int; exact Hsafe ].
Qed.

Print Assumptions b64_orient_robust_sound.
Print Assumptions b64_orient_robust_sound_small_int.
