(* ==========================================================================
   Orient_b64_exact_full.v  --  EXACT orientation soundness over the FULL
   binary64 plane (no integer / |coord| <= 2^25 restriction).

   State-of-the-art exact geometric computation, the honest backing for
   JTS #1106: a provably-sound orientation predicate over arbitrary double
   coordinates.

   Key idea (common-exponent integer determinant).  Every finite binary64 is
   exactly  B2R x = IZR m * 2^e  (Flocq's `B2R` on the `B754_finite`
   constructor IS this F2R).  Let E = min of the six input exponents; then
   every coordinate is  IZR M * 2^E  with M = m * 2^(e-E) an INTEGER.  The
   orientation determinant is degree-2 homogeneous, so

       cross_R_BP = 2^E * 2^E * IZR(IntDet)

   with IntDet the determinant of the integer mantissas (a single `Z`, hence
   arbitrary precision -- no fixed-width-bit ceiling, no rounding).  Since
   2^E * 2^E > 0, the sign of the real determinant equals `Z.sgn IntDet` for
   ALL finite doubles.

   This does NOT prove JTS's double-double `Orientation.index` sound (DD is a
   fast approximation that still fails near-collinear); it is the exact
   ground-truth / spec, sound over the whole plane.
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra.
From Flocq Require Import IEEE754.Binary Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 Orientation_b64
                                      B64_bridge Orient_b64_R Orient_b64_sound
                                      Orient_b64_exact.

Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Exact decode of a finite binary64 into (mantissa, exponent).               *)
(* -------------------------------------------------------------------------- *)

Definition b64_mant (x : binary64) : Z :=
  match x with
  | Binary.B754_finite _ _ s m _ _ => cond_Zopp s (Zpos m)
  | _ => 0%Z
  end.

Definition b64_exp (x : binary64) : Z :=
  match x with
  | Binary.B754_finite _ _ _ _ e _ => e
  | _ => 0%Z
  end.

Lemma b64_decode :
  forall x : binary64,
    Binary.is_finite prec emax x = true ->
    Binary.B2R prec emax x = IZR (b64_mant x) * bpow radix2 (b64_exp x).
Proof.
  intros x Hfin.
  destruct x as [s | s | s pl Hpl | s m e He]; simpl in Hfin; try discriminate Hfin.
  - (* B754_zero *) simpl. unfold F2R; simpl. lra.
  - (* B754_finite *) simpl. unfold F2R; simpl. reflexivity.
Qed.

(* Mantissa rescaled to the common exponent E (integer because e - E >= 0). *)
Definition shifted_mant (x : binary64) (E : Z) : Z :=
  (b64_mant x * 2 ^ (b64_exp x - E))%Z.

Lemma b64_decode_shift :
  forall (x : binary64) (E : Z),
    Binary.is_finite prec emax x = true ->
    (E <= b64_exp x)%Z ->
    Binary.B2R prec emax x = IZR (shifted_mant x E) * bpow radix2 E.
Proof.
  intros x E Hfin Hle.
  rewrite (b64_decode x Hfin).
  unfold shifted_mant.
  rewrite mult_IZR.
  rewrite <- (bpow_radix2_eq_IZR_pow (b64_exp x - E)) by lia.
  rewrite Rmult_assoc, <- bpow_plus.
  replace (b64_exp x - E + E)%Z with (b64_exp x) by lia.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* The exact integer determinant and the exact predicate.                     *)
(* -------------------------------------------------------------------------- *)

Definition b64_min_exp6 (P0 P1 Q : BPoint) : Z :=
  Z.min (b64_exp (bx P0))
   (Z.min (b64_exp (bx P1))
    (Z.min (b64_exp (bx Q))
     (Z.min (b64_exp (by_ P0))
      (Z.min (b64_exp (by_ P1)) (b64_exp (by_ Q)))))).

Definition b64_orient2d_intdet (P0 P1 Q : BPoint) : Z :=
  let E := b64_min_exp6 P0 P1 Q in
  ((shifted_mant (bx P1) E - shifted_mant (bx P0) E)
     * (shifted_mant (by_ Q) E - shifted_mant (by_ P0) E)
   - (shifted_mant (bx Q) E - shifted_mant (bx P0) E)
     * (shifted_mant (by_ P1) E - shifted_mant (by_ P0) E))%Z.

Definition b64_orient2d_exact (P0 P1 Q : BPoint) : Z :=
  Z.sgn (b64_orient2d_intdet P0 P1 Q).

(* -------------------------------------------------------------------------- *)
(* The exact factorisation: cross_R_BP = (2^E)^2 * IZR IntDet.                 *)
(* -------------------------------------------------------------------------- *)

Definition all_finite (P0 P1 Q : BPoint) : Prop :=
  Binary.is_finite prec emax (bx P0) = true /\
  Binary.is_finite prec emax (bx P1) = true /\
  Binary.is_finite prec emax (bx Q)  = true /\
  Binary.is_finite prec emax (by_ P0) = true /\
  Binary.is_finite prec emax (by_ P1) = true /\
  Binary.is_finite prec emax (by_ Q)  = true.

Lemma cross_R_BP_factor :
  forall P0 P1 Q,
    all_finite P0 P1 Q ->
    cross_R_BP P0 P1 Q
    = (bpow radix2 (b64_min_exp6 P0 P1 Q) * bpow radix2 (b64_min_exp6 P0 P1 Q))
      * IZR (b64_orient2d_intdet P0 P1 Q).
Proof.
  intros P0 P1 Q [Hx0 [Hx1 [Hxq [Hy0 [Hy1 Hyq]]]]].
  set (E := b64_min_exp6 P0 P1 Q).
  assert (Le0x : (E <= b64_exp (bx P0))%Z) by (unfold E, b64_min_exp6; lia).
  assert (Le1x : (E <= b64_exp (bx P1))%Z) by (unfold E, b64_min_exp6; lia).
  assert (Leqx : (E <= b64_exp (bx Q))%Z)  by (unfold E, b64_min_exp6; lia).
  assert (Le0y : (E <= b64_exp (by_ P0))%Z) by (unfold E, b64_min_exp6; lia).
  assert (Le1y : (E <= b64_exp (by_ P1))%Z) by (unfold E, b64_min_exp6; lia).
  assert (Leqy : (E <= b64_exp (by_ Q))%Z)  by (unfold E, b64_min_exp6; lia).
  unfold cross_R_BP.
  rewrite (b64_decode_shift (bx P0) E Hx0 Le0x).
  rewrite (b64_decode_shift (bx P1) E Hx1 Le1x).
  rewrite (b64_decode_shift (bx Q) E Hxq Leqx).
  rewrite (b64_decode_shift (by_ P0) E Hy0 Le0y).
  rewrite (b64_decode_shift (by_ P1) E Hy1 Le1y).
  rewrite (b64_decode_shift (by_ Q) E Hyq Leqy).
  unfold b64_orient2d_intdet. fold E.
  rewrite minus_IZR, !mult_IZR, !minus_IZR.
  set (b := bpow radix2 E).
  ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Full-double soundness: the exact predicate's sign = the true sign.         *)
(* -------------------------------------------------------------------------- *)

Lemma bpow_sq_pos : forall E : Z, 0 < bpow radix2 E * bpow radix2 E.
Proof.
  intros E. apply Rmult_lt_0_compat; apply bpow_gt_0.
Qed.

Theorem b64_orient2d_exact_sound :
  forall P0 P1 Q,
    all_finite P0 P1 Q ->
    (0 < cross_R_BP P0 P1 Q   <-> b64_orient2d_exact P0 P1 Q = 1%Z) /\
    (cross_R_BP P0 P1 Q < 0   <-> b64_orient2d_exact P0 P1 Q = (-1)%Z) /\
    (cross_R_BP P0 P1 Q = 0   <-> b64_orient2d_exact P0 P1 Q = 0%Z).
Proof.
  intros P0 P1 Q Hfin.
  pose proof (cross_R_BP_factor P0 P1 Q Hfin) as Hfac.
  set (k := bpow radix2 (b64_min_exp6 P0 P1 Q)
            * bpow radix2 (b64_min_exp6 P0 P1 Q)) in *.
  assert (Hk : 0 < k) by (unfold k; apply bpow_sq_pos).
  unfold b64_orient2d_exact.
  set (d := b64_orient2d_intdet P0 P1 Q) in *.
  (* cross_R_BP = k * IZR d with k > 0; split on the sign of d. *)
  destruct (Z.sgn_spec d) as [[Hd Hs] | [[Hd Hs] | [Hd Hs]]]; rewrite Hs, Hfac.
  - assert (Hid : 0 < IZR d) by (apply IZR_lt; lia).
    assert (Hx : 0 < k * IZR d) by nra.
    repeat split; intro H; solve [reflexivity | lra | discriminate | exfalso; lra].
  - assert (Hx : k * IZR d = 0) by (replace d with 0%Z by lia; simpl; ring).
    repeat split; intro H; solve [reflexivity | lra | discriminate | exfalso; lra].
  - assert (Hid : IZR d < 0) by (apply IZR_lt; lia).
    assert (Hx : k * IZR d < 0) by nra.
    repeat split; intro H; solve [reflexivity | lra | discriminate | exfalso; lra].
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_decode.
Print Assumptions cross_R_BP_factor.
Print Assumptions b64_orient2d_exact_sound.
