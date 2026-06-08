(* ============================================================================
   NetTopologySuite.Proofs.Flocq.InCircle_b64_exact
   ----------------------------------------------------------------------------
   Sign-exactness and integer-regime bit-exactness for `b64_inCircle`.

   Two parallel tracks, mirroring the orient2d story:

     1. Full-double sign exactness (`b64_inCircle_exact`), the common-exponent
        integer-determinant predicate in the style of
        `Orient_b64_exact_full.b64_orient2d_exact`.  The in-circle lifted
        determinant is degree-4 homogeneous, so

            inCircle_R_BP = (2^E)^4 * IZR(IntDet)

        with E the minimum exponent over the sixteen input coordinates.

     2. Integer-regime value exactness (`b64_inCircle_exact_for_small_int`):
        when every coordinate is integer-valued with `|n| <= 2^11`, every
        intermediate in the `b64_inCircle` chain stays inside binary64's
        53-bit integer-exactness window (tighter than orient2d's 2^25 because
        the determinant has degree-4 terms).  The rounded value equals
        `inCircle_R_BP` on the nose.

     3. Perron worst-case witness (mirrors `KakeyaOrient2d_b64.v`): stage-10
        Perron thin sliver scaled by `2^11` into the arc integer regime, with
        chord endpoints carrying opposite `inCircle_R_BP` signs.

   Closes issue #64 ask #4b and unblocks the ARC_* oracle sign bridges.

   No `Admitted`, no `Axiom`, no `Parameter`.
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra.
From Flocq Require Import IEEE754.Binary IEEE754.BinarySingleNaN Core.

From NTS.Proofs        Require Import Distance ArcOrient.
From NTS.Proofs.Flocq  Require Import Validate_binary64 InCircle_b64_compute
                                      B64_bridge Orient_b64_exact
                                      Orient_b64_exact_full Orient_b64_sound
                                      Intersect_b64.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* BPoint bridge to the R-side inCircle predicate.                              *)
(* -------------------------------------------------------------------------- *)

Definition inCircle_R_BP (A B C P : BPoint) : R :=
  let xA := Binary.B2R prec emax (bx A) in
  let yA := Binary.B2R prec emax (by_ A) in
  let xB := Binary.B2R prec emax (bx B) in
  let yB := Binary.B2R prec emax (by_ B) in
  let xC := Binary.B2R prec emax (bx C) in
  let yC := Binary.B2R prec emax (by_ C) in
  let xP := Binary.B2R prec emax (bx P) in
  let yP := Binary.B2R prec emax (by_ P) in
  let ax := xA - xP in let ay := yA - yP in
  let bx' := xB - xP in let by' := yB - yP in
  let cx := xC - xP in let cy := yC - yP in
  let na := ax * ax + ay * ay in
  let nb := bx' * bx' + by' * by' in
  let nc := cx * cx + cy * cy in
  ax * (by' * nc - cy * nb) - ay * (bx' * nc - cx * nb) + na * (bx' * cy - cx * by').

Lemma inCircle_R_BP_eq_inCircle_BP2P :
  forall A B C P,
    inCircle_R_BP A B C P
      = inCircle_R (BP2P A) (BP2P B) (BP2P C) (BP2P P).
Proof.
  intros A B C P.
  unfold inCircle_R_BP, inCircle_R, BP2P, px, py.
  simpl. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Track 1: full-double sign exactness (b64_orient2d_exact pattern).            *)
(* -------------------------------------------------------------------------- *)

Definition Zfold_min8 (e1 e2 e3 e4 e5 e6 e7 e8 : Z) : Z :=
  Z.min e1 (Z.min e2 (Z.min e3 (Z.min e4 (Z.min e5 (Z.min e6 (Z.min e7 e8)))))).

Lemma Zfold_min8_le1 : forall e1 e2 e3 e4 e5 e6 e7 e8 : Z,
  (Zfold_min8 e1 e2 e3 e4 e5 e6 e7 e8 <= e1)%Z.
Proof. intros. unfold Zfold_min8. lia. Qed.

Lemma Zfold_min8_le2 : forall e1 e2 e3 e4 e5 e6 e7 e8 : Z,
  (Zfold_min8 e1 e2 e3 e4 e5 e6 e7 e8 <= e2)%Z.
Proof. intros. unfold Zfold_min8. lia. Qed.

Lemma Zfold_min8_le3 : forall e1 e2 e3 e4 e5 e6 e7 e8 : Z,
  (Zfold_min8 e1 e2 e3 e4 e5 e6 e7 e8 <= e3)%Z.
Proof. intros. unfold Zfold_min8. lia. Qed.

Lemma Zfold_min8_le4 : forall e1 e2 e3 e4 e5 e6 e7 e8 : Z,
  (Zfold_min8 e1 e2 e3 e4 e5 e6 e7 e8 <= e4)%Z.
Proof. intros. unfold Zfold_min8. lia. Qed.

Lemma Zfold_min8_le5 : forall e1 e2 e3 e4 e5 e6 e7 e8 : Z,
  (Zfold_min8 e1 e2 e3 e4 e5 e6 e7 e8 <= e5)%Z.
Proof. intros. unfold Zfold_min8. lia. Qed.

Lemma Zfold_min8_le6 : forall e1 e2 e3 e4 e5 e6 e7 e8 : Z,
  (Zfold_min8 e1 e2 e3 e4 e5 e6 e7 e8 <= e6)%Z.
Proof. intros. unfold Zfold_min8. lia. Qed.

Lemma Zfold_min8_le7 : forall e1 e2 e3 e4 e5 e6 e7 e8 : Z,
  (Zfold_min8 e1 e2 e3 e4 e5 e6 e7 e8 <= e7)%Z.
Proof. intros. unfold Zfold_min8. lia. Qed.

Lemma Zfold_min8_le8 : forall e1 e2 e3 e4 e5 e6 e7 e8 : Z,
  (Zfold_min8 e1 e2 e3 e4 e5 e6 e7 e8 <= e8)%Z.
Proof. intros. unfold Zfold_min8. lia. Qed.

Definition b64_min_exp16 (A B C P : BPoint) : Z :=
  Zfold_min8
    (b64_exp (bx A)) (b64_exp (by_ A))
    (b64_exp (bx B)) (b64_exp (by_ B))
    (b64_exp (bx C)) (b64_exp (by_ C))
    (b64_exp (bx P)) (b64_exp (by_ P)).

Definition b64_inCircle_intdet (A B C P : BPoint) : Z :=
  let E := b64_min_exp16 A B C P in
  let ax := (shifted_mant (bx A) E - shifted_mant (bx P) E)%Z in
  let ay := (shifted_mant (by_ A) E - shifted_mant (by_ P) E)%Z in
  let bx' := (shifted_mant (bx B) E - shifted_mant (bx P) E)%Z in
  let by' := (shifted_mant (by_ B) E - shifted_mant (by_ P) E)%Z in
  let cx := (shifted_mant (bx C) E - shifted_mant (bx P) E)%Z in
  let cy := (shifted_mant (by_ C) E - shifted_mant (by_ P) E)%Z in
  let na := (ax * ax + ay * ay)%Z in
  let nb := (bx' * bx' + by' * by')%Z in
  let nc := (cx * cx + cy * cy)%Z in
  (ax * (by' * nc - cy * nb)%Z
   - ay * (bx' * nc - cx * nb)%Z
   + na * (bx' * cy - cx * by')%Z)%Z.

Definition b64_inCircle_exact (A B C P : BPoint) : Z :=
  Z.sgn (b64_inCircle_intdet A B C P).

Definition all_finite16 (A B C P : BPoint) : Prop :=
  Binary.is_finite prec emax (bx A)  = true /\
  Binary.is_finite prec emax (by_ A)  = true /\
  Binary.is_finite prec emax (bx B)  = true /\
  Binary.is_finite prec emax (by_ B)  = true /\
  Binary.is_finite prec emax (bx C)  = true /\
  Binary.is_finite prec emax (by_ C)  = true /\
  Binary.is_finite prec emax (bx P)  = true /\
  Binary.is_finite prec emax (by_ P)  = true.

Lemma IZR_mul_diff (za zc : Z) (rb : R) :
  IZR za * rb - IZR zc * rb = IZR (za - zc)%Z * rb.
Proof. rewrite <- Rmult_minus_distr_r, minus_IZR. reflexivity. Qed.

Lemma IZR_mul_sq (za : Z) (rb : R) :
  (IZR za * rb) * (IZR za * rb) = IZR (za * za)%Z * (rb * rb).
Proof.
  transitivity (IZR za * IZR za * rb * rb); [ring |].
  rewrite mult_IZR. ring.
Qed.

Lemma IZR_sq_sum (z1 z2 : Z) :
  IZR z1 * IZR z1 + IZR z2 * IZR z2 = IZR (z1 * z1 + z2 * z2)%Z.
Proof.
  rewrite <- !mult_IZR.
  rewrite <- plus_IZR.
  reflexivity.
Qed.

Lemma IZR_coord_sq_pair (z1 z2 : Z) (b : R) :
  (IZR z1 * b) * (IZR z1 * b) + (IZR z2 * b) * (IZR z2 * b)
  = IZR ((z1 * z1 + z2 * z2)%Z) * (b * b).
Proof.
  rewrite !IZR_mul_sq.
  rewrite <- Rmult_plus_distr_r, plus_IZR.
  reflexivity.
Qed.

Lemma b64_shift_diff (x64 y64 : binary64) (Ez : Z) :
  Binary.is_finite prec emax x64 = true ->
  Binary.is_finite prec emax y64 = true ->
  (Ez <= b64_exp x64)%Z ->
  (Ez <= b64_exp y64)%Z ->
  Binary.B2R prec emax x64 - Binary.B2R prec emax y64
    = IZR (shifted_mant x64 Ez - shifted_mant y64 Ez) * bpow radix2 Ez.
Proof.
  intros Hx Hy Hlex Hley.
  rewrite (b64_decode_shift x64 Ez Hx Hlex), (b64_decode_shift y64 Ez Hy Hley).
  rewrite <- Rmult_minus_distr_r, minus_IZR. reflexivity.
Qed.

Lemma bpow_quartic_pos : forall E : Z,
  0 < bpow radix2 E * bpow radix2 E * bpow radix2 E * bpow radix2 E.
Proof.
  intros E.
  repeat apply Rmult_lt_0_compat; apply bpow_gt_0.
Qed.

Lemma inCircle_Zdet_distrib :
  forall (axz ayz bxz byz cxz cyz : Z),
  (axz * byz * (cxz * cxz + cyz * cyz) - axz * cyz * (bxz * bxz + byz * byz)
   - ayz * bxz * (cxz * cxz + cyz * cyz) + ayz * cxz * (bxz * bxz + byz * byz)
   + (axz * axz + ayz * ayz) * (bxz * cyz - cxz * byz))%Z
  = (axz * (byz * (cxz * cxz + cyz * cyz) - cyz * (bxz * bxz + byz * byz))%Z
     - ayz * (bxz * (cxz * cxz + cyz * cyz) - cxz * (bxz * bxz + byz * byz))%Z
     + (axz * axz + ayz * ayz) * (bxz * cyz - cxz * byz))%Z.
Proof.
  intros.
  Open Scope Z_scope.
  ring.
  Close Scope Z_scope.
Qed.

Lemma inCircle_shift_quartic_IZR_pack :
  forall (axz ayz bxz byz cxz cyz : Z),
  IZR axz * (IZR byz * IZR ((cxz * cxz + cyz * cyz)%Z) - IZR cyz * IZR ((bxz * bxz + byz * byz)%Z))
  - IZR ayz * (IZR bxz * IZR ((cxz * cxz + cyz * cyz)%Z) - IZR cxz * IZR ((bxz * bxz + byz * byz)%Z))
  + IZR ((axz * axz + ayz * ayz)%Z)
    * (IZR bxz * IZR cyz - IZR cxz * IZR byz)
  = IZR ((axz * byz * (cxz * cxz + cyz * cyz)
          - axz * cyz * (bxz * bxz + byz * byz)
          - ayz * bxz * (cxz * cxz + cyz * cyz)
          + ayz * cxz * (bxz * bxz + byz * byz)
          + (axz * axz + ayz * ayz) * (bxz * cyz - cxz * byz))%Z).
Proof.
  intros axz ayz bxz byz cxz cyz.
  repeat rewrite Rmult_minus_distr_l.
  repeat rewrite Rmult_assoc.
  repeat rewrite mult_IZR.
  repeat rewrite minus_IZR.
  repeat rewrite Rmult_minus_distr_l.
  repeat rewrite Rmult_assoc.
  repeat rewrite <- mult_IZR.
  repeat rewrite <- minus_IZR.
  repeat rewrite <- plus_IZR.
  f_equal.
  Open Scope Z_scope.
  ring.
  Close Scope Z_scope.
Qed.

Lemma inCircle_shift_quartic_homog :
  forall (axz ayz bxz byz cxz cyz : Z) (b : R),
  (IZR axz * b) * ((IZR byz * b) * (IZR ((cxz * cxz + cyz * cyz)%Z) * (b * b))
                   - (IZR cyz * b) * (IZR ((bxz * bxz + byz * byz)%Z) * (b * b)))
  - (IZR ayz * b) * ((IZR bxz * b) * (IZR ((cxz * cxz + cyz * cyz)%Z) * (b * b))
                   - (IZR cxz * b) * (IZR ((bxz * bxz + byz * byz)%Z) * (b * b)))
  + (IZR ((axz * axz + ayz * ayz)%Z) * (b * b))
    * ((IZR bxz * b) * (IZR cyz * b) - (IZR cxz * b) * (IZR byz * b))
  = (b * b * b * b)
    * IZR ((axz * (byz * (cxz * cxz + cyz * cyz) - cyz * (bxz * bxz + byz * byz))%Z
            - ayz * (bxz * (cxz * cxz + cyz * cyz) - cxz * (bxz * bxz + byz * byz))%Z
            + (axz * axz + ayz * ayz) * (bxz * cyz - cxz * byz))%Z).
Proof.
  intros axz ayz bxz byz cxz cyz b.
  set (uax := IZR axz).
  set (uay := IZR ayz).
  set (ubx := IZR bxz).
  set (uby := IZR byz).
  set (ucx := IZR cxz).
  set (ucy := IZR cyz).
  set (una := IZR ((axz * axz + ayz * ayz)%Z)).
  set (unb := IZR ((bxz * bxz + byz * byz)%Z)).
  set (unc := IZR ((cxz * cxz + cyz * cyz)%Z)).
  transitivity (b * b * b * b
    * (uax * (uby * unc - ucy * unb)
       - uay * (ubx * unc - ucx * unb)
       + una * (ubx * ucy - ucx * uby))).
  - repeat (match goal with
            | |- context[IZR axz] => change (IZR axz) with uax
            | |- context[IZR ayz] => change (IZR ayz) with uay
            | |- context[IZR bxz] => change (IZR bxz) with ubx
            | |- context[IZR byz] => change (IZR byz) with uby
            | |- context[IZR cxz] => change (IZR cxz) with ucx
            | |- context[IZR cyz] => change (IZR cyz) with ucy
            | |- context[IZR ((axz * axz + ayz * ayz)%Z)] =>
                change (IZR ((axz * axz + ayz * ayz)%Z)) with una
            | |- context[IZR ((bxz * bxz + byz * byz)%Z)] =>
                change (IZR ((bxz * bxz + byz * byz)%Z)) with unb
            | |- context[IZR ((cxz * cxz + cyz * cyz)%Z)] =>
                change (IZR ((cxz * cxz + cyz * cyz)%Z)) with unc
            end).
    ring.
  - f_equal.
    transitivity (IZR ((axz * byz * (cxz * cxz + cyz * cyz)
                        - axz * cyz * (bxz * bxz + byz * byz)
                        - ayz * bxz * (cxz * cxz + cyz * cyz)
                        + ayz * cxz * (bxz * bxz + byz * byz)
                        + (axz * axz + ayz * ayz) * (bxz * cyz - cxz * byz))%Z)).
    + unfold uax, uay, ubx, uby, ucx, ucy, una, unb, unc.
      apply inCircle_shift_quartic_IZR_pack.
    + f_equal. apply inCircle_Zdet_distrib.
Qed.

Lemma inCircle_R_BP_factor :
  forall A B C P,
    all_finite16 A B C P ->
    inCircle_R_BP A B C P
    = (bpow radix2 (b64_min_exp16 A B C P)
       * bpow radix2 (b64_min_exp16 A B C P)
       * bpow radix2 (b64_min_exp16 A B C P)
       * bpow radix2 (b64_min_exp16 A B C P))
      * IZR (b64_inCircle_intdet A B C P).
Proof.
  intros A B C P [HxA [HyA [HxB [HyB [HxC [HyC [HxP HyP]]]]]]].
  set (E := b64_min_exp16 A B C P).
  assert (LeAx : (E <= b64_exp (bx A))%Z)
    by (unfold E, b64_min_exp16; apply Zfold_min8_le1).
  assert (LeAy : (E <= b64_exp (by_ A))%Z)
    by (unfold E, b64_min_exp16; apply Zfold_min8_le2).
  assert (LeBx : (E <= b64_exp (bx B))%Z)
    by (unfold E, b64_min_exp16; apply Zfold_min8_le3).
  assert (LeBy : (E <= b64_exp (by_ B))%Z)
    by (unfold E, b64_min_exp16; apply Zfold_min8_le4).
  assert (LeCx : (E <= b64_exp (bx C))%Z)
    by (unfold E, b64_min_exp16; apply Zfold_min8_le5).
  assert (LeCy : (E <= b64_exp (by_ C))%Z)
    by (unfold E, b64_min_exp16; apply Zfold_min8_le6).
  assert (LePx : (E <= b64_exp (bx P))%Z)
    by (unfold E, b64_min_exp16; apply Zfold_min8_le7).
  assert (LePy : (E <= b64_exp (by_ P))%Z)
    by (unfold E, b64_min_exp16; apply Zfold_min8_le8).
  unfold inCircle_R_BP, b64_inCircle_intdet. fold E.
  set (b := bpow radix2 E).
  replace (Binary.B2R prec emax (bx A) - Binary.B2R prec emax (bx P))
    with (IZR (shifted_mant (bx A) E - shifted_mant (bx P) E) * b)
    by (symmetry; apply b64_shift_diff; assumption).
  replace (Binary.B2R prec emax (by_ A) - Binary.B2R prec emax (by_ P))
    with (IZR (shifted_mant (by_ A) E - shifted_mant (by_ P) E) * b)
    by (symmetry; apply b64_shift_diff; assumption).
  replace (Binary.B2R prec emax (bx B) - Binary.B2R prec emax (bx P))
    with (IZR (shifted_mant (bx B) E - shifted_mant (bx P) E) * b)
    by (symmetry; apply b64_shift_diff; assumption).
  replace (Binary.B2R prec emax (by_ B) - Binary.B2R prec emax (by_ P))
    with (IZR (shifted_mant (by_ B) E - shifted_mant (by_ P) E) * b)
    by (symmetry; apply b64_shift_diff; assumption).
  replace (Binary.B2R prec emax (bx C) - Binary.B2R prec emax (bx P))
    with (IZR (shifted_mant (bx C) E - shifted_mant (bx P) E) * b)
    by (symmetry; apply b64_shift_diff; assumption).
  replace (Binary.B2R prec emax (by_ C) - Binary.B2R prec emax (by_ P))
    with (IZR (shifted_mant (by_ C) E - shifted_mant (by_ P) E) * b)
    by (symmetry; apply b64_shift_diff; assumption).
  set (axz := (shifted_mant (bx A) E - shifted_mant (bx P) E)%Z).
  set (ayz := (shifted_mant (by_ A) E - shifted_mant (by_ P) E)%Z).
  set (bxz := (shifted_mant (bx B) E - shifted_mant (bx P) E)%Z).
  set (byz := (shifted_mant (by_ B) E - shifted_mant (by_ P) E)%Z).
  set (cxz := (shifted_mant (bx C) E - shifted_mant (bx P) E)%Z).
  set (cyz := (shifted_mant (by_ C) E - shifted_mant (by_ P) E)%Z).
  repeat (
    match goal with
    | |- context[bpow radix2 E] => change (bpow radix2 E) with b
    end).
  repeat rewrite (IZR_coord_sq_pair axz ayz b).
  repeat rewrite (IZR_coord_sq_pair bxz byz b).
  repeat rewrite (IZR_coord_sq_pair cxz cyz b).
  repeat rewrite Rmult_assoc.
  transitivity (b * b * b * b
    * IZR ((axz * (byz * (cxz * cxz + cyz * cyz) - cyz * (bxz * bxz + byz * byz))%Z
            - ayz * (bxz * (cxz * cxz + cyz * cyz) - cxz * (bxz * bxz + byz * byz))%Z
            + (axz * axz + ayz * ayz) * (bxz * cyz - cxz * byz))%Z)).
  - set (uax := IZR axz).
    set (uay := IZR ayz).
    set (ubx := IZR bxz).
    set (uby := IZR byz).
    set (ucx := IZR cxz).
    set (ucy := IZR cyz).
    set (una := IZR ((axz * axz + ayz * ayz)%Z)).
    set (unb := IZR ((bxz * bxz + byz * byz)%Z)).
    set (unc := IZR ((cxz * cxz + cyz * cyz)%Z)).
    transitivity (b * b * b * b
      * (uax * (uby * unc - ucy * unb)
         - uay * (ubx * unc - ucx * unb)
         + una * (ubx * ucy - ucx * uby))).
    + repeat (match goal with
              | |- context[IZR axz] => change (IZR axz) with uax
              | |- context[IZR ayz] => change (IZR ayz) with uay
              | |- context[IZR bxz] => change (IZR bxz) with ubx
              | |- context[IZR byz] => change (IZR byz) with uby
              | |- context[IZR cxz] => change (IZR cxz) with ucx
              | |- context[IZR cyz] => change (IZR cyz) with ucy
              | |- context[IZR ((axz * axz + ayz * ayz)%Z)] =>
                  change (IZR ((axz * axz + ayz * ayz)%Z)) with una
              | |- context[IZR ((bxz * bxz + byz * byz)%Z)] =>
                  change (IZR ((bxz * bxz + byz * byz)%Z)) with unb
              | |- context[IZR ((cxz * cxz + cyz * cyz)%Z)] =>
                  change (IZR ((cxz * cxz + cyz * cyz)%Z)) with unc
              end).
      ring.
    + f_equal.
      transitivity (IZR ((axz * byz * (cxz * cxz + cyz * cyz)
                          - axz * cyz * (bxz * bxz + byz * byz)
                          - ayz * bxz * (cxz * cxz + cyz * cyz)
                          + ayz * cxz * (bxz * bxz + byz * byz)
                          + (axz * axz + ayz * ayz) * (bxz * cyz - cxz * byz))%Z)).
      * unfold uax, uay, ubx, uby, ucx, ucy, una, unb, unc.
        apply inCircle_shift_quartic_IZR_pack.
      * f_equal. apply inCircle_Zdet_distrib.
  - unfold b, b64_inCircle_intdet.
    fold axz; fold ayz; fold bxz; fold byz; fold cxz; fold cyz.
    repeat rewrite Rmult_assoc.
    reflexivity.
Qed.

Theorem b64_inCircle_exact_sound :
  forall A B C P,
    all_finite16 A B C P ->
    (0 < inCircle_R_BP A B C P   <-> b64_inCircle_exact A B C P = 1%Z) /\
    (inCircle_R_BP A B C P < 0   <-> b64_inCircle_exact A B C P = (-1)%Z) /\
    (inCircle_R_BP A B C P = 0   <-> b64_inCircle_exact A B C P = 0%Z).
Proof.
  intros A B C P Hfin.
  pose proof (inCircle_R_BP_factor A B C P Hfin) as Hfac.
  set (k := bpow radix2 (b64_min_exp16 A B C P)
            * bpow radix2 (b64_min_exp16 A B C P)
            * bpow radix2 (b64_min_exp16 A B C P)
            * bpow radix2 (b64_min_exp16 A B C P)) in *.
  assert (Hk : 0 < k) by (unfold k; apply bpow_quartic_pos).
  unfold b64_inCircle_exact.
  set (d := b64_inCircle_intdet A B C P) in *.
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
(* Track 2: integer-regime bit-exactness for computed `b64_inCircle`.           *)
(*                                                                            *)
(* Bound `|coord| <= 2^11` (tighter than orient2d's 2^25): degree-4 chain.    *)
(* -------------------------------------------------------------------------- *)

Lemma IZR_na_cross_pack (na bx' by' cx cy : Z) :
  IZR na * (IZR bx' * IZR cy - IZR cx * IZR by')
  = IZR na * IZR (bx' * cy - cx * by').
Proof.
  f_equal.
  rewrite <- mult_IZR.
  rewrite <- mult_IZR.
  rewrite <- minus_IZR.
  reflexivity.
Qed.

Lemma inCircle_det_IZR_pack :
  forall (ax ay bx' by' cx cy na nb nc : Z),
  IZR ax * (IZR by' * IZR nc - IZR cy * IZR nb)
  - IZR ay * (IZR bx' * IZR nc - IZR cx * IZR nb)
  + IZR na * IZR (bx' * cy - cx * by')
  = IZR (ax * (by' * nc - cy * nb)
         - ay * (bx' * nc - cx * nb)
         + na * (bx' * cy - cx * by'))%Z.
Proof.
  intros.
  transitivity (IZR ax * (IZR (by' * nc)%Z - IZR (cy * nb)%Z)
                  - IZR ay * (IZR (bx' * nc)%Z - IZR (cx * nb)%Z)
                  + IZR (na * (bx' * cy - cx * by'))%Z).
  { repeat rewrite mult_IZR. reflexivity. }
  pose proof (minus_IZR (by' * nc)%Z (cy * nb)%Z) as H1.
  pose proof (minus_IZR (bx' * nc)%Z (cx * nb)%Z) as H2.
  rewrite <- H1.
  rewrite <- H2.
  transitivity (IZR (ax * (by' * nc - cy * nb))%Z - IZR (ay * (bx' * nc - cx * nb))%Z
                  + IZR (na * (bx' * cy - cx * by'))%Z).
  { repeat rewrite mult_IZR. reflexivity. }
  pose proof (minus_IZR (ax * (by' * nc - cy * nb))%Z (ay * (bx' * nc - cx * nb))%Z) as H3.
  rewrite <- H3.
  rewrite <- plus_IZR.
  reflexivity.
Qed.

Definition arc_coord_int_safe (x : binary64) : Prop :=
  Binary.is_finite prec emax x = true /\
  exists n : Z,
    Binary.B2R prec emax x = IZR n /\ (Z.abs n <= 2 ^ 11)%Z.

Definition inCircle_inputs_int_safe (A B C P : BPoint) : Prop :=
  arc_coord_int_safe (bx A)  /\ arc_coord_int_safe (by_ A) /\
  arc_coord_int_safe (bx B)  /\ arc_coord_int_safe (by_ B) /\
  arc_coord_int_safe (bx C)  /\ arc_coord_int_safe (by_ C) /\
  arc_coord_int_safe (bx P)  /\ arc_coord_int_safe (by_ P).

Lemma arc_diff_bound_2p12 :
  forall (a b : Z),
    (Z.abs a <= 2 ^ 11)%Z -> (Z.abs b <= 2 ^ 11)%Z ->
    (Z.abs (a - b) <= 2 ^ 12)%Z.
Proof. intros. replace (2 ^ 12)%Z with (2 ^ 11 + 2 ^ 11)%Z by lia. lia. Qed.

Lemma arc_sq_bound_2p24 :
  forall (a : Z),
    (Z.abs a <= 2 ^ 12)%Z -> (Z.abs (a * a) <= 2 ^ 24)%Z.
Proof.
  intros a Ha.
  rewrite Z.abs_mul.
  replace (2 ^ 24)%Z with (2 ^ 12 * 2 ^ 12)%Z by lia.
  apply Z.mul_le_mono_nonneg; try apply Z.abs_nonneg; assumption.
Qed.

Lemma arc_sum_sq_bound_2p25 :
  forall (a b : Z),
    (Z.abs a <= 2 ^ 24)%Z -> (Z.abs b <= 2 ^ 24)%Z ->
    (Z.abs (a + b) <= 2 ^ 25)%Z.
Proof. intros. replace (2 ^ 25)%Z with (2 ^ 24 + 2 ^ 24)%Z by lia. lia. Qed.

Lemma arc_product_bound_2p24 :
  forall (a b : Z),
    (Z.abs a <= 2 ^ 12)%Z -> (Z.abs b <= 2 ^ 12)%Z ->
    (Z.abs (a * b) <= 2 ^ 24)%Z.
Proof.
  intros a b Ha Hb.
  rewrite Z.abs_mul.
  replace (2 ^ 24)%Z with (2 ^ 12 * 2 ^ 12)%Z by lia.
  apply Z.mul_le_mono_nonneg; try apply Z.abs_nonneg; assumption.
Qed.

Lemma arc_product_bound_2p37 :
  forall (a b : Z),
    (Z.abs a <= 2 ^ 12)%Z -> (Z.abs b <= 2 ^ 25)%Z ->
    (Z.abs (a * b) <= 2 ^ 37)%Z.
Proof.
  intros a b Ha Hb.
  rewrite Z.abs_mul.
  replace (2 ^ 37)%Z with (2 ^ 12 * 2 ^ 25)%Z by lia.
  apply Z.mul_le_mono_nonneg; try apply Z.abs_nonneg; assumption.
Qed.

Lemma arc_product_bound_2p50_12_38 :
  forall (a b : Z),
    (Z.abs a <= 2 ^ 12)%Z -> (Z.abs b <= 2 ^ 38)%Z ->
    (Z.abs (a * b) <= 2 ^ 50)%Z.
Proof.
  intros a b Ha Hb.
  rewrite Z.abs_mul.
  replace (2 ^ 50)%Z with (2 ^ 12 * 2 ^ 38)%Z by lia.
  apply Z.mul_le_mono_nonneg; try apply Z.abs_nonneg; assumption.
Qed.

Lemma arc_diff_bound_2p25 :
  forall (a b : Z),
    (Z.abs a <= 2 ^ 24)%Z -> (Z.abs b <= 2 ^ 24)%Z ->
    (Z.abs (a - b) <= 2 ^ 25)%Z.
Proof. intros. replace (2 ^ 25)%Z with (2 ^ 24 + 2 ^ 24)%Z by lia. lia. Qed.

Lemma arc_row3_diff_bound_2p38 :
  forall (a b : Z),
    (Z.abs a <= 2 ^ 37)%Z -> (Z.abs b <= 2 ^ 37)%Z ->
    (Z.abs (a - b) <= 2 ^ 38)%Z.
Proof. intros. replace (2 ^ 38)%Z with (2 ^ 37 + 2 ^ 37)%Z by lia. lia. Qed.

Lemma arc_row4_bound_2p50 :
  forall (a b : Z),
    (Z.abs a <= 2 ^ 25)%Z -> (Z.abs b <= 2 ^ 25)%Z ->
    (Z.abs (a * b) <= 2 ^ 50)%Z.
Proof.
  intros a b Ha Hb.
  rewrite Z.abs_mul.
  replace (2 ^ 50)%Z with (2 ^ 25 * 2 ^ 25)%Z by lia.
  apply Z.mul_le_mono_nonneg; try apply Z.abs_nonneg; assumption.
Qed.

Lemma arc_outer_diff_bound_2p51 :
  forall (a b : Z),
    (Z.abs a <= 2 ^ 50)%Z -> (Z.abs b <= 2 ^ 50)%Z ->
    (Z.abs (a - b) <= 2 ^ 51)%Z.
Proof. intros. replace (2 ^ 51)%Z with (2 ^ 50 + 2 ^ 50)%Z by lia. lia. Qed.

Lemma arc_final_sum_bound_2p52 :
  forall (a b : Z),
    (Z.abs a <= 2 ^ 51)%Z -> (Z.abs b <= 2 ^ 50)%Z ->
    (Z.abs (a + b) <= 2 ^ 52)%Z.
Proof.
  intros a b Ha Hb.
  apply (Z.le_trans _ (Z.abs a + Z.abs b)%Z); [apply Z.abs_triangle |].
  apply (Z.le_trans _ (2 ^ 51 + 2 ^ 50)%Z); [lia |].
  replace (2 ^ 51 + 2 ^ 50)%Z with (3 * 2 ^ 50)%Z by lia.
  replace (2 ^ 52)%Z with (4 * 2 ^ 50)%Z by lia.
  lia.
Qed.

Lemma le_2pN_le_2pprec :
  forall (n : Z) (N : Z),
    (0 <= N <= 53)%Z ->
    (Z.abs n <= 2 ^ N)%Z -> (Z.abs n <= 2 ^ prec)%Z.
Proof.
  intros n N HN H.
  apply Z.le_trans with (2 ^ N)%Z; [exact H|].
  unfold prec. apply Z.pow_le_mono_r; lia.
Qed.

Lemma le_2p12_le_2pprec :
  forall n : Z, (Z.abs n <= 2 ^ 12)%Z -> (Z.abs n <= 2 ^ prec)%Z.
Proof. intros n H. apply (le_2pN_le_2pprec n 12); [lia | exact H]. Qed.

Lemma le_2p24_le_2pprec :
  forall n : Z, (Z.abs n <= 2 ^ 24)%Z -> (Z.abs n <= 2 ^ prec)%Z.
Proof. intros n H. apply (le_2pN_le_2pprec n 24); [lia | exact H]. Qed.

Lemma le_2p25_le_2pprec :
  forall n : Z, (Z.abs n <= 2 ^ 25)%Z -> (Z.abs n <= 2 ^ prec)%Z.
Proof. intros n H. apply (le_2pN_le_2pprec n 25); [lia | exact H]. Qed.

Lemma le_2p37_le_2pprec :
  forall n : Z, (Z.abs n <= 2 ^ 37)%Z -> (Z.abs n <= 2 ^ prec)%Z.
Proof. intros n H. apply (le_2pN_le_2pprec n 37); [lia | exact H]. Qed.

Lemma le_2p38_le_2pprec :
  forall n : Z, (Z.abs n <= 2 ^ 38)%Z -> (Z.abs n <= 2 ^ prec)%Z.
Proof. intros n H. apply (le_2pN_le_2pprec n 38); [lia | exact H]. Qed.

Lemma le_2p50_le_2pprec :
  forall n : Z, (Z.abs n <= 2 ^ 50)%Z -> (Z.abs n <= 2 ^ prec)%Z.
Proof. intros n H. apply (le_2pN_le_2pprec n 50); [lia | exact H]. Qed.

Lemma le_2p51_le_2pprec :
  forall n : Z, (Z.abs n <= 2 ^ 51)%Z -> (Z.abs n <= 2 ^ prec)%Z.
Proof. intros n H. apply (le_2pN_le_2pprec n 51); [lia | exact H]. Qed.

Lemma le_2p52_le_2pprec :
  forall n : Z, (Z.abs n <= 2 ^ 52)%Z -> (Z.abs n <= 2 ^ prec)%Z.
Proof. intros n H. apply (le_2pN_le_2pprec n 52); [lia | exact H]. Qed.

Lemma inCircle_int_witness :
  forall A B C P,
    inCircle_inputs_int_safe A B C P ->
    exists n : Z,
      inCircle_R_BP A B C P = IZR n /\ (Z.abs n <= 2 ^ 52)%Z.
Proof.
  intros A B C P Hsafe.
  destruct Hsafe as (HxA & HyA & HxB & HyB & HxC & HyC & HxP & HyP).
  destruct HxA as (_ & nAx & HAxR & HAxb).
  destruct HyA as (_ & nAy & HAyR & HAyb).
  destruct HxB as (_ & nBx & HBxR & HBxb).
  destruct HyB as (_ & nBy & HByR & HByb).
  destruct HxC as (_ & nCx & HCxR & HCxb).
  destruct HyC as (_ & nCy & HCyR & HCyb).
  destruct HxP as (_ & nPx & HPxR & HPxb).
  destruct HyP as (_ & nPy & HPyR & HPyb).
  set (ax := (nAx - nPx)%Z).
  set (ay := (nAy - nPy)%Z).
  set (bx' := (nBx - nPx)%Z).
  set (by' := (nBy - nPy)%Z).
  set (cx := (nCx - nPx)%Z).
  set (cy := (nCy - nPy)%Z).
  set (na := (ax * ax + ay * ay)%Z).
  set (nb := (bx' * bx' + by' * by')%Z).
  set (nc := (cx * cx + cy * cy)%Z).
  set (det := (ax * (by' * nc - cy * nb)%Z
               - ay * (bx' * nc - cx * nb)%Z
               + na * (bx' * cy - cx * by')%Z)%Z).
  exists det.
  split.
  - unfold inCircle_R_BP.
    rewrite HAxR, HAyR, HBxR, HByR, HCxR, HCyR, HPxR, HPyR.
    pose proof (minus_IZR nAx nPx) as Haxz.
    pose proof (minus_IZR nAy nPy) as Hayz.
    pose proof (minus_IZR nBx nPx) as Hbxz.
    pose proof (minus_IZR nBy nPy) as Hbyz.
    pose proof (minus_IZR nCx nPx) as Hcxz.
    pose proof (minus_IZR nCy nPy) as Hcyz.
    rewrite <- Haxz, <- Hayz, <- Hbxz, <- Hbyz, <- Hcxz, <- Hcyz.
    fold ax; fold ay; fold bx'; fold by'; fold cx; fold cy.
    repeat rewrite (IZR_sq_sum cx cy) at 1.
    repeat rewrite (IZR_sq_sum bx' by') at 1.
    rewrite (IZR_sq_sum ax ay) at 1.
    fold na; fold nb; fold nc.
    rewrite (IZR_na_cross_pack na bx' by' cx cy) at 1.
    rewrite (inCircle_det_IZR_pack ax ay bx' by' cx cy na nb nc) at 1.
    unfold det.
    reflexivity.
  - pose proof (arc_diff_bound_2p12 nAx nPx HAxb HPxb) as Bax.
    pose proof (arc_diff_bound_2p12 nAy nPy HAyb HPyb) as Bay.
    pose proof (arc_diff_bound_2p12 nBx nPx HBxb HPxb) as Bbx.
    pose proof (arc_diff_bound_2p12 nBy nPy HByb HPyb) as Bby.
    pose proof (arc_diff_bound_2p12 nCx nPx HCxb HPxb) as Bcx.
    pose proof (arc_diff_bound_2p12 nCy nPy HCyb HPyb) as Bcy.
    pose proof (arc_sq_bound_2p24 ax Bax) as Bax2.
    pose proof (arc_sq_bound_2p24 ay Bay) as Bay2.
    pose proof (arc_sq_bound_2p24 bx' Bbx) as Bbx2.
    pose proof (arc_sq_bound_2p24 by' Bby) as Bby2.
    pose proof (arc_sq_bound_2p24 cx Bcx) as Bcx2.
    pose proof (arc_sq_bound_2p24 cy Bcy) as Bcy2.
    pose proof (arc_sum_sq_bound_2p25 (ax * ax) (ay * ay) Bax2 Bay2) as Bna.
    pose proof (arc_sum_sq_bound_2p25 (bx' * bx') (by' * by') Bbx2 Bby2) as Bnb.
    pose proof (arc_sum_sq_bound_2p25 (cx * cx) (cy * cy) Bcx2 Bcy2) as Bnc.
    pose proof (arc_product_bound_2p37 by' nc Bby Bnc) as Bt1.
    pose proof (arc_product_bound_2p37 cy nb Bcy Bnb) as Bt2.
    pose proof (arc_row3_diff_bound_2p38 (by' * nc) (cy * nb) Bt1 Bt2) as Br1.
    pose proof (arc_product_bound_2p37 bx' nc Bbx Bnc) as Bt3.
    pose proof (arc_product_bound_2p37 cx nb Bcx Bnb) as Bt4.
    pose proof (arc_row3_diff_bound_2p38 (bx' * nc) (cx * nb) Bt3 Bt4) as Br2.
    pose proof (arc_product_bound_2p50_12_38 ax (by' * nc - cy * nb) Bax Br1) as Brow_a.
    pose proof (arc_product_bound_2p50_12_38 ay (bx' * nc - cx * nb) Bay Br2) as Brow_b.
    pose proof (arc_product_bound_2p24 bx' cy Bbx Bcy) as Brc1.
    pose proof (arc_product_bound_2p24 cx by' Bcx Bby) as Brc2.
    pose proof (arc_diff_bound_2p25 (bx' * cy) (cx * by') Brc1 Brc2) as Brc.
    pose proof (arc_row4_bound_2p50 na (bx' * cy - cx * by') Bna Brc) as Brow_c.
    pose proof (arc_outer_diff_bound_2p51
                  (ax * (by' * nc - cy * nb)) (ay * (bx' * nc - cx * nb))
                  Brow_a Brow_b) as Bsub.
    pose proof (arc_final_sum_bound_2p52
                  (ax * (by' * nc - cy * nb) - ay * (bx' * nc - cx * nb))
                  (na * (bx' * cy - cx * by')) Bsub Brow_c) as Bfin.
    unfold det. exact Bfin.
Qed.

Theorem b64_inCircle_exact_for_small_int :
  forall A B C P,
    inCircle_inputs_int_safe A B C P ->
    Binary.B2R prec emax (b64_inCircle A B C P) = inCircle_R_BP A B C P.
Proof.
  intros A B C P Hsafe.
  destruct Hsafe as (HxA & HyA & HxB & HyB & HxC & HyC & HxP & HyP).
  destruct HxA as (FxA & nAx & HAxR & HAxb).
  destruct HyA as (FyA & nAy & HAyR & HAyb).
  destruct HxB as (FxB & nBx & HBxR & HBxb).
  destruct HyB as (FyB & nBy & HByR & HByb).
  destruct HxC as (FxC & nCx & HCxR & HCxb).
  destruct HyC as (FyC & nCy & HCyR & HCyb).
  destruct HxP as (FxP & nPx & HPxR & HPxb).
  destruct HyP as (FyP & nPy & HPyR & HPyb).
  set (axz := (nAx - nPx)%Z).
  set (ayz := (nAy - nPy)%Z).
  set (bxz := (nBx - nPx)%Z).
  set (byz := (nBy - nPy)%Z).
  set (cxz := (nCx - nPx)%Z).
  set (cyz := (nCy - nPy)%Z).
  pose proof (arc_diff_bound_2p12 nAx nPx HAxb HPxb) as Bax.
  pose proof (arc_diff_bound_2p12 nAy nPy HAyb HPyb) as Bay.
  pose proof (arc_diff_bound_2p12 nBx nPx HBxb HPxb) as Bbx.
  pose proof (arc_diff_bound_2p12 nBy nPy HByb HPyb) as Bby.
  pose proof (arc_diff_bound_2p12 nCx nPx HCxb HPxb) as Bcx.
  pose proof (arc_diff_bound_2p12 nCy nPy HCyb HPyb) as Bcy.
  set (ax := b64_minus (bx A) (bx P)) in *.
  set (ay := b64_minus (by_ A) (by_ P)) in *.
  set (bbx := b64_minus (bx B) (bx P)) in *.
  set (bby := b64_minus (by_ B) (by_ P)) in *.
  set (ccx := b64_minus (bx C) (bx P)) in *.
  set (ccy := b64_minus (by_ C) (by_ P)) in *.
  destruct (b64_minus_int_exact _ _ nAx nPx FxA FxP HAxR HPxR
              (le_2p12_le_2pprec axz Bax)) as [Hax_diffR Faxf].
  destruct (b64_minus_int_exact _ _ nAy nPy FyA FyP HAyR HPyR
              (le_2p12_le_2pprec ayz Bay)) as [Hay_diffR Fayf].
  destruct (b64_minus_int_exact _ _ nBx nPx FxB FxP HBxR HPxR
              (le_2p12_le_2pprec bxz Bbx)) as [Hbbx_diffR Fbbxf].
  destruct (b64_minus_int_exact _ _ nBy nPy FyB FyP HByR HPyR
              (le_2p12_le_2pprec byz Bby)) as [Hbby_diffR Fbbyf].
  destruct (b64_minus_int_exact _ _ nCx nPx FxC FxP HCxR HPxR
              (le_2p12_le_2pprec cxz Bcx)) as [Hccx_diffR Fccxf].
  destruct (b64_minus_int_exact _ _ nCy nPy FyC FyP HCyR HPyR
              (le_2p12_le_2pprec cyz Bcy)) as [Hccy_diffR Fccyf].
  pose proof (arc_sq_bound_2p24 axz Bax) as Bax2.
  pose proof (arc_sq_bound_2p24 ayz Bay) as Bay2.
  pose proof (arc_sq_bound_2p24 bxz Bbx) as Bbx2.
  pose proof (arc_sq_bound_2p24 byz Bby) as Bby2.
  pose proof (arc_sq_bound_2p24 cxz Bcx) as Bcx2.
  pose proof (arc_sq_bound_2p24 cyz Bcy) as Bcy2.
  destruct (b64_mult_int_exact _ _ axz axz Faxf Faxf Hax_diffR Hax_diffR
              (le_2p24_le_2pprec (axz * axz) Bax2)) as [Hax2R Fax2].
  destruct (b64_mult_int_exact _ _ ayz ayz Fayf Fayf Hay_diffR Hay_diffR
              (le_2p24_le_2pprec (ayz * ayz) Bay2)) as [Hay2R Fay2].
  destruct (b64_mult_int_exact _ _ bxz bxz Fbbxf Fbbxf Hbbx_diffR Hbbx_diffR
              (le_2p24_le_2pprec (bxz * bxz) Bbx2)) as [Hbbx2R Fbbx2].
  destruct (b64_mult_int_exact _ _ byz byz Fbbyf Fbbyf Hbby_diffR Hbby_diffR
              (le_2p24_le_2pprec (byz * byz) Bby2)) as [Hbby2R Fbby2].
  destruct (b64_mult_int_exact _ _ cxz cxz Fccxf Fccxf Hccx_diffR Hccx_diffR
              (le_2p24_le_2pprec (cxz * cxz) Bcx2)) as [Hccx2R Fccx2].
  destruct (b64_mult_int_exact _ _ cyz cyz Fccyf Fccyf Hccy_diffR Hccy_diffR
              (le_2p24_le_2pprec (cyz * cyz) Bcy2)) as [Hccy2R Fccy2].
  set (naz := (axz * axz + ayz * ayz)%Z).
  set (nbz := (bxz * bxz + byz * byz)%Z).
  set (ncz := (cxz * cxz + cyz * cyz)%Z).
  pose proof (arc_sum_sq_bound_2p25 (axz * axz) (ayz * ayz) Bax2 Bay2) as Bna.
  pose proof (arc_sum_sq_bound_2p25 (bxz * bxz) (byz * byz) Bbx2 Bby2) as Bnb.
  pose proof (arc_sum_sq_bound_2p25 (cxz * cxz) (cyz * cyz) Bcx2 Bcy2) as Bnc.
  destruct (b64_plus_int_exact _ _ (axz * axz) (ayz * ayz) Fax2 Fay2 Hax2R Hay2R
              (le_2p25_le_2pprec naz Bna)) as [HnaR Fna].
  destruct (b64_plus_int_exact _ _ (bxz * bxz) (byz * byz) Fbbx2 Fbby2 Hbbx2R Hbby2R
              (le_2p25_le_2pprec nbz Bnb)) as [HnbR Fnb].
  destruct (b64_plus_int_exact _ _ (cxz * cxz) (cyz * cyz) Fccx2 Fccy2 Hccx2R Hccy2R
              (le_2p25_le_2pprec ncz Bnc)) as [HncR Fnc].
  pose proof (arc_product_bound_2p37 byz ncz Bby Bnc) as Bt1.
  pose proof (arc_product_bound_2p37 cyz nbz Bcy Bnb) as Bt2.
  destruct (b64_mult_int_exact _ _ byz ncz Fbbyf Fnc Hbby_diffR HncR
              (le_2p37_le_2pprec (byz * ncz)%Z Bt1)) as [Ht1aR Ft1a].
  destruct (b64_mult_int_exact _ _ cyz nbz Fccyf Fnb Hccy_diffR HnbR
              (le_2p37_le_2pprec (cyz * nbz)%Z Bt2)) as [Ht1bR Ft1b].
  pose proof (arc_row3_diff_bound_2p38 (byz * ncz) (cyz * nbz) Bt1 Bt2) as Br1d.
  destruct (b64_minus_int_exact _ _ (byz * ncz) (cyz * nbz) Ft1a Ft1b Ht1aR Ht1bR
              (le_2p38_le_2pprec (byz * ncz - cyz * nbz)%Z Br1d)) as [Hr1R Fr1].
  pose proof (arc_product_bound_2p37 bxz ncz Bbx Bnc) as Bt3.
  pose proof (arc_product_bound_2p37 cxz nbz Bcx Bnb) as Bt4.
  destruct (b64_mult_int_exact _ _ bxz ncz Fbbxf Fnc Hbbx_diffR HncR
              (le_2p37_le_2pprec (bxz * ncz)%Z Bt3)) as [Ht2aR Ft2a].
  destruct (b64_mult_int_exact _ _ cxz nbz Fccxf Fnb Hccx_diffR HnbR
              (le_2p37_le_2pprec (cxz * nbz)%Z Bt4)) as [Ht2bR Ft2b].
  pose proof (arc_row3_diff_bound_2p38 (bxz * ncz) (cxz * nbz) Bt3 Bt4) as Br2d.
  destruct (b64_minus_int_exact _ _ (bxz * ncz) (cxz * nbz) Ft2a Ft2b Ht2aR Ht2bR
              (le_2p38_le_2pprec (bxz * ncz - cxz * nbz)%Z Br2d)) as [Hr2R Fr2].
  pose proof (arc_product_bound_2p50_12_38 axz (byz * ncz - cyz * nbz)%Z Bax Br1d) as Browa.
  destruct (b64_mult_int_exact _ _ axz (byz * ncz - cyz * nbz)%Z Faxf Fr1 Hax_diffR Hr1R
              (le_2p50_le_2pprec (axz * (byz * ncz - cyz * nbz))%Z Browa)) as [HrowaR Frowa].
  pose proof (arc_product_bound_2p50_12_38 ayz (bxz * ncz - cxz * nbz)%Z Bay Br2d) as Browb.
  destruct (b64_mult_int_exact _ _ ayz (bxz * ncz - cxz * nbz)%Z Fayf Fr2 Hay_diffR Hr2R
              (le_2p50_le_2pprec (ayz * (bxz * ncz - cxz * nbz))%Z Browb)) as [HrowbR Frowb].
  pose proof (arc_product_bound_2p24 bxz cyz Bbx Bcy) as Brc1z.
  pose proof (arc_product_bound_2p24 cxz byz Bcx Bby) as Brc2z.
  destruct (b64_mult_int_exact _ _ bxz cyz Fbbxf Fccyf Hbbx_diffR Hccy_diffR
              (le_2p24_le_2pprec (bxz * cyz)%Z Brc1z)) as [Hrc1R Frc1].
  destruct (b64_mult_int_exact _ _ cxz byz Fccxf Fbbyf Hccx_diffR Hbby_diffR
              (le_2p24_le_2pprec (cxz * byz)%Z Brc2z)) as [Hrc2R Frc2].
  pose proof (arc_diff_bound_2p25 (bxz * cyz) (cxz * byz) Brc1z Brc2z) as Brcd.
  destruct (b64_minus_int_exact _ _ (bxz * cyz) (cxz * byz) Frc1 Frc2 Hrc1R Hrc2R
              (le_2p25_le_2pprec (bxz * cyz - cxz * byz)%Z Brcd)) as [HrcR Frc].
  pose proof (arc_row4_bound_2p50 naz (bxz * cyz - cxz * byz) Bna Brcd) as Browc.
  destruct (b64_mult_int_exact _ _ naz (bxz * cyz - cxz * byz)%Z Fna Frc HnaR HrcR
              (le_2p50_le_2pprec (naz * (bxz * cyz - cxz * byz))%Z Browc)) as [HrowcR Frowc].
  pose proof (arc_outer_diff_bound_2p51
                (axz * (byz * ncz - cyz * nbz)) (ayz * (bxz * ncz - cxz * nbz))
                Browa Browb) as Bsubd.
  destruct (b64_minus_int_exact _ _
              (axz * (byz * ncz - cyz * nbz)) (ayz * (bxz * ncz - cxz * nbz))
              Frowa Frowb HrowaR HrowbR
              (le_2p51_le_2pprec
                 (axz * (byz * ncz - cyz * nbz) - ayz * (bxz * ncz - cxz * nbz))%Z
                 Bsubd)) as [HsubR Fsub].
  pose proof (arc_final_sum_bound_2p52
                (axz * (byz * ncz - cyz * nbz) - ayz * (bxz * ncz - cxz * nbz))
                (naz * (bxz * cyz - cxz * byz)) Bsubd Browc) as Bfind.
  destruct (b64_plus_int_exact _ _
              (axz * (byz * ncz - cyz * nbz) - ayz * (bxz * ncz - cxz * nbz))
              (naz * (bxz * cyz - cxz * byz))
              Fsub Frowc HsubR HrowcR
              (le_2p52_le_2pprec
                 (axz * (byz * ncz - cyz * nbz) - ayz * (bxz * ncz - cxz * nbz)
                  + naz * (bxz * cyz - cxz * byz))%Z
                 Bfind)) as [HoutR _].
  unfold b64_inCircle.
  cbn iota.
  rewrite HoutR.
  unfold inCircle_R_BP.
  rewrite HAxR, HAyR, HBxR, HByR, HCxR, HCyR, HPxR, HPyR.
  pose proof (minus_IZR nAx nPx) as Haxz.
  pose proof (minus_IZR nAy nPy) as Hayz.
  pose proof (minus_IZR nBx nPx) as Hbxz.
  pose proof (minus_IZR nBy nPy) as Hbyz.
  pose proof (minus_IZR nCx nPx) as Hcxz.
  pose proof (minus_IZR nCy nPy) as Hcyz.
  rewrite <- Haxz, <- Hayz, <- Hbxz, <- Hbyz, <- Hcxz, <- Hcyz.
  fold axz; fold ayz; fold bxz; fold byz; fold cxz; fold cyz.
  repeat rewrite (IZR_sq_sum cxz cyz) at 1.
  repeat rewrite (IZR_sq_sum bxz byz) at 1.
  rewrite (IZR_sq_sum axz ayz) at 1.
  fold naz; fold nbz; fold ncz.
  rewrite (IZR_na_cross_pack naz bxz byz cxz cyz) at 1.
  rewrite (inCircle_det_IZR_pack axz ayz bxz byz cxz cyz naz nbz ncz) at 1.
  reflexivity.
Qed.

Theorem b64_inCircle_B2R_sign_sound_small_int :
  forall A B C P,
    inCircle_inputs_int_safe A B C P ->
    (0 < inCircle_R_BP A B C P <->
     0 < Binary.B2R prec emax (b64_inCircle A B C P)) /\
    (inCircle_R_BP A B C P < 0 <->
     Binary.B2R prec emax (b64_inCircle A B C P) < 0) /\
    (inCircle_R_BP A B C P = 0 <->
     Binary.B2R prec emax (b64_inCircle A B C P) = 0).
Proof.
  intros A B C P Hsafe.
  pose proof (b64_inCircle_exact_for_small_int A B C P Hsafe) as Hexact.
  repeat split; rewrite Hexact; tauto.
Qed.

(* -------------------------------------------------------------------------- *)
(* Perron worst-case witness (KakeyaOrient2d_b64 pattern).                    *)
(*                                                                            *)
(* Perron stage n=10 subdivides the unit base into 2^10 pieces.  Scaled by     *)
(* 2^11 the vertices are integers at the |coord| <= 2^11 boundary:              *)
(*   apex = (2^10, 2^11),  base_k = (2k, 0).                                  *)
(*                                                                            *)
(* The thinnest sub-triangle (k = 0) is the hardest inCircle stress geometry: *)
(* a near-flat sliver whose circumcircle test forces the degree-4 chain.      *)
(* Chord endpoints P = (1, 0) and Q = (2^11, 0) carry opposite signs -- the   *)
(* arc-line intersection regime exercised by `ArcLineIntersect_b64_exact`.  *)
(* -------------------------------------------------------------------------- *)

Definition b64Z (m : Z) : binary64 :=
  Binary.binary_normalize prec emax prec_gt_0_b64 prec_lt_emax_b64
    mode_NE m 0 false.

Lemma b64Z_R :
  forall m : Z, (Z.abs m <= 2 ^ 53)%Z ->
    Binary.B2R prec emax (b64Z m) = IZR m
    /\ Binary.is_finite prec emax (b64Z m) = true.
Proof.
  intros m Hm. unfold b64Z.
  pose proof (Binary.binary_normalize_correct prec emax
                prec_gt_0_b64 prec_lt_emax_b64 mode_NE m 0 false) as H.
  assert (HF2R : F2R (Float radix2 m 0) = IZR m).
  { unfold F2R; simpl. lra. }
  rewrite HF2R in H.
  assert (Hround : Generic_fmt.round radix2 (SpecFloat.fexp prec emax)
                     (round_mode mode_NE) (IZR m) = IZR m).
  { apply Generic_fmt.round_generic; [apply valid_rnd_round_mode |].
    apply generic_format_IZR_le_bpow_prec. unfold prec; lia. }
  rewrite Hround in H.
  assert (Hbnd : Rabs (IZR m) < bpow radix2 emax).
  { rewrite <- abs_IZR.
    apply (Rle_lt_trans _ (bpow radix2 53)).
    - rewrite bpow_radix2_eq_IZR_pow by lia. apply IZR_le. exact Hm.
    - apply bpow_lt; unfold emax; lia. }
  apply Rlt_bool_true in Hbnd. rewrite Hbnd in H.
  destruct H as [HB2R [Hfin _]]. split; assumption.
Qed.

Lemma b64Z_arc_coord_int_safe :
  forall m : Z, (Z.abs m <= 2 ^ 11)%Z -> arc_coord_int_safe (b64Z m).
Proof.
  intros m Hm.
  destruct (b64Z_R m ltac:(lia)) as [HR Hf].
  split; [ exact Hf | exists m; split; [ exact HR | exact Hm ] ].
Qed.

(* Stage-10 Perron thin sliver: apex over the midpoint, k = 0 base edge. *)
Definition perron_sliver_S : BPoint := mkBP (b64Z (2 ^ 10)) (b64Z (2 ^ 11)).
Definition perron_sliver_M : BPoint := mkBP (b64Z 0) (b64Z 0).
Definition perron_sliver_E : BPoint := mkBP (b64Z 2) (b64Z 0).

(* Chord endpoints along the scaled unit base: opposite inCircle signs. *)
Definition perron_chord_P : BPoint := mkBP (b64Z 1) (b64Z 0).
Definition perron_chord_Q : BPoint := mkBP (b64Z (2 ^ 11)) (b64Z 0).

Lemma perron_sliver_inputs_int_safe :
  inCircle_inputs_int_safe perron_sliver_S perron_sliver_M perron_sliver_E perron_chord_P.
Proof.
  unfold inCircle_inputs_int_safe, perron_sliver_S, perron_sliver_M,
         perron_sliver_E, perron_chord_P; cbn [bx by_].
  repeat split; apply b64Z_arc_coord_int_safe; lia.
Qed.

Lemma perron_chord_Q_inputs_int_safe :
  inCircle_inputs_int_safe perron_sliver_S perron_sliver_M perron_sliver_E perron_chord_Q.
Proof.
  unfold inCircle_inputs_int_safe, perron_sliver_S, perron_sliver_M,
         perron_sliver_E, perron_chord_Q; cbn [bx by_].
  repeat split; apply b64Z_arc_coord_int_safe; lia.
Qed.

Lemma b64Z_R_small (m : Z) :
  (Z.abs m <= 2 ^ 11)%Z ->
  Binary.B2R prec emax (b64Z m) = IZR m.
Proof.
  intros Hm. apply (proj1 (b64Z_R m ltac:(lia))).
Qed.

Lemma perron_b64Z_witnesses :
  Binary.B2R prec emax (bx perron_sliver_S) = IZR (2 ^ 10) /\
  Binary.B2R prec emax (by_ perron_sliver_S) = IZR (2 ^ 11) /\
  Binary.B2R prec emax (bx perron_sliver_M) = IZR 0 /\
  Binary.B2R prec emax (by_ perron_sliver_M) = IZR 0 /\
  Binary.B2R prec emax (bx perron_sliver_E) = IZR 2 /\
  Binary.B2R prec emax (by_ perron_sliver_E) = IZR 0 /\
  Binary.B2R prec emax (bx perron_chord_P) = IZR 1 /\
  Binary.B2R prec emax (by_ perron_chord_P) = IZR 0.
Proof.
  unfold perron_sliver_S, perron_sliver_M, perron_sliver_E, perron_chord_P.
  cbn [bx by_].
  repeat split.
  all: rewrite b64Z_R_small; [reflexivity |].
  all: unfold Z.abs; simpl; lia.
Qed.

Lemma perron_b64Z_witnesses_Q :
  Binary.B2R prec emax (bx perron_chord_Q) = IZR (2 ^ 11) /\
  Binary.B2R prec emax (by_ perron_chord_Q) = IZR 0.
Proof.
  unfold perron_chord_Q.
  cbn [bx by_].
  repeat split.
  all: rewrite b64Z_R_small; [reflexivity |].
  all: unfold Z.abs; simpl; lia.
Qed.

Lemma inCircle_R_BP_Z_pack :
  forall (ax ay bx' by' cx cy na nb nc : Z),
    (na = (ax * ax + ay * ay)%Z) ->
    (nb = (bx' * bx' + by' * by')%Z) ->
    (nc = (cx * cx + cy * cy)%Z) ->
    IZR ax * (IZR by' * IZR nc - IZR cy * IZR nb)
    - IZR ay * (IZR bx' * IZR nc - IZR cx * IZR nb)
    + (IZR ax * IZR ax + IZR ay * IZR ay)
        * (IZR bx' * IZR cy - IZR cx * IZR by')
    = IZR (ax * (by' * nc - cy * nb)
           - ay * (bx' * nc - cx * nb)
           + na * (bx' * cy - cx * by'))%Z.
Proof.
  intros ax ay bx' by' cx cy na nb nc Hna Hnb Hnc.
  assert (Hsum : IZR ax * IZR ax + IZR ay * IZR ay = IZR na).
  { transitivity (IZR (ax * ax + ay * ay)%Z); [apply IZR_sq_sum | rewrite Hna; reflexivity]. }
  rewrite Hsum.
  rewrite (IZR_na_cross_pack na bx' by' cx cy).
  apply inCircle_det_IZR_pack.
Qed.

Lemma perron_inCircle_Zdet_P :
  (-2048 * ((-1) * 1 - 1 * 1))%Z = 4096%Z.
Proof. lia. Qed.

Lemma perron_inCircle_Zdet_Q :
  (-2048 * ((-2048) * (2046 * 2046) - (-2046) * (2048 * 2048)))%Z
    = (-17163091968)%Z.
Proof. lia. Qed.

Lemma perron_inCircle_det_pos :
  inCircle_R_BP perron_sliver_S perron_sliver_M perron_sliver_E perron_chord_P
    = IZR 4096.
Proof.
  set (z := (1023 * (0 * 1 - 0 * 1)
               - 2048 * ((-1) * 1 - 1 * 1)
               + (1023 * 1023 + 2048 * 2048) * ((-1) * 0 - 1 * 0))%Z).
  assert (Hz : z = 4096%Z) by lia.
  destruct perron_b64Z_witnesses as [HSx [HSy [HMx [HMy [HEx [HEy [HPx HPy]]]]]]].
  unfold inCircle_R_BP.
  rewrite HSx, HSy, HMx, HMy, HEx, HEy, HPx, HPy.
  replace (IZR 0 - IZR 0) with (0 : R) by lra.
  replace (IZR 0 - IZR 0) with (0 : R) by lra.
  repeat rewrite <- minus_IZR.
  simpl.
  repeat rewrite (IZR_sq_sum 1 0) at 1.
  repeat rewrite (IZR_sq_sum (-1) 0) at 1.
  rewrite (IZR_sq_sum 1023 2048) at 1.
  rewrite (IZR_na_cross_pack (1023 * 1023 + 2048 * 2048) (-1) 0 1 0) at 1.
  rewrite (inCircle_det_IZR_pack 1023 2048 (-1) 0 1 0
             (1023 * 1023 + 2048 * 2048) 1 1) at 1.
  replace (IZR z) with (IZR 4096) by (f_equal; exact Hz).
  reflexivity.
Qed.

Lemma perron_inCircle_det_neg :
  inCircle_R_BP perron_sliver_S perron_sliver_M perron_sliver_E perron_chord_Q
    = IZR (-17163091968).
Proof.
  set (z := ((-1024) * (0 * (2046 * 2046) - 0 * (2048 * 2048))
               - 2048 * ((-2048) * (2046 * 2046) - (-2046) * (2048 * 2048))
               + ((-1024) * (-1024) + 2048 * 2048) * ((-2048) * 0 - (-2046) * 0))%Z).
  assert (Hz : z = (-17163091968)%Z) by lia.
  destruct perron_b64Z_witnesses as [HSx [HSy [HMx [HMy [HEx [HEy _]]]]]].
  destruct perron_b64Z_witnesses_Q as [HQx HQy].
  unfold inCircle_R_BP.
  rewrite HSx, HSy, HMx, HMy, HEx, HEy, HQx, HQy.
  replace (IZR 0 - IZR 0) with (0 : R) by lra.
  replace (IZR 0 - IZR 0) with (0 : R) by lra.
  repeat rewrite <- minus_IZR.
  simpl.
  repeat rewrite (IZR_sq_sum (-2046) 0) at 1.
  repeat rewrite (IZR_sq_sum (-2048) 0) at 1.
  rewrite (IZR_sq_sum (-1024) 2048) at 1.
  rewrite (IZR_na_cross_pack ((-1024) * (-1024) + 2048 * 2048) (-2048) 0 (-2046) 0) at 1.
  rewrite (inCircle_det_IZR_pack (-1024) 2048 (-2048) 0 (-2046) 0
             ((-1024) * (-1024) + 2048 * 2048) (2048 * 2048) (2046 * 2046)) at 1.
  replace (IZR z) with (IZR (-17163091968)) by (f_equal; exact Hz).
  reflexivity.
Qed.

Lemma perron_chord_opposite_signs :
  inCircle_R_BP perron_sliver_S perron_sliver_M perron_sliver_E perron_chord_P > 0 /\
  inCircle_R_BP perron_sliver_S perron_sliver_M perron_sliver_E perron_chord_Q < 0.
Proof.
  rewrite perron_inCircle_det_pos, perron_inCircle_det_neg.
  repeat split; apply IZR_lt; lia.
Qed.

Theorem perron_inCircle_bit_exact_P :
  Binary.B2R prec emax
    (b64_inCircle perron_sliver_S perron_sliver_M perron_sliver_E perron_chord_P)
  = inCircle_R_BP perron_sliver_S perron_sliver_M perron_sliver_E perron_chord_P.
Proof.
  apply b64_inCircle_exact_for_small_int.
  exact perron_sliver_inputs_int_safe.
Qed.

Theorem perron_inCircle_bit_exact_Q :
  Binary.B2R prec emax
    (b64_inCircle perron_sliver_S perron_sliver_M perron_sliver_E perron_chord_Q)
  = inCircle_R_BP perron_sliver_S perron_sliver_M perron_sliver_E perron_chord_Q.
Proof.
  apply b64_inCircle_exact_for_small_int.
  exact perron_chord_Q_inputs_int_safe.
Qed.

Theorem perron_inCircle_sign_sound :
  (0 < Binary.B2R prec emax
        (b64_inCircle perron_sliver_S perron_sliver_M perron_sliver_E perron_chord_P)) /\
  (Binary.B2R prec emax
     (b64_inCircle perron_sliver_S perron_sliver_M perron_sliver_E perron_chord_Q) < 0).
Proof.
  rewrite perron_inCircle_bit_exact_P, perron_inCircle_bit_exact_Q.
  exact perron_chord_opposite_signs.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions inCircle_R_BP_factor.
Print Assumptions b64_inCircle_exact_sound.
Print Assumptions b64_inCircle_exact_for_small_int.
Print Assumptions b64_inCircle_B2R_sign_sound_small_int.
Print Assumptions perron_sliver_inputs_int_safe.
Print Assumptions perron_inCircle_det_pos.
Print Assumptions perron_inCircle_bit_exact_P.
Print Assumptions perron_inCircle_sign_sound.