(* ============================================================================
   NetTopologySuite.Proofs.Flocq.ArcLineIntersect_b64_exact
   ----------------------------------------------------------------------------
   Phase 4 first slice (Scope A): first-stage bit-exactness for the binary64
   arc-line (circle-chord) intersection-point computation -- the prefix of
   the Cramer-rule chain that lands BEFORE the dividing step.

   Honest scoping note: the headline
       B2R (b64_arc_line_intersect_point_x ...) = arc_line_intersect_x_R ...
   does NOT hold on the nose in the integer regime, because the intersection
   parameter along the chord is generally a non-dyadic rational.  Round-chain
   identity (Scope B) and forward-error bound (Scope C) are queued as
   follow-up slices.

   What this file ships:

     - Total binary64 projections `b64_arc_line_intersect_point_x` /
       `b64_arc_line_intersect_point_y` (return `binary64`, not `option`).
     - Safety predicate `arc_line_intersect_inputs_int_safe` extending the
       ten-coordinate `inCircle_inputs_int_safe` regime with the R-side
       denominator-non-zero condition.
     - R-side reference expressions: `arc_line_intersect_param_s`,
       `arc_line_intersect_x_R`, `arc_line_intersect_y_R`.
     - First-stage exactness: the two outer inCircle evaluations (`sP`, `sQ`)
       and the two chord coordinate differences (`dx`, `dy`) are bit-exact
       integer-valued binary64.

   Mirrors `Intersect_b64_exact.v` Scope A; parallels the arc-chord existence
   predicate in `theories/ArcIntersect.v` with coordinate machinery.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra.

From Flocq Require Import IEEE754.Binary Core.

From NTS.Proofs.Flocq Require Import Validate_binary64 InCircle_b64_compute
                                      InCircle_b64_exact Orient_b64_exact
                                      Intersect_b64 B64_bridge B64_lib.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* R-side Cramer's-rule reference expressions.                                *)
(*                                                                            *)
(* Arc S,M,E defines the circumcircle; chord P->Q is parameterised by         *)
(*   t := inCircle_R(S,M,E,P) / (inCircle_R(S,M,E,P) - inCircle_R(S,M,E,Q)). *)
(* This is the direct analogue of `intersect_param_s` with cross products      *)
(* replaced by inCircle determinants.                                         *)
(* -------------------------------------------------------------------------- *)

Definition arc_line_intersect_param_s (S M E P Q : BPoint) : R :=
  inCircle_R_BP S M E P
    / (inCircle_R_BP S M E P - inCircle_R_BP S M E Q).

Definition arc_line_intersect_x_R (S M E P Q : BPoint) : R :=
  Binary.B2R prec emax (bx P)
  + arc_line_intersect_param_s S M E P Q
    * (Binary.B2R prec emax (bx Q) - Binary.B2R prec emax (bx P)).

Definition arc_line_intersect_y_R (S M E P Q : BPoint) : R :=
  Binary.B2R prec emax (by_ P)
  + arc_line_intersect_param_s S M E P Q
    * (Binary.B2R prec emax (by_ Q) - Binary.B2R prec emax (by_ P)).

(* -------------------------------------------------------------------------- *)
(* Total binary64 projections.                                                *)
(* -------------------------------------------------------------------------- *)

Definition b64_arc_line_intersect_point_x (S M E P Q : BPoint) : binary64 :=
  let sP := b64_inCircle S M E P in
  let sQ := b64_inCircle S M E Q in
  let den := b64_minus sP sQ in
  let t   := b64_div sP den in
  let dx  := b64_minus (bx Q) (bx P) in
  b64_plus (bx P) (b64_mult t dx).

Definition b64_arc_line_intersect_point_y (S M E P Q : BPoint) : binary64 :=
  let sP := b64_inCircle S M E P in
  let sQ := b64_inCircle S M E Q in
  let den := b64_minus sP sQ in
  let t   := b64_div sP den in
  let dy  := b64_minus (by_ Q) (by_ P) in
  b64_plus (by_ P) (b64_mult t dy).

(* -------------------------------------------------------------------------- *)
(* Safety predicate.                                                          *)
(*                                                                            *)
(* Ten arc_coord_int_safe premises (|coord| <= 2^11) for the degree-4 inCircle *)
(* chain, plus the R-side denominator-non-zero condition.                     *)
(* -------------------------------------------------------------------------- *)

Definition arc_line_intersect_inputs_int_safe (S M E P Q : BPoint) : Prop :=
  inCircle_inputs_int_safe S M E P /\
  inCircle_inputs_int_safe S M E Q /\
  inCircle_R_BP S M E P <> inCircle_R_BP S M E Q.

Lemma arc_line_intersect_inputs_int_safe_SMP :
  forall S M E P Q : BPoint,
    arc_line_intersect_inputs_int_safe S M E P Q ->
    inCircle_inputs_int_safe S M E P.
Proof.
  intros S M E P Q [Hint [_ _]]. exact Hint.
Qed.

Lemma arc_line_intersect_inputs_int_safe_SMQ :
  forall S M E P Q : BPoint,
    arc_line_intersect_inputs_int_safe S M E P Q ->
    inCircle_inputs_int_safe S M E Q.
Proof.
  intros S M E P Q [_ [Hint _]]. exact Hint.
Qed.

(* -------------------------------------------------------------------------- *)
(* First-stage exactness lemmas: the prefix before division is bit-exact.      *)
(* -------------------------------------------------------------------------- *)

Lemma b64_arc_line_sP_R :
  forall S M E P Q : BPoint,
    arc_line_intersect_inputs_int_safe S M E P Q ->
    Binary.B2R prec emax (b64_inCircle S M E P)
    = inCircle_R_BP S M E P.
Proof.
  intros S M E P Q Hsafe.
  apply b64_inCircle_exact_for_small_int.
  apply (arc_line_intersect_inputs_int_safe_SMP _ _ _ _ _ Hsafe).
Qed.

Lemma b64_arc_line_sQ_R :
  forall S M E P Q : BPoint,
    arc_line_intersect_inputs_int_safe S M E P Q ->
    Binary.B2R prec emax (b64_inCircle S M E Q)
    = inCircle_R_BP S M E Q.
Proof.
  intros S M E P Q Hsafe.
  apply b64_inCircle_exact_for_small_int.
  apply (arc_line_intersect_inputs_int_safe_SMQ _ _ _ _ _ Hsafe).
Qed.

Lemma b64_arc_line_dx_R :
  forall S M E P Q : BPoint,
    arc_line_intersect_inputs_int_safe S M E P Q ->
    Binary.B2R prec emax (b64_minus (bx Q) (bx P))
    = Binary.B2R prec emax (bx Q) - Binary.B2R prec emax (bx P)
    /\ Binary.is_finite prec emax (b64_minus (bx Q) (bx P)) = true.
Proof.
  intros S M E P Q Hsafe.
  destruct (arc_line_intersect_inputs_int_safe_SMP _ _ _ _ _ Hsafe) as
    (_ & _ & _ & _ & _ & _ & HxP & _).
  destruct (arc_line_intersect_inputs_int_safe_SMQ _ _ _ _ _ Hsafe) as
    (_ & _ & _ & _ & _ & _ & HxQ & _).
  destruct HxP as (FxP & nxP & HxPR & HxPb).
  destruct HxQ as (FxQ & nxQ & HxQR & HxQb).
  set (dx := (nxQ - nxP)%Z).
  pose proof (arc_diff_bound_2p12 nxQ nxP HxQb HxPb) as Bdx.
  destruct (b64_minus_int_exact (bx Q) (bx P) nxQ nxP FxQ FxP HxQR HxPR
                (le_2p12_le_2pprec dx Bdx)) as [Hdx Fdx].
  rewrite HxQR, HxPR, <- minus_IZR. split; [exact Hdx | exact Fdx].
Qed.

Lemma b64_arc_line_dy_R :
  forall S M E P Q : BPoint,
    arc_line_intersect_inputs_int_safe S M E P Q ->
    Binary.B2R prec emax (b64_minus (by_ Q) (by_ P))
    = Binary.B2R prec emax (by_ Q) - Binary.B2R prec emax (by_ P)
    /\ Binary.is_finite prec emax (b64_minus (by_ Q) (by_ P)) = true.
Proof.
  intros S M E P Q Hsafe.
  destruct (arc_line_intersect_inputs_int_safe_SMP _ _ _ _ _ Hsafe) as
    (_ & _ & _ & _ & _ & _ & _ & HyP).
  destruct (arc_line_intersect_inputs_int_safe_SMQ _ _ _ _ _ Hsafe) as
    (_ & _ & _ & _ & _ & _ & _ & HyQ).
  destruct HyP as (FyP & nyP & HyPR & HyPb).
  destruct HyQ as (FyQ & nyQ & HyQR & HyQb).
  set (dy := (nyQ - nyP)%Z).
  pose proof (arc_diff_bound_2p12 nyQ nyP HyQb HyPb) as Bdy.
  destruct (b64_minus_int_exact (by_ Q) (by_ P) nyQ nyP FyQ FyP HyQR HyPR
                (le_2p12_le_2pprec dy Bdy)) as [Hdy Fdy].
  rewrite HyQR, HyPR, <- minus_IZR. split; [exact Hdy | exact Fdy].
Qed.

(* -------------------------------------------------------------------------- *)
(* Scope B.1: the denominator round-chain piece.                              *)
(*                                                                            *)
(* den = b64_minus sP sQ, where sP = b64_inCircle S M E P, sQ = ... Q.  Both  *)
(* are exact integers (Scope A) of magnitude <= 2^52 (inCircle_int_witness),  *)
(* so their difference (magnitude <= 2^53 = 2^prec) is computed bit-exactly   *)
(* by b64_minus, and is nonzero exactly when the two inCircle values differ   *)
(* (the safety predicate's third clause).  Uses b64_inCircle_finite_for_small *)
(* _int -- the finiteness prerequisite the whole Scope B/C chain rests on.     *)
(* -------------------------------------------------------------------------- *)

Lemma b64_arc_line_den_exact :
  forall S M E P Q : BPoint,
    arc_line_intersect_inputs_int_safe S M E P Q ->
    Binary.B2R prec emax
      (b64_minus (b64_inCircle S M E P) (b64_inCircle S M E Q))
      = inCircle_R_BP S M E P - inCircle_R_BP S M E Q
    /\ Binary.is_finite prec emax
         (b64_minus (b64_inCircle S M E P) (b64_inCircle S M E Q)) = true.
Proof.
  intros S M E P Q Hsafe.
  pose proof (arc_line_intersect_inputs_int_safe_SMP _ _ _ _ _ Hsafe) as HsafeP.
  pose proof (arc_line_intersect_inputs_int_safe_SMQ _ _ _ _ _ Hsafe) as HsafeQ.
  destruct (inCircle_int_witness _ _ _ _ HsafeP) as (nP & HnPR & HnPb).
  destruct (inCircle_int_witness _ _ _ _ HsafeQ) as (nQ & HnQR & HnQb).
  pose proof (b64_inCircle_finite_for_small_int _ _ _ _ HsafeP) as FP.
  pose proof (b64_inCircle_finite_for_small_int _ _ _ _ HsafeQ) as FQ.
  pose proof (b64_inCircle_exact_for_small_int _ _ _ _ HsafeP) as HsP.
  pose proof (b64_inCircle_exact_for_small_int _ _ _ _ HsafeQ) as HsQ.
  assert (HsPZ : Binary.B2R prec emax (b64_inCircle S M E P) = IZR nP)
    by (rewrite HsP; exact HnPR).
  assert (HsQZ : Binary.B2R prec emax (b64_inCircle S M E Q) = IZR nQ)
    by (rewrite HsQ; exact HnQR).
  assert (Hbnd : (Z.abs (nP - nQ) <= 2 ^ prec)%Z) by (unfold prec; lia).
  destruct (b64_minus_int_exact (b64_inCircle S M E P) (b64_inCircle S M E Q)
              nP nQ FP FQ HsPZ HsQZ Hbnd) as [Hd Fd].
  split; [ | exact Fd ].
  rewrite Hd, minus_IZR, <- HnPR, <- HnQR. reflexivity.
Qed.

Lemma b64_arc_line_den_nonzero :
  forall S M E P Q : BPoint,
    arc_line_intersect_inputs_int_safe S M E P Q ->
    Binary.B2R prec emax
      (b64_minus (b64_inCircle S M E P) (b64_inCircle S M E Q)) <> 0.
Proof.
  intros S M E P Q Hsafe.
  destruct (b64_arc_line_den_exact S M E P Q Hsafe) as [Hd _].
  destruct Hsafe as (_ & _ & Hne).
  rewrite Hd. intro Hz. apply Hne. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Scope B.2: the round-chain identity for the intersection coordinate.       *)
(*                                                                            *)
(* On the integer grid every prefix is exact (Scope A/B.1); the only roundings *)
(* are the division t = sP/den and the two arithmetic ops t*dx, P + (t*dx).   *)
(* So B2R of the coordinate is the explicit nested-round expression below --   *)
(* the exact rounding-error contract callers compose against.  Mirrors          *)
(* `Intersect_b64_exact.v`'s `b64_intersect_point_x_round_chain`.  Magnitudes   *)
(* are tiny here (|coord|<=2^11 => inCircle <= 2^52, t <= 2^52, t*dx <= 2^64),  *)
(* so every no-overflow side condition is discharged by `bpow _ < bpow emax`.  *)
(* -------------------------------------------------------------------------- *)

Lemma bpow_double : forall e : Z, (bpow radix2 (e + 1) = bpow radix2 e + bpow radix2 e)%R.
Proof.
  intro e. rewrite bpow_plus.
  replace (bpow radix2 1) with 2%R by reflexivity. lra.
Qed.

Lemma inCircle_R_BP_abs_le_52 :
  forall A B C P : BPoint,
    inCircle_inputs_int_safe A B C P ->
    (Rabs (inCircle_R_BP A B C P) <= bpow radix2 52)%R.
Proof.
  intros A B C P H. destruct (inCircle_int_witness _ _ _ _ H) as (n & Hn & Hb).
  rewrite Hn, <- abs_IZR, <- (IZR_Zpower radix2 52) by lia. apply IZR_le. exact Hb.
Qed.

Theorem b64_arc_line_intersect_point_x_round_chain :
  forall S M E P Q : BPoint,
    arc_line_intersect_inputs_int_safe S M E P Q ->
    Binary.B2R prec emax (b64_arc_line_intersect_point_x S M E P Q)
    = b64_round
        (Binary.B2R prec emax (bx P)
         + b64_round
             (b64_round (inCircle_R_BP S M E P
                        / (inCircle_R_BP S M E P - inCircle_R_BP S M E Q))
              * (Binary.B2R prec emax (bx Q) - Binary.B2R prec emax (bx P)))).
Proof.
  intros S M E P Q Hsafe.
  pose proof (arc_line_intersect_inputs_int_safe_SMP _ _ _ _ _ Hsafe) as HP.
  pose proof (arc_line_intersect_inputs_int_safe_SMQ _ _ _ _ _ Hsafe) as HQ.
  pose proof (b64_arc_line_sP_R _ _ _ _ _ Hsafe) as HsPR.
  destruct (b64_arc_line_dx_R _ _ _ _ _ Hsafe) as [HdxR Fdx].
  destruct (b64_arc_line_den_exact _ _ _ _ _ Hsafe) as [HdenR Fden].
  pose proof (b64_arc_line_den_nonzero _ _ _ _ _ Hsafe) as Hden0.
  pose proof (b64_inCircle_finite_for_small_int _ _ _ _ HP) as FsP.
  (* coordinate finiteness/bounds for bx P, bx Q *)
  destruct HP as (_ & _ & _ & _ & _ & _ & HxP & _).
  destruct HQ as (_ & _ & _ & _ & _ & _ & HxQ & _).
  destruct HxP as (FxP & nxP & HxPR & HxPb).
  destruct HxQ as (FxQ & nxQ & HxQR & HxQb).
  (* magnitude facts *)
  assert (HsP52 : (Rabs (Binary.B2R prec emax (b64_inCircle S M E P)) <= bpow radix2 52)%R).
  { rewrite HsPR. apply inCircle_R_BP_abs_le_52.
    exact (arc_line_intersect_inputs_int_safe_SMP _ _ _ _ _ Hsafe). }
  assert (Hden1 : (1 <= Rabs (Binary.B2R prec emax (b64_minus (b64_inCircle S M E P)
                                                              (b64_inCircle S M E Q))))%R).
  { rewrite HdenR.
    destruct (inCircle_int_witness _ _ _ _
                (arc_line_intersect_inputs_int_safe_SMP _ _ _ _ _ Hsafe)) as (nP & HnP & _).
    destruct (inCircle_int_witness _ _ _ _
                (arc_line_intersect_inputs_int_safe_SMQ _ _ _ _ _ Hsafe)) as (nQ & HnQ & _).
    rewrite HnP, HnQ, <- minus_IZR, <- abs_IZR.
    replace 1%R with (IZR 1) by reflexivity. apply IZR_le.
    assert (Hne : (nP <> nQ)%Z).
    { intro Hz. apply Hden0. rewrite HdenR, HnP, HnQ, Hz. lra. }
    lia. }
  assert (Hdx12 : (Rabs (Binary.B2R prec emax (b64_minus (bx Q) (bx P))) <= bpow radix2 12)%R).
  { rewrite HdxR, HxPR, HxQR, <- minus_IZR, <- abs_IZR, <- (IZR_Zpower radix2 12) by lia.
    apply IZR_le. change (Zpower radix2 12) with (2 ^ 12)%Z. lia. }
  (* t = b64_div sP den : B2R t = round(sP_R / den_R) *)
  assert (Htdiv_bnd : (Rabs (b64_round (Binary.B2R prec emax (b64_inCircle S M E P)
                              / Binary.B2R prec emax (b64_minus (b64_inCircle S M E P)
                                                                (b64_inCircle S M E Q))))
                       < bpow radix2 emax)%R).
  { apply (Rle_lt_trans _ (bpow radix2 52)); [ | apply bpow_lt; unfold emax; lia ].
    apply b64_round_abs_le_bpow; [ unfold emax; lia | ].
    unfold Rdiv. rewrite Rabs_mult, Rabs_inv.
    apply (Rle_trans _ (Rabs (Binary.B2R prec emax (b64_inCircle S M E P)) * 1)).
    - apply Rmult_le_compat_l; [ apply Rabs_pos | ].
      rewrite <- Rinv_1. apply Rinv_le_contravar; [ lra | exact Hden1 ].
    - rewrite Rmult_1_r. exact HsP52. }
  destruct (b64_div_correct (b64_inCircle S M E P)
              (b64_minus (b64_inCircle S M E P) (b64_inCircle S M E Q))
              FsP Fden Hden0 Htdiv_bnd) as [HtR Ft].
  (* t magnitude <= bpow 52 *)
  assert (Ht52 : (Rabs (Binary.B2R prec emax
                     (b64_div (b64_inCircle S M E P)
                       (b64_minus (b64_inCircle S M E P) (b64_inCircle S M E Q))))
                  <= bpow radix2 52)%R).
  { rewrite HtR. apply b64_round_abs_le_bpow; [ unfold emax; lia | ].
    unfold Rdiv. rewrite Rabs_mult, Rabs_inv.
    apply (Rle_trans _ (Rabs (Binary.B2R prec emax (b64_inCircle S M E P)) * 1)).
    - apply Rmult_le_compat_l; [ apply Rabs_pos | ].
      rewrite <- Rinv_1. apply Rinv_le_contravar; [ lra | exact Hden1 ].
    - rewrite Rmult_1_r. exact HsP52. }
  (* mult t dx safe *)
  set (t := b64_div (b64_inCircle S M E P)
              (b64_minus (b64_inCircle S M E P) (b64_inCircle S M E Q))) in *.
  set (dx := b64_minus (bx Q) (bx P)) in *.
  assert (Hmult_safe : b64_safe Rmult t dx).
  { split; [ exact Ft | split; [ exact Fdx | ] ].
    apply (Rle_lt_trans _ (bpow radix2 64)); [ | apply bpow_lt; unfold emax; lia ].
    apply b64_round_abs_le_bpow; [ unfold emax; lia | ].
    rewrite Rabs_mult.
    replace (bpow radix2 64) with (bpow radix2 52 * bpow radix2 12)%R
      by (rewrite <- bpow_plus; reflexivity).
    apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  destruct (b64_mult_correct t dx Hmult_safe) as [HmR Fm].
  (* mult magnitude <= bpow 64 *)
  assert (Hm64 : (Rabs (Binary.B2R prec emax (b64_mult t dx)) <= bpow radix2 64)%R).
  { rewrite HmR. apply b64_round_abs_le_bpow; [ unfold emax; lia | ].
    rewrite Rabs_mult.
    replace (bpow radix2 64) with (bpow radix2 52 * bpow radix2 12)%R
      by (rewrite <- bpow_plus; reflexivity).
    apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  (* plus (bx P) (mult) safe *)
  assert (Hplus_safe : b64_safe Rplus (bx P) (b64_mult t dx)).
  { split; [ exact FxP | split; [ exact Fm | ] ].
    apply (Rle_lt_trans _ (bpow radix2 65)); [ | apply bpow_lt; unfold emax; lia ].
    apply b64_round_abs_le_bpow; [ unfold emax; lia | ].
    apply (Rle_trans _ (Rabs (Binary.B2R prec emax (bx P)) + Rabs (Binary.B2R prec emax (b64_mult t dx)))).
    - apply Rabs_triang.
    - apply (Rle_trans _ (bpow radix2 11 + bpow radix2 64)).
      + apply Rplus_le_compat; [ | exact Hm64 ].
        rewrite HxPR, <- abs_IZR, <- (IZR_Zpower radix2 11) by lia. apply IZR_le.
        change (Zpower radix2 11) with (2 ^ 11)%Z. lia.
      + replace (bpow radix2 65) with (bpow radix2 64 + bpow radix2 64)%R
          by (rewrite <- bpow_double; reflexivity).
        apply Rplus_le_compat; apply bpow_le; lia. }
  destruct (b64_plus_correct (bx P) (b64_mult t dx) Hplus_safe) as [HpR _].
  (* assemble *)
  unfold b64_arc_line_intersect_point_x. fold t dx.
  rewrite HpR, HmR, HtR, HsPR, HdenR, HdxR.
  reflexivity.
Qed.

Theorem b64_arc_line_intersect_point_y_round_chain :
  forall S M E P Q : BPoint,
    arc_line_intersect_inputs_int_safe S M E P Q ->
    Binary.B2R prec emax (b64_arc_line_intersect_point_y S M E P Q)
    = b64_round
        (Binary.B2R prec emax (by_ P)
         + b64_round
             (b64_round (inCircle_R_BP S M E P
                        / (inCircle_R_BP S M E P - inCircle_R_BP S M E Q))
              * (Binary.B2R prec emax (by_ Q) - Binary.B2R prec emax (by_ P)))).
Proof.
  intros S M E P Q Hsafe.
  pose proof (arc_line_intersect_inputs_int_safe_SMP _ _ _ _ _ Hsafe) as HP.
  pose proof (arc_line_intersect_inputs_int_safe_SMQ _ _ _ _ _ Hsafe) as HQ.
  pose proof (b64_arc_line_sP_R _ _ _ _ _ Hsafe) as HsPR.
  destruct (b64_arc_line_dy_R _ _ _ _ _ Hsafe) as [HdyR Fdy].
  destruct (b64_arc_line_den_exact _ _ _ _ _ Hsafe) as [HdenR Fden].
  pose proof (b64_arc_line_den_nonzero _ _ _ _ _ Hsafe) as Hden0.
  pose proof (b64_inCircle_finite_for_small_int _ _ _ _ HP) as FsP.
  (* coordinate finiteness/bounds for by_ P, by_ Q *)
  destruct HP as (_ & _ & _ & _ & _ & _ & _ & HyP).
  destruct HQ as (_ & _ & _ & _ & _ & _ & _ & HyQ).
  destruct HyP as (FyP & nyP & HyPR & HyPb).
  destruct HyQ as (FyQ & nyQ & HyQR & HyQb).
  (* magnitude facts *)
  assert (HsP52 : (Rabs (Binary.B2R prec emax (b64_inCircle S M E P)) <= bpow radix2 52)%R).
  { rewrite HsPR. apply inCircle_R_BP_abs_le_52.
    exact (arc_line_intersect_inputs_int_safe_SMP _ _ _ _ _ Hsafe). }
  assert (Hden1 : (1 <= Rabs (Binary.B2R prec emax (b64_minus (b64_inCircle S M E P)
                                                              (b64_inCircle S M E Q))))%R).
  { rewrite HdenR.
    destruct (inCircle_int_witness _ _ _ _
                (arc_line_intersect_inputs_int_safe_SMP _ _ _ _ _ Hsafe)) as (nP & HnP & _).
    destruct (inCircle_int_witness _ _ _ _
                (arc_line_intersect_inputs_int_safe_SMQ _ _ _ _ _ Hsafe)) as (nQ & HnQ & _).
    rewrite HnP, HnQ, <- minus_IZR, <- abs_IZR.
    replace 1%R with (IZR 1) by reflexivity. apply IZR_le.
    assert (Hne : (nP <> nQ)%Z).
    { intro Hz. apply Hden0. rewrite HdenR, HnP, HnQ, Hz. lra. }
    lia. }
  assert (Hdy12 : (Rabs (Binary.B2R prec emax (b64_minus (by_ Q) (by_ P))) <= bpow radix2 12)%R).
  { rewrite HdyR, HyPR, HyQR, <- minus_IZR, <- abs_IZR, <- (IZR_Zpower radix2 12) by lia.
    apply IZR_le. change (Zpower radix2 12) with (2 ^ 12)%Z. lia. }
  (* t = b64_div sP den : B2R t = round(sP_R / den_R) *)
  assert (Htdiv_bnd : (Rabs (b64_round (Binary.B2R prec emax (b64_inCircle S M E P)
                              / Binary.B2R prec emax (b64_minus (b64_inCircle S M E P)
                                                                (b64_inCircle S M E Q))))
                       < bpow radix2 emax)%R).
  { apply (Rle_lt_trans _ (bpow radix2 52)); [ | apply bpow_lt; unfold emax; lia ].
    apply b64_round_abs_le_bpow; [ unfold emax; lia | ].
    unfold Rdiv. rewrite Rabs_mult, Rabs_inv.
    apply (Rle_trans _ (Rabs (Binary.B2R prec emax (b64_inCircle S M E P)) * 1)).
    - apply Rmult_le_compat_l; [ apply Rabs_pos | ].
      rewrite <- Rinv_1. apply Rinv_le_contravar; [ lra | exact Hden1 ].
    - rewrite Rmult_1_r. exact HsP52. }
  destruct (b64_div_correct (b64_inCircle S M E P)
              (b64_minus (b64_inCircle S M E P) (b64_inCircle S M E Q))
              FsP Fden Hden0 Htdiv_bnd) as [HtR Ft].
  (* t magnitude <= bpow 52 *)
  assert (Ht52 : (Rabs (Binary.B2R prec emax
                     (b64_div (b64_inCircle S M E P)
                       (b64_minus (b64_inCircle S M E P) (b64_inCircle S M E Q))))
                  <= bpow radix2 52)%R).
  { rewrite HtR. apply b64_round_abs_le_bpow; [ unfold emax; lia | ].
    unfold Rdiv. rewrite Rabs_mult, Rabs_inv.
    apply (Rle_trans _ (Rabs (Binary.B2R prec emax (b64_inCircle S M E P)) * 1)).
    - apply Rmult_le_compat_l; [ apply Rabs_pos | ].
      rewrite <- Rinv_1. apply Rinv_le_contravar; [ lra | exact Hden1 ].
    - rewrite Rmult_1_r. exact HsP52. }
  (* mult t dy safe *)
  set (t := b64_div (b64_inCircle S M E P)
              (b64_minus (b64_inCircle S M E P) (b64_inCircle S M E Q))) in *.
  set (dy := b64_minus (by_ Q) (by_ P)) in *.
  assert (Hmult_safe : b64_safe Rmult t dy).
  { split; [ exact Ft | split; [ exact Fdy | ] ].
    apply (Rle_lt_trans _ (bpow radix2 64)); [ | apply bpow_lt; unfold emax; lia ].
    apply b64_round_abs_le_bpow; [ unfold emax; lia | ].
    rewrite Rabs_mult.
    replace (bpow radix2 64) with (bpow radix2 52 * bpow radix2 12)%R
      by (rewrite <- bpow_plus; reflexivity).
    apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  destruct (b64_mult_correct t dy Hmult_safe) as [HmR Fm].
  (* mult magnitude <= bpow 64 *)
  assert (Hm64 : (Rabs (Binary.B2R prec emax (b64_mult t dy)) <= bpow radix2 64)%R).
  { rewrite HmR. apply b64_round_abs_le_bpow; [ unfold emax; lia | ].
    rewrite Rabs_mult.
    replace (bpow radix2 64) with (bpow radix2 52 * bpow radix2 12)%R
      by (rewrite <- bpow_plus; reflexivity).
    apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  (* plus (by_ P) (mult) safe *)
  assert (Hplus_safe : b64_safe Rplus (by_ P) (b64_mult t dy)).
  { split; [ exact FyP | split; [ exact Fm | ] ].
    apply (Rle_lt_trans _ (bpow radix2 65)); [ | apply bpow_lt; unfold emax; lia ].
    apply b64_round_abs_le_bpow; [ unfold emax; lia | ].
    apply (Rle_trans _ (Rabs (Binary.B2R prec emax (by_ P)) + Rabs (Binary.B2R prec emax (b64_mult t dy)))).
    - apply Rabs_triang.
    - apply (Rle_trans _ (bpow radix2 11 + bpow radix2 64)).
      + apply Rplus_le_compat; [ | exact Hm64 ].
        rewrite HyPR, <- abs_IZR, <- (IZR_Zpower radix2 11) by lia. apply IZR_le.
        change (Zpower radix2 11) with (2 ^ 11)%Z. lia.
      + replace (bpow radix2 65) with (bpow radix2 64 + bpow radix2 64)%R
          by (rewrite <- bpow_double; reflexivity).
        apply Rplus_le_compat; apply bpow_le; lia. }
  destruct (b64_plus_correct (by_ P) (b64_mult t dy) Hplus_safe) as [HpR _].
  (* assemble *)
  unfold b64_arc_line_intersect_point_y. fold t dy.
  rewrite HpR, HmR, HtR, HsPR, HdenR, HdyR.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Perron worst-case witness (from InCircle_b64_exact).                       *)
(* -------------------------------------------------------------------------- *)

Lemma perron_arc_line_inputs_int_safe :
  arc_line_intersect_inputs_int_safe
    perron_sliver_S perron_sliver_M perron_sliver_E perron_chord_P perron_chord_Q.
Proof.
  unfold arc_line_intersect_inputs_int_safe.
  split; [| split].
  - exact perron_sliver_inputs_int_safe.
  - exact perron_chord_Q_inputs_int_safe.
  - destruct perron_chord_opposite_signs as [Hpos Hneg].
    lra.
Qed.

Theorem perron_arc_line_sP_exact :
  Binary.B2R prec emax
    (b64_inCircle perron_sliver_S perron_sliver_M perron_sliver_E perron_chord_P)
  = inCircle_R_BP perron_sliver_S perron_sliver_M perron_sliver_E perron_chord_P.
Proof.
  apply (b64_arc_line_sP_R _ _ _ _ _ perron_arc_line_inputs_int_safe).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_arc_line_sP_R.
Print Assumptions b64_arc_line_sQ_R.
Print Assumptions b64_arc_line_dx_R.
Print Assumptions b64_arc_line_dy_R.
Print Assumptions b64_arc_line_intersect_point_x_round_chain.
Print Assumptions b64_arc_line_intersect_point_y_round_chain.