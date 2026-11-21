(* QedRootsExamples.v -- worked instances and negative controls for qedroots.

   Graduated from the hunt probe docs/h1-vacuity/JensenSignCertificate.v
   (docs/attacks/2026-11-20-jensen-hyperbolicity-certificate.md).

     P5 = (X+1)(2X+1)(X+2)(3X+1)(X+3) = 6 + 41X + 97X^2 + 97X^3 + 41X^4 + 6X^5
   positive coefficients and negative roots, like a xi Jensen polynomial
   (it is also self-reciprocal; Jensen polynomials are not in general).
   Proofs use only the six signs at rational points,
   never the factored form.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import Reals QArith Qreals Lra Psatz List.
From NTS.Proofs Require Import QedPoly QedInterval QedRoots QedRootsRefute.
Import ListNotations.

Local Open Scope Q_scope.

Definition P5 : list Q := [6; 41; 97; 97; 41; 6].
Definition xs5 : list Q := [-4; -5#2; -3#2; -3#4; -2#5; -1#4].

Lemma P5_cert : box_cert (point_box P5) xs5 = true.
Proof. vm_compute. reflexivity. Qed.

(* The exact sign list: the orientation-predicate analogue. *)
Lemma P5_signs :
  map (fun x => isign (ieval (point_box P5) x)) xs5 = [-1; 1; -1; 1; -1; 1]%Z.
Proof. vm_compute. reflexivity. Qed.

(* Absolute width 1/20 on every coefficient keeps the certificate: the
   minimal normalised margin |P(x)| / sum |x|^j at these points is
   8/133 ~ 0.060 (x = -5/2 and x = -2/5). *)
Lemma P5_cert_width : box_cert (width_box (1#20) P5) xs5 = true.
Proof. vm_compute. reflexivity. Qed.

(* Width 1/10 is rejected AT THESE POINTS -- a fact about the checker, not
   a non-hyperbolic witness in the widened family. *)
Lemma P5_reject_width : box_cert (width_box (1#10) P5) xs5 = false.
Proof. vm_compute. reflexivity. Qed.

Local Open Scope R_scope.

Theorem P5_simple_real_rooted : simple_real_rooted (pQ2R P5).
Proof. exact (point_cert_sound P5 xs5 P5_cert). Qed.

Theorem P5_neighbourhood_simple_real_rooted (p : list R) :
  in_box p (width_box (1#20) P5) -> simple_real_rooted p.
Proof. intros H. exact (cert_sound _ _ _ H P5_cert_width). Qed.

(* ------------------------------------------------------------------ *)
(* Multiplicities.                                                      *)
(* ------------------------------------------------------------------ *)
Local Open Scope Q_scope.

(* (X+1)^2 (X+2) = 2 + 5X + 4X^2 + X^3 *)
Definition D3 : list Q := [2; 5; 4; 1].

(* Certified hyperbolic through the factor certificate, with the double
   root written as a repeated factor. *)
Lemma D3_factor_cert :
  factor_cert 1 [([1; 1], [-2; 0]); ([1; 1], [-2; 0]); ([2; 1], [-3; 0])] D3
  = true.
Proof. vm_compute. reflexivity. Qed.

Theorem D3_hyperbolic : hyperbolic (pQ2R D3).
Proof. exact (factor_cert_sound _ _ _ D3_factor_cert). Qed.

(* Q5 = (2X^2+5X+2)^2 (X+3): degree 5, two double roots and a simple one.
   = 12 + 64X + 119X^2 + 93X^3 + 32X^4 + 4X^5 *)
Definition Q5 : list Q := [12; 64; 119; 93; 32; 4].

Lemma Q5_factor_cert :
  factor_cert 1 [([2; 5; 2], [-3; -1; 0]); ([2; 5; 2], [-3; -1; 0]);
                 ([3; 1], [-4; 0])] Q5 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem Q5_hyperbolic : hyperbolic (pQ2R Q5).
Proof. exact (factor_cert_sound _ _ _ Q5_factor_cert). Qed.

Local Open Scope R_scope.

(* ... but the robust box certificate can never accept D3, for any points
   and any box containing it: soundness would give 3 distinct real roots,
   and the only real roots are -1 and -2.  Sound, not complete. *)
Theorem double_root_box_uncertifiable (b : box) (xs : list Q) :
  in_box (pQ2R D3) b -> box_cert b xs = false.
Proof.
  intros Hb. destruct (box_cert b xs) eqn:E; [|reflexivity]. exfalso.
  destruct (cert_sound _ _ _ Hb E) as (rs & _ & Hl & Hnd & Hiff & _).
  simpl in Hl. injection Hl as Hl.
  assert (Hr : forall y, In y rs -> y = -1 \/ y = -2).
  { intros y Hy. apply Hiff in Hy. unfold Q2R in Hy; simpl in Hy.
    assert (Hf : (y + 1) * (y + 1) * (y + 2) = 0) by lra.
    apply Rmult_integral in Hf as [Hf|Hf];
      [apply Rmult_integral in Hf as [Hf|Hf]|]; lra. }
  destruct rs as [|a [|b' [|c [|? ?]]]]; simpl in Hl; try discriminate.
  inversion Hnd as [|? ? Ha Hnd1]; subst.
  assert (Ha' := Hr a (or_introl eq_refl)).
  assert (Hb2 := Hr b' (or_intror (or_introl eq_refl))).
  assert (Hc' := Hr c (or_intror (or_intror (or_introl eq_refl)))).
  inversion Hnd1 as [|? ? Hb3 Hnd2]; subst.
  simpl in Ha, Hb3.
  destruct Ha' as [-> | ->]; destruct Hb2 as [-> | ->];
    destruct Hc' as [-> | ->]; tauto.
Qed.

(* X^2 + 1: no real roots, so no box certificate ever passes. *)
Theorem no_real_roots_box_uncertifiable (b : box) (xs : list Q) :
  in_box (pQ2R [1; 0; 1]%Q) b -> box_cert b xs = false.
Proof.
  intros Hb. destruct (box_cert b xs) eqn:E; [|reflexivity]. exfalso.
  destruct (cert_sound _ _ _ Hb E) as (rs & _ & Hl & _ & Hiff & _).
  destruct rs as [|y l]; simpl in Hl; try discriminate.
  assert (Hy : In y (y :: l)) by (left; reflexivity).
  apply Hiff in Hy. unfold Q2R in Hy; simpl in Hy.
  pose proof (Rle_0_sqr y). unfold Rsqr in *. lra.
Qed.

(* ------------------------------------------------------------------ *)
(* Refutation side (QedRootsRefute): exact "not hyperbolic" witnesses.  *)
(* ------------------------------------------------------------------ *)
Local Open Scope Q_scope.

(* X^2 + 1 at x = 0:  L = 0^2 - 1 * 2 = -2. *)
Lemma x2_plus_one_lag_cert : lag_box_cert (point_box [1; 0; 1]) 0 = true.
Proof. vm_compute. reflexivity. Qed.

(* (X+1)(X^2+1) = 1 + X + X^2 + X^3 at x = 1/2:  L = -29/16. *)
Lemma cubic_lag : lag_box_cert (point_box [1; 1; 1; 1]) (1#2) = true.
Proof. vm_compute. reflexivity. Qed.

(* P5 lifted by 3 in the constant term: the local minimum near -3/2
   (P5(-3/2) = -21/8) is pushed above zero, two real roots leave the axis.
   Refuted robustly: every real quintic within +-1/2 of it, coefficientwise,
   is non-hyperbolic (Laguerre at x = -1/4). *)
Definition P5up : list Q := [9; 41; 97; 97; 41; 6].

Lemma P5up_lag_width : lag_box_cert (width_box (1#2) P5up) (-1#4) = true.
Proof. vm_compute. reflexivity. Qed.

Local Open Scope R_scope.

Theorem x2_plus_one_not_hyperbolic : ~ hyperbolic (pQ2R [1; 0; 1]%Q).
Proof. exact (lag_point_cert_sound _ _ x2_plus_one_lag_cert). Qed.

Theorem cubic_not_hyperbolic : ~ hyperbolic (pQ2R [1; 1; 1; 1]%Q).
Proof. exact (lag_point_cert_sound _ _ cubic_lag). Qed.

Theorem P5up_neighbourhood_not_hyperbolic (p : list R) :
  in_box p (width_box (1#2) P5up) -> ~ hyperbolic p.
Proof. intros H. exact (lag_box_cert_sound _ _ _ H P5up_lag_width). Qed.

(* ------------------------------------------------------------------ *)
(* Non-vacuity of the neighbourhood theorems: each box contains its     *)
(* centre polynomial.                                                   *)
(* ------------------------------------------------------------------ *)

Lemma P5_width_box_inhabited : in_box (pQ2R P5) (width_box (1#20) P5).
Proof. apply in_box_width. vm_compute. discriminate. Qed.

Lemma P5up_width_box_inhabited : in_box (pQ2R P5up) (width_box (1#2) P5up).
Proof. apply in_box_width. vm_compute. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(* Negative control: lag_box_cert is NOT complete on proper boxes, even *)
(* in degree 2.   beta_box = 1 + [-3/2, 3/2] X + X^2.                   *)
(* Every member has discriminant <= 9/4 - 4 < 0, so none is hyperbolic  *)
(* (beta_box_not_hyperbolic); the box is inhabited (beta_box_inhabited);*)
(* yet the checker fails at EVERY rational x (beta_box_lag_never):      *)
(* P, D, E are enclosed independently, and                              *)
(*   lag_upper >= 2x^2 + 6B|x| + B^2 - 2 >= 1/4   (B = 3/2).            *)
(* ------------------------------------------------------------------ *)
Local Open Scope Q_scope.

Definition beta_box : box := [(1, 1); (-3#2, 3#2); (1, 1)].

Local Open Scope R_scope.

Lemma beta_box_inhabited : in_box (pQ2R [1; 0; 1]%Q) beta_box.
Proof. repeat constructor; unfold Q2R; simpl; lra. Qed.

Theorem beta_box_not_hyperbolic (p : list R) :
  in_box p beta_box -> ~ hyperbolic p.
Proof.
  intros H.
  inversion H as [|a lh0 p1 b1 Ha H1]; subst.
  inversion H1 as [|b lh1 p2 b2 Hb H2]; subst.
  inversion H2 as [|c lh2 p3 b3 Hc H3]; subst.
  inversion H3; subst.
  unfold Q2R in Ha, Hb, Hc; simpl in Ha, Hb, Hc.
  apply quadratic_negative_discriminant_not_hyperbolic; nra.
Qed.

Lemma beta_lag_upper_ge x : Q2R (lag_upper beta_box x) >= 1/4.
Proof.
  unfold lag_upper, beta_box. cbn [ieval pderivB pderivB_aux tl].
  assert (Hx : (0 <= Q2R x) \/ Q2R x < 0) by lra.
  destruct (Qle_bool 0 x); cbv beta iota; rewrite Q2R_minus;
  match goal with |- Q2R (qmax ?a ?b) - Q2R (qmin (qmin ?c ?d) (qmin ?e ?f)) >= _ =>
    pose proof (qmax_ge a b) as [Ma Mb];
    pose proof (qmin_le (qmin c d) (qmin e f)) as [M1 M2];
    pose proof (qmin_le c d) as [Mc _];
    pose proof (qmin_le e f) as [Me _] end;
  repeat (rewrite Q2R_plus in Ma || rewrite Q2R_mult in Ma || rewrite Q2R_inject_nat in Ma);
  repeat (rewrite Q2R_plus in Mb || rewrite Q2R_mult in Mb || rewrite Q2R_inject_nat in Mb);
  repeat (rewrite Q2R_plus in Mc || rewrite Q2R_mult in Mc || rewrite Q2R_inject_nat in Mc);
  repeat (rewrite Q2R_plus in Me || rewrite Q2R_mult in Me || rewrite Q2R_inject_nat in Me);
  remember (Q2R x) as X eqn:HX in *;
  replace (Q2R (-3 # 2)) with (-3/2) in * by (unfold Q2R; simpl; field);
  replace (Q2R (3 # 2)) with (3/2) in * by (unfold Q2R; simpl; field);
  replace (Q2R 1) with 1 in * by (unfold Q2R; simpl; field);
  replace (Q2R 0) with 0 in * by (unfold Q2R; simpl; field);
  replace (INR 1) with 1 in * by (simpl; ring);
  replace (INR 2) with 2 in * by (simpl; ring);
  destruct Hx; nra.
Qed.


Theorem beta_box_lag_never (x : Q) : lag_box_cert beta_box x = false.
Proof.
  unfold lag_box_cert.
  destruct (Qltb (lag_upper beta_box x) 0) eqn:E; [|apply andb_false_r].
  exfalso. apply Qltb_spec in E. rewrite Q2R_0 in E.
  pose proof (beta_lag_upper_ge x). lra.
Qed.

Print Assumptions P5_cert.
Print Assumptions P5_cert_width.
Print Assumptions P5_reject_width.
Print Assumptions P5_simple_real_rooted.
Print Assumptions P5_neighbourhood_simple_real_rooted.
Print Assumptions D3_hyperbolic.
Print Assumptions Q5_hyperbolic.
Print Assumptions double_root_box_uncertifiable.
Print Assumptions no_real_roots_box_uncertifiable.
Print Assumptions x2_plus_one_lag_cert.
Print Assumptions x2_plus_one_not_hyperbolic.
Print Assumptions cubic_not_hyperbolic.
Print Assumptions P5up_neighbourhood_not_hyperbolic.
Print Assumptions P5_width_box_inhabited.
Print Assumptions P5up_width_box_inhabited.
Print Assumptions beta_box_not_hyperbolic.
Print Assumptions beta_box_lag_never.
