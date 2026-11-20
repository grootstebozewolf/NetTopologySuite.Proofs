(* QedRootsExamples.v -- worked instances and negative controls for qedroots.

   Graduated from the hunt probe docs/h1-vacuity/JensenSignCertificate.v
   (docs/attacks/2026-11-20-jensen-hyperbolicity-certificate.md).

     P5 = (X+1)(2X+1)(X+2)(3X+1)(X+3) = 6 + 41X + 97X^2 + 97X^3 + 41X^4 + 6X^5
   self-reciprocal, positive coefficients, negative roots: the shape of a
   xi Jensen polynomial.  Proofs use only the six signs at rational points,
   never the factored form.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import Reals QArith Qreals Lra List.
From NTS.Proofs Require Import QedPoly QedInterval QedRoots.
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
