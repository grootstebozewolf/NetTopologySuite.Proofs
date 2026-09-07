(* ============================================================================
   NetTopologySuite.Proofs.CircularCookZ
   ----------------------------------------------------------------------------
   Integer circle–circle discriminant classifier + named-root hen mint.

   I_circles_z is an extractable seam, not glossary 𝓘 (that is Hit (p*, tᵢ, tⱼ);
   there is no γ / [0,1] here). Hens 0/1 are birth certificates of the named
   radical roots, not a proved identity.

       I_circles_z : Hit | Empty | Touch | Decline

   Touch is tangent contact (one hen). Decline is degenerate input
   (r ≤ 0 or coincident centres), not the egg/arc case.

   WITNESS topic: core · claimId: 64-i-circular · witness: 64-i-circular-locked
   0-axiom (Z only). No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   ========================================================================== *)

From Stdlib Require Import ZArith Bool.
Open Scope Z_scope.

Definition HenZ : Type := nat.

(* Birth certificates: plus/minus radical roots. *)
Definition hen_plus : HenZ := 0%nat.
Definition hen_minus : HenZ := 1%nat.

Inductive RadicalRoot : Type :=
| RootPlus
| RootMinus.

Definition hen_of_root (r : RadicalRoot) : HenZ :=
  match r with
  | RootPlus => hen_plus
  | RootMinus => hen_minus
  end.

Inductive IZResult : Type :=
| IZHit (h_plus h_minus : HenZ)
| IZEmpty
| IZTouch (h : HenZ)
| IZDecline.

Definition circ_d2 (o1x o1y o2x o2y : Z) : Z :=
  (o2x - o1x) * (o2x - o1x) + (o2y - o1y) * (o2y - o1y).

Definition mint_pair : IZResult := IZHit hen_plus hen_minus.

Definition mint_touch : IZResult := IZTouch hen_plus.

(* Squared tests, no sqrt.
   Decline: r ≤ 0 or coincident centres.
   Touch:   kiss (d = r1±r2).
   Empty:   disjoint circumcircles.
   Hit:     proper intersection; mint plus/minus hens. *)
Definition I_circles_z (o1x o1y r1 o2x o2y r2 : Z) : IZResult :=
  if (r1 <=? 0) || (r2 <=? 0) then IZDecline
  else if circ_d2 o1x o1y o2x o2y =? 0 then IZDecline
  else if (circ_d2 o1x o1y o2x o2y =? (r1 + r2) * (r1 + r2))
          || (circ_d2 o1x o1y o2x o2y =? (r1 - r2) * (r1 - r2))
       then mint_touch
  else if ((r1 + r2) * (r1 + r2) <? circ_d2 o1x o1y o2x o2y)
          || (circ_d2 o1x o1y o2x o2y <? (r1 - r2) * (r1 - r2))
       then IZEmpty
  else mint_pair.

(* WITNESS {"claimId":"64-i-circular","topic":"core","lemma":"locked_I_circles_z_hit","title":"Integer circle-circle discriminant: locked (0,0)/(7,0) r=5 is Hit hens 0 and 1","file":"theories/CircularCookZ.v","witness":"64-i-circular-locked","board":"ADR-0007"} *)

Lemma locked_I_circles_z_hit :
  I_circles_z 0 0 5 7 0 5 = IZHit hen_plus hen_minus.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma locked_disjoint_is_empty :
  I_circles_z 0 0 5 20 0 5 = IZEmpty.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma locked_coincident_is_decline :
  I_circles_z 0 0 5 0 0 5 = IZDecline.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma locked_zero_radius_is_decline :
  I_circles_z 0 0 0 7 0 5 = IZDecline.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma locked_external_kiss_is_touch :
  I_circles_z 0 0 5 10 0 5 = IZTouch hen_plus.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma IZEmpty_neq_IZDecline : IZEmpty <> IZDecline.
Proof.
  discriminate.
Qed.

Lemma IZTouch_neq_IZDecline : forall h, IZTouch h <> IZDecline.
Proof.
  intros. discriminate.
Qed.

Print Assumptions locked_I_circles_z_hit.
Print Assumptions locked_external_kiss_is_touch.
Print Assumptions IZEmpty_neq_IZDecline.
Print Assumptions IZTouch_neq_IZDecline.
