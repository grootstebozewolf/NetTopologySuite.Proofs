(* ============================================================================
   nts-eval micro unit — claimId 64-i-circular
   ----------------------------------------------------------------------------
   Twin of CircularCookZ.I_circles_z on the locked (0,0)/(7,0) r=5 fixture.
   ========================================================================== *)

(* WITNESS {"claimId":"64-i-circular","topic":"core","lemma":"locked_I_circles_z_hit","title":"Integer circle-circle discriminant: locked (0,0)/(7,0) r=5 is Hit hens 0 and 1"} *)

From Stdlib Require Import ZArith Bool.
Open Scope Z_scope.

Definition HenZ : Type := nat.
Definition hen_plus : HenZ := 0%nat.
Definition hen_minus : HenZ := 1%nat.

Inductive IZResult : Type :=
| IZHit (h_plus h_minus : HenZ)
| IZEmpty
| IZTouch (h : HenZ)
| IZDecline.

Definition circ_d2 (o1x o1y o2x o2y : Z) : Z :=
  (o2x - o1x) * (o2x - o1x) + (o2y - o1y) * (o2y - o1y).

Definition mint_pair : IZResult := IZHit hen_plus hen_minus.
Definition mint_touch : IZResult := IZTouch hen_plus.

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

Lemma locked_I_circles_z_hit :
  I_circles_z 0 0 5 7 0 5 = IZHit hen_plus hen_minus.
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

Print Assumptions locked_I_circles_z_hit.
Print Assumptions locked_external_kiss_is_touch.
