(* ============================================================================
   nts-eval micro unit — claimId 64-i-circular
   ----------------------------------------------------------------------------
   Year-1 extractable circular 𝓘 on the locked DISC_OVERLAY fixture.
   Self-contained: no NTS.Proofs Requires. Mirrors CircularCookZ.v.

   WITNESS claimId: 64-i-circular
   Lemma: locked_I_circles_z_hit
   ========================================================================== *)

(* WITNESS {"claimId":"64-i-circular","topic":"core","lemma":"locked_I_circles_z_hit","title":"Year-1 circular I on locked (0,0)/(7,0) r=5 is Hit minting hens 0 and 1"} *)

From Stdlib Require Import ZArith Bool.
Open Scope Z_scope.

Definition HenZ : Type := nat.
Definition hen_plus : HenZ := 0%nat.
Definition hen_minus : HenZ := 1%nat.

Inductive IZResult : Type :=
| IZHit (h_plus h_minus : HenZ)
| IZEmpty
| IZDecline.

Definition I_circles_z (o1x o1y r1 o2x o2y r2 : Z) : IZResult :=
  if (r1 <=? 0) || (r2 <=? 0) then IZDecline
  else
    let dx := o2x - o1x in
    let dy := o2y - o1y in
    let d2 := dx * dx + dy * dy in
    if d2 =? 0 then IZDecline
    else
      let sum := r1 + r2 in
      let dif := r1 - r2 in
      let sum2 := sum * sum in
      let dif2 := dif * dif in
      if (d2 =? sum2) || (d2 =? dif2) then IZDecline
      else if (sum2 <? d2) || (d2 <? dif2) then IZEmpty
      else IZHit hen_plus hen_minus.

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

Lemma IZEmpty_neq_IZDecline : IZEmpty <> IZDecline.
Proof.
  discriminate.
Qed.

Print Assumptions locked_I_circles_z_hit.
Print Assumptions IZEmpty_neq_IZDecline.
