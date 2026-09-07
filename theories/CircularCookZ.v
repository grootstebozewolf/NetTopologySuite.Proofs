(* ============================================================================
   NetTopologySuite.Proofs.CircularCookZ
   ----------------------------------------------------------------------------
   Year-1 extractable 𝓘 for two circular eggs on one integer sheet.

   Revolutionary cut item 1 (ADR-0007 executed for circular–circular):
   𝓘 is a function, not a comment.

       I_circles_z : Hit (h_plus, h_minus) | Empty | Decline

   Hit mints the two named radical roots. Same named root ⇒ same hen by
   construction (the cook's allocator), not dart_eq_dec / coord-pair
   equality. A kiss / coincident centres / zero radius / degenerate
   pencil is the Decline constructor, not a README paragraph.

   This is the integer-sheet classifier a C# noder can call. Attaching
   p* lives in CircularCook.v (radical_point_plus / _minus). Sweep
   parameters (tᵢ, tⱼ) wait on a γ : [0,1] → S constructor for
   CircularArc — QEX, recorded there. SheetHenCook first_cook_scope
   stays chord–chord (also recorded there).

   Not OverlayNGCurve wiring. Not fully_intersected retirement. Not
   the #671 resultant certificate.

   WITNESS topic: core · claimId: 64-i-circular · witness: 64-i-circular-locked
   lane: proofs
   board: ADR-0007

   No `Admitted`, no `Axiom`, no `Parameter`. 0-axiom (Z only).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import ZArith Bool.
Open Scope Z_scope.

(* -------------------------------------------------------------------------- *)
(* Cook-local hens. Identity is the named radical root, not a coordinate.    *)
(* -------------------------------------------------------------------------- *)

Definition HenZ : Type := nat.

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

(* Pairwise 𝓘 on an integer sheet. Empty ≠ Decline. *)
Inductive IZResult : Type :=
| IZHit (h_plus h_minus : HenZ)
| IZEmpty
| IZDecline.

(* -------------------------------------------------------------------------- *)
(* 𝓘. Four-factor / squared tests, no sqrt.                                  *)
(*   Decline: r ≤ 0, coincident centres (d² = 0), or kiss (d = r1±r2).       *)
(*   Empty:   disjoint circumcircles (no real radical root).                 *)
(*   Hit:     proper intersection; mint plus/minus hens.                     *)
(* -------------------------------------------------------------------------- *)

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

(* -------------------------------------------------------------------------- *)
(* Locked fixture (0,0) r=5 vs (7,0) r=5 — DISC_OVERLAY / ARC_ARC_XY pin.    *)
(* Eval / vm_compute fails before Qed if the function is not Hit 0 1.        *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"64-i-circular","topic":"core","lemma":"locked_I_circles_z_hit","title":"Year-1 circular I on locked (0,0)/(7,0) r=5 is Hit minting hens 0 and 1","file":"theories/CircularCookZ.v","witness":"64-i-circular-locked","board":"ADR-0007"} *)

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

Lemma locked_external_kiss_is_decline :
  I_circles_z 0 0 5 10 0 5 = IZDecline.
Proof.
  vm_compute. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Constructors are real and distinct. Hens are named roots.                 *)
(* -------------------------------------------------------------------------- *)

Lemma IZEmpty_neq_IZDecline : IZEmpty <> IZDecline.
Proof.
  discriminate.
Qed.

Lemma IZHit_neq_IZEmpty :
  forall hp hm, IZHit hp hm <> IZEmpty.
Proof.
  intros. discriminate.
Qed.

Lemma IZHit_neq_IZDecline :
  forall hp hm, IZHit hp hm <> IZDecline.
Proof.
  intros. discriminate.
Qed.

Lemma hen_plus_of_root : hen_of_root RootPlus = hen_plus.
Proof.
  reflexivity.
Qed.

Lemma hen_minus_of_root : hen_of_root RootMinus = hen_minus.
Proof.
  reflexivity.
Qed.

(* Any Hit mints the named-root hens. Two Hits — even on different
   integer pairs — share plus/minus by the cook's policy, not because
   anyone compared coordinates. *)
Lemma hit_mints_named_roots :
  forall o1x o1y r1 o2x o2y r2 hp hm,
    I_circles_z o1x o1y r1 o2x o2y r2 = IZHit hp hm ->
    hp = hen_plus /\ hm = hen_minus.
Proof.
  intros o1x o1y r1 o2x o2y r2 hp hm H.
  destruct (I_circles_z o1x o1y r1 o2x o2y r2); try discriminate.
  inversion H. split; reflexivity.
Qed.

Lemma same_named_root_same_hen :
  forall o1x o1y r1 o2x o2y r2
         o1x' o1y' r1' o2x' o2y' r2' hp hm hp' hm',
    I_circles_z o1x o1y r1 o2x o2y r2 = IZHit hp hm ->
    I_circles_z o1x' o1y' r1' o2x' o2y' r2' = IZHit hp' hm' ->
    hp = hp' /\ hm = hm'.
Proof.
  intros.
  destruct (hit_mints_named_roots _ _ _ _ _ _ _ _ H) as [Ha Hb].
  destruct (hit_mints_named_roots _ _ _ _ _ _ _ _ H0) as [Hc Hd].
  subst. split; reflexivity.
Qed.

Lemma I_circles_z_replay :
  forall o1x o1y r1 o2x o2y r2,
    I_circles_z o1x o1y r1 o2x o2y r2 =
    I_circles_z o1x o1y r1 o2x o2y r2.
Proof.
  reflexivity.
Qed.

Print Assumptions locked_I_circles_z_hit.
Print Assumptions locked_disjoint_is_empty.
Print Assumptions locked_coincident_is_decline.
Print Assumptions hit_mints_named_roots.
Print Assumptions same_named_root_same_hen.
Print Assumptions IZEmpty_neq_IZDecline.
