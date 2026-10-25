(* ============================================================================
   NetTopologySuite.Proofs.ClothoidAffine
   ----------------------------------------------------------------------------
   Proof half of claimId `cloth-affine-closure` (statements pinned in
   ClothoidAffineStmt.v).  Placed clothoids o + M c are closed under any
   affine map f(p) = b + L p: the image is the placed clothoid
   (f(o), L M) over the same host egg (act_eval).  The action is a left
   action of the affine group (act_id, act_comp; inverses for det L <> 0,
   aff_inv_l / aff_inv_r), multiplies det M by det L (act_det), and
   commutes with split, reverse and the chord demote by construction
   (act_split, act_rev, act_chord).  Tangents map by L (act_tangent) and
   are the derivatives of the image (pc_tangent_deriv); tangent cross
   products scale by det L (act_tangent_cross), so touching is kept.

   This is statement A of the shear plan: the representation is closed.
   It is not a statement about curvature or arc length (see
   ClothoidShearLaw.v) nor about noding (ADR-0007 transport, not here).

   claimId: cloth-affine-closure.
   3-axiom host. No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
   ========================================================================== *)

From Stdlib Require Import Reals Lra Ranalysis1.
From NTS.Proofs Require Import Distance SignedCurvature SheetHenClothoidCore
  ClothoidLinearize ClothoidTraversal ClothoidPlacement ClothoidAffineStmt.
Local Open Scope R_scope.

Lemma aff_point_eta : forall p, mkPoint (px p) (py p) = p.
Proof. intros [x y]. reflexivity. Qed.

Lemma lin_eta : forall M, mkLin2 (l11 M) (l12 M) (l21 M) (l22 M) = M.
Proof. intros [a b c d]. reflexivity. Qed.

Lemma lin_ap_mul : forall L M p,
  lin_ap (lin_mul L M) p = lin_ap L (lin_ap M p).
Proof. intros. unfold lin_ap, lin_mul. cbn. f_equal; ring. Qed.

Lemma lin_mul_id_l : forall M, lin_mul lin_id M = M.
Proof.
  intro M. rewrite <- (lin_eta M) at 2. unfold lin_mul, lin_id. cbn. f_equal; ring.
Qed.

Lemma lin_mul_assoc : forall K L M,
  lin_mul K (lin_mul L M) = lin_mul (lin_mul K L) M.
Proof. intros. unfold lin_mul. cbn. f_equal; ring. Qed.

Lemma lin_det_mul : forall L M,
  lin_det (lin_mul L M) = lin_det L * lin_det M.
Proof. intros. unfold lin_det, lin_mul. cbn. ring. Qed.

Lemma placed_comp : forall b L o M p,
  placed b L (placed o M p) = placed (placed b L o) (lin_mul L M) p.
Proof. intros. unfold placed, lin_ap, lin_mul. cbn. f_equal; ring. Qed.

Theorem act_eval : act_eval_stmt.
Proof.
  intros f pc t. unfold pc_eval, pc_act, aff_ap. cbn.
  symmetry. apply placed_comp.
Qed.

Theorem act_id : act_id_stmt.
Proof.
  intros [o M c]. unfold pc_act, aff_id, aff_ap. cbn.
  rewrite lin_mul_id_l. f_equal.
  rewrite <- (aff_point_eta o) at 2. unfold placed, lin_ap, lin_id. cbn. f_equal; ring.
Qed.

Theorem act_comp : act_comp_stmt.
Proof.
  intros g f [o M c]. unfold pc_act, aff_comp, aff_ap. cbn.
  rewrite lin_mul_assoc, placed_comp. reflexivity.
Qed.

Theorem act_det : act_det_stmt.
Proof. intros f pc. unfold pc_act. cbn. apply lin_det_mul. Qed.

Theorem act_split : act_split_stmt.
Proof. intros f pc t. reflexivity. Qed.

Theorem act_rev : act_rev_stmt.
Proof. intros f pc. reflexivity. Qed.

Theorem act_chord : act_chord_stmt.
Proof.
  intros f pc. unfold pc_chord. cbn [fst snd]. rewrite !act_eval. reflexivity.
Qed.

Theorem cloth_affine_claim : ClothoidAffineStmt.claim.
Proof.
  exact (conj act_eval (conj act_id (conj act_comp (conj act_det
           (conj act_split (conj act_rev act_chord)))))).
Qed.

(* -------------------------------------------------------------------------- *)
(* Supporting: inverses, tangents, cross products.                            *)
(* -------------------------------------------------------------------------- *)

Lemma lin_inv_l : forall L, lin_det L <> 0 -> lin_mul (lin_inv L) L = lin_id.
Proof.
  intros L H. unfold lin_mul, lin_inv, lin_id, lin_det in *. cbn.
  f_equal; field; exact H.
Qed.

Lemma lin_inv_r : forall L, lin_det L <> 0 -> lin_mul L (lin_inv L) = lin_id.
Proof.
  intros L H. unfold lin_mul, lin_inv, lin_id, lin_det in *. cbn.
  f_equal; field; exact H.
Qed.

Theorem aff_inv_l : forall f, lin_det (af_L f) <> 0 ->
  aff_comp (aff_inv f) f = aff_id.
Proof.
  intros [b L] H. cbn in H. unfold aff_comp, aff_inv, aff_id, aff_ap. cbn.
  rewrite lin_inv_l by exact H. f_equal.
  unfold placed, lin_ap, lin_inv, lin_det in *. cbn. f_equal; field; exact H.
Qed.

Theorem aff_inv_r : forall f, lin_det (af_L f) <> 0 ->
  aff_comp f (aff_inv f) = aff_id.
Proof.
  intros [b L] H. cbn in H. unfold aff_comp, aff_inv, aff_id, aff_ap. cbn.
  rewrite lin_inv_r by exact H. f_equal.
  unfold placed, lin_ap, lin_inv, lin_det in *. cbn. f_equal; field; exact H.
Qed.

Theorem act_arc : forall f pc s,
  pc_arc (pc_act f pc) s = aff_ap f (pc_arc pc s).
Proof.
  intros f pc s. unfold pc_arc, pc_act, aff_ap. cbn. symmetry. apply placed_comp.
Qed.

Theorem act_tangent : forall f pc s,
  pc_tangent (pc_act f pc) s = lin_ap (af_L f) (pc_tangent pc s).
Proof. intros f pc s. unfold pc_tangent, pc_act. cbn. apply lin_ap_mul. Qed.

Theorem pc_tangent_deriv : forall pc s,
  derivable_pt_lim (fun u => px (pc_arc pc u)) s (px (pc_tangent pc s)) /\
  derivable_pt_lim (fun u => py (pc_arc pc u)) s (py (pc_tangent pc s)).
Proof.
  intros pc s. unfold pc_arc, pc_tangent.
  apply placed_deriv.
  - apply cloth_arc_px_deriv.
  - apply cloth_arc_py_deriv.
Qed.

Theorem act_tangent_cross : forall f pc s pc' s',
  curv_cross (pc_tangent (pc_act f pc) s) (pc_tangent (pc_act f pc') s')
    = lin_det (af_L f) * curv_cross (pc_tangent pc s) (pc_tangent pc' s').
Proof. intros. rewrite !act_tangent. apply curv_cross_lin. Qed.

Theorem cloth_affine_supporting : ClothoidAffineStmt.supporting.
Proof.
  split; [intros f H; split; [apply aff_inv_l | apply aff_inv_r]; exact H|].
  split; [intros f pc s; split; [apply act_arc | apply act_tangent]|].
  split; [exact pc_tangent_deriv | exact act_tangent_cross].
Qed.

(* -------------------------------------------------------------------------- *)
(* Witness: the GEOS #1566 shear is one affine map away from identity.        *)
(* -------------------------------------------------------------------------- *)

Theorem cloth_affine_witness : ClothoidAffineStmt.witness.
Proof.
  exists (mkAff2 (mkPoint 0 0) geos_shear).
  cbn. unfold geos_shear. cbn.
  split; [unfold lin_det; cbn; lra|].
  split; [lra|].
  unfold pc_act, aff_ap, placed, lin_ap, lin_mul, lin_id. cbn.
  f_equal; f_equal; ring.
Qed.

Print Assumptions aff_point_eta.
Print Assumptions lin_ap_mul.
Print Assumptions lin_mul_assoc.
Print Assumptions lin_det_mul.
Print Assumptions placed_comp.
Print Assumptions act_eval.
Print Assumptions act_id.
Print Assumptions act_comp.
Print Assumptions act_det.
Print Assumptions act_split.
Print Assumptions act_rev.
Print Assumptions act_chord.
Print Assumptions cloth_affine_claim.
Print Assumptions aff_inv_l.
Print Assumptions aff_inv_r.
Print Assumptions act_arc.
Print Assumptions act_tangent.
Print Assumptions pc_tangent_deriv.
Print Assumptions act_tangent_cross.
Print Assumptions cloth_affine_supporting.
Print Assumptions cloth_affine_witness.
