(* ============================================================================
   NetTopologySuite.Proofs.ClothoidSheet
   ----------------------------------------------------------------------------
   Proof half of claimId `cloth-sheet-transport` (statements pinned in
   ClothoidSheetStmt.v), statement C of the shear plan.

   An invertible affine map f is injective (aff_inj), so it moves a correct
   clothoid x clothoid result to a correct result and back (transport):
   the Hit point on both curves at (ti, tj) becomes its image under f,
   on both images at the same (ti, tj); disjoint images stay disjoint.  On the host sheet the
   placed spec is the clothoid arm of I_ok (host_spec).  A pair placed on a
   common invertible frame (o, M) is the image of its host pair under that
   frame (act_frame_host), so pull-back / host cook / push-forward meets the
   sheet spec (sheet_cook_ok); any other pair declines.

   Supporting: the scope test, sheet composition and frame orientation,
   list noding, tangency, split vertices, on-boundary location, and the
   det L law for Orientation.cross and RingArea979.signed_area2 (the
   translation part telescopes around a closed ring, shoelace_open_map).

   claimId: cloth-sheet-transport.
   3-axiom host. No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Bool.
From NTS.Proofs Require Import Distance Orientation RingArea979 SignedCurvature
  SheetHenClothoidCore SheetHenCookCore ClothoidTraversal ClothoidPlacement
  ClothoidAffineStmt ClothoidAffine ClothoidShearLawStmt ClothoidShearLaw
  ClothoidCookMkClothoid ClothoidSheetStmt.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Affine maps: composition, identity, injectivity.                       *)
(* -------------------------------------------------------------------------- *)

Lemma aff_comp_ap : forall g f p, aff_ap (aff_comp g f) p = aff_ap g (aff_ap f p).
Proof. intros. unfold aff_comp, aff_ap. cbn. symmetry. apply placed_comp. Qed.

Lemma aff_id_ap : forall p, aff_ap aff_id p = p.
Proof.
  intros [x y]. unfold aff_ap, aff_id, placed, lin_ap, lin_id. cbn. f_equal; ring.
Qed.

Lemma aff_inj : forall f p q, lin_det (af_L f) <> 0 ->
  aff_ap f p = aff_ap f q -> p = q.
Proof.
  intros f p q HD E.
  rewrite <- (aff_id_ap p), <- (aff_id_ap q), <- (aff_inv_l f HD), !aff_comp_ap, E.
  reflexivity.
Qed.

Lemma placed_zero_id : forall p, placed (mkPoint 0 0) lin_id p = p.
Proof. exact aff_id_ap. Qed.

Lemma host_eval : forall c t, pc_eval (host_pc c) t = cloth_eval c t.
Proof. intros. unfold pc_eval, host_pc. cbn. apply placed_zero_id. Qed.

Lemma lin_mul_id_r : forall M, lin_mul M lin_id = M.
Proof.
  intro M. rewrite <- (lin_eta M) at 2. unfold lin_mul, lin_id. cbn. f_equal; ring.
Qed.

(* A placed clothoid is its host egg moved by its own frame. *)
Lemma act_frame_host : forall pc, pc_act (pc_frame pc) (host_pc (pc_c pc)) = pc.
Proof.
  intros [o M c]. unfold pc_act, pc_frame, host_pc, aff_ap. cbn.
  rewrite lin_mul_id_r. f_equal.
  rewrite <- (aff_point_eta o) at 2. unfold placed, lin_ap. cbn. f_equal; ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The claim.                                                             *)
(* -------------------------------------------------------------------------- *)

Theorem push_shape : push_shape_stmt.
Proof.
  intros f o. destruct o as [p ti tj| |]; cbn.
  - split; [split; discriminate|]. split; [split; discriminate|].
    intros p' ti' tj' E. injection E as -> -> ->. reflexivity.
  - split; [split; discriminate|]. split; [split; reflexivity|].
    intros p ti tj E. discriminate.
  - split; [split; reflexivity|]. split; [split; discriminate|].
    intros p ti tj E. discriminate.
Qed.

Lemma on_pc_host : forall c t p, on_cloth c t p <-> on_pc (host_pc c) t p.
Proof.
  intros c t p. unfold on_cloth, on_pc. rewrite host_eval. reflexivity.
Qed.

Theorem host_spec : host_spec_stmt.
Proof.
  intros c1 c2 [p ti tj| |]; unfold I_ok, I_placed_ok.
  - rewrite <- !on_pc_host. reflexivity.
  - split; intros H (X & t1 & t2 & H1 & H2); apply H; exists X, t1, t2;
      [rewrite !on_pc_host | rewrite <- !on_pc_host]; split; assumption.
  - reflexivity.
Qed.

Lemma on_pc_act : forall f pc t p, lin_det (af_L f) <> 0 ->
  (on_pc pc t p <-> on_pc (pc_act f pc) t (aff_ap f p)).
Proof.
  intros f pc t p HD. unfold on_pc. rewrite act_eval. split.
  - intros [Ht ->]. split; [exact Ht | reflexivity].
  - intros [Ht E]. split; [exact Ht | exact (aff_inj f _ _ HD E)].
Qed.

Lemma on_pc_act_inv : forall f pc t X, on_pc (pc_act f pc) t X ->
  X = aff_ap f (pc_eval pc t).
Proof. intros f pc t X [_ E]. rewrite E, act_eval. reflexivity. Qed.

Theorem transport : transport_stmt.
Proof.
  intros f pc1 pc2 [p ti tj| |] HD; cbn.
  - rewrite <- !(on_pc_act f) by exact HD. reflexivity.
  - split.
    + intros H (X & t1 & t2 & H1 & H2). apply H.
      pose proof (on_pc_act_inv f pc1 t1 X H1) as E1.
      exists (pc_eval pc1 t1), t1, t2. split.
      * apply (proj2 (on_pc_act f pc1 t1 _ HD)). rewrite <- E1. exact H1.
      * apply (proj2 (on_pc_act f pc2 t2 _ HD)). rewrite <- E1. exact H2.
    + intros H (X & t1 & t2 & H1 & H2). apply H.
      exists (aff_ap f X), t1, t2.
      split; [apply (proj1 (on_pc_act f pc1 t1 X HD)) | apply (proj1 (on_pc_act f pc2 t2 X HD))];
        assumption.
  - reflexivity.
Qed.

Lemma sheet_req_b_true : forall a b, req_b a b = true <-> a = b.
Proof.
  intros a b. unfold req_b. destruct (Req_EM_T a b) as [E|N].
  - split; [intros _; exact E | reflexivity].
  - split; [discriminate | intro E; contradiction].
Qed.

Lemma pc_scope_b_iff : forall pc1 pc2, pc_scope_b pc1 pc2 = true <-> pc_scope pc1 pc2.
Proof.
  intros [[x1 y1] [a1 b1 c1 d1] e1] [[x2 y2] [a2 b2 c2 d2] e2].
  unfold pc_scope_b, pc_scope. cbn.
  rewrite !andb_true_iff, negb_true_iff, !sheet_req_b_true.
  assert (Hf : forall z, req_b z 0 = false <-> z <> 0).
  { intro z. split.
    - intros H E. apply sheet_req_b_true in E. congruence.
    - intro H. destruct (req_b z 0) eqn:E; [|reflexivity].
      apply sheet_req_b_true in E. contradiction. }
  rewrite Hf. split.
  - intros ((((((-> & ->) & ->) & ->) & ->) & ->) & HD). repeat split; exact HD.
  - intros (Eo & EM & HD). injection Eo as -> ->. injection EM as -> -> -> ->.
    repeat split; exact HD.
Qed.

Theorem sheet_cook_ok : sheet_cook_stmt.
Proof.
  intros cook pc1 pc2 Hcook. unfold sheet_cook.
  destruct (pc_scope_b pc1 pc2) eqn:Eb.
  - pose proof (proj1 (pc_scope_b_iff pc1 pc2) Eb) as Hs.
    pose proof (Hcook Hs) as Hok.
    destruct Hs as (Eo & EM & HD).
    assert (E2 : pc_act (pc_frame pc1) (host_pc (pc_c pc2)) = pc2).
    { unfold pc_frame. rewrite Eo, EM.
      exact (act_frame_host pc2). }
    set (o := cook (MkClothoid (pc_c pc1)) (MkClothoid (pc_c pc2))) in *.
    assert (Hp : I_placed_ok pc1 pc2 (res_push (pc_frame pc1) o)).
    { rewrite <- (act_frame_host pc1) at 1. rewrite <- E2.
      apply (proj1 (transport (pc_frame pc1) _ _ o HD)).
      apply (proj1 (host_spec _ _ o)). exact Hok. }
    destruct o as [p ti tj| |]; cbn in Hp |- *.
    + split; [exact (conj Eo (conj EM HD)) | exact Hp].
    + split; [exact (conj Eo (conj EM HD)) | exact Hp].
    + exact (False_ind _ Hp).
  - cbn. intro Hs. apply (proj2 (pc_scope_b_iff pc1 pc2)) in Hs. congruence.
Qed.

Theorem cloth_sheet_claim : ClothoidSheetStmt.claim.
Proof.
  exact (conj push_shape (conj host_spec (conj transport sheet_cook_ok))).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Supporting.                                                            *)
(* -------------------------------------------------------------------------- *)

Lemma sheet_act_comp : forall g f S,
  sheet_act (aff_comp g f) S = sheet_act g (sheet_act f S).
Proof.
  intros g f S. unfold sheet_act. cbn. rewrite aff_comp_ap, !lin_ap_mul. reflexivity.
Qed.

Lemma sheet_act_frame : forall f S,
  curv_cross (sheet_e1 (sheet_act f S)) (sheet_e2 (sheet_act f S))
    = lin_det (af_L f) * curv_cross (sheet_e1 S) (sheet_e2 S).
Proof. intros. unfold sheet_act. cbn. apply curv_cross_lin. Qed.

Lemma noded_list_transport : forall f (G : list (PCloth * PCloth * IResult)),
  lin_det (af_L f) <> 0 ->
  Forall (fun r => I_placed_ok (fst (fst r)) (snd (fst r)) (snd r)) G ->
  Forall (fun r => I_placed_ok (fst (fst r)) (snd (fst r)) (snd r))
    (map (fun r => (pc_act f (fst (fst r)), pc_act f (snd (fst r)),
                    res_push f (snd r))) G).
Proof.
  intros f G HD HG. apply Forall_map. eapply Forall_impl; [|exact HG].
  intros [[pc1 pc2] o] H. cbn in *. apply (proj1 (transport f pc1 pc2 o HD)). exact H.
Qed.

Lemma tangency_transport : forall f pc1 pc2 s1 s2, lin_det (af_L f) <> 0 ->
  (curv_cross (pc_tangent pc1 s1) (pc_tangent pc2 s2) = 0
   <-> curv_cross (pc_tangent (pc_act f pc1) s1) (pc_tangent (pc_act f pc2) s2) = 0).
Proof.
  intros f pc1 pc2 s1 s2 HD. rewrite act_tangent_cross. split.
  - intros ->. ring.
  - intro H. apply (mul_nz_zero (lin_det (af_L f))); assumption.
Qed.

Lemma split_hen_transport : forall f pc t,
  pc_eval (fst (pc_split (pc_act f pc) t)) 1 = aff_ap f (pc_eval pc t) /\
  pc_eval (snd (pc_split (pc_act f pc) t)) 0 = aff_ap f (pc_eval pc t).
Proof.
  intros f pc t. rewrite act_split. cbn [fst snd]. rewrite !act_eval.
  unfold pc_split, pc_eval. cbn [pc_o pc_M pc_c fst snd].
  rewrite cloth_split_eval_left, cloth_split_eval_right.
  replace (t * 1) with t by ring. replace (t + (1 - t) * 0) with t by ring.
  split; reflexivity.
Qed.

Lemma boundary_transport : forall f pc p, lin_det (af_L f) <> 0 ->
  ((exists t, on_pc pc t p) <-> (exists t, on_pc (pc_act f pc) t (aff_ap f p))).
Proof.
  intros f pc p HD. split; intros [t H]; exists t; apply (on_pc_act f pc t p HD); exact H.
Qed.

Lemma orient_transport : forall f P Q X,
  Orientation.cross (aff_ap f P) (aff_ap f Q) (aff_ap f X)
    = lin_det (af_L f) * Orientation.cross P Q X.
Proof. intros. unfold Orientation.cross, aff_ap, placed, lin_ap, lin_det. cbn. ring. Qed.

Lemma edge_cross_aff : forall f p q,
  edge_cross (aff_ap f p) (aff_ap f q)
    = lin_det (af_L f) * edge_cross p q
      + edge_cross (af_b f) (lin_ap (af_L f) q) - edge_cross (af_b f) (lin_ap (af_L f) p).
Proof. intros. unfold edge_cross, aff_ap, placed, lin_ap, lin_det. cbn. ring. Qed.

Lemma shoelace_open_map : forall f l p d,
  shoelace_open (map (aff_ap f) (p :: l))
    = lin_det (af_L f) * shoelace_open (p :: l)
      + edge_cross (af_b f) (lin_ap (af_L f) (last (p :: l) d))
      - edge_cross (af_b f) (lin_ap (af_L f) p).
Proof.
  intros f l. induction l as [|q l IH]; intros p d.
  - cbn. ring.
  - change (map (aff_ap f) (p :: q :: l))
      with (aff_ap f p :: aff_ap f q :: map (aff_ap f) l).
    rewrite shoelace_open_cons2, shoelace_open_cons2.
    change (aff_ap f q :: map (aff_ap f) l) with (map (aff_ap f) (q :: l)).
    rewrite (IH q d), edge_cross_aff.
    change (last (p :: q :: l) d) with (last (q :: l) d). ring.
Qed.

Lemma ring_area_transport : forall f l,
  RingArea979.signed_area2 (map (aff_ap f) l)
    = lin_det (af_L f) * RingArea979.signed_area2 l.
Proof.
  intros f [|p0 rest]; [cbn; ring|].
  assert (Hm : (aff_ap f p0 :: map (aff_ap f) rest) ++ [aff_ap f p0]
               = map (aff_ap f) (p0 :: rest ++ [p0]))
    by (cbn [map app]; rewrite map_app; reflexivity).
  unfold RingArea979.signed_area2.
  change (map (aff_ap f) (p0 :: rest)) with (aff_ap f p0 :: map (aff_ap f) rest).
  cbv beta iota. rewrite Hm.
  change ((p0 :: rest) ++ [p0]) with (p0 :: rest ++ [p0]).
  rewrite (shoelace_open_map f (rest ++ [p0]) p0 p0).
  rewrite app_comm_cons, last_last. ring.
Qed.

Theorem cloth_sheet_supporting : ClothoidSheetStmt.supporting.
Proof.
  split; [exact pc_scope_b_iff|].
  split; [exact sheet_act_comp|].
  split; [exact sheet_act_frame|].
  split; [exact noded_list_transport|].
  split; [exact tangency_transport|].
  split; [exact split_hen_transport|].
  split; [exact boundary_transport|].
  split; [exact orient_transport | exact ring_area_transport].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Witness: the locked Hit on the GEOS shear frame, and the limit.        *)
(* -------------------------------------------------------------------------- *)

Lemma placed_zero : forall M p, placed (mkPoint 0 0) M p = lin_ap M p.
Proof. intros M [x y]. unfold placed, lin_ap. cbn. f_equal; ring. Qed.

Theorem cloth_sheet_witness : ClothoidSheetStmt.witness.
Proof.
  assert (HD : lin_det geos_shear <> 0) by (rewrite geos_shear_det; lra).
  split; [|split].
  - set (pcA := mkPCloth (mkPoint 0 0) geos_shear locked_cloth_A).
    set (pcB := mkPCloth (mkPoint 0 0) geos_shear locked_cloth_B).
    set (cook := fun (_ _ : Egg) =>
                   IHit locked_cloth_hit_pt locked_cloth_ti locked_cloth_tj).
    assert (Hs : pc_scope pcA pcB)
      by (unfold pc_scope, pcA, pcB; cbn; repeat split; exact HD).
    pose proof (sheet_cook_ok cook pcA pcB (fun _ => locked_mkclothoid_I_ok)) as Hk.
    replace (IHit (lin_ap geos_shear locked_cloth_hit_pt) locked_cloth_ti locked_cloth_tj)
      with (sheet_cook cook pcA pcB); [exact Hk|].
    unfold sheet_cook. rewrite (proj2 (pc_scope_b_iff pcA pcB) Hs).
    unfold cook, pcA, res_push, pc_frame, aff_ap. cbn [pc_o pc_M af_b af_L].
    rewrite placed_zero. reflexivity.
  - intro cook. unfold sheet_cook.
    destruct (pc_scope_b _ _) eqn:E; [|reflexivity].
    apply pc_scope_b_iff in E. destruct E as (_ & EM & _).
    unfold host_pc, lin_id, geos_shear in EM. cbn in EM. injection EM. lra.
  - intros s1 s2 H12.
    replace (lin_mul (lin_inv (pc_M (host_pc locked_cloth_A))) geos_shear)
      with geos_shear.
    + exact (cloth_shear_law_witness s1 s2 H12).
    + unfold host_pc, lin_mul, lin_inv, lin_id, lin_det, geos_shear. cbn.
      f_equal; field.
Qed.

Print Assumptions aff_inj.
Print Assumptions act_frame_host.
Print Assumptions push_shape.
Print Assumptions host_spec.
Print Assumptions transport.
Print Assumptions pc_scope_b_iff.
Print Assumptions sheet_cook_ok.
Print Assumptions cloth_sheet_claim.
Print Assumptions sheet_act_comp.
Print Assumptions noded_list_transport.
Print Assumptions tangency_transport.
Print Assumptions split_hen_transport.
Print Assumptions boundary_transport.
Print Assumptions orient_transport.
Print Assumptions shoelace_open_map.
Print Assumptions ring_area_transport.
Print Assumptions cloth_sheet_supporting.
Print Assumptions cloth_sheet_witness.
