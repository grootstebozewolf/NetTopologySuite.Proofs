(* ============================================================================
   NetTopologySuite.Proofs.RelateNGTouchEdgeCellsGeneral
   ----------------------------------------------------------------------------
   Issue #842 / ADR-0003 specification tier (open interior, 0 < gtri).

   Forall-quantified IB/BI/IE/EI/BE/EB cells of a shared-edge triangle
   touch.  The frozen pair in RelateNGTouchEdgeCells stays the witness
   instance (touch_edge_pair_ogc_gtri_cells); this module does not
   re-prove that pair as the claim.

   IB/IE are corollaries of touch_int_ext_exclusion.  BI/EI are the
   same facts after triangles_touch_on_shared_edge_sym.  BE/EB are the
   half-plane separation touch_halfplane_ext: once both triangles are
   CCW, same-direction shares_edge is impossible and the shared edge
   is traversed in opposite directions, so a positive shared-edge
   slack of A is a negative slack of B.

   0 < gdbl is the CCW reading that makes 0 < gtri the open interior.
   It is not a ring_complement / ray_avoids_vertices guard.  These
   six cells never cross the parity-to-spec bridge.

   claimId: 0003-touch-edge-cells-general
   WITNESS topic: relate · claimId: 0003-touch-edge-cells-general
   witness: 0003-touch-edge-cells-general
   board: ADR-0003
   issue: #842 (parent map #822; classification #823)

   No Admitted, no Axiom, no Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Orientation.
From NTS.Proofs Require Import GeneralTriangleSeparation.
From NTS.Proofs Require Import RelateMatrixTriangle.
From NTS.Proofs Require Import RelateNGTouch.

Local Open Scope R_scope.

(* Same cell-dimension predicates as RelateNGDisjointCells. *)
Definition gtri_cell_empty (P : Point -> Prop) : Prop :=
  forall p, ~ P p.

Definition gtri_cell_dim1 (P : Point -> Prop) : Prop :=
  exists q r, P q /\ P r /\ q <> r.

Definition gtri_cell_dim2 (P : Point -> Prop) : Prop :=
  exists c r, 0 < r /\ forall q, dist c q < r -> P q.

(* -------------------------------------------------------------------------- *)
(* Symmetry of the 9-disjunct touch predicate.                                *)
(* -------------------------------------------------------------------------- *)

Lemma shares_edge_sym : forall p1 p2 q1 q2,
  shares_edge p1 p2 q1 q2 -> shares_edge q1 q2 p1 p2.
Proof.
  intros p1 p2 q1 q2 [[H1 H2] | [H1 H2]].
  - left. split; symmetry; assumption.
  - right. split; symmetry; assumption.
Qed.

Lemma opposite_sides_sym : forall p1 p2 p q,
  opposite_sides p1 p2 p q -> opposite_sides p1 p2 q p.
Proof.
  unfold opposite_sides. intros p1 p2 p q H. lra.
Qed.

Lemma cross_rev : forall p1 p2 q,
  cross p2 p1 q = - cross p1 p2 q.
Proof.
  intros p1 p2 q. unfold cross. simpl. ring.
Qed.

Lemma opposite_sides_rev_edge : forall p1 p2 p q,
  opposite_sides p1 p2 p q -> opposite_sides p2 p1 p q.
Proof.
  intros p1 p2 p q H.
  unfold opposite_sides in *.
  rewrite (cross_rev p1 p2 p), (cross_rev p1 p2 q).
  lra.
Qed.

Ltac finish_sym H :=
  let Hs := fresh "Hs" in
  let Ho := fresh "Ho" in
  let Ha := fresh "Ha" in
  let Hb := fresh "Hb" in
  destruct H as [Hs Ho];
  destruct Hs as [[Ha Hb] | [Ha Hb]];
  [ split;
      [ left; split; [ symmetry; exact Ha | symmetry; exact Hb ]
      | subst; apply opposite_sides_sym; exact Ho ]
  | split;
      [ right; split; [ symmetry; exact Hb | symmetry; exact Ha ]
      | subst; apply opposite_sides_sym;
        apply opposite_sides_rev_edge; exact Ho ]
  ].

Lemma triangles_touch_on_shared_edge_sym :
  forall a1 a2 a3 b1 b2 b3,
    triangles_touch_on_shared_edge a1 a2 a3 b1 b2 b3 ->
    triangles_touch_on_shared_edge b1 b2 b3 a1 a2 a3.
Proof.
  intros a1 a2 a3 b1 b2 b3 H.
  destruct H as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]].
  - left. finish_sym H.
  - do 3 right. left. finish_sym H.
  - do 6 right. left. finish_sym H.
  - right. left. finish_sym H.
  - do 4 right. left. finish_sym H.
  - do 7 right. left. finish_sym H.
  - do 2 right. left. finish_sym H.
  - do 5 right. left. finish_sym H.
  - do 8 right. finish_sym H.
Qed.

(* -------------------------------------------------------------------------- *)
(* CCW orientation identities.  Same-direction sharing contradicts both CCW.  *)
(* -------------------------------------------------------------------------- *)

Lemma cross_abc : forall ax ay bx by_ cx cy,
  cross (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy) =
  gdbl ax ay bx by_ cx cy.
Proof. intros. unfold cross, gdbl. simpl. ring. Qed.

Lemma cross_bca : forall ax ay bx by_ cx cy,
  cross (mkPoint bx by_) (mkPoint cx cy) (mkPoint ax ay) =
  gdbl ax ay bx by_ cx cy.
Proof. intros. unfold cross, gdbl. simpl. ring. Qed.

Lemma cross_cab : forall ax ay bx by_ cx cy,
  cross (mkPoint cx cy) (mkPoint ax ay) (mkPoint bx by_) =
  gdbl ax ay bx by_ cx cy.
Proof. intros. unfold cross, gdbl. simpl. ring. Qed.

Lemma not_opp_when_pos : forall p1 p2 u v,
  0 < cross p1 p2 u ->
  0 < cross p1 p2 v ->
  ~ opposite_sides p1 p2 u v.
Proof.
  intros p1 p2 u v Hu Hv Hopp.
  unfold opposite_sides in Hopp.
  apply (Rlt_irrefl 0).
  apply Rlt_trans with (cross p1 p2 u * cross p1 p2 v).
  - apply Rmult_lt_0_compat; assumption.
  - exact Hopp.
Qed.

Lemma gdbl_rot : forall ax ay bx by_ cx cy,
  gdbl bx by_ cx cy ax ay = gdbl ax ay bx by_ cx cy.
Proof. intros. unfold gdbl. ring. Qed.

Lemma gdbl_rot2 : forall ax ay bx by_ cx cy,
  gdbl cx cy ax ay bx by_ = gdbl ax ay bx by_ cx cy.
Proof.
  intros.
  rewrite (gdbl_rot bx by_ cx cy ax ay).
  rewrite (gdbl_rot ax ay bx by_ cx cy).
  reflexivity.
Qed.

Lemma Rmin_rot : forall a b c, Rmin (Rmin b c) a = Rmin (Rmin a b) c.
Proof.
  intros a b c.
  rewrite (Rmin_comm (Rmin b c) a).
  rewrite <- (Rmin_assoc a b c).
  reflexivity.
Qed.

Lemma gtri_rot : forall ax ay bx by_ cx cy p,
  gtri bx by_ cx cy ax ay p = gtri ax ay bx by_ cx cy p.
Proof.
  intros ax ay bx by_ cx cy p.
  unfold gtri.
  assert (E1 : gsA bx by_ cx cy p = gsB bx by_ cx cy p) by (unfold gsA, gsB; ring).
  assert (E2 : gsB cx cy ax ay p = gsC ax ay cx cy p) by (unfold gsB, gsC; ring).
  assert (E3 : gsC bx by_ ax ay p = gsA ax ay bx by_ p) by (unfold gsC, gsA; ring).
  rewrite E1, E2, E3.
  apply Rmin_rot.
Qed.

Lemma gtri_rot2 : forall ax ay bx by_ cx cy p,
  gtri cx cy ax ay bx by_ p = gtri ax ay bx by_ cx cy p.
Proof.
  intros ax ay bx by_ cx cy p.
  rewrite (gtri_rot bx by_ cx cy ax ay p).
  rewrite (gtri_rot ax ay bx by_ cx cy p).
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Half-plane: B's first edge is the reverse of A's first edge, so a point    *)
(* strictly on A's side of that line has negative gtri against B.             *)
(* -------------------------------------------------------------------------- *)

Lemma gsA_neg_rev : forall ax ay bx by_ p,
  gsA bx by_ ax ay p = - gsA ax ay bx by_ p.
Proof. intros. unfold gsA. simpl. ring. Qed.

Lemma touch_halfplane_ext :
  forall ax ay bx by_ ox oy p,
    0 < gsA ax ay bx by_ p ->
    gtri bx by_ ax ay ox oy p < 0.
Proof.
  intros ax ay bx by_ ox oy p Hs.
  apply Rle_lt_trans with (gsA bx by_ ax ay p).
  - apply (gtri_le_gsA bx by_ ax ay ox oy p).
  - rewrite (gsA_neg_rev ax ay bx by_ p). lra.
Qed.

Lemma gtri_zero_gsC : forall ax ay bx by_ cx cy p,
  0 <= gsA ax ay bx by_ p ->
  0 <= gsB bx by_ cx cy p ->
  gsC ax ay cx cy p = 0 ->
  gtri ax ay bx by_ cx cy p = 0.
Proof.
  intros ax ay bx by_ cx cy p HA HB HC.
  unfold gtri. rewrite HC.
  apply Rmin_right.
  apply Rmin_glb; assumption.
Qed.

Lemma gs_on_ac : forall ax ay bx by_ cx cy t,
  gsA ax ay bx by_
      (mkPoint ((1 - t) * ax + t * cx) ((1 - t) * ay + t * cy)) =
    t * gdbl ax ay bx by_ cx cy /\
  gsB bx by_ cx cy
      (mkPoint ((1 - t) * ax + t * cx) ((1 - t) * ay + t * cy)) =
    (1 - t) * gdbl ax ay bx by_ cx cy /\
  gsC ax ay cx cy
      (mkPoint ((1 - t) * ax + t * cx) ((1 - t) * ay + t * cy)) = 0.
Proof.
  intros ax ay bx by_ cx cy t.
  unfold gsA, gsB, gsC, gdbl. simpl. repeat split; ring.
Qed.

(* Open relative interior of the non-shared edge AC, in the canonical
   reverse-edge frame.  t = 0 is the shared vertex A and is excluded. *)
Lemma touch_nonshared_edge_ext :
  forall ax ay bx by_ cx cy ox oy t,
    0 < gdbl ax ay bx by_ cx cy ->
    0 < t ->
    t <= 1 ->
    gtri ax ay bx by_ cx cy
      (mkPoint ((1 - t) * ax + t * cx) ((1 - t) * ay + t * cy)) = 0 /\
    gtri bx by_ ax ay ox oy
      (mkPoint ((1 - t) * ax + t * cx) ((1 - t) * ay + t * cy)) < 0 /\
    gsA ax ay bx by_
      (mkPoint ((1 - t) * ax + t * cx) ((1 - t) * ay + t * cy)) =
      t * gdbl ax ay bx by_ cx cy.
Proof.
  intros ax ay bx by_ cx cy ox oy t Hccw Ht0 Ht1.
  destruct (gs_on_ac ax ay bx by_ cx cy t) as [HA [HB HC]].
  split; [| split].
  - apply gtri_zero_gsC.
    + rewrite HA. apply Rmult_le_pos; apply Rlt_le; assumption.
    + rewrite HB. apply Rmult_le_pos.
      * lra.
      * apply Rlt_le. exact Hccw.
    + exact HC.
  - apply (touch_halfplane_ext ax ay bx by_ ox oy).
    rewrite HA.
    apply Rmult_lt_0_compat; assumption.
  - exact HA.
Qed.

Lemma be_points_ab_rev :
  forall ax ay bx by_ cx cy ox oy,
    0 < gdbl ax ay bx by_ cx cy ->
    0 < gdbl bx by_ ax ay ox oy ->
    exists q r,
      gtri ax ay bx by_ cx cy q = 0 /\
      gtri bx by_ ax ay ox oy q < 0 /\
      gtri ax ay bx by_ cx cy r = 0 /\
      gtri bx by_ ax ay ox oy r < 0 /\
      q <> r.
Proof.
  intros ax ay bx by_ cx cy ox oy HA HB.
  pose (q := mkPoint ((1 - 1) * ax + 1 * cx) ((1 - 1) * ay + 1 * cy)).
  pose (r := mkPoint ((1 - 1 / 2) * ax + (1 / 2) * cx)
                     ((1 - 1 / 2) * ay + (1 / 2) * cy)).
  assert (Hq : gtri ax ay bx by_ cx cy q = 0 /\
               gtri bx by_ ax ay ox oy q < 0 /\
               gsA ax ay bx by_ q = 1 * gdbl ax ay bx by_ cx cy).
  { apply (touch_nonshared_edge_ext ax ay bx by_ cx cy ox oy 1); lra. }
  assert (Hr : gtri ax ay bx by_ cx cy r = 0 /\
               gtri bx by_ ax ay ox oy r < 0 /\
               gsA ax ay bx by_ r = (1 / 2) * gdbl ax ay bx by_ cx cy).
  { apply (touch_nonshared_edge_ext ax ay bx by_ cx cy ox oy (1 / 2)); lra. }
  exists q, r.
  destruct Hq as [Hq0 [HqB HqS]].
  destruct Hr as [Hr0 [HrB HrS]].
  repeat split; try assumption.
  intro Heq.
  assert (gsA ax ay bx by_ q = gsA ax ay bx by_ r) by (rewrite Heq; reflexivity).
  lra.
Qed.

Ltac align_B E1 E2 Harea :=
  let X1 := fresh "X1" in
  let Y1 := fresh "Y1" in
  let X2 := fresh "X2" in
  let Y2 := fresh "Y2" in
  pose proof (f_equal px E1) as X1;
  pose proof (f_equal py E1) as Y1;
  pose proof (f_equal px E2) as X2;
  pose proof (f_equal py E2) as Y2;
  simpl in X1, Y1, X2, Y2;
  rewrite <- X1, <- Y1, <- X2, <- Y2 in Harea.

Ltac align_goal E1 E2 :=
  let X1 := fresh "X1" in
  let Y1 := fresh "Y1" in
  let X2 := fresh "X2" in
  let Y2 := fresh "Y2" in
  pose proof (f_equal px E1) as X1;
  pose proof (f_equal py E1) as Y1;
  pose proof (f_equal px E2) as X2;
  pose proof (f_equal py E2) as Y2;
  simpl in X1, Y1, X2, Y2;
  rewrite <- X1, <- Y1, <- X2, <- Y2.

Lemma touch_be_dim1_general :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    triangles_touch_on_shared_edge
      (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
      (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) ->
    0 < gdbl ax ay bx by_ cx cy ->
    0 < gdbl dx dy ex ey fx fy ->
    gtri_cell_dim1 (fun p =>
      gtri ax ay bx by_ cx cy p = 0 /\
      gtri dx dy ex ey fx fy p < 0).
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Htouch HA HB.
  destruct Htouch as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]].
  - (* a1 a2 with b1 b2 *)
    destruct H as [Hsh Hopp].
    destruct Hsh as [[E1 E2] | [E1 E2]].
    + exfalso. align_B E1 E2 HB.
      apply (not_opp_when_pos (mkPoint ax ay) (mkPoint bx by_)
               (mkPoint cx cy) (mkPoint fx fy)).
      * rewrite (cross_abc ax ay bx by_ cx cy). exact HA.
      * rewrite (cross_abc ax ay bx by_ fx fy). exact HB.
      * exact Hopp.
    + align_B E1 E2 HB. align_goal E1 E2.
      destruct (be_points_ab_rev ax ay bx by_ cx cy fx fy HA HB)
        as (q & r & Hq0 & HqB & Hr0 & HrB & Hneq).
      exists q, r. repeat split; assumption.
  - (* a1 a2 with b2 b3 *)
    destruct H as [Hsh Hopp].
    destruct Hsh as [[E1 E2] | [E1 E2]].
    + exfalso. align_B E1 E2 HB.
      apply (not_opp_when_pos (mkPoint ax ay) (mkPoint bx by_)
               (mkPoint cx cy) (mkPoint dx dy)).
      * rewrite (cross_abc ax ay bx by_ cx cy). exact HA.
      * rewrite (cross_bca dx dy ax ay bx by_). exact HB.
      * exact Hopp.
    + align_B E1 E2 HB. align_goal E1 E2.
      assert (HB' : 0 < gdbl bx by_ ax ay dx dy).
      { rewrite (gdbl_rot dx dy bx by_ ax ay). exact HB. }
      destruct (be_points_ab_rev ax ay bx by_ cx cy dx dy HA HB')
        as (q & r & Hq0 & HqB & Hr0 & HrB & Hneq).
      rewrite (gtri_rot dx dy bx by_ ax ay q) in HqB.
      rewrite (gtri_rot dx dy bx by_ ax ay r) in HrB.
      exists q, r. repeat split; assumption.
  - (* a1 a2 with b3 b1 *)
    destruct H as [Hsh Hopp].
    destruct Hsh as [[E1 E2] | [E1 E2]].
    + exfalso. align_B E1 E2 HB.
      apply (not_opp_when_pos (mkPoint ax ay) (mkPoint bx by_)
               (mkPoint cx cy) (mkPoint ex ey)).
      * rewrite (cross_abc ax ay bx by_ cx cy). exact HA.
      * rewrite (cross_cab bx by_ ex ey ax ay). exact HB.
      * exact Hopp.
    + align_B E1 E2 HB. align_goal E1 E2.
      assert (HB' : 0 < gdbl bx by_ ax ay ex ey).
      { rewrite (gdbl_rot2 ax ay ex ey bx by_). exact HB. }
      destruct (be_points_ab_rev ax ay bx by_ cx cy ex ey HA HB')
        as (q & r & Hq0 & HqB & Hr0 & HrB & Hneq).
      rewrite (gtri_rot2 ax ay ex ey bx by_ q) in HqB.
      rewrite (gtri_rot2 ax ay ex ey bx by_ r) in HrB.
      exists q, r. repeat split; assumption.
  - (* a2 a3 with b1 b2 *)
    destruct H as [Hsh Hopp].
    destruct Hsh as [[E1 E2] | [E1 E2]].
    + exfalso. align_B E1 E2 HB.
      apply (not_opp_when_pos (mkPoint bx by_) (mkPoint cx cy)
               (mkPoint ax ay) (mkPoint fx fy)).
      * rewrite (cross_bca ax ay bx by_ cx cy). exact HA.
      * rewrite (cross_abc bx by_ cx cy fx fy). exact HB.
      * exact Hopp.
    + align_B E1 E2 HB. align_goal E1 E2.
      assert (HA' : 0 < gdbl bx by_ cx cy ax ay).
      { rewrite (gdbl_rot ax ay bx by_ cx cy). exact HA. }
      destruct (be_points_ab_rev bx by_ cx cy ax ay fx fy HA' HB)
        as (q & r & Hq0 & HqB & Hr0 & HrB & Hneq).
      rewrite (gtri_rot ax ay bx by_ cx cy q) in Hq0.
      rewrite (gtri_rot ax ay bx by_ cx cy r) in Hr0.
      exists q, r. repeat split; assumption.
  - (* a2 a3 with b2 b3 *)
    destruct H as [Hsh Hopp].
    destruct Hsh as [[E1 E2] | [E1 E2]].
    + exfalso. align_B E1 E2 HB.
      apply (not_opp_when_pos (mkPoint bx by_) (mkPoint cx cy)
               (mkPoint ax ay) (mkPoint dx dy)).
      * rewrite (cross_bca ax ay bx by_ cx cy). exact HA.
      * rewrite (cross_bca dx dy bx by_ cx cy). exact HB.
      * exact Hopp.
    + align_B E1 E2 HB. align_goal E1 E2.
      assert (HA' : 0 < gdbl bx by_ cx cy ax ay).
      { rewrite (gdbl_rot ax ay bx by_ cx cy). exact HA. }
      assert (HB' : 0 < gdbl cx cy bx by_ dx dy).
      { rewrite (gdbl_rot dx dy cx cy bx by_). exact HB. }
      destruct (be_points_ab_rev bx by_ cx cy ax ay dx dy HA' HB')
        as (q & r & Hq0 & HqB & Hr0 & HrB & Hneq).
      rewrite (gtri_rot ax ay bx by_ cx cy q) in Hq0.
      rewrite (gtri_rot ax ay bx by_ cx cy r) in Hr0.
      rewrite (gtri_rot dx dy cx cy bx by_ q) in HqB.
      rewrite (gtri_rot dx dy cx cy bx by_ r) in HrB.
      exists q, r. repeat split; assumption.
  - (* a2 a3 with b3 b1 *)
    destruct H as [Hsh Hopp].
    destruct Hsh as [[E1 E2] | [E1 E2]].
    + exfalso. align_B E1 E2 HB.
      apply (not_opp_when_pos (mkPoint bx by_) (mkPoint cx cy)
               (mkPoint ax ay) (mkPoint ex ey)).
      * rewrite (cross_bca ax ay bx by_ cx cy). exact HA.
      * rewrite (cross_cab cx cy ex ey bx by_). exact HB.
      * exact Hopp.
    + align_B E1 E2 HB. align_goal E1 E2.
      assert (HA' : 0 < gdbl bx by_ cx cy ax ay).
      { rewrite (gdbl_rot ax ay bx by_ cx cy). exact HA. }
      assert (HB' : 0 < gdbl cx cy bx by_ ex ey).
      { rewrite (gdbl_rot2 bx by_ ex ey cx cy). exact HB. }
      destruct (be_points_ab_rev bx by_ cx cy ax ay ex ey HA' HB')
        as (q & r & Hq0 & HqB & Hr0 & HrB & Hneq).
      rewrite (gtri_rot ax ay bx by_ cx cy q) in Hq0.
      rewrite (gtri_rot ax ay bx by_ cx cy r) in Hr0.
      rewrite (gtri_rot2 bx by_ ex ey cx cy q) in HqB.
      rewrite (gtri_rot2 bx by_ ex ey cx cy r) in HrB.
      exists q, r. repeat split; assumption.
  - (* a3 a1 with b1 b2 *)
    destruct H as [Hsh Hopp].
    destruct Hsh as [[E1 E2] | [E1 E2]].
    + exfalso. align_B E1 E2 HB.
      apply (not_opp_when_pos (mkPoint cx cy) (mkPoint ax ay)
               (mkPoint bx by_) (mkPoint fx fy)).
      * rewrite (cross_cab ax ay bx by_ cx cy). exact HA.
      * rewrite (cross_abc cx cy ax ay fx fy). exact HB.
      * exact Hopp.
    + align_B E1 E2 HB. align_goal E1 E2.
      assert (HA' : 0 < gdbl cx cy ax ay bx by_).
      { rewrite (gdbl_rot2 ax ay bx by_ cx cy). exact HA. }
      destruct (be_points_ab_rev cx cy ax ay bx by_ fx fy HA' HB)
        as (q & r & Hq0 & HqB & Hr0 & HrB & Hneq).
      rewrite (gtri_rot2 ax ay bx by_ cx cy q) in Hq0.
      rewrite (gtri_rot2 ax ay bx by_ cx cy r) in Hr0.
      exists q, r. repeat split; assumption.
  - (* a3 a1 with b2 b3 *)
    destruct H as [Hsh Hopp].
    destruct Hsh as [[E1 E2] | [E1 E2]].
    + exfalso. align_B E1 E2 HB.
      apply (not_opp_when_pos (mkPoint cx cy) (mkPoint ax ay)
               (mkPoint bx by_) (mkPoint dx dy)).
      * rewrite (cross_cab ax ay bx by_ cx cy). exact HA.
      * rewrite (cross_bca dx dy cx cy ax ay). exact HB.
      * exact Hopp.
    + align_B E1 E2 HB. align_goal E1 E2.
      assert (HA' : 0 < gdbl cx cy ax ay bx by_).
      { rewrite (gdbl_rot2 ax ay bx by_ cx cy). exact HA. }
      assert (HB' : 0 < gdbl ax ay cx cy dx dy).
      { rewrite (gdbl_rot dx dy ax ay cx cy). exact HB. }
      destruct (be_points_ab_rev cx cy ax ay bx by_ dx dy HA' HB')
        as (q & r & Hq0 & HqB & Hr0 & HrB & Hneq).
      rewrite (gtri_rot2 ax ay bx by_ cx cy q) in Hq0.
      rewrite (gtri_rot2 ax ay bx by_ cx cy r) in Hr0.
      rewrite (gtri_rot dx dy ax ay cx cy q) in HqB.
      rewrite (gtri_rot dx dy ax ay cx cy r) in HrB.
      exists q, r. repeat split; assumption.
  - (* a3 a1 with b3 b1 *)
    destruct H as [Hsh Hopp].
    destruct Hsh as [[E1 E2] | [E1 E2]].
    + exfalso. align_B E1 E2 HB.
      apply (not_opp_when_pos (mkPoint cx cy) (mkPoint ax ay)
               (mkPoint bx by_) (mkPoint ex ey)).
      * rewrite (cross_cab ax ay bx by_ cx cy). exact HA.
      * rewrite (cross_cab ax ay ex ey cx cy). exact HB.
      * exact Hopp.
    + align_B E1 E2 HB. align_goal E1 E2.
      assert (HA' : 0 < gdbl cx cy ax ay bx by_).
      { rewrite (gdbl_rot2 ax ay bx by_ cx cy). exact HA. }
      assert (HB' : 0 < gdbl ax ay cx cy ex ey).
      { rewrite (gdbl_rot2 cx cy ex ey ax ay). exact HB. }
      destruct (be_points_ab_rev cx cy ax ay bx by_ ex ey HA' HB')
        as (q & r & Hq0 & HqB & Hr0 & HrB & Hneq).
      rewrite (gtri_rot2 ax ay bx by_ cx cy q) in Hq0.
      rewrite (gtri_rot2 ax ay bx by_ cx cy r) in Hr0.
      rewrite (gtri_rot2 cx cy ex ey ax ay q) in HqB.
      rewrite (gtri_rot2 cx cy ex ey ax ay r) in HrB.
      exists q, r. repeat split; assumption.
Qed.

Lemma touch_eb_dim1_general :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    triangles_touch_on_shared_edge
      (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
      (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) ->
    0 < gdbl ax ay bx by_ cx cy ->
    0 < gdbl dx dy ex ey fx fy ->
    gtri_cell_dim1 (fun p =>
      gtri ax ay bx by_ cx cy p < 0 /\
      gtri dx dy ex ey fx fy p = 0).
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Htouch HA HB.
  pose proof (triangles_touch_on_shared_edge_sym
                (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
                (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) Htouch)
    as Hsym.
  destruct (touch_be_dim1_general dx dy ex ey fx fy ax ay bx by_ cx cy
              Hsym HB HA)
    as (q & r & (Hq0 & HqA) & (Hr0 & HrA) & Hneq).
  exists q, r.
  split; [split; [exact HqA | exact Hq0]|].
  split; [split; [exact HrA | exact Hr0]| exact Hneq].
Qed.

(* -------------------------------------------------------------------------- *)
(* Open interior disk of a CCW triangle, then IE / EI.                        *)
(* -------------------------------------------------------------------------- *)

Lemma gs_centroid : forall ax ay bx by_ cx cy,
  gsA ax ay bx by_
      (mkPoint ((ax + bx + cx) / 3) ((ay + by_ + cy) / 3)) =
    gdbl ax ay bx by_ cx cy / 3 /\
  gsB bx by_ cx cy
      (mkPoint ((ax + bx + cx) / 3) ((ay + by_ + cy) / 3)) =
    gdbl ax ay bx by_ cx cy / 3 /\
  gsC ax ay cx cy
      (mkPoint ((ax + bx + cx) / 3) ((ay + by_ + cy) / 3)) =
    gdbl ax ay bx by_ cx cy / 3.
Proof.
  intros ax ay bx by_ cx cy.
  unfold gsA, gsB, gsC, gdbl. simpl. repeat split; field.
Qed.

Lemma gsA_delta : forall ax ay bx by_ p q,
  gsA ax ay bx by_ p - gsA ax ay bx by_ q =
    (bx - ax) * (py p - py q) - (by_ - ay) * (px p - px q).
Proof. intros. unfold gsA. ring. Qed.

Lemma gsB_delta : forall bx by_ cx cy p q,
  gsB bx by_ cx cy p - gsB bx by_ cx cy q =
    (cx - bx) * (py p - py q) - (cy - by_) * (px p - px q).
Proof. intros. unfold gsB. ring. Qed.

Lemma gsC_delta : forall ax ay cx cy p q,
  gsC ax ay cx cy p - gsC ax ay cx cy q =
    (ax - cx) * (py p - py q) - (ay - cy) * (px p - px q).
Proof. intros. unfold gsC. ring. Qed.

Lemma Rabs_lin_bound : forall a b u v d,
  Rabs u <= d ->
  Rabs v <= d ->
  Rabs (a * u - b * v) <= (Rabs a + Rabs b) * d.
Proof.
  intros a b u v d Hu Hv.
  replace (a * u - b * v) with (a * u + (- b) * v) by ring.
  eapply Rle_trans.
  - apply Rabs_triang.
  - rewrite (Rabs_mult a u), (Rabs_mult (- b) v), (Rabs_Ropp b).
    apply Rle_trans with (Rabs a * d + Rabs b * d).
    + apply Rplus_le_compat; apply Rmult_le_compat_l; try apply Rabs_pos; assumption.
    + replace (Rabs a * d + Rabs b * d) with ((Rabs a + Rabs b) * d) by ring.
      apply Rle_refl.
Qed.

Lemma Rabs_mul_self : forall x, Rabs x * Rabs x = x * x.
Proof.
  intros x. rewrite <- Rabs_mult. apply Rabs_pos_eq. apply Rle_0_sqr.
Qed.

Lemma abs_coord_le_dist_x : forall p q, Rabs (px p - px q) <= dist p q.
Proof.
  intros p q.
  pose proof (dist_sq_nonneg p q) as Hnn.
  unfold dist.
  apply (proj2 (sq_monotone_nonneg (Rabs (px p - px q))
                   (sqrt (dist_sq p q)) (Rabs_pos _) (sqrt_pos _))).
  rewrite sqrt_sqrt by exact Hnn.
  rewrite Rabs_mul_self.
  unfold dist_sq. pose proof (Rle_0_sqr (py p - py q)). unfold Rsqr in *. lra.
Qed.

Lemma abs_coord_le_dist_y : forall p q, Rabs (py p - py q) <= dist p q.
Proof.
  intros p q.
  pose proof (dist_sq_nonneg p q) as Hnn.
  unfold dist.
  apply (proj2 (sq_monotone_nonneg (Rabs (py p - py q))
                   (sqrt (dist_sq p q)) (Rabs_pos _) (sqrt_pos _))).
  rewrite sqrt_sqrt by exact Hnn.
  rewrite Rabs_mul_self.
  unfold dist_sq. pose proof (Rle_0_sqr (px p - px q)). unfold Rsqr in *. lra.
Qed.

Lemma plus_abs_ge : forall x y, y <= x + Rabs (x - y).
Proof.
  intros x y.
  pose proof (Rle_abs (- (x - y))) as H.
  rewrite Rabs_Ropp in H. lra.
Qed.

Lemma slack_above_lip : forall s s0 edge d rad,
  Rabs (s - s0) <= edge * d ->
  d <= rad ->
  0 <= edge ->
  edge * rad < s0 ->
  0 < s.
Proof.
  intros s s0 edge d rad Habs Hd Hedge Hlt.
  assert (s0 - Rabs (s - s0) <= s).
  { pose proof (plus_abs_ge s s0) as Hp. lra. }
  assert (s0 - edge * d <= s0 - Rabs (s - s0)).
  { apply Rplus_le_compat_l. apply Ropp_le_contravar. exact Habs. }
  assert (edge * d <= edge * rad).
  { apply Rmult_le_compat_l; assumption. }
  lra.
Qed.

Lemma edge_rad_lt_slack : forall edge lip0 g3,
  0 <= edge ->
  edge < lip0 ->
  0 < lip0 ->
  0 < g3 ->
  edge * (g3 / lip0) < g3.
Proof.
  intros edge lip0 g3 _ Hlt Hlip Hg.
  apply (Rmult_lt_reg_l lip0).
  - exact Hlip.
  - unfold Rdiv.
    replace (lip0 * (edge * (g3 * / lip0))) with (edge * g3).
    + apply Rmult_lt_compat_r; assumption.
    + field. exact (not_eq_sym (Rlt_not_eq 0 lip0 Hlip)).
Qed.

Lemma ccw_triangle_interior_disk :
  forall ax ay bx by_ cx cy,
    0 < gdbl ax ay bx by_ cx cy ->
    exists c r,
      0 < r /\
      forall q, dist c q < r -> 0 < gtri ax ay bx by_ cx cy q.
Proof.
  intros ax ay bx by_ cx cy Hccw.
  set (c := mkPoint ((ax + bx + cx) / 3) ((ay + by_ + cy) / 3)).
  set (eAB := Rabs (bx - ax) + Rabs (by_ - ay)).
  set (eBC := Rabs (cx - bx) + Rabs (cy - by_)).
  set (eCA := Rabs (ax - cx) + Rabs (ay - cy)).
  set (lip := 1 + eAB + eBC + eCA).
  set (g3 := gdbl ax ay bx by_ cx cy / 3).
  set (rad := g3 / lip).
  exists c, rad.
  assert (Hnn : 0 <= eAB /\ 0 <= eBC /\ 0 <= eCA).
  { unfold eAB, eBC, eCA.
    repeat split; apply Rplus_le_le_0_compat; apply Rabs_pos. }
  assert (Hlip : 0 < lip) by (unfold lip; lra).
  assert (Hg3 : 0 < g3) by (unfold g3; lra).
  assert (Hrad : 0 < rad).
  { unfold rad. apply Rdiv_lt_0_compat; assumption. }
  split; [exact Hrad|].
  intros q Hq.
  destruct (gs_centroid ax ay bx by_ cx cy) as [HcA [HcB HcC]].
  assert (Hdx : Rabs (px q - px c) <= dist c q).
  { rewrite (Rabs_minus_sym (px q) (px c)). apply abs_coord_le_dist_x. }
  assert (Hdy : Rabs (py q - py c) <= dist c q).
  { rewrite (Rabs_minus_sym (py q) (py c)). apply abs_coord_le_dist_y. }
  assert (Hdle : dist c q <= rad) by (apply Rlt_le; exact Hq).
  assert (HeAB : eAB < lip) by (unfold lip; lra).
  assert (HeBC : eBC < lip) by (unfold lip; lra).
  assert (HeCA : eCA < lip) by (unfold lip; lra).
  assert (HA : 0 < gsA ax ay bx by_ q).
  { apply (slack_above_lip (gsA ax ay bx by_ q) (gsA ax ay bx by_ c)
             eAB (dist c q) rad).
    - rewrite gsA_delta. unfold eAB. apply Rabs_lin_bound; assumption.
    - exact Hdle.
    - exact (proj1 Hnn).
    - unfold c, g3, rad. rewrite HcA.
      apply edge_rad_lt_slack; try assumption.
      exact (proj1 Hnn). }
  assert (HB : 0 < gsB bx by_ cx cy q).
  { apply (slack_above_lip (gsB bx by_ cx cy q) (gsB bx by_ cx cy c)
             eBC (dist c q) rad).
    - rewrite gsB_delta. unfold eBC. apply Rabs_lin_bound; assumption.
    - exact Hdle.
    - exact (proj1 (proj2 Hnn)).
    - unfold c, g3, rad. rewrite HcB.
      apply edge_rad_lt_slack; try assumption.
      exact (proj1 (proj2 Hnn)). }
  assert (HC : 0 < gsC ax ay cx cy q).
  { apply (slack_above_lip (gsC ax ay cx cy q) (gsC ax ay cx cy c)
             eCA (dist c q) rad).
    - rewrite gsC_delta. unfold eCA. apply Rabs_lin_bound; assumption.
    - exact Hdle.
    - exact (proj2 (proj2 Hnn)).
    - unfold c, g3, rad. rewrite HcC.
      apply edge_rad_lt_slack; try assumption.
      exact (proj2 (proj2 Hnn)). }
  apply gtri_pos_iff. repeat split; assumption.
Qed.

Lemma touch_ib_empty_general :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    triangles_touch_on_shared_edge
      (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
      (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) ->
    gtri_cell_empty (fun p =>
      0 < gtri ax ay bx by_ cx cy p /\
      gtri dx dy ex ey fx fy p = 0).
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Htouch p [HA HB0].
  pose proof (touch_int_ext_exclusion
                ax ay bx by_ cx cy dx dy ex ey fx fy p Htouch HA) as Hlt.
  lra.
Qed.

Lemma touch_bi_empty_general :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    triangles_touch_on_shared_edge
      (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
      (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) ->
    gtri_cell_empty (fun p =>
      gtri ax ay bx by_ cx cy p = 0 /\
      0 < gtri dx dy ex ey fx fy p).
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Htouch p [HA0 HB].
  pose proof (triangles_touch_on_shared_edge_sym
                (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
                (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) Htouch)
    as Hsym.
  pose proof (touch_int_ext_exclusion
                dx dy ex ey fx fy ax ay bx by_ cx cy p Hsym HB) as Hlt.
  lra.
Qed.

Lemma touch_ie_dim2_general :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    triangles_touch_on_shared_edge
      (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
      (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) ->
    0 < gdbl ax ay bx by_ cx cy ->
    gtri_cell_dim2 (fun p =>
      0 < gtri ax ay bx by_ cx cy p /\
      gtri dx dy ex ey fx fy p < 0).
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Htouch Hccw.
  destruct (ccw_triangle_interior_disk ax ay bx by_ cx cy Hccw)
    as (c & r & Hr & Hin).
  exists c, r. split; [exact Hr|].
  intros q Hq.
  split.
  - apply Hin. exact Hq.
  - apply (touch_int_ext_exclusion
             ax ay bx by_ cx cy dx dy ex ey fx fy q Htouch).
    apply Hin. exact Hq.
Qed.

Lemma touch_ei_dim2_general :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    triangles_touch_on_shared_edge
      (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
      (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) ->
    0 < gdbl dx dy ex ey fx fy ->
    gtri_cell_dim2 (fun p =>
      gtri ax ay bx by_ cx cy p < 0 /\
      0 < gtri dx dy ex ey fx fy p).
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Htouch HccwB.
  pose proof (triangles_touch_on_shared_edge_sym
                (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
                (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) Htouch)
    as Hsym.
  destruct (touch_ie_dim2_general dx dy ex ey fx fy ax ay bx by_ cx cy
              Hsym HccwB)
    as (c & r & Hr & Hin).
  exists c, r. split; [exact Hr|].
  intros q Hq.
  destruct (Hin q Hq) as [Hb Ha].
  split; assumption.
Qed.

Lemma touch_edge_six_cells_general :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    triangles_touch_on_shared_edge
      (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
      (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) ->
    0 < gdbl ax ay bx by_ cx cy ->
    0 < gdbl dx dy ex ey fx fy ->
    gtri_cell_empty (fun p =>
      0 < gtri ax ay bx by_ cx cy p /\ gtri dx dy ex ey fx fy p = 0) /\
    gtri_cell_empty (fun p =>
      gtri ax ay bx by_ cx cy p = 0 /\ 0 < gtri dx dy ex ey fx fy p) /\
    gtri_cell_dim2 (fun p =>
      0 < gtri ax ay bx by_ cx cy p /\ gtri dx dy ex ey fx fy p < 0) /\
    gtri_cell_dim2 (fun p =>
      gtri ax ay bx by_ cx cy p < 0 /\ 0 < gtri dx dy ex ey fx fy p) /\
    gtri_cell_dim1 (fun p =>
      gtri ax ay bx by_ cx cy p = 0 /\ gtri dx dy ex ey fx fy p < 0) /\
    gtri_cell_dim1 (fun p =>
      gtri ax ay bx by_ cx cy p < 0 /\ gtri dx dy ex ey fx fy p = 0).
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Htouch HA HB.
  split; [| split; [| split; [| split; [| split]]]].
  - apply touch_ib_empty_general. exact Htouch.
  - apply touch_bi_empty_general. exact Htouch.
  - apply touch_ie_dim2_general; assumption.
  - apply touch_ei_dim2_general; assumption.
  - apply touch_be_dim1_general; assumption.
  - apply touch_eb_dim1_general; assumption.
Qed.

(* Frozen pair of RelateNGTouchEdgeCells is one instance, not the claim. *)
Lemma touch_edge_witness_ccw :
  triangles_touch_on_shared_edge
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint 1 1) (mkPoint 0 1) /\
  0 < gdbl 0 0 1 0 0 1 /\
  0 < gdbl 1 0 1 1 0 1.
Proof.
  split; [exact ex_triangles_touch_on_shared_edge|].
  unfold gdbl. split; lra.
Qed.

Lemma touch_edge_witness_six_cells :
  gtri_cell_empty (fun p =>
    0 < gtri 0 0 1 0 0 1 p /\ gtri 1 0 1 1 0 1 p = 0) /\
  gtri_cell_empty (fun p =>
    gtri 0 0 1 0 0 1 p = 0 /\ 0 < gtri 1 0 1 1 0 1 p) /\
  gtri_cell_dim2 (fun p =>
    0 < gtri 0 0 1 0 0 1 p /\ gtri 1 0 1 1 0 1 p < 0) /\
  gtri_cell_dim2 (fun p =>
    gtri 0 0 1 0 0 1 p < 0 /\ 0 < gtri 1 0 1 1 0 1 p) /\
  gtri_cell_dim1 (fun p =>
    gtri 0 0 1 0 0 1 p = 0 /\ gtri 1 0 1 1 0 1 p < 0) /\
  gtri_cell_dim1 (fun p =>
    gtri 0 0 1 0 0 1 p < 0 /\ gtri 1 0 1 1 0 1 p = 0).
Proof.
  destruct touch_edge_witness_ccw as [Ht [HA HB]].
  apply (touch_edge_six_cells_general
           0 0 1 0 0 1 1 0 1 1 0 1 Ht HA HB).
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stop.  LEFT is the six forall cells.  RIGHT would   *)
(* be a point on the positive side of the canonical reversed edge whose gtri  *)
(* against B is not strictly negative (the half-plane lemma failing).         *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0003-touch-edge-cells-general","topic":"relate","lemma":"ticket_0003_touch_edge_cells_general_qed_or_qex","title":"ADR-0003 shared-edge touch: forall CCW pair, IB=BI=F, IE=EI=dim2, BE=EB=dim1 at 0<gtri (QED) or the canonical reverse-edge half-plane fails (QEX); discharged QED; no ring_complement guard; frozen pair is an instance","file":"theories/RelateNGTouchEdgeCellsGeneral.v","witness":"0003-touch-edge-cells-general","board":"ADR-0003"} *)

Theorem ticket_0003_touch_edge_cells_general_qed_or_qex :
  (forall ax ay bx by_ cx cy dx dy ex ey fx fy,
     triangles_touch_on_shared_edge
       (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
       (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) ->
     0 < gdbl ax ay bx by_ cx cy ->
     0 < gdbl dx dy ex ey fx fy ->
     gtri_cell_empty (fun p =>
       0 < gtri ax ay bx by_ cx cy p /\ gtri dx dy ex ey fx fy p = 0) /\
     gtri_cell_empty (fun p =>
       gtri ax ay bx by_ cx cy p = 0 /\ 0 < gtri dx dy ex ey fx fy p) /\
     gtri_cell_dim2 (fun p =>
       0 < gtri ax ay bx by_ cx cy p /\ gtri dx dy ex ey fx fy p < 0) /\
     gtri_cell_dim2 (fun p =>
       gtri ax ay bx by_ cx cy p < 0 /\ 0 < gtri dx dy ex ey fx fy p) /\
     gtri_cell_dim1 (fun p =>
       gtri ax ay bx by_ cx cy p = 0 /\ gtri dx dy ex ey fx fy p < 0) /\
     gtri_cell_dim1 (fun p =>
       gtri ax ay bx by_ cx cy p < 0 /\ gtri dx dy ex ey fx fy p = 0))
  \/
  (exists ax ay bx by_ ox oy p,
     0 < gsA ax ay bx by_ p /\
     ~ gtri bx by_ ax ay ox oy p < 0).
Proof.
  left.
  exact touch_edge_six_cells_general.
Qed.

Print Assumptions triangles_touch_on_shared_edge_sym.
Print Assumptions touch_halfplane_ext.
Print Assumptions touch_nonshared_edge_ext.
Print Assumptions touch_ib_empty_general.
Print Assumptions touch_bi_empty_general.
Print Assumptions touch_ie_dim2_general.
Print Assumptions touch_ei_dim2_general.
Print Assumptions touch_be_dim1_general.
Print Assumptions touch_eb_dim1_general.
Print Assumptions touch_edge_six_cells_general.
Print Assumptions touch_edge_witness_six_cells.
Print Assumptions ticket_0003_touch_edge_cells_general_qed_or_qex.
