(* ============================================================================
   NetTopologySuite.Proofs.GeneralTriangleSeparation
   ----------------------------------------------------------------------------
   Special-case JCT: the separation half for an ARBITRARY (CCW) triangle.

   Parametric over three vertices A=(ax,ay), B=(bx,by_), C=(cx,cy) in
   counter-clockwise order (positive signed area `gdbl`).  Discharges the
   bounded-component obligation of `parity_characterises_interior_cont` for the
   triangle interior, via the IVT engine `SeparationField.separation_via_field`:

     gtri_interior_is_geometric :
       0 < gtri pt  ->  geometric_interior_cont pt gtri_ring

   where the separating field is the min of the three inward signed areas
     gsA pt = cross(B-A, P-A),  gsB pt = cross(C-B, P-B),  gsC pt = cross(A-C, P-C)
     gtri pt = Rmin (Rmin (gsA pt) (gsB pt)) (gsC pt)
   (> 0 strictly inside, = 0 exactly on the three edges, < 0 outside).

   The proofs lean on three `ring` identities -- the area sum
   `gsA+gsB+gsC = gdbl` and the two barycentric position identities
   `px*gdbl = gsB*ax + gsC*bx + gsA*cx` (and the y analogue) -- which turn the
   bound (interior point lies in the vertex bounding box) and the boundary
   parametrisation (edge parameter = a signed-area ratio) into `nra`/`field`.
   No edge-slope case analysis, so vertical/horizontal edges are not special.

   This is the SEPARATION half; the ray-parity half over three sloped edges
   (with the `ray_avoids_vertices` grazing guard) is a separate slice.

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (claude-opus-4-8)
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From Stdlib Require Import Ranalysis.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam.
From NTS.Proofs Require Import RectangleJCT RectangleSeparation SeparationField.
Import ListNotations.

Local Open Scope R_scope.

(* Generic helpers: a convex combination lies between the min and max value. *)
Lemma convex3_le : forall w1 w2 w3 v1 v2 v3 d X V,
  0 < w1 -> 0 < w2 -> 0 < w3 -> w1 + w2 + w3 = d -> 0 < d ->
  X * d = w1 * v1 + w2 * v2 + w3 * v3 ->
  v1 <= V -> v2 <= V -> v3 <= V -> X <= V.
Proof. intros; nra. Qed.

Lemma convex3_ge : forall w1 w2 w3 v1 v2 v3 d X V,
  0 < w1 -> 0 < w2 -> 0 < w3 -> w1 + w2 + w3 = d -> 0 < d ->
  X * d = w1 * v1 + w2 * v2 + w3 * v3 ->
  V <= v1 -> V <= v2 -> V <= v3 -> V <= X.
Proof. intros; nra. Qed.

(* Continuity of an affine map k1*(py - c1) - k2*(px - c2) along a path. *)
Lemma cont_affine2 : forall k1 c1 k2 c2 (g : R -> Point) t,
  continuity_pt (fun s => px (g s)) t ->
  continuity_pt (fun s => py (g s)) t ->
  continuity_pt (fun s => k1 * (py (g s) - c1) - k2 * (px (g s) - c2)) t.
Proof.
  intros k1 c1 k2 c2 g t Hu Hv.
  apply continuity_pt_minus.
  - apply continuity_pt_scal. apply continuity_pt_minus;
      [ exact Hv | apply continuity_pt_const; intros ? ?; reflexivity ].
  - apply continuity_pt_scal. apply continuity_pt_minus;
      [ exact Hu | apply continuity_pt_const; intros ? ?; reflexivity ].
Qed.

Section GeneralTriangle.

Variables ax ay bx by_ cx cy : R.

(* Twice the signed area; CCW means it is positive. *)
Definition gdbl : R := (bx - ax) * (cy - ay) - (by_ - ay) * (cx - ax).
Hypothesis Hccw : 0 < gdbl.

(* The three inward signed areas (cross products). *)
Definition gsA (pt : Point) : R := (bx - ax) * (py pt - ay) - (by_ - ay) * (px pt - ax).
Definition gsB (pt : Point) : R := (cx - bx) * (py pt - by_) - (cy - by_) * (px pt - bx).
Definition gsC (pt : Point) : R := (ax - cx) * (py pt - cy) - (ay - cy) * (px pt - cx).

Definition gtri (pt : Point) : R := Rmin (Rmin (gsA pt) (gsB pt)) (gsC pt).

Definition gtri_ring : Ring :=
  [ mkPoint ax ay ; mkPoint bx by_ ; mkPoint cx cy ; mkPoint ax ay ].

(* The three `ring` identities. *)
Lemma g_sum : forall pt, gsA pt + gsB pt + gsC pt = gdbl.
Proof. intros pt; unfold gsA, gsB, gsC, gdbl; ring. Qed.

Lemma g_baryx : forall pt, px pt * gdbl = gsB pt * ax + gsC pt * bx + gsA pt * cx.
Proof. intros pt; unfold gsA, gsB, gsC, gdbl; ring. Qed.

Lemma g_baryy : forall pt, py pt * gdbl = gsB pt * ay + gsC pt * by_ + gsA pt * cy.
Proof. intros pt; unfold gsA, gsB, gsC, gdbl; ring. Qed.

(* Strict positivity = strictly inside all three half-planes. *)
Lemma gtri_pos_iff : forall pt,
  0 < gtri pt <-> (0 < gsA pt /\ 0 < gsB pt /\ 0 < gsC pt).
Proof. intros pt; unfold gtri; rewrite !Rmin_pos_iff; tauto. Qed.

Lemma ring_edges_gtri :
  ring_edges gtri_ring =
    [ (mkPoint ax ay, mkPoint bx by_)
    ; (mkPoint bx by_, mkPoint cx cy)
    ; (mkPoint cx cy, mkPoint ax ay) ].
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Continuity of gtri along a path.                                            *)
(* -------------------------------------------------------------------------- *)

Lemma continuity_pt_gtri_path : forall (g : R -> Point) t,
  continuity_pt (fun s => px (g s)) t ->
  continuity_pt (fun s => py (g s)) t ->
  continuity_pt (fun s => gtri (g s)) t.
Proof.
  intros g t Hu Hv. unfold gtri, gsA, gsB, gsC.
  apply continuity_pt_Rmin; [ apply continuity_pt_Rmin | ]; apply cont_affine2; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* A strict-interior point lies in the vertex bounding box -> radius bound.     *)
(* -------------------------------------------------------------------------- *)

Definition gVmax := Rmax ax (Rmax bx cx).
Definition gVmin := Rmin ax (Rmin bx cx).
Definition gHmax := Rmax ay (Rmax by_ cy).
Definition gHmin := Rmin ay (Rmin by_ cy).

Lemma gtri_x_range : forall pt,
  0 < gtri pt -> gVmin <= px pt <= gVmax.
Proof.
  intros pt Hp. apply gtri_pos_iff in Hp. destruct Hp as [HA [HB HC]].
  pose proof (g_sum pt) as Hsum. pose proof (g_baryx pt) as Hbx.
  unfold gVmin, gVmax.
  assert (axM : ax <= Rmax ax (Rmax bx cx)) by apply Rmax_l.
  assert (bxM : bx <= Rmax ax (Rmax bx cx))
    by (eapply Rle_trans; [ apply Rmax_l | apply Rmax_r ]).
  assert (cxM : cx <= Rmax ax (Rmax bx cx))
    by (eapply Rle_trans; [ apply Rmax_r | apply Rmax_r ]).
  assert (Max : ax >= Rmin ax (Rmin bx cx)) by (apply Rle_ge; apply Rmin_l).
  assert (Mbx : bx >= Rmin ax (Rmin bx cx))
    by (apply Rle_ge; eapply Rle_trans; [ apply Rmin_r | apply Rmin_l ]).
  assert (Mcx : cx >= Rmin ax (Rmin bx cx))
    by (apply Rle_ge; eapply Rle_trans; [ apply Rmin_r | apply Rmin_r ]).
  split.
  - apply (convex3_ge (gsB pt) (gsC pt) (gsA pt) ax bx cx gdbl (px pt));
      try assumption; try lra.
  - apply (convex3_le (gsB pt) (gsC pt) (gsA pt) ax bx cx gdbl (px pt));
      try assumption; try lra.
Qed.

Lemma gtri_y_range : forall pt,
  0 < gtri pt -> gHmin <= py pt <= gHmax.
Proof.
  intros pt Hp. apply gtri_pos_iff in Hp. destruct Hp as [HA [HB HC]].
  pose proof (g_sum pt) as Hsum. pose proof (g_baryy pt) as Hby.
  unfold gHmin, gHmax.
  assert (ayM : ay <= Rmax ay (Rmax by_ cy)) by apply Rmax_l.
  assert (byM : by_ <= Rmax ay (Rmax by_ cy))
    by (eapply Rle_trans; [ apply Rmax_l | apply Rmax_r ]).
  assert (cyM : cy <= Rmax ay (Rmax by_ cy))
    by (eapply Rle_trans; [ apply Rmax_r | apply Rmax_r ]).
  assert (May : ay >= Rmin ay (Rmin by_ cy)) by (apply Rle_ge; apply Rmin_l).
  assert (Mby : by_ >= Rmin ay (Rmin by_ cy))
    by (apply Rle_ge; eapply Rle_trans; [ apply Rmin_r | apply Rmin_l ]).
  assert (Mcy : cy >= Rmin ay (Rmin by_ cy))
    by (apply Rle_ge; eapply Rle_trans; [ apply Rmin_r | apply Rmin_r ]).
  split.
  - apply (convex3_ge (gsB pt) (gsC pt) (gsA pt) ay by_ cy gdbl (py pt));
      try assumption; try lra.
  - apply (convex3_le (gsB pt) (gsC pt) (gsA pt) ay by_ cy gdbl (py pt));
      try assumption; try lra.
Qed.

Definition gM : R :=
  sqrt (gVmin * gVmin + gVmax * gVmax + (gHmin * gHmin + gHmax * gHmax) + 1).

Lemma gM_pos : 0 < gM.
Proof. unfold gM. apply sqrt_lt_R0; nra. Qed.

Lemma gtri_bound : forall pt,
  0 < gtri pt -> px pt * px pt + py pt * py pt <= gM * gM.
Proof.
  intros pt Hp.
  pose proof (gtri_x_range pt Hp) as [Hx1 Hx2].
  pose proof (gtri_y_range pt Hp) as [Hy1 Hy2].
  pose proof (sq_le_max_endpoints (px pt) gVmin gVmax (conj Hx1 Hx2)) as Hxsq.
  pose proof (sq_le_max_endpoints (py pt) gHmin gHmax (conj Hy1 Hy2)) as Hysq.
  assert (Hsx : Rmax (gVmin * gVmin) (gVmax * gVmax) <= gVmin * gVmin + gVmax * gVmax)
    by (apply Rmax_lub; nra).
  assert (Hsy : Rmax (gHmin * gHmin) (gHmax * gHmax) <= gHmin * gHmin + gHmax * gHmax)
    by (apply Rmax_lub; nra).
  assert (HMM : gM * gM = gVmin * gVmin + gVmax * gVmax + (gHmin * gHmin + gHmax * gHmax) + 1)
    by (unfold gM; apply sqrt_sqrt; nra).
  rewrite HMM. nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Boundary: gtri = 0 lands on one of the three edges (ring_image).            *)
(* The edge parameter is a signed-area ratio (from the barycentric identity).  *)
(* -------------------------------------------------------------------------- *)

Lemma gtri_zero_imp_ring_image : forall pt,
  gtri pt = 0 -> ring_image gtri_ring pt.
Proof.
  intros pt H. unfold gtri in H.
  destruct (Rmin_eq_0_inv _ _ H) as [HAB [HC Hor]].
  assert (HA : 0 <= gsA pt) by (pose proof (Rmin_l (gsA pt) (gsB pt)); lra).
  assert (HB : 0 <= gsB pt) by (pose proof (Rmin_r (gsA pt) (gsB pt)); lra).
  pose proof (g_baryx pt) as Hbx. pose proof (g_baryy pt) as Hby.
  unfold ring_image; rewrite ring_edges_gtri.
  destruct Hor as [Hinner | Hzc].
  - destruct (Rmin_eq_0_inv _ _ Hinner) as [_ [_ [HzA | HzB]]].
    + (* gsA = 0 : edge (A,B), t = gsC / gdbl *)
      assert (HgsB : gsB pt = gdbl - gsC pt) by (pose proof (g_sum pt); lra).
      exists (mkPoint ax ay, mkPoint bx by_), (gsC pt / gdbl).
      pose proof (div_in_01 (gsC pt) gdbl HC ltac:(lra) Hccw) as Ht.
      repeat split; [ cbn [In]; auto | lra | lra
        | cbn [px py fst snd]; apply (Rmult_eq_reg_r gdbl);
            [ rewrite Hbx, HzA, HgsB; field | ]; lra
        | cbn [px py fst snd]; apply (Rmult_eq_reg_r gdbl);
            [ rewrite Hby, HzA, HgsB; field | ]; lra ].
    + (* gsB = 0 : edge (B,C), t = gsA / gdbl *)
      assert (HgsC : gsC pt = gdbl - gsA pt) by (pose proof (g_sum pt); lra).
      exists (mkPoint bx by_, mkPoint cx cy), (gsA pt / gdbl).
      pose proof (div_in_01 (gsA pt) gdbl HA ltac:(lra) Hccw) as Ht.
      repeat split; [ cbn [In]; auto | lra | lra
        | cbn [px py fst snd]; apply (Rmult_eq_reg_r gdbl);
            [ rewrite Hbx, HzB, HgsC; field | ]; lra
        | cbn [px py fst snd]; apply (Rmult_eq_reg_r gdbl);
            [ rewrite Hby, HzB, HgsC; field | ]; lra ].
  - (* gsC = 0 : edge (C,A), t = gsB / gdbl *)
    assert (HgsA : gsA pt = gdbl - gsB pt) by (pose proof (g_sum pt); lra).
    exists (mkPoint cx cy, mkPoint ax ay), (gsB pt / gdbl).
    pose proof (div_in_01 (gsB pt) gdbl HB ltac:(lra) Hccw) as Ht.
    repeat split; [ cbn [In]; auto | lra | lra
      | cbn [px py fst snd]; apply (Rmult_eq_reg_r gdbl);
          [ rewrite Hbx, Hzc, HgsA; field | ]; lra
      | cbn [px py fst snd]; apply (Rmult_eq_reg_r gdbl);
          [ rewrite Hby, Hzc, HgsA; field | ]; lra ].
Qed.

Lemma gtri_nonzero_off_skeleton : forall pt,
  ring_complement gtri_ring pt -> gtri pt <> 0.
Proof.
  intros pt Hc Hz. apply Hc. apply gtri_zero_imp_ring_image; exact Hz.
Qed.

(* -------------------------------------------------------------------------- *)
(* A strict-interior point is off the edge skeleton.                           *)
(* -------------------------------------------------------------------------- *)

Lemma gtri_interior_complement : forall pt,
  0 < gtri pt -> ring_complement gtri_ring pt.
Proof.
  intros pt Hp. apply gtri_pos_iff in Hp. destruct Hp as [HA [HB HC]].
  intros [e [t [Hin [Ht [Hpx Hpy]]]]].
  rewrite ring_edges_gtri in Hin. cbn [In] in Hin.
  destruct Hin as [He | [He | [He | []]]];
    subst e; cbn [px py fst snd] in Hpx, Hpy;
    unfold gsA, gsB, gsC in *; nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Headline: a strict-interior point is a geometric interior point.            *)
(* -------------------------------------------------------------------------- *)

Theorem gtri_interior_is_geometric : forall pt,
  0 < gtri pt -> geometric_interior_cont pt gtri_ring.
Proof.
  intros pt Hp; split.
  - apply gtri_interior_complement; exact Hp.
  - apply (separation_via_field gtri_ring gtri pt gM).
    + intros g Hcx Hcy t. apply continuity_pt_gtri_path; [ apply Hcx | apply Hcy ].
    + intros pt' Hc. apply gtri_nonzero_off_skeleton; exact Hc.
    + exact Hp.
    + apply gM_pos.
    + intros pt' Hp'. apply gtri_bound; exact Hp'.
Qed.

End GeneralTriangle.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions gtri_interior_is_geometric.
