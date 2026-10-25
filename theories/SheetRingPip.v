(* ============================================================================
   NetTopologySuite.Proofs.SheetRingPip
   ----------------------------------------------------------------------------
   Proof half of claimId `sheet-pip-transport` (statements pinned in
   SheetRingPipStmt.v): the canonical half-open east-ray point-in-ring test
   agrees across an invertible affine change of sheet, for seam rings.

   Route.  The test is not transported edge by edge (its ray direction
   changes); it is routed through the topology, which is affine-invariant:
     1. off-ring and bounded-component interior transport for every ring
        (ring_image_act, connected_act, bounded_act, geo_act): f maps edges
        to edges, complement paths to complement paths, and is
        bi-Lipschitz (aff_norm_bound);
     2. on a seam ring, at a point whose ray avoids the vertices, the test
        IS the topological interior (seam_ho: point_in_ring_ho_agrees and
        JCTEscapeDescentHolds.parity_seam_offring_taut);
     3. the vertex guard is removed on both sheets at once: a short move
        p -> p' inside the complement ball (RingComplementOpen) along a
        direction w with w_y <> 0 and (L w)_y <> 0 dodges the finitely many
        vertex heights of both sheets (avoid_list), and the half-open parity
        is constant along complement paths of any closed ring
        (ho_along: JCTSeamAssembly.ho_parity_locally_constant_holds with
        JCTParityTransport.invariant_transport_along_path).
   Tautness, vertex-properness and the point count transport (taut_act,
   core_nodup_act); "no horizontal edge" is assumed on both sheets.

   claimId: sheet-pip-transport.
   3-axiom host. No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List FinFun.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam
  PointInRingCorrect JCTHalfOpenParity JCTParityTransport JCTTautClearance
  JCTRingCycle JCTHugStep JCTSeamAssembly JCTEscapeDescentHolds RingComplementOpen
  ConvexChainSplit ClothoidPlacement ClothoidAffineStmt ClothoidAffine
  ClothoidSheet SheetRingPipStmt.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Affine maps on points, edges and rings.                                *)
(* -------------------------------------------------------------------------- *)

Lemma pip_pt_ext : forall p q : Point, px p = px q -> py p = py q -> p = q.
Proof. intros [x1 y1] [x2 y2] Hx Hy. cbn in *. subst. reflexivity. Qed.

Lemma aff_px : forall f p,
  px (aff_ap f p) = px (af_b f) + (l11 (af_L f) * px p + l12 (af_L f) * py p).
Proof. reflexivity. Qed.

Lemma aff_py : forall f p,
  py (aff_ap f p) = py (af_b f) + (l21 (af_L f) * px p + l22 (af_L f) * py p).
Proof. reflexivity. Qed.

Definition combo (a b : Point) (t : R) : Point :=
  mkPoint ((1 - t) * px a + t * px b) ((1 - t) * py a + t * py b).

Lemma aff_combo : forall f a b t,
  aff_ap f (combo a b t) = combo (aff_ap f a) (aff_ap f b) t.
Proof.
  intros. apply pip_pt_ext; rewrite ?aff_px, ?aff_py; unfold combo; cbn; ring.
Qed.

Lemma pip_ring_edges_map : forall (g : Point -> Point) r,
  ring_edges (map g r) = map (fun e => (g (fst e), g (snd e))) (ring_edges r).
Proof.
  intros g r. induction r as [|a r IH]; [reflexivity|].
  destruct r as [|b r']; [reflexivity|].
  change (map g (a :: b :: r')) with (g a :: map g (b :: r')).
  change (ring_edges (g a :: map g (b :: r')))
    with ((g a, g b) :: ring_edges (map g (b :: r'))).
  rewrite IH. reflexivity.
Qed.

Lemma ring_image_act : forall f r q, lin_det (af_L f) <> 0 ->
  (ring_image (ring_act f r) (aff_ap f q) <-> ring_image r q).
Proof.
  intros f r q HD. unfold ring_image, ring_act. rewrite pip_ring_edges_map. split.
  - intros (e' & t & Hin & Ht & Hx & Hy).
    apply in_map_iff in Hin. destruct Hin as (e & <- & Hin). cbn [fst snd] in Hx, Hy.
    assert (E : aff_ap f q = aff_ap f (combo (fst e) (snd e) t)).
    { rewrite aff_combo. apply pip_pt_ext; unfold combo; cbn [px py]; assumption. }
    apply aff_inj in E; [|exact HD].
    exists e, t. split; [exact Hin|]. split; [exact Ht|].
    rewrite E. unfold combo. cbn. split; reflexivity.
  - intros (e & t & Hin & Ht & Hx & Hy).
    exists (aff_ap f (fst e), aff_ap f (snd e)), t.
    split; [apply in_map_iff; exists e; split; [reflexivity | exact Hin]|].
    split; [exact Ht|]. cbn [fst snd].
    assert (E : q = combo (fst e) (snd e) t)
      by (apply pip_pt_ext; unfold combo; cbn [px py]; assumption).
    rewrite E, aff_combo. unfold combo. cbn. split; reflexivity.
Qed.

Lemma complement_act : forall f r q, lin_det (af_L f) <> 0 ->
  (ring_complement r q <-> ring_complement (ring_act f r) (aff_ap f q)).
Proof.
  intros f r q HD. unfold ring_complement. rewrite ring_image_act by exact HD.
  reflexivity.
Qed.

Lemma lin_det_inv : forall L, lin_det L <> 0 -> lin_det (lin_inv L) <> 0.
Proof.
  intros L H. replace (lin_det (lin_inv L)) with (/ lin_det L).
  - apply Rinv_neq_0_compat. exact H.
  - unfold lin_inv, lin_det in *. cbn. field. exact H.
Qed.

Lemma aff_inv_det : forall f, lin_det (af_L f) <> 0 -> lin_det (af_L (aff_inv f)) <> 0.
Proof. intros f H. cbn. apply lin_det_inv. exact H. Qed.

Lemma aff_inv_ap_l : forall f x, lin_det (af_L f) <> 0 ->
  aff_ap (aff_inv f) (aff_ap f x) = x.
Proof. intros f x H. rewrite <- aff_comp_ap, aff_inv_l by exact H. apply aff_id_ap. Qed.

Lemma aff_inv_ap_r : forall f x, lin_det (af_L f) <> 0 ->
  aff_ap f (aff_ap (aff_inv f) x) = x.
Proof. intros f x H. rewrite <- aff_comp_ap, aff_inv_r by exact H. apply aff_id_ap. Qed.

Lemma ring_act_inv : forall f r, lin_det (af_L f) <> 0 ->
  ring_act (aff_inv f) (ring_act f r) = r.
Proof.
  intros f r H. unfold ring_act. rewrite map_map.
  rewrite <- (map_id r) at 2. apply map_ext. intro x. apply aff_inv_ap_l. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Paths, components, bounds.                                             *)
(* -------------------------------------------------------------------------- *)

Lemma pip_cont_affine2 : forall c a b (f1 f2 : R -> R),
  continuity f1 -> continuity f2 ->
  continuity (fun t => c + (a * f1 t + b * f2 t)).
Proof.
  intros c a b f1 f2 H1 H2 x.
  apply (continuity_pt_plus (fct_cte c) (fun t => a * f1 t + b * f2 t));
    [apply continuity_pt_const; intros u v; reflexivity|].
  apply (continuity_pt_plus (fun t => a * f1 t) (fun t => b * f2 t)).
  - apply (continuity_pt_scal f1 a). apply H1.
  - apply (continuity_pt_scal f2 b). apply H2.
Qed.

Lemma path_act : forall f g, path_continuous g ->
  path_continuous (fun t => aff_ap f (g t)).
Proof.
  intros f g [Hx Hy]. split.
  - apply (pip_cont_affine2 _ _ _ (fun t => px (g t)) (fun t => py (g t)) Hx Hy).
  - apply (pip_cont_affine2 _ _ _ (fun t => px (g t)) (fun t => py (g t)) Hx Hy).
Qed.

Lemma connected_act : forall f r p q, lin_det (af_L f) <> 0 ->
  connected_in_complement_cont r p q ->
  connected_in_complement_cont (ring_act f r) (aff_ap f p) (aff_ap f q).
Proof.
  intros f r p q HD (g & Hg & H0 & H1 & Hc).
  exists (fun t => aff_ap f (g t)). split; [apply path_act; exact Hg|].
  split; [rewrite H0; reflexivity|]. split; [rewrite H1; reflexivity|].
  intros t Ht. apply (proj1 (complement_act f r (g t) HD)). apply Hc. exact Ht.
Qed.

Lemma aff_norm_bound : forall f x,
  px (aff_ap f x) * px (aff_ap f x) + py (aff_ap f x) * py (aff_ap f x)
    <= 2 * (px (af_b f) * px (af_b f) + py (af_b f) * py (af_b f))
       + 2 * (l11 (af_L f) * l11 (af_L f) + l12 (af_L f) * l12 (af_L f)
              + l21 (af_L f) * l21 (af_L f) + l22 (af_L f) * l22 (af_L f))
           * (px x * px x + py x * py x).
Proof.
  intros f x. rewrite aff_px, aff_py.
  set (bx := px (af_b f)). set (by0 := py (af_b f)).
  set (a := l11 (af_L f)). set (b := l12 (af_L f)).
  set (c := l21 (af_L f)). set (d := l22 (af_L f)).
  set (u := px x). set (v := py x).
  pose proof (Rle_0_sqr (bx - (a * u + b * v))) as S1.
  pose proof (Rle_0_sqr (by0 - (c * u + d * v))) as S2.
  pose proof (Rle_0_sqr (a * v - b * u)) as S3.
  pose proof (Rle_0_sqr (c * v - d * u)) as S4.
  unfold Rsqr in *.
  match goal with |- ?L <= ?Rh =>
    assert (E : Rh - L = (bx - (a * u + b * v)) * (bx - (a * u + b * v))
                 + (by0 - (c * u + d * v)) * (by0 - (c * u + d * v))
                 + 2 * ((a * v - b * u) * (a * v - b * u))
                 + 2 * ((c * v - d * u) * (c * v - d * u))) by ring
  end.
  lra.
Qed.

Lemma bounded_act : forall f r p, lin_det (af_L f) <> 0 ->
  in_bounded_component_cont r p ->
  in_bounded_component_cont (ring_act f r) (aff_ap f p).
Proof.
  intros f r p HD (M & HM & Hb).
  set (B := px (af_b f) * px (af_b f) + py (af_b f) * py (af_b f)).
  set (T := l11 (af_L f) * l11 (af_L f) + l12 (af_L f) * l12 (af_L f)
            + l21 (af_L f) * l21 (af_L f) + l22 (af_L f) * l22 (af_L f)).
  set (K := 2 * B + 2 * T * (M * M)).
  assert (HB : 0 <= B) by (unfold B; nra).
  assert (HT : 0 <= T) by (unfold T; nra).
  assert (HK : 0 <= K) by (unfold K; nra).
  pose proof (sqrt_pos K) as Hs. pose proof (sqrt_sqrt K HK) as Hss.
  exists (sqrt K + 1). split; [lra|].
  intros q Hq.
  pose proof (connected_act (aff_inv f) _ _ _ (aff_inv_det f HD) Hq) as Hq'.
  rewrite ring_act_inv, aff_inv_ap_l in Hq' by exact HD.
  pose proof (Hb _ Hq') as Hx.
  set (x := aff_ap (aff_inv f) q) in *.
  assert (Eq : q = aff_ap f x) by (unfold x; rewrite aff_inv_ap_r by exact HD; reflexivity).
  rewrite Eq. eapply Rle_trans; [apply aff_norm_bound|]. fold B T.
  assert (Hm : T * (px x * px x + py x * py x) <= T * (M * M))
    by (apply Rmult_le_compat_l; assumption).
  replace ((sqrt K + 1) * (sqrt K + 1)) with (sqrt K * sqrt K + 2 * sqrt K + 1) by ring.
  rewrite Hss. assert (HKd : K = 2 * B + 2 * T * (M * M)) by reflexivity. lra.
Qed.

Lemma geo_act_fwd : forall f r p, lin_det (af_L f) <> 0 ->
  geometric_interior_cont p r -> geometric_interior_cont (aff_ap f p) (ring_act f r).
Proof.
  intros f r p HD [Hc Hb]. split.
  - apply (proj1 (complement_act f r p HD)). exact Hc.
  - apply bounded_act; assumption.
Qed.

Theorem geo_act : forall f r p, lin_det (af_L f) <> 0 ->
  (geometric_interior_cont p r <-> geometric_interior_cont (aff_ap f p) (ring_act f r)).
Proof.
  intros f r p HD. split; [apply geo_act_fwd; exact HD|].
  intro H. apply (geo_act_fwd (aff_inv f)) in H; [|apply aff_inv_det; exact HD].
  rewrite ring_act_inv, aff_inv_ap_l in H by exact HD. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The seam conditions that transport.                                    *)
(* -------------------------------------------------------------------------- *)

Lemma taut_act : forall f r, lin_det (af_L f) <> 0 ->
  ring_taut r -> ring_taut (ring_act f r).
Proof.
  intros f r HD Ht e' g' He' Hg' t s Ht01 Hs01 Hx Hy.
  unfold ring_act in He', Hg'. rewrite pip_ring_edges_map in He', Hg'.
  apply in_map_iff in He'. destruct He' as (e & <- & He).
  apply in_map_iff in Hg'. destruct Hg' as (g & <- & Hg).
  cbn [fst snd] in Hx, Hy.
  assert (E : aff_ap f (combo (fst e) (snd e) t) = aff_ap f (combo (fst g) (snd g) s)).
  { rewrite !aff_combo. apply pip_pt_ext; unfold combo; cbn [px py]; assumption. }
  apply aff_inj in E; [|exact HD].
  assert (Ex := f_equal px E). assert (Ey := f_equal py E).
  unfold combo in Ex, Ey. cbn [px py] in Ex, Ey.
  destruct (Ht e g He Hg t s Ht01 Hs01 Ex Ey) as [H | [H1 H2]].
  - left. exact H.
  - right. cbn [fst snd]. rewrite H1, H2. split; reflexivity.
Qed.

Lemma core_nodup_act : forall f r, lin_det (af_L f) <> 0 ->
  ring_core_nodup r -> ring_core_nodup (ring_act f r).
Proof.
  intros f r HD (p & ps & Hr & Hnd).
  exists (aff_ap f p), (map (aff_ap f) ps). split.
  - rewrite Hr. unfold ring_act. rewrite map_cons, map_app. reflexivity.
  - change (aff_ap f p :: map (aff_ap f) ps) with (map (aff_ap f) (p :: ps)).
    apply Injective_map_NoDup; [|exact Hnd].
    intros x y E. exact (aff_inj f x y HD E).
Qed.

Lemma min_points_act : forall f r,
  ring_has_minimum_points r -> ring_has_minimum_points (ring_act f r).
Proof. intros f r H. unfold ring_has_minimum_points, ring_act in *. rewrite length_map. exact H. Qed.

Theorem sheet_pip_supporting : SheetRingPipStmt.supporting.
Proof.
  split; [exact complement_act|]. split; [exact geo_act|].
  intros f r HD. split; [apply taut_act; exact HD|].
  split; [apply core_nodup_act; exact HD | apply min_points_act].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The seam on one sheet, and parity along complement paths.              *)
(* -------------------------------------------------------------------------- *)

Lemma seam_ho : forall r x, seam_ring r -> ring_complement r x ->
  ray_avoids_vertices x r ->
  (point_in_ring_ho x r <-> geometric_interior_cont x r).
Proof.
  intros r x (Ht & Hnd & Hmin & Hnoh) Hc Hrav.
  rewrite (point_in_ring_ho_agrees x r Hrav).
  symmetry. apply (parity_seam_offring_taut r x Ht Hnd Hnoh).
  - apply ring_taut_implies_simple. exact Ht.
  - apply ring_core_nodup_closed. exact Hnd.
  - exact Hmin.
  - exact Hc.
  - unfold no_horizontal_edge_at. apply Forall_forall. exact Hnoh.
  - exact Hrav.
Qed.

Lemma ho_along : forall r (g : R -> Point), ring_closed r ->
  path_continuous g -> (forall t, 0 <= t <= 1 -> ring_complement r (g t)) ->
  (point_in_ring_ho (g 0) r <-> point_in_ring_ho (g 1) r).
Proof.
  intros r g Hcl Hg Hc.
  apply (invariant_transport_along_path (fun q => point_in_ring_ho q r) g).
  - intro q. apply point_in_ring_ho_dec.
  - exact (ho_parity_locally_constant_holds r Hcl g Hg Hc).
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Dodging finitely many heights.                                         *)
(* -------------------------------------------------------------------------- *)

Lemma avoid_list : forall (l : list R) d, 0 < d ->
  exists e, 0 < e < d /\ forall x, In x l -> x <> e.
Proof.
  induction l as [|x l IH]; intros d Hd.
  - exists (d / 2). split; [lra | intros x []].
  - destruct (IH d Hd) as (e0 & He0 & Hav0).
    destruct (Req_EM_T x e0) as [Ex | Nx].
    + destruct (IH e0 (proj1 He0)) as (e1 & He1 & Hav1).
      exists e1. split; [lra|]. intros y [<- | Hy]; [lra | exact (Hav1 y Hy)].
    + exists e0. split; [exact He0|]. intros y [<- | Hy]; [exact Nx | exact (Hav0 y Hy)].
Qed.

Lemma seg_path_cont : forall p wx e,
  path_continuous (fun t => mkPoint (px p + t * (e * wx)) (py p + t * e)).
Proof.
  intros p wx e. split; cbn [px py].
  - apply derivable_continuous. reg.
  - apply derivable_continuous. reg.
Qed.

(* A point near p, joined to p in the complement, whose ray avoids the
   vertices on both sheets. *)
Lemma guard_move : forall f r p, lin_det (af_L f) <> 0 -> ring_complement r p ->
  exists g : R -> Point,
    path_continuous g /\ g 0 = p /\
    (forall t, 0 <= t <= 1 -> ring_complement r (g t)) /\
    ray_avoids_vertices (g 1) r /\
    ray_avoids_vertices (aff_ap f (g 1)) (ring_act f r).
Proof.
  intros f r p HD Hc.
  destruct (ring_complement_open r p Hc) as (dl & Hdl & Hball).
  set (wx := if Req_EM_T (l22 (af_L f)) 0 then 1 else 0).
  set (cy := l21 (af_L f) * wx + l22 (af_L f)).
  assert (Hcy : cy <> 0).
  { unfold cy, wx. destruct (Req_EM_T (l22 (af_L f)) 0) as [E|N].
    - rewrite E. intro Z. apply HD. unfold lin_det. rewrite E.
      replace (l21 (af_L f)) with 0 by lra. ring.
    - replace (l21 (af_L f) * 0 + l22 (af_L f)) with (l22 (af_L f)) by ring. exact N. }
  assert (Hwx : 0 <= wx <= 1)
    by (unfold wx; destruct (Req_EM_T (l22 (af_L f)) 0); lra).
  set (bad := map (fun v => py v - py p) r
              ++ map (fun v => (py (aff_ap f v) - py (aff_ap f p)) / cy) r).
  destruct (avoid_list bad (dl / 2) ltac:(lra)) as (e & He & Hav).
  exists (fun t => mkPoint (px p + t * (e * wx)) (py p + t * e)).
  split; [apply seg_path_cont|].
  split; [apply pip_pt_ext; cbn; ring|].
  split; [|split].
  - intros t Ht. apply Hball. unfold dist, dist_sq. cbn [px py].
    replace ((px p - (px p + t * (e * wx))) * (px p - (px p + t * (e * wx)))
             + (py p - (py p + t * e)) * (py p - (py p + t * e)))
      with ((t * e) * (t * e) * (wx * wx + 1)) by ring.
    assert (H1 : 0 <= (t * e) * (t * e) * (wx * wx + 1) < dl * dl).
    { split; [apply Rmult_le_pos; [apply Rle_0_sqr | nra]|].
      assert (Hu : 0 <= t * e <= e) by nra.
      assert (Hu2 : (t * e) * (t * e) <= e * e)
        by (apply Rmult_le_compat; lra).
      assert (Hw2 : wx * wx + 1 <= 2) by nra.
      assert (He2 : e * e < (dl / 2) * (dl / 2)) by (apply Rmult_le_0_lt_compat; lra).
      assert (Hp : (t * e) * (t * e) * (wx * wx + 1) <= (t * e) * (t * e) * 2)
        by (apply Rmult_le_compat_l; [apply Rle_0_sqr | exact Hw2]).
      replace ((dl / 2) * (dl / 2)) with ((dl * dl) / 4) in He2 by field.
      assert (Hd2 : 0 < dl * dl) by nra.
      set (A := (t * e) * (t * e)) in *. set (W := wx * wx + 1) in *.
      set (E2 := e * e) in *. set (D2 := dl * dl) in *.
      lra. }
    rewrite <- (sqrt_square dl) by lra.
    apply sqrt_lt_1_alt. exact H1.
  - intros v Hv [Hy _]. cbn [px py] in Hy.
    apply (Hav (py v - py p)); [apply in_or_app; left; apply in_map_iff; exists v; split; [reflexivity | exact Hv] | lra].
  - intros v' Hv' [Hy _].
    unfold ring_act in Hv'. apply in_map_iff in Hv'. destruct Hv' as (v & <- & Hv).
    apply (Hav ((py (aff_ap f v) - py (aff_ap f p)) / cy)).
    + apply in_or_app; right. apply in_map_iff. exists v. split; [reflexivity | exact Hv].
    + rewrite Hy. rewrite !aff_py. cbn [px py]. unfold cy. field. exact Hcy.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  The claim.                                                             *)
(* -------------------------------------------------------------------------- *)

Theorem sheet_pip_claim : SheetRingPipStmt.claim.
Proof.
  intros f r p HD Hs Hnoh' Hc.
  pose proof Hs as (Ht & Hnd & Hmin & Hnoh).
  assert (Hs' : seam_ring (ring_act f r)).
  { split; [apply taut_act; assumption|]. split; [apply core_nodup_act; assumption|].
    split; [apply min_points_act; exact Hmin | exact Hnoh']. }
  assert (Hcl : ring_closed r) by (apply ring_core_nodup_closed; exact Hnd).
  assert (Hcl' : ring_closed (ring_act f r))
    by (apply ring_core_nodup_closed; apply core_nodup_act; assumption).
  destruct (guard_move f r p HD Hc) as (g & Hg & H0 & Hgc & Hrav & Hrav').
  pose proof (ho_along r g Hcl Hg Hgc) as Hr.
  pose proof (ho_along (ring_act f r) (fun t => aff_ap f (g t)) Hcl' (path_act f g Hg)
                (fun t Ht => proj1 (complement_act f r (g t) HD) (Hgc t Ht))) as Hr'.
  cbv beta in Hr'. rewrite H0 in Hr, Hr'.
  assert (Hc1 : ring_complement r (g 1)) by (apply Hgc; lra).
  rewrite Hr, Hr'.
  rewrite (seam_ho r (g 1) Hs Hc1 Hrav).
  rewrite (seam_ho (ring_act f r) (aff_ap f (g 1)) Hs'
             (proj1 (complement_act f r (g 1) HD) Hc1) Hrav').
  apply geo_act. exact HD.
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  Witness: the corpus diamond under the vertical shear.                  *)
(* -------------------------------------------------------------------------- *)

Lemma diamond_edges_eq : ring_edges diamond_ring =
  [ (mkPoint 0 (-2), mkPoint 2 0); (mkPoint 2 0, mkPoint 0 2);
    (mkPoint 0 2, mkPoint (-2) 0); (mkPoint (-2) 0, mkPoint 0 (-2)) ].
Proof. reflexivity. Qed.

Lemma diamond_taut : ring_taut diamond_ring.
Proof.
  unfold ring_taut. rewrite diamond_edges_eq.
  intros e g He Hg t s Ht Hs Hx Hy. cbn [In] in He, Hg.
  destruct He as [<- | [<- | [<- | [<- | []]]]];
  destruct Hg as [<- | [<- | [<- | [<- | []]]]];
    cbn [fst snd px py] in Hx, Hy;
    first
      [ right; split; reflexivity
      | left; left; lra
      | left; right; lra
      | exfalso; lra ].
Qed.

Lemma diamond_core_nodup : ring_core_nodup diamond_ring.
Proof.
  exists (mkPoint 0 (-2)), [mkPoint 2 0; mkPoint 0 2; mkPoint (-2) 0].
  split; [reflexivity|].
  repeat constructor; cbn [In];
    repeat (intros [E | H]; [injection E; lra | revert H]); intros [].
Qed.

Lemma diamond_seam : seam_ring diamond_ring.
Proof.
  split; [exact diamond_taut|]. split; [exact diamond_core_nodup|].
  split; [unfold ring_has_minimum_points, diamond_ring; cbn; repeat constructor|].
  unfold no_horizontal_edges. rewrite diamond_edges_eq.
  intros g Hg. cbn [In] in Hg.
  destruct Hg as [<- | [<- | [<- | [<- | []]]]]; cbn; lra.
Qed.

Lemma diamond_vshear_noh : no_horizontal_edges (ring_act vshear_half diamond_ring).
Proof.
  unfold no_horizontal_edges, ring_act. rewrite pip_ring_edges_map, diamond_edges_eq.
  intros g Hg. cbn [map In] in Hg.
  destruct Hg as [<- | [<- | [<- | [<- | []]]]];
    cbn [fst snd]; rewrite !aff_py; cbn; lra.
Qed.

Lemma diamond_origin_off : ring_complement diamond_ring (mkPoint 0 0).
Proof.
  unfold ring_complement, ring_image. rewrite diamond_edges_eq.
  intros (e & t & He & Ht & Hx & Hy). cbn [In] in He.
  destruct He as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd px py] in Hx, Hy; lra.
Qed.

Lemma diamond_origin_in : point_in_ring_ho (mkPoint 0 0) diamond_ring.
Proof.
  unfold point_in_ring_ho. rewrite diamond_edges_eq.
  apply hpo_skip; [unfold edge_crosses_ray_ho; cbn; lra|].
  apply hpo_cross; [unfold edge_crosses_ray_ho; cbn; left; split; [lra|]; lra|].
  apply hpe_skip; [unfold edge_crosses_ray_ho; cbn; intros [[_ H] | [_ H]]; lra|].
  apply hpe_skip; [unfold edge_crosses_ray_ho; cbn; lra|].
  apply hpe_nil.
Qed.

Theorem sheet_pip_witness : SheetRingPipStmt.witness.
Proof.
  split; [exact diamond_seam|]. split; [exact diamond_vshear_noh|].
  split; [cbn; lra|]. split; [exact diamond_origin_off|].
  split; [exact diamond_origin_in|].
  apply (proj1 (sheet_pip_claim vshear_half diamond_ring (mkPoint 0 0)
                  ltac:(unfold lin_det; cbn; lra) diamond_seam diamond_vshear_noh
                  diamond_origin_off)).
  exact diamond_origin_in.
Qed.

Print Assumptions pip_ring_edges_map.
Print Assumptions ring_image_act.
Print Assumptions complement_act.
Print Assumptions connected_act.
Print Assumptions aff_norm_bound.
Print Assumptions bounded_act.
Print Assumptions geo_act.
Print Assumptions taut_act.
Print Assumptions core_nodup_act.
Print Assumptions sheet_pip_supporting.
Print Assumptions seam_ho.
Print Assumptions ho_along.
Print Assumptions avoid_list.
Print Assumptions guard_move.
Print Assumptions sheet_pip_claim.
Print Assumptions diamond_taut.
Print Assumptions diamond_origin_in.
Print Assumptions sheet_pip_witness.
