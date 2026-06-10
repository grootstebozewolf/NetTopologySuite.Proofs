(* ============================================================================
   NetTopologySuite.Proofs.JCTGenericStability
   ----------------------------------------------------------------------------
   H1 PROPER, part 3: the half-open parity is locally constant at every
   GENERIC-HEIGHT complement point -- and with it, the kernel of the trapped
   half shrinks to vertex-level points only.

   At a complement point q whose height differs from every vertex height,
   each edge's half-open crossing condition is a conjunction/disjunction of
   STRICT affine inequalities in (px q, py q): the band atoms `ya <= h` and
   `h < yb` are strictly satisfied or strictly violated (genericity), and
   the ray atom is the sign of the affine form

     PA = (yb - ya)*(xa - x) + (xb - xa)*(h - ya)     (ascending edge)

   which is nonzero because PA = 0 inside the band puts q ON the edge
   (excluded by the complement).  Strict affine signs are stable on an
   explicit ball (`affine_sign_stable`); a finite Rmin over the edge list
   gives a parity-constant ball (`ho_parity_ball`), and path continuity
   lifts the ball to a parameter interval.

   Consequently (`ho_kernel_of_level_stable`): the FULL kernel
   `ho_parity_locally_constant r` follows from its restriction to
   VERTEX-LEVEL complement points,

     ho_level_stable r

   -- the y-monotone vertex-pairing content of the polygonal JCT in its
   purest form (at such a point, the edges incident to each level vertex
   exchange their half-open bands; everything else is already stable).
   The capstone `odd_parity_trapped_of_level_stable` composes with parts
   1-2: H1's trapped half now needs ONLY `ho_level_stable`.

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam.
From NTS.Proofs Require Import PointInRingCorrect JCT JCT_OnEdgeCounterexample.
From NTS.Proofs Require Import ConvexOffringSeam JCTParityTransport JCTHalfOpenParity.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §1  Strict affine signs are stable on an explicit ball.
   --------------------------------------------------------------------------- *)

Lemma affine_sign_stable : forall (al be c x h : R),
  0 < al * x + be * h + c ->
  exists eps, 0 < eps /\
    forall x' h', Rabs (x' - x) < eps -> Rabs (h' - h) < eps ->
      0 < al * x' + be * h' + c.
Proof.
  intros al be c x h HF.
  set (L := Rabs al + Rabs be + 1).
  assert (HL : 1 <= L)
    by (unfold L; pose proof (Rabs_pos al); pose proof (Rabs_pos be); lra).
  exists ((al * x + be * h + c) / L). split.
  - apply Rdiv_lt_0_compat; lra.
  - intros x' h' Hx Hh.
    set (eps := (al * x + be * h + c) / L) in *.
    assert (Heps : eps * L = al * x + be * h + c) by (unfold eps; field; lra).
    assert (Heps0 : 0 < eps) by (unfold eps; apply Rdiv_lt_0_compat; lra).
    assert (Ha : Rabs (al * (x' - x)) <= Rabs al * eps).
    { rewrite Rabs_mult. apply Rmult_le_compat_l; [ apply Rabs_pos | lra ]. }
    assert (Hb : Rabs (be * (h' - h)) <= Rabs be * eps).
    { rewrite Rabs_mult. apply Rmult_le_compat_l; [ apply Rabs_pos | lra ]. }
    assert (Hz1 : - Rabs (al * (x' - x)) <= al * (x' - x))
      by (pose proof (Rle_abs (- (al * (x' - x)))); rewrite Rabs_Ropp in *; lra).
    assert (Hz2 : - Rabs (be * (h' - h)) <= be * (h' - h))
      by (pose proof (Rle_abs (- (be * (h' - h)))); rewrite Rabs_Ropp in *; lra).
    unfold L in *. nra.
Qed.

(* ---------------------------------------------------------------------------
   §2  Division-free crossing characterisations (ascending / descending).
   --------------------------------------------------------------------------- *)

Lemma ho_asc_iff : forall (a b q : Point),
  py a < py b ->
  (edge_crosses_ray_ho q (a, b) <->
   (py a <= py q < py b /\
    0 < (py b - py a) * (px a - px q) + (px b - px a) * (py q - py a))).
Proof.
  intros a b q Hab. unfold edge_crosses_ray_ho. split.
  - intros [[Hy Hx] | [[Hy1 Hy2] Hx]]; [ | lra ].
    split; [ exact Hy | ].
    apply (Rmult_lt_compat_r (py b - py a)) in Hx; [ | lra ].
    replace ((px a + (px b - px a) * (py q - py a) / (py b - py a)) * (py b - py a))
      with (px a * (py b - py a) + (px b - px a) * (py q - py a)) in Hx
      by (field; lra).
    nra.
  - intros [Hy HP]. left. split; [ exact Hy | ].
    apply (Rmult_lt_reg_r (py b - py a)); [ lra | ].
    replace ((px a + (px b - px a) * (py q - py a) / (py b - py a)) * (py b - py a))
      with (px a * (py b - py a) + (px b - px a) * (py q - py a)) by (field; lra).
    nra.
Qed.

Lemma ho_desc_iff : forall (a b q : Point),
  py b < py a ->
  (edge_crosses_ray_ho q (a, b) <->
   (py b <= py q < py a /\
    0 < (py a - py b) * (px b - px q) + (px a - px b) * (py q - py b))).
Proof.
  intros a b q Hab. unfold edge_crosses_ray_ho. split.
  - intros [[[Hy1 Hy2] Hx] | [Hy Hx]]; [ lra | ].
    split; [ exact Hy | ].
    apply (Rmult_lt_compat_r (py a - py b)) in Hx; [ | lra ].
    replace ((px b + (px a - px b) * (py q - py b) / (py a - py b)) * (py a - py b))
      with (px b * (py a - py b) + (px a - px b) * (py q - py b)) in Hx
      by (field; lra).
    nra.
  - intros [Hy HP]. right. split; [ exact Hy | ].
    apply (Rmult_lt_reg_r (py a - py b)); [ lra | ].
    replace ((px b + (px a - px b) * (py q - py b) / (py a - py b)) * (py a - py b))
      with (px b * (py a - py b) + (px a - px b) * (py q - py b)) by (field; lra).
    nra.
Qed.

(* ---------------------------------------------------------------------------
   §3  Per-edge stability at a generic-height off-edge point.
   --------------------------------------------------------------------------- *)

Lemma ho_cross_stable_generic : forall (a b q : Point),
  (~ exists t : R, 0 <= t <= 1 /\
        px q = (1 - t) * px a + t * px b /\
        py q = (1 - t) * py a + t * py b) ->
  py q <> py a -> py q <> py b ->
  exists eps, 0 < eps /\
    forall q' : Point,
      Rabs (px q' - px q) < eps -> Rabs (py q' - py q) < eps ->
      (edge_crosses_ray_ho q' (a, b) <-> edge_crosses_ray_ho q (a, b)).
Proof.
  intros a b q Hoff Hna Hnb.
  destruct (Rtotal_order (py a) (py q)) as [Hya | [Hya | Hya]];
    [ | exfalso; apply Hna; symmetry; exact Hya | ];
  destruct (Rtotal_order (py b) (py q)) as [Hyb | [Hyb | Hyb]];
    try (exfalso; apply Hnb; symmetry; exact Hyb).
  - (* ya < h, yb < h : no band can hold near q *)
    destruct (affine_sign_stable 0 1 (- py a) (px q) (py q) ltac:(lra))
      as [e1 [He1 Hb1]].
    destruct (affine_sign_stable 0 1 (- py b) (px q) (py q) ltac:(lra))
      as [e2 [He2 Hb2]].
    exists (Rmin e1 e2). split.
    + apply Rmin_glb_lt; lra.
    + intros q' Hx Hh.
      assert (Hx1 : Rabs (px q' - px q) < e1)
        by (eapply Rlt_le_trans; [ exact Hx | apply Rmin_l ]).
      assert (Hh1 : Rabs (py q' - py q) < e1)
        by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_l ]).
      assert (Hx2 : Rabs (px q' - px q) < e2)
        by (eapply Rlt_le_trans; [ exact Hx | apply Rmin_r ]).
      assert (Hh2 : Rabs (py q' - py q) < e2)
        by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_r ]).
      pose proof (Hb1 (px q') (py q') Hx1 Hh1) as H1.
      pose proof (Hb2 (px q') (py q') Hx2 Hh2) as H2.
      unfold edge_crosses_ray_ho.
      split; intros [[[Hu1 Hu2] _] | [[Hu1 Hu2] _]]; lra.
  - (* ya < h, h < yb : ascending band, strict *)
    set (PA := (py b - py a) * (px a - px q) + (px b - px a) * (py q - py a)).
    assert (HPA : PA <> 0).
    { intro Hz. apply Hoff.
      exists ((py q - py a) / (py b - py a)).
      assert (Hd : py b - py a <> 0) by lra.
      split; [ split | split ].
      - apply Rmult_le_reg_r with (py b - py a); [ lra | ].
        replace ((py q - py a) / (py b - py a) * (py b - py a))
          with (py q - py a) by (field; lra). lra.
      - apply Rmult_le_reg_r with (py b - py a); [ lra | ].
        replace ((py q - py a) / (py b - py a) * (py b - py a))
          with (py q - py a) by (field; lra). lra.
      - apply Rmult_eq_reg_r with (py b - py a); [ | lra ].
        replace (((1 - (py q - py a) / (py b - py a)) * px a +
                  (py q - py a) / (py b - py a) * px b) * (py b - py a))
          with (px a * (py b - py q) + px b * (py q - py a)) by (field; lra).
        unfold PA in Hz. nra.
      - apply Rmult_eq_reg_r with (py b - py a); [ | lra ].
        replace (((1 - (py q - py a) / (py b - py a)) * py a +
                  (py q - py a) / (py b - py a) * py b) * (py b - py a))
          with (py a * (py b - py q) + py b * (py q - py a)) by (field; lra).
        nra. }
    destruct (Rtotal_order 0 PA) as [HPAp | [HPAz | HPAn]];
      [ | exfalso; exact (HPA (eq_sym HPAz)) | ].
    + destruct (affine_sign_stable 0 1 (- py a) (px q) (py q) ltac:(lra))
        as [e1 [He1 Hb1]].
      destruct (affine_sign_stable 0 (-1) (py b) (px q) (py q) ltac:(lra))
        as [e2 [He2 Hb2]].
      destruct (affine_sign_stable
                  (- (py b - py a)) (px b - px a)
                  ((py b - py a) * px a - (px b - px a) * py a)
                  (px q) (py q) ltac:(unfold PA in HPAp; nra))
        as [e3 [He3 Hb3]].
      exists (Rmin (Rmin e1 e2) e3). split.
      * apply Rmin_glb_lt; [ apply Rmin_glb_lt; lra | lra ].
      * intros q' Hx Hh.
        assert (Hx1 : Rabs (px q' - px q) < e1)
          by (eapply Rlt_le_trans; [ exact Hx | ];
              eapply Rle_trans; [ apply Rmin_l | apply Rmin_l ]).
        assert (Hh1 : Rabs (py q' - py q) < e1)
          by (eapply Rlt_le_trans; [ exact Hh | ];
              eapply Rle_trans; [ apply Rmin_l | apply Rmin_l ]).
        assert (Hx2 : Rabs (px q' - px q) < e2)
          by (eapply Rlt_le_trans; [ exact Hx | ];
              eapply Rle_trans; [ apply Rmin_l | apply Rmin_r ]).
        assert (Hh2 : Rabs (py q' - py q) < e2)
          by (eapply Rlt_le_trans; [ exact Hh | ];
              eapply Rle_trans; [ apply Rmin_l | apply Rmin_r ]).
        assert (Hx3 : Rabs (px q' - px q) < e3)
          by (eapply Rlt_le_trans; [ exact Hx | apply Rmin_r ]).
        assert (Hh3 : Rabs (py q' - py q) < e3)
          by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_r ]).
        pose proof (Hb1 (px q') (py q') Hx1 Hh1) as S1.
        pose proof (Hb2 (px q') (py q') Hx2 Hh2) as S2.
        pose proof (Hb3 (px q') (py q') Hx3 Hh3) as S3.
        rewrite (ho_asc_iff a b q' ltac:(lra)), (ho_asc_iff a b q ltac:(lra)).
        split; intros _; (split; [ lra | unfold PA in *; nra ]).
    + destruct (affine_sign_stable
                  (py b - py a) (- (px b - px a))
                  (- ((py b - py a) * px a - (px b - px a) * py a))
                  (px q) (py q) ltac:(unfold PA in HPAn; nra))
        as [e3 [He3 Hb3]].
      exists e3. split; [ lra | ].
      intros q' Hx Hh.
      pose proof (Hb3 (px q') (py q') Hx Hh) as S3.
      rewrite (ho_asc_iff a b q' ltac:(lra)), (ho_asc_iff a b q ltac:(lra)).
      split; intros [Hu HP]; exfalso; try unfold PA in *; try unfold PD in *; nra.
  - (* yb < h < ya : descending band, strict *)
    set (PD := (py a - py b) * (px b - px q) + (px a - px b) * (py q - py b)).
    assert (HPD : PD <> 0).
    { intro Hz. apply Hoff.
      exists ((py a - py q) / (py a - py b)).
      assert (Hd : py a - py b <> 0) by lra.
      split; [ split | split ].
      - apply Rmult_le_reg_r with (py a - py b); [ lra | ].
        replace ((py a - py q) / (py a - py b) * (py a - py b))
          with (py a - py q) by (field; lra). lra.
      - apply Rmult_le_reg_r with (py a - py b); [ lra | ].
        replace ((py a - py q) / (py a - py b) * (py a - py b))
          with (py a - py q) by (field; lra). lra.
      - apply Rmult_eq_reg_r with (py a - py b); [ | lra ].
        replace (((1 - (py a - py q) / (py a - py b)) * px a +
                  (py a - py q) / (py a - py b) * px b) * (py a - py b))
          with (px a * (py q - py b) + px b * (py a - py q)) by (field; lra).
        unfold PD in Hz. nra.
      - apply Rmult_eq_reg_r with (py a - py b); [ | lra ].
        replace (((1 - (py a - py q) / (py a - py b)) * py a +
                  (py a - py q) / (py a - py b) * py b) * (py a - py b))
          with (py a * (py q - py b) + py b * (py a - py q)) by (field; lra).
        nra. }
    destruct (Rtotal_order 0 PD) as [HPDp | [HPDz | HPDn]];
      [ | exfalso; exact (HPD (eq_sym HPDz)) | ].
    + (* crossing TRUE at q, stably *)
      destruct (affine_sign_stable 0 1 (- py b) (px q) (py q) ltac:(lra))
        as [e1 [He1 Hb1]].
      destruct (affine_sign_stable 0 (-1) (py a) (px q) (py q) ltac:(lra))
        as [e2 [He2 Hb2]].
      destruct (affine_sign_stable
                  (- (py a - py b)) (px a - px b)
                  ((py a - py b) * px b - (px a - px b) * py b)
                  (px q) (py q) ltac:(unfold PD in HPDp; nra))
        as [e3 [He3 Hb3]].
      exists (Rmin (Rmin e1 e2) e3). split.
      * apply Rmin_glb_lt; [ apply Rmin_glb_lt; lra | lra ].
      * intros q' Hx Hh.
        assert (Hx1 : Rabs (px q' - px q) < e1)
          by (eapply Rlt_le_trans; [ exact Hx | ];
              eapply Rle_trans; [ apply Rmin_l | apply Rmin_l ]).
        assert (Hh1 : Rabs (py q' - py q) < e1)
          by (eapply Rlt_le_trans; [ exact Hh | ];
              eapply Rle_trans; [ apply Rmin_l | apply Rmin_l ]).
        assert (Hx2 : Rabs (px q' - px q) < e2)
          by (eapply Rlt_le_trans; [ exact Hx | ];
              eapply Rle_trans; [ apply Rmin_l | apply Rmin_r ]).
        assert (Hh2 : Rabs (py q' - py q) < e2)
          by (eapply Rlt_le_trans; [ exact Hh | ];
              eapply Rle_trans; [ apply Rmin_l | apply Rmin_r ]).
        assert (Hx3 : Rabs (px q' - px q) < e3)
          by (eapply Rlt_le_trans; [ exact Hx | apply Rmin_r ]).
        assert (Hh3 : Rabs (py q' - py q) < e3)
          by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_r ]).
        pose proof (Hb1 (px q') (py q') Hx1 Hh1) as S1.
        pose proof (Hb2 (px q') (py q') Hx2 Hh2) as S2.
        pose proof (Hb3 (px q') (py q') Hx3 Hh3) as S3.
        rewrite (ho_desc_iff a b q' ltac:(lra)), (ho_desc_iff a b q ltac:(lra)).
        split; intros _; (split; [ lra | unfold PD in *; nra ]).
    + (* crossing FALSE at q, stably (the ray atom stays negative) *)
      destruct (affine_sign_stable
                  (py a - py b) (- (px a - px b))
                  (- ((py a - py b) * px b - (px a - px b) * py b))
                  (px q) (py q) ltac:(unfold PD in HPDn; nra))
        as [e3 [He3 Hb3]].
      exists e3. split; [ lra | ].
      intros q' Hx Hh.
      pose proof (Hb3 (px q') (py q') Hx Hh) as S3.
      rewrite (ho_desc_iff a b q' ltac:(lra)), (ho_desc_iff a b q ltac:(lra)).
      split; intros [Hu HP]; exfalso; try unfold PA in *; try unfold PD in *; nra.
  - (* h < ya, h < yb : no band can hold near q *)
    destruct (affine_sign_stable 0 (-1) (py a) (px q) (py q) ltac:(lra))
      as [e1 [He1 Hb1]].
    destruct (affine_sign_stable 0 (-1) (py b) (px q) (py q) ltac:(lra))
      as [e2 [He2 Hb2]].
    exists (Rmin e1 e2). split; [ apply Rmin_glb_lt; lra | ].
    intros q' Hx Hh.
    assert (Hx1 : Rabs (px q' - px q) < e1)
      by (eapply Rlt_le_trans; [ exact Hx | apply Rmin_l ]).
    assert (Hh1 : Rabs (py q' - py q) < e1)
      by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_l ]).
    assert (Hx2 : Rabs (px q' - px q) < e2)
      by (eapply Rlt_le_trans; [ exact Hx | apply Rmin_r ]).
    assert (Hh2 : Rabs (py q' - py q) < e2)
      by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_r ]).
    pose proof (Hb1 (px q') (py q') Hx1 Hh1) as H1.
    pose proof (Hb2 (px q') (py q') Hx2 Hh2) as H2.
    unfold edge_crosses_ray_ho.
    split; intros [[[Hu1 Hu2] _] | [[Hu1 Hu2] _]]; lra.
Qed.

(* ---------------------------------------------------------------------------
   §4  Finite assembly: a parity-constant ball at a generic-height point.
   --------------------------------------------------------------------------- *)

Lemma ho_parity_ball : forall (q : Point) (es : list Edge),
  (forall e, In e es ->
     exists eps, 0 < eps /\
       forall q' : Point,
         Rabs (px q' - px q) < eps -> Rabs (py q' - py q) < eps ->
         (edge_crosses_ray_ho q' e <-> edge_crosses_ray_ho q e)) ->
  exists eps, 0 < eps /\
    forall q' : Point,
      Rabs (px q' - px q) < eps -> Rabs (py q' - py q) < eps ->
      (ho_parity_odd q' es <-> ho_parity_odd q es)
      /\ (ho_parity_even q' es <-> ho_parity_even q es).
Proof.
  intros q; induction es as [| e es' IH]; intros Hst.
  - exists 1. split; [ lra | ].
    intros q' _ _. split; split; intro H; try (inversion H; fail); constructor.
  - destruct (Hst e (or_introl eq_refl)) as [e1 [He1 Hb1]].
    destruct (IH (fun e' He' => Hst e' (or_intror He'))) as [e2 [He2 Hb2]].
    exists (Rmin e1 e2). split; [ apply Rmin_glb_lt; lra | ].
    intros q' Hx Hh.
    assert (Hx1 : Rabs (px q' - px q) < e1)
      by (eapply Rlt_le_trans; [ exact Hx | apply Rmin_l ]).
    assert (Hh1 : Rabs (py q' - py q) < e1)
      by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_l ]).
    assert (Hx2 : Rabs (px q' - px q) < e2)
      by (eapply Rlt_le_trans; [ exact Hx | apply Rmin_r ]).
    assert (Hh2 : Rabs (py q' - py q) < e2)
      by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_r ]).
    pose proof (Hb1 q' Hx1 Hh1) as Hiff.
    destruct (Hb2 q' Hx2 Hh2) as [IHo IHe].
    destruct (edge_crosses_ray_ho_dec q e) as [Hc | Hn].
    + assert (Hc' : edge_crosses_ray_ho q' e) by tauto.
      rewrite (ho_odd_cons_cross _ _ _ Hc), (ho_odd_cons_cross _ _ _ Hc'),
              (ho_even_cons_cross _ _ _ Hc), (ho_even_cons_cross _ _ _ Hc').
      tauto.
    + assert (Hn' : ~ edge_crosses_ray_ho q' e) by tauto.
      rewrite (ho_odd_cons_skip _ _ _ Hn), (ho_odd_cons_skip _ _ _ Hn'),
              (ho_even_cons_skip _ _ _ Hn), (ho_even_cons_skip _ _ _ Hn').
      tauto.
Qed.

(* ---------------------------------------------------------------------------
   §5  Path lifting and the kernel reduction to vertex-level points.
   --------------------------------------------------------------------------- *)

Lemma path_coord_close : forall (g : R -> Point) (t eps : R),
  0 < eps -> path_continuous g ->
  exists d, 0 < d /\
    forall s, Rabs (s - t) < d ->
      Rabs (px (g s) - px (g t)) < eps /\ Rabs (py (g s) - py (g t)) < eps.
Proof.
  intros g t eps Heps [Hgx Hgy].
  destruct (Hgx t eps Heps) as [a1 [Ha1 Hb1]].
  destruct (Hgy t eps Heps) as [a2 [Ha2 Hb2]].
  exists (Rmin a1 a2). split; [ apply Rmin_glb_lt; lra | ].
  intros s Hs.
  destruct (Req_dec t s) as [Heq | Hne].
  { rewrite <- Heq.
    unfold Rminus; rewrite !Rplus_opp_r, Rabs_R0. split; lra. }
  split.
  - assert (Hd : R_dist (px (g s)) (px (g t)) < eps).
    { apply Hb1. split.
      - split; [ exact I | exact Hne ].
      - simpl. unfold R_dist.
        eapply Rlt_le_trans; [ exact Hs | apply Rmin_l ]. }
    unfold R_dist in Hd. exact Hd.
  - assert (Hd : R_dist (py (g s)) (py (g t)) < eps).
    { apply Hb2. split.
      - split; [ exact I | exact Hne ].
      - simpl. unfold R_dist.
        eapply Rlt_le_trans; [ exact Hs | apply Rmin_r ]. }
    unfold R_dist in Hd. exact Hd.
Qed.

(* Deciding whether q sits at some vertex level. *)
Lemma vertex_at_level_dec : forall (r : Ring) (q : Point),
  {exists v, In v r /\ py v = py q} + {forall v, In v r -> py v <> py q}.
Proof.
  intros r q. induction r as [| v r' IH].
  - right; intros v [].
  - destruct (Req_EM_T (py v) (py q)) as [He | Hne].
    + left; exists v; split; [ left; reflexivity | exact He ].
    + destruct IH as [Hex | Hno].
      * left. destruct Hex as [w [Hw He']].
        exists w. split; [ right; exact Hw | exact He' ].
      * right; intros u [Hu | Hu]; [ subst u; exact Hne | exact (Hno u Hu) ].
Qed.

(* THE REMAINING KERNEL: local constancy at VERTEX-LEVEL complement points
   only -- the vertex-pairing content of the polygonal JCT. *)
Definition ho_level_stable (r : Ring) : Prop :=
  forall q : Point,
    ring_complement r q ->
    (exists v, In v r /\ py v = py q) ->
    exists eps, 0 < eps /\
      forall q' : Point,
        Rabs (px q' - px q) < eps -> Rabs (py q' - py q) < eps ->
        ring_complement r q' ->
        (point_in_ring_ho q' r <-> point_in_ring_ho q r).

(* Generic-height local constancy, Qed. *)
Theorem ho_generic_stable : forall (r : Ring) (q : Point),
  ring_complement r q ->
  (forall v, In v r -> py v <> py q) ->
  exists eps, 0 < eps /\
    forall q' : Point,
      Rabs (px q' - px q) < eps -> Rabs (py q' - py q) < eps ->
      (point_in_ring_ho q' r <-> point_in_ring_ho q r).
Proof.
  intros r q Hcompl Hgen.
  destruct (ho_parity_ball q (ring_edges r)) as [eps [Heps Hball]].
  { intros [a b] Hin.
    destruct (ring_edges_endpoints_in r _ Hin) as [Ha Hb].
    cbn [fst snd] in Ha, Hb.
    apply ho_cross_stable_generic.
    - intro Hex. apply Hcompl.
      destruct Hex as [t [[Ht1 Ht2] [Hx Hy]]].
      exists (a, b), t. cbn [fst snd]. repeat split; assumption.
    - intro He; exact (Hgen a Ha (eq_sym He)).
    - intro He; exact (Hgen b Hb (eq_sym He)). }
  exists eps. split; [ exact Heps | ].
  intros q' Hx Hh. exact (proj1 (Hball q' Hx Hh)).
Qed.

(* The reduction: level stability implies the full kernel. *)
Theorem ho_kernel_of_level_stable : forall (r : Ring),
  ho_level_stable r ->
  ho_parity_locally_constant r.
Proof.
  intros r Hlev g Hg Hcompl t Ht.
  destruct (vertex_at_level_dec r (g t)) as [Hat | Hgen].
  - destruct (Hlev (g t) (Hcompl t Ht) Hat) as [eps [Heps Hball]].
    destruct (path_coord_close g t eps Heps Hg) as [d [Hd Hcl]].
    exists d. split; [ exact Hd | ].
    intros s Hs01 Hst. destruct (Hcl s Hst) as [Hx Hh].
    exact (Hball (g s) Hx Hh (Hcompl s Hs01)).
  - destruct (ho_generic_stable r (g t) (Hcompl t Ht) Hgen)
      as [eps [Heps Hball]].
    destruct (path_coord_close g t eps Heps Hg) as [d [Hd Hcl]].
    exists d. split; [ exact Hd | ].
    intros s Hs01 Hst. destruct (Hcl s Hst) as [Hx Hh].
    exact (Hball (g s) Hx Hh).
Qed.

(* THE CAPSTONE: H1's trapped half needs only `ho_level_stable`. *)
Theorem odd_parity_trapped_of_level_stable : forall (r : Ring) (p : Point),
  ring_closed r ->
  ho_level_stable r ->
  ray_avoids_vertices p r ->
  point_in_ring p r ->
  in_bounded_component_cont r p.
Proof.
  intros r p Hclosed Hlev Hrav Hpir.
  apply (odd_parity_trapped_of_ho_kernel r p Hclosed); try assumption.
  apply ho_kernel_of_level_stable. exact Hlev.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions affine_sign_stable.
Print Assumptions ho_cross_stable_generic.
Print Assumptions ho_generic_stable.
Print Assumptions ho_kernel_of_level_stable.
Print Assumptions odd_parity_trapped_of_level_stable.
