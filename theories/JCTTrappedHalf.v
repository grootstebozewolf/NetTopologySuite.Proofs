(* ============================================================================
   NetTopologySuite.Proofs.JCTTrappedHalf
   ----------------------------------------------------------------------------
   H1 PROPER, part 5: THE DOWNWARD LEVEL JUMP IS A THEOREM -- and with it,
   the TRAPPED HALF of the polygonal Jordan Curve Theorem is Qed,
   unconditionally, for every closed ring:

     odd_parity_trapped :
       ring_closed r -> ray_avoids_vertices p r -> point_in_ring p r ->
       in_bounded_component_cont r p.

   The discovery that makes the vertex-pairing argument finite: define the
   EAST-LEVEL FLAG  F(v) := (py v = py q /\ px q < px v).  For a complement
   point q at level h and a point q' just below the level, the per-edge
   comparison of half-open crossings satisfies, for EVERY edge (u,w),

     (cross q' <-> cross q)  <->  (F u <-> F w).

   Case check: edges away from the level are stable and have F u = F w =
   False; an edge whose BOTTOM endpoint sits at the level counts AT the
   level iff that endpoint is east (PA reduces to (yb-ya)(xa-x)) and never
   counts below; an edge whose TOP endpoint sits at the level counts BELOW
   iff that endpoint is east (PA at the level is (yb-ya)(xb-x), nonzero and
   affine-stable) and never at it; and a HORIZONTAL edge at the level never
   counts on either side while its two flags AGREE -- because a horizontal
   level edge with endpoints on opposite sides of q would contain q
   (excluded by the complement).  So the jump contribution of each edge is
   exactly the flag flip F u (+) F w, and around a CLOSED walk the flag
   returns to its start: the total flip telescopes to zero
   (`ho_jump_walk` / `ho_jump_closed`), mirroring the far-west walk lemma.

   Hence `ho_level_jump_holds` (the part-4 kernel, now a theorem) and the
   unconditional capstone.  Note `ring_simple` is NOT needed: odd half-open
   parity traps the point inside ANY closed ring.

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam.
From NTS.Proofs Require Import PointInRingCorrect JCT JCT_OnEdgeCounterexample.
From NTS.Proofs Require Import ConvexOffringSeam JCTParityTransport.
From NTS.Proofs Require Import JCTHalfOpenParity JCTGenericStability JCTLevelJump.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §1  The east-level flag.
   --------------------------------------------------------------------------- *)

Definition eastlevel (q v : Point) : Prop :=
  py v = py q /\ px q < px v.

Lemma eastlevel_dec : forall q v, {eastlevel q v} + {~ eastlevel q v}.
Proof.
  intros q v. unfold eastlevel.
  destruct (Req_EM_T (py v) (py q)) as [He | Hne].
  - destruct (Rlt_dec (px q) (px v)) as [Hl | Hl].
    + left; split; assumption.
    + right; intros [_ Hc]; exact (Hl Hc).
  - right; intros [Hc _]; exact (Hne Hc).
Qed.

(* ---------------------------------------------------------------------------
   §2  The per-edge jump law: crossing-agreement equals flag-agreement.
   --------------------------------------------------------------------------- *)

Lemma ho_cross_lower_flag : forall (a b q : Point),
  (~ exists t : R, 0 <= t <= 1 /\
        px q = (1 - t) * px a + t * px b /\
        py q = (1 - t) * py a + t * py b) ->
  exists eps, 0 < eps /\
    forall q' : Point,
      Rabs (px q' - px q) < eps -> py q - eps < py q' < py q ->
      ((edge_crosses_ray_ho q' (a, b) <-> edge_crosses_ray_ho q (a, b))
         <-> (eastlevel q a <-> eastlevel q b)).
Proof.
  intros a b q Hoff.
  destruct (Rtotal_order (py a) (py q)) as [Hya | [Hya | Hya]];
  destruct (Rtotal_order (py b) (py q)) as [Hyb | [Hyb | Hyb]].
  - (* I: ya < h, yb < h : dead on both sides with margin *)
    exists (Rmin (py q - py a) (py q - py b)). split.
    + apply Rmin_glb_lt; lra.
    + intros q' Hx Hh.
      pose proof (Rmin_l (py q - py a) (py q - py b)).
      pose proof (Rmin_r (py q - py a) (py q - py b)).
      assert (Hnc' : ~ edge_crosses_ray_ho q' (a, b))
        by (intros [[[Hu1 Hu2] _] | [[Hu1 Hu2] _]]; lra).
      assert (Hnc : ~ edge_crosses_ray_ho q (a, b))
        by (intros [[[Hu1 Hu2] _] | [[Hu1 Hu2] _]]; lra).
      assert (Ha : ~ eastlevel q a) by (intros [He _]; lra).
      assert (Hb : ~ eastlevel q b) by (intros [He _]; lra).
      tauto.
  - (* VI: ya < h = yb : ascending TOP at the level *)
    assert (Hab : py a < py b) by lra.
    assert (Hxb : px b <> px q).
    { intro He. apply Hoff. exists 1. split; [ lra | ]. split.
      - replace ((1 - 1) * px a + 1 * px b) with (px b) by ring. auto.
      - replace ((1 - 1) * py a + 1 * py b) with (py b) by ring. auto. }
    assert (HELa : ~ eastlevel q a) by (intros [He _]; lra).
    assert (HELb : eastlevel q b <-> px q < px b)
      by (unfold eastlevel; split; [ intros [_ ?]; assumption
                                   | intro; split; [ exact Hyb | assumption ] ]).
    assert (Hnc : ~ edge_crosses_ray_ho q (a, b))
      by (intros [[[Hu1 Hu2] _] | [[Hu1 Hu2] _]]; lra).
    destruct (Rtotal_order (px q) (px b)) as [Hxq | [Hxq | Hxq]];
      [ | exfalso; exact (Hxb (eq_sym Hxq)) | ].
    + (* b east: the edge counts just below the level *)
      assert (HPA : 0 < (py b - py a) * (px a - px q)
                      + (px b - px a) * (py q - py a)) by nra.
      destruct (affine_sign_stable
                  (- (py b - py a)) (px b - px a)
                  ((py b - py a) * px a - (px b - px a) * py a)
                  (px q) (py q) ltac:(nra))
        as [e3 [He3 Hb3]].
      exists (Rmin e3 (py q - py a)). split.
      * apply Rmin_glb_lt; lra.
      * intros q' Hx Hh.
        pose proof (Rmin_l e3 (py q - py a)).
        pose proof (Rmin_r e3 (py q - py a)).
        assert (Hx3 : Rabs (px q' - px q) < e3) by lra.
        assert (Hh3 : Rabs (py q' - py q) < e3)
          by (unfold Rabs; destruct (Rcase_abs (py q' - py q)); lra).
        pose proof (Hb3 (px q') (py q') Hx3 Hh3) as S3.
        assert (Hc' : edge_crosses_ray_ho q' (a, b)).
        { apply (ho_asc_iff a b q' Hab). split; [ lra | nra ]. }
        tauto.
    + (* b west: the edge counts on neither side *)
      assert (HPA : (py b - py a) * (px a - px q)
                      + (px b - px a) * (py q - py a) < 0) by nra.
      destruct (affine_sign_stable
                  (py b - py a) (- (px b - px a))
                  (- ((py b - py a) * px a - (px b - px a) * py a))
                  (px q) (py q) ltac:(nra))
        as [e3 [He3 Hb3]].
      exists e3. split; [ lra | ].
      intros q' Hx Hh.
      assert (Hh3 : Rabs (py q' - py q) < e3)
        by (unfold Rabs; destruct (Rcase_abs (py q' - py q)); lra).
      pose proof (Hb3 (px q') (py q') Hx Hh3) as S3.
      assert (Hnc' : ~ edge_crosses_ray_ho q' (a, b)).
      { rewrite (ho_asc_iff a b q' Hab). intros [Hu HP]. nra. }
      assert (Hbw : ~ eastlevel q b) by (rewrite HELb; lra).
      tauto.
  - (* III: ya < h < yb : strict ascending band, stable *)
    assert (Hab : py a < py b) by lra.
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
    assert (HELa : ~ eastlevel q a) by (intros [He _]; lra).
    assert (HELb : ~ eastlevel q b) by (intros [He _]; lra).
    destruct (Rtotal_order 0 PA) as [HPAp | [HPAz | HPAn]];
      [ | exfalso; exact (HPA (eq_sym HPAz)) | ].
    + destruct (affine_sign_stable
                  (- (py b - py a)) (px b - px a)
                  ((py b - py a) * px a - (px b - px a) * py a)
                  (px q) (py q) ltac:(unfold PA in HPAp; nra))
        as [e3 [He3 Hb3]].
      exists (Rmin e3 (py q - py a)). split.
      * apply Rmin_glb_lt; lra.
      * intros q' Hx Hh.
        pose proof (Rmin_l e3 (py q - py a)).
        pose proof (Rmin_r e3 (py q - py a)).
        assert (Hx3 : Rabs (px q' - px q) < e3) by lra.
        assert (Hh3 : Rabs (py q' - py q) < e3)
          by (unfold Rabs; destruct (Rcase_abs (py q' - py q)); lra).
        pose proof (Hb3 (px q') (py q') Hx3 Hh3) as S3.
        assert (Hc' : edge_crosses_ray_ho q' (a, b))
          by (apply (ho_asc_iff a b q' Hab); split; [ lra | nra ]).
        assert (Hc : edge_crosses_ray_ho q (a, b))
          by (apply (ho_asc_iff a b q Hab); split; [ lra | unfold PA in *; nra ]).
        tauto.
    + destruct (affine_sign_stable
                  (py b - py a) (- (px b - px a))
                  (- ((py b - py a) * px a - (px b - px a) * py a))
                  (px q) (py q) ltac:(unfold PA in HPAn; nra))
        as [e3 [He3 Hb3]].
      exists e3. split; [ lra | ].
      intros q' Hx Hh.
      assert (Hh3 : Rabs (py q' - py q) < e3)
        by (unfold Rabs; destruct (Rcase_abs (py q' - py q)); lra).
      pose proof (Hb3 (px q') (py q') Hx Hh3) as S3.
      assert (Hnc' : ~ edge_crosses_ray_ho q' (a, b))
        by (rewrite (ho_asc_iff a b q' Hab); intros [Hu HP]; nra).
      assert (Hnc : ~ edge_crosses_ray_ho q (a, b))
        by (rewrite (ho_asc_iff a b q Hab); intros [Hu HP];
            unfold PA in *; nra).
      tauto.
  - (* VIII: yb < h = ya : descending TOP at the level *)
    assert (Hab : py b < py a) by lra.
    assert (Hxa : px a <> px q).
    { intro He. apply Hoff. exists 0. split; [ lra | ]. split.
      - replace ((1 - 0) * px a + 0 * px b) with (px a) by ring. auto.
      - replace ((1 - 0) * py a + 0 * py b) with (py a) by ring. auto. }
    assert (HELb : ~ eastlevel q b) by (intros [He _]; lra).
    assert (HELa : eastlevel q a <-> px q < px a)
      by (unfold eastlevel; split; [ intros [_ ?]; assumption
                                   | intro; split; [ exact Hya | assumption ] ]).
    assert (Hnc : ~ edge_crosses_ray_ho q (a, b))
      by (intros [[[Hu1 Hu2] _] | [[Hu1 Hu2] _]]; lra).
    destruct (Rtotal_order (px q) (px a)) as [Hxq | [Hxq | Hxq]];
      [ | exfalso; exact (Hxa (eq_sym Hxq)) | ].
    + assert (HPD : 0 < (py a - py b) * (px b - px q)
                      + (px a - px b) * (py q - py b)) by nra.
      destruct (affine_sign_stable
                  (- (py a - py b)) (px a - px b)
                  ((py a - py b) * px b - (px a - px b) * py b)
                  (px q) (py q) ltac:(nra))
        as [e3 [He3 Hb3]].
      exists (Rmin e3 (py q - py b)). split.
      * apply Rmin_glb_lt; lra.
      * intros q' Hx Hh.
        pose proof (Rmin_l e3 (py q - py b)).
        pose proof (Rmin_r e3 (py q - py b)).
        assert (Hx3 : Rabs (px q' - px q) < e3) by lra.
        assert (Hh3 : Rabs (py q' - py q) < e3)
          by (unfold Rabs; destruct (Rcase_abs (py q' - py q)); lra).
        pose proof (Hb3 (px q') (py q') Hx3 Hh3) as S3.
        assert (Hc' : edge_crosses_ray_ho q' (a, b)).
        { apply (ho_desc_iff a b q' Hab). split; [ lra | nra ]. }
        tauto.
    + assert (HPD : (py a - py b) * (px b - px q)
                      + (px a - px b) * (py q - py b) < 0) by nra.
      destruct (affine_sign_stable
                  (py a - py b) (- (px a - px b))
                  (- ((py a - py b) * px b - (px a - px b) * py b))
                  (px q) (py q) ltac:(nra))
        as [e3 [He3 Hb3]].
      exists e3. split; [ lra | ].
      intros q' Hx Hh.
      assert (Hh3 : Rabs (py q' - py q) < e3)
        by (unfold Rabs; destruct (Rcase_abs (py q' - py q)); lra).
      pose proof (Hb3 (px q') (py q') Hx Hh3) as S3.
      assert (Hnc' : ~ edge_crosses_ray_ho q' (a, b)).
      { rewrite (ho_desc_iff a b q' Hab). intros [Hu HP]. nra. }
      assert (Haw : ~ eastlevel q a) by (rewrite HELa; lra).
      tauto.
  - (* IX: ya = yb = h : horizontal at the level; flags agree (same side) *)
    exists 1. split; [ lra | ].
    intros q' Hx Hh.
    assert (Hnc' : ~ edge_crosses_ray_ho q' (a, b))
      by (intros [[[Hu1 Hu2] _] | [[Hu1 Hu2] _]]; lra).
    assert (Hnc : ~ edge_crosses_ray_ho q (a, b))
      by (intros [[[Hu1 Hu2] _] | [[Hu1 Hu2] _]]; lra).
    assert (Hside : (px q < px a) <-> (px q < px b)).
    { destruct (Req_EM_T (px a) (px b)) as [Heq | Hne];
        [ rewrite Heq; tauto | ].
      split; intro Hlt.
      - destruct (Rlt_dec (px q) (px b)) as [Hok | Hge]; [ exact Hok | ].
        exfalso. apply Hoff.
        exists ((px q - px a) / (px b - px a)).
        assert (Hd : px b - px a <> 0) by lra.
        split; [ split | split ].
        + apply Rmult_le_reg_r with (px a - px b); [ lra | ].
          replace ((px q - px a) / (px b - px a) * (px a - px b))
            with (px a - px q) by (field; lra). lra.
        + apply Rmult_le_reg_r with (px a - px b); [ lra | ].
          replace ((px q - px a) / (px b - px a) * (px a - px b))
            with (px a - px q) by (field; lra). lra.
        + apply Rmult_eq_reg_r with (px b - px a); [ | lra ].
          replace (((1 - (px q - px a) / (px b - px a)) * px a +
                    (px q - px a) / (px b - px a) * px b) * (px b - px a))
            with (px a * (px b - px q) + px b * (px q - px a)) by (field; lra).
          nra.
        + apply Rmult_eq_reg_r with (px b - px a); [ | lra ].
          replace (((1 - (px q - px a) / (px b - px a)) * py a +
                    (px q - px a) / (px b - px a) * py b) * (px b - px a))
            with (py a * (px b - px q) + py b * (px q - px a)) by (field; lra).
          nra.
      - destruct (Rlt_dec (px q) (px a)) as [Hok | Hge]; [ exact Hok | ].
        exfalso. apply Hoff.
        exists ((px q - px a) / (px b - px a)).
        assert (Hd : px b - px a <> 0) by lra.
        split; [ split | split ].
        + apply Rmult_le_reg_r with (px b - px a); [ lra | ].
          replace ((px q - px a) / (px b - px a) * (px b - px a))
            with (px q - px a) by (field; lra). lra.
        + apply Rmult_le_reg_r with (px b - px a); [ lra | ].
          replace ((px q - px a) / (px b - px a) * (px b - px a))
            with (px q - px a) by (field; lra). lra.
        + apply Rmult_eq_reg_r with (px b - px a); [ | lra ].
          replace (((1 - (px q - px a) / (px b - px a)) * px a +
                    (px q - px a) / (px b - px a) * px b) * (px b - px a))
            with (px a * (px b - px q) + px b * (px q - px a)) by (field; lra).
          nra.
        + apply Rmult_eq_reg_r with (px b - px a); [ | lra ].
          replace (((1 - (px q - px a) / (px b - px a)) * py a +
                    (px q - px a) / (px b - px a) * py b) * (px b - px a))
            with (py a * (px b - px q) + py b * (px q - px a)) by (field; lra).
          nra. }
    assert (HELa : eastlevel q a <-> px q < px a)
      by (unfold eastlevel; split; [ intros [_ ?]; assumption
                                   | intro; split; [ exact Hya | assumption ] ]).
    assert (HELb : eastlevel q b <-> px q < px b)
      by (unfold eastlevel; split; [ intros [_ ?]; assumption
                                   | intro; split; [ exact Hyb | assumption ] ]).
    tauto.
  - (* V: ya = h < yb : ascending BOTTOM at the level *)
    assert (Hab : py a < py b) by lra.
    assert (HELb : ~ eastlevel q b) by (intros [He _]; lra).
    assert (HELa : eastlevel q a <-> px q < px a)
      by (unfold eastlevel; split; [ intros [_ ?]; assumption
                                   | intro; split; [ exact Hya | assumption ] ]).
    assert (Hcq : edge_crosses_ray_ho q (a, b) <-> px q < px a).
    { rewrite (ho_asc_iff a b q Hab). split.
      - intros [_ HP]. nra.
      - intro Hlt. split; [ lra | nra ]. }
    exists 1. split; [ lra | ].
    intros q' Hx Hh.
    assert (Hnc' : ~ edge_crosses_ray_ho q' (a, b))
      by (intros [[[Hu1 Hu2] _] | [[Hu1 Hu2] _]]; lra).
    tauto.
  - (* IV: yb < h < ya : strict descending band, stable *)
    assert (Hab : py b < py a) by lra.
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
    assert (HELa : ~ eastlevel q a) by (intros [He _]; lra).
    assert (HELb : ~ eastlevel q b) by (intros [He _]; lra).
    destruct (Rtotal_order 0 PD) as [HPDp | [HPDz | HPDn]];
      [ | exfalso; exact (HPD (eq_sym HPDz)) | ].
    + destruct (affine_sign_stable
                  (- (py a - py b)) (px a - px b)
                  ((py a - py b) * px b - (px a - px b) * py b)
                  (px q) (py q) ltac:(unfold PD in HPDp; nra))
        as [e3 [He3 Hb3]].
      exists (Rmin e3 (py q - py b)). split.
      * apply Rmin_glb_lt; lra.
      * intros q' Hx Hh.
        pose proof (Rmin_l e3 (py q - py b)).
        pose proof (Rmin_r e3 (py q - py b)).
        assert (Hx3 : Rabs (px q' - px q) < e3) by lra.
        assert (Hh3 : Rabs (py q' - py q) < e3)
          by (unfold Rabs; destruct (Rcase_abs (py q' - py q)); lra).
        pose proof (Hb3 (px q') (py q') Hx3 Hh3) as S3.
        assert (Hc' : edge_crosses_ray_ho q' (a, b))
          by (apply (ho_desc_iff a b q' Hab); split; [ lra | nra ]).
        assert (Hc : edge_crosses_ray_ho q (a, b))
          by (apply (ho_desc_iff a b q Hab); split; [ lra | unfold PD in *; nra ]).
        tauto.
    + destruct (affine_sign_stable
                  (py a - py b) (- (px a - px b))
                  (- ((py a - py b) * px b - (px a - px b) * py b))
                  (px q) (py q) ltac:(unfold PD in HPDn; nra))
        as [e3 [He3 Hb3]].
      exists e3. split; [ lra | ].
      intros q' Hx Hh.
      assert (Hh3 : Rabs (py q' - py q) < e3)
        by (unfold Rabs; destruct (Rcase_abs (py q' - py q)); lra).
      pose proof (Hb3 (px q') (py q') Hx Hh3) as S3.
      assert (Hnc' : ~ edge_crosses_ray_ho q' (a, b))
        by (rewrite (ho_desc_iff a b q' Hab); intros [Hu HP]; nra).
      assert (Hnc : ~ edge_crosses_ray_ho q (a, b))
        by (rewrite (ho_desc_iff a b q Hab); intros [Hu HP];
            unfold PD in *; nra).
      tauto.
  - (* VII: yb = h < ya : descending BOTTOM at the level *)
    assert (Hab : py b < py a) by lra.
    assert (HELa : ~ eastlevel q a) by (intros [He _]; lra).
    assert (HELb : eastlevel q b <-> px q < px b)
      by (unfold eastlevel; split; [ intros [_ ?]; assumption
                                   | intro; split; [ exact Hyb | assumption ] ]).
    assert (Hcq : edge_crosses_ray_ho q (a, b) <-> px q < px b).
    { rewrite (ho_desc_iff a b q Hab). split.
      - intros [_ HP]. nra.
      - intro Hlt. split; [ lra | nra ]. }
    exists 1. split; [ lra | ].
    intros q' Hx Hh.
    assert (Hnc' : ~ edge_crosses_ray_ho q' (a, b))
      by (intros [[[Hu1 Hu2] _] | [[Hu1 Hu2] _]]; lra).
    tauto.
  - (* II: h < ya, h < yb : dead on both sides *)
    exists 1. split; [ lra | ].
    intros q' Hx Hh.
    assert (Hnc' : ~ edge_crosses_ray_ho q' (a, b))
      by (intros [[[Hu1 Hu2] _] | [[Hu1 Hu2] _]]; lra).
    assert (Hnc : ~ edge_crosses_ray_ho q (a, b))
      by (intros [[[Hu1 Hu2] _] | [[Hu1 Hu2] _]]; lra).
    assert (Ha : ~ eastlevel q a) by (intros [He _]; lra).
    assert (Hb : ~ eastlevel q b) by (intros [He _]; lra).
    tauto.
Qed.

(* ---------------------------------------------------------------------------
   §3  Uniform radius over the edge list.
   --------------------------------------------------------------------------- *)

Lemma ho_lower_eps_all : forall (q : Point) (es : list Edge),
  (forall e, In e es ->
     ~ exists t : R, 0 <= t <= 1 /\
         px q = (1 - t) * px (fst e) + t * px (snd e) /\
         py q = (1 - t) * py (fst e) + t * py (snd e)) ->
  exists eps, 0 < eps /\
    forall e, In e es ->
      forall q' : Point,
        Rabs (px q' - px q) < eps -> py q - eps < py q' < py q ->
        ((edge_crosses_ray_ho q' e <-> edge_crosses_ray_ho q e)
           <-> (eastlevel q (fst e) <-> eastlevel q (snd e))).
Proof.
  intros q; induction es as [| [a b] es' IH]; intros Hoff.
  - exists 1. split; [ lra | ]. intros e [].
  - destruct (ho_cross_lower_flag a b q (Hoff (a, b) (or_introl eq_refl)))
      as [e1 [He1 Hb1]].
    destruct (IH (fun e He => Hoff e (or_intror He))) as [e2 [He2 Hb2]].
    exists (Rmin e1 e2). split; [ apply Rmin_glb_lt; lra | ].
    intros e Hin q' Hx Hh.
    pose proof (Rmin_l e1 e2). pose proof (Rmin_r e1 e2).
    destruct Hin as [He | Hin].
    + subst e. cbn [fst snd]. apply Hb1; [ lra | lra ].
    + apply (Hb2 e Hin); [ lra | lra ].
Qed.

(* ---------------------------------------------------------------------------
   §4  The telescoping walk: total jump = flag flip start-to-end.
   --------------------------------------------------------------------------- *)

Lemma ho_jump_walk : forall (q q' : Point) (l : list Point) (v : Point),
  (forall e, In e (ring_edges (v :: l)) ->
     ((edge_crosses_ray_ho q' e <-> edge_crosses_ray_ho q e)
        <-> (eastlevel q (fst e) <-> eastlevel q (snd e)))) ->
  ((ho_parity_odd q' (ring_edges (v :: l))
      <-> ho_parity_odd q (ring_edges (v :: l)))
     <-> (eastlevel q v <-> eastlevel q (last l v))).
Proof.
  intros q q' l. induction l as [| w l' IH]; intros v Hhyp.
  - cbn [ring_edges last]. split.
    + intros _. tauto.
    + intros _. split; intro H; inversion H.
  - assert (Hhd := Hhyp (v, w) (or_introl eq_refl)).
    cbn [fst snd] in Hhd.
    assert (Hhyp' : forall e, In e (ring_edges (w :: l')) ->
       ((edge_crosses_ray_ho q' e <-> edge_crosses_ray_ho q e)
          <-> (eastlevel q (fst e) <-> eastlevel q (snd e))))
      by (intros e He; apply Hhyp; right; exact He).
    pose proof (IH w Hhyp') as IHw.
    assert (Hlast : last (w :: l') v = last l' w).
    { destruct l' as [| u l'']; [ reflexivity | ].
      cbn [last]. apply last_irrel. }
    cbn [ring_edges]. rewrite Hlast.
    (* decide everything *)
    assert (Eq' : ho_parity_even q' (ring_edges (w :: l'))
                    <-> ~ ho_parity_odd q' (ring_edges (w :: l'))).
    { split.
      - intros He Ho; exact (ho_parity_excl _ _ Ho He).
      - intro Hn. destruct (ho_parity_dec q' (ring_edges (w :: l')));
          [ exact (False_ind _ (Hn h)) | assumption ]. }
    assert (Eq : ho_parity_even q (ring_edges (w :: l'))
                    <-> ~ ho_parity_odd q (ring_edges (w :: l'))).
    { split.
      - intros He Ho; exact (ho_parity_excl _ _ Ho He).
      - intro Hn. destruct (ho_parity_dec q (ring_edges (w :: l')));
          [ exact (False_ind _ (Hn h)) | assumption ]. }
    destruct (edge_crosses_ray_ho_dec q' (v, w)) as [Hc' | Hn'];
    destruct (edge_crosses_ray_ho_dec q (v, w)) as [Hc | Hn].
    + rewrite (ho_odd_cons_cross _ _ _ Hc'), (ho_odd_cons_cross _ _ _ Hc).
      rewrite Eq', Eq.
      destruct (eastlevel_dec q v); destruct (eastlevel_dec q w);
      destruct (eastlevel_dec q (last l' w));
      destruct (ho_parity_dec q' (ring_edges (w :: l'))) as [HO' | HE'];
      destruct (ho_parity_dec q (ring_edges (w :: l'))) as [HO | HE];
      try pose proof (fun Ho => ho_parity_excl q' _ Ho HE');
      try pose proof (fun Ho => ho_parity_excl q _ Ho HE);
      tauto.
    + rewrite (ho_odd_cons_cross _ _ _ Hc'), (ho_odd_cons_skip _ _ _ Hn).
      rewrite Eq'.
      destruct (eastlevel_dec q v); destruct (eastlevel_dec q w);
      destruct (eastlevel_dec q (last l' w));
      destruct (ho_parity_dec q' (ring_edges (w :: l'))) as [HO' | HE'];
      destruct (ho_parity_dec q (ring_edges (w :: l'))) as [HO | HE];
      try pose proof (fun Ho => ho_parity_excl q' _ Ho HE');
      try pose proof (fun Ho => ho_parity_excl q _ Ho HE);
      tauto.
    + rewrite (ho_odd_cons_skip _ _ _ Hn'), (ho_odd_cons_cross _ _ _ Hc).
      rewrite Eq.
      destruct (eastlevel_dec q v); destruct (eastlevel_dec q w);
      destruct (eastlevel_dec q (last l' w));
      destruct (ho_parity_dec q' (ring_edges (w :: l'))) as [HO' | HE'];
      destruct (ho_parity_dec q (ring_edges (w :: l'))) as [HO | HE];
      try pose proof (fun Ho => ho_parity_excl q' _ Ho HE');
      try pose proof (fun Ho => ho_parity_excl q _ Ho HE);
      tauto.
    + rewrite (ho_odd_cons_skip _ _ _ Hn'), (ho_odd_cons_skip _ _ _ Hn).
      destruct (eastlevel_dec q v); destruct (eastlevel_dec q w);
      destruct (eastlevel_dec q (last l' w));
      destruct (ho_parity_dec q' (ring_edges (w :: l'))) as [HO' | HE'];
      destruct (ho_parity_dec q (ring_edges (w :: l'))) as [HO | HE];
      try pose proof (fun Ho => ho_parity_excl q' _ Ho HE');
      try pose proof (fun Ho => ho_parity_excl q _ Ho HE);
      tauto.
Qed.

(* Around a CLOSED ring the flag returns home: the parities agree. *)
Lemma ho_jump_closed : forall (q q' : Point) (r : Ring),
  ring_closed r ->
  (forall e, In e (ring_edges r) ->
     ((edge_crosses_ray_ho q' e <-> edge_crosses_ray_ho q e)
        <-> (eastlevel q (fst e) <-> eastlevel q (snd e)))) ->
  (ho_parity_odd q' (ring_edges r) <-> ho_parity_odd q (ring_edges r)).
Proof.
  intros q q' r [v [ls Heq]] Hhyp. subst r.
  pose proof (ho_jump_walk q q' (ls ++ [v]) v Hhyp) as Hw.
  rewrite last_app_single in Hw.
  tauto.
Qed.

(* ---------------------------------------------------------------------------
   §5  THE KERNEL IS A THEOREM -- and the trapped half closes.
   --------------------------------------------------------------------------- *)

Theorem ho_level_jump_holds : forall (r : Ring),
  ring_closed r -> ho_level_jump r.
Proof.
  intros r Hclosed q Hcompl _.
  destruct (ho_lower_eps_all q (ring_edges r)) as [eps [Heps Hball]].
  { intros e He Hex. apply Hcompl.
    destruct Hex as [t [[Ht1 Ht2] [Hx Hy]]].
    exists e, t. repeat split; assumption. }
  exists eps. split; [ exact Heps | ].
  intros q' Hx Hh _.
  unfold point_in_ring_ho.
  apply (ho_jump_closed q q' r Hclosed).
  intros e He. exact (Hball e He q' Hx Hh).
Qed.

(* ============================================================================
   THE TRAPPED HALF OF THE POLYGONAL JORDAN CURVE THEOREM, UNCONDITIONALLY:
   an odd-parity point with the rightward-ray guard is confined to a bounded
   complement component of ANY closed ring.  (ring_simple is not needed.)
   ============================================================================ *)

Theorem odd_parity_trapped : forall (r : Ring) (p : Point),
  ring_closed r ->
  ray_avoids_vertices p r ->
  point_in_ring p r ->
  in_bounded_component_cont r p.
Proof.
  intros r p Hclosed Hrav Hpir.
  apply (odd_parity_trapped_of_level_jump r p Hclosed); try assumption.
  apply ho_level_jump_holds. exact Hclosed.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions ho_cross_lower_flag.
Print Assumptions ho_jump_closed.
Print Assumptions ho_level_jump_holds.
Print Assumptions odd_parity_trapped.
