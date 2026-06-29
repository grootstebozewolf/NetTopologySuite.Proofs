(* ============================================================================
   NetTopologySuite.Proofs.RingComplementOpen
   ----------------------------------------------------------------------------
   The complement of a ring's boundary image is OPEN: an off-ring point has a
   whole ball of off-ring points around it.  This is the geometric foundation
   the half-open ESCAPE migration needs -- it lets a non-generic even-parity
   complement point be perturbed to a nearby GENERIC complement point in the
   same component (no point-to-segment distance machinery existed in the corpus).

   Built bottom-up:
     - `dist_sq_to_seg_lower` : for a point P off a segment [a,b], the closest
       point c on the segment (the clamped projection) is at strictly positive
       distance, and every segment point is at least that far -- a uniform
       positive lower bound on dist_sq.
     - `not_on_edge_imp_ball` : hence a dist-ball around P avoids the edge image.
     - `ring_complement_open` : finite Rmin of the per-edge balls avoids the whole
       ring image.

   Pure-R; classical-reals trio only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents.
Import ListNotations.

Local Open Scope R_scope.

(* On-edge membership for a single edge, matching ring_image's disjunct. *)
Definition on_edge_pt (q : Point) (e : Edge) : Prop :=
  exists t : R, 0 <= t <= 1 /\
    px q = (1 - t) * px (fst e) + t * px (snd e) /\
    py q = (1 - t) * py (fst e) + t * py (snd e).

Lemma ring_image_iff_on_edge : forall r q,
  ring_image r q <-> exists e, In e (ring_edges r) /\ on_edge_pt q e.
Proof.
  intros r q. unfold ring_image, on_edge_pt. split.
  - intros [e [t [Hin [Ht [Hx Hy]]]]]. exists e; split; [exact Hin | exists t; auto].
  - intros [e [Hin [t [Ht [Hx Hy]]]]]. exists e, t; auto.
Qed.

(* The squared distance from P to the segment point at parameter t. *)
Definition seg_dsq (p : Point) (a b : Point) (t : R) : R :=
  (px p - ((1 - t) * px a + t * px b)) * (px p - ((1 - t) * px a + t * px b)) +
  (py p - ((1 - t) * py a + t * py b)) * (py p - ((1 - t) * py a + t * py b)).

(* Closest parameter (clamped projection) and its data. *)
Definition seg_D (a b : Point) : R :=
  (px b - px a) * (px b - px a) + (py b - py a) * (py b - py a).
Definition seg_N (p a b : Point) : R :=
  (px b - px a) * (px p - px a) + (py b - py a) * (py p - py a).

Lemma seg_D_nonneg : forall a b, 0 <= seg_D a b.
Proof. intros a b. unfold seg_D. apply Rplus_le_le_0_compat; apply sqr_nonneg. Qed.

Lemma seg_dsq_nonneg : forall p a b t, 0 <= seg_dsq p a b t.
Proof. intros. unfold seg_dsq. apply Rplus_le_le_0_compat; apply sqr_nonneg. Qed.

Lemma seg_dsq_zero_split : forall p a b t,
  seg_dsq p a b t = 0 ->
  px p = (1 - t) * px a + t * px b /\ py p = (1 - t) * py a + t * py b.
Proof.
  intros p a b t H. unfold seg_dsq in H.
  set (u := px p - ((1 - t) * px a + t * px b)) in *.
  set (v := py p - ((1 - t) * py a + t * py b)) in *.
  pose proof (sqr_nonneg u). pose proof (sqr_nonneg v).
  assert (Hu : u * u = 0) by lra.
  assert (Hv : v * v = 0) by lra.
  apply sqr_eq_zero in Hu. apply sqr_eq_zero in Hv.
  unfold u, v in *. split; lra.
Qed.

(* From N/D < 0 (resp. > 1) and 0 < D, recover the sign of N. *)
Lemma N_neg_of_quot_neg : forall p a b,
  0 < seg_D a b -> seg_N p a b / seg_D a b < 0 -> seg_N p a b < 0.
Proof.
  intros p a b HD Hq.
  assert (Heq : seg_N p a b = (seg_N p a b / seg_D a b) * seg_D a b) by (field; lra).
  nra.
Qed.

Lemma N_gt_D_of_quot_gt : forall p a b,
  0 < seg_D a b -> 1 < seg_N p a b / seg_D a b -> seg_D a b < seg_N p a b.
Proof.
  intros p a b HD Hq.
  assert (Heq : seg_N p a b = (seg_N p a b / seg_D a b) * seg_D a b) by (field; lra).
  nra.
Qed.

(* For a NON-degenerate edge, the clamped projection minimizes seg_dsq over [0,1]
   and is strictly positive when P is off the segment. *)
Lemma seg_dsq_lower_nondeg : forall p a b,
  0 < seg_D a b ->
  ~ on_edge_pt p (a, b) ->
  exists m, 0 < m /\ forall t, 0 <= t <= 1 -> m <= seg_dsq p a b t.
Proof.
  intros p a b HD Hoff.
  set (tc := Rmax 0 (Rmin 1 (seg_N p a b / seg_D a b))) in *.
  assert (Htc : 0 <= tc <= 1).
  { unfold tc. split; [ apply Rmax_l | apply Rmax_lub; [ lra | apply Rmin_l ] ]. }
  exists (seg_dsq p a b tc). split.
  - (* 0 < m : else P would be on the segment at tc *)
    destruct (Rle_lt_or_eq_dec 0 _ (seg_dsq_nonneg p a b tc)) as [Hlt | Heq];
      [ exact Hlt | ].
    exfalso. apply Hoff. exists tc. split; [ exact Htc | ].
    cbn [fst snd]. apply seg_dsq_zero_split. symmetry. exact Heq.
  - (* tc minimizes seg_dsq over [0,1] *)
    intros t Ht.
    cut (0 <= seg_dsq p a b t - seg_dsq p a b tc); [ lra | ].
    pose proof (seg_D_nonneg a b) as HDn.
    unfold tc.
    destruct (Rle_dec (seg_N p a b / seg_D a b) 1) as [Hle1 | Hgt1].
    + rewrite Rmin_right by exact Hle1.
      destruct (Rle_dec 0 (seg_N p a b / seg_D a b)) as [Hge0 | Hlt0].
      * (* interior: diff = (D t - N)^2 / D >= 0 *)
        rewrite Rmax_right by exact Hge0.
        assert (Hid : seg_dsq p a b t - seg_dsq p a b (seg_N p a b / seg_D a b)
                = (seg_D a b * t - seg_N p a b) * (seg_D a b * t - seg_N p a b)
                    / seg_D a b).
        { unfold seg_dsq, seg_D, seg_N. field. apply Rgt_not_eq.
          unfold seg_D in HD. exact HD. }
        rewrite Hid. apply Rmult_le_pos;
          [ apply sqr_nonneg | left; apply Rinv_0_lt_compat; exact HD ].
      * (* tc = 0; N < 0; diff = t*(D t - 2 N) >= 0 for t in [0,1] *)
        rewrite Rmax_left by lra.
        pose proof (N_neg_of_quot_neg p a b HD (Rnot_le_lt _ _ Hlt0)) as HN.
        replace (seg_dsq p a b t - seg_dsq p a b 0)
          with (t * (seg_D a b * t - 2 * seg_N p a b))
          by (unfold seg_dsq, seg_D, seg_N; ring).
        apply Rmult_le_pos; [ lra | ].
        assert (0 <= seg_D a b * t) by (apply Rmult_le_pos; lra). lra.
    + (* tc = 1; N > D; diff = (1-t)*(2 N - D t - D) >= 0 for t in [0,1] *)
      rewrite Rmin_left by (apply Rlt_le, Rnot_le_lt; exact Hgt1).
      rewrite Rmax_right by lra.
      pose proof (N_gt_D_of_quot_gt p a b HD (Rnot_le_lt _ _ Hgt1)) as HN.
      replace (seg_dsq p a b t - seg_dsq p a b 1)
        with ((1 - t) * (2 * seg_N p a b - seg_D a b * t - seg_D a b))
        by (unfold seg_dsq, seg_D, seg_N; ring).
      apply Rmult_le_pos; [ lra | ].
      assert (HDt : seg_D a b * t <= seg_D a b).
      { rewrite <- (Rmult_1_r (seg_D a b)) at 2.
        apply Rmult_le_compat_l; [ exact HDn | lra ]. }
      lra.
Qed.

(* Degenerate edge a=b: the image is the single point a; off it -> ball. *)
Lemma seg_dsq_lower_deg : forall p a b,
  seg_D a b = 0 ->
  ~ on_edge_pt p (a, b) ->
  exists m, 0 < m /\ forall t, 0 <= t <= 1 -> m <= seg_dsq p a b t.
Proof.
  intros p a b HD Hoff.
  assert (Hab : px b - px a = 0 /\ py b - py a = 0).
  { unfold seg_D in HD. pose proof (sqr_nonneg (px b - px a)).
    pose proof (sqr_nonneg (py b - py a)). split; apply sqr_eq_zero; lra. }
  destruct Hab as [Hxab Hyab].
  exists (seg_dsq p a b 0). split.
  - destruct (Rle_lt_or_eq_dec 0 _ (seg_dsq_nonneg p a b 0)) as [Hlt | Heq];
      [ exact Hlt | ].
    exfalso. apply Hoff. exists 0. split; [ lra | ].
    cbn [fst snd]. apply seg_dsq_zero_split. symmetry. exact Heq.
  - intros t Ht.
    assert (Heqt : seg_dsq p a b t = seg_dsq p a b 0).
    { unfold seg_dsq. assert (px b = px a) by lra. assert (py b = py a) by lra.
      rewrite H, H0. ring. }
    lra.
Qed.

Lemma not_on_edge_imp_ball : forall p a b,
  ~ on_edge_pt p (a, b) ->
  exists eps, 0 < eps /\ forall q, dist p q < eps -> ~ on_edge_pt q (a, b).
Proof.
  intros p a b Hoff.
  destruct (Rle_lt_or_eq_dec 0 (seg_D a b) (seg_D_nonneg a b))
    as [Hpos | Hzero].
  - (* nondegenerate *)
    destruct (seg_dsq_lower_nondeg p a b Hpos Hoff) as [m [Hm Hlb]].
    exists (sqrt m). split.
    + apply sqrt_lt_R0; exact Hm.
    + intros q Hq [t [Ht [Hx Hy]]].
      assert (Hd : dist_sq p q = seg_dsq p a b t).
      { unfold dist_sq, seg_dsq. cbn [fst snd] in *. rewrite Hx, Hy. ring. }
      pose proof (Hlb t Ht) as Hmle.
      pose proof (dist_nonneg p q) as Hdn.
      pose proof (dist_mul_self p q) as Hms.
      pose proof (sqrt_sqrt m (Rlt_le _ _ Hm)) as Hsm.
      assert (Hsq : dist p q * dist p q < sqrt m * sqrt m)
        by (apply Rmult_le_0_lt_compat; lra).
      lra.
  - (* degenerate *)
    destruct (seg_dsq_lower_deg p a b (eq_sym Hzero) Hoff) as [m [Hm Hlb]].
    exists (sqrt m). split.
    + apply sqrt_lt_R0; exact Hm.
    + intros q Hq [t [Ht [Hx Hy]]].
      assert (Hd : dist_sq p q = seg_dsq p a b t).
      { unfold dist_sq, seg_dsq. cbn [fst snd] in *. rewrite Hx, Hy. ring. }
      pose proof (Hlb t Ht) as Hmle.
      pose proof (dist_nonneg p q) as Hdn.
      pose proof (dist_mul_self p q) as Hms.
      pose proof (sqrt_sqrt m (Rlt_le _ _ Hm)) as Hsm.
      assert (Hsq : dist p q * dist p q < sqrt m * sqrt m)
        by (apply Rmult_le_0_lt_compat; lra).
      lra.
Qed.

(* A ball avoiding every edge of a finite list. *)
Lemma off_edges_imp_ball : forall (L : list Edge) (p : Point),
  (forall e, In e L -> ~ on_edge_pt p e) ->
  exists eps, 0 < eps /\
    forall q, dist p q < eps -> forall e, In e L -> ~ on_edge_pt q e.
Proof.
  induction L as [| e es IH]; intros p Hoff.
  - exists 1. split; [ lra | ]. intros q _ e [].
  - destruct e as [a b].
    destruct (not_on_edge_imp_ball p a b (Hoff (a, b) (or_introl eq_refl)))
      as [eps1 [He1 Hb1]].
    destruct (IH p (fun f Hf => Hoff f (or_intror Hf))) as [eps2 [He2 Hb2]].
    exists (Rmin eps1 eps2). split; [ apply Rmin_glb_lt; lra | ].
    intros q Hq f Hf.
    destruct Hf as [<- | Hf].
    + apply (Hb1 q). eapply Rlt_le_trans; [ exact Hq | apply Rmin_l ].
    + apply (Hb2 q); [ eapply Rlt_le_trans; [ exact Hq | apply Rmin_r ] | exact Hf ].
Qed.

(* The complement of the ring image is open. *)
Theorem ring_complement_open : forall r p,
  ring_complement r p ->
  exists eps, 0 < eps /\ forall q, dist p q < eps -> ring_complement r q.
Proof.
  intros r p Hp.
  assert (Hoff : forall e, In e (ring_edges r) -> ~ on_edge_pt p e).
  { intros e He Hone. apply Hp. apply ring_image_iff_on_edge. exists e; auto. }
  destruct (off_edges_imp_ball (ring_edges r) p Hoff) as [eps [Heps Hball]].
  exists eps. split; [ exact Heps | ].
  intros q Hq Himg. apply ring_image_iff_on_edge in Himg.
  destruct Himg as [e [He Hone]]. exact (Hball q Hq e He Hone).
Qed.

Print Assumptions ring_complement_open.
