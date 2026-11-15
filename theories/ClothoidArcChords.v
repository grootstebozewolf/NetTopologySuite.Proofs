(* ============================================================================
   NetTopologySuite.Proofs.ClothoidArcChords
   ----------------------------------------------------------------------------
   Arc-preserving approximation of a host clothoid window, realised as
   chords, with an end-to-end Hausdorff budget.

   This is not a better linearization theorem.  For a polyline tolerance
   alone, ClothoidLinearizeContract.clothoid_linearizes is tighter at the
   same vertex count and its vertices lie on the clothoid.  The point here
   is the intermediate object: the heading-interpolating arc spline S of
   ClothoidArcSpline, kept as arcs, with chords P as a downstream
   realisation.  The statement keeps the two budgets apart:

     d_H(C, P) <= d_H(C, S) + d_H(S, P)
               <= (b - a)^3 / (8 A^2 N^2) + r_max * (1 - cos (step / 2)).

     * C  cac_window_shape   the clothoid on the station window [a, b].
     * S  cac_spline_shape   the N pieces cas_piece, unchanged.
     * P  poly_shape (cac_pts ..)  the chords of every piece, one list.
     * eps  any bound with (b - a)^3 <= 8 A^2 N^2 eps
            (ClothoidArcSpline.cas_arc_spline_within_eps / _cover).
     * cac_tol = cac_rmax * (1 - cos (step / 2)), cac_rmax the largest
       piece radius 1 / |kappa_k| (0 for a straight piece)
       (ArcLinearizeContract.arc_linearize_hausdorff, reused unchanged).

   Discretisation.  One angular step for all arcs; piece k gets
   subdiv_n step (kappa_k h) chords, the count the arc contract uses.
   No fixed chords-per-arc parameter.

   Bridge (cac_piece_eval).  A piece with curvature kappa <> 0, start Q
   and heading phi is exactly the CircularEgg with centre Q + n / kappa
   (n the left normal), radius 1 / |kappa|, start angle
   phi - sign(kappa) PI / 2 and sweep kappa h:
     cas_piece c a h k (x_k + t h) = circ_eval (cac_egg c a h k) t.
   It is an equality of points for every t; cas_piece is not modified or
   re-parameterised.  A piece with kappa = 0 is the segment between its
   end points and is its own chord (tolerance 0).  The heading angle is
   Atan2.atan2 of the frame vector; Stdlib atan prints classic.

   Hypotheses of the headline beyond cloth_wf, a < b, N <> 0:
     * 0 < step <= 2 PI                      (from the arc contract);
     * |kappa_k h| <= 2 PI for every piece   (from the arc contract: a
       piece may not wind more than once).
   clothoid_arc_spline_chords_hausdorff_window replaces the second by a
   condition on the window alone,
     max(|a|, |b|) * (b - a) <= 2 PI * N * A^2   (cac_sweep_bound).

   Two chord budgets for the same polyline cac_pts.

   clothoid_arc_spline_chords_closed_form (use this one):
     d_H(C, P) <= eps + max(|a|, |b|) (b - a)^2 / (32 A^2 N^2).
   The chord term is cac_chord_budget.  It has no radius in it, so it is
   continuous through the inflection and decreases in N, and it does not
   depend on step: step only chooses how many chords each arc gets (at
   least two).  It comes from
   ArcLinearizeContract.arc_linearize_hausdorff_subtended, which bounds a
   chord by the angle |kappa_k h| / n_k it subtends, with
   1 - cos x <= x^2 / 2, n_k >= 2 and |kappa_k| <= max(|a|, |b|) / A^2.
   Its only winding premise is the window one above.

   clothoid_arc_spline_chords_hausdorff (the witness of the claim):
     d_H(C, P) <= eps + cac_rmax * (1 - cos (step / 2)).
   CAVEAT for this form only: it degenerates near the inflection.
   kappa_k is sigma * m_k / A^2 with m_k = x_k + h / 2, so the piece
   radius is A^2 / |m_k| and cac_rmax = A^2 / min |m_k|.  For a window
   that contains or approaches station 0 it is unbounded: with a = 0,
   cac_tol is about A^2 step^2 / (4 h), which GROWS with N.  The
   statement is true and exact, and close to vacuous there.  It bounds a
   chord by the nominal angle step; it is the better of the two only
   when step is small against |kappa_k h| / n_k on every piece.

   Not here: no Linearizes instance (chord vertices lie on the arcs, up
   to eps from the clothoid, so lz_on_curve fails); no binary64; no
   bridge to the (k0, k1, L) parameters of ClothoidResidual; no overlay
   theorem.  cac_pts repeats each junction vertex (last point of one
   piece, first of the next); the extra segment is a point.

   claimId: 0007-clothoid-arc-spline-chords.
   witness: clothoid_arc_spline_chords_hausdorff.
   3-axiom host.  No Admitted / Axiom / Parameter.  No MVT, RiemannInt.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude Code
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List.
From NTS.Proofs Require Import Distance Atan2 Linearise LinearizeContract.
From NTS.Proofs Require Import SheetHenCircEgg ArcLinearize ArcLinearizeBound
  ArcLinearizeContract.
From NTS.Proofs Require Import SheetHenClothoidCore SheetHenClothoidBounds
  ClothoidTangent ClothoidArcSpline.
Local Open Scope R_scope.

(* ---- Hausdorff composition on Shape -------------------------------------- *)

Lemma within_eps_trans :
  forall (A B C : Shape) e1 e2,
    within_eps A B e1 -> within_eps B C e2 -> within_eps A C (e1 + e2).
Proof.
  intros A B C e1 e2 HAB HBC p Hp.
  destruct (HAB p Hp) as [q [Hq Hpq]].
  destruct (HBC q Hq) as [r [Hr Hqr]].
  exists r. split; [exact Hr|].
  pose proof (dist_triangle p q r). lra.
Qed.

Lemma hausdorff_le_trans :
  forall (A B C : Shape) e1 e2,
    hausdorff_le A B e1 -> hausdorff_le B C e2 -> hausdorff_le A C (e1 + e2).
Proof.
  intros A B C e1 e2 [HAB HBA] [HBC HCB]. split.
  - apply (within_eps_trans A B C); assumption.
  - rewrite Rplus_comm. apply (within_eps_trans C B A); assumption.
Qed.

Lemma within_eps_weaken :
  forall (A B : Shape) e e', e <= e' -> within_eps A B e -> within_eps A B e'.
Proof.
  intros A B e e' He H p Hp. destruct (H p Hp) as [q [Hq Hd]].
  exists q. split; [exact Hq | lra].
Qed.

(* ---- a nonzero-curvature piece is a CircularEgg arc ---------------------- *)

Definition cac_sign (kap : R) : R := if Rle_dec 0 kap then 1 else -1.

Definition cac_arc_egg (Q : Point) (phi kap h : R) : CircularEgg :=
  mkCircularEgg
    (mkPoint (px Q - sin phi / kap) (py Q + cos phi / kap))
    (cac_sign kap / kap)
    (phi - cac_sign kap * (PI / 2))
    (kap * h).

Lemma cac_arc_egg_eval :
  forall Q phi kap h t, kap <> 0 ->
    circ_eval (cac_arc_egg Q phi kap h) t
    = cas_arc_pt Q (cos phi) (sin phi) kap (t * h).
Proof.
  intros Q phi kap h t Hk.
  unfold circ_eval, cac_arc_egg, cas_arc_pt, cas_arc_X, cas_arc_Y, cac_sign.
  cbn [circ_o circ_r circ_theta0 circ_sweep px py].
  destruct (Req_EM_T kap 0) as [Hz|_]; [contradiction|].
  replace (kap * (t * h)) with (t * (kap * h)) by ring.
  set (y := t * (kap * h)).
  destruct (Rle_dec 0 kap) as [Hp|Hn].
  - replace (phi - 1 * (PI / 2) + y) with ((phi + y) - PI / 2) by ring.
    rewrite cos_minus, sin_minus, cos_PI2, sin_PI2, sin_plus, cos_plus.
    f_equal; field; exact Hk.
  - replace (phi - -1 * (PI / 2) + y) with ((phi + y) + PI / 2) by ring.
    rewrite (cos_plus (phi + y)), (sin_plus (phi + y)), cos_PI2, sin_PI2,
      sin_plus, cos_plus.
    f_equal; field; exact Hk.
Qed.

Lemma cac_arc_egg_r_nn : forall Q phi kap h, kap <> 0 ->
  0 <= circ_r (cac_arc_egg Q phi kap h).
Proof.
  intros Q phi kap h Hk. unfold cac_arc_egg, cac_sign. cbn [circ_r].
  destruct (Rle_dec 0 kap) as [Hp|Hn].
  - apply Rlt_le. apply Rdiv_lt_0_compat; lra.
  - replace (-1 / kap) with (1 / - kap) by (field; exact Hk).
    apply Rlt_le. apply Rdiv_lt_0_compat; lra.
Qed.

(* Heading of the clothoid frame as an angle (corpus atan2, no classic). *)
Definition cac_phi0 (c : ClothoidEgg) : R := atan2 (cloth_sin0 c) (cloth_cos0 c).

Lemma cac_phi0_ok : forall c, cloth_h2 c <> 0 ->
  cos (cac_phi0 c) = cloth_cos0 c /\ sin (cac_phi0 c) = cloth_sin0 c.
Proof.
  intros c Hh. pose proof (cloth_frame_sumsq c Hh) as Hs.
  assert (Hnz : ~ (cloth_cos0 c = 0 /\ cloth_sin0 c = 0)).
  { intros [H1 H2]. rewrite H1, H2 in Hs. lra. }
  unfold cac_phi0.
  rewrite (cos_atan2 _ _ Hnz), (sin_atan2 _ _ Hnz), Hs, sqrt_1.
  split; field.
Qed.

Lemma cac_tangent_angle : forall c s, cloth_h2 c <> 0 ->
  cloth_vx c s = cos (cac_phi0 c + cloth_psi c s) /\
  cloth_vy c s = sin (cac_phi0 c + cloth_psi c s).
Proof.
  intros c s Hh. destruct (cac_phi0_ok c Hh) as [Hc Hs].
  unfold cloth_vx, cloth_vy. rewrite cos_plus, sin_plus, Hc, Hs. split; ring.
Qed.

Definition cac_egg (c : ClothoidEgg) (a h : R) (k : nat) : CircularEgg :=
  cac_arc_egg (cas_start c a h k)
    (cac_phi0 c + cloth_psi c (cas_node a h k))
    (cas_kap c (cas_node a h k) h) h.

(* The bridge: piece k at station x_k + t h is the arc at parameter t. *)
Lemma cac_piece_eval :
  forall c a h k t, cloth_h2 c <> 0 ->
    cas_kap c (cas_node a h k) h <> 0 ->
    cas_piece c a h k (cas_node a h k + t * h) = circ_eval (cac_egg c a h k) t.
Proof.
  intros c a h k t Hh Hk. unfold cac_egg.
  rewrite (cac_arc_egg_eval _ _ _ h t Hk).
  destruct (cac_tangent_angle c (cas_node a h k) Hh) as [Hx Hy].
  unfold cas_piece. rewrite Hx, Hy.
  replace (cas_node a h k + t * h - cas_node a h k) with (t * h) by ring.
  reflexivity.
Qed.

(* ---- shapes --------------------------------------------------------------- *)

(* The clothoid on the station window [a, b]. *)
Definition cac_window_shape (c : ClothoidEgg) (a b : R) : Shape :=
  fun p => exists u, a <= u <= b /\ p = cloth_P c u.

Definition cac_piece_shape (c : ClothoidEgg) (a h : R) (k : nat) : Shape :=
  fun p => exists u,
    cas_node a h k <= u <= cas_node a h (S k) /\ p = cas_piece c a h k u.

(* The arc spline: the union of its N pieces. *)
Definition cac_spline_shape (c : ClothoidEgg) (a b : R) (N : nat) : Shape :=
  fun p => exists k, (k < N)%nat /\ cac_piece_shape c a (cas_step a b N) k p.

(* Chords of piece k.  A zero-curvature piece is a segment and is its own
   chord; any other piece is the existing uniform arc densifier at the
   angular step. *)
Definition cac_piece_pts (c : ClothoidEgg) (a h step : R) (k : nat)
  : list Point :=
  if Req_EM_T (cas_kap c (cas_node a h k) h) 0
  then cas_start c a h k :: cas_start c a h (S k) :: nil
  else lin_pts (cac_egg c a h k)
         (subdiv_n step (circ_sweep (cac_egg c a h k))).

Definition cac_chords_shape (c : ClothoidEgg) (a b : R) (N : nat) (step : R)
  : Shape :=
  fun p => exists k, (k < N)%nat /\
    poly_shape (cac_piece_pts c a (cas_step a b N) step k) p.

(* Radius of piece k (0 for a segment), and the largest over k < N. *)
Definition cac_r (c : ClothoidEgg) (a h : R) (k : nat) : R :=
  if Req_EM_T (cas_kap c (cas_node a h k) h) 0 then 0
  else circ_r (cac_egg c a h k).

Fixpoint cac_rmax (c : ClothoidEgg) (a h : R) (N : nat) : R :=
  match N with
  | O => 0
  | S n => Rmax (cac_rmax c a h n) (cac_r c a h n)
  end.

Lemma cac_r_le_rmax : forall c a h N k, (k < N)%nat ->
  cac_r c a h k <= cac_rmax c a h N.
Proof.
  intros c a h N. induction N as [|n IH]; intros k Hk; [lia|].
  cbn [cac_rmax]. destruct (Nat.eq_dec k n) as [->|Hne].
  - apply Rmax_r.
  - eapply Rle_trans; [apply IH; lia | apply Rmax_l].
Qed.

(* ---- union lifting -------------------------------------------------------- *)

Lemma within_eps_union :
  forall (I : nat -> Prop) (A B : nat -> Shape) e,
    (forall k, I k -> within_eps (A k) (B k) e) ->
    within_eps (fun p => exists k, I k /\ A k p)
               (fun p => exists k, I k /\ B k p) e.
Proof.
  intros I A B e H p [k [Hk Hp]].
  destruct (H k Hk p Hp) as [q [Hq Hd]].
  exists q. split; [exists k; split; assumption | exact Hd].
Qed.

(* ---- one piece against its chords ---------------------------------------- *)

Lemma cac_node_step : forall a h k, cas_node a h (S k) = cas_node a h k + h.
Proof. intros. apply cas_node_S. Qed.

Lemma cac_cos_gap_nn : forall step, 0 <= 1 - cos (step / 2).
Proof. intro step. pose proof (COS_bound (step / 2)). lra. Qed.

Lemma cac_piece_arc_shape :
  forall c a h k p, cloth_h2 c <> 0 -> 0 < h ->
    cas_kap c (cas_node a h k) h <> 0 ->
    (cac_piece_shape c a h k p <-> curve_shape (circ_eval (cac_egg c a h k)) p).
Proof.
  intros c a h k p Hh Hpos Hk. unfold cac_piece_shape, curve_shape. split.
  - intros [u [Hu Hp]]. rewrite cac_node_step in Hu.
    exists ((u - cas_node a h k) / h). split.
    + split.
      * apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat; exact Hpos].
      * apply Rmult_le_reg_r with h; [exact Hpos|].
        unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra.
    + rewrite <- (cac_piece_eval c a h k _ Hh Hk).
      replace (cas_node a h k + (u - cas_node a h k) / h * h) with u
        by (field; lra).
      exact Hp.
  - intros [t [Ht Hp]]. exists (cas_node a h k + t * h). split.
    + rewrite cac_node_step. split; nra.
    + rewrite (cac_piece_eval c a h k t Hh Hk). exact Hp.
Qed.

Lemma cac_piece_line :
  forall c a h k u, 0 < h ->
    cas_kap c (cas_node a h k) h = 0 ->
    cas_piece c a h k u
    = seg_at (cas_start c a h k) (cas_start c a h (S k))
        ((u - cas_node a h k) / h).
Proof.
  intros c a h k u Hpos Hk.
  cbn [cas_start]. unfold cas_piece, cas_arc_pt, cas_arc_X, cas_arc_Y, seg_at.
  rewrite Hk. destruct (Req_EM_T 0 0) as [_|Hn]; [|exfalso; apply Hn; reflexivity].
  cbn [px py]. f_equal; field; lra.
Qed.

Lemma cac_piece_hausdorff :
  forall c a h step k,
    cloth_h2 c <> 0 -> 0 < h ->
    0 < step <= 2 * PI ->
    Rabs (cas_kap c (cas_node a h k) h * h) <= 2 * PI ->
    hausdorff_le (cac_piece_shape c a h k)
      (poly_shape (cac_piece_pts c a h step k))
      (cac_r c a h k * (1 - cos (step / 2))).
Proof.
  intros c a h step k Hh Hpos Hstep Hsw.
  unfold cac_piece_pts, cac_r.
  destruct (Req_EM_T (cas_kap c (cas_node a h k) h) 0) as [Hz|Hnz].
  - rewrite Rmult_0_l. split.
    + intros p [u [Hu Hp]]. exists p. split; [|rewrite dist_self; lra].
      exists 0%nat, ((u - cas_node a h k) / h), p. split; [cbn; lia|].
      rewrite cac_node_step in Hu. split.
      * split.
        -- apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat; exact Hpos].
        -- apply Rmult_le_reg_r with h; [exact Hpos|].
           unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra.
      * cbn [nth]. rewrite Hp. apply cac_piece_line; assumption.
    + intros q [j [lam [d [Hj [Hlam Hq]]]]]. exists q.
      split; [|rewrite dist_self; lra].
      assert (j = 0%nat) by (cbn in Hj; lia). subst j. cbn [nth] in Hq.
      exists (cas_node a h k + lam * h). split.
      * rewrite cac_node_step. split; nra.
      * rewrite Hq, (cac_piece_line c a h k _ Hpos Hz). f_equal. field. lra.
  - set (e := cac_egg c a h k).
    assert (Hsweep : circ_sweep e = cas_kap c (cas_node a h k) h * h)
      by reflexivity.
    destruct (subdiv_n_ok step (circ_sweep e) (proj1 Hstep))
      as [Hn [_ [Hcount _]]].
    pose proof (arc_linearize_hausdorff e step (subdiv_n step (circ_sweep e))
                  Hn (cac_arc_egg_r_nn _ _ _ _ Hnz) Hstep
                  ltac:(rewrite Hsweep; exact Hsw) Hcount) as [H1 H2].
    split.
    + intros p Hp. apply H1.
      apply (cac_piece_arc_shape c a h k p Hh Hpos Hnz). exact Hp.
    + intros q Hq. destruct (H2 q Hq) as [p [Hp Hd]].
      exists p. split; [|exact Hd].
      apply (cac_piece_arc_shape c a h k p Hh Hpos Hnz). exact Hp.
Qed.

Lemma cac_r_nn : forall c a h k, 0 <= cac_r c a h k.
Proof.
  intros c a h k. unfold cac_r.
  destruct (Req_EM_T (cas_kap c (cas_node a h k) h) 0) as [Hz|Hnz]; [lra|].
  apply cac_arc_egg_r_nn. exact Hnz.
Qed.

(* ---- the arc spline against its chords ----------------------------------- *)

Definition cac_tol (c : ClothoidEgg) (a b : R) (N : nat) (step : R) : R :=
  cac_rmax c a (cas_step a b N) N * (1 - cos (step / 2)).

Lemma cac_step_pos : forall a b N, a < b -> (N <> 0)%nat -> 0 < cas_step a b N.
Proof.
  intros a b N Hab HN. unfold cas_step.
  apply Rdiv_lt_0_compat; [lra | apply lt_0_INR; lia].
Qed.

Theorem cac_spline_chords_hausdorff :
  forall c a b N step,
    cloth_wf c -> a < b -> (N <> 0)%nat ->
    0 < step <= 2 * PI ->
    (forall k, (k < N)%nat ->
       Rabs (cas_kap c (cas_node a (cas_step a b N) k) (cas_step a b N)
             * cas_step a b N) <= 2 * PI) ->
    hausdorff_le (cac_spline_shape c a b N) (cac_chords_shape c a b N step)
      (cac_tol c a b N step).
Proof.
  intros c a b N step Hwf Hab HN Hstep Hsw.
  destruct Hwf as [_ [Hh _]].
  pose proof (cac_step_pos a b N Hab HN) as Hpos.
  assert (Hk : forall k, (k < N)%nat ->
            hausdorff_le (cac_piece_shape c a (cas_step a b N) k)
              (poly_shape (cac_piece_pts c a (cas_step a b N) step k))
              (cac_tol c a b N step)).
  { intros k Hk.
    destruct (cac_piece_hausdorff c a (cas_step a b N) step k Hh Hpos Hstep
                (Hsw k Hk)) as [H1 H2].
    assert (Hle : cac_r c a (cas_step a b N) k * (1 - cos (step / 2))
                  <= cac_tol c a b N step).
    { unfold cac_tol. apply Rmult_le_compat_r; [apply cac_cos_gap_nn|].
      apply cac_r_le_rmax. exact Hk. }
    split; eapply within_eps_weaken; eauto. }
  split.
  - apply (within_eps_union (fun k => (k < N)%nat)
             (cac_piece_shape c a (cas_step a b N))
             (fun k => poly_shape (cac_piece_pts c a (cas_step a b N) step k))).
    intros k Hlt. exact (proj1 (Hk k Hlt)).
  - apply (within_eps_union (fun k => (k < N)%nat)
             (fun k => poly_shape (cac_piece_pts c a (cas_step a b N) step k))
             (cac_piece_shape c a (cas_step a b N))).
    intros k Hlt. exact (proj2 (Hk k Hlt)).
Qed.

(* ---- the clothoid against the arc spline --------------------------------- *)

Lemma cac_node_in_window :
  forall a b N k, a <= b -> (k < N)%nat ->
    a <= cas_node a (cas_step a b N) k /\
    cas_node a (cas_step a b N) (S k) <= b.
Proof.
  intros a b N k Hab Hk.
  assert (HN : (N <> 0)%nat) by lia.
  assert (HNp : 0 < INR N) by (apply lt_0_INR; lia).
  assert (Hh : 0 <= cas_step a b N).
  { unfold cas_step. apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat, HNp]. }
  split.
  - unfold cas_node.
    assert (0 <= INR k * cas_step a b N)
      by (apply Rmult_le_pos; [apply pos_INR | exact Hh]).
    lra.
  - rewrite <- (cas_node_N a b N HN) at 2. unfold cas_node.
    assert (INR (S k) * cas_step a b N <= INR N * cas_step a b N)
      by (apply Rmult_le_compat_r; [exact Hh | apply le_INR; lia]).
    lra.
Qed.

Theorem cac_clothoid_spline_hausdorff :
  forall c a b N eps,
    cloth_wf c -> a <= b -> (N <> 0)%nat ->
    (b - a) * (b - a) * (b - a)
      <= 8 * (cloth_A c * cloth_A c) * (INR N * INR N) * eps ->
    hausdorff_le (cac_window_shape c a b) (cac_spline_shape c a b N) eps.
Proof.
  intros c a b N eps Hwf Hab HN Hgate. split.
  - intros p [u [Hu Hp]].
    destruct (cas_arc_spline_cover c a b N eps Hwf Hab HN Hgate u Hu)
      as [k [Hk [Hr Hd]]].
    exists (cas_piece c a (cas_step a b N) k u). split.
    + exists k. split; [exact Hk|]. exists u. split; [exact Hr | reflexivity].
    + rewrite Hp. exact Hd.
  - intros q [k [Hk [u [Hu Hq]]]].
    exists (cloth_P c u). split.
    + exists u. split; [|reflexivity].
      destruct (cac_node_in_window a b N k Hab Hk). lra.
    + rewrite Hq, dist_sym.
      apply (cas_arc_spline_within_eps c a b N eps Hwf Hab HN Hgate k u Hk Hu).
Qed.

(* ---- composition ---------------------------------------------------------- *)

Theorem clothoid_arc_chords_hausdorff :
  forall c a b N step eps,
    cloth_wf c -> a < b -> (N <> 0)%nat ->
    (b - a) * (b - a) * (b - a)
      <= 8 * (cloth_A c * cloth_A c) * (INR N * INR N) * eps ->
    0 < step <= 2 * PI ->
    (forall k, (k < N)%nat ->
       Rabs (cas_kap c (cas_node a (cas_step a b N) k) (cas_step a b N)
             * cas_step a b N) <= 2 * PI) ->
    hausdorff_le (cac_window_shape c a b) (cac_chords_shape c a b N step)
      (eps + cac_tol c a b N step).
Proof.
  intros c a b N step eps Hwf Hab HN Hgate Hstep Hsw.
  apply (hausdorff_le_trans _ (cac_spline_shape c a b N)).
  - apply cac_clothoid_spline_hausdorff; [exact Hwf | lra | exact HN | exact Hgate].
  - apply cac_spline_chords_hausdorff; assumption.
Qed.

(* ---- the chords as one point list ----------------------------------------- *)

Lemma seg_at_one : forall P Q, seg_at P Q 1 = Q.
Proof. intros [x y] [x' y']. unfold seg_at. cbn. f_equal; ring. Qed.

(* Appending a list that starts where the first one ends adds only a
   degenerate segment at the junction. *)
Lemma poly_shape_app :
  forall (l1 l2 : list Point) q,
    (2 <= length l1)%nat -> (1 <= length l2)%nat ->
    (forall d, nth (length l1 - 1) l1 d = nth 0 l2 d) ->
    (poly_shape (l1 ++ l2) q <-> poly_shape l1 q \/ poly_shape l2 q).
Proof.
  intros l1 l2 q H1 H2 HJ. split.
  - intros [k [lam [d [Hk [Hlam Hq]]]]]. rewrite length_app in Hk.
    destruct (Nat.lt_ge_cases (S k) (length l1)) as [Hlt|Hge].
    + left. exists k, lam, d. split; [exact Hlt|]. split; [exact Hlam|].
      rewrite !app_nth1 in Hq by lia. exact Hq.
    + destruct (Nat.eq_dec (S k) (length l1)) as [He|Hne].
      * left. rewrite (app_nth1 l1 l2 d) in Hq by lia.
        rewrite (app_nth2 l1 l2 d) in Hq by lia.
        replace (S k - length l1)%nat with 0%nat in Hq by lia.
        rewrite <- (HJ d) in Hq.
        replace (length l1 - 1)%nat with k in Hq by lia.
        rewrite seg_at_same in Hq.
        exists (k - 1)%nat, 1, d. split; [lia|]. split; [lra|].
        replace (S (k - 1)) with k by lia. rewrite seg_at_one. exact Hq.
      * right. exists (k - length l1)%nat, lam, d. split; [lia|].
        split; [exact Hlam|].
        rewrite !app_nth2 in Hq by lia.
        replace (S k - length l1)%nat with (S (k - length l1)) in Hq by lia.
        exact Hq.
  - intros [[k [lam [d [Hk [Hlam Hq]]]]] | [k [lam [d [Hk [Hlam Hq]]]]]].
    + exists k, lam, d. rewrite length_app. split; [lia|]. split; [exact Hlam|].
      rewrite !app_nth1 by lia. exact Hq.
    + exists (length l1 + k)%nat, lam, d. rewrite length_app. split; [lia|].
      split; [exact Hlam|].
      rewrite (app_nth2 l1 l2 d) by lia.
      replace (S (length l1 + k)) with (length l1 + S k)%nat by lia.
      rewrite (app_nth2 l1 l2 d) by lia.
      replace (length l1 + k - length l1)%nat with k by lia.
      replace (length l1 + S k - length l1)%nat with (S k) by lia.
      exact Hq.
Qed.

(* All chords, piece after piece.  A junction vertex appears twice (as the
   last point of one piece and the first of the next). *)
Fixpoint cac_pts (c : ClothoidEgg) (a h step : R) (N : nat) : list Point :=
  match N with
  | O => nil
  | S n => cac_pts c a h step n ++ cac_piece_pts c a h step n
  end.

Lemma cac_piece_at_node : forall c a h k,
  cas_piece c a h k (cas_node a h k) = cas_start c a h k.
Proof.
  intros c a h k. unfold cas_piece, cas_arc_pt, cas_arc_X, cas_arc_Y.
  replace (cas_node a h k - cas_node a h k) with 0 by ring.
  destruct (cas_start c a h k) as [x y].
  destruct (Req_EM_T (cas_kap c (cas_node a h k) h) 0) as [Hz|Hnz]; cbn [px py].
  - f_equal; ring.
  - rewrite Rmult_0_r, sin_0, cos_0. f_equal; field; exact Hnz.
Qed.

Lemma cac_piece_pts_ends :
  forall c a h step k, cloth_h2 c <> 0 -> 0 < step ->
    (2 <= length (cac_piece_pts c a h step k))%nat /\
    (forall d, nth 0 (cac_piece_pts c a h step k) d = cas_start c a h k) /\
    (forall d, nth (length (cac_piece_pts c a h step k) - 1)
                 (cac_piece_pts c a h step k) d = cas_start c a h (S k)).
Proof.
  intros c a h step k Hh Hstep. unfold cac_piece_pts.
  destruct (Req_EM_T (cas_kap c (cas_node a h k) h) 0) as [Hz|Hnz].
  - split; [cbn; lia|]. split; intro d; reflexivity.
  - set (e := cac_egg c a h k). set (n := subdiv_n step (circ_sweep e)).
    destruct (subdiv_n_ok step (circ_sweep e) Hstep) as [Hn _]. fold n in Hn.
    assert (Hlen : length (lin_pts e n) = S n) by (apply lin_pts_length; lia).
    split; [lia|]. split; intro d.
    + rewrite (nth_indep (lin_pts e n) d (circ_start e)) by lia.
      rewrite (lin_endpoint_start e n Hn). unfold circ_start, e.
      rewrite <- (cac_piece_eval c a h k 0 Hh Hnz).
      replace (cas_node a h k + 0 * h) with (cas_node a h k) by ring.
      apply cac_piece_at_node.
    + rewrite Hlen. replace (S n - 1)%nat with n by lia.
      rewrite (nth_indep (lin_pts e n) d (circ_start e)) by lia.
      rewrite (lin_endpoint_end e n Hn). unfold circ_end, e.
      rewrite <- (cac_piece_eval c a h k 1 Hh Hnz).
      replace (cas_node a h k + 1 * h) with (cas_node a h (S k))
        by (rewrite cas_node_S; ring).
      apply cas_piece_end.
Qed.

Lemma cac_pts_end :
  forall c a h step N, cloth_h2 c <> 0 -> 0 < step -> (N <> 0)%nat ->
    (2 <= length (cac_pts c a h step N))%nat /\
    (forall d, nth (length (cac_pts c a h step N) - 1)
                 (cac_pts c a h step N) d = cas_start c a h N).
Proof.
  intros c a h step N Hh Hstep HN. destruct N as [|n]; [contradiction|].
  cbn [cac_pts].
  destruct (cac_piece_pts_ends c a h step n Hh Hstep) as [Hl [_ Hlast]].
  rewrite length_app. split; [lia|]. intro d.
  rewrite app_nth2 by lia.
  replace (length (cac_pts c a h step n)
           + length (cac_piece_pts c a h step n) - 1
           - length (cac_pts c a h step n))%nat
    with (length (cac_piece_pts c a h step n) - 1)%nat by lia.
  apply Hlast.
Qed.

Lemma cac_pts_shape :
  forall c a h step N q, cloth_h2 c <> 0 -> 0 < step ->
    (poly_shape (cac_pts c a h step N) q <->
     exists k, (k < N)%nat /\ poly_shape (cac_piece_pts c a h step k) q).
Proof.
  intros c a h step N q Hh Hstep. induction N as [|n IH].
  - split.
    + intros [k [lam [d [Hk _]]]]. cbn in Hk. lia.
    + intros [k [Hk _]]. lia.
  - destruct n as [|m].
    + cbn [cac_pts app]. split.
      * intro H. exists 0%nat. split; [lia | exact H].
      * intros [k [Hk H]]. assert (k = 0%nat) by lia. subst k. exact H.
    + change (cac_pts c a h step (S (S m)))
        with (cac_pts c a h step (S m) ++ cac_piece_pts c a h step (S m)).
      destruct (cac_pts_end c a h step (S m) Hh Hstep) as [Hl Hlast]; [lia|].
      destruct (cac_piece_pts_ends c a h step (S m) Hh Hstep)
        as [Hl2 [Hfirst _]].
      assert (Hl2' : (1 <= length (cac_piece_pts c a h step (S m)))%nat) by lia.
      assert (HJ : forall d,
                nth (length (cac_pts c a h step (S m)) - 1)
                  (cac_pts c a h step (S m)) d
                = nth 0 (cac_piece_pts c a h step (S m)) d)
        by (intro d; rewrite Hlast, Hfirst; reflexivity).
      pose proof (poly_shape_app _ _ q Hl Hl2' HJ) as Happ.
      split.
      * intro H. apply Happ in H. destruct H as [H | H].
        -- apply IH in H. destruct H as [k [Hk H]].
           exists k. split; [lia | exact H].
        -- exists (S m). split; [lia | exact H].
      * intros [k [Hk H]]. apply Happ.
        destruct (Nat.eq_dec k (S m)) as [->|Hne].
        -- right. exact H.
        -- left. apply IH. exists k. split; [lia | exact H].
Qed.

(* ---- headline ------------------------------------------------------------- *)

(* The end-to-end budget is eps (clothoid -> arc spline) plus cac_tol
   (arc spline -> chords).  Each term is the bound of the theorem it comes
   from; nothing is traded between them. *)
(* WITNESS {"claimId":"0007-clothoid-arc-spline-chords","topic":"curves","lemma":"clothoid_arc_spline_chords_hausdorff","title":"Arc-preserving approximation of a host clothoid window realised as chords: the N-piece heading-interpolating arc spline, each arc densified at one angular step, is a polyline within eps + r_max (1 - cos(step/2)) of the clothoid in Hausdorff distance, (b-a)^3 <= 8 A^2 N^2 eps; the terms are the clothoid-to-spline and spline-to-chords budgets. Not a Linearizes instance and not tighter than clothoid_linearizes","file":"theories/ClothoidArcChords.v","witness":"clothoid_arc_spline_chords_hausdorff","board":"ADR-0007"} *)
Theorem clothoid_arc_spline_chords_hausdorff :
  forall c a b N step eps,
    cloth_wf c -> a < b -> (N <> 0)%nat ->
    (b - a) * (b - a) * (b - a)
      <= 8 * (cloth_A c * cloth_A c) * (INR N * INR N) * eps ->
    0 < step <= 2 * PI ->
    (forall k, (k < N)%nat ->
       Rabs (cas_kap c (cas_node a (cas_step a b N) k) (cas_step a b N)
             * cas_step a b N) <= 2 * PI) ->
    hausdorff_le (cac_window_shape c a b)
      (poly_shape (cac_pts c a (cas_step a b N) step N))
      (eps + cac_tol c a b N step).
Proof.
  intros c a b N step eps Hwf Hab HN Hgate Hstep Hsw.
  destruct (clothoid_arc_chords_hausdorff c a b N step eps
              Hwf Hab HN Hgate Hstep Hsw) as [H1 H2].
  assert (Hh : cloth_h2 c <> 0) by (destruct Hwf as [_ [Hh _]]; exact Hh).
  split.
  - intros p Hp. destruct (H1 p Hp) as [q [Hq Hd]]. exists q.
    split; [|exact Hd].
    apply (cac_pts_shape c a (cas_step a b N) step N q Hh (proj1 Hstep)).
    exact Hq.
  - intros q Hq. apply H2.
    apply (cac_pts_shape c a (cas_step a b N) step N q Hh (proj1 Hstep)).
    exact Hq.
Qed.

(* ---- the winding premise from the window alone --------------------------- *)

Lemma cac_sigma_abs : forall c, Rabs (cloth_sigma c) = 1.
Proof.
  intro c. unfold cloth_sigma. destruct (Rle_dec 0 (cloth_cross c)).
  - apply Rabs_R1.
  - unfold Rabs. destruct (Rcase_abs (-1)); lra.
Qed.

(* Turning of piece k, bounded in the window and N. *)
Lemma cac_sweep_bound :
  forall c a b N k, 0 < cloth_A c -> a < b -> (k < N)%nat ->
    Rabs (cas_kap c (cas_node a (cas_step a b N) k) (cas_step a b N)
          * cas_step a b N)
    <= Rmax (Rabs a) (Rabs b) * (b - a) / (INR N * (cloth_A c * cloth_A c)).
Proof.
  intros c a b N k HA Hab Hk.
  assert (HN : (N <> 0)%nat) by lia.
  assert (HNp : 0 < INR N) by (apply lt_0_INR; lia).
  pose proof (cac_step_pos a b N Hab HN) as Hh.
  destruct (cac_node_in_window a b N k (Rlt_le _ _ Hab) Hk) as [Hlo Hhi].
  rewrite cas_node_S in Hhi.
  set (h := cas_step a b N) in *. set (x := cas_node a h k) in *.
  set (M := Rmax (Rabs a) (Rabs b)).
  assert (HAA : 0 < cloth_A c * cloth_A c) by (apply Rmult_lt_0_compat; exact HA).
  assert (Hq : 0 < h / (cloth_A c * cloth_A c)) by (apply Rdiv_lt_0_compat; assumption).
  assert (Hm : Rabs (x + h / 2) <= M).
  { pose proof (Rmax_l (Rabs a) (Rabs b)). pose proof (Rmax_r (Rabs a) (Rabs b)).
    pose proof (Rle_abs b). pose proof (Rle_abs (- a)) as Ha'.
    rewrite Rabs_Ropp in Ha'. unfold M.
    apply Rabs_le. lra. }
  unfold cas_kap.
  replace (cloth_sigma c * (x + h / 2) / (cloth_A c * cloth_A c) * h)
    with (cloth_sigma c * ((x + h / 2) * (h / (cloth_A c * cloth_A c))))
    by (field; lra).
  rewrite Rabs_mult, cac_sigma_abs, Rmult_1_l, Rabs_mult.
  rewrite (Rabs_pos_eq (h / (cloth_A c * cloth_A c))) by lra.
  replace (M * (b - a) / (INR N * (cloth_A c * cloth_A c)))
    with (M * (h / (cloth_A c * cloth_A c)))
    by (unfold h, cas_step; field; split; lra).
  apply Rmult_le_compat_r; [lra | exact Hm].
Qed.

(* The headline with the winding premise stated on the window. *)
Corollary clothoid_arc_spline_chords_hausdorff_window :
  forall c a b N step eps,
    cloth_wf c -> a < b -> (N <> 0)%nat ->
    (b - a) * (b - a) * (b - a)
      <= 8 * (cloth_A c * cloth_A c) * (INR N * INR N) * eps ->
    0 < step <= 2 * PI ->
    Rmax (Rabs a) (Rabs b) * (b - a)
      <= 2 * PI * (INR N * (cloth_A c * cloth_A c)) ->
    hausdorff_le (cac_window_shape c a b)
      (poly_shape (cac_pts c a (cas_step a b N) step N))
      (eps + cac_tol c a b N step).
Proof.
  intros c a b N step eps Hwf Hab HN Hgate Hstep Hwin.
  apply clothoid_arc_spline_chords_hausdorff; try assumption.
  intros k Hk. destruct Hwf as [HA _].
  eapply Rle_trans; [apply cac_sweep_bound; assumption|].
  assert (HNp : 0 < INR N) by (apply lt_0_INR; lia).
  assert (Hd : 0 < INR N * (cloth_A c * cloth_A c))
    by (repeat apply Rmult_lt_0_compat; assumption).
  apply Rmult_le_reg_r with (INR N * (cloth_A c * cloth_A c)); [exact Hd|].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra.
Qed.

(* ---- closed-form chord budget (#1027) ------------------------------------ *)

(* radius * |sweep| is the arc length of the piece. *)
Lemma cac_egg_arc_length :
  forall c a h k, cas_kap c (cas_node a h k) h <> 0 -> 0 < h ->
    circ_r (cac_egg c a h k) * Rabs (cas_kap c (cas_node a h k) h * h) = h.
Proof.
  intros c a h k Hk Hh. unfold cac_egg, cac_arc_egg, cac_sign. cbn [circ_r].
  set (kap := cas_kap c (cas_node a h k) h) in *.
  destruct (Rle_dec 0 kap) as [Hp|Hn].
  - rewrite Rabs_pos_eq by nra. field. exact Hk.
  - rewrite Rabs_left by nra. field. exact Hk.
Qed.

(* One piece against its chords, at the angle each chord subtends.  The
   bound is |kappa_k h| * h / 32: it vanishes with the curvature and does
   not depend on step. *)
Lemma cac_piece_hausdorff_subtended :
  forall c a h step k,
    cloth_h2 c <> 0 -> 0 < h -> 0 < step ->
    Rabs (cas_kap c (cas_node a h k) h * h) <= 2 * PI ->
    hausdorff_le (cac_piece_shape c a h k)
      (poly_shape (cac_piece_pts c a h step k))
      (Rabs (cas_kap c (cas_node a h k) h * h) * h / 32).
Proof.
  intros c a h step k Hh Hpos Hstep Hsw.
  pose proof PI_RGT_0 as Hpi.
  destruct (Req_EM_T (cas_kap c (cas_node a h k) h) 0) as [Hz|Hnz].
  - assert (Hpts : cac_piece_pts c a h step k
                   = cac_piece_pts c a h (2 * PI) k).
    { unfold cac_piece_pts.
      destruct (Req_EM_T (cas_kap c (cas_node a h k) h) 0);
        [reflexivity | contradiction]. }
    assert (Hone : 0 < 2 * PI <= 2 * PI) by lra.
    pose proof (cac_piece_hausdorff c a h (2 * PI) k Hh Hpos Hone Hsw)
      as [H1 H2].
    assert (Hr : cac_r c a h k = 0).
    { unfold cac_r.
      destruct (Req_EM_T (cas_kap c (cas_node a h k) h) 0);
        [reflexivity | contradiction]. }
    rewrite Hr, Rmult_0_l in H1, H2. rewrite Hpts.
    assert (Hle : 0 <= Rabs (cas_kap c (cas_node a h k) h * h) * h / 32).
    { pose proof (Rabs_pos (cas_kap c (cas_node a h k) h * h)). nra. }
    split; eapply within_eps_weaken; eauto.
  - set (e := cac_egg c a h k).
    assert (Hsweep : circ_sweep e = cas_kap c (cas_node a h k) h * h)
      by reflexivity.
    assert (Hs0 : circ_sweep e <> 0).
    { rewrite Hsweep. apply Rmult_integral_contrapositive. split; lra. }
    destruct (subdiv_n_ok step (circ_sweep e) Hstep) as [Hn _].
    set (n := subdiv_n step (circ_sweep e)) in *.
    pose proof (arc_linearize_hausdorff_subtended e n Hn
                  (cac_arc_egg_r_nn _ _ _ _ Hnz) Hs0
                  ltac:(rewrite Hsweep; exact Hsw)) as Harc.
    assert (HN2 : 2 <= INR n)
      by (pose proof (le_INR 2 n Hn) as H; simpl in H; lra).
    set (S := Rabs (circ_sweep e)) in *.
    assert (HS : 0 < S) by (apply Rabs_pos_lt; exact Hs0).
    assert (HSle : S <= 2 * PI) by (unfold S; rewrite Hsweep; exact Hsw).
    assert (Hrs : circ_r e * S = h).
    { unfold S. rewrite Hsweep. apply cac_egg_arc_length; assumption. }
    assert (Hr : 0 <= circ_r e) by (apply cac_arc_egg_r_nn; exact Hnz).
    assert (Htol : circ_r e * (1 - cos (S / INR n / 2)) <= S * h / 32).
    { set (x := S / INR n / 2).
      assert (Hx0 : 0 <= x).
      { unfold x. apply Rmult_le_pos; [|lra].
        apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat; lra]. }
      assert (Hx1 : x <= PI / 2).
      { unfold x. apply Rmult_le_reg_r with (2 * INR n); [lra|].
        replace (S / INR n / 2 * (2 * INR n)) with S by (field; lra). nra. }
      pose proof (cos_ge_quad x ltac:(lra) Hx1) as Hc.
      apply Rle_trans with (circ_r e * (x * x / 2)).
      { apply Rmult_le_compat_l; [exact Hr | lra]. }
      replace (circ_r e * (x * x / 2))
        with ((circ_r e * S) * S * / (8 * (INR n * INR n)))
        by (unfold x; field; lra).
      rewrite Hrs.
      replace (S * h / 32) with (h * S * / 32) by field.
      apply Rmult_le_compat_l; [nra|].
      apply Rinv_le_contravar; nra. }
    rewrite <- Hsweep. fold S.
    destruct Harc as [H1 H2]. fold S in H1, H2.
    unfold cac_piece_pts.
    destruct (Req_EM_T (cas_kap c (cas_node a h k) h) 0) as [Hz'|_];
      [contradiction|]. fold e. fold n.
    split.
    + eapply within_eps_weaken; [exact Htol|].
      intros p Hp. apply H1.
      apply (cac_piece_arc_shape c a h k p Hh Hpos Hnz). exact Hp.
    + eapply within_eps_weaken; [exact Htol|].
      intros q Hq. destruct (H2 q Hq) as [p [Hp Hd]].
      exists p. split; [|exact Hd].
      apply (cac_piece_arc_shape c a h k p Hh Hpos Hnz). exact Hp.
Qed.

(* Chord budget in the window and N alone. *)
Definition cac_chord_budget (c : ClothoidEgg) (a b : R) (N : nat) : R :=
  Rmax (Rabs a) (Rabs b) * (b - a) * (b - a)
  / (32 * (cloth_A c * cloth_A c) * (INR N * INR N)).

Theorem cac_spline_chords_hausdorff_closed :
  forall c a b N step,
    cloth_wf c -> a < b -> (N <> 0)%nat -> 0 < step ->
    Rmax (Rabs a) (Rabs b) * (b - a)
      <= 2 * PI * (INR N * (cloth_A c * cloth_A c)) ->
    hausdorff_le (cac_spline_shape c a b N) (cac_chords_shape c a b N step)
      (cac_chord_budget c a b N).
Proof.
  intros c a b N step Hwf Hab HN Hstep Hwin.
  destruct Hwf as [HA [Hh _]].
  pose proof (cac_step_pos a b N Hab HN) as Hpos.
  assert (HNp : 0 < INR N) by (apply lt_0_INR; lia).
  assert (HAA : 0 < cloth_A c * cloth_A c) by (apply Rmult_lt_0_compat; exact HA).
  assert (Hd : 0 < INR N * (cloth_A c * cloth_A c))
    by (apply Rmult_lt_0_compat; assumption).
  assert (Hk : forall k, (k < N)%nat ->
            hausdorff_le (cac_piece_shape c a (cas_step a b N) k)
              (poly_shape (cac_piece_pts c a (cas_step a b N) step k))
              (cac_chord_budget c a b N)).
  { intros k Hk.
    pose proof (cac_sweep_bound c a b N k HA Hab Hk) as Hsb.
    assert (Hsw : Rabs (cas_kap c (cas_node a (cas_step a b N) k)
                          (cas_step a b N) * cas_step a b N) <= 2 * PI).
    { eapply Rle_trans; [exact Hsb|].
      apply Rmult_le_reg_r with (INR N * (cloth_A c * cloth_A c)); [exact Hd|].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
    destruct (cac_piece_hausdorff_subtended c a (cas_step a b N) step k
                Hh Hpos Hstep Hsw) as [H1 H2].
    assert (Hle : Rabs (cas_kap c (cas_node a (cas_step a b N) k)
                          (cas_step a b N) * cas_step a b N)
                  * cas_step a b N / 32 <= cac_chord_budget c a b N).
    { unfold cac_chord_budget.
      replace (Rmax (Rabs a) (Rabs b) * (b - a) * (b - a)
               / (32 * (cloth_A c * cloth_A c) * (INR N * INR N)))
        with (Rmax (Rabs a) (Rabs b) * (b - a)
              / (INR N * (cloth_A c * cloth_A c)) * cas_step a b N / 32)
        by (unfold cas_step; field; split; lra).
      unfold Rdiv at 1 3.
      apply Rmult_le_compat_r; [lra|].
      apply Rmult_le_compat_r; [lra | exact Hsb]. }
    split; eapply within_eps_weaken; eauto. }
  split.
  - apply (within_eps_union (fun k => (k < N)%nat)
             (cac_piece_shape c a (cas_step a b N))
             (fun k => poly_shape (cac_piece_pts c a (cas_step a b N) step k))).
    intros k Hlt. exact (proj1 (Hk k Hlt)).
  - apply (within_eps_union (fun k => (k < N)%nat)
             (fun k => poly_shape (cac_piece_pts c a (cas_step a b N) step k))
             (cac_piece_shape c a (cas_step a b N))).
    intros k Hlt. exact (proj2 (Hk k Hlt)).
Qed.

(* The headline with both budgets in closed form:
     d_H(C, P) <= (b - a)^3 / (8 A^2 N^2)
                  + max(|a|, |b|) (b - a)^2 / (32 A^2 N^2).
   Same polyline cac_pts as clothoid_arc_spline_chords_hausdorff.  The
   chord term has no radius in it: it is continuous through the
   inflection, decreases in N, and does not depend on step (step only
   chooses how many chords each arc gets, at least two). *)
Theorem clothoid_arc_spline_chords_closed_form :
  forall c a b N step eps,
    cloth_wf c -> a < b -> (N <> 0)%nat ->
    (b - a) * (b - a) * (b - a)
      <= 8 * (cloth_A c * cloth_A c) * (INR N * INR N) * eps ->
    0 < step ->
    Rmax (Rabs a) (Rabs b) * (b - a)
      <= 2 * PI * (INR N * (cloth_A c * cloth_A c)) ->
    hausdorff_le (cac_window_shape c a b)
      (poly_shape (cac_pts c a (cas_step a b N) step N))
      (eps + cac_chord_budget c a b N).
Proof.
  intros c a b N step eps Hwf Hab HN Hgate Hstep Hwin.
  assert (Hh : cloth_h2 c <> 0) by (destruct Hwf as [_ [Hh _]]; exact Hh).
  destruct (hausdorff_le_trans _ (cac_spline_shape c a b N) _ eps
              (cac_chord_budget c a b N)
              (cac_clothoid_spline_hausdorff c a b N eps Hwf
                 (Rlt_le _ _ Hab) HN Hgate)
              (cac_spline_chords_hausdorff_closed c a b N step
                 Hwf Hab HN Hstep Hwin)) as [H1 H2].
  split.
  - intros p Hp. destruct (H1 p Hp) as [q [Hq Hd]]. exists q.
    split; [|exact Hd].
    apply (cac_pts_shape c a (cas_step a b N) step N q Hh Hstep). exact Hq.
  - intros q Hq. apply H2.
    apply (cac_pts_shape c a (cas_step a b N) step N q Hh Hstep). exact Hq.
Qed.

Print Assumptions within_eps_trans.
Print Assumptions hausdorff_le_trans.
Print Assumptions within_eps_weaken.
Print Assumptions cac_arc_egg_eval.
Print Assumptions cac_arc_egg_r_nn.
Print Assumptions cac_phi0_ok.
Print Assumptions cac_tangent_angle.
Print Assumptions cac_piece_eval.
Print Assumptions cac_r_le_rmax.
Print Assumptions within_eps_union.
Print Assumptions cac_node_step.
Print Assumptions cac_cos_gap_nn.
Print Assumptions cac_piece_arc_shape.
Print Assumptions cac_piece_line.
Print Assumptions cac_piece_hausdorff.
Print Assumptions cac_r_nn.
Print Assumptions cac_step_pos.
Print Assumptions cac_spline_chords_hausdorff.
Print Assumptions cac_node_in_window.
Print Assumptions cac_clothoid_spline_hausdorff.
Print Assumptions clothoid_arc_chords_hausdorff.
Print Assumptions seg_at_one.
Print Assumptions poly_shape_app.
Print Assumptions cac_piece_at_node.
Print Assumptions cac_piece_pts_ends.
Print Assumptions cac_pts_end.
Print Assumptions cac_pts_shape.
Print Assumptions clothoid_arc_spline_chords_hausdorff.
Print Assumptions cac_sigma_abs.
Print Assumptions cac_sweep_bound.
Print Assumptions clothoid_arc_spline_chords_hausdorff_window.
Print Assumptions cac_egg_arc_length.
Print Assumptions cac_piece_hausdorff_subtended.
Print Assumptions cac_spline_chords_hausdorff_closed.
Print Assumptions clothoid_arc_spline_chords_closed_form.
