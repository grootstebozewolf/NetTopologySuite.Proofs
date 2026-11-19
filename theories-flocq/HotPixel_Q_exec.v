(* ============================================================================
   NetTopologySuite.Proofs.Flocq.HotPixel_Q_exec
   ----------------------------------------------------------------------------
   An EXECUTABLE rational (Q) twin of the snap-rounding and closed
   passes-through specifications in HotPixel_b64.v, at ANY positive rational
   scale, with Qed reflection lemmas.  This is the code tools/klic-demo runs.

   Why.  `snap_round_coord` and `passes_through_hot_pixel_closed` are stated
   over Rocq's non-computational reals.  The binary64 filter
   `b64_passes_through_hot_pixel` reads coordinates through B2R and is also a
   specification (HotPixel_b64.v), and its rounded compute twin
   (PassesThrough_b64_compute.v) is exact only on the tight unit grid
   |n| <= 2^22 (PassesThrough_b64_grid_exact.v).  Dutch RD coordinates on a
   1 mm grid are ~1.5e8 .. 6.3e8 mm, far outside that window, and the
   metre-to-millimetre step is a rounding multiply in binary64.

   This file removes both gaps by computing in exact rationals:

     q_round_ne      : Q -> Z      round-half-to-even, Z division only
     q_snap_coord    : Q -> Q -> Q snap to the grid of spacing 1/s
     q_touches_closed: closed segment / closed hot-pixel test (Liang-Barsky
                       on exact Q intervals)
     q_passes_through_closed : touch on the original AND the snapped segment

   and proving, Qed, that each one REFLECTS its real specification:

     q_round_ne_correct      : IZR (q_round_ne q) = IZR (round_mode mode_NE (Q2R q))
     q_snap_coord_correct    : Q2R (q_snap_coord x s) = snap_round_coord (Q2R x) (Q2R s)
     q_snap_correct          : QP2P (q_snap P s) = snap_round (QP2P P) (Q2R s)
     q_touches_closed_reflect: q_touches_closed P0 P1 C s = true
                                 <-> segment_touches_hot_pixel_closed .. (Q2R s)
     q_passes_through_closed_reflect :
                               q_passes_through_closed P0 P1 C s = true
                                 <-> passes_through_hot_pixel_closed .. (Q2R s)
     q_snap_disp_bound       : Q2R (q_snap_disp x s) <= / (2 * Q2R s)
                               (displacement <= half a grid cell, any scale)

   The scale is a parameter, so the 1 mm grid on metre input is s = 1000 and
   the 1 mm grid on millimetre input is s = 1.  There is no range limit: the
   arithmetic is exact at RD magnitudes.  Extraction to OCaml (no overrides:
   Z/positive/Q extract as the Stdlib inductive types) lives in
   tools/klic-demo/rocq/Extract_HotPixel_Q.v.

   SCOPE.  This is node placement and hot-pixel passing.  It is NOT a
   verified overlay: no theorem here says anything about the topology of an
   intersection, union or covers result.

   Corpus invariant: no Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   topic: hot-pixel
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.
From Stdlib Require Import Qreals.
From Stdlib Require Import Lia.
From Stdlib Require Import Lra.

From Flocq Require Import Core.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Flocq Require Import IEEE754.Binary.

From NTS.Proofs        Require Import Distance HotPixel.
From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import HotPixel_b64_refs.
From NTS.Proofs.Flocq Require Import HotPixel_b64.
From NTS.Proofs.Flocq Require Import Orient_b64_exact.

Local Open Scope R_scope.

Local Abbreviation b64_fexp := (SpecFloat.fexp prec emax).

(* -------------------------------------------------------------------------- *)
(* §0  Small Q2R facts.                                                       *)
(* -------------------------------------------------------------------------- *)

Lemma hpq_Q2R_0 : Q2R 0%Q = 0.
Proof. unfold Q2R; simpl. field. Qed.

Lemma hpq_Q2R_1 : Q2R 1%Q = 1.
Proof. unfold Q2R; simpl. field. Qed.

Lemma hpq_Q2R_2 : Q2R (2 # 1)%Q = 2.
Proof. unfold Q2R; simpl. field. Qed.

Lemma hpq_Q2R_inject_Z : forall n : Z, Q2R (inject_Z n) = IZR n.
Proof. intros n. unfold Q2R, inject_Z; simpl. field. Qed.

Lemma hpq_Q2R_nonzero : forall q : Q, Q2R q <> 0 -> ~ (q == 0)%Q.
Proof.
  intros q Hq Heq. apply Hq. rewrite (Qeq_eqR _ _ Heq). apply hpq_Q2R_0.
Qed.

(* Operand-selecting min / max (Boolean, extractable) and their R images. *)
Definition q_min (a b : Q) : Q := if Qle_bool a b then a else b.
Definition q_max (a b : Q) : Q := if Qle_bool a b then b else a.

Lemma Q2R_q_min : forall a b, Q2R (q_min a b) = Rmin (Q2R a) (Q2R b).
Proof.
  intros a b. unfold q_min. destruct (Qle_bool a b) eqn:E.
  - apply Qle_bool_iff in E. apply Qle_Rle in E. symmetry. apply Rmin_left; exact E.
  - assert (Hlt : (b < a)%Q).
    { apply Qnot_le_lt. intros H. apply Qle_bool_iff in H. congruence. }
    apply Qlt_Rlt in Hlt. symmetry. apply Rmin_right. lra.
Qed.

Lemma Q2R_q_max : forall a b, Q2R (q_max a b) = Rmax (Q2R a) (Q2R b).
Proof.
  intros a b. unfold q_max. destruct (Qle_bool a b) eqn:E.
  - apply Qle_bool_iff in E. apply Qle_Rle in E. symmetry. apply Rmax_right; exact E.
  - assert (Hlt : (b < a)%Q).
    { apply Qnot_le_lt. intros H. apply Qle_bool_iff in H. congruence. }
    apply Qlt_Rlt in Hlt. symmetry. apply Rmax_left. lra.
Qed.

Lemma hpq_Qle_bool_R : forall a b, Qle_bool a b = true <-> Q2R a <= Q2R b.
Proof.
  intros a b. rewrite Qle_bool_iff. split; [apply Qle_Rle | apply Rle_Qle].
Qed.

Lemma hpq_Qeq_bool_R : forall a b, Qeq_bool a b = true <-> Q2R a = Q2R b.
Proof.
  intros a b. rewrite Qeq_bool_iff. split; [apply Qeq_eqR | apply eqR_Qeq].
Qed.

(* -------------------------------------------------------------------------- *)
(* §1  Round-half-to-even on Q, by integer division only.                     *)
(* -------------------------------------------------------------------------- *)

Definition q_round_ne (q : Q) : Z :=
  let n := Qnum q in
  let d := Zpos (Qden q) in
  let f := (n / d)%Z in
  let r := (n mod d)%Z in
  match Z.compare (2 * r) d with
  | Lt => f
  | Eq => if Z.even f then f else (f + 1)%Z
  | Gt => (f + 1)%Z
  end.

Theorem q_round_ne_correct :
  forall q : Q, q_round_ne q = round_mode mode_NE (Q2R q).
Proof.
  intros [n dp]. unfold q_round_ne, Q2R. cbn [Qnum Qden round_mode].
  set (d := Zpos dp).
  assert (Hd : (0 < d)%Z) by (unfold d; lia).
  assert (HdR : 0 < IZR d) by (apply IZR_lt; exact Hd).
  set (x := IZR n * / IZR d).
  set (f := (n / d)%Z). set (r := (n mod d)%Z).
  assert (Hfl : Zfloor x = f).
  { unfold x, f. change (IZR n * / IZR d) with (IZR n / IZR d).
    apply Zfloor_div. lia. }
  assert (Hdm : n = (d * f + r)%Z) by (unfold f, r; apply Z.div_mod; lia).
  assert (Hr : (0 <= r < d)%Z) by (unfold r; apply Z.mod_pos_bound; exact Hd).
  assert (Hfrac : x - IZR f = IZR r / IZR d).
  { unfold x. rewrite Hdm, plus_IZR, mult_IZR. field. lra. }
  assert (Hceil : r <> 0%Z -> Zceil x = (f + 1)%Z).
  { intros Hr0. rewrite <- Hfl. apply Zceil_floor_neq. rewrite Hfl.
    intros Heq. assert (Hz : IZR r / IZR d = 0) by (rewrite <- Hfrac; lra).
    apply Hr0. apply eq_IZR.
    assert (Hm : IZR r = IZR r / IZR d * IZR d) by (field; lra).
    rewrite Hz in Hm. lra. }
  assert (Hsign : IZR r / IZR d - / 2 = IZR (2 * r - d) / (2 * IZR d)).
  { rewrite minus_IZR, mult_IZR. field. lra. }
  unfold Znearest. rewrite Hfl, Hfrac.
  destruct (Z.compare_spec (2 * r) d) as [Heq | Hlt | Hgt].
  - (* exactly half *)
    assert (Hr0 : r <> 0%Z) by lia.
    assert (Hc : Rcompare (IZR r / IZR d) (/ 2) = Eq).
    { apply Rcompare_Eq. assert (Hz : (2 * r - d)%Z = 0%Z) by lia.
      rewrite Hz in Hsign. unfold Rdiv in Hsign. rewrite Rmult_0_l in Hsign. lra. }
    rewrite Hc, (Hceil Hr0).
    destruct (Z.even f); reflexivity.
  - assert (Hc : Rcompare (IZR r / IZR d) (/ 2) = Lt).
    { apply Rcompare_Lt.
      assert (H1 : IZR (2 * r - d) < 0) by (apply IZR_lt; lia).
      assert (H2 : IZR (2 * r - d) / (2 * IZR d) < 0).
      { apply Rdiv_neg_pos; lra. }
      lra. }
    rewrite Hc. reflexivity.
  - assert (Hr0 : r <> 0%Z) by lia.
    assert (Hc : Rcompare (IZR r / IZR d) (/ 2) = Gt).
    { apply Rcompare_Gt.
      assert (H1 : 0 < IZR (2 * r - d)) by (apply IZR_lt; lia).
      assert (H2 : 0 < IZR (2 * r - d) / (2 * IZR d)).
      { apply Rdiv_pos_pos; lra. }
      lra. }
    rewrite Hc, (Hceil Hr0). reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Snap to the grid of spacing 1/s, and its exact bridge.                 *)
(* -------------------------------------------------------------------------- *)

Definition q_snap_coord (x s : Q) : Q := (inject_Z (q_round_ne (x * s)) / s)%Q.

Theorem q_snap_coord_correct :
  forall x s : Q, Q2R s <> 0 ->
    Q2R (q_snap_coord x s) = snap_round_coord (Q2R x) (Q2R s).
Proof.
  intros x s Hs. unfold q_snap_coord, snap_round_coord.
  rewrite Q2R_div by (apply hpq_Q2R_nonzero; exact Hs).
  rewrite hpq_Q2R_inject_Z, q_round_ne_correct, Q2R_mult, round_FIX0_IZR.
  reflexivity.
Qed.

Record QPoint : Type := mkQP { qx : Q; qy : Q }.

Definition QP2P (P : QPoint) : Point := mkPoint (Q2R (qx P)) (Q2R (qy P)).

Definition q_snap (P : QPoint) (s : Q) : QPoint :=
  mkQP (q_snap_coord (qx P) s) (q_snap_coord (qy P) s).

Theorem q_snap_correct :
  forall (P : QPoint) (s : Q), Q2R s <> 0 ->
    QP2P (q_snap P s) = snap_round (QP2P P) (Q2R s).
Proof.
  intros P s Hs. unfold QP2P, q_snap, snap_round. cbn [qx qy px py].
  rewrite !q_snap_coord_correct by exact Hs. reflexivity.
Qed.

(* Displacement |snap(x) - x| of a snapped coordinate, computed exactly. *)
Definition q_snap_disp (x s : Q) : Q :=
  let d := (q_snap_coord x s - x)%Q in q_max d (- d)%Q.

(* The general-scale tolerance: snapping moves a coordinate by at most half a
   grid cell, 1 / (2 s).  At s = 1 this is NodingSeparation_b64's
   snap_round_coord_tolerance. *)
Lemma snap_round_coord_tolerance_scale :
  forall x s : R, 0 < s ->
    Rabs (snap_round_coord x s - x) <= / (2 * s).
Proof.
  intros x s Hs. unfold snap_round_coord. rewrite round_FIX0_IZR.
  pose proof (Znearest_half (fun z => negb (Z.even z)) (x * s)) as H.
  set (n := Znearest (fun z => negb (Z.even z)) (x * s)) in *.
  change (round_mode mode_NE (x * s)) with n.
  replace (IZR n / s - x) with ((IZR n - x * s) / s) by (field; lra).
  unfold Rdiv. rewrite Rabs_mult, Rabs_inv, (Rabs_right s) by lra.
  rewrite Rabs_minus_sym in H.
  replace (/ (2 * s)) with (/ 2 * / s) by (field; lra).
  apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra | exact H].
Qed.

Theorem q_snap_disp_bound :
  forall x s : Q, 0 < Q2R s ->
    Q2R (q_snap_disp x s) <= / (2 * Q2R s).
Proof.
  intros x s Hs. unfold q_snap_disp.
  rewrite Q2R_q_max, Q2R_opp, Q2R_minus, q_snap_coord_correct by lra.
  pose proof (snap_round_coord_tolerance_scale (Q2R x) (Q2R s) Hs) as H.
  set (d := snap_round_coord (Q2R x) (Q2R s) - Q2R x) in *.
  apply Rmax_lub.
  - eapply Rle_trans; [apply Rle_abs | exact H].
  - eapply Rle_trans; [| exact H]. rewrite <- Rabs_Ropp. apply Rle_abs.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Exact closed segment / hot-pixel test (Liang-Barsky on Q).             *)
(* -------------------------------------------------------------------------- *)

(* Per axis: the interval of t for which lo <= (1-t) c0 + t c1 <= hi, or None
   when the segment is parallel to the slab and outside it.  A degenerate axis
   inside its slab constrains nothing, reported as [0, 1]. *)
Definition q_axis (c0 c1 lo hi : Q) : option (Q * Q) :=
  if Qeq_bool c1 c0 then
    (if andb (Qle_bool lo c0) (Qle_bool c0 hi) then Some (0%Q, 1%Q) else None)
  else
    let a := ((lo - c0) / (c1 - c0))%Q in
    let b := ((hi - c0) / (c1 - c0))%Q in
    Some (q_min a b, q_max a b).

Definition q_hot_pixel_radius (s : Q) : Q := (/ ((2 # 1) * s))%Q.

Definition q_touches_closed (P0 P1 C : QPoint) (s : Q) : bool :=
  let r := q_hot_pixel_radius s in
  match q_axis (qx P0) (qx P1) (qx C - r)%Q (qx C + r)%Q,
        q_axis (qy P0) (qy P1) (qy C - r)%Q (qy C + r)%Q with
  | Some (lx, hx), Some (ly, hy) =>
      Qle_bool (q_max 0 (q_max lx ly)) (q_min 1 (q_min hx hy))
  | _, _ => false
  end.

Definition q_passes_through_closed (P0 P1 C : QPoint) (s : Q) : bool :=
  andb (q_touches_closed P0 P1 C s)
       (q_touches_closed (q_snap P0 s) (q_snap P1 s) C s).

(* --- R-side interval algebra --------------------------------------------- *)

Local Lemma div_le_pos : forall a d t, 0 < d -> (a / d <= t <-> a <= t * d).
Proof.
  intros a d t Hd. split; intros H.
  - apply (Rmult_le_compat_r d) in H; [|lra].
    replace (a / d * d) with a in H by (field; lra). exact H.
  - apply (Rmult_le_reg_r d); [lra|].
    replace (a / d * d) with a by (field; lra). exact H.
Qed.

Local Lemma le_div_pos : forall a d t, 0 < d -> (t <= a / d <-> t * d <= a).
Proof.
  intros a d t Hd. split; intros H.
  - apply (Rmult_le_compat_r d) in H; [|lra].
    replace (a / d * d) with a in H by (field; lra). exact H.
  - apply (Rmult_le_reg_r d); [lra|].
    replace (a / d * d) with a by (field; lra). exact H.
Qed.

(* One axis, non-degenerate: the slab condition is the t-interval. *)
Local Lemma axis_interval :
  forall c0 c1 lo hi t : R,
    lo <= hi -> c1 <> c0 ->
    (lo <= (1 - t) * c0 + t * c1 <= hi <->
     Rmin ((lo - c0) / (c1 - c0)) ((hi - c0) / (c1 - c0)) <= t <=
     Rmax ((lo - c0) / (c1 - c0)) ((hi - c0) / (c1 - c0))).
Proof.
  intros c0 c1 lo hi t Hlh Hne.
  replace ((1 - t) * c0 + t * c1) with (c0 + t * (c1 - c0)) by ring.
  destruct (Rlt_or_le 0 (c1 - c0)) as [Hp | Hn].
  - (* increasing *)
    assert (Hab : (lo - c0) / (c1 - c0) <= (hi - c0) / (c1 - c0)).
    { unfold Rdiv. apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra | lra]. }
    rewrite Rmin_left, Rmax_right by exact Hab.
    rewrite div_le_pos, le_div_pos by exact Hp. lra.
  - assert (Hm : 0 < c0 - c1) by (assert (c1 - c0 <> 0) by lra; lra).
    replace ((lo - c0) / (c1 - c0)) with ((c0 - lo) / (c0 - c1)) by (field; lra).
    replace ((hi - c0) / (c1 - c0)) with ((c0 - hi) / (c0 - c1)) by (field; lra).
    assert (Hab : (c0 - hi) / (c0 - c1) <= (c0 - lo) / (c0 - c1)).
    { unfold Rdiv. apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra | lra]. }
    rewrite Rmin_right, Rmax_left by exact Hab.
    rewrite div_le_pos, le_div_pos by exact Hm. lra.
Qed.

(* Three intervals (with [0,1]) meet iff max of lows <= min of highs. *)
Local Lemma intervals_meet :
  forall l1 h1 l2 h2 : R,
    (exists t, (0 <= t <= 1 /\ l1 <= t <= h1) /\ l2 <= t <= h2) <->
    Rmax 0 (Rmax l1 l2) <= Rmin 1 (Rmin h1 h2).
Proof.
  intros l1 h1 l2 h2. split.
  - intros [t [[H01 H1] H2]].
    apply Rle_trans with t.
    + apply Rmax_lub; [lra|]. apply Rmax_lub; lra.
    + apply Rmin_glb; [lra|]. apply Rmin_glb; lra.
  - intros H. exists (Rmax 0 (Rmax l1 l2)).
    pose proof (Rmax_l 0 (Rmax l1 l2)). pose proof (Rmax_r 0 (Rmax l1 l2)).
    pose proof (Rmax_l l1 l2). pose proof (Rmax_r l1 l2).
    pose proof (Rmin_l 1 (Rmin h1 h2)). pose proof (Rmin_r 1 (Rmin h1 h2)).
    pose proof (Rmin_l h1 h2). pose proof (Rmin_r h1 h2).
    repeat split; lra.
Qed.

(* Specification of q_axis, relative to t in [0,1]. *)
Local Lemma q_axis_spec :
  forall c0 c1 lo hi : Q,
    Q2R lo <= Q2R hi ->
    match q_axis c0 c1 lo hi with
    | Some (l, h) =>
        forall t, 0 <= t <= 1 ->
          (Q2R lo <= (1 - t) * Q2R c0 + t * Q2R c1 <= Q2R hi <->
           Q2R l <= t <= Q2R h)
    | None =>
        forall t, ~ (Q2R lo <= (1 - t) * Q2R c0 + t * Q2R c1 <= Q2R hi)
    end.
Proof.
  intros c0 c1 lo hi Hlh. unfold q_axis.
  destruct (Qeq_bool c1 c0) eqn:Edeg.
  - apply hpq_Qeq_bool_R in Edeg.
    destruct (Qle_bool lo c0) eqn:E1; destruct (Qle_bool c0 hi) eqn:E2;
      cbn [andb].
    + apply hpq_Qle_bool_R in E1. apply hpq_Qle_bool_R in E2.
      intros t Ht. rewrite hpq_Q2R_0, hpq_Q2R_1.
      replace ((1 - t) * Q2R c0 + t * Q2R c1) with (Q2R c0)
        by (rewrite Edeg; ring). lra.
    + intros t Ht. replace ((1 - t) * Q2R c0 + t * Q2R c1) with (Q2R c0) in Ht
        by (rewrite Edeg; ring).
      assert (Hf : ~ Q2R c0 <= Q2R hi).
      { intros H. apply hpq_Qle_bool_R in H. congruence. }
      lra.
    + intros t Ht. replace ((1 - t) * Q2R c0 + t * Q2R c1) with (Q2R c0) in Ht
        by (rewrite Edeg; ring).
      assert (Hf : ~ Q2R lo <= Q2R c0).
      { intros H. apply hpq_Qle_bool_R in H. congruence. }
      lra.
    + intros t Ht. replace ((1 - t) * Q2R c0 + t * Q2R c1) with (Q2R c0) in Ht
        by (rewrite Edeg; ring).
      assert (Hf : ~ Q2R lo <= Q2R c0).
      { intros H. apply hpq_Qle_bool_R in H. congruence. }
      lra.
  - assert (Hne : Q2R c1 <> Q2R c0).
    { intros H. apply hpq_Qeq_bool_R in H. congruence. }
    assert (Hd : ~ (c1 - c0 == 0)%Q).
    { apply hpq_Q2R_nonzero. rewrite Q2R_minus. lra. }
    intros t _.
    rewrite Q2R_q_min, Q2R_q_max, !Q2R_div by exact Hd.
    rewrite !Q2R_minus.
    apply axis_interval; assumption.
Qed.

Lemma Q2R_hot_pixel_radius :
  forall s : Q, 0 < Q2R s -> Q2R (q_hot_pixel_radius s) = hot_pixel_radius (Q2R s).
Proof.
  intros s Hs. unfold q_hot_pixel_radius, hot_pixel_radius.
  rewrite Q2R_inv.
  - rewrite Q2R_mult, hpq_Q2R_2. reflexivity.
  - apply hpq_Q2R_nonzero. rewrite Q2R_mult, hpq_Q2R_2. lra.
Qed.

Theorem q_touches_closed_reflect :
  forall (P0 P1 C : QPoint) (s : Q), 0 < Q2R s ->
    q_touches_closed P0 P1 C s = true <->
    segment_touches_hot_pixel_closed (QP2P P0) (QP2P P1) (QP2P C) (Q2R s).
Proof.
  intros P0 P1 C s Hs.
  unfold segment_touches_hot_pixel_closed, in_hot_pixel_closed, segment_point,
         QP2P, q_touches_closed.
  cbn [px py].
  assert (Hr : 0 < hot_pixel_radius (Q2R s)) by (apply hot_pixel_radius_pos; exact Hs).
  rewrite <- (Q2R_hot_pixel_radius s Hs) in *.
  set (r := q_hot_pixel_radius s) in *.
  pose proof (q_axis_spec (qx P0) (qx P1) (qx C - r)%Q (qx C + r)%Q) as Hx.
  pose proof (q_axis_spec (qy P0) (qy P1) (qy C - r)%Q (qy C + r)%Q) as Hy.
  rewrite !Q2R_minus, !Q2R_plus in Hx, Hy.
  specialize (Hx ltac:(lra)). specialize (Hy ltac:(lra)).
  destruct (q_axis (qx P0) (qx P1) (qx C - r)%Q (qx C + r)%Q) as [[lx hx]|];
  destruct (q_axis (qy P0) (qy P1) (qy C - r)%Q (qy C + r)%Q) as [[ly hy]|].
  - rewrite hpq_Qle_bool_R, !Q2R_q_max, !Q2R_q_min, hpq_Q2R_0, hpq_Q2R_1.
    rewrite <- intervals_meet. split.
    + intros [t [[Ht H1] H2]]. exists t. split; [exact Ht|].
      split; [apply (Hx t Ht) | apply (Hy t Ht)]; assumption.
    + intros [t [Ht [H1 H2]]]. exists t.
      split; [split; [exact Ht | apply (Hx t Ht); exact H1] | apply (Hy t Ht); exact H2].
  - split; [discriminate|]. intros [t [_ [_ H2]]]. exfalso; exact (Hy t H2).
  - split; [discriminate|]. intros [t [_ [H1 _]]]. exfalso; exact (Hx t H1).
  - split; [discriminate|]. intros [t [_ [H1 _]]]. exfalso; exact (Hx t H1).
Qed.

Theorem q_passes_through_closed_reflect :
  forall (P0 P1 C : QPoint) (s : Q), 0 < Q2R s ->
    q_passes_through_closed P0 P1 C s = true <->
    passes_through_hot_pixel_closed (QP2P P0) (QP2P P1) (QP2P C) (Q2R s).
Proof.
  intros P0 P1 C s Hs. unfold q_passes_through_closed, passes_through_hot_pixel_closed.
  rewrite Bool.andb_true_iff, !q_touches_closed_reflect by exact Hs.
  rewrite !q_snap_correct by lra. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Scale and representability at Dutch RD magnitudes.                     *)
(* -------------------------------------------------------------------------- *)

(* The snapped coordinate is an integer number of grid cells: on a 1 mm grid
   with millimetre input (s = 1) it is an integer number of millimetres. *)
Lemma q_snap_coord_unit_integer :
  forall x : Q, Q2R (q_snap_coord x 1%Q) = IZR (q_round_ne (x * 1)%Q).
Proof.
  intros x. unfold q_snap_coord. rewrite Q2R_div.
  - rewrite hpq_Q2R_inject_Z, hpq_Q2R_1. field.
  - apply hpq_Q2R_nonzero. rewrite hpq_Q2R_1. lra.
Qed.

(* Every integer millimetre coordinate within 10^9 mm (1000 km; RD x and y
   are below 3.0e8 mm and 6.3e8 mm) is EXACTLY representable in binary64
   (it lies in the binary64 FLT format; 10^9 < 2^53).  So a node snapped to
   the 1 mm grid, written in millimetres, round-trips through a double with
   no rounding.  (Metre values of the same nodes, n / 1000, are in general
   NOT binary64 values; the demo therefore keeps metres as exact decimals.) *)
Theorem rd_mm_grid_representable_b64 :
  forall n : Z, (Z.abs n <= 1000000000)%Z ->
    generic_format radix2 b64_fexp (IZR n).
Proof.
  intros n Hn. apply generic_format_IZR_le_bpow_prec.
  apply Z.le_trans with 1000000000%Z; [exact Hn|]. vm_compute. discriminate.
Qed.

(* The binary64 unit-grid snap and the Q snap agree on binary64 inputs: if a
   Q value has the same real value as a binary64, the snapped values agree
   too.  (HotPixel_b64.b64_snap_coord_B2R composed with §2.) *)
Theorem b64_snap_coord_Q_agree :
  forall (b : binary64) (q : Q),
    Binary.B2R prec emax b = Q2R q ->
    Binary.B2R prec emax (b64_snap_coord b) = Q2R (q_snap_coord q 1%Q).
Proof.
  intros b q Hbq. rewrite b64_snap_coord_B2R, q_snap_coord_correct.
  - rewrite hpq_Q2R_1, Hbq. reflexivity.
  - rewrite hpq_Q2R_1. lra.
Qed.

(* Soundness transfer: whenever the Qed-sound binary64 filter fires on a
   segment, the Q twin fires on the same real coordinates (unit grid). *)
Theorem b64_passes_through_implies_q :
  forall (P0 P1 C : BPoint) (Q0 Q1 QC : QPoint),
    BP2P P0 = QP2P Q0 -> BP2P P1 = QP2P Q1 -> BP2P C = QP2P QC ->
    b64_passes_through_hot_pixel P0 P1 C = true ->
    q_passes_through_closed Q0 Q1 QC 1%Q = true.
Proof.
  intros P0 P1 C Q0 Q1 QC H0 H1 HC Hb.
  apply b64_passes_through_sound in Hb.
  apply q_passes_through_closed_reflect; [rewrite hpq_Q2R_1; lra|].
  rewrite hpq_Q2R_1, <- H0, <- H1, <- HC. exact Hb.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Exact segment / segment intersection point (proper, non-parallel).     *)
(* -------------------------------------------------------------------------- *)

(* For non-parallel segments, the unique common point of the two supporting
   lines, returned only when it lies on BOTH closed segments.  Exact in Q: no
   rounding, so this is the node position that snap rounding then moves by
   at most half a grid cell (q_snap_disp_bound).  Parallel / collinear pairs
   return None (the demo's inputs do not need them). *)
Definition q_seg_intersection (P0 P1 Q0 Q1 : QPoint) : option QPoint :=
  let dx := (qx P1 - qx P0)%Q in let dy := (qy P1 - qy P0)%Q in
  let ex := (qx Q1 - qx Q0)%Q in let ey := (qy Q1 - qy Q0)%Q in
  let wx := (qx Q0 - qx P0)%Q in let wy := (qy Q0 - qy P0)%Q in
  let den := (dx * ey - dy * ex)%Q in
  if Qeq_bool den 0 then None else
  let t := ((wx * ey - wy * ex) / den)%Q in
  let u := ((wx * dy - wy * dx) / den)%Q in
  if andb (andb (Qle_bool 0 t) (Qle_bool t 1)) (andb (Qle_bool 0 u) (Qle_bool u 1))
  then Some (mkQP (qx P0 + t * dx) (qy P0 + t * dy))%Q
  else None.

Theorem q_seg_intersection_sound :
  forall P0 P1 Q0 Q1 X : QPoint,
    q_seg_intersection P0 P1 Q0 Q1 = Some X ->
    exists t u : R,
      0 <= t <= 1 /\ 0 <= u <= 1 /\
      QP2P X = segment_point (QP2P P0) (QP2P P1) t /\
      QP2P X = segment_point (QP2P Q0) (QP2P Q1) u.
Proof.
  intros P0 P1 Q0 Q1 X H. unfold q_seg_intersection in H.
  set (den := ((qx P1 - qx P0) * (qy Q1 - qy Q0) - (qy P1 - qy P0) * (qx Q1 - qx Q0))%Q) in H.
  destruct (Qeq_bool den 0) eqn:Ed; [discriminate|].
  assert (HdR : Q2R den <> 0).
  { intros Hz. rewrite <- hpq_Q2R_0 in Hz. apply hpq_Qeq_bool_R in Hz. congruence. }
  assert (Hd : ~ (den == 0)%Q) by (apply hpq_Q2R_nonzero; exact HdR).
  set (t := (((qx Q0 - qx P0) * (qy Q1 - qy Q0) - (qy Q0 - qy P0) * (qx Q1 - qx Q0)) / den)%Q) in H.
  set (u := (((qx Q0 - qx P0) * (qy P1 - qy P0) - (qy Q0 - qy P0) * (qx P1 - qx P0)) / den)%Q) in H.
  destruct (Qle_bool 0 t) eqn:E1; destruct (Qle_bool t 1) eqn:E2;
  destruct (Qle_bool 0 u) eqn:E3; destruct (Qle_bool u 1) eqn:E4;
  cbn [andb] in H; try discriminate.
  injection H as <-.
  apply hpq_Qle_bool_R in E1, E2, E3, E4. rewrite hpq_Q2R_0 in E1, E3. rewrite hpq_Q2R_1 in E2, E4.
  exists (Q2R t), (Q2R u). split; [lra|]. split; [lra|].
  unfold QP2P, segment_point. cbn [qx qy px py].
  assert (Ht : Q2R t = ((Q2R (qx Q0) - Q2R (qx P0)) * (Q2R (qy Q1) - Q2R (qy Q0))
                        - (Q2R (qy Q0) - Q2R (qy P0)) * (Q2R (qx Q1) - Q2R (qx Q0))) / Q2R den).
  { unfold t. rewrite Q2R_div by exact Hd. rewrite Q2R_minus, !Q2R_mult, !Q2R_minus. reflexivity. }
  assert (Hu : Q2R u = ((Q2R (qx Q0) - Q2R (qx P0)) * (Q2R (qy P1) - Q2R (qy P0))
                        - (Q2R (qy Q0) - Q2R (qy P0)) * (Q2R (qx P1) - Q2R (qx P0))) / Q2R den).
  { unfold u. rewrite Q2R_div by exact Hd. rewrite Q2R_minus, !Q2R_mult, !Q2R_minus. reflexivity. }
  assert (Hden : Q2R den = (Q2R (qx P1) - Q2R (qx P0)) * (Q2R (qy Q1) - Q2R (qy Q0))
                           - (Q2R (qy P1) - Q2R (qy P0)) * (Q2R (qx Q1) - Q2R (qx Q0))).
  { unfold den. rewrite Q2R_minus, !Q2R_mult, !Q2R_minus. reflexivity. }
  rewrite !Q2R_plus, !Q2R_mult, !Q2R_minus.
  rewrite Ht, Hu. rewrite Hden in HdR |- *.
  split; f_equal; field; exact HdR.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions q_round_ne_correct.
Print Assumptions q_snap_coord_correct.
Print Assumptions q_snap_correct.
Print Assumptions snap_round_coord_tolerance_scale.
Print Assumptions q_snap_disp_bound.
Print Assumptions q_touches_closed_reflect.
Print Assumptions q_passes_through_closed_reflect.
Print Assumptions q_snap_coord_unit_integer.
Print Assumptions rd_mm_grid_representable_b64.
Print Assumptions b64_snap_coord_Q_agree.
Print Assumptions b64_passes_through_implies_q.
Print Assumptions q_seg_intersection_sound.
