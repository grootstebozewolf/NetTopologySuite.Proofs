(* ============================================================================
   NetTopologySuite.Proofs.CurveRingWinding
   ----------------------------------------------------------------------------
   W1. Winding number of a curve ring (chords and CircularEgg arcs).

   wind(ms, P) = (1 / 2π) · Σ member angles, for P off the ring.
   A chord A→B contributes the signed visual angle ∠(A−P, B−P) ∈ (−π, π],
   i.e. atan2(cross, dot). An arc contributes that chord angle plus
   sweep_sign · 2π when P lies in the open circular segment between the
   chord and the arc. Segment membership is the chord half-plane cut by
   the open disk; on the circle that half-plane is the chart interval
   (CircleChart.arc_member_iff_zeta_interval). Arc members are CircularEgg
   values, not a parallel field record.

   Headline: a closed adjacent ring and a probe off the image give
   wind ∈ ℤ, because endpoint arguments telescope and every arc extra is
   an integer number of turns.

   Not discharged here (real Props, not False): wind_locally_constant,
   simple_ring_wind_class, wind_agrees_taut_height (#791), and
   area_sign_eq_winding_sign (#901). Does not import RelateNGFace and
   does not flip RNG_JordanUncond. Not the ray-crossing count in
   WindingNumber.v.

   WITNESS topic: relate · claimId: 0007-curve-ring-wind
   witness: 0007-curve-ring-wind · board: ADR-0007
   3-axiom host lane (Stdlib Reals). No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra ZArith Lia List.
From NTS.Proofs Require Import Distance Atan2 SheetHenCircEgg CircleChart Segment.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Members, visual angle, segment.                                        *)
(* -------------------------------------------------------------------------- *)

Inductive WindMember : Type :=
| WMChord (A B : Point)
| WMArc (egg : CircularEgg).

Definition member_start (m : WindMember) : Point :=
  match m with
  | WMChord A _ => A
  | WMArc c => circ_start c
  end.

Definition member_end (m : WindMember) : Point :=
  match m with
  | WMChord _ B => B
  | WMArc c => circ_end c
  end.

Definition dx (P Q : Point) : R := px Q - px P.
Definition dy (P Q : Point) : R := py Q - py P.

Definition view_arg (P Q : Point) : R := atan2 (dy P Q) (dx P Q).

Definition vcross (P A B : Point) : R :=
  dx P A * dy P B - dy P A * dx P B.

Definition vdot (P A B : Point) : R :=
  dx P A * dx P B + dy P A * dy P B.

Definition chord_angle (P A B : Point) : R :=
  atan2 (vcross P A B) (vdot P A B).

Definition egg_arc_ok (c : CircularEgg) : Prop :=
  0 < circ_r c /\
  circ_sweep c <> 0 /\
  Rabs (circ_sweep c) < 2 * PI /\
  circ_start c <> circ_end c /\
  orient_pts (circ_start c) (circ_end c) (circ_eval c (1 / 2)) <> 0.

(* Open segment: chord half-plane of the egg mid, cut by the open disk.
   On the circle the half-plane is the ζ-interval
   (segment_b_iff_chart / arc_member_iff_zeta_interval). *)
Definition in_circ_segment_b (c : CircularEgg) (P : Point) : bool :=
  let A := circ_start c in
  let B := circ_end c in
  let M := circ_eval c (1 / 2) in
  if Rlt_dec 0 (orient_pts A B M * orient_pts A B P)
  then if Rlt_dec (dist_sq (circ_o c) P) (circ_r c * circ_r c)
       then true else false
  else false.

Definition sweep_sign (c : CircularEgg) : Z :=
  if Rlt_dec 0 (circ_sweep c) then 1%Z
  else if Rlt_dec (circ_sweep c) 0 then (-1)%Z
  else 0%Z.

Definition chord_part (P : Point) (m : WindMember) : R :=
  chord_angle P (member_start m) (member_end m).

Definition arc_extra (P : Point) (m : WindMember) : R :=
  match m with
  | WMChord _ _ => 0
  | WMArc c =>
      if in_circ_segment_b c P
      then IZR (sweep_sign c) * (2 * PI)
      else 0
  end.

Definition member_angle (P : Point) (m : WindMember) : R :=
  chord_part P m + arc_extra P m.

Fixpoint sum_R (f : WindMember -> R) (ms : list WindMember) : R :=
  match ms with
  | [] => 0
  | m :: rest => f m + sum_R f rest
  end.

Definition angle_sum (P : Point) (ms : list WindMember) : R :=
  sum_R (member_angle P) ms.

Definition wind (P : Point) (ms : list WindMember) : R :=
  angle_sum P ms / (2 * PI).

Fixpoint members_adjacent (ms : list WindMember) : Prop :=
  match ms with
  | [] => True
  | m1 :: rest =>
      match rest with
      | [] => True
      | m2 :: _ =>
          member_end m1 = member_start m2 /\ members_adjacent rest
      end
  end.

Definition members_closed (ms : list WindMember) : Prop :=
  match ms with
  | [] => False
  | m :: _ => member_end (last ms m) = member_start m
  end.

Definition on_member_image (P : Point) (m : WindMember) : Prop :=
  match m with
  | WMChord A B => orient_pts A B P = 0 /\ between A B P
  | WMArc c => exists t, 0 <= t <= 1 /\ P = circ_eval c t
  end.

Definition off_ring (P : Point) (ms : list WindMember) : Prop :=
  Forall (fun m => ~ on_member_image P m) ms.

Definition off_vertex (P : Point) (m : WindMember) : Prop :=
  member_start m <> P /\ member_end m <> P.

(* -------------------------------------------------------------------------- *)
(* §2  Argument step: chord angle = Δarg − 2π k, k ∈ {−1,0,1}.               *)
(* -------------------------------------------------------------------------- *)

Lemma mkPoint_x_neq : forall x y x' y',
  x <> x' -> mkPoint x y <> mkPoint x' y'.
Proof.
  intros x y x' y' H E. apply H. apply (f_equal px) in E. exact E.
Qed.

Lemma mkPoint_y_neq : forall x y x' y',
  y <> y' -> mkPoint x y <> mkPoint x' y'.
Proof.
  intros x y x' y' H E. apply H. apply (f_equal py) in E. exact E.
Qed.

Lemma vec_nz : forall A P,
  A <> P -> ~ (dx P A = 0 /\ dy P A = 0).
Proof.
  intros A P H [Hx Hy]. apply H.
  destruct A as [ax ay], P as [px' py'].
  unfold dx, dy in Hx, Hy. cbn in Hx, Hy.
  replace ax with px' by lra. replace ay with py' by lra. reflexivity.
Qed.

Lemma dotcross_nz : forall P A B,
  A <> P -> B <> P ->
  ~ (vdot P A B = 0 /\ vcross P A B = 0).
Proof.
  intros P A B HA HB [Hd Hc].
  assert (Lag :
    vdot P A B * vdot P A B + vcross P A B * vcross P A B
    = (dx P A * dx P A + dy P A * dy P A)
      * (dx P B * dx P B + dy P B * dy P B)).
  { unfold vdot, vcross. ring. }
  rewrite Hd, Hc in Lag.
  assert (Hu : 0 < dx P A * dx P A + dy P A * dy P A).
  { pose proof (vec_nz A P HA) as Hz.
    destruct (Req_dec (dx P A) 0) as [Ex|Nx].
    - destruct (Req_dec (dy P A) 0) as [Ey|Ny].
      + exfalso. apply Hz. split; assumption.
      + nra.
    - nra. }
  assert (Hv : 0 < dx P B * dx P B + dy P B * dy P B).
  { pose proof (vec_nz B P HB) as Hz.
    destruct (Req_dec (dx P B) 0) as [Ex|Nx].
    - destruct (Req_dec (dy P B) 0) as [Ey|Ny].
      + exfalso. apply Hz. split; assumption.
      + nra.
    - nra. }
  nra.
Qed.

Lemma cos_sin_view_diff : forall P A B,
  A <> P -> B <> P ->
  let d := view_arg P B - view_arg P A in
  let ra := sqrt (dx P A * dx P A + dy P A * dy P A) in
  let rb := sqrt (dx P B * dx P B + dy P B * dy P B) in
  cos d = vdot P A B / (ra * rb) /\
  sin d = vcross P A B / (ra * rb).
Proof.
  intros P A B HA HB d ra rb.
  assert (HnA : ~ (dx P A = 0 /\ dy P A = 0)) by (apply vec_nz; exact HA).
  assert (HnB : ~ (dx P B = 0 /\ dy P B = 0)) by (apply vec_nz; exact HB).
  pose proof (cos_atan2 (dx P A) (dy P A) HnA) as HcA.
  pose proof (sin_atan2 (dx P A) (dy P A) HnA) as HsA.
  pose proof (cos_atan2 (dx P B) (dy P B) HnB) as HcB.
  pose proof (sin_atan2 (dx P B) (dy P B) HnB) as HsB.
  assert (Hra : 0 < ra) by (apply atan2_r_pos; exact HnA).
  assert (Hrb : 0 < rb) by (apply atan2_r_pos; exact HnB).
  assert (Hra0 : ra <> 0) by lra.
  assert (Hrb0 : rb <> 0) by lra.
  unfold d, view_arg.
  split.
  - rewrite cos_minus. unfold ra, rb in *.
    rewrite HcA, HsA, HcB, HsB. unfold vdot.
    field. split; assumption.
  - rewrite sin_minus. unfold ra, rb in *.
    rewrite HcA, HsA, HcB, HsB. unfold vcross.
    field. split; assumption.
Qed.

Lemma chord_cos_sin : forall P A B,
  A <> P -> B <> P ->
  let ra := sqrt (dx P A * dx P A + dy P A * dy P A) in
  let rb := sqrt (dx P B * dx P B + dy P B * dy P B) in
  cos (chord_angle P A B) = vdot P A B / (ra * rb) /\
  sin (chord_angle P A B) = vcross P A B / (ra * rb).
Proof.
  intros P A B HA HB ra rb.
  pose proof (dotcross_nz P A B HA HB) as Hdc.
  assert (Hrad :
    sqrt (vdot P A B * vdot P A B + vcross P A B * vcross P A B) = ra * rb).
  { assert (Lag :
      vdot P A B * vdot P A B + vcross P A B * vcross P A B
      = (dx P A * dx P A + dy P A * dy P A)
        * (dx P B * dx P B + dy P B * dy P B)).
    { unfold vdot, vcross. ring. }
    rewrite Lag.
    assert (Ha : 0 <= dx P A * dx P A + dy P A * dy P A).
    { pose proof (vec_nz A P HA) as Hz.
      destruct (Req_dec (dx P A) 0) as [Ex|Nx].
      - destruct (Req_dec (dy P A) 0) as [Ey|Ny].
        + exfalso. apply Hz. split; assumption.
        + nra.
      - nra. }
    assert (Hb : 0 <= dx P B * dx P B + dy P B * dy P B).
    { pose proof (vec_nz B P HB) as Hz.
      destruct (Req_dec (dx P B) 0) as [Ex|Nx].
      - destruct (Req_dec (dy P B) 0) as [Ey|Ny].
        + exfalso. apply Hz. split; assumption.
        + nra.
      - nra. }
    rewrite sqrt_mult by assumption.
    unfold ra, rb. reflexivity. }
  unfold chord_angle.
  pose proof (cos_atan2 (vdot P A B) (vcross P A B) Hdc) as Hc.
  pose proof (sin_atan2 (vdot P A B) (vcross P A B) Hdc) as Hs.
  rewrite Hc, Hs, Hrad. split; reflexivity.
Qed.

Lemma angle_delta_cos_one : forall P A B,
  A <> P -> B <> P ->
  cos (chord_angle P A B - (view_arg P B - view_arg P A)) = 1.
Proof.
  intros P A B HA HB.
  pose proof (cos_sin_view_diff P A B HA HB) as [Hc Hs].
  pose proof (chord_cos_sin P A B HA HB) as [Hc2 Hs2].
  assert (Hceq : cos (chord_angle P A B) = cos (view_arg P B - view_arg P A)).
  { rewrite Hc, Hc2. reflexivity. }
  assert (Hseq : sin (chord_angle P A B) = sin (view_arg P B - view_arg P A)).
  { rewrite Hs, Hs2. reflexivity. }
  rewrite cos_minus. rewrite Hceq, Hseq.
  set (d := view_arg P B - view_arg P A).
  pose proof (sin2_cos2 d) as Hid. unfold Rsqr in Hid.
  rewrite <- Hid. ring.
Qed.

Lemma cos_plus_2pi : forall t, cos (t + 2 * PI) = cos t.
Proof.
  intro t. pose proof (cos_period t 1%nat) as H.
  replace (INR 1) with 1 in H by reflexivity.
  replace (2 * 1 * PI) with (2 * PI) in H by ring. exact H.
Qed.

Lemma cos_minus_2pi : forall t, cos (t - 2 * PI) = cos t.
Proof.
  intro t. pose proof (cos_plus_2pi (t - 2 * PI)) as H.
  replace (t - 2 * PI + 2 * PI) with t in H by ring. symmetry. exact H.
Qed.

Definition angle_step_k (P A B : Point) : Z :=
  let t := chord_angle P A B - (view_arg P B - view_arg P A) in
  if Rle_dec (2 * PI) t then (-1)%Z
  else if Rle_dec t (- (2 * PI)) then 1%Z
  else 0%Z.

Lemma chord_angle_step : forall P A B,
  A <> P -> B <> P ->
  chord_angle P A B =
    view_arg P B - view_arg P A - 2 * PI * IZR (angle_step_k P A B).
Proof.
  intros P A B HA HB.
  set (delta := view_arg P B - view_arg P A).
  set (t := chord_angle P A B - delta).
  pose proof (angle_delta_cos_one P A B HA HB) as Ht1.
  fold delta in Ht1. fold t in Ht1.
  pose proof (atan2_range (dx P A) (dy P A) (vec_nz A P HA)) as Ha.
  pose proof (atan2_range (dx P B) (dy P B) (vec_nz B P HB)) as Hb.
  pose proof (atan2_range (vdot P A B) (vcross P A B)
                (dotcross_nz P A B HA HB)) as Hc.
  assert (Hdelta : - (2 * PI) < delta < 2 * PI).
  { unfold delta, view_arg. pose proof PI_RGT_0. lra. }
  assert (Htbd : - (3 * PI) < t < 3 * PI).
  { unfold t, chord_angle. pose proof PI_RGT_0. lra. }
  unfold angle_step_k.
  set (t0 := chord_angle P A B - (view_arg P B - view_arg P A)).
  replace t0 with t by (unfold t, delta; reflexivity).
  destruct (Rle_dec (2 * PI) t) as [Hhi|Hhi].
  - set (t' := t - 2 * PI).
    assert (Hb' : - (2 * PI) < t' < 2 * PI).
    { unfold t'. pose proof PI_RGT_0. lra. }
    assert (Hc' : cos t' = 1).
    { unfold t'. rewrite cos_minus_2pi. exact Ht1. }
    assert (Hz : t' = 0) by (apply cos_eq_1_two_pi; assumption).
    assert (Et : t = 2 * PI) by (unfold t' in Hz; lra).
    replace (IZR (-1)) with (-1) by reflexivity.
    unfold t in Et. lra.
  - destruct (Rle_dec t (- (2 * PI))) as [Hlo|Hlo].
    + set (t' := t + 2 * PI).
      assert (Hb' : - (2 * PI) < t' < 2 * PI).
      { unfold t'. pose proof PI_RGT_0. lra. }
      assert (Hc' : cos t' = 1).
      { unfold t'. rewrite cos_plus_2pi. exact Ht1. }
      assert (Hz : t' = 0) by (apply cos_eq_1_two_pi; assumption).
      assert (Et : t = - (2 * PI)) by (unfold t' in Hz; lra).
      replace (IZR 1) with 1 by reflexivity.
      unfold t in Et. lra.
    + assert (Hb' : - (2 * PI) < t < 2 * PI).
      { pose proof PI_RGT_0. lra. }
      assert (Hz : t = 0) by (apply cos_eq_1_two_pi; assumption).
      replace (IZR 0) with 0 by reflexivity.
      unfold t in Hz. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Chart half-plane.                                                      *)
(* -------------------------------------------------------------------------- *)

Lemma circ_eval_dist_sq : forall c t,
  dist_sq (circ_o c) (circ_eval c t) = circ_r c * circ_r c.
Proof.
  intros c t. unfold dist_sq, circ_eval. cbn [px py].
  set (th := circ_theta0 c + t * circ_sweep c).
  set (dx0 := px (circ_o c) - (px (circ_o c) + circ_r c * cos th)).
  set (dy0 := py (circ_o c) - (py (circ_o c) + circ_r c * sin th)).
  assert (Ex : dx0 = - (circ_r c * cos th)) by (unfold dx0; ring).
  assert (Ey : dy0 = - (circ_r c * sin th)) by (unfold dy0; ring).
  rewrite Ex, Ey.
  assert (E : cos th * cos th + sin th * sin th = 1).
  { pose proof (sin2_cos2 th) as Hid. unfold Rsqr in Hid.
    rewrite <- Hid. ring. }
  replace ((- (circ_r c * cos th)) * (- (circ_r c * cos th))
           + (- (circ_r c * sin th)) * (- (circ_r c * sin th)))
    with (circ_r c * circ_r c * (cos th * cos th + sin th * sin th)) by ring.
  rewrite E. ring.
Qed.

Lemma mid_on_chart : forall c,
  egg_arc_ok c ->
  let O := circ_o c in
  let A := circ_start c in
  let B := circ_end c in
  let M := circ_eval c (1 / 2) in
  let Q := pole_point O M (midpoint A B) in
  in_zeta_interval (zeta_of_pt O Q A) (zeta_of_pt O Q B) (zeta_of_pt O Q M).
Proof.
  intros c Hok O A B M Q.
  destruct Hok as [_ [_ [_ [Hab Horient]]]].
  assert (HAM : dist_sq O A = dist_sq O M).
  { unfold O, A, M, circ_start. rewrite !circ_eval_dist_sq. reflexivity. }
  assert (HBM : dist_sq O B = dist_sq O M).
  { unfold O, B, M, circ_end. rewrite !circ_eval_dist_sq. reflexivity. }
  assert (HMM : dist_sq O M = dist_sq O M) by reflexivity.
  assert (Hpole : M <> pole_point O M (midpoint A B)).
  { intro E.
    pose proof (pole_opposite_M O A B M HAM HBM Hab Horient) as Hop.
    rewrite <- E in Hop.
    pose proof (Rsqr_pos_lt (orient_pts A B M) Horient) as Hs.
    unfold Rsqr in Hs. nra. }
  assert (Hmem : arc_member_AB_M A B M M).
  { left.
    pose proof (Rsqr_pos_lt (orient_pts A B M) Horient) as Hs.
    unfold Rsqr in Hs. nra. }
  destruct (arc_member_iff_zeta_interval O A B M M HAM HBM HMM Hab Horient Hpole)
    as [Hfwd _].
  unfold Q. apply Hfwd. exact Hmem.
Qed.

Definition chart_halfplane (c : CircularEgg) (P : Point) : Prop :=
  let O := circ_o c in
  let A := circ_start c in
  let B := circ_end c in
  let M := circ_eval c (1 / 2) in
  let Q := pole_point O M (midpoint A B) in
  in_zeta_interval (zeta_of_pt O Q A) (zeta_of_pt O Q B) (zeta_of_pt O Q M) /\
  0 < orient_pts A B M * orient_pts A B P.

Theorem segment_b_iff_chart : forall c P,
  egg_arc_ok c ->
  (in_circ_segment_b c P = true <->
     dist_sq (circ_o c) P < circ_r c * circ_r c /\ chart_halfplane c P).
Proof.
  intros c P Hok. split.
  - intro Hb. unfold in_circ_segment_b in Hb.
    destruct (Rlt_dec 0 _) as [Hs|Hs]; [| discriminate].
    destruct (Rlt_dec _ _) as [Hd|Hd]; [| discriminate].
    split; [exact Hd |].
    split; [apply mid_on_chart; exact Hok | exact Hs].
  - intros [Hd [_ Hs]].
    unfold in_circ_segment_b.
    destruct (Rlt_dec 0 _) as [_|Hn]; [| exfalso; apply Hn; exact Hs].
    destruct (Rlt_dec _ _) as [_|Hn]; [| exfalso; apply Hn; exact Hd].
    reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Telescope.                                                             *)
(* -------------------------------------------------------------------------- *)

Fixpoint chain_k (P : Point) (ms : list WindMember) : Z :=
  match ms with
  | [] => 0%Z
  | m :: rest =>
      (angle_step_k P (member_start m) (member_end m) + chain_k P rest)%Z
  end.

Fixpoint extra_k (P : Point) (ms : list WindMember) : Z :=
  match ms with
  | [] => 0%Z
  | WMChord _ _ :: rest => extra_k P rest
  | WMArc c :: rest =>
      ((if in_circ_segment_b c P then sweep_sign c else 0%Z)
       + extra_k P rest)%Z
  end.

Lemma last_default_irrel : forall (A : Type) (l : list A) (d1 d2 : A),
  l <> [] -> last l d1 = last l d2.
Proof.
  intros A l d1 d2 H. induction l as [|a l IH].
  - contradiction.
  - destruct l as [|b l']; [reflexivity |].
    simpl. apply IH. discriminate.
Qed.

Lemma members_closed_nonempty : forall ms, members_closed ms -> ms <> [].
Proof. intros ms H. destruct ms; [exfalso; exact H | discriminate]. Qed.

Lemma off_image_endpoints : forall P m,
  ~ on_member_image P m -> off_vertex P m.
Proof.
  intros P m H. unfold off_vertex. destruct m as [A B|c].
  - split.
    + intro E. apply H. subst P. split.
      * unfold orient_pts, orient3, crs. cbn. ring.
      * apply between_P0.
    + intro E. apply H. subst P. split.
      * unfold orient_pts, orient3, crs. cbn. ring.
      * apply between_P1.
  - split.
    + intro E. apply H. exists 0. split; [lra |].
      rewrite <- E. unfold member_start, circ_start. reflexivity.
    + intro E. apply H. exists 1. split; [lra |].
      rewrite <- E. unfold member_end, circ_end. reflexivity.
Qed.

Lemma off_ring_vertices : forall P ms,
  off_ring P ms -> Forall (off_vertex P) ms.
Proof.
  intros P ms H. induction H as [|m ms Hm Hrest IH].
  - constructor.
  - constructor; [apply off_image_endpoints; exact Hm | exact IH].
Qed.

Lemma sum_chord_telescopes : forall P ms d,
  members_adjacent ms ->
  Forall (off_vertex P) ms ->
  ms <> [] ->
  sum_R (chord_part P) ms =
    view_arg P (member_end (last ms d))
    - view_arg P (member_start (hd d ms))
    - 2 * PI * IZR (chain_k P ms).
Proof.
  intros P ms.
  induction ms as [|m rest IH]; intros d Hadj Hoff Hne.
  - contradiction.
  - destruct rest as [|m2 rest'].
    + inversion Hoff as [|x l Hv Hnil]; subst x l.
      destruct Hv as [Hs He].
      cbn [sum_R chain_k last hd].
      change (chain_k P []) with 0%Z.
      unfold chord_part.
      rewrite (chord_angle_step P (member_start m) (member_end m) Hs He).
      rewrite Z.add_0_r. ring.
    + assert (Hrest : m2 :: rest' <> []) by discriminate.
      cbn [members_adjacent] in Hadj.
      destruct Hadj as [Hjoin Hadj'].
      inversion Hoff as [|x l Hv Hoff']; subst x l.
      specialize (IH d Hadj' Hoff' Hrest).
      change (sum_R (chord_part P) (m :: m2 :: rest'))
        with (chord_part P m + sum_R (chord_part P) (m2 :: rest')).
      change (chain_k P (m :: m2 :: rest'))
        with ((angle_step_k P (member_start m) (member_end m)
               + chain_k P (m2 :: rest'))%Z).
      change (hd d (m :: m2 :: rest')) with m.
      replace (last (m :: m2 :: rest') d) with (last (m2 :: rest') d)
        by reflexivity.
      unfold chord_part at 1.
      destruct Hv as [Hs He].
      rewrite (chord_angle_step P (member_start m) (member_end m) Hs He).
      rewrite IH. rewrite Hjoin. rewrite plus_IZR.
      change (hd d (m2 :: rest')) with m2.
      ring.
Qed.

Lemma sum_chord_closed : forall P ms,
  members_closed ms ->
  members_adjacent ms ->
  Forall (off_vertex P) ms ->
  sum_R (chord_part P) ms = - (2 * PI * IZR (chain_k P ms)).
Proof.
  intros P ms Hcl Hadj Hoff.
  destruct ms as [|m ms']; [contradiction |].
  pose proof (sum_chord_telescopes P (m :: ms') m Hadj Hoff
                ltac:(discriminate)) as E.
  rewrite E. cbn [hd].
  assert (Hend : member_end (last (m :: ms') m) = member_start m) by exact Hcl.
  rewrite Hend. ring.
Qed.

Lemma sum_extra_int : forall P ms,
  sum_R (arc_extra P) ms = 2 * PI * IZR (extra_k P ms).
Proof.
  intros P ms. induction ms as [|m ms IH].
  - cbn. replace (IZR 0) with 0 by reflexivity. ring.
  - destruct m as [A B|c].
    + cbn [sum_R arc_extra extra_k]. rewrite IH. ring.
    + cbn [sum_R arc_extra extra_k].
      destruct (in_circ_segment_b c P) eqn:Hb.
      * rewrite IH. rewrite plus_IZR. ring.
      * rewrite IH. rewrite Z.add_0_l. ring.
Qed.

Lemma sum_angle_split : forall P ms,
  angle_sum P ms = sum_R (chord_part P) ms + sum_R (arc_extra P) ms.
Proof.
  intros P ms. unfold angle_sum. induction ms as [|m ms IH].
  - cbn. ring.
  - cbn [sum_R]. rewrite IH. unfold member_angle. ring.
Qed.

Lemma mul_div_2pi : forall z, (2 * PI * z) / (2 * PI) = z.
Proof.
  intro z. pose proof PI_RGT_0. field. lra.
Qed.

Theorem wind_integer : forall P ms,
  members_closed ms ->
  members_adjacent ms ->
  off_ring P ms ->
  exists n : Z, wind P ms = IZR n.
Proof.
  intros P ms Hcl Hadj Hoff.
  pose proof (off_ring_vertices P ms Hoff) as Hv.
  unfold wind. rewrite sum_angle_split.
  rewrite (sum_chord_closed P ms Hcl Hadj Hv).
  rewrite (sum_extra_int P ms).
  replace (- (2 * PI * IZR (chain_k P ms)) + 2 * PI * IZR (extra_k P ms))
    with (2 * PI * (IZR (extra_k P ms) - IZR (chain_k P ms))) by ring.
  rewrite mul_div_2pi. rewrite <- minus_IZR.
  exists (extra_k P ms - chain_k P ms)%Z. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Fixtures from #804: locked_rect, locked_lens, grazing diamond.        *)
(* -------------------------------------------------------------------------- *)

Definition rect_probe : Point := mkPoint (1 / 2) (1 / 2).

Definition locked_rect : list WindMember :=
  [ WMChord (mkPoint 0 0) (mkPoint 1 0)
  ; WMChord (mkPoint 1 0) (mkPoint 1 1)
  ; WMChord (mkPoint 1 1) (mkPoint 0 1)
  ; WMChord (mkPoint 0 1) (mkPoint 0 0) ].

Lemma chord_angle_halfpi : forall P A B,
  vcross P A B = 1 / 2 ->
  vdot P A B = 0 ->
  chord_angle P A B = PI / 2.
Proof.
  intros P A B Hc Hd. unfold chord_angle. rewrite Hc, Hd.
  replace (1 / 2) with ((1 / 2) * 1) by field.
  replace 0 with ((1 / 2) * 0) at 1 by field.
  rewrite (atan2_pos_scale (1 / 2) 1 0) by lra.
  apply atan2_pos_y_axis. lra.
Qed.

Lemma not_on_chord_orient : forall P A B,
  orient_pts A B P <> 0 -> ~ on_member_image P (WMChord A B).
Proof.
  intros P A B H [Ho _]. apply H. exact Ho.
Qed.

Lemma locked_rect_wind_one :
  members_closed locked_rect /\
  members_adjacent locked_rect /\
  off_ring rect_probe locked_rect /\
  wind rect_probe locked_rect = 1.
Proof.
  split; [| split; [| split]].
  - cbn. reflexivity.
  - cbn. repeat split; reflexivity.
  - repeat constructor; apply not_on_chord_orient; unfold orient_pts, orient3, crs;
      cbn; lra.
  - unfold wind, angle_sum, locked_rect.
    cbn [sum_R]. unfold member_angle, chord_part.
    cbn [member_start member_end arc_extra].
    assert (H1 : chord_angle rect_probe (mkPoint 0 0) (mkPoint 1 0) = PI / 2).
    { apply chord_angle_halfpi; unfold vcross, vdot, dx, dy, rect_probe; cbn; field. }
    assert (H2 : chord_angle rect_probe (mkPoint 1 0) (mkPoint 1 1) = PI / 2).
    { apply chord_angle_halfpi; unfold vcross, vdot, dx, dy, rect_probe; cbn; field. }
    assert (H3 : chord_angle rect_probe (mkPoint 1 1) (mkPoint 0 1) = PI / 2).
    { apply chord_angle_halfpi; unfold vcross, vdot, dx, dy, rect_probe; cbn; field. }
    assert (H4 : chord_angle rect_probe (mkPoint 0 1) (mkPoint 0 0) = PI / 2).
    { apply chord_angle_halfpi; unfold vcross, vdot, dx, dy, rect_probe; cbn; field. }
    rewrite H1, H2, H3, H4.
    replace (PI / 2 + 0 + (PI / 2 + 0 + (PI / 2 + 0 + (PI / 2 + 0 + 0))))
      with (2 * PI) by field.
    pose proof PI_RGT_0. field. lra.
Qed.

Definition lens_egg : CircularEgg :=
  mkCircularEgg (mkPoint 0 0) 1 0 PI.

Definition lens_probe : Point := mkPoint 0 (1 / 2).

Definition locked_lens : list WindMember :=
  [ WMArc lens_egg
  ; WMChord (mkPoint (-1) 0) (mkPoint 1 0) ].

Lemma lens_controls :
  circ_start lens_egg = mkPoint 1 0 /\
  circ_eval lens_egg (1 / 2) = mkPoint 0 1 /\
  circ_end lens_egg = mkPoint (-1) 0.
Proof.
  unfold circ_start, circ_end, circ_eval, lens_egg. cbn.
  assert (Hs : 0 + 0 * PI = 0) by field.
  assert (Hm : 0 + 1 / 2 * PI = PI / 2) by field.
  assert (He : 0 + 1 * PI = PI) by field.
  rewrite Hs, Hm, He, cos_0, sin_0, cos_PI2, sin_PI2, cos_PI, sin_PI.
  repeat split; f_equal; field.
Qed.

Lemma lens_egg_ok : egg_arc_ok lens_egg.
Proof.
  destruct lens_controls as [Hs [Hm He]].
  repeat split.
  - unfold lens_egg. cbn. lra.
  - unfold lens_egg. cbn. pose proof PI_RGT_0. lra.
  - unfold lens_egg. cbn. pose proof PI_RGT_0.
    rewrite Rabs_right; lra.
  - rewrite Hs, He. apply mkPoint_x_neq. lra.
  - rewrite Hs, He, Hm. unfold orient_pts, orient3, crs. cbn. lra.
Qed.

Lemma lens_in_segment : in_circ_segment_b lens_egg lens_probe = true.
Proof.
  destruct lens_controls as [Hs [Hm He]].
  unfold in_circ_segment_b. rewrite Hs, Hm, He.
  assert (Hside : 0 < orient_pts (mkPoint 1 0) (mkPoint (-1) 0) (mkPoint 0 1)
                      * orient_pts (mkPoint 1 0) (mkPoint (-1) 0) lens_probe).
  { unfold orient_pts, orient3, crs, lens_probe. cbn. lra. }
  assert (Hdisk : dist_sq (circ_o lens_egg) lens_probe
                  < circ_r lens_egg * circ_r lens_egg).
  { unfold dist_sq, lens_egg, lens_probe. cbn. lra. }
  destruct (Rlt_dec 0 _) as [_|Hn]; [| exfalso; apply Hn; exact Hside].
  destruct (Rlt_dec _ _) as [_|Hn]; [| exfalso; apply Hn; exact Hdisk].
  reflexivity.
Qed.

Lemma lens_sweep_one : sweep_sign lens_egg = 1%Z.
Proof.
  unfold sweep_sign, lens_egg. cbn [circ_sweep].
  destruct (Rlt_dec 0 PI) as [_|H]; [reflexivity |].
  pose proof PI_RGT_0. exfalso. apply H. lra.
Qed.

Lemma atan2_opp : forall y x,
  ~ (x = 0 /\ y = 0) ->
  y <> 0 ->
  atan2 (- y) x = - atan2 y x.
Proof.
  intros y x Hne Hy.
  set (a := atan2 y x).
  pose proof (atan2_range x y Hne) as Ha.
  pose proof (cos_atan2 x y Hne) as Hc.
  pose proof (sin_atan2 x y Hne) as Hs.
  assert (Hne' : ~ (x = 0 /\ - y = 0)) by (intros [Hx Hy0]; apply Hy; lra).
  assert (Ha_ne_pi : a <> PI).
  { intro E. unfold a in E. rewrite E in Hs. rewrite sin_PI in Hs.
    pose proof (atan2_r_pos x y Hne) as Hr.
    unfold Rdiv in Hs.
    assert (E0 : / sqrt (x * x + y * y) * y = 0).
    { rewrite Rmult_comm. symmetry. exact Hs. }
    apply Hy.
    apply (Rmult_eq_reg_l (/ sqrt (x * x + y * y))).
    - rewrite E0. rewrite Rmult_0_r. reflexivity.
    - apply Rinv_neq_0_compat. lra. }
  assert (Hrng : - PI < - a <= PI).
  { destruct Ha as [Hlo Hhi].
    destruct (Rle_lt_or_eq_dec _ _ Hhi) as [Hlt|Heq].
    - split.
      + apply Ropp_lt_contravar. exact Hlt.
      + apply Rlt_le.
        assert (Hop : - a < - (- PI)) by (apply Ropp_lt_contravar; exact Hlo).
        replace (- (- PI)) with PI in Hop by ring. exact Hop.
    - contradiction. }
  apply eq_sym. apply atan2_unique; try assumption.
  - rewrite cos_neg. unfold a. rewrite Hc.
    replace (x * x + - y * - y) with (x * x + y * y) by ring. reflexivity.
  - rewrite sin_neg. unfold a. rewrite Hs.
    replace (x * x + - y * - y) with (x * x + y * y) by ring. field.
    pose proof (atan2_r_pos x y Hne) as Hr. lra.
Qed.

Lemma chord_angle_rev : forall P A B,
  A <> P -> B <> P ->
  vcross P A B <> 0 ->
  chord_angle P B A = - chord_angle P A B.
Proof.
  intros P A B HA HB Hc.
  unfold chord_angle.
  replace (vcross P B A) with (- vcross P A B)
    by (unfold vcross, dx, dy; ring).
  replace (vdot P B A) with (vdot P A B)
    by (unfold vdot, dx, dy; ring).
  apply atan2_opp.
  - intros [Hd Hx]. apply Hc. lra.
  - exact Hc.
Qed.

Lemma locked_lens_wind_one :
  members_closed locked_lens /\
  members_adjacent locked_lens /\
  egg_arc_ok lens_egg /\
  off_ring lens_probe locked_lens /\
  wind lens_probe locked_lens = 1.
Proof.
  split; [| split; [| split; [| split]]].
  - destruct lens_controls as [Hs [_ _]]. cbn. rewrite <- Hs. reflexivity.
  - destruct lens_controls as [_ [_ He]]. cbn. rewrite He. split; reflexivity.
  - exact lens_egg_ok.
  - constructor.
    + intro Hex. destruct Hex as [t [_ Ht]].
      assert (Hd : dist_sq (circ_o lens_egg) lens_probe
                   = circ_r lens_egg * circ_r lens_egg).
      { rewrite Ht. apply circ_eval_dist_sq. }
      revert Hd. unfold dist_sq, lens_egg, lens_probe. cbn. lra.
    + constructor; [| constructor].
      apply not_on_chord_orient.
      destruct lens_controls as [_ [_ He]].
      unfold orient_pts, orient3, crs, lens_probe. cbn. lra.
  - destruct lens_controls as [Hs [_ He]].
    unfold wind, angle_sum, locked_lens.
    cbn [sum_R]. unfold member_angle, chord_part.
    cbn [member_start member_end arc_extra].
    rewrite lens_in_segment, lens_sweep_one.
    replace (IZR 1) with 1 by reflexivity.
    assert (HA : circ_start lens_egg <> lens_probe).
    { rewrite Hs. apply mkPoint_x_neq. unfold lens_probe. cbn. lra. }
    assert (HB : circ_end lens_egg <> lens_probe).
    { rewrite He. apply mkPoint_x_neq. unfold lens_probe. cbn. lra. }
    assert (Hc : vcross lens_probe (circ_start lens_egg) (circ_end lens_egg) <> 0).
    { rewrite Hs, He. unfold vcross, dx, dy, lens_probe. cbn. lra. }
    rewrite <- Hs, <- He.
    rewrite (chord_angle_rev lens_probe (circ_start lens_egg) (circ_end lens_egg)
               HA HB Hc).
    replace (chord_angle lens_probe (circ_start lens_egg) (circ_end lens_egg)
             + 1 * (2 * PI)
             + (- chord_angle lens_probe (circ_start lens_egg) (circ_end lens_egg)
                + 0 + 0))
      with (2 * PI) by ring.
    pose proof PI_RGT_0. field. lra.
Qed.

Definition graz_A : Point := mkPoint 0 (1 / 2).
Definition graz_B : Point := mkPoint 0 0.

Definition grazing_diamond : list WindMember :=
  [ WMChord (mkPoint 0 1) (mkPoint 1 0)
  ; WMChord (mkPoint 1 0) (mkPoint 0 (-1))
  ; WMChord (mkPoint 0 (-1)) (mkPoint (-1) 0)
  ; WMChord (mkPoint (-1) 0) (mkPoint 0 1) ].

Lemma chord_angle_neg_halfpi : forall P A B,
  vcross P A B = -1 ->
  vdot P A B = 0 ->
  chord_angle P A B = - (PI / 2).
Proof.
  intros P A B Hc Hd. unfold chord_angle. rewrite Hc, Hd.
  apply atan2_neg_y_axis. lra.
Qed.

Lemma grazing_B_angles :
  members_closed grazing_diamond /\
  members_adjacent grazing_diamond /\
  off_ring graz_B grazing_diamond /\
  wind graz_B grazing_diamond = -1.
Proof.
  split; [| split; [| split]].
  - cbn. reflexivity.
  - cbn. repeat split; reflexivity.
  - repeat constructor; apply not_on_chord_orient; unfold orient_pts, orient3, crs;
      cbn; lra.
  - unfold wind, angle_sum, grazing_diamond.
    cbn [sum_R]. unfold member_angle, chord_part.
    cbn [member_start member_end arc_extra].
    assert (H1 : chord_angle graz_B (mkPoint 0 1) (mkPoint 1 0) = - (PI / 2)).
    { apply chord_angle_neg_halfpi; unfold vcross, vdot, dx, dy, graz_B; cbn; field. }
    assert (H2 : chord_angle graz_B (mkPoint 1 0) (mkPoint 0 (-1)) = - (PI / 2)).
    { apply chord_angle_neg_halfpi; unfold vcross, vdot, dx, dy, graz_B; cbn; field. }
    assert (H3 : chord_angle graz_B (mkPoint 0 (-1)) (mkPoint (-1) 0) = - (PI / 2)).
    { apply chord_angle_neg_halfpi; unfold vcross, vdot, dx, dy, graz_B; cbn; field. }
    assert (H4 : chord_angle graz_B (mkPoint (-1) 0) (mkPoint 0 1) = - (PI / 2)).
    { apply chord_angle_neg_halfpi; unfold vcross, vdot, dx, dy, graz_B; cbn; field. }
    rewrite H1, H2, H3, H4.
    replace (- (PI / 2) + 0 + (- (PI / 2) + 0 + (- (PI / 2) + 0 + (- (PI / 2) + 0 + 0))))
      with (- (2 * PI)) by field.
    replace (- (2 * PI) / (2 * PI)) with (-1) by (pose proof PI_RGT_0; field; lra).
    reflexivity.
Qed.

Lemma atan2_neg_of_y : forall y x,
  ~ (x = 0 /\ y = 0) -> y < 0 -> atan2 y x < 0.
Proof.
  intros y x Hne Hy.
  pose proof (sin_atan2 x y Hne) as Hs.
  pose proof (atan2_range x y Hne) as Hb.
  pose proof (atan2_r_pos x y Hne) as Hr.
  assert (Hsn : sin (atan2 y x) < 0).
  { rewrite Hs. unfold Rdiv.
    assert (0 < / sqrt (x * x + y * y)) by (apply Rinv_0_lt_compat; exact Hr).
    nra. }
  destruct (Rtotal_order 0 (atan2 y x)) as [Hpos|[Heq|Hneg]].
  - destruct Hb as [_ Hhi].
    destruct (Req_EM_T (atan2 y x) PI) as [Ep|Np].
    + rewrite Ep, sin_PI in Hsn. lra.
    + assert (Hlt : atan2 y x < PI) by lra.
      pose proof (sin_gt_0 (atan2 y x) Hpos Hlt) as Hsp. lra.
  - rewrite <- Heq, sin_0 in Hsn. lra.
  - exact Hneg.
Qed.

Lemma chord_angle_strict_neg : forall P A B,
  vcross P A B < 0 -> - PI < chord_angle P A B < 0.
Proof.
  intros P A B Hc. unfold chord_angle. split.
  - apply atan2_range. intros [_ Hy]. lra.
  - apply atan2_neg_of_y; [| exact Hc]. intros [_ Hy]. lra.
Qed.

Lemma izr_only_neg1 : forall n : Z, -2 < IZR n < 0 -> n = (-1)%Z.
Proof.
  intros n [Hlo Hhi].
  destruct (Z_lt_le_dec n (-1)) as [Hn|Hn].
  - assert (Hle : (n <= -2)%Z) by lia.
    pose proof (IZR_le _ _ Hle) as Hz.
    assert (E : IZR (-2) = -2).
    { replace (-2)%Z with (Z.opp 2) by reflexivity.
      rewrite opp_IZR. replace (IZR 2) with 2 by reflexivity. ring. }
    lra.
  - destruct (Z_lt_le_dec (-1) n) as [Hn'|Hn'].
    + assert (Hge : (0 <= n)%Z) by lia.
      pose proof (IZR_le _ _ Hge) as Hz.
      replace (IZR 0) with 0 in Hz by reflexivity. lra.
    + lia.
Qed.

Lemma grazing_A_wind :
  off_ring graz_A grazing_diamond /\
  wind graz_A grazing_diamond = -1.
Proof.
  split.
  - repeat constructor; apply not_on_chord_orient; unfold orient_pts, orient3, crs;
      unfold graz_A; cbn; lra.
  - destruct grazing_B_angles as [Hcl [Hadj [_ _]]].
    destruct (wind_integer graz_A grazing_diamond Hcl Hadj
                ltac:(repeat constructor; apply not_on_chord_orient;
                      unfold orient_pts, orient3, crs, graz_A; cbn; lra))
      as [n Hn].
    assert (Hs : angle_sum graz_A grazing_diamond = 2 * PI * IZR n).
    { unfold wind in Hn. pose proof PI_RGT_0.
      assert (E : angle_sum graz_A grazing_diamond
                  = (angle_sum graz_A grazing_diamond / (2 * PI)) * (2 * PI))
        by (field; lra).
      rewrite Hn in E. rewrite E. ring. }
    unfold angle_sum, grazing_diamond in Hs.
    cbn [sum_R] in Hs. unfold member_angle, chord_part in Hs.
    cbn [member_start member_end arc_extra] in Hs.
    set (a1 := chord_angle graz_A (mkPoint 0 1) (mkPoint 1 0)) in *.
    set (a2 := chord_angle graz_A (mkPoint 1 0) (mkPoint 0 (-1))) in *.
    set (a3 := chord_angle graz_A (mkPoint 0 (-1)) (mkPoint (-1) 0)) in *.
    set (a4 := chord_angle graz_A (mkPoint (-1) 0) (mkPoint 0 1)) in *.
    assert (C1 : vcross graz_A (mkPoint 0 1) (mkPoint 1 0) < 0)
      by (unfold vcross, dx, dy, graz_A; cbn; lra).
    assert (C2 : vcross graz_A (mkPoint 1 0) (mkPoint 0 (-1)) < 0)
      by (unfold vcross, dx, dy, graz_A; cbn; lra).
    assert (C3 : vcross graz_A (mkPoint 0 (-1)) (mkPoint (-1) 0) < 0)
      by (unfold vcross, dx, dy, graz_A; cbn; lra).
    assert (C4 : vcross graz_A (mkPoint (-1) 0) (mkPoint 0 1) < 0)
      by (unfold vcross, dx, dy, graz_A; cbn; lra).
    pose proof (chord_angle_strict_neg _ _ _ C1) as B1.
    pose proof (chord_angle_strict_neg _ _ _ C2) as B2.
    pose proof (chord_angle_strict_neg _ _ _ C3) as B3.
    pose proof (chord_angle_strict_neg _ _ _ C4) as B4.
    fold a1 in B1. fold a2 in B2. fold a3 in B3. fold a4 in B4.
    assert (Hsum : - (4 * PI) < a1 + a2 + a3 + a4 < 0) by lra.
    assert (Esum : a1 + 0 + (a2 + 0 + (a3 + 0 + (a4 + 0 + 0))) = a1 + a2 + a3 + a4)
      by ring.
    rewrite Esum in Hs.
    assert (Hnrg : -2 < IZR n < 0).
    { pose proof PI_RGT_0 as Hp.
      assert (Hpos : 0 < 2 * PI) by lra.
      split.
      - apply (Rmult_lt_reg_l (2 * PI)); [exact Hpos |].
        replace (2 * PI * -2) with (- (4 * PI)) by ring.
        replace (2 * PI * IZR n) with (a1 + a2 + a3 + a4) by exact Hs.
        lra.
      - apply (Rmult_lt_reg_l (2 * PI)); [exact Hpos |].
        replace (2 * PI * IZR n) with (a1 + a2 + a3 + a4) by exact Hs.
        replace (2 * PI * 0) with 0 by ring. lra. }
    assert (En : n = (-1)%Z) by (apply izr_only_neg1; exact Hnrg).
    rewrite En in Hn. rewrite Hn. replace (IZR (-1)) with (-1) by reflexivity.
    reflexivity.
Qed.

Lemma grazing_diamond_wind_neg_one :
  wind graz_B grazing_diamond = -1 /\
  wind graz_A grazing_diamond = -1.
Proof.
  split.
  - exact (proj2 (proj2 (proj2 grazing_B_angles))).
  - exact (proj2 grazing_A_wind).
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Deferred obligations. Real Props. Not discharged. Not False.          *)
(* -------------------------------------------------------------------------- *)

Definition lerp (P Q : Point) (t : R) : Point :=
  mkPoint (px P + t * (px Q - px P)) (py P + t * (py Q - py P)).

Definition seg_off (ms : list WindMember) (P Q : Point) : Prop :=
  forall t, 0 <= t <= 1 -> off_ring (lerp P Q t) ms.

Definition bounded_component (ms : list WindMember) (P : Point) : Prop :=
  off_ring P ms /\
  exists R, forall Q, seg_off ms P Q -> dist_sq (mkPoint 0 0) Q <= R.

Definition member_chord_cross (m1 m2 : WindMember) : Prop :=
  let A := member_start m1 in let B := member_end m1 in
  let C := member_start m2 in let D := member_end m2 in
  A <> C /\ A <> D /\ B <> C /\ B <> D /\
  0 < orient_pts A B C * orient_pts A B D /\
  orient_pts C D A * orient_pts C D B < 0.

Definition endpoint_nocross (ms : list WindMember) : Prop :=
  forall m1 m2, In m1 ms -> In m2 ms -> ~ member_chord_cross m1 m2.

(* Off the ring, winding is constant along a complement segment. *)
Definition wind_locally_constant : Prop :=
  forall ms P Q,
    members_closed ms ->
    members_adjacent ms ->
    off_ring P ms ->
    off_ring Q ms ->
    seg_off ms P Q ->
    wind P ms = wind Q ms.

(* Simple rings: wind ∈ {−1,0,1}, and ±1 is exactly the bounded side.
   endpoint_nocross bans a proper crossing of member chords (the #804
   diamond and the unit rectangle pass; a pentagram does not). *)
Definition simple_ring_wind_class : Prop :=
  forall ms P,
    members_closed ms ->
    members_adjacent ms ->
    NoDup (map member_start ms) ->
    endpoint_nocross ms ->
    off_ring P ms ->
    (wind P ms = -1 \/ wind P ms = 0 \/ wind P ms = 1) /\
    ((wind P ms = 1 \/ wind P ms = -1) <-> bounded_component ms P).

(* #791 relateng_jordan_true_region_taut: a taut chord ring's odd bounded
   witness and even unbounded witness are nonzero and zero winding.
   The ray predicate is not re-imported; the split is the obligation. *)
Definition wind_agrees_taut_height : Prop :=
  forall ms,
    members_closed ms ->
    members_adjacent ms ->
    (forall m, In m ms -> exists A B, m = WMChord A B) ->
    (exists P, off_ring P ms /\ (wind P ms = 1 \/ wind P ms = -1)) ->
    exists p_in p_out,
      off_ring p_in ms /\ off_ring p_out ms /\
      (wind p_in ms = 1 \/ wind p_in ms = -1) /\
      wind p_out ms = 0.

(* Signed shoelace of chords, plus the circular-segment term
   (1/2) r² (sweep − sin sweep) on an egg. #901's members_area is this
   sign; the sign law is not proved here. *)
Definition wind_members_area (ms : list WindMember) : R :=
  fold_right (fun m acc =>
    match m with
    | WMChord A B =>
        px A * py B - py A * px B
    | WMArc c =>
        px (circ_start c) * py (circ_end c)
        - py (circ_start c) * px (circ_end c)
        + circ_r c * circ_r c * (circ_sweep c - sin (circ_sweep c))
    end + acc) 0 ms.

Definition area_sign_eq_winding_sign : Prop :=
  forall ms P,
    members_closed ms ->
    members_adjacent ms ->
    off_ring P ms ->
    wind P ms <> 0 ->
    0 < wind_members_area ms * wind P ms.

(* WITNESS {"claimId":"0007-curve-ring-wind","topic":"relate","lemma":"wind_integer","title":"closed curve ring, probe off the image: winding is an integer; locked_rect and locked_lens wind 1, grazing diamond winds -1 at the ray-graze point and at the odd-parity point","file":"theories/CurveRingWinding.v","witness":"0007-curve-ring-wind","board":"ADR-0007"} *)
Theorem ticket_0007_curve_ring_wind_qed_or_qex :
  (forall P ms,
      members_closed ms ->
      members_adjacent ms ->
      off_ring P ms ->
      exists n : Z, wind P ms = IZR n) /\
  wind rect_probe locked_rect = 1 /\
  wind lens_probe locked_lens = 1 /\
  wind graz_B grazing_diamond = -1 /\
  wind graz_A grazing_diamond = -1.
Proof.
  split; [exact wind_integer |].
  split; [exact (proj2 (proj2 (proj2 locked_rect_wind_one))) |].
  split; [exact (proj2 (proj2 (proj2 (proj2 locked_lens_wind_one)))) |].
  exact grazing_diamond_wind_neg_one.
Qed.

Print Assumptions mkPoint_x_neq.
Print Assumptions mkPoint_y_neq.
Print Assumptions vec_nz.
Print Assumptions dotcross_nz.
Print Assumptions cos_sin_view_diff.
Print Assumptions chord_cos_sin.
Print Assumptions angle_delta_cos_one.
Print Assumptions cos_plus_2pi.
Print Assumptions cos_minus_2pi.
Print Assumptions chord_angle_step.
Print Assumptions circ_eval_dist_sq.
Print Assumptions mid_on_chart.
Print Assumptions segment_b_iff_chart.
Print Assumptions last_default_irrel.
Print Assumptions members_closed_nonempty.
Print Assumptions off_image_endpoints.
Print Assumptions off_ring_vertices.
Print Assumptions sum_chord_telescopes.
Print Assumptions sum_chord_closed.
Print Assumptions sum_extra_int.
Print Assumptions sum_angle_split.
Print Assumptions mul_div_2pi.
Print Assumptions wind_integer.
Print Assumptions chord_angle_halfpi.
Print Assumptions not_on_chord_orient.
Print Assumptions locked_rect_wind_one.
Print Assumptions lens_controls.
Print Assumptions lens_egg_ok.
Print Assumptions lens_in_segment.
Print Assumptions lens_sweep_one.
Print Assumptions chord_angle_rev.
Print Assumptions atan2_opp.
Print Assumptions locked_lens_wind_one.
Print Assumptions chord_angle_neg_halfpi.
Print Assumptions grazing_B_angles.
Print Assumptions atan2_neg_of_y.
Print Assumptions chord_angle_strict_neg.
Print Assumptions izr_only_neg1.
Print Assumptions grazing_A_wind.
Print Assumptions grazing_diamond_wind_neg_one.
Print Assumptions ticket_0007_curve_ring_wind_qed_or_qex.
