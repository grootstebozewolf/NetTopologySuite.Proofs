(* ============================================================================
   NetTopologySuite.Proofs.ArcLinearize
   ----------------------------------------------------------------------------
   GEOS-aligned arc linearizer on a certified intake egg (θ0, Δθ).
   Behavioural reference only (do not copy; GEOS is LGPL):
   CircularArc::addLinearizedPoints, CurveToLineParams,
   CircularArcs::interpolateZM.

   Vertex formula (directed order, proved equal to the CCW walk below):
     γ(t) = O + r·(cos(θ0 + t·Δθ), sin(θ0 + t·Δθ))
     p0   = γ(0)           (previous segment; included in `linearize`)
     p_k  = γ(k/n)         for k = 1 .. n-1
     p_n  = γ(1)           exactly (`circ_end`, not a fresh sample)
   CCW walk: sample the |Δθ|-sweep from its CCW start at k/n,
   reverse that interior list when Δθ < 0, then append γ(1).
   n is a parameter satisfying `subdiv_ok` (n = max(ceil(|Δθ|/step), 2)).
   Existence of that n uses archimedean `up`, outside the 3-axiom
   allowlist, so it is not constructed here.

   Z/M: None is NaN. Exact at t=0, t=1, and at t_m when the ordinate
   and the parameter are both present. Otherwise piecewise linear in
   the parameter (hence in angle when Δθ ≠ 0) on p0→p1 or p1→p2.
   Missing p1 ordinate, or a missing p1 parameter, interpolates p0→p2.

   `CurveGeometry.chord_approx_arc` stays the inscribed control polygon.
   Densifying it falsifies the control-triangle reductions.

   claimId: none. verified-claims.md has no chord-densifier id.
   ArcChordDensity / ArcChordSubdivision / Linearise are other witnesses.
   3-axiom host. No Admitted / Axiom / Parameter. No RiemannInt.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia Field Psatz List PeanoNat.
From NTS.Proofs Require Import Distance SheetHenCircEgg Atan2.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Step count. The archimedean witness is the open gap (see the header).      *)
(* -------------------------------------------------------------------------- *)

Definition subdiv_ok (step sweep : R) (n : nat) : Prop :=
  (2 <= n)%nat /\
  0 < step /\
  Rabs sweep <= INR n * step /\
  ((n = 2)%nat \/ INR (n - 1) * step < Rabs sweep).

(* -------------------------------------------------------------------------- *)
(* CCW-normalized walk.                                                       *)
(* -------------------------------------------------------------------------- *)

Definition ccw_egg (c : CircularEgg) : CircularEgg :=
  mkCircularEgg (circ_o c) (circ_r c)
    (if Rle_dec 0 (circ_sweep c) then circ_theta0 c
     else circ_theta0 c + circ_sweep c)
    (Rabs (circ_sweep c)).

Definition ccw_interiors (c : CircularEgg) (n : nat) : list Point :=
  map (fun k => circ_eval (ccw_egg c) (INR k / INR n)) (seq 1 (Nat.pred n)).

Definition lin_interiors (c : CircularEgg) (n : nat) : list Point :=
  if Rle_dec 0 (circ_sweep c) then ccw_interiors c n else rev (ccw_interiors c n).

Definition lin_pts (c : CircularEgg) (n : nat) : list Point :=
  circ_start c :: lin_interiors c n ++ [circ_end c].

Definition direct_pt (c : CircularEgg) (n k : nat) : Point :=
  if (k =? 0)%nat then circ_start c
  else if (k =? n)%nat then circ_end c
  else circ_eval c (INR k / INR n).

Definition lin_pts_direct (c : CircularEgg) (n : nat) : list Point :=
  map (direct_pt c n) (seq 0 (S n)).

Definition rev_egg (c : CircularEgg) : CircularEgg :=
  mkCircularEgg (circ_o c) (circ_r c)
    (circ_theta0 c + circ_sweep c) (- circ_sweep c).

Definition vtx_t (n k : nat) : R :=
  if (k =? n)%nat then 1 else INR k / INR n.

(* -------------------------------------------------------------------------- *)
(* Z/M. None is NaN.                                                          *)
(* -------------------------------------------------------------------------- *)

Definition lerp (a b u : R) : R := (1 - u) * a + u * b.

Definition zm_at (z0 z1 z2 : option R) (tm : option R) (t : R) : option R :=
  if Req_EM_T t 0 then z0
  else if Req_EM_T t 1 then z2
  else
    match z1, tm with
    | Some b, Some m =>
        if Req_EM_T t m then Some b
        else if Rle_dec t m then
          match z0 with
          | Some a => Some (lerp a b (t / m))
          | None => None
          end
        else
          match z2 with
          | Some c => Some (lerp b c ((t - m) / (1 - m)))
          | None => None
          end
    | _, _ =>
        match z0, z2 with
        | Some a, Some c => Some (lerp a c t)
        | _, _ => None
        end
    end.

Definition lin_angle (c : CircularEgg) (t : R) : R :=
  circ_theta0 c + t * circ_sweep c.

(* -------------------------------------------------------------------------- *)
(* Vertices.                                                                  *)
(* -------------------------------------------------------------------------- *)

Record LinVtx : Type := mkLinVtx {
  lv_p : Point;
  lv_z : option R;
  lv_m : option R
}.

Definition circ_vtx (c : CircularEgg) (tm : option R)
    (z0 z1 z2 m0 m1 m2 : option R) (n k : nat) : LinVtx :=
  mkLinVtx
    (nth k (lin_pts c n) (circ_start c))
    (zm_at z0 z1 z2 tm (vtx_t n k))
    (zm_at m0 m1 m2 tm (vtx_t n k)).

Definition circ_lin_vtxs (c : CircularEgg) (tm : option R)
    (z0 z1 z2 m0 m1 m2 : option R) (n : nat) : list LinVtx :=
  map (circ_vtx c tm z0 z1 z2 m0 m1 m2 n) (seq 0 (S n)).

Inductive LinArc : Type :=
| LinCollinear (p0 p2 : Point) (z0 z2 m0 m2 : option R)
| LinCircular (c : CircularEgg) (tm : option R)
    (z0 z1 z2 m0 m1 m2 : option R).

Definition shift_tm (tm : option R) : option R :=
  option_map (fun m => 1 - m) tm.

Definition lin_reverse (a : LinArc) : LinArc :=
  match a with
  | LinCollinear p0 p2 z0 z2 m0 m2 =>
      LinCollinear p2 p0 z2 z0 m2 m0
  | LinCircular c tm z0 z1 z2 m0 m1 m2 =>
      LinCircular (rev_egg c) (shift_tm tm) z2 z1 z0 m2 m1 m0
  end.

Definition ord_rev_ok (tm : option R) (z1 : option R) : Prop :=
  match tm, z1 with
  | Some m, Some _ => 0 < m < 1
  | _, _ => True
  end.

Definition lin_rev_ok (a : LinArc) : Prop :=
  match a with
  | LinCollinear _ _ _ _ _ _ => True
  | LinCircular _ tm _ z1 _ _ m1 _ => ord_rev_ok tm z1 /\ ord_rev_ok tm m1
  end.

Definition linearize (a : LinArc) (n : nat) : option (list LinVtx) :=
  match a with
  | LinCollinear p0 p2 z0 z2 m0 m2 =>
      Some [mkLinVtx p0 z0 m0; mkLinVtx p2 z2 m2]
  | LinCircular c tm z0 z1 z2 m0 m1 m2 =>
      if (n <? 2)%nat then None
      else Some (circ_lin_vtxs c tm z0 z1 z2 m0 m1 m2 n)
  end.

Definition lin_theta (c : CircularEgg) (n k : nat) : R :=
  circ_theta0 c + (INR k / INR n) * circ_sweep c.

(* -------------------------------------------------------------------------- *)
(* List arithmetic.                                                           *)
(* -------------------------------------------------------------------------- *)

Lemma seq_snoc : forall len start,
  seq start (S len) = seq start len ++ [(start + len)%nat].
Proof.
  intros len start.
  replace (S len) with (len + 1)%nat by lia.
  rewrite seq_app.
  replace (seq (start + len)%nat 1) with [(start + len)%nat] by reflexivity.
  reflexivity.
Qed.

Lemma seq_shift : forall len start,
  seq (S start) len = map S (seq start len).
Proof.
  induction len as [|len IH]; intros start; simpl; [|rewrite IH]; reflexivity.
Qed.

Lemma rev_map_complement_m : forall (A : Type) (f : nat -> A) (m : nat),
  rev (map (fun k => f (S m - k)%nat) (seq 1 m)) = map f (seq 1 m).
Proof.
  intros A f m. revert f.
  induction m as [|m IH]; intros f.
  - reflexivity.
  - rewrite (seq_snoc m 1) at 1.
    rewrite map_app, rev_app_distr. cbn [map rev app].
    assert (Ek : (S (S m) - (1 + m))%nat = 1%nat) by lia.
    rewrite Ek.
    assert (Hshift :
      map (fun k => f (S (S m) - k)%nat) (seq 1 m) =
      map (fun k => f (S (S m - k))%nat) (seq 1 m)).
    { apply map_ext_in. intros k Hk. apply in_seq in Hk. f_equal. lia. }
    rewrite Hshift.
    specialize (IH (fun j => f (S j))).
    rewrite IH.
    rewrite <- map_map. rewrite <- (seq_shift m 1).
    reflexivity.
Qed.

Lemma map_countdown_rev : forall (A : Type) (f : nat -> A) (n : nat),
  map (fun k => f (n - k)%nat) (seq 0 (S n)) = rev (map f (seq 0 (S n))).
Proof.
  intros A f n.
  set (g := fun k => f (n - k)%nat).
  apply nth_ext with (d := f 0%nat) (d' := f 0%nat).
  - rewrite length_rev, !length_map, !length_seq. reflexivity.
  - intros i Hi.
    rewrite length_map, length_seq in Hi.
    rewrite (@nth_indep A (map g (seq 0 (S n))) i (f 0%nat) (g 0%nat))
      by (rewrite length_map, length_seq; exact Hi).
    rewrite (map_nth g (seq 0 (S n)) 0%nat i).
    rewrite (@seq_nth (S n) 0 i 0%nat Hi).
    assert (Hi' : (i < length (map f (seq 0 (S n))))%nat)
      by (rewrite length_map, length_seq; exact Hi).
    rewrite (@rev_nth A (map f (seq 0 (S n))) (f 0%nat) i Hi').
    rewrite length_map, length_seq.
    rewrite (map_nth f (seq 0 (S n)) 0%nat (S n - S i)).
    rewrite (@seq_nth (S n) 0 (S n - S i) 0%nat) by lia.
    unfold g. reflexivity.
Qed.

Lemma seq_frame : forall n,
  (1 <= n)%nat ->
  seq 0 (S n) = 0%nat :: seq 1 (Nat.pred n) ++ [n].
Proof.
  intros n Hn.
  replace (S n) with (1 + n)%nat by lia.
  rewrite seq_app. simpl. f_equal.
  replace n with (S (Nat.pred n)) at 1 by lia.
  rewrite (seq_snoc (Nat.pred n) 1).
  repeat f_equal. lia.
Qed.

Lemma abs_of_nonneg : forall x, 0 <= x -> Rabs x = x.
Proof.
  intros x Hx. unfold Rabs. destruct (Rcase_abs x); lra.
Qed.

Lemma abs_of_neg : forall x, x < 0 -> Rabs x = - x.
Proof.
  intros x Hx. unfold Rabs. destruct (Rcase_abs x); lra.
Qed.

Lemma frac_complement : forall n k,
  (n <> 0)%nat -> (k <= n)%nat ->
  1 - INR k / INR n = INR (n - k) / INR n.
Proof.
  intros n k Hn Hk. rewrite minus_INR by lia. field.
  apply not_0_INR. exact Hn.
Qed.

Lemma ccw_sample_pos : forall c t,
  0 <= circ_sweep c ->
  circ_eval (ccw_egg c) t = circ_eval c t.
Proof.
  intros c t Hs. unfold circ_eval, ccw_egg.
  destruct (Rle_dec 0 (circ_sweep c)) as [_|Hno].
  - cbn [circ_o circ_r circ_theta0 circ_sweep].
    rewrite (abs_of_nonneg (circ_sweep c) Hs). reflexivity.
  - exfalso. lra.
Qed.

Lemma ccw_sample_neg_t : forall c t,
  circ_sweep c < 0 ->
  circ_eval (ccw_egg c) t = circ_eval c (1 - t).
Proof.
  intros c t Hs. unfold circ_eval, ccw_egg.
  destruct (Rle_dec 0 (circ_sweep c)) as [Hle|Hlt].
  - exfalso. lra.
  - cbn [circ_o circ_r circ_theta0 circ_sweep].
    rewrite (abs_of_neg (circ_sweep c) Hs).
    replace (circ_theta0 c + circ_sweep c + t * (- circ_sweep c))
      with (circ_theta0 c + (1 - t) * circ_sweep c) by ring.
    reflexivity.
Qed.

Lemma direct_pt_0 : forall c n,
  direct_pt c n 0 = circ_start c.
Proof.
  intros c n. unfold direct_pt. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma direct_pt_last : forall c n,
  (n <> 0)%nat -> direct_pt c n n = circ_end c.
Proof.
  intros c n Hn. unfold direct_pt.
  destruct (Nat.eqb_spec n 0) as [Hz|Hz]; [lia|].
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma direct_pt_eval : forall c n k,
  (n <> 0)%nat -> (k <= n)%nat ->
  direct_pt c n k = circ_eval c (INR k / INR n).
Proof.
  intros c n k Hn Hk. unfold direct_pt.
  destruct (Nat.eqb_spec k 0) as [Hk0|Hk0].
  - subst k. unfold circ_start.
    replace (INR 0 / INR n) with 0.
    + reflexivity.
    + rewrite INR_0. field. apply not_0_INR. exact Hn.
  - destruct (Nat.eqb_spec k n) as [Hkn|Hkn].
    + subst k. unfold circ_end.
      replace (INR n / INR n) with 1 by (field; apply not_0_INR; exact Hn).
      reflexivity.
    + reflexivity.
Qed.

Lemma lin_pts_eq_direct : forall c n,
  (2 <= n)%nat -> lin_pts c n = lin_pts_direct c n.
Proof.
  intros c n Hn.
  assert (Hn1 : (1 <= n)%nat) by lia.
  assert (Hn0 : (n <> 0)%nat) by lia.
  unfold lin_pts, lin_pts_direct, lin_interiors.
  rewrite (seq_frame n Hn1). rewrite map_cons, map_app. cbn [map].
  rewrite direct_pt_0, (direct_pt_last c n Hn0).
  f_equal. f_equal.
  destruct (Rle_dec 0 (circ_sweep c)) as [Hs|Hs].
  - unfold ccw_interiors. apply map_ext_in. intros k Hk.
    apply in_seq in Hk.
    rewrite (ccw_sample_pos c (INR k / INR n) Hs).
    rewrite <- (direct_pt_eval c n k) by lia. reflexivity.
  - unfold ccw_interiors.
    assert (Hsw : circ_sweep c < 0) by lra.
    assert (Hstep :
      map (fun k => circ_eval (ccw_egg c) (INR k / INR n)) (seq 1 (Nat.pred n)) =
      map (fun k => direct_pt c n (n - k)%nat) (seq 1 (Nat.pred n))).
    { apply map_ext_in. intros k Hk. apply in_seq in Hk.
      rewrite (ccw_sample_neg_t c (INR k / INR n) Hsw).
      rewrite (frac_complement n k) by lia.
      symmetry. apply direct_pt_eval; lia. }
    rewrite Hstep.
    assert (Hsub :
      map (fun k => direct_pt c n (n - k)%nat) (seq 1 (Nat.pred n)) =
      map (fun k => direct_pt c n (S (Nat.pred n) - k)%nat) (seq 1 (Nat.pred n))).
    { apply map_ext_in. intros k Hk. apply in_seq in Hk. f_equal. lia. }
    rewrite Hsub. apply rev_map_complement_m.
Qed.

Lemma lin_pts_length : forall c n,
  (1 <= n)%nat -> length (lin_pts c n) = S n.
Proof.
  intros c n Hn. unfold lin_pts, lin_interiors, ccw_interiors.
  destruct (Rle_dec 0 (circ_sweep c)).
  - cbn [length]. rewrite length_app, length_map, length_seq. cbn [length]. lia.
  - cbn [length]. rewrite length_app, length_rev, length_map, length_seq.
    cbn [length]. lia.
Qed.

Lemma lin_interiors_length : forall c n,
  (1 <= n)%nat -> length (lin_interiors c n) = Nat.pred n.
Proof.
  intros c n Hn. unfold lin_interiors, ccw_interiors.
  destruct (Rle_dec 0 (circ_sweep c));
    rewrite ?length_rev, length_map, length_seq; reflexivity.
Qed.

Lemma nth_lin_pts : forall c n k,
  (2 <= n)%nat -> (k <= n)%nat ->
  nth k (lin_pts c n) (circ_start c) = direct_pt c n k.
Proof.
  intros c n k Hn Hk.
  rewrite lin_pts_eq_direct by exact Hn.
  unfold lin_pts_direct.
  rewrite (@nth_indep Point (map (direct_pt c n) (seq 0 (S n))) k
             (circ_start c) (direct_pt c n k))
    by (rewrite length_map, length_seq; lia).
  rewrite (map_nth (direct_pt c n) (seq 0 (S n)) k k).
  rewrite (@seq_nth (S n) 0 k k) by lia.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* L1. Every vertex is the egg point at k/n, hence on the circle and sweep.  *)
(* -------------------------------------------------------------------------- *)

Lemma frac_in_unit : forall n k,
  (n <> 0)%nat -> (k <= n)%nat -> 0 <= INR k / INR n <= 1.
Proof.
  intros n k Hn Hk.
  assert (Hpos : 0 < INR n) by (apply lt_0_INR; lia).
  split.
  - unfold Rdiv. apply Rmult_le_pos.
    + apply pos_INR.
    + apply Rlt_le, Rinv_0_lt_compat. exact Hpos.
  - apply Rmult_le_reg_r with (r := INR n); [exact Hpos|].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l
      by (apply not_0_INR; exact Hn).
    apply le_INR. exact Hk.
Qed.

Lemma circ_eval_on_circle : forall c t,
  dist_sq (circ_o c) (circ_eval c t) = circ_r c * circ_r c.
Proof.
  intros c t. unfold circ_eval, dist_sq. cbn.
  pose proof (sin2_cos2 (circ_theta0 c + t * circ_sweep c)) as Hs.
  unfold Rsqr in Hs. nra.
Qed.

Theorem lin_vertex_on_arc : forall c n k,
  (2 <= n)%nat -> (k <= n)%nat ->
  let t := INR k / INR n in
  nth k (lin_pts c n) (circ_start c) = circ_eval c t /\
  dist_sq (circ_o c) (nth k (lin_pts c n) (circ_start c)) =
    circ_r c * circ_r c /\
  0 <= t <= 1 /\
  lin_angle c t = circ_theta0 c + t * circ_sweep c.
Proof.
  intros c n k Hn Hk t.
  assert (Hn0 : (n <> 0)%nat) by lia.
  rewrite nth_lin_pts by assumption.
  rewrite (direct_pt_eval c n k Hn0 Hk).
  unfold t.
  refine (conj _ (conj _ (conj _ _))).
  - reflexivity.
  - apply circ_eval_on_circle.
  - apply frac_in_unit; assumption.
  - unfold lin_angle. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* L2. Endpoints are the egg's endpoints. The control sample is interior     *)
(* only when its parameter is a grid node.                                   *)
(* -------------------------------------------------------------------------- *)

Lemma lin_endpoint_start : forall c n,
  (2 <= n)%nat -> nth 0 (lin_pts c n) (circ_start c) = circ_start c.
Proof.
  intros c n Hn. rewrite nth_lin_pts by lia. apply direct_pt_0.
Qed.

Lemma lin_endpoint_end : forall c n,
  (2 <= n)%nat -> nth n (lin_pts c n) (circ_start c) = circ_end c.
Proof.
  intros c n Hn. rewrite nth_lin_pts by lia. apply direct_pt_last. lia.
Qed.

Lemma eval_cos_sin_eq : forall c t s,
  circ_r c <> 0 ->
  circ_eval c t = circ_eval c s ->
  cos (lin_angle c t) = cos (lin_angle c s) /\
  sin (lin_angle c t) = sin (lin_angle c s).
Proof.
  intros c t s Hr Heq.
  apply (f_equal px) in Heq as Hx.
  apply (f_equal py) in Heq as Hy.
  unfold circ_eval, lin_angle in Hx, Hy. cbn in Hx, Hy.
  split.
  - apply (Rmult_eq_reg_l (circ_r c)); [|exact Hr].
    apply (Rplus_eq_reg_l (px (circ_o c))). exact Hx.
  - apply (Rmult_eq_reg_l (circ_r c)); [|exact Hr].
    apply (Rplus_eq_reg_l (py (circ_o c))). exact Hy.
Qed.

Lemma angles_eq_of_cossin : forall a b,
  - (2 * PI) < a - b < 2 * PI ->
  cos a = cos b -> sin a = sin b -> a = b.
Proof.
  intros a b Hb Hc Hs.
  assert (Hone : cos (a - b) = 1).
  { rewrite cos_minus, Hc, Hs.
    pose proof (sin2_cos2 a) as E. unfold Rsqr in E. nra. }
  assert (Hz : a - b = 0) by (apply cos_eq_1_two_pi; [lra|exact Hone]).
  lra.
Qed.

Lemma circ_eval_inj_strict : forall c t s,
  circ_r c <> 0 ->
  circ_sweep c <> 0 ->
  Rabs (circ_sweep c) <= 2 * PI ->
  0 <= t <= 1 -> 0 <= s <= 1 ->
  Rabs (t - s) < 1 ->
  circ_eval c t = circ_eval c s ->
  t = s.
Proof.
  intros c t s Hr Hsweep Hsw Ht Hs Hts Heq.
  destruct (eval_cos_sin_eq c t s Hr Heq) as [Hc Hsn].
  assert (Hdiff : Rabs ((t - s) * circ_sweep c) < 2 * PI).
  { rewrite Rabs_mult.
    pose proof PI_RGT_0 as HPI.
    assert (Hle : Rabs (t - s) * Rabs (circ_sweep c)
                   <= Rabs (t - s) * (2 * PI)).
    { apply Rmult_le_compat_l; [apply Rabs_pos|exact Hsw]. }
    assert (Hlt : Rabs (t - s) * (2 * PI) < 1 * (2 * PI)).
    { apply Rmult_lt_compat_r; [lra|exact Hts]. }
    lra. }
  assert (Hang : lin_angle c t = lin_angle c s).
  { apply angles_eq_of_cossin; [|exact Hc|exact Hsn].
    unfold lin_angle.
    replace (circ_theta0 c + t * circ_sweep c
             - (circ_theta0 c + s * circ_sweep c))
      with ((t - s) * circ_sweep c) by ring.
    destruct (Rabs_def2 _ _ Hdiff) as [Hhi Hlo]. split; assumption. }
  unfold lin_angle in Hang.
  assert (Hmul : (t - s) * circ_sweep c = 0) by lra.
  apply Rmult_integral in Hmul. destruct Hmul as [Hz|Hz]; lra.
Qed.

Theorem lin_control_interior_iff : forall c n k tm,
  (2 <= n)%nat ->
  (0 < k < n)%nat ->
  circ_r c <> 0 ->
  circ_sweep c <> 0 ->
  Rabs (circ_sweep c) <= 2 * PI ->
  0 < tm < 1 ->
  (circ_eval c tm = nth k (lin_pts c n) (circ_start c)
    <-> tm = INR k / INR n).
Proof.
  intros c n k tm Hn Hk Hr Hsweep Hsw Htm.
  assert (Hn0 : (n <> 0)%nat) by lia.
  rewrite nth_lin_pts by lia.
  rewrite (direct_pt_eval c n k Hn0) by lia.
  split.
  - intros Heq.
    assert (Hunit : 0 < INR k / INR n < 1).
    { split.
      - apply Rdiv_lt_0_compat; [apply lt_0_INR; lia|apply lt_0_INR; lia].
      - apply Rmult_lt_reg_r with (r := INR n).
        + apply lt_0_INR. lia.
        + unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l
            by (apply not_0_INR; lia).
          apply lt_INR. lia. }
    apply circ_eval_inj_strict with (c := c); try assumption; try lra.
    assert (Habs : -1 < tm - INR k / INR n < 1) by lra.
    apply Rabs_def1; lra.
  - intros ->. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* L3. Directed angles are monotone and cover the whole sweep, 2π included.  *)
(* -------------------------------------------------------------------------- *)

Lemma lin_theta_zero : forall c n,
  (n <> 0)%nat -> lin_theta c n 0 = circ_theta0 c.
Proof.
  intros c n Hn. unfold lin_theta. rewrite INR_0.
  replace (0 / INR n * circ_sweep c) with 0 by (field; apply not_0_INR; exact Hn).
  ring.
Qed.

Lemma lin_theta_last : forall c n,
  (n <> 0)%nat -> lin_theta c n n = circ_theta0 c + circ_sweep c.
Proof.
  intros c n Hn. unfold lin_theta.
  replace (INR n / INR n) with 1 by (field; apply not_0_INR; exact Hn).
  ring.
Qed.

Theorem lin_sweep_total : forall c n,
  (n <> 0)%nat -> lin_theta c n n - lin_theta c n 0 = circ_sweep c.
Proof.
  intros c n Hn. rewrite lin_theta_zero, lin_theta_last by exact Hn. ring.
Qed.

Theorem lin_sweep_abs_total : forall c n,
  (n <> 0)%nat ->
  Rabs (lin_theta c n n - lin_theta c n 0) = Rabs (circ_sweep c).
Proof.
  intros c n Hn. rewrite lin_sweep_total by exact Hn. reflexivity.
Qed.

Theorem lin_theta_mono_pos : forall c n i j,
  (n <> 0)%nat -> (i <= j)%nat -> (j <= n)%nat ->
  0 <= circ_sweep c ->
  lin_theta c n i <= lin_theta c n j.
Proof.
  intros c n i j Hn Hij Hjn Hs. unfold lin_theta.
  assert (Hfrac : INR i / INR n <= INR j / INR n).
  { apply Rmult_le_compat_r.
    - apply Rlt_le, Rinv_0_lt_compat, lt_0_INR. lia.
    - apply le_INR. exact Hij. }
  nra.
Qed.

Theorem lin_theta_mono_neg : forall c n i j,
  (n <> 0)%nat -> (i <= j)%nat -> (j <= n)%nat ->
  circ_sweep c <= 0 ->
  lin_theta c n j <= lin_theta c n i.
Proof.
  intros c n i j Hn Hij Hjn Hs. unfold lin_theta.
  assert (Hfrac : INR i / INR n <= INR j / INR n).
  { apply Rmult_le_compat_r.
    - apply Rlt_le, Rinv_0_lt_compat, lt_0_INR. lia.
    - apply le_INR. exact Hij. }
  nra.
Qed.

Theorem lin_full_circle_closed : forall c n,
  (2 <= n)%nat ->
  (circ_sweep c = 2 * PI \/ circ_sweep c = - (2 * PI)) ->
  nth 0 (lin_pts c n) (circ_start c) = nth n (lin_pts c n) (circ_start c).
Proof.
  intros c n Hn [H|H].
  -     rewrite lin_endpoint_start, lin_endpoint_end by exact Hn.
    unfold circ_start, circ_end, circ_eval. rewrite H.
    replace (circ_theta0 c + 1 * (2 * PI)) with (circ_theta0 c + 2 * PI) by ring.
    replace (circ_theta0 c + 0 * (2 * PI)) with (circ_theta0 c) by ring.
    assert (Hc : cos (circ_theta0 c + 2 * PI) = cos (circ_theta0 c)).
    { rewrite cos_plus, cos_2PI, sin_2PI. ring. }
    assert (Hs : sin (circ_theta0 c + 2 * PI) = sin (circ_theta0 c)).
    { rewrite sin_plus, cos_2PI, sin_2PI. ring. }
    rewrite Hc, Hs. reflexivity.
  -     rewrite lin_endpoint_start, lin_endpoint_end by exact Hn.
    unfold circ_start, circ_end, circ_eval. rewrite H.
    replace (circ_theta0 c + 1 * - (2 * PI))
      with (circ_theta0 c + - (2 * PI)) by ring.
    replace (circ_theta0 c + 0 * - (2 * PI)) with (circ_theta0 c) by ring.
    assert (Hc : cos (circ_theta0 c + - (2 * PI)) = cos (circ_theta0 c)).
    { rewrite cos_plus, cos_neg, sin_neg, cos_2PI, sin_2PI. ring. }
    assert (Hs : sin (circ_theta0 c + - (2 * PI)) = sin (circ_theta0 c)).
    { rewrite sin_plus, cos_neg, sin_neg, cos_2PI, sin_2PI. ring. }
    rewrite Hc, Hs. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* L5. Z/M are exact at the controls and piecewise linear in the parameter.  *)
(* None is NaN. A missing p1 ordinate or parameter interpolates p0 to p2.    *)
(* -------------------------------------------------------------------------- *)

Lemma lerp_0 : forall a b, lerp a b 0 = a.
Proof. intros. unfold lerp. ring. Qed.

Lemma lerp_1 : forall a b, lerp a b 1 = b.
Proof. intros. unfold lerp. ring. Qed.

Lemma lerp_rev : forall a b u, lerp a b u = lerp b a (1 - u).
Proof. intros. unfold lerp. ring. Qed.

Lemma zm_exact_p0 : forall z0 z1 z2 tm, zm_at z0 z1 z2 tm 0 = z0.
Proof.
  intros. unfold zm_at.
  destruct (Req_EM_T 0 0) as [_|H]; [reflexivity|exfalso; apply H; reflexivity].
Qed.

Lemma zm_exact_p2 : forall z0 z1 z2 tm, zm_at z0 z1 z2 tm 1 = z2.
Proof.
  intros. unfold zm_at.
  destruct (Req_EM_T 1 0) as [Ha|Hb]; [lra|].
  destruct (Req_EM_T 1 1) as [_|H1]; [reflexivity|exfalso; apply H1; reflexivity].
Qed.

Lemma zm_exact_p1 : forall z0 z2 b m,
  0 < m < 1 -> zm_at z0 (Some b) z2 (Some m) m = Some b.
Proof.
  intros. unfold zm_at.
  destruct (Req_EM_T m 0) as [Ha|Hb]; [lra|].
  destruct (Req_EM_T m 1) as [H1|H1]; [lra|].
  destruct (Req_EM_T m m) as [_|Hne]; [reflexivity|exfalso; apply Hne; reflexivity].
Qed.

Lemma zm_left_piece : forall a b z2 m t,
  0 < m < 1 -> 0 <= t <= m ->
  zm_at (Some a) (Some b) z2 (Some m) t = Some (lerp a b (t / m)).
Proof.
  intros a b z2 m t Hm Ht. unfold zm_at.
  destruct (Req_EM_T t 0) as [->|H0].
  - f_equal. replace (0 / m) with 0 by (field; lra). symmetry. apply lerp_0.
  - destruct (Req_EM_T t 1) as [->|H1]; [lra|].
    destruct (Req_EM_T t m) as [->|Htm].
    + f_equal. replace (m / m) with 1 by (field; lra). symmetry. apply lerp_1.
    + destruct (Rle_dec t m) as [_|Hlt]; [|lra]. reflexivity.
Qed.

Lemma zm_right_piece : forall z0 b c m t,
  0 < m < 1 -> m <= t <= 1 ->
  zm_at z0 (Some b) (Some c) (Some m) t =
    Some (lerp b c ((t - m) / (1 - m))).
Proof.
  intros z0 b c m t Hm Ht. unfold zm_at.
  destruct (Req_EM_T t 0) as [->|H0]; [lra|].
  destruct (Req_EM_T t 1) as [->|H1].
  - f_equal. replace ((1 - m) / (1 - m)) with 1 by (field; lra). symmetry. apply lerp_1.
  - destruct (Req_EM_T t m) as [->|Htm].
    + f_equal. replace ((m - m) / (1 - m)) with 0 by (field; lra). symmetry. apply lerp_0.
    + destruct (Rle_dec t m) as [Hle|Hlt]; [lra|]. reflexivity.
Qed.

Lemma zm_left_lin : forall a b z2 m t,
  0 < m < 1 -> 0 <= t <= m ->
  zm_at (Some a) (Some b) z2 (Some m) t = Some (a + (t / m) * (b - a)).
Proof.
  intros. rewrite zm_left_piece by assumption. f_equal. unfold lerp. field. lra.
Qed.

Lemma zm_right_lin : forall z0 b c m t,
  0 < m < 1 -> m <= t <= 1 ->
  zm_at z0 (Some b) (Some c) (Some m) t =
    Some (b + ((t - m) / (1 - m)) * (c - b)).
Proof.
  intros. rewrite zm_right_piece by assumption. f_equal. unfold lerp. field. lra.
Qed.

Lemma zm_fallback : forall a c tm t,
  0 <= t <= 1 ->
  zm_at (Some a) None (Some c) tm t = Some (lerp a c t).
Proof.
  intros a c tm t Ht. unfold zm_at.
  destruct (Req_EM_T t 0) as [->|H0].
  - f_equal. symmetry. apply lerp_0.
  - destruct (Req_EM_T t 1) as [->|H1].
    + f_equal. symmetry. apply lerp_1.
    + reflexivity.
Qed.

Lemma zm_fallback_lin : forall a c tm t,
  0 <= t <= 1 ->
  zm_at (Some a) None (Some c) tm t = Some (a + t * (c - a)).
Proof.
  intros. rewrite zm_fallback by assumption. f_equal. unfold lerp. ring.
Qed.

Lemma zm_no_tm : forall a b c t,
  0 <= t <= 1 ->
  zm_at (Some a) (Some b) (Some c) None t = Some (lerp a c t).
Proof.
  intros a b c t Ht. unfold zm_at.
  destruct (Req_EM_T t 0) as [->|H0].
  - f_equal. symmetry. apply lerp_0.
  - destruct (Req_EM_T t 1) as [->|H1].
    + f_equal. symmetry. apply lerp_1.
    + reflexivity.
Qed.

Lemma zm_left_none : forall b z2 m t,
  0 < m < 1 -> 0 <= t < m ->
  zm_at None (Some b) z2 (Some m) t = None.
Proof.
  intros b z2 m t Hm Ht. unfold zm_at.
  destruct (Req_EM_T t 0) as [->|H0].
  - reflexivity.
  - destruct (Req_EM_T t 1); [lra|].
    destruct (Req_EM_T t m); [lra|].
    destruct (Rle_dec t m); [reflexivity|lra].
Qed.

Lemma zm_right_none : forall z0 b m t,
  0 < m < 1 -> m < t <= 1 ->
  zm_at z0 (Some b) None (Some m) t = None.
Proof.
  intros z0 b m t Hm Ht. unfold zm_at.
  destruct (Req_EM_T t 0); [lra|].
  destruct (Req_EM_T t 1) as [->|H1].
  - reflexivity.
  - destruct (Req_EM_T t m); [lra|].
    destruct (Rle_dec t m); [lra|reflexivity].
Qed.

Lemma zm_missing_tm_as_nan : forall z0 b z2 tm t,
  zm_at z0 (Some b) z2 None t = zm_at z0 None z2 tm t.
Proof.
  intros z0 b z2 tm t. unfold zm_at.
  destruct (Req_EM_T t 0) as [_|H0]; [reflexivity|].
  destruct (Req_EM_T t 1) as [_|H1]; [reflexivity|].
  reflexivity.
Qed.

Lemma zm_nan_rev : forall z0 z2 tm1 tm2 t,
  0 <= t <= 1 ->
  zm_at z2 None z0 tm1 t = zm_at z0 None z2 tm2 (1 - t).
Proof.
  intros z0 z2 tm1 tm2 t Ht.
  destruct z2 as [c|], z0 as [a|].
  - rewrite (zm_fallback c a tm1 t Ht).
    assert (Hs : 0 <= 1 - t <= 1) by lra.
    rewrite (zm_fallback a c tm2 (1 - t) Hs).
    f_equal. apply lerp_rev.
  - unfold zm_at.
    destruct (Req_EM_T t 0) as [->|H0].
    + replace (1 - 0) with 1 by ring.
      destruct (Req_EM_T 1 0) as [Ha|Hb]; [lra|].
      destruct (Req_EM_T 1 1) as [_|H1]; [reflexivity|exfalso; apply H1; reflexivity].
    + destruct (Req_EM_T t 1) as [->|H1].
      * replace (1 - 1) with 0 by ring.
        destruct (Req_EM_T 0 0) as [_|H]; [reflexivity|exfalso; apply H; reflexivity].
      * assert (0 < 1 - t < 1) by lra.
        destruct (Req_EM_T (1 - t) 0) as [Hs0|Hs0]; [lra|].
        destruct (Req_EM_T (1 - t) 1) as [Hs1|Hs1]; [lra|].
        reflexivity.
  - unfold zm_at.
    destruct (Req_EM_T t 0) as [->|H0].
    + replace (1 - 0) with 1 by ring.
      destruct (Req_EM_T 1 0) as [Ha|Hb]; [lra|].
      destruct (Req_EM_T 1 1) as [_|H1]; [reflexivity|exfalso; apply H1; reflexivity].
    + destruct (Req_EM_T t 1) as [->|H1].
      * replace (1 - 1) with 0 by ring.
        destruct (Req_EM_T 0 0) as [_|H]; [reflexivity|exfalso; apply H; reflexivity].
      * assert (0 < 1 - t < 1) by lra.
        destruct (Req_EM_T (1 - t) 0) as [Hs0|Hs0]; [lra|].
        destruct (Req_EM_T (1 - t) 1) as [Hs1|Hs1]; [lra|].
        reflexivity.
  - unfold zm_at.
    destruct (Req_EM_T t 0) as [->|H0].
    + replace (1 - 0) with 1 by ring.
      destruct (Req_EM_T 1 0) as [Ha|Hb]; [lra|].
      destruct (Req_EM_T 1 1) as [_|H1]; [reflexivity|exfalso; apply H1; reflexivity].
    + destruct (Req_EM_T t 1) as [->|H1].
      * replace (1 - 1) with 0 by ring.
        destruct (Req_EM_T 0 0) as [_|H]; [reflexivity|exfalso; apply H; reflexivity].
      * assert (0 < 1 - t < 1) by lra.
        destruct (Req_EM_T (1 - t) 0) as [Hs0|Hs0]; [lra|].
        destruct (Req_EM_T (1 - t) 1) as [Hs1|Hs1]; [lra|].
        reflexivity.
Qed.

Lemma zm_split_rev : forall z0 z2 b m t,
  0 < m < 1 -> 0 <= t <= 1 ->
  zm_at z2 (Some b) z0 (Some (1 - m)) t =
  zm_at z0 (Some b) z2 (Some m) (1 - t).
Proof.
  intros z0 z2 b m t Hm Ht.
  destruct (Rtotal_order t (1 - m)) as [Hlt|[Heq|Hgt]].
  - destruct z2 as [c|].
    + rewrite (zm_left_piece c b z0 (1 - m) t) by lra.
      rewrite (zm_right_piece z0 b c m (1 - t)) by lra.
      f_equal. rewrite (lerp_rev c b (t / (1 - m))). f_equal. field. lra.
    + rewrite (zm_left_none b z0 (1 - m) t) by lra.
      rewrite (zm_right_none z0 b m (1 - t)) by lra.
      reflexivity.
  - subst t.
    rewrite (zm_exact_p1 z2 z0 b (1 - m)) by lra.
    replace (1 - (1 - m)) with m by ring.
    rewrite (zm_exact_p1 z0 z2 b m) by lra.
    reflexivity.
  - destruct z0 as [a|].
    + rewrite (zm_right_piece z2 b a (1 - m) t) by lra.
      rewrite (zm_left_piece a b z2 m (1 - t)) by lra.
      f_equal. rewrite (lerp_rev b a ((t - (1 - m)) / (1 - (1 - m)))).
      f_equal. field. lra.
    + rewrite (zm_right_none z2 b (1 - m) t) by lra.
      rewrite (zm_left_none b z2 m (1 - t)) by lra.
      reflexivity.
Qed.

Lemma zm_at_rev : forall z0 z1 z2 tm t,
  0 <= t <= 1 ->
  ord_rev_ok tm z1 ->
  zm_at z2 z1 z0 (shift_tm tm) t = zm_at z0 z1 z2 tm (1 - t).
Proof.
  intros z0 z1 z2 tm t Ht Hok.
  destruct z1 as [b|].
  - destruct tm as [m|].
    + cbn in Hok. unfold shift_tm. cbn.
      apply zm_split_rev; assumption.
    + unfold shift_tm. cbn.
      rewrite (zm_missing_tm_as_nan z2 b z0 None t).
      rewrite (zm_missing_tm_as_nan z0 b z2 None (1 - t)).
      apply zm_nan_rev. exact Ht.
  - apply zm_nan_rev. exact Ht.
Qed.

(* -------------------------------------------------------------------------- *)
(* L6. Reversing the arc reverses the vertex list.                           *)
(* -------------------------------------------------------------------------- *)

Lemma vtx_t_frac : forall n k,
  (n <> 0)%nat -> (k < n)%nat -> vtx_t n k = INR k / INR n.
Proof.
  intros n k Hn Hk. unfold vtx_t.
  destruct (Nat.eqb_spec k n) as [E|E]; [lia|reflexivity].
Qed.

Lemma vtx_t_last : forall n, vtx_t n n = 1.
Proof. intros n. unfold vtx_t. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma vtx_t_bound : forall n k,
  (n <> 0)%nat -> (k <= n)%nat -> 0 <= vtx_t n k <= 1.
Proof.
  intros n k Hn Hk.
  destruct (Nat.eq_dec k n) as [->|Hne].
  - rewrite vtx_t_last. lra.
  - rewrite vtx_t_frac by lia. apply frac_in_unit; lia.
Qed.

Lemma vtx_t_compl : forall n k,
  (n <> 0)%nat -> (k <= n)%nat ->
  vtx_t n (n - k)%nat = 1 - vtx_t n k.
Proof.
  intros n k Hn Hk.
  destruct (Nat.eq_dec k n) as [->|Hkn].
  - rewrite Nat.sub_diag. rewrite vtx_t_last.
    rewrite vtx_t_frac by lia. rewrite INR_0.
    replace (0 / INR n) with 0 by (field; apply not_0_INR; exact Hn). ring.
  - destruct (Nat.eq_dec k 0%nat) as [->|Hk0].
    + rewrite Nat.sub_0_r. rewrite vtx_t_last.
      rewrite vtx_t_frac by lia. rewrite INR_0.
      replace (0 / INR n) with 0 by (field; apply not_0_INR; exact Hn). ring.
    + rewrite (vtx_t_frac n k) by lia.
      rewrite (vtx_t_frac n (n - k)) by lia.
      symmetry. apply frac_complement; lia.
Qed.

Lemma zm_index_rev : forall z0 z1 z2 tm n k,
  (2 <= n)%nat -> (k <= n)%nat ->
  ord_rev_ok tm z1 ->
  zm_at z2 z1 z0 (shift_tm tm) (vtx_t n k) =
  zm_at z0 z1 z2 tm (vtx_t n (n - k)%nat).
Proof.
  intros z0 z1 z2 tm n k Hn Hk Hok.
  rewrite (vtx_t_compl n k) by lia.
  apply zm_at_rev; [|exact Hok].
  apply vtx_t_bound; lia.
Qed.

Lemma rev_egg_eval : forall c t,
  circ_eval (rev_egg c) t = circ_eval c (1 - t).
Proof.
  intros c t. unfold circ_eval, rev_egg. cbn.
  replace (circ_theta0 c + circ_sweep c + t * - circ_sweep c)
    with (circ_theta0 c + (1 - t) * circ_sweep c) by ring.
  reflexivity.
Qed.

Lemma direct_pt_rev : forall c n k,
  (n <> 0)%nat -> (k <= n)%nat ->
  direct_pt (rev_egg c) n k = direct_pt c n (n - k)%nat.
Proof.
  intros c n k Hn Hk.
  rewrite (direct_pt_eval (rev_egg c) n k) by lia.
  rewrite (direct_pt_eval c n (n - k)%nat) by lia.
  rewrite rev_egg_eval. rewrite frac_complement by lia. reflexivity.
Qed.

Lemma lin_pts_rev : forall c n,
  (2 <= n)%nat -> lin_pts (rev_egg c) n = rev (lin_pts c n).
Proof.
  intros c n Hn.
  rewrite (lin_pts_eq_direct (rev_egg c) n) by exact Hn.
  rewrite (lin_pts_eq_direct c n) by exact Hn.
  unfold lin_pts_direct.
  rewrite <- (map_countdown_rev Point (direct_pt c n) n).
  apply map_ext_in. intros k Hk. apply in_seq in Hk.
  apply direct_pt_rev; lia.
Qed.

Lemma nth_rev_lin : forall c n k,
  (2 <= n)%nat -> (k <= n)%nat ->
  nth k (rev (lin_pts c n)) (circ_start c) =
  nth (n - k) (lin_pts c n) (circ_start c).
Proof.
  intros c n k Hn Hk.
  assert (Hi : (k < length (lin_pts c n))%nat)
    by (rewrite lin_pts_length by lia; lia).
  rewrite (@rev_nth Point (lin_pts c n) (circ_start c) k Hi).
  rewrite lin_pts_length by lia. reflexivity.
Qed.

Lemma circ_vtx_rev : forall c tm z0 z1 z2 m0 m1 m2 n k,
  (2 <= n)%nat -> (k <= n)%nat ->
  ord_rev_ok tm z1 -> ord_rev_ok tm m1 ->
  circ_vtx (rev_egg c) (shift_tm tm) z2 z1 z0 m2 m1 m0 n k =
  circ_vtx c tm z0 z1 z2 m0 m1 m2 n (n - k)%nat.
Proof.
  intros c tm z0 z1 z2 m0 m1 m2 n k Hn Hk Hz Hm.
  unfold circ_vtx.
  rewrite (nth_lin_pts (rev_egg c) n k) by lia.
  rewrite (direct_pt_rev c n k) by lia.
  rewrite <- (nth_lin_pts c n (n - k)%nat) by lia.
  rewrite (zm_index_rev z0 z1 z2 tm n k Hn Hk Hz).
  rewrite (zm_index_rev m0 m1 m2 tm n k Hn Hk Hm).
  reflexivity.
Qed.

Lemma circ_lin_vtxs_rev : forall c tm z0 z1 z2 m0 m1 m2 n,
  (2 <= n)%nat ->
  ord_rev_ok tm z1 -> ord_rev_ok tm m1 ->
  circ_lin_vtxs (rev_egg c) (shift_tm tm) z2 z1 z0 m2 m1 m0 n =
  rev (circ_lin_vtxs c tm z0 z1 z2 m0 m1 m2 n).
Proof.
  intros c tm z0 z1 z2 m0 m1 m2 n Hn Hz Hm.
  unfold circ_lin_vtxs.
  rewrite <- (map_countdown_rev LinVtx
    (circ_vtx c tm z0 z1 z2 m0 m1 m2 n) n).
  apply map_ext_in. intros k Hk. apply in_seq in Hk.
  apply circ_vtx_rev; try assumption; lia.
Qed.

Theorem lin_reverse_commutes : forall a n,
  lin_rev_ok a ->
  linearize (lin_reverse a) n = option_map (@rev LinVtx) (linearize a n).
Proof.
  intros a n Hok.
  destruct a as [p0 p2 z0 z2 m0 m2|c tm z0 z1 z2 m0 m1 m2].
  - simpl. reflexivity.
  - simpl in Hok. destruct Hok as [Hz Hm].
    unfold linearize, lin_reverse.
    destruct (Nat.ltb_spec n 2) as [Hlt|Hge].
    + destruct (Nat.ltb_spec n 2) as [Hlt2|Hge2]; [reflexivity|lia].
    + destruct (Nat.ltb_spec n 2) as [Hlt2|Hge2]; [lia|].
      cbn [option_map]. f_equal.
      apply circ_lin_vtxs_rev; [lia|exact Hz|exact Hm].
Qed.

(* -------------------------------------------------------------------------- *)
(* L7. The step count is at least 2. A collinear arc is exactly the segment. *)
(* -------------------------------------------------------------------------- *)

Theorem subdiv_n_ge_2 : forall step sweep n,
  subdiv_ok step sweep n -> (2 <= n)%nat.
Proof. intros step sweep n [Hn _]. exact Hn. Qed.

Theorem lin_collinear_segment : forall p0 p2 z0 z2 m0 m2 n,
  linearize (LinCollinear p0 p2 z0 z2 m0 m2) n =
  Some [mkLinVtx p0 z0 m0; mkLinVtx p2 z2 m2].
Proof. intros. reflexivity. Qed.

Theorem lin_circ_short_none : forall c tm z0 z1 z2 m0 m1 m2 n,
  (n < 2)%nat ->
  linearize (LinCircular c tm z0 z1 z2 m0 m1 m2) n = None.
Proof.
  intros. unfold linearize.
  destruct (Nat.ltb_spec n 2) as [Hlt|Hge]; [reflexivity|lia].
Qed.

Theorem lin_circ_some : forall c tm z0 z1 z2 m0 m1 m2 n,
  (2 <= n)%nat ->
  linearize (LinCircular c tm z0 z1 z2 m0 m1 m2) n =
  Some (circ_lin_vtxs c tm z0 z1 z2 m0 m1 m2 n).
Proof.
  intros. unfold linearize.
  destruct (Nat.ltb_spec n 2) as [Hlt|Hge]; [lia|reflexivity].
Qed.

(* Assumptions: each block stays inside the 3-axiom allowlist. *)
Print Assumptions seq_snoc.
Print Assumptions seq_shift.
Print Assumptions rev_map_complement_m.
Print Assumptions map_countdown_rev.
Print Assumptions seq_frame.
Print Assumptions abs_of_nonneg.
Print Assumptions abs_of_neg.
Print Assumptions frac_complement.
Print Assumptions ccw_sample_pos.
Print Assumptions ccw_sample_neg_t.
Print Assumptions direct_pt_0.
Print Assumptions direct_pt_last.
Print Assumptions direct_pt_eval.
Print Assumptions lin_pts_eq_direct.
Print Assumptions lin_pts_length.
Print Assumptions lin_interiors_length.
Print Assumptions nth_lin_pts.
Print Assumptions frac_in_unit.
Print Assumptions circ_eval_on_circle.
Print Assumptions lin_vertex_on_arc.
Print Assumptions lin_endpoint_start.
Print Assumptions lin_endpoint_end.
Print Assumptions eval_cos_sin_eq.
Print Assumptions angles_eq_of_cossin.
Print Assumptions circ_eval_inj_strict.
Print Assumptions lin_control_interior_iff.
Print Assumptions lin_theta_zero.
Print Assumptions lin_theta_last.
Print Assumptions lin_sweep_total.
Print Assumptions lin_sweep_abs_total.
Print Assumptions lin_theta_mono_pos.
Print Assumptions lin_theta_mono_neg.
Print Assumptions lin_full_circle_closed.
Print Assumptions lerp_0.
Print Assumptions lerp_1.
Print Assumptions lerp_rev.
Print Assumptions zm_exact_p0.
Print Assumptions zm_exact_p2.
Print Assumptions zm_exact_p1.
Print Assumptions zm_left_piece.
Print Assumptions zm_right_piece.
Print Assumptions zm_left_lin.
Print Assumptions zm_right_lin.
Print Assumptions zm_fallback.
Print Assumptions zm_fallback_lin.
Print Assumptions zm_no_tm.
Print Assumptions zm_left_none.
Print Assumptions zm_right_none.
Print Assumptions zm_missing_tm_as_nan.
Print Assumptions zm_nan_rev.
Print Assumptions zm_split_rev.
Print Assumptions zm_at_rev.
Print Assumptions vtx_t_frac.
Print Assumptions vtx_t_last.
Print Assumptions vtx_t_bound.
Print Assumptions vtx_t_compl.
Print Assumptions zm_index_rev.
Print Assumptions rev_egg_eval.
Print Assumptions direct_pt_rev.
Print Assumptions lin_pts_rev.
Print Assumptions nth_rev_lin.
Print Assumptions circ_vtx_rev.
Print Assumptions circ_lin_vtxs_rev.
Print Assumptions lin_reverse_commutes.
Print Assumptions subdiv_n_ge_2.
Print Assumptions lin_collinear_segment.
Print Assumptions lin_circ_short_none.
Print Assumptions lin_circ_some.
