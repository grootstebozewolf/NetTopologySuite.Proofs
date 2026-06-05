(* ============================================================================
   NetTopologySuite.Proofs.Flocq.NodingSeparation_b64
   ----------------------------------------------------------------------------
   A WEAKER-but-TRUE noding-preservation claim, with the recently-closed
   buffer offset pipeline as its bridgehead.

   Context.  `HobbyCounterexample_b64.v` refuted `hobby_lemma_4_3_no_proper`:
   snap-rounding two ARBITRARY segments can manufacture a proper
   intersection (parallel collapse onto one grid line).  The universal
   per-pair preservation is therefore false.

   This file lands the honest replacement: snap-rounding preserves
   "no proper intersection" for pairs that are SEPARATED -- whose
   projections onto some axis are more than one grid unit apart.  Snapping
   moves each coordinate by at most 1/2 (the round-to-nearest tolerance),
   so a gap greater than 1 cannot close.  The collinear-collapse witness is
   excluded precisely because its segments were NOT separated (the
   y-coordinates 0.7 and 1.3 are only 0.6 < 1 apart).

   The arrangement lift `fully_intersected_snap_of_nodable` discharges the
   noding hypothesis `fully_intersected (snap_round_segments segs)` whenever
   every distinct pair of input segments either shares an endpoint or is
   separated -- the true, usable form of the noding step that
   `overlay_ng_correct_conditional` / `buffer_correct_conditional` consume.

   Buffer bridgehead.  The recently-closed `theories/BufferOffset.v` proves
   each offset endpoint is the source translated by `d * unit_normal`, with
   `vmag_sq_unit_perp` giving the normal unit length.  Hence each coordinate
   of an offset segment is within `|d|` of its source.  So source edges
   separated by more than `1 + 2|d|` produce offset segments separated by
   more than `1` (`offset_seg_x_left_of`), and the buffer's `offset_curve`
   nodes to a fully-intersected arrangement under a checkable separation
   precondition (`buffer_offset_nodable`).

   ----------------------------------------------------------------------------
   Audit footprint.  References `snap_round` (Flocq-pinned), so it inherits
   the `Classical_Prop.classic` lineage of HobbyTheorem_b64.v /
   HotPixel_b64.v; listed in docs/audit-exceptions.txt.  No `Admitted` /
   `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lra.
From Stdlib Require Import List.

From Flocq Require Import Core.
From Flocq Require Import IEEE754.Binary.
From Flocq Require Import IEEE754.BinarySingleNaN.

From NTS.Proofs        Require Import Real Vec Distance Direction.
From NTS.Proofs        Require Import HotPixel.
From NTS.Proofs        Require Import Overlay OverlayGraph.
From NTS.Proofs        Require Import BufferOffset BufferCorrectness.
From NTS.Proofs.Flocq  Require Import HotPixel_b64.
From NTS.Proofs.Flocq  Require Import HobbyTheorem_b64.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The snap-rounding tolerance bound.                                     *)
(* -------------------------------------------------------------------------- *)

(* The standalone "tolerance-square half-width" bound flagged in
   docs/hobby-theorem-proof-structure.md §7: round-to-nearest on the unit
   grid moves a coordinate by at most 1/2. *)
Lemma snap_round_coord_tolerance :
  forall x : R, Rabs (snap_round_coord x 1 - x) <= /2.
Proof.
  intros x. unfold snap_round_coord.
  unfold Rdiv. rewrite Rinv_1, !Rmult_1_r.
  rewrite round_FIX_IZR. unfold round_mode.
  rewrite Rabs_minus_sym. apply Znearest_half.
Qed.

Lemma snap_round_x_tol :
  forall P : Point, Rabs (px (snap_round P 1) - px P) <= /2.
Proof. intros P. unfold snap_round; simpl. apply snap_round_coord_tolerance. Qed.

Lemma snap_round_y_tol :
  forall P : Point, Rabs (py (snap_round P 1) - py P) <= /2.
Proof. intros P. unfold snap_round; simpl. apply snap_round_coord_tolerance. Qed.

Lemma snap_x_bounds :
  forall P : Point, px P - /2 <= px (snap_round P 1) <= px P + /2.
Proof.
  intros P. pose proof (snap_round_x_tol P) as H.
  assert (Hu : px (snap_round P 1) - px P <= /2)
    by (eapply Rle_trans; [apply Rle_abs | exact H]).
  assert (Hl : px P - px (snap_round P 1) <= /2)
    by (eapply Rle_trans; [apply Rle_abs |]; rewrite Rabs_minus_sym; exact H).
  lra.
Qed.

Lemma snap_y_bounds :
  forall P : Point, py P - /2 <= py (snap_round P 1) <= py P + /2.
Proof.
  intros P. pose proof (snap_round_y_tol P) as H.
  assert (Hu : py (snap_round P 1) - py P <= /2)
    by (eapply Rle_trans; [apply Rle_abs | exact H]).
  assert (Hl : py P - py (snap_round P 1) <= /2)
    by (eapply Rle_trans; [apply Rle_abs |]; rewrite Rabs_minus_sym; exact H).
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Axis separation and the no-proper-intersection core.                   *)
(* -------------------------------------------------------------------------- *)

(* `s1` lies left of `s2` in x with a unit-plus gap: every x-coordinate of
   s1 is <= a, every x-coordinate of s2 is >= b, and b - a > 1. *)
Definition x_left_of (s1 s2 : Point * Point) : Prop :=
  exists a b : R, b - a > 1 /\
    px (fst s1) <= a /\ px (snd s1) <= a /\
    px (fst s2) >= b /\ px (snd s2) >= b.

Definition y_below_of (s1 s2 : Point * Point) : Prop :=
  exists a b : R, b - a > 1 /\
    py (fst s1) <= a /\ py (snd s1) <= a /\
    py (fst s2) >= b /\ py (snd s2) >= b.

(* Symmetric separation: apart in some axis, in either order. *)
Definition separated (s1 s2 : Point * Point) : Prop :=
  x_left_of s1 s2 \/ x_left_of s2 s1 \/
  y_below_of s1 s2 \/ y_below_of s2 s1.

(* `segments_intersect_properly` is symmetric in the two segments. *)
Lemma sip_comm :
  forall A B C D : Point,
    segments_intersect_properly A B C D ->
    segments_intersect_properly C D A B.
Proof.
  intros A B C D [t [s [Ht [Hs [Hx Hy]]]]].
  exists s, t. repeat split; lra.
Qed.

(* Core: an x-gap greater than 1 survives snapping (each coordinate moves by
   <= 1/2), so the snapped segments stay in disjoint vertical strips and
   cannot cross properly. *)
Lemma x_left_of_snap_no_proper :
  forall s1 s2 : Point * Point,
    x_left_of s1 s2 ->
    ~ segments_intersect_properly
        (snap_round (fst s1) 1) (snap_round (snd s1) 1)
        (snap_round (fst s2) 1) (snap_round (snd s2) 1).
Proof.
  intros s1 s2 [a [b [Hgap [HA [HB [HC HD]]]]]].
  intros [t [s [Ht [Hs [Hpx _]]]]].
  pose proof (snap_x_bounds (fst s1)) as B1.
  pose proof (snap_x_bounds (snd s1)) as B2.
  pose proof (snap_x_bounds (fst s2)) as B3.
  pose proof (snap_x_bounds (snd s2)) as B4.
  assert (HA' : px (snap_round (fst s1) 1) <= a + /2) by lra.
  assert (HB' : px (snap_round (snd s1) 1) <= a + /2) by lra.
  assert (HC' : px (snap_round (fst s2) 1) >= b - /2) by lra.
  assert (HD' : px (snap_round (snd s2) 1) >= b - /2) by lra.
  assert (HL : (1 - t) * px (snap_round (fst s1) 1)
               + t * px (snap_round (snd s1) 1) <= a + /2) by nra.
  assert (HR : (1 - s) * px (snap_round (fst s2) 1)
               + s * px (snap_round (snd s2) 1) >= b - /2) by nra.
  rewrite Hpx in HL. lra.
Qed.

Lemma y_below_of_snap_no_proper :
  forall s1 s2 : Point * Point,
    y_below_of s1 s2 ->
    ~ segments_intersect_properly
        (snap_round (fst s1) 1) (snap_round (snd s1) 1)
        (snap_round (fst s2) 1) (snap_round (snd s2) 1).
Proof.
  intros s1 s2 [a [b [Hgap [HA [HB [HC HD]]]]]].
  intros [t [s [Ht [Hs [_ Hpy]]]]].
  pose proof (snap_y_bounds (fst s1)) as B1.
  pose proof (snap_y_bounds (snd s1)) as B2.
  pose proof (snap_y_bounds (fst s2)) as B3.
  pose proof (snap_y_bounds (snd s2)) as B4.
  assert (HA' : py (snap_round (fst s1) 1) <= a + /2) by lra.
  assert (HB' : py (snap_round (snd s1) 1) <= a + /2) by lra.
  assert (HC' : py (snap_round (fst s2) 1) >= b - /2) by lra.
  assert (HD' : py (snap_round (snd s2) 1) >= b - /2) by lra.
  assert (HL : (1 - t) * py (snap_round (fst s1) 1)
               + t * py (snap_round (snd s1) 1) <= a + /2) by nra.
  assert (HR : (1 - s) * py (snap_round (fst s2) 1)
               + s * py (snap_round (snd s2) 1) >= b - /2) by nra.
  rewrite Hpy in HL. lra.
Qed.

(* The symmetric statement: separated pairs do not cross properly after
   snapping. *)
Lemma separated_snap_no_proper :
  forall s1 s2 : Point * Point,
    separated s1 s2 ->
    ~ segments_intersect_properly
        (snap_round (fst s1) 1) (snap_round (snd s1) 1)
        (snap_round (fst s2) 1) (snap_round (snd s2) 1).
Proof.
  intros s1 s2 [H | [H | [H | H]]].
  - apply x_left_of_snap_no_proper; exact H.
  - intro Hp. apply (x_left_of_snap_no_proper s2 s1 H), sip_comm, Hp.
  - apply y_below_of_snap_no_proper; exact H.
  - intro Hp. apply (y_below_of_snap_no_proper s2 s1 H), sip_comm, Hp.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The arrangement lift -- the usable noding discharge.                   *)
(* -------------------------------------------------------------------------- *)

(* Every distinct pair in the arrangement either shares an endpoint or is
   separated.  This is the true precondition under which snap-rounding
   preserves the fully-intersected invariant (replacing the false universal
   `hobby_lemma_4_3_no_proper`). *)
Definition pairwise_nodable (segs : list (Point * Point)) : Prop :=
  forall s1 s2 : Point * Point,
    In s1 segs -> In s2 segs -> s1 <> s2 ->
    (fst s1 = fst s2 \/ fst s1 = snd s2 \/ snd s1 = fst s2 \/ snd s1 = snd s2)
    \/ separated s1 s2.

Theorem fully_intersected_snap_of_nodable :
  forall segs : list (Point * Point),
    pairwise_nodable segs ->
    fully_intersected (snap_round_segments segs).
Proof.
  intros segs Hpn sigma1 sigma2 Hin1 Hin2 Hne.
  unfold snap_round_segments in Hin1, Hin2.
  apply in_map_iff in Hin1. destruct Hin1 as [s1 [Heq1 Hs1]].
  apply in_map_iff in Hin2. destruct Hin2 as [s2 [Heq2 Hs2]].
  assert (Hs12 : s1 <> s2).
  { intro Hc. apply Hne. subst s2. rewrite <- Heq1, <- Heq2. reflexivity. }
  destruct (Hpn s1 s2 Hs1 Hs2 Hs12) as [Hshare | Hsep].
  - subst sigma1 sigma2. cbn.
    right. apply hobby_lemma_4_3_shared_endpoint. exact Hshare.
  - subst sigma1 sigma2. cbn.
    left. apply (separated_snap_no_proper s1 s2 Hsep).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Buffer bridgehead: source separation -> offset separation.            *)
(* -------------------------------------------------------------------------- *)

(* The buffer's offset normal is a unit (or, degenerately, zero) vector, so
   its x-component has magnitude at most 1.  Uses the Qed-closed
   `BufferOffset.vmag_sq_unit_perp`. *)
Lemma offset_normal_vx_sq_le_1 :
  forall A B : Point,
    vx (offset_normal A B) * vx (offset_normal A B) <= 1.
Proof.
  intros A B. unfold offset_normal.
  destruct (Req_dec_T (vmag_sq (seg_vec A B)) 0) as [Hz | Hnz].
  - assert (Hzero : seg_vec A B = vzero)
      by (apply (proj1 (vmag_sq_zero_iff _)); exact Hz).
    rewrite Hzero. unfold unit_perp, vperp, vscale, vzero. cbn [vx vy]. nra.
  - assert (Hne : seg_vec A B <> vzero).
    { intro Hc. apply Hnz. rewrite Hc. unfold vmag_sq, vdot, vzero. cbn. ring. }
    pose proof (vmag_sq_unit_perp (seg_vec A B) Hne) as Hu.
    unfold vmag_sq, vdot in Hu.
    pose proof (Rle_0_sqr (vy (unit_perp (seg_vec A B)))) as Hy.
    unfold Rsqr in Hy. nra.
Qed.

(* Each offset endpoint's x-coordinate is within |d| of its source's. *)
Lemma offset_point_x_shift :
  forall A B P : Point, forall d : R,
    Rabs (px (offset_point A B P d) - px P) <= Rabs d.
Proof.
  intros A B P d. unfold offset_point, pt_translate. cbn [px].
  replace (px P + d * vx (offset_normal A B) - px P)
    with (d * vx (offset_normal A B)) by ring.
  rewrite Rabs_mult.
  assert (Habs : Rabs (vx (offset_normal A B)) <= 1).
  { pose proof (offset_normal_vx_sq_le_1 A B) as Hb.
    pose proof (Rabs_pos (vx (offset_normal A B))) as Hp.
    pose proof (Rsqr_abs (vx (offset_normal A B))) as Hsq. unfold Rsqr in Hsq.
    nra. }
  rewrite <- (Rmult_1_r (Rabs d)) at 2.
  apply Rmult_le_compat_l; [ apply Rabs_pos | exact Habs ].
Qed.

(* Source edges separated in x by more than 1 + 2|d| produce offset segments
   separated in x by more than 1. *)
Lemma offset_seg_x_left_of :
  forall (A1 B1 A2 B2 : Point) (d a b : R),
    b - a > 1 + 2 * Rabs d ->
    px A1 <= a -> px B1 <= a -> px A2 >= b -> px B2 >= b ->
    x_left_of (offset_seg A1 B1 d) (offset_seg A2 B2 d).
Proof.
  intros A1 B1 A2 B2 d a b Hgap HA HB HC HD.
  pose proof (offset_point_x_shift A1 B1 A1 d) as S1.
  pose proof (offset_point_x_shift A1 B1 B1 d) as S2.
  pose proof (offset_point_x_shift A2 B2 A2 d) as S3.
  pose proof (offset_point_x_shift A2 B2 B2 d) as S4.
  assert (U1 : px (offset_point A1 B1 A1 d) - px A1 <= Rabs d)
    by (eapply Rle_trans; [apply Rle_abs | exact S1]).
  assert (U2 : px (offset_point A1 B1 B1 d) - px B1 <= Rabs d)
    by (eapply Rle_trans; [apply Rle_abs | exact S2]).
  assert (L3 : px A2 - px (offset_point A2 B2 A2 d) <= Rabs d)
    by (eapply Rle_trans; [apply Rle_abs |]; rewrite Rabs_minus_sym; exact S3).
  assert (L4 : px B2 - px (offset_point A2 B2 B2 d) <= Rabs d)
    by (eapply Rle_trans; [apply Rle_abs |]; rewrite Rabs_minus_sym; exact S4).
  exists (a + Rabs d), (b - Rabs d).
  unfold offset_seg; cbn [fst snd].
  repeat split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Buffer pipeline hook: discharging the noding hypothesis.              *)
(* -------------------------------------------------------------------------- *)

(* The honest, true discharge of the buffer headline's noding step
   (`fully_intersected (snap_round_segments (offset_curve g d))`): whenever
   the generated offset curve is pairwise nodable (separated or
   endpoint-sharing edges), its snapped arrangement is fully intersected.
   This is the weaker claim that survives HobbyCounterexample_b64.v, planted
   into the recently-closed buffer pipeline as a bridgehead. *)
Corollary buffer_offset_nodable :
  forall (g : Geometry) (d : R),
    pairwise_nodable (offset_curve g d) ->
    fully_intersected (snap_round_segments (offset_curve g d)).
Proof.
  intros g d H. apply fully_intersected_snap_of_nodable, H.
Qed.

Print Assumptions fully_intersected_snap_of_nodable.
Print Assumptions buffer_offset_nodable.
