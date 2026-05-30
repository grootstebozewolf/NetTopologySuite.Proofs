(* ============================================================================
   NetTopologySuite.Proofs.Flocq.PassesThroughHalfopen_b64
   ----------------------------------------------------------------------------
   Phase 2 follow-up: the half-open passes-through predicate.

   `b64_passes_through_hot_pixel` (HotPixel_b64.v) is:
     - complete vs the HALF-OPEN R-side `passes_through_hot_pixel` (Slice 11);
     - sound only vs the CLOSED R-side `passes_through_hot_pixel_closed`.

   The gap is the boundary region: segments grazing the top/right edge
   make the filter say true while the half-open R-spec says false (the
   `passes_through_self` non-result from Slice 11).

   This file closes the missing direction: a strictly tighter bool filter
   `b64_passes_through_hot_pixel_halfopen` that is BOTH sound AND complete
   vs the existing half-open R-spec.  Plus the bracket lemma and an explicit
   divergence witness (a segment grazing x = xhi: closed filter accepts,
   half-open rejects).

   Gates the Phase 2 oracle extraction's `PASSES_THROUGH_HALFOPEN` mode.

   Design.  The LB t-bounds use `Rmin`/`Rmax`, so which one corresponds to
   `x = xhi` depends on `sign(c1 - c0)`.  A uniform `Rle_bool -> Rlt_bool`
   substitution does NOT characterise half-open across both orientations.

   Approach: evaluate the segment at the t-MIDPOINT and require
   `x(tmid) < xhi`, `y(tmid) < yhi` explicitly.  Combined with the
   existing closed filter (which guarantees `xlo <= x(tmid) <= xhi` via
   `lb_axis_sound`), the explicit strict-upper check tightens the
   conclusion to the half-open form `xlo <= x(tmid) < xhi`.  The
   completeness direction uses a strict-interior algebraic lemma for the
   non-degenerate case; the degenerate axis-parallel case is handled
   directly by `lb_inslab_halfopen`'s strict upper-bound check.

   Audit footprint.  Same `snap_round` -> `Classical_Prop.classic` lineage
   as the other snap files; listed in docs/audit-exceptions.txt.  No
   Admitteds.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lra.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import Core.

From NTS.Proofs        Require Import Distance HotPixel.
From NTS.Proofs.Flocq  Require Import Validate_binary64.
From NTS.Proofs.Flocq  Require Import HotPixel_b64.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1 Half-open slab membership for the degenerate (axis-parallel) case.      *)
(* -------------------------------------------------------------------------- *)

(* Same as `lb_inslab` (HotPixel_b64.v:2125) but the upper-bound check is
   STRICT, matching the half-open slab `[lo, hi)`. *)
Definition lb_inslab_halfopen (c0 c1 lo hi : R) : bool :=
  if Req_dec_T c1 c0 then (Rle_bool lo c0 && Rlt_bool c0 hi) else true.

(* lb_inslab_halfopen TRUE -> lb_inslab TRUE.  Same as Rlt -> Rle on the
   strict component; trivially equal for non-degenerate. *)
Lemma lb_inslab_halfopen_implies_lb_inslab :
  forall c0 c1 lo hi,
    lb_inslab_halfopen c0 c1 lo hi = true ->
    lb_inslab c0 c1 lo hi = true.
Proof.
  intros c0 c1 lo hi H.
  unfold lb_inslab_halfopen, lb_inslab in *.
  destruct (Req_dec_T c1 c0) as [Heq | Hne]; [|exact H].
  apply Bool.andb_true_iff in H. destruct H as [Hl Hh].
  apply Bool.andb_true_iff. split; [exact Hl|].
  apply Rle_bool_true. apply Rlt_le. apply Rlt_bool_elim. exact Hh.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2 Strict-interior soundness lemma (non-degenerate axes only).             *)
(* -------------------------------------------------------------------------- *)

(* Tighter version of `lb_axis_sound` (HotPixel_b64.v:2153) for the
   non-degenerate case: strict t-interior gives strict x-interior.
   The degenerate case is excluded: when c0 = c1, x(t) is constantly c0,
   and the slab-boundary cases lo = c0 or c0 = hi don't yield strict x.
   The half-open filter handles degenerate axes via `lb_inslab_halfopen`
   directly, never invoking this lemma in the degenerate branch. *)
Lemma lb_axis_sound_strict_interior :
  forall c0 c1 lo hi t,
    lo <= hi ->
    c1 <> c0 ->
    lb_tlo c0 c1 lo hi < t ->
    t < lb_thi c0 c1 lo hi ->
    lo < (1 - t) * c0 + t * c1 < hi.
Proof.
  intros c0 c1 lo hi t Hlohi Hne Htlo Hthi.
  unfold lb_tlo, lb_thi in *.
  destruct (Req_dec_T c1 c0) as [Heq | _]; [contradiction|].
  assert (Hd : c1 - c0 <> 0) by lra.
  set (a := (lo - c0) / (c1 - c0)) in *.
  set (b := (hi - c0) / (c1 - c0)) in *.
  assert (Hva : (1 - a) * c0 + a * c1 = lo) by (unfold a; field; exact Hd).
  assert (Hvb : (1 - b) * c0 + b * c1 = hi) by (unfold b; field; exact Hd).
  assert (Hvlo : (1 - t) * c0 + t * c1 - lo = (t - a) * (c1 - c0))
    by (rewrite <- Hva; ring).
  assert (Hvhi : (1 - t) * c0 + t * c1 - hi = (t - b) * (c1 - c0))
    by (rewrite <- Hvb; ring).
  assert (Hprod_strict : (t - a) * (t - b) < 0).
  { revert Htlo Hthi. unfold Rmin, Rmax.
    destruct (Rle_dec a b); nra. }
  assert (Hsq_pos : 0 < (c1 - c0) * (c1 - c0))
    by (destruct (Rdichotomy _ _ Hd); nra).
  assert (Hineq : ((1 - t) * c0 + t * c1 - lo)
                  * ((1 - t) * c0 + t * c1 - hi) < 0).
  { replace (((1 - t) * c0 + t * c1 - lo)
            * ((1 - t) * c0 + t * c1 - hi))
      with ((t - a) * (t - b) * ((c1 - c0) * (c1 - c0)))
      by (rewrite Hvlo, Hvhi; ring).
    nra. }
  nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3 The half-open Liang-Barsky filter.                                      *)
(* -------------------------------------------------------------------------- *)

(* Filter: closed-LB conditions (with halfopen slab guards) + explicit
   strict-upper checks at the t-midpoint of the clipped t-interval.

   The midpoint witness is the key: when the clipped t-interval has strict
   interior, the midpoint lands strictly inside (lb_tlo, lb_thi) for each
   axis, and the strict-interior lemma gives `x(tmid) < xhi`.  When the
   t-interval degenerates to a point (tmin = tmax), the midpoint IS that
   point, and the strict-upper checks fall back to the explicit
   `Rlt_bool xmid xhi` -- which is exactly the half-open condition the
   R-spec demands at the witness t. *)
Definition b64_liang_barsky_touches_halfopen
    (P0 P1 C : BPoint) : bool :=
  let x0 := Binary.B2R prec emax (bx P0)  in
  let x1 := Binary.B2R prec emax (bx P1)  in
  let y0 := Binary.B2R prec emax (by_ P0) in
  let y1 := Binary.B2R prec emax (by_ P1) in
  let cx := Binary.B2R prec emax (bx C)   in
  let cy := Binary.B2R prec emax (by_ C)  in
  let xlo := cx - / 2 in let xhi := cx + / 2 in
  let ylo := cy - / 2 in let yhi := cy + / 2 in
  let tmin := Rmax 0 (Rmax (lb_tlo x0 x1 xlo xhi) (lb_tlo y0 y1 ylo yhi)) in
  let tmax := Rmin 1 (Rmin (lb_thi x0 x1 xlo xhi) (lb_thi y0 y1 ylo yhi)) in
  let tmid := (tmin + tmax) / 2 in
  let xmid := (1 - tmid) * x0 + tmid * x1 in
  let ymid := (1 - tmid) * y0 + tmid * y1 in
  lb_inslab_halfopen x0 x1 xlo xhi
  && lb_inslab_halfopen y0 y1 ylo yhi
  && Rle_bool tmin tmax
  && Rlt_bool xmid xhi
  && Rlt_bool ymid yhi.

(* The half-open filter is strictly tighter than the closed filter.
   Both lb_inslab_halfopen-conditions imply lb_inslab; the closed filter's
   t-overlap `Rle_bool tmin tmax` is the same in both.  The two extra
   strict-upper midpoint checks are additional conjuncts. *)
Lemma b64_liang_barsky_touches_halfopen_implies_closed :
  forall P0 P1 C : BPoint,
    b64_liang_barsky_touches_halfopen P0 P1 C = true ->
    b64_liang_barsky_touches P0 P1 C = true.
Proof.
  intros P0 P1 C H.
  unfold b64_liang_barsky_touches_halfopen in H.
  unfold b64_liang_barsky_touches.
  apply Bool.andb_true_iff in H. destruct H as [H _Hymid].
  apply Bool.andb_true_iff in H. destruct H as [H _Hxmid].
  apply Bool.andb_true_iff in H. destruct H as [H Hcmp].
  apply Bool.andb_true_iff in H. destruct H as [Hsx Hsy].
  apply Bool.andb_true_iff. split; [|exact Hcmp].
  apply Bool.andb_true_iff. split.
  - apply lb_inslab_halfopen_implies_lb_inslab. exact Hsx.
  - apply lb_inslab_halfopen_implies_lb_inslab. exact Hsy.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4 Soundness of the half-open filter vs the half-open R-spec.              *)
(* -------------------------------------------------------------------------- *)

(* The half-open spec at the segment's t-midpoint, as a Prop.  This is the
   `b64_segment_touches_hot_pixel_spec` form (line 714) for the half-open
   slab. *)
Lemma b64_liang_barsky_touches_halfopen_sound :
  forall P0 P1 C : BPoint,
    b64_liang_barsky_touches_halfopen P0 P1 C = true ->
    b64_segment_touches_hot_pixel_spec P0 P1 C.
Proof.
  intros P0 P1 C H.
  pose proof H as Hclosed.
  apply b64_liang_barsky_touches_halfopen_implies_closed in Hclosed.
  (* Get the closed soundness conclusion, then refine with the midpoint
     strict-upper checks. *)
  unfold b64_liang_barsky_touches_halfopen in H.
  apply Bool.andb_true_iff in H. destruct H as [H Hymid].
  apply Bool.andb_true_iff in H. destruct H as [H Hxmid].
  apply Bool.andb_true_iff in H. destruct H as [H Hcmp].
  apply Bool.andb_true_iff in H. destruct H as [Hsx Hsy].
  apply Rle_bool_elim in Hcmp.
  apply Rlt_bool_elim in Hxmid.
  apply Rlt_bool_elim in Hymid.
  (* Witness: t = the midpoint of the clipped t-interval. *)
  set (x0 := Binary.B2R prec emax (bx P0)) in *.
  set (x1 := Binary.B2R prec emax (bx P1)) in *.
  set (y0 := Binary.B2R prec emax (by_ P0)) in *.
  set (y1 := Binary.B2R prec emax (by_ P1)) in *.
  set (cx := Binary.B2R prec emax (bx C)) in *.
  set (cy := Binary.B2R prec emax (by_ C)) in *.
  set (xlo := cx - / 2) in *. set (xhi := cx + / 2) in *.
  set (ylo := cy - / 2) in *. set (yhi := cy + / 2) in *.
  set (tmin := Rmax 0 (Rmax (lb_tlo x0 x1 xlo xhi) (lb_tlo y0 y1 ylo yhi))) in *.
  set (tmax := Rmin 1 (Rmin (lb_thi x0 x1 xlo xhi) (lb_thi y0 y1 ylo yhi))) in *.
  set (tmid := (tmin + tmax) / 2) in *.
  exists tmid.
  assert (H0_tmin : 0 <= tmin)
    by (unfold tmin; apply Rmax_l).
  assert (Htmax_1 : tmax <= 1)
    by (unfold tmax; apply Rmin_l).
  assert (Htlox_tmin : lb_tlo x0 x1 xlo xhi <= tmin).
  { unfold tmin. eapply Rle_trans; [|apply Rmax_r].
    apply Rmax_l. }
  assert (Htloy_tmin : lb_tlo y0 y1 ylo yhi <= tmin).
  { unfold tmin. eapply Rle_trans; [|apply Rmax_r].
    apply Rmax_r. }
  assert (Hthix_tmax : tmax <= lb_thi x0 x1 xlo xhi).
  { unfold tmax. eapply Rle_trans; [apply Rmin_r|]. apply Rmin_l. }
  assert (Hthiy_tmax : tmax <= lb_thi y0 y1 ylo yhi).
  { unfold tmax. eapply Rle_trans; [apply Rmin_r|]. apply Rmin_r. }
  assert (Htmid_range : 0 <= tmid <= 1).
  { unfold tmid. split; lra. }
  assert (Htlox_tmid : lb_tlo x0 x1 xlo xhi <= tmid)
    by (unfold tmid; lra).
  assert (Htmid_thix : tmid <= lb_thi x0 x1 xlo xhi)
    by (unfold tmid; lra).
  assert (Htloy_tmid : lb_tlo y0 y1 ylo yhi <= tmid)
    by (unfold tmid; lra).
  assert (Htmid_thiy : tmid <= lb_thi y0 y1 ylo yhi)
    by (unfold tmid; lra).
  assert (Hxlohi : xlo <= xhi) by (unfold xlo, xhi; lra).
  assert (Hylohi : ylo <= yhi) by (unfold ylo, yhi; lra).
  (* Closed bounds at the midpoint by lb_axis_sound. *)
  pose proof (lb_axis_sound x0 x1 xlo xhi tmid Hxlohi
                (lb_inslab_halfopen_implies_lb_inslab _ _ _ _ Hsx)
                Htlox_tmid Htmid_thix) as [Hxlo_mid Hxhi_mid].
  pose proof (lb_axis_sound y0 y1 ylo yhi tmid Hylohi
                (lb_inslab_halfopen_implies_lb_inslab _ _ _ _ Hsy)
                Htloy_tmid Htmid_thiy) as [Hylo_mid Hyhi_mid].
  (* Unfold the goal: b64_segment_touches_hot_pixel_spec is the
     R-side segment_touches_hot_pixel via BP2P. *)
  unfold b64_segment_touches_hot_pixel_spec, segment_touches_hot_pixel.
  split; [exact Htmid_range|].
  unfold in_hot_pixel, segment_point, BP2P, px, py, hot_pixel_radius.
  simpl. replace (/ (2 * 1)) with (/ 2) by lra.
  fold x0 x1 y0 y1 cx cy.
  split; split.
  - (* xlo <= x(tmid) *)
    fold xlo. exact Hxlo_mid.
  - (* x(tmid) < xhi *)
    fold xhi. exact Hxmid.
  - (* ylo <= y(tmid) *)
    fold ylo. exact Hylo_mid.
  - (* y(tmid) < yhi *)
    fold yhi. exact Hymid.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5 Completeness of the half-open filter vs the half-open R-spec.           *)
(* -------------------------------------------------------------------------- *)

Lemma b64_liang_barsky_touches_halfopen_complete :
  forall P0 P1 C : BPoint,
    b64_segment_touches_hot_pixel_spec P0 P1 C ->
    b64_liang_barsky_touches_halfopen P0 P1 C = true.
Proof.
  intros P0 P1 C [t [Ht Hin]].
  unfold in_hot_pixel, segment_point, BP2P, px, py, hot_pixel_radius in Hin.
  simpl in Hin. replace (/ (2 * 1)) with (/ 2) in Hin by lra.
  destruct Hin as [[Hxlo Hxhi] [Hylo Hyhi]].
  unfold b64_liang_barsky_touches_halfopen.
  set (x0 := Binary.B2R prec emax (bx P0)) in *.
  set (x1 := Binary.B2R prec emax (bx P1)) in *.
  set (y0 := Binary.B2R prec emax (by_ P0)) in *.
  set (y1 := Binary.B2R prec emax (by_ P1)) in *.
  set (cx := Binary.B2R prec emax (bx C)) in *.
  set (cy := Binary.B2R prec emax (by_ C)) in *.
  set (xlo := cx - / 2) in *. set (xhi := cx + / 2) in *.
  set (ylo := cy - / 2) in *. set (yhi := cy + / 2) in *.
  (* lb_axis_complete on each axis gives lb_inslab + the closed t-bounds. *)
  pose proof (lb_axis_complete x0 x1 xlo xhi t Ht
                (conj Hxlo (Rlt_le _ _ Hxhi))) as [Hsx [Htlox Hthix]].
  pose proof (lb_axis_complete y0 y1 ylo yhi t Ht
                (conj Hylo (Rlt_le _ _ Hyhi))) as [Hsy [Htloy Hthiy]].
  set (tmin := Rmax 0 (Rmax (lb_tlo x0 x1 xlo xhi) (lb_tlo y0 y1 ylo yhi))) in *.
  set (tmax := Rmin 1 (Rmin (lb_thi x0 x1 xlo xhi) (lb_thi y0 y1 ylo yhi))) in *.
  assert (Htmin_t : tmin <= t).
  { unfold tmin.
    apply Rmax_lub; [apply (proj1 Ht)|].
    apply Rmax_lub; [exact Htlox | exact Htloy]. }
  assert (Ht_tmax : t <= tmax).
  { unfold tmax.
    apply Rmin_glb; [apply (proj2 Ht)|].
    apply Rmin_glb; [exact Hthix | exact Hthiy]. }
  assert (Htmin_tmax : tmin <= tmax) by lra.
  (* Strengthen lb_inslab to lb_inslab_halfopen using the half-open hypothesis. *)
  assert (Hsx_ho : lb_inslab_halfopen x0 x1 xlo xhi = true).
  { unfold lb_inslab_halfopen.
    destruct (Req_dec_T x1 x0) as [Heq | Hne]; [|reflexivity].
    (* Degenerate x: c0 = c1.  From Hxlo, Hxhi at t: xlo <= x(t) < xhi.
       In the degenerate case x(t) is constant = x0 = x1. *)
    apply Bool.andb_true_iff. split.
    - apply Rle_bool_true.
      replace ((1 - t) * x0 + t * x1) with x0 in Hxlo by (rewrite Heq; ring).
      exact Hxlo.
    - apply Rlt_bool_true.
      replace ((1 - t) * x0 + t * x1) with x0 in Hxhi by (rewrite Heq; ring).
      exact Hxhi. }
  assert (Hsy_ho : lb_inslab_halfopen y0 y1 ylo yhi = true).
  { unfold lb_inslab_halfopen.
    destruct (Req_dec_T y1 y0) as [Heq | Hne]; [|reflexivity].
    apply Bool.andb_true_iff. split.
    - apply Rle_bool_true.
      replace ((1 - t) * y0 + t * y1) with y0 in Hylo by (rewrite Heq; ring).
      exact Hylo.
    - apply Rlt_bool_true.
      replace ((1 - t) * y0 + t * y1) with y0 in Hyhi by (rewrite Heq; ring).
      exact Hyhi. }
  set (tmid := (tmin + tmax) / 2) in *.
  (* Strict-upper midpoint checks: case-split on tmin = tmax vs tmin < tmax. *)
  assert (Hxmid : (1 - tmid) * x0 + tmid * x1 < xhi).
  { destruct (Req_dec_T tmin tmax) as [Heq_t | Hne_t].
    - (* tmin = tmax forces tmid = tmin = t (since tmin <= t <= tmax). *)
      assert (Htmid_eq_t : tmid = t).
      { unfold tmid. rewrite <- Heq_t. lra. }
      rewrite Htmid_eq_t. exact Hxhi.
    - (* tmin < tmax: midpoint is strict interior of (lb_tlo_x, lb_thi_x).
         Use the strict-interior lemma on the non-degenerate x-axis, OR
         the degenerate-case argument on lb_inslab_halfopen. *)
      assert (Htmin_lt_tmax : tmin < tmax) by lra.
      assert (Htlox_tmid : lb_tlo x0 x1 xlo xhi <= tmid).
      { unfold tmid, tmin.
        eapply Rle_trans;
          [|apply Rmult_le_compat_r; [lra|]; apply Rplus_le_compat_r].
        instantiate (1 := lb_tlo x0 x1 xlo xhi).
        - lra.
        - eapply Rle_trans; [|apply Rmax_r]. apply Rmax_l. }
      assert (Htmid_thix : tmid <= lb_thi x0 x1 xlo xhi).
      { unfold tmid, tmax.
        eapply Rle_trans;
          [apply Rmult_le_compat_r; [lra|]; apply Rplus_le_compat_l|].
        instantiate (1 := lb_thi x0 x1 xlo xhi).
        - eapply Rle_trans; [apply Rmin_r|]. apply Rmin_l.
        - lra. }
      destruct (Req_dec_T x1 x0) as [Heq_x | Hne_x].
      + (* Degenerate x: x is constant x0 = x1.  lb_inslab_halfopen gives
           x0 < xhi. *)
        unfold lb_inslab_halfopen in Hsx_ho.
        destruct (Req_dec_T x1 x0) as [_ | Hne]; [|contradiction].
        apply Bool.andb_true_iff in Hsx_ho.
        destruct Hsx_ho as [_ Hxhi_const].
        apply Rlt_bool_elim in Hxhi_const.
        replace ((1 - tmid) * x0 + tmid * x1) with x0 by (rewrite Heq_x; ring).
        exact Hxhi_const.
      + (* Non-degenerate: strict-interior algebra.  Need
           lb_tlo_x < tmid < lb_thi_x strict.

           tmid = (tmin + tmax)/2 with tmin < tmax => tmid in (tmin, tmax).
           tmin >= lb_tlo_x and tmax <= lb_thi_x: so tmid > tmin >= lb_tlo_x
           and tmid < tmax <= lb_thi_x.  Both strict. *)
        assert (Htmin_tmid : tmin < tmid) by (unfold tmid; lra).
        assert (Htmid_tmax : tmid < tmax) by (unfold tmid; lra).
        assert (Hstrict_lo : lb_tlo x0 x1 xlo xhi < tmid).
        { eapply Rle_lt_trans; [|exact Htmin_tmid].
          unfold tmin. eapply Rle_trans; [|apply Rmax_r]. apply Rmax_l. }
        assert (Hstrict_hi : tmid < lb_thi x0 x1 xlo xhi).
        { eapply Rlt_le_trans; [exact Htmid_tmax|].
          unfold tmax. eapply Rle_trans; [apply Rmin_r|]. apply Rmin_l. }
        assert (Hxlohi : xlo <= xhi) by (unfold xlo, xhi; lra).
        pose proof (lb_axis_sound_strict_interior
                      x0 x1 xlo xhi tmid Hxlohi Hne_x
                      Hstrict_lo Hstrict_hi) as [_ Hx_lt_xhi].
        exact Hx_lt_xhi. }
  assert (Hymid : (1 - tmid) * y0 + tmid * y1 < yhi).
  { destruct (Req_dec_T tmin tmax) as [Heq_t | Hne_t].
    - assert (Htmid_eq_t : tmid = t).
      { unfold tmid. rewrite <- Heq_t. lra. }
      rewrite Htmid_eq_t. exact Hyhi.
    - assert (Htmin_lt_tmax : tmin < tmax) by lra.
      destruct (Req_dec_T y1 y0) as [Heq_y | Hne_y].
      + unfold lb_inslab_halfopen in Hsy_ho.
        destruct (Req_dec_T y1 y0) as [_ | Hne]; [|contradiction].
        apply Bool.andb_true_iff in Hsy_ho.
        destruct Hsy_ho as [_ Hyhi_const].
        apply Rlt_bool_elim in Hyhi_const.
        replace ((1 - tmid) * y0 + tmid * y1) with y0 by (rewrite Heq_y; ring).
        exact Hyhi_const.
      + assert (Htmin_tmid : tmin < tmid) by (unfold tmid; lra).
        assert (Htmid_tmax : tmid < tmax) by (unfold tmid; lra).
        assert (Hstrict_lo : lb_tlo y0 y1 ylo yhi < tmid).
        { eapply Rle_lt_trans; [|exact Htmin_tmid].
          unfold tmin. eapply Rle_trans; [|apply Rmax_r]. apply Rmax_r. }
        assert (Hstrict_hi : tmid < lb_thi y0 y1 ylo yhi).
        { eapply Rlt_le_trans; [exact Htmid_tmax|].
          unfold tmax. eapply Rle_trans; [apply Rmin_r|]. apply Rmin_r. }
        assert (Hylohi : ylo <= yhi) by (unfold ylo, yhi; lra).
        pose proof (lb_axis_sound_strict_interior
                      y0 y1 ylo yhi tmid Hylohi Hne_y
                      Hstrict_lo Hstrict_hi) as [_ Hy_lt_yhi].
        exact Hy_lt_yhi. }
  (* Assemble. *)
  apply Bool.andb_true_iff. split.
  apply Bool.andb_true_iff. split.
  apply Bool.andb_true_iff. split.
  apply Bool.andb_true_iff. split.
  - exact Hsx_ho.
  - exact Hsy_ho.
  - apply Rle_bool_true. exact Htmin_tmax.
  - apply Rlt_bool_true. exact Hxmid.
  - apply Rlt_bool_true. exact Hymid.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6 The half-open passes-through predicate.                                 *)
(* -------------------------------------------------------------------------- *)

(* Mirror of `b64_passes_through_hot_pixel` (HotPixel_b64.v:2374) using the
   half-open LB filter on both the original and the snapped segment. *)
Definition b64_passes_through_hot_pixel_halfopen (P0 P1 C : BPoint) : bool :=
  b64_liang_barsky_touches_halfopen P0 P1 C &&
  b64_liang_barsky_touches_halfopen (b64_snap P0) (b64_snap P1) C.

(* Soundness vs the half-open R-spec.  Mirror of b64_passes_through_complete
   structure but in the SOUND direction (the missing direction for the
   existing filter). *)
Theorem b64_passes_through_hot_pixel_halfopen_sound :
  forall P0 P1 C : BPoint,
    b64_passes_through_hot_pixel_halfopen P0 P1 C = true ->
    passes_through_hot_pixel (BP2P P0) (BP2P P1) (BP2P C) 1.
Proof.
  intros P0 P1 C H.
  unfold b64_passes_through_hot_pixel_halfopen in H.
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  split.
  - exact (b64_liang_barsky_touches_halfopen_sound _ _ _ H1).
  - pose proof (b64_liang_barsky_touches_halfopen_sound _ _ _ H2) as Hs.
    unfold b64_segment_touches_hot_pixel_spec in Hs.
    rewrite !BP2P_b64_snap in Hs. exact Hs.
Qed.

(* Completeness vs the half-open R-spec.  Mirror of b64_passes_through_complete
   for the new tighter filter. *)
Theorem b64_passes_through_hot_pixel_halfopen_complete :
  forall P0 P1 C : BPoint,
    passes_through_hot_pixel (BP2P P0) (BP2P P1) (BP2P C) 1 ->
    b64_passes_through_hot_pixel_halfopen P0 P1 C = true.
Proof.
  intros P0 P1 C [H1 H2].
  unfold b64_passes_through_hot_pixel_halfopen.
  rewrite Bool.andb_true_iff. split.
  - apply b64_liang_barsky_touches_halfopen_complete. exact H1.
  - apply b64_liang_barsky_touches_halfopen_complete.
    unfold b64_segment_touches_hot_pixel_spec.
    rewrite !BP2P_b64_snap. exact H2.
Qed.

(* -------------------------------------------------------------------------- *)
(* §7 The bracket lemma: halfopen TRUE -> closed TRUE.                        *)
(* -------------------------------------------------------------------------- *)

(* The halfopen filter is strictly tighter than the closed one (half-open
   pixel is a subset of the closed pixel).  This is the option-layer pin's
   TRUE-branch contract for the oracle. *)
Lemma b64_passes_through_hot_pixel_halfopen_implies_closed :
  forall P0 P1 C : BPoint,
    b64_passes_through_hot_pixel_halfopen P0 P1 C = true ->
    b64_passes_through_hot_pixel P0 P1 C = true.
Proof.
  intros P0 P1 C H.
  unfold b64_passes_through_hot_pixel_halfopen in H.
  unfold b64_passes_through_hot_pixel.
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  apply Bool.andb_true_iff. split.
  - apply b64_liang_barsky_touches_halfopen_implies_closed. exact H1.
  - apply b64_liang_barsky_touches_halfopen_implies_closed. exact H2.
Qed.

(* -------------------------------------------------------------------------- *)
(* §8 Divergence witness.                                                     *)
(*                                                                            *)
(* There exist b64 inputs where the closed filter accepts (`= true`) and the *)
(* half-open filter rejects (`= false`).  Construction:                       *)
(*                                                                            *)
(*   P0 = (1, 0), P1 = (1, 0), C = (1/2, 0).                                  *)
(*                                                                            *)
(* Pixel slabs at this center: x in [0, 1] (closed) vs [0, 1) (half-open),    *)
(* y in [-1/2, 1/2] vs [-1/2, 1/2).  The segment is the degenerate point     *)
(* (1, 0) on the upper x-boundary of the closed slab (which the closed       *)
(* filter accepts) but outside the half-open slab (which the half-open       *)
(* filter rejects via `lb_inslab_halfopen_x = false`).  Snap is identity     *)
(* at integer coordinates so the snapped filter agrees with the original.    *)
(*                                                                            *)
(* The bracket lemma above is the option-layer pin's load-bearing piece;     *)
(* this witness formalises the bracket gap's non-vacuity, evident at the    *)
(* spec level from `in_hot_pixel`'s `<= , <` shape.                          *)
(* -------------------------------------------------------------------------- *)

(* Local b64 zero -- the IEEE positive zero. *)
Definition b64_zero : binary64 := Binary.B754_zero prec emax false.

Lemma B2R_b64_zero : Binary.B2R prec emax b64_zero = 0.
Proof. reflexivity. Qed.

(* `snap_round_coord 1 1 = 1`: 1 is already on the unit integer grid, so
   round-to-nearest-even is the identity. *)
Lemma snap_round_coord_one : snap_round_coord 1 1 = 1.
Proof.
  unfold snap_round_coord. rewrite Rmult_1_r, Rdiv_1_r.
  apply round_generic; auto with typeclass_instances.
  apply generic_format_FIX.
  exists (Defs.Float radix2 1%Z 0%Z); simpl.
  - unfold F2R; simpl. lra.
  - reflexivity.
Qed.

(* `snap_round_coord 0 1 = 0`. *)
Lemma snap_round_coord_zero : snap_round_coord 0 1 = 0.
Proof.
  unfold snap_round_coord. rewrite Rmult_0_l, Rdiv_1_r.
  apply round_0; auto with typeclass_instances.
Qed.

(* B2R of the snapped b64_one is 1 (1 stays on the integer grid). *)
Lemma B2R_b64_snap_one :
  Binary.B2R prec emax (b64_snap_coord b64_one) = 1.
Proof.
  rewrite b64_snap_coord_B2R, B2R_b64_one.
  apply snap_round_coord_one.
Qed.

(* B2R of the snapped b64_zero is 0. *)
Lemma B2R_b64_snap_zero :
  Binary.B2R prec emax (b64_snap_coord b64_zero) = 0.
Proof.
  rewrite b64_snap_coord_B2R, B2R_b64_zero.
  apply snap_round_coord_zero.
Qed.

(* lb_inslab on the degenerate axis at x = upper boundary: closed = true. *)
Lemma lb_inslab_one_one_zero_one : lb_inslab 1 1 0 1 = true.
Proof.
  unfold lb_inslab.
  destruct (Req_dec_T 1 1) as [_ | Hne]; [|exfalso; apply Hne; reflexivity].
  apply Bool.andb_true_iff. split; apply Rle_bool_true; lra.
Qed.

(* lb_inslab_halfopen on the degenerate axis at x = upper boundary: false
   (the strict `c0 < hi` check excludes the boundary). *)
Lemma lb_inslab_halfopen_one_one_zero_one :
  lb_inslab_halfopen 1 1 0 1 = false.
Proof.
  unfold lb_inslab_halfopen.
  destruct (Req_dec_T 1 1) as [_ | Hne]; [|exfalso; apply Hne; reflexivity].
  apply Bool.andb_false_iff. right.
  apply Rlt_bool_false. lra.
Qed.

(* lb_inslab on the degenerate y-axis at y=0 in slab [-1/2, 1/2]: true. *)
Lemma lb_inslab_zero_zero_halfneg_half : lb_inslab 0 0 (- / 2) (/ 2) = true.
Proof.
  unfold lb_inslab.
  destruct (Req_dec_T 0 0) as [_ | Hne]; [|exfalso; apply Hne; reflexivity].
  apply Bool.andb_true_iff. split; apply Rle_bool_true; lra.
Qed.

(* lb_tlo at the degenerate axis: 0. *)
Lemma lb_tlo_degenerate : forall c lo hi, lb_tlo c c lo hi = 0.
Proof.
  intros. unfold lb_tlo.
  destruct (Req_dec_T c c) as [_ | Hne]; [reflexivity|].
  exfalso; apply Hne; reflexivity.
Qed.

(* lb_thi at the degenerate axis: 1. *)
Lemma lb_thi_degenerate : forall c lo hi, lb_thi c c lo hi = 1.
Proof.
  intros. unfold lb_thi.
  destruct (Req_dec_T c c) as [_ | Hne]; [reflexivity|].
  exfalso; apply Hne; reflexivity.
Qed.

(* The boundary divergence witness.  Closed filter accepts, half-open
   rejects, on the same b64 input. *)
Theorem b64_passes_through_hot_pixel_boundary_diverges :
  exists P0 P1 C : BPoint,
    b64_passes_through_hot_pixel P0 P1 C = true /\
    b64_passes_through_hot_pixel_halfopen P0 P1 C = false.
Proof.
  exists (mkBP b64_one b64_zero).
  exists (mkBP b64_one b64_zero).
  exists (mkBP b64_half b64_zero).
  split.
  - (* CLOSED filter: true. *)
    unfold b64_passes_through_hot_pixel.
    apply Bool.andb_true_iff. split.
    + (* Original segment (1,0)-(1,0) at center (1/2, 0). *)
      unfold b64_liang_barsky_touches.
      cbn [bx by_].
      rewrite B2R_b64_one, B2R_b64_half, B2R_b64_zero.
      replace (/ 2 - / 2) with 0 by lra.
      replace (/ 2 + / 2) with 1 by lra.
      replace (0 - / 2) with (- / 2) by lra.
      replace (0 + / 2) with (/ 2) by lra.
      rewrite lb_inslab_one_one_zero_one.
      rewrite lb_inslab_zero_zero_halfneg_half.
      rewrite !lb_tlo_degenerate, !lb_thi_degenerate.
      simpl andb.
      apply Rle_bool_true.
      apply Rmax_lub;
        [apply Rmin_glb; [lra | apply Rmin_glb; lra]
        |apply Rmax_lub;
           [apply Rmin_glb; [lra | apply Rmin_glb; lra]
           |apply Rmin_glb; [lra | apply Rmin_glb; lra]]].
    + (* Snapped segment.  Snap of (1, 0) stays (B2R = 1, B2R = 0). *)
      unfold b64_liang_barsky_touches.
      cbn [bx by_ b64_snap].
      rewrite B2R_b64_snap_one, B2R_b64_snap_zero.
      rewrite B2R_b64_half, B2R_b64_zero.
      replace (/ 2 - / 2) with 0 by lra.
      replace (/ 2 + / 2) with 1 by lra.
      replace (0 - / 2) with (- / 2) by lra.
      replace (0 + / 2) with (/ 2) by lra.
      rewrite lb_inslab_one_one_zero_one.
      rewrite lb_inslab_zero_zero_halfneg_half.
      rewrite !lb_tlo_degenerate, !lb_thi_degenerate.
      simpl andb.
      apply Rle_bool_true.
      apply Rmax_lub;
        [apply Rmin_glb; [lra | apply Rmin_glb; lra]
        |apply Rmax_lub;
           [apply Rmin_glb; [lra | apply Rmin_glb; lra]
           |apply Rmin_glb; [lra | apply Rmin_glb; lra]]].
  - (* HALFOPEN filter: false. *)
    unfold b64_passes_through_hot_pixel_halfopen.
    apply Bool.andb_false_iff. left.
    unfold b64_liang_barsky_touches_halfopen.
    cbn [bx by_].
    rewrite B2R_b64_one, B2R_b64_half, B2R_b64_zero.
    replace (/ 2 - / 2) with 0 by lra.
    replace (/ 2 + / 2) with 1 by lra.
    rewrite lb_inslab_halfopen_one_one_zero_one.
    reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_passes_through_hot_pixel_halfopen_sound.
Print Assumptions b64_passes_through_hot_pixel_halfopen_complete.
Print Assumptions b64_passes_through_hot_pixel_halfopen_implies_closed.
Print Assumptions B2R_b64_zero.
Print Assumptions snap_round_coord_one.
Print Assumptions snap_round_coord_zero.
Print Assumptions b64_passes_through_hot_pixel_boundary_diverges.
