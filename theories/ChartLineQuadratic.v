(* ============================================================================
   NetTopologySuite.Proofs.ChartLineQuadratic
   ----------------------------------------------------------------------------
   C1 kernel, oracle lane (#767 / #770).  Chord line against the C0 chart
   circle, as a quadratic in τ.

     chart_line_qa = cross(d, Q − S0)     zero iff the pole lies on the line
     chart_line_qb = 2 · dot(d, O − Q)
     chart_line_qc = cross(d, (2O − Q) − S0)    2O − Q is the τ = 0 point
     chart_line_qf t = qa·t² + qb·t + qc

   dot, crs, vx_of, vy_of come from CircleChart.  Do not shadow them.

   Verified shape on Coq 8.18 (classic-free).  Re-run Print Assumptions
   on the corpus Rocq before any consumer.  C1.4–C1.14 are not in this
   file.  No Admitted.

   TCross2 decision (not proved here): pre-split the chord at the foot
     tF = dot(d, O − S0) / |d|²
   which is rational, and tj1 + tj2 = 2·tF.  Each piece is TCross1 or
   TEmpty, so IResult stays IHit | IEmpty | IDecline.  No two-hit arm.
   No re-cook of LeftoverBagTermArm / #814 / LoopDischarged.

   The extra collinear vertex F is an oracle-lane artefact.  This file
   does not claim noding-output equivalence with NTS.  That claim waits
   on a proved collinear post-merge.  Endpoint and boundary tangency
   stay inside TCross / TTouch.  No TEnd.  d = 0 is out of scope.

   Does not remint CircularEgg, CircGamma, IResult, or MkNurbs.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import CircleChart.

Local Open Scope R_scope.

Section ChartLine.
Variables ox oy qx qy s0x s0y dx dy : R.

Definition chart_line_cpx (t : R) : R :=
  ox + vx_of (ox - qx) (oy - qy) t.
Definition chart_line_cpy (t : R) : R :=
  oy + vy_of (ox - qx) (oy - qy) t.

Definition chart_line_qa : R :=
  crs dx dy (qx - s0x) (qy - s0y).
Definition chart_line_qb : R :=
  2 * dot dx dy (ox - qx) (oy - qy).
Definition chart_line_qc : R :=
  crs dx dy (2 * ox - qx - s0x) (2 * oy - qy - s0y).
Definition chart_line_qf (t : R) : R :=
  chart_line_qa * t * t + chart_line_qb * t + chart_line_qc.

Theorem line_chart_quadratic : forall t,
  crs dx dy (chart_line_cpx t - s0x) (chart_line_cpy t - s0y) * (1 + t * t)
  = chart_line_qf t.
Proof.
  intro t. assert (0 < 1 + t * t) by nra.
  unfold chart_line_qf, chart_line_qa, chart_line_qb, chart_line_qc,
    chart_line_cpx, chart_line_cpy, vx_of, vy_of, crs, dot.
  field. lra.
Qed.

Theorem disc_identity :
  chart_line_qb * chart_line_qb - 4 * chart_line_qa * chart_line_qc
  = 4 * ((dx * dx + dy * dy)
           * dot (ox - qx) (oy - qy) (ox - qx) (oy - qy)
         - crs dx dy (ox - s0x) (oy - s0y)
           * crs dx dy (ox - s0x) (oy - s0y)).
Proof.
  unfold chart_line_qa, chart_line_qb, chart_line_qc, crs, dot. ring.
Qed.

Definition chart_line_tj (t : R) : R :=
  dot dx dy (chart_line_cpx t - s0x) (chart_line_cpy t - s0y)
  / (dx * dx + dy * dy).

Theorem on_line_param : forall t,
  (dx, dy) <> (0, 0) ->
  chart_line_qf t = 0 ->
  chart_line_cpx t = s0x + chart_line_tj t * dx /\
  chart_line_cpy t = s0y + chart_line_tj t * dy.
Proof.
  intros t Hd Hf.
  assert (Hdd : 0 < dx * dx + dy * dy).
  { destruct (Req_dec dx 0) as [->|Hx].
    - destruct (Req_dec dy 0) as [->|Hy]; [congruence|]. nra.
    - nra. }
  assert (Hc : crs dx dy (chart_line_cpx t - s0x) (chart_line_cpy t - s0y) = 0).
  { pose proof (line_chart_quadratic t) as E. rewrite Hf in E.
    assert (0 < 1 + t * t) by nra. nra. }
  unfold chart_line_tj, dot.
  set (dd := dx * dx + dy * dy) in *.
  assert (EX : (chart_line_cpx t - s0x) * dd
             = (dx * (chart_line_cpx t - s0x) + dy * (chart_line_cpy t - s0y)) * dx
               - crs dx dy (chart_line_cpx t - s0x) (chart_line_cpy t - s0y) * dy)
    by (unfold dd, crs; ring).
  assert (EY : (chart_line_cpy t - s0y) * dd
             = (dx * (chart_line_cpx t - s0x) + dy * (chart_line_cpy t - s0y)) * dy
               + crs dx dy (chart_line_cpx t - s0x) (chart_line_cpy t - s0y) * dx)
    by (unfold dd, crs; ring).
  rewrite Hc in EX, EY.
  split.
  - apply (Rmult_eq_reg_r dd); [| lra].
    replace ((s0x + (dx * (chart_line_cpx t - s0x)
                      + dy * (chart_line_cpy t - s0y)) / dd * dx) * dd)
      with (s0x * dd
            + (dx * (chart_line_cpx t - s0x)
               + dy * (chart_line_cpy t - s0y)) * dx) by (field; lra).
    replace (chart_line_cpx t * dd)
      with ((chart_line_cpx t - s0x) * dd + s0x * dd) by ring.
    rewrite EX. ring.
  - apply (Rmult_eq_reg_r dd); [| lra].
    replace ((s0y + (dx * (chart_line_cpx t - s0x)
                      + dy * (chart_line_cpy t - s0y)) / dd * dy) * dd)
      with (s0y * dd
            + (dx * (chart_line_cpx t - s0x)
               + dy * (chart_line_cpy t - s0y)) * dy) by (field; lra).
    replace (chart_line_cpy t * dd)
      with ((chart_line_cpy t - s0y) * dd + s0y * dd) by ring.
    rewrite EY. ring.
Qed.

End ChartLine.

Print Assumptions line_chart_quadratic.
Print Assumptions disc_identity.
Print Assumptions on_line_param.
