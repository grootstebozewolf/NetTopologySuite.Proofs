(* ============================================================================
   NetTopologySuite.Proofs.ChartLineQuadratic
   ----------------------------------------------------------------------------
   ζ = stereographic half-tangent chart; not the corpus tag τ, not the ArcParamBridge sweep ψ.
   C1 kernel, oracle lane (#767 / #770).  Chord line against the C0 chart
   circle, as a quadratic in ζ.

     zeta_qa = cross(d, Q − S0)     zero iff the pole lies on the line
     zeta_qb = 2 · dot(d, O − Q)
     zeta_qc = cross(d, (2O − Q) − S0)    2O − Q is the ζ = 0 point
     zeta_qf t = zeta_qa·t² + zeta_qb·t + zeta_qc

   dot, crs, zeta_ptx, zeta_pty come from CircleChart.  Do not shadow them.

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

Definition zeta_abs_x (t : R) : R :=
  ox + zeta_ptx (ox - qx) (oy - qy) t.
Definition zeta_abs_y (t : R) : R :=
  oy + zeta_pty (ox - qx) (oy - qy) t.

Definition zeta_qa : R :=
  crs dx dy (qx - s0x) (qy - s0y).
Definition zeta_qb : R :=
  2 * dot dx dy (ox - qx) (oy - qy).
Definition zeta_qc : R :=
  crs dx dy (2 * ox - qx - s0x) (2 * oy - qy - s0y).
Definition zeta_qf (t : R) : R :=
  zeta_qa * t * t + zeta_qb * t + zeta_qc.

Theorem line_chart_quadratic : forall t,
  crs dx dy (zeta_abs_x t - s0x) (zeta_abs_y t - s0y) * (1 + t * t)
  = zeta_qf t.
Proof.
  intro t. assert (0 < 1 + t * t) by nra.
  unfold zeta_qf, zeta_qa, zeta_qb, zeta_qc,
    zeta_abs_x, zeta_abs_y, zeta_ptx, zeta_pty, crs, dot.
  field. lra.
Qed.

Theorem disc_identity :
  zeta_qb * zeta_qb - 4 * zeta_qa * zeta_qc
  = 4 * ((dx * dx + dy * dy)
           * dot (ox - qx) (oy - qy) (ox - qx) (oy - qy)
         - crs dx dy (ox - s0x) (oy - s0y)
           * crs dx dy (ox - s0x) (oy - s0y)).
Proof.
  unfold zeta_qa, zeta_qb, zeta_qc, crs, dot. ring.
Qed.

Definition tj_of (t : R) : R :=
  dot dx dy (zeta_abs_x t - s0x) (zeta_abs_y t - s0y)
  / (dx * dx + dy * dy).

Theorem on_line_param : forall t,
  (dx, dy) <> (0, 0) ->
  zeta_qf t = 0 ->
  zeta_abs_x t = s0x + tj_of t * dx /\
  zeta_abs_y t = s0y + tj_of t * dy.
Proof.
  intros t Hd Hf.
  assert (Hdd : 0 < dx * dx + dy * dy).
  { destruct (Req_dec dx 0) as [->|Hx].
    - destruct (Req_dec dy 0) as [->|Hy]; [congruence|]. nra.
    - nra. }
  assert (Hc : crs dx dy (zeta_abs_x t - s0x) (zeta_abs_y t - s0y) = 0).
  { pose proof (line_chart_quadratic t) as E. rewrite Hf in E.
    assert (0 < 1 + t * t) by nra. nra. }
  unfold tj_of, dot.
  set (dd := dx * dx + dy * dy) in *.
  assert (EX : (zeta_abs_x t - s0x) * dd
             = (dx * (zeta_abs_x t - s0x) + dy * (zeta_abs_y t - s0y)) * dx
               - crs dx dy (zeta_abs_x t - s0x) (zeta_abs_y t - s0y) * dy)
    by (unfold dd, crs; ring).
  assert (EY : (zeta_abs_y t - s0y) * dd
             = (dx * (zeta_abs_x t - s0x) + dy * (zeta_abs_y t - s0y)) * dy
               + crs dx dy (zeta_abs_x t - s0x) (zeta_abs_y t - s0y) * dx)
    by (unfold dd, crs; ring).
  rewrite Hc in EX, EY.
  split.
  - apply (Rmult_eq_reg_r dd); [| lra].
    replace ((s0x + (dx * (zeta_abs_x t - s0x)
                      + dy * (zeta_abs_y t - s0y)) / dd * dx) * dd)
      with (s0x * dd
            + (dx * (zeta_abs_x t - s0x)
               + dy * (zeta_abs_y t - s0y)) * dx) by (field; lra).
    replace (zeta_abs_x t * dd)
      with ((zeta_abs_x t - s0x) * dd + s0x * dd) by ring.
    rewrite EX. ring.
  - apply (Rmult_eq_reg_r dd); [| lra].
    replace ((s0y + (dx * (zeta_abs_x t - s0x)
                      + dy * (zeta_abs_y t - s0y)) / dd * dy) * dd)
      with (s0y * dd
            + (dx * (zeta_abs_x t - s0x)
               + dy * (zeta_abs_y t - s0y)) * dy) by (field; lra).
    replace (zeta_abs_y t * dd)
      with ((zeta_abs_y t - s0y) * dd + s0y * dd) by ring.
    rewrite EY. ring.
Qed.

End ChartLine.

Print Assumptions line_chart_quadratic.
Print Assumptions disc_identity.
Print Assumptions on_line_param.
