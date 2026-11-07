(* ============================================================================
   NetTopologySuite.Proofs.Flocq.PassesThrough_b64_executable_replay
   ----------------------------------------------------------------------------
   Replay of the C2 counterexample through the EXECUTABLE conservative filter
   (nearest operation + pred/succ).  The original round-to-nearest compute still
   rejects the witness; the executable repair accepts it, and its outward bounds
   enclose the exact value 1/9 and are at least as wide as the Flocq-mode
   reference bounds.  No Admitted.
   ========================================================================== *)
From Stdlib Require Import Reals ZArith Lra Lia.
From Flocq Require Import IEEE754.Binary IEEE754.BinarySingleNaN Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 HotPixel_b64
  PassesThrough_b64_compute PassesThrough_b64_c2_counterexample
  PassesThrough_b64_conservative PassesThrough_b64_conservative_replay
  PassesThrough_b64_executable.
Local Open Scope R_scope.
Local Notation B2R := (Binary.B2R prec emax).

Theorem c2_exec_accepts_witness :
  b64_passes_through_hot_pixel c2P0 c2P1 c2C = true /\
  b64_passes_through_hot_pixel_compute c2P0 c2P1 c2C = false /\
  b64_passes_through_hot_pixel_exec c2P0 c2P1 c2C = true.
Proof.
  split; [exact c2_spec_true|]. split; [exact c2_compute_false|].
  vm_compute. reflexivity.
Qed.

Corollary c2_exec_accepts_witness_by_theorem :
  b64_passes_through_hot_pixel_exec c2P0 c2P1 c2C = true.
Proof. exact (b64_passes_through_complete_exec _ _ _ c2_spec_true). Qed.

(* Polarity at the witness for the executable bounds: computed lower <= 1/9 <=
   computed upper, so the executable interval is nonempty. *)
Theorem c2_exec_polarity_at_witness :
  exists lo hi : binary64,
    g_axis_lo exec_prims c2_x0 c2_x1 c2_cx = Some lo /\
    g_axis_hi exec_prims c2_y0 c2_y1 c2_cy = Some hi /\
    Binary.is_finite prec emax lo = true /\ Binary.is_finite prec emax hi = true /\
    B2R lo <= 1 / 9 /\ 1 / 9 <= B2R hi /\ b64_le lo hi = true.
Proof.
  destruct c2_in_domain as (Dx0 & Dy0 & Dx1 & Dy1 & Dcx & Dcy).
  destruct (dom_ok _ Dx0) as [Fx0 Hx0]. destruct (dom_ok _ Dx1) as [Fx1 Hx1].
  destruct (dom_ok _ Dcx) as [Fcx Hcx]. destruct (dom_ok _ Dy0) as [Fy0 Hy0].
  destruct (dom_ok _ Dy1) as [Fy1 Hy1]. destruct (dom_ok _ Dcy) as [Fcy Hcy].
  assert (Elo : exists lo, g_axis_lo exec_prims c2_x0 c2_x1 c2_cx = Some lo)
    by (vm_compute; eexists; reflexivity).
  assert (Ehi : exists hi, g_axis_hi exec_prims c2_y0 c2_y1 c2_cy = Some hi)
    by (vm_compute; eexists; reflexivity).
  destruct Elo as [lo Elo]. destruct Ehi as [hi Ehi].
  pose proof (g_axis_lo_ok exec_prims _ _ _ Fx0 Fx1 Fcx Hx0 Hx1 Hcx) as L.
  pose proof (g_axis_hi_ok exec_prims _ _ _ Fy0 Fy1 Fcy Hy0 Hy1 Hcy) as U.
  rewrite Elo in L. rewrite Ehi in U.
  destruct L as [Fl Hl]. destruct U as [Fh Hh].
  rewrite exact_tlo_x_is_ninth in Hl. rewrite exact_thi_y_is_ninth in Hh.
  exists lo, hi. repeat split; try assumption.
  apply b64_le_complete; [exact Fl | exact Fh | lra].
Qed.

(* The executable bounds are at least as wide as the Flocq-mode reference. *)
Definition get_or_zero (o : option binary64) : binary64 :=
  match o with Some v => v | None => b64_zero end.

Theorem c2_exec_wider_than_reference :
  b64_le (get_or_zero (g_axis_lo exec_prims c2_x0 c2_x1 c2_cx))
         (get_or_zero (axis_lo c2_x0 c2_x1 c2_cx)) = true /\
  b64_le (get_or_zero (axis_hi c2_y0 c2_y1 c2_cy))
         (get_or_zero (g_axis_hi exec_prims c2_y0 c2_y1 c2_cy)) = true.
Proof. split; vm_compute; reflexivity. Qed.

Print Assumptions c2_exec_accepts_witness.
Print Assumptions c2_exec_polarity_at_witness.
Print Assumptions c2_exec_wider_than_reference.
