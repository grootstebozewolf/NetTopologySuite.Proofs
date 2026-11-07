(* ============================================================================
   NetTopologySuite.Proofs.Flocq.PassesThrough_b64_conservative_replay
   ----------------------------------------------------------------------------
   Replay of the C2 counterexample (PassesThrough_b64_c2_counterexample.v) against
   the conservative repair (PassesThrough_b64_conservative.v).

   Witness: the exact t-bounds are tlo_x = thi_y = 1/9 (corner tangency).  The old
   round-to-nearest filter inverts them by one ulp and REJECTS.  The repair
   computes outward bounds  lo_x <= 1/9 <= hi_y  (lower bound rounded DOWN, upper
   bound rounded UP, through the whole subtraction/division path), so its
   interval  [lo_x, hi_y]  is nonempty and the touch is ACCEPTED.
   No Admitted.
   ========================================================================== *)
From Stdlib Require Import Reals ZArith Lra Lia.
From Flocq Require Import IEEE754.Binary IEEE754.BinarySingleNaN Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 HotPixel_b64
  PassesThrough_b64_compute PassesThrough_b64_c2_counterexample
  PassesThrough_b64_conservative.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).

(* Headline: old filter rejects, spec accepts, repair accepts. *)
Theorem c2_repair_accepts_witness :
  b64_passes_through_hot_pixel c2P0 c2P1 c2C = true /\
  b64_passes_through_hot_pixel_compute c2P0 c2P1 c2C = false /\
  b64_passes_through_hot_pixel_cons c2P0 c2P1 c2C = true.
Proof.
  split; [exact c2_spec_true|]. split; [exact c2_compute_false|].
  vm_compute. reflexivity.
Qed.

(* The same acceptance, via the general completeness theorem. *)
Corollary c2_repair_accepts_witness_by_theorem :
  b64_passes_through_hot_pixel_cons c2P0 c2P1 c2C = true.
Proof. exact (b64_passes_through_complete_cons _ _ _ c2_spec_true). Qed.

(* The exact bounds are 1/9 on both axes ... *)
Lemma exact_tlo_x_is_ninth :
  lb_tlo (B2R c2_x0) (B2R c2_x1) (B2R c2_cx - / 2) (B2R c2_cx + / 2) = 1 / 9.
Proof.
  rewrite v_x0, v_x1, v_cx.
  unfold lb_tlo. destruct (Req_dec_T _ _) as [E|_]; [exfalso; lra|].
  unfold Rmin. repeat destruct (Rle_dec _ _); lra.
Qed.

Lemma exact_thi_y_is_ninth :
  lb_thi (B2R c2_y0) (B2R c2_y1) (B2R c2_cy - / 2) (B2R c2_cy + / 2) = 1 / 9.
Proof.
  rewrite v_y0, v_y1, v_cy.
  unfold lb_thi. destruct (Req_dec_T _ _) as [E|_]; [exfalso; lra|].
  unfold Rmax. repeat destruct (Rle_dec _ _); lra.
Qed.

Lemma c2_in_domain :
  b64_dom c2_x0 = true /\ b64_dom c2_y0 = true /\ b64_dom c2_x1 = true /\
  b64_dom c2_y1 = true /\ b64_dom c2_cx = true /\ b64_dom c2_cy = true.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ... and the repair's outward bounds enclose 1/9 with the correct polarity:
   computed lower <= exact lower = 1/9 = exact upper <= computed upper. *)
Theorem c2_repair_polarity_at_witness :
  exists lo hi : binary64,
    axis_lo c2_x0 c2_x1 c2_cx = Some lo /\
    axis_hi c2_y0 c2_y1 c2_cy = Some hi /\
    Binary.is_finite prec emax lo = true /\ Binary.is_finite prec emax hi = true /\
    B2R lo <= 1 / 9 /\ 1 / 9 <= B2R hi /\ b64_le lo hi = true.
Proof.
  destruct c2_in_domain as (Dx0 & Dy0 & Dx1 & Dy1 & Dcx & Dcy).
  destruct (dom_ok _ Dx0) as [Fx0 Hx0]. destruct (dom_ok _ Dx1) as [Fx1 Hx1].
  destruct (dom_ok _ Dcx) as [Fcx Hcx]. destruct (dom_ok _ Dy0) as [Fy0 Hy0].
  destruct (dom_ok _ Dy1) as [Fy1 Hy1]. destruct (dom_ok _ Dcy) as [Fcy Hcy].
  assert (Elo : exists lo, axis_lo c2_x0 c2_x1 c2_cx = Some lo)
    by (vm_compute; eexists; reflexivity).
  assert (Ehi : exists hi, axis_hi c2_y0 c2_y1 c2_cy = Some hi)
    by (vm_compute; eexists; reflexivity).
  destruct Elo as [lo Elo]. destruct Ehi as [hi Ehi].
  pose proof (axis_lo_ok _ _ _ Fx0 Fx1 Fcx Hx0 Hx1 Hcx) as L.
  pose proof (axis_hi_ok _ _ _ Fy0 Fy1 Fcy Hy0 Hy1 Hcy) as U.
  rewrite Elo in L. rewrite Ehi in U.
  destruct L as [Fl Hl]. destruct U as [Fh Hh].
  rewrite exact_tlo_x_is_ninth in Hl. rewrite exact_thi_y_is_ninth in Hh.
  exists lo, hi. repeat split; try assumption.
  apply b64_le_complete; [exact Fl | exact Fh | lra].
Qed.

Print Assumptions c2_repair_accepts_witness.
Print Assumptions c2_repair_accepts_witness_by_theorem.
Print Assumptions c2_repair_polarity_at_witness.
