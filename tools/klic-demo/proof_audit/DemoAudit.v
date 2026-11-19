(* Audit probe for tools/klic-demo: run tools/klic-demo/proof_audit/audit.sh *)
From NTS.Proofs.Flocq Require Import HotPixel_b64 NodingSeparation_b64 SnapRoundingScale_b64 HotPixel_Q_exec.
Print Assumptions q_round_ne_correct.
Print Assumptions q_snap_coord_correct.
Print Assumptions q_snap_correct.
Print Assumptions snap_round_coord_tolerance_scale.
Print Assumptions q_snap_disp_bound.
Print Assumptions q_touches_closed_reflect.
Print Assumptions q_passes_through_closed_reflect.
Print Assumptions q_seg_intersection_sound.
Print Assumptions q_snap_coord_unit_integer.
Print Assumptions rd_mm_grid_representable_b64.
Print Assumptions b64_snap_coord_Q_agree.
Print Assumptions b64_passes_through_implies_q.
Print Assumptions snap_round_preserves_passes_through_scale.
Print Assumptions snap_round_x_tol.
Print Assumptions snap_round_y_tol.
Print Assumptions b64_passes_through_sound.
Print Assumptions b64_passes_through_complete.
Print Assumptions b64_liang_barsky_sound_closed.
Print Assumptions b64_liang_barsky_complete.
