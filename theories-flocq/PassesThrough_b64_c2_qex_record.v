(* ============================================================================
   NetTopologySuite.Proofs.Flocq.PassesThrough_b64_c2_qex_record
   ----------------------------------------------------------------------------
   QEX record for the implementation-level C2 question
         C2 preconditions  ->  b64_result = exact_geometric_result.
   (docs/c2-implementation-qex-2026-11.md)

   The C2 decision is the comparison  tlo_x <= thi_y  of two Liang-Barsky
   quotients a_x/b_x and a_y/b_y.  Cross-multiplying, the exact determinant is
        D = a_x * b_y - a_y * b_x          (sign D = sign (tlo_x - thi_y) up to
                                            the sign of b_x b_y),
   and the binary64 implementation realises it as  Dhat = that_x - that_y  (the
   real interpretation of the two computed `b64_div` results compared by b64_le).

   This file proves, for the C2 witness of PassesThrough_b64_c2_counterexample:
     * it satisfies the corpus's own off-grid domain predicates (finite,
       |c| <= 2^500 = `b64_coord_safe`; non-degenerate axes) and is off-grid
       (`~ coord_int_safe`);
     * D = 0 exactly (corner tangency);
     * Dhat = 2^-56 > 0;
     * hence sign Dhat <> sign D, and |D| > E is IMPOSSIBLE for every E >= 0;
     * spec = true and compute = false: the implementation result differs from
       the exact geometric result.
   No Admitted.
   ========================================================================== *)
From Stdlib Require Import Reals ZArith Lra Lia.
From Flocq Require Import IEEE754.Binary IEEE754.BinarySingleNaN Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge HotPixel_b64
  PassesThrough_b64_compute Orient_b64_exact PassesThrough_b64_c2_counterexample
  PassesThrough_b64_conservative PassesThrough_b64_conservative_replay.
Local Open Scope R_scope.
Local Notation B2R := (Binary.B2R prec emax).

(* --- the intended C2 preconditions hold ---------------------------------- *)
Lemma c2_witness_coords_safe :
  b64_coord_safe c2_x0 /\ b64_coord_safe c2_y0 /\ b64_coord_safe c2_x1 /\
  b64_coord_safe c2_y1 /\ b64_coord_safe c2_cx /\ b64_coord_safe c2_cy.
Proof.
  assert (D : forall v, b64_dom v = true -> b64_coord_safe v).
  { intros v H. destruct (dom_ok _ H) as [F Hb]. split; [exact F|]. exact Hb. }
  destruct c2_in_domain as (a & b & c & d & e & f).
  repeat split; apply D; assumption.
Qed.

Lemma c2_witness_nondegenerate :
  B2R c2_x1 <> B2R c2_x0 /\ B2R c2_y1 <> B2R c2_y0.
Proof.
  rewrite v_x1, v_x0, v_y1, v_y0. split; intro H; lra.
Qed.

(* Off the grid: the corpus's integer-grid predicate FAILS on four coordinates. *)
Lemma c2_witness_off_grid :
  ~ coord_int_safe c2_x0 /\ ~ coord_int_safe c2_y0 /\
  ~ coord_int_safe c2_x1 /\ ~ coord_int_safe c2_y1.
Proof.
  repeat split; intros [_ [n [Hn _]]].
  - rewrite v_x0 in Hn.
    assert (E : (n * 562949953421312 = -1888912008722237)%Z)
      by (apply eq_IZR; rewrite mult_IZR; lra).
    lia.
  - rewrite v_y0 in Hn.
    assert (E : (n * 549755813888 = 839343893073)%Z)
      by (apply eq_IZR; rewrite mult_IZR; lra).
    lia.
  - rewrite v_x1 in Hn.
    assert (E : (n * 70368744177664 = 2205571357521725)%Z)
      by (apply eq_IZR; rewrite mult_IZR; lra).
    lia.
  - rewrite v_y1 in Hn.
    assert (E : (n * 68719476736 = -1148581538385)%Z)
      by (apply eq_IZR; rewrite mult_IZR; lra).
    lia.
Qed.

(* --- exact determinant and the computed real value ------------------------ *)
(* D = a_x b_y - a_y b_x, a = (pixel lower edge) - c0, b = c1 - c0, per axis. *)
Definition c2_D : R :=
  ((B2R c2_cx - / 2) - B2R c2_x0) * (B2R c2_y1 - B2R c2_y0)
  - ((B2R c2_cy - / 2) - B2R c2_y0) * (B2R c2_x1 - B2R c2_x0).

(* Dhat = that_x - that_y : the real interpretation of the two b64_div results
   (lit_tx, lit_ty are the values of b64_lb_tlo on x and b64_lb_thi on y;
   identified with the actual compute path by c2_report_x_axis / _y_axis). *)
Definition c2_Dhat : R := B2R lit_tx - B2R lit_ty.

Lemma c2_exact_D_zero : c2_D = 0.
Proof.
  unfold c2_D. rewrite v_cx, v_x0, v_y1, v_y0, v_cy, v_x1. lra.
Qed.

Lemma c2_Dhat_value : c2_Dhat = / 72057594037927936.
Proof. unfold c2_Dhat. rewrite val_tx, val_ty. lra. Qed.

Lemma c2_sign_mismatch :
  Rcompare c2_D 0 = Eq /\ Rcompare c2_Dhat 0 = Gt.
Proof.
  split.
  - rewrite c2_exact_D_zero. apply Rcompare_Eq. reflexivity.
  - rewrite c2_Dhat_value. apply Rcompare_Gt.
    apply Rinv_0_lt_compat. lra.
Qed.

(* The forward error is perfectly small (one ulp) ... *)
Lemma c2_forward_error : Rabs (c2_Dhat - c2_D) = / 72057594037927936.
Proof.
  rewrite c2_exact_D_zero, c2_Dhat_value, Rminus_0_r.
  apply Rabs_right. apply Rle_ge, Rlt_le, Rinv_0_lt_compat. lra.
Qed.

(* ... but the separation |D| > E is impossible for EVERY E >= 0, because D = 0
   (the tangent case the specification accepts with equality). *)
Lemma c2_separation_impossible : forall E : R, 0 <= E -> ~ (E < Rabs c2_D).
Proof.
  intros E HE H. rewrite c2_exact_D_zero, Rabs_R0 in H. lra.
Qed.

(* --- the implementation-level QEX ---------------------------------------- *)
Theorem c2_implementation_qex :
  (* preconditions: finite, |c| <= 2^500, non-degenerate axes, off-grid *)
  (b64_coord_safe c2_x0 /\ b64_coord_safe c2_y0 /\ b64_coord_safe c2_x1 /\
   b64_coord_safe c2_y1 /\ b64_coord_safe c2_cx /\ b64_coord_safe c2_cy) /\
  (B2R c2_x1 <> B2R c2_x0 /\ B2R c2_y1 <> B2R c2_y0) /\
  (~ coord_int_safe c2_x0 /\ ~ coord_int_safe c2_y0 /\
   ~ coord_int_safe c2_x1 /\ ~ coord_int_safe c2_y1) /\
  (* exact geometry accepts, implementation rejects *)
  b64_passes_through_hot_pixel c2P0 c2P1 c2C = true /\
  b64_passes_through_hot_pixel_compute c2P0 c2P1 c2C = false /\
  (* the determinant picture of the same failure *)
  c2_D = 0 /\ c2_Dhat = / 72057594037927936 /\
  Rcompare c2_Dhat 0 <> Rcompare c2_D 0.
Proof.
  refine (conj c2_witness_coords_safe (conj c2_witness_nondegenerate
          (conj c2_witness_off_grid (conj c2_spec_true (conj c2_compute_false
          (conj c2_exact_D_zero (conj c2_Dhat_value _))))))).
  destruct c2_sign_mismatch as [E1 E2]. rewrite E1, E2. discriminate.
Qed.

(* Hence the implementation-level equality fails off the grid. *)
Corollary c2_result_equality_false :
  ~ (forall P0 P1 C : BPoint,
       b64_coord_safe (bx P0) -> b64_coord_safe (by_ P0) ->
       b64_coord_safe (bx P1) -> b64_coord_safe (by_ P1) ->
       b64_coord_safe (bx C) -> b64_coord_safe (by_ C) ->
       b64_passes_through_hot_pixel_compute P0 P1 C
       = b64_passes_through_hot_pixel P0 P1 C).
Proof.
  intro H.
  destruct c2_witness_coords_safe as (a & b & c & d & e & f).
  pose proof (H c2P0 c2P1 c2C a b c d e f) as H1.
  rewrite c2_compute_false, c2_spec_true in H1. discriminate.
Qed.

Print Assumptions c2_implementation_qex.
Print Assumptions c2_result_equality_false.
Print Assumptions c2_separation_impossible.
Print Assumptions c2_witness_off_grid.
