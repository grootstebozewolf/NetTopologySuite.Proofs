(* ============================================================================
   NetTopologySuite.Proofs.Flocq.PassesThrough_b64_spec_symmetric
   ----------------------------------------------------------------------------
   GREEN companion to PassesThrough_b64_compute_asymmetric.v.

   That file proves the ROUNDED `_compute` passes-through filter is NOT
   symmetric under segment reversal P0<->P1 (the order-dependent-noding defect
   behind JTS#752 / JTS#1133).  THIS file proves the EXACT R-spec filter IS
   symmetric -- so the order-safe noder primitive is the spec, not the rounded
   compute filter.  Same statement shape, opposite (and correct) verdict:

     b64_passes_through_hot_pixel P0 P1 C = b64_passes_through_hot_pixel P1 P0 C.

   Mathematics.  A segment is the unordered pair {P0,P1}; reversing it is the
   reparametrisation t |-> 1-t, which maps the Liang-Barsky clipped parameter
   interval [tlo,thi] to [1-thi,1-tlo].  Concretely, with c1 <> c0,
     (lo - c1)/(c0 - c1) = 1 - (lo - c0)/(c1 - c0),
   so the per-axis bounds swap as  lb_tlo c1 c0 = 1 - lb_thi c0 c1  and
   lb_thi c1 c0 = 1 - lb_tlo c0 c1 (the degenerate axis-parallel case gives
   0/1, for which the identity still holds).  The clipped-interval-nonempty
   test  max 0 (...tlo...) <= min 1 (...thi...)  is invariant under t |-> 1-t,
   and the slab guard lb_inslab is visibly symmetric.  No rounding enters the
   R-spec, so unlike the rounded filter the symmetry is exact.  Refs #66.
   ========================================================================== *)

From Flocq Require Import Core.
Require Import Reals.
Require Import Lra.
From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import HotPixel_b64.
Local Open Scope R_scope.

(* Flipping both arguments by 1 - x reverses a <= comparison: a boolean fact. *)
Lemma Rle_bool_flip : forall A B : R, Rle_bool (1 - B) (1 - A) = Rle_bool A B.
Proof.
  intros A B. destruct (Rle_bool_spec A B) as [H|H].
  - apply Rle_bool_true; lra.
  - apply Rle_bool_false; lra.
Qed.

(* The slab guard is symmetric under endpoint swap. *)
Lemma lb_inslab_sym : forall c0 c1 lo hi : R,
  lb_inslab c0 c1 lo hi = lb_inslab c1 c0 lo hi.
Proof.
  intros c0 c1 lo hi. unfold lb_inslab.
  destruct (Req_dec_T c1 c0) as [E|E]; destruct (Req_dec_T c0 c1) as [E2|E2].
  - rewrite E. reflexivity.
  - exfalso; apply E2; symmetry; exact E.
  - exfalso; apply E; symmetry; exact E2.
  - reflexivity.
Qed.

(* Per-axis t-bounds swap as t |-> 1 - t (the reparametrisation). *)
Lemma lb_tlo_swap : forall c0 c1 lo hi : R,
  lb_tlo c1 c0 lo hi = 1 - lb_thi c0 c1 lo hi.
Proof.
  intros c0 c1 lo hi. unfold lb_tlo, lb_thi.
  destruct (Req_dec_T c0 c1) as [E|E]; destruct (Req_dec_T c1 c0) as [E2|E2].
  - lra.
  - exfalso; apply E2; symmetry; exact E.
  - exfalso; apply E; symmetry; exact E2.
  - assert (A1 : (lo - c1) / (c0 - c1) = 1 - (lo - c0) / (c1 - c0)) by (field; lra).
    assert (A2 : (hi - c1) / (c0 - c1) = 1 - (hi - c0) / (c1 - c0)) by (field; lra).
    rewrite A1, A2. unfold Rmin, Rmax.
    repeat destruct (Rle_dec _ _); lra.
Qed.

Lemma lb_thi_swap : forall c0 c1 lo hi : R,
  lb_thi c1 c0 lo hi = 1 - lb_tlo c0 c1 lo hi.
Proof.
  intros c0 c1 lo hi. unfold lb_tlo, lb_thi.
  destruct (Req_dec_T c0 c1) as [E|E]; destruct (Req_dec_T c1 c0) as [E2|E2].
  - lra.
  - exfalso; apply E2; symmetry; exact E.
  - exfalso; apply E; symmetry; exact E2.
  - assert (A1 : (lo - c1) / (c0 - c1) = 1 - (lo - c0) / (c1 - c0)) by (field; lra).
    assert (A2 : (hi - c1) / (c0 - c1) = 1 - (hi - c0) / (c1 - c0)) by (field; lra).
    rewrite A1, A2. unfold Rmin, Rmax.
    repeat destruct (Rle_dec _ _); lra.
Qed.

(* The clipped-interval test is invariant under t |-> 1 - t on both axes. *)
Lemma clip_flip : forall TloX TloY ThiX ThiY : R,
  Rle_bool (Rmax 0 (Rmax TloX TloY)) (Rmin 1 (Rmin ThiX ThiY))
  = Rle_bool (Rmax 0 (Rmax (1 - ThiX) (1 - ThiY)))
             (Rmin 1 (Rmin (1 - TloX) (1 - TloY))).
Proof.
  intros TloX TloY ThiX ThiY.
  assert (Ha : Rmax 0 (Rmax (1 - ThiX) (1 - ThiY)) = 1 - Rmin 1 (Rmin ThiX ThiY)).
  { unfold Rmin, Rmax. repeat destruct (Rle_dec _ _); lra. }
  assert (Hb : Rmin 1 (Rmin (1 - TloX) (1 - TloY)) = 1 - Rmax 0 (Rmax TloX TloY)).
  { unfold Rmin, Rmax. repeat destruct (Rle_dec _ _); lra. }
  rewrite Ha, Hb, Rle_bool_flip. reflexivity.
Qed.

(* The exact-real Liang-Barsky touch is symmetric under endpoint swap. *)
Lemma b64_liang_barsky_touches_sym : forall P0 P1 C : BPoint,
  b64_liang_barsky_touches P0 P1 C = b64_liang_barsky_touches P1 P0 C.
Proof.
  intros P0 P1 C. unfold b64_liang_barsky_touches.
  rewrite (lb_inslab_sym (Binary.B2R prec emax (bx P0)) (Binary.B2R prec emax (bx P1))).
  rewrite (lb_inslab_sym (Binary.B2R prec emax (by_ P0)) (Binary.B2R prec emax (by_ P1))).
  rewrite (lb_tlo_swap (Binary.B2R prec emax (bx P0)) (Binary.B2R prec emax (bx P1))).
  rewrite (lb_tlo_swap (Binary.B2R prec emax (by_ P0)) (Binary.B2R prec emax (by_ P1))).
  rewrite (lb_thi_swap (Binary.B2R prec emax (bx P0)) (Binary.B2R prec emax (bx P1))).
  rewrite (lb_thi_swap (Binary.B2R prec emax (by_ P0)) (Binary.B2R prec emax (by_ P1))).
  rewrite clip_flip. reflexivity.
Qed.

(* Headline: the exact passes-through R-spec (touch on original AND snapped
   segment) is order-independent -- the property the rounded filter loses. *)
Theorem b64_passes_through_hot_pixel_symmetric : forall P0 P1 C : BPoint,
  b64_passes_through_hot_pixel P0 P1 C = b64_passes_through_hot_pixel P1 P0 C.
Proof.
  intros P0 P1 C. unfold b64_passes_through_hot_pixel.
  rewrite (b64_liang_barsky_touches_sym P0 P1 C).
  rewrite (b64_liang_barsky_touches_sym (b64_snap P0) (b64_snap P1) C).
  reflexivity.
Qed.

Print Assumptions b64_passes_through_hot_pixel_symmetric.
