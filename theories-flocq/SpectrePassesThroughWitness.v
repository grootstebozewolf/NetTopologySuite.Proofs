(* ============================================================================
   NetTopologySuite.Proofs.Flocq.SpectrePassesThroughWitness
   ----------------------------------------------------------------------------
   A WITNESS TEST of the on-grid passes-through machinery (C1 grid-exactness,
   PassesThrough_b64_grid_exact.v) on the SPECTRE aperiodic monotile -- the same
   hard, non-convex shape used as the point_in_ring regression anchor in
   theories/SpectreExample.v (docs/spectre-example.md).

   The R-side Spectre uses the rational hex embedding `(x + y/2, y)`.  Scaling by
   2 maps every vertex to INTEGER coordinates `(2x + y, 2y)` -- the same
   combinatorial polygon -- so the scaled vertices live on the binary64 integer
   grid `coord_int_safe`, exactly the regime the C1 grid theorems require.

   This file does two things, both Qed:
     1. discharges `bpoint_int_safe` for a real (2x-scaled) Spectre edge and two
        hot-pixel centres -- i.e. the C1 grid regime genuinely holds on a Spectre
        edge (via the reusable integer-to-binary64 builder `b64Z`); and
     2. exhibits the EXTRACTED compute filter's concrete verdicts on that edge by
        `vm_compute` (a through-pixel TRUE witness and a missed-pixel FALSE
        witness), then instantiates the conditional grid-exactness headline
        `b64_passes_through_grid_exact_cond` on the Spectre edge.

   Regression anchor, not a pipeline face.  No Admitted / Axiom / Parameter.
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra.
From Flocq Require Import IEEE754.Binary Core.

From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import B64_lib.
From NTS.Proofs.Flocq Require Import Orient_b64_exact.
From NTS.Proofs.Flocq Require Import HotPixel_b64.
From NTS.Proofs.Flocq Require Import PassesThrough_b64_compute.
From NTS.Proofs.Flocq Require Import PassesThrough_b64_grid_exact.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Reusable integer-to-binary64 builder (generalises b64_one / b64_two).       *)
(* -------------------------------------------------------------------------- *)
Definition b64Z (n : Z) : binary64 :=
  Binary.binary_normalize prec emax prec_gt_0_b64 prec_lt_emax_b64 mode_b64 n 0 false.

Lemma b64Z_B2R_finite :
  forall n : Z,
    (Z.abs n <= 2 ^ 25)%Z ->
    Binary.B2R prec emax (b64Z n) = IZR n
    /\ Binary.is_finite prec emax (b64Z n) = true.
Proof.
  intros n Hn.
  unfold b64Z.
  pose proof (Binary.binary_normalize_correct prec emax
                prec_gt_0_b64 prec_lt_emax_b64 mode_b64 n 0 false) as H.
  assert (HF2R : F2R (Float radix2 n 0) = IZR n).
  { unfold F2R, Fnum, Fexp. replace (bpow radix2 0) with 1%R by reflexivity. lra. }
  rewrite HF2R in H.
  rewrite (b64_round_IZR_exact n ltac:(unfold prec; lia)) in H.
  assert (Hbnd : Rabs (IZR n) < bpow radix2 emax).
  { rewrite <- abs_IZR.
    apply (Rle_lt_trans _ (bpow radix2 25)).
    - rewrite <- (IZR_Zpower radix2 25) by lia. apply IZR_le. exact Hn.
    - apply bpow_lt. unfold emax. lia. }
  apply Rlt_bool_true in Hbnd. rewrite Hbnd in H.
  destruct H as (HB2R & Hfin & _). split; assumption.
Qed.

Lemma b64Z_coord_int_safe :
  forall n : Z, (Z.abs n <= 2 ^ 25)%Z -> coord_int_safe (b64Z n).
Proof.
  intros n Hn. destruct (b64Z_B2R_finite n Hn) as [HR Hf].
  split; [ exact Hf | exists n; split; [ exact HR | exact Hn ] ].
Qed.

(* -------------------------------------------------------------------------- *)
(* A real Spectre edge, 2x-scaled to the integer grid.                         *)
(*                                                                            *)
(* Edge E5 of theories/SpectreExample.v's `spectre_ring`: the south-east edge *)
(* hpt 6 0 -- hpt 7 1 = (6,0)-(7.5,1) (the one the interior-point ray         *)
(* crosses).  Scaled by 2: (12,0)-(15,2).                                     *)
(* -------------------------------------------------------------------------- *)
Definition sP0 : BPoint := mkBP (b64Z 12) (b64Z 0).
Definition sP1 : BPoint := mkBP (b64Z 15) (b64Z 2).

(* Two hot-pixel centres on the integer grid:
   - sCthru = (13,1): the segment (12,0)-(15,2) enters this pixel for
     x in [12.75, 13.5] (y = (2/3)(x-12) in [0.5, 1]); and
   - sCmiss = (14,0): there the segment has y in [1, 5/3], outside [-1/2,1/2]. *)
Definition sCthru : BPoint := mkBP (b64Z 13) (b64Z 1).
Definition sCmiss : BPoint := mkBP (b64Z 14) (b64Z 0).

(* -------------------------------------------------------------------------- *)
(* (1) The C1 grid regime holds on the Spectre edge.                           *)
(* -------------------------------------------------------------------------- *)
Lemma sP0_safe : bpoint_int_safe sP0.
Proof. split; apply b64Z_coord_int_safe; lia. Qed.

Lemma sP1_safe : bpoint_int_safe sP1.
Proof. split; apply b64Z_coord_int_safe; lia. Qed.

Lemma sCthru_safe : bpoint_int_safe sCthru.
Proof. split; apply b64Z_coord_int_safe; lia. Qed.

Lemma sCmiss_safe : bpoint_int_safe sCmiss.
Proof. split; apply b64Z_coord_int_safe; lia. Qed.

(* -------------------------------------------------------------------------- *)
(* (2) The extracted compute filter's concrete verdicts on the Spectre edge.   *)
(*     These are the differential-oracle predicate run on real Spectre data.   *)
(* -------------------------------------------------------------------------- *)
Theorem spectre_edge_passes_thru :
  b64_passes_through_hot_pixel_compute sP0 sP1 sCthru = true.
Proof. vm_compute. reflexivity. Qed.

Theorem spectre_edge_misses :
  b64_passes_through_hot_pixel_compute sP0 sP1 sCmiss = false.
Proof. vm_compute. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* (3) The conditional grid-exactness headline, instantiated on the Spectre    *)
(* edge: on this real shape the rounded compute filter equals the exact R-spec *)
(* under the single named clip-comparison reflection (Slice 10).  Combined     *)
(* with (2), the exact spec's verdict on the Spectre edge is pinned modulo     *)
(* that one hypothesis.                                                         *)
(* -------------------------------------------------------------------------- *)
Theorem spectre_edge_grid_exact_cond :
  (Rle_bool (b64_round (tmin_exact sP0 sP1 sCthru)) (b64_round (tmax_exact sP0 sP1 sCthru))
     = Rle_bool (tmin_exact sP0 sP1 sCthru) (tmax_exact sP0 sP1 sCthru)) ->
  b64_passes_through_hot_pixel_compute sP0 sP1 sCthru
    = b64_passes_through_hot_pixel sP0 sP1 sCthru.
Proof.
  apply b64_passes_through_grid_exact_cond.
  - exact sP0_safe.
  - exact sP1_safe.
  - exact sCthru_safe.
Qed.

(* Spelled out: under the reflection, the exact R-spec passes-through verdict on
   the Spectre edge at the through-pixel is TRUE (transported from the compute
   witness (2) through (3)). *)
Corollary spectre_edge_spec_passes_thru :
  (Rle_bool (b64_round (tmin_exact sP0 sP1 sCthru)) (b64_round (tmax_exact sP0 sP1 sCthru))
     = Rle_bool (tmin_exact sP0 sP1 sCthru) (tmax_exact sP0 sP1 sCthru)) ->
  b64_passes_through_hot_pixel sP0 sP1 sCthru = true.
Proof.
  intro Href.
  rewrite <- (spectre_edge_grid_exact_cond Href).
  exact spectre_edge_passes_thru.
Qed.
