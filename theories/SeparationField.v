(* ============================================================================
   NetTopologySuite.Proofs.SeparationField
   ----------------------------------------------------------------------------
   The IVT separation engine, abstracted from the rectangle case (slice 3a).

   The rectangle separation (theories/RectangleSeparation.v) showed that a
   single continuous scalar field that is >0 inside, =0 exactly on the edge
   skeleton, and <0 outside lets the intermediate value theorem confine any
   complement-connected path to the interior.  Nothing in that argument is
   special to a rectangle.  This module extracts the reusable engine:

     separation_via_field : a continuous `phi : Point -> R` that is nonzero off
       the ring skeleton and whose positive region is bounded, with `phi p > 0`,
       forces `in_bounded_component_cont r p`.

   Any future ring family (convex polygons, tilted boxes, ...) discharges its
   bounded-component obligation by supplying such a field -- for convex
   polygons, the min over edges of the inward signed distance, exactly as
   `box_min` is the four-slab min for the axis-aligned box.  We re-derive the
   rectangle instance (`rect_in_bounded_component`) through the engine as a
   sanity check / usage example.

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (claude-opus-4-8)
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From Stdlib Require Import Ranalysis Ranalysis5.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam.
From NTS.Proofs Require Import RectangleJCT RectangleSeparation.

Local Open Scope R_scope.

(* A scalar field is "continuous along paths" if composing it with any
   continuous path yields a (pointwise) continuous real function. *)
Definition field_continuous_along_paths (phi : Point -> R) : Prop :=
  forall g : R -> Point,
    continuity (fun s => px (g s)) ->
    continuity (fun s => py (g s)) ->
    forall t, continuity_pt (fun s => phi (g s)) t.

(* -------------------------------------------------------------------------- *)
(* The engine: a separating, bounded-positive field traps the interior.        *)
(* -------------------------------------------------------------------------- *)

Theorem separation_via_field :
  forall (r : Ring) (phi : Point -> R) (p : Point) (M : R),
    field_continuous_along_paths phi ->
    (forall pt, ring_complement r pt -> phi pt <> 0) ->   (* nonzero off skeleton *)
    0 < phi p ->                                          (* p is interior      *)
    0 < M ->
    (forall pt, 0 < phi pt -> px pt * px pt + py pt * py pt <= M * M) ->
                                                          (* positive region bounded *)
    in_bounded_component_cont r p.
Proof.
  intros r phi p M Hcont Hnz Hp0 HM Hbound.
  exists M; split; [ exact HM | ].
  intros q Hconn.
  destruct Hconn as [g [[Hcx Hcy] [Hg0 [Hg1 Hcompl]]]].
  set (F := fun t => phi (g t)).
  assert (HcF : forall a, continuity_pt F a) by (intro a; apply Hcont; assumption).
  assert (HF0 : 0 < F 0) by (unfold F; rewrite Hg0; exact Hp0).
  assert (Hnz' : forall t, 0 <= t <= 1 -> F t <> 0)
    by (intros t Ht; unfold F; apply Hnz; apply Hcompl; exact Ht).
  (* No sign change without a zero: F stays positive to the endpoint. *)
  assert (HF1 : 0 < F 1).
  { destruct (Rtotal_order (F 1) 0) as [Hlt | [Heq | Hgt]].
    - assert (Hc' : forall a, 0 <= a <= 1 -> continuity_pt (fun t => - F t) a)
        by (intros a _; apply continuity_pt_opp; apply HcF).
      destruct (IVT_interv (fun t => - F t) 0 1 Hc' Rlt_0_1) as [z [Hz Hzeq]];
        [ simpl; lra | simpl; lra | ].
      exfalso; apply (Hnz' z Hz); lra.
    - exfalso; apply (Hnz' 1 ltac:(lra)); exact Heq.
    - exact Hgt. }
  unfold F in HF1; rewrite Hg1 in HF1.
  apply Hbound; exact HF1.
Qed.

(* -------------------------------------------------------------------------- *)
(* Instance: the axis-aligned rectangle, via box_min -- demonstrates the engine *)
(* (an independent route to RectangleSeparation's bounded-component result).    *)
(* -------------------------------------------------------------------------- *)

Theorem rect_in_bounded_component : forall x0 y0 x1 y1 p,
  x0 < x1 -> y0 < y1 ->
  x0 < px p < x1 -> y0 < py p < y1 ->
  in_bounded_component_cont (rect_ring x0 y0 x1 y1) p.
Proof.
  intros x0 y0 x1 y1 p Hx01 Hy01 Hxp Hyp.
  assert (Hx2 : 0 <= Rmax (x0 * x0) (x1 * x1))
    by (apply Rle_trans with (x0 * x0); [ nra | apply Rmax_l ]).
  assert (Hy2 : 0 <= Rmax (y0 * y0) (y1 * y1))
    by (apply Rle_trans with (y0 * y0); [ nra | apply Rmax_l ]).
  apply (separation_via_field (rect_ring x0 y0 x1 y1) (box_min x0 y0 x1 y1) p
           (sqrt (Rmax (x0 * x0) (x1 * x1) + Rmax (y0 * y0) (y1 * y1) + 1))).
  - intros g Hcx Hcy t. apply continuity_pt_box_min_path; [ apply Hcx | apply Hcy ].
  - intros pt Hc. apply box_min_nonzero_off_skeleton; [ exact Hx01 | exact Hy01 | exact Hc ].
  - apply box_min_pos_iff; split; assumption.
  - apply sqrt_lt_R0; lra.
  - intros pt Hpos. apply box_min_pos_iff in Hpos.
    destruct Hpos as [[Hax Hbx] [Hay Hby]].
    assert (HMM : sqrt (Rmax (x0 * x0) (x1 * x1) + Rmax (y0 * y0) (y1 * y1) + 1)
                * sqrt (Rmax (x0 * x0) (x1 * x1) + Rmax (y0 * y0) (y1 * y1) + 1)
                = Rmax (x0 * x0) (x1 * x1) + Rmax (y0 * y0) (y1 * y1) + 1)
      by (apply sqrt_sqrt; lra).
    rewrite HMM.
    pose proof (sq_le_max_endpoints (px pt) x0 x1 ltac:(lra)) as Hpx2.
    pose proof (sq_le_max_endpoints (py pt) y0 y1 ltac:(lra)) as Hpy2.
    lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions separation_via_field.
Print Assumptions rect_in_bounded_component.
