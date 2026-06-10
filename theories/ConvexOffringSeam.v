(* ============================================================================
   NetTopologySuite.Proofs.ConvexOffringSeam
   ----------------------------------------------------------------------------
   The generic CONVEX assembly layer for the corrected off-ring H1 seam, and
   the right triangle as the THIRD total family (free, via the general
   triangle).

   `ConvexField.v` provides the separation engine for a half-plane-presented
   ring (`conv_min`, `convex_separation`).  What it lacks is everything else a
   total seam instance needs.  This file adds the generic pieces, each proved
   ONCE for an arbitrary ring + half-plane presentation:

     - `ring_edges_endpoints_in`     : edge endpoints are ring vertices;
     - `image_slack_nonneg`          : if all VERTICES satisfy a half-plane,
       the whole skeleton does (each edge point is a convex combination and
       the slack is affine) -- the n-gon induction that replaced the
       per-family `gtri_image_slacks_nonneg` / `rect_image_bounds`;
     - `conv_min_neg_inv`            : a negative field names a violated
       half-plane (list induction over Rmin);
     - `convex_exterior_escapes`     : a point strictly beyond a vertex-
       satisfied half-plane escapes (instantiates `escape_beyond_halfplane`);
     - `convex_parity_seam_offring_of` : THE ASSEMBLY -- for any ring with a
       half-plane presentation, the total off-ring seam follows from exactly
       four named family obligations: the zero set of `conv_min` lies on the
       skeleton, the positive region is bounded, and the two guarded parity
       facts (interior odd, exterior even).  Future convex n-gon families
       discharge those four and inherit the seam; no topology remains.

   NOTE on the definition of convexity used: `vertices_in_halfplane` is the
   GLOBAL condition (every vertex inside every edge half-plane), not the
   local all-CCW-turns condition.  Locally-convex but non-simple rings (the
   pentagram) satisfy the local condition yet are NOT intersections of their
   half-planes, so the global form is the honest hypothesis.

   Bonus: `rtri_parity_seam_offring`.  The right-triangle ring is
   DEFINITIONALLY a `gtri_ring` instance (`rtri_ring x0 y0 x1 y1 =
   gtri_ring x0 y0 x1 y0 x0 y1`), so the triangle's total seam specialises to
   it in one line -- the third total family.

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam.
From NTS.Proofs Require Import PointInRingCorrect JCT JCT_OnEdgeCounterexample.
From NTS.Proofs Require Import RectangleJCT RectangleSeparation RectangleOffringSeam.
From NTS.Proofs Require Import SeparationField ConvexField.
From NTS.Proofs Require Import GeneralTriangleSeparation GeneralTriangleParity.
From NTS.Proofs Require Import GeneralTriangleHoleNesting GeneralTriangleJCT.
From NTS.Proofs Require Import GeneralTriangleExterior GeneralTriangleOffringSeam.
From NTS.Proofs Require Import RightTriangleJCT.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §1  Edge endpoints are ring vertices.
   --------------------------------------------------------------------------- *)

Lemma ring_edges_endpoints_in : forall (r : Ring) (e : Edge),
  In e (ring_edges r) -> In (fst e) r /\ In (snd e) r.
Proof.
  induction r as [| a r' IH]; [ contradiction | ].
  destruct r' as [| b r'']; [ contradiction | ].
  intros e He. cbn [ring_edges In] in He.
  destruct He as [He | He].
  - subst e. cbn [fst snd]. split; [ left | right; left ]; reflexivity.
  - destruct (IH e He) as [H1 H2].
    split; right; assumption.
Qed.

(* ---------------------------------------------------------------------------
   §2  Vertices inside a half-plane put the whole skeleton inside it.
   --------------------------------------------------------------------------- *)

Definition vertices_in_halfplane (r : Ring) (hp : R * R * R) : Prop :=
  forall v : Point, In v r -> 0 <= hp_slack hp v.

Lemma image_slack_nonneg : forall (r : Ring) (hp : R * R * R) (q : Point),
  vertices_in_halfplane r hp ->
  ring_image r q ->
  0 <= hp_slack hp q.
Proof.
  intros r hp q Hv [e [t [Hin [Ht [Hx Hy]]]]].
  destruct (ring_edges_endpoints_in r e Hin) as [H1 H2].
  pose proof (Hv _ H1) as S1. pose proof (Hv _ H2) as S2.
  destruct hp as [[a b] c]. unfold hp_slack in *.
  rewrite Hx, Hy. nra.
Qed.

(* ---------------------------------------------------------------------------
   §3  A negative convex field names a violated half-plane.
   --------------------------------------------------------------------------- *)

Lemma conv_min_neg_inv : forall (hps : list (R * R * R)) (pt : Point),
  conv_min hps pt < 0 ->
  exists hp, In hp hps /\ hp_slack hp pt < 0.
Proof.
  induction hps as [| hp rest IH]; intros pt Hneg; cbn [conv_min] in Hneg.
  - lra.
  - destruct (Rmin_neg_inv _ _ Hneg) as [Hhd | Htl].
    + exists hp. split; [ left; reflexivity | exact Hhd ].
    + destruct (IH pt Htl) as [hp' [Hin' Hs']].
      exists hp'. split; [ right; exact Hin' | exact Hs' ].
Qed.

(* ---------------------------------------------------------------------------
   §4  Generic exterior escape for a half-plane-presented ring.
   --------------------------------------------------------------------------- *)

Theorem convex_exterior_escapes : forall (r : Ring) (a b c : R) (p : Point),
  0 < a * a + b * b ->
  vertices_in_halfplane r (a, b, c) ->
  hp_slack (a, b, c) p < 0 ->
  ~ in_bounded_component_cont r p.
Proof.
  intros r a b c p Hnd Hv Hp.
  apply (escape_beyond_halfplane r p a b c).
  - exact Hnd.
  - intros q Hq.
    pose proof (image_slack_nonneg r (a, b, c) q Hv Hq) as Hs.
    unfold hp_slack in Hs. lra.
  - unfold hp_slack in Hp. lra.
Qed.

(* ---------------------------------------------------------------------------
   §5  THE ASSEMBLY: the total off-ring seam for any half-plane-presented
       ring, from four named family obligations.
   --------------------------------------------------------------------------- *)

Theorem convex_parity_seam_offring_of :
  forall (r : Ring) (hps : list (R * R * R)) (p : Point) (M : R),
    (* presentation facts *)
    (forall pt, conv_min hps pt = 0 -> ring_image r pt) ->
    Forall (vertices_in_halfplane r) hps ->
    Forall (fun hp : R * R * R =>
              let '(a, b, _) := hp in 0 < a * a + b * b) hps ->
    0 < M ->
    (forall pt, 0 < conv_min hps pt ->
                px pt * px pt + py pt * py pt <= M * M) ->
    (* the family's guarded parity facts *)
    (0 < conv_min hps p -> ray_avoids_vertices p r ->
       no_horizontal_edge_at p r -> point_in_ring p r) ->
    (conv_min hps p < 0 -> ray_avoids_vertices p r ->
       no_horizontal_edge_at p r -> ~ point_in_ring p r) ->
    parity_characterises_interior_cont_offring p r.
Proof.
  intros r hps p M Hzero Hverts Hnd HM Hbound Hpar_int Hpar_ext.
  unfold parity_characterises_interior_cont_offring.
  intros _ _ _ Hcompl Hnh Hrav.
  destruct (Rtotal_order (conv_min hps p) 0) as [Hneg | [Hz | Hpos]].
  - (* strict exterior: both sides false *)
    split.
    + intros [_ Hbnd]. exfalso.
      destruct (conv_min_neg_inv hps p Hneg) as [[[a b] c] [Hin Hs]].
      refine (convex_exterior_escapes r a b c p _ _ Hs Hbnd).
      * rewrite Forall_forall in Hnd. exact (Hnd _ Hin).
      * rewrite Forall_forall in Hverts. exact (Hverts _ Hin).
    + intro Hpir. exfalso. exact (Hpar_ext Hneg Hrav Hnh Hpir).
  - (* on the skeleton: excluded by the off-ring premise *)
    exfalso. apply Hcompl. apply Hzero. exact Hz.
  - (* strict interior *)
    split.
    + intros _. apply Hpar_int; assumption.
    + intros _. split; [ exact Hcompl | ].
      apply (convex_separation r hps p M); try assumption.
      intros pt Hc Hz. apply Hc. apply Hzero. exact Hz.
Qed.

(* ---------------------------------------------------------------------------
   §6  The right triangle: the THIRD total family, free.  Its ring is
       definitionally a `gtri_ring` instance.
   --------------------------------------------------------------------------- *)

Lemma rtri_ring_is_gtri : forall x0 y0 x1 y1,
  rtri_ring x0 y0 x1 y1 = gtri_ring x0 y0 x1 y0 x0 y1.
Proof. reflexivity. Qed.

Theorem rtri_parity_seam_offring : forall x0 y0 x1 y1 p,
  x0 < x1 -> y0 < y1 ->
  parity_characterises_interior_cont_offring p (rtri_ring x0 y0 x1 y1).
Proof.
  intros x0 y0 x1 y1 p Hx01 Hy01.
  rewrite rtri_ring_is_gtri.
  apply gtri_parity_seam_offring.
  unfold gdbl. nra.
Qed.

(* Sanity instance: the unit right triangle at an exterior point. *)
Example rtri_seam_unit_exterior :
  parity_characterises_interior_cont_offring (mkPoint 5 5) (rtri_ring 0 0 1 1).
Proof. apply rtri_parity_seam_offring; lra. Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions image_slack_nonneg.
Print Assumptions convex_exterior_escapes.
Print Assumptions convex_parity_seam_offring_of.
Print Assumptions rtri_parity_seam_offring.
