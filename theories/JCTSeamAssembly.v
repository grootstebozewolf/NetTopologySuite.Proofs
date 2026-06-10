(* ============================================================================
   NetTopologySuite.Proofs.JCTSeamAssembly
   ----------------------------------------------------------------------------
   H1 PROPER, assembly: the corrected off-ring seam for GENERAL rings, with
   the trapped half discharged and the ESCAPE half isolated as the single
   remaining residual of the polygonal Jordan Curve Theorem.

   With `JCTTrappedHalf.odd_parity_trapped` Qed, the seam's hard direction
   is a theorem for every closed ring:

     point_in_ring_imp_geometric_cont :
       ring_closed r -> ring_complement r p -> ray_avoids_vertices p r ->
       point_in_ring p r -> geometric_interior_cont p r.

   (Also named here: `ho_parity_locally_constant_holds` -- the part-3/4/5
   kernel chain composed: the half-open parity is locally constant along
   complement paths of ANY closed ring.)

   The dual direction is the ESCAPE half: an even-parity off-ring point of a
   SIMPLE ring reaches infinity through the complement.  Stated per-point as

     even_parity_escapes r p := ~ point_in_ring p r ->
                                ~ in_bounded_component_cont r p

   it is the LAST open ingredient: `parity_seam_offring_of_escape` derives
   the full corrected seam `parity_characterises_interior_cont_offring p r`
   from it (the parity side of the biconditional is decided by
   `point_in_ring_dec`, so no classical step is added).  Simplicity is
   genuinely needed by the residual and only by it: a doubly-wound ring has
   even-parity points that are trapped, so the escape cannot follow from
   closedness alone -- while the trapped half, as proved, needs no
   simplicity at all.

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam.
From NTS.Proofs Require Import PointInRingCorrect JCT JCT_OnEdgeCounterexample.
From NTS.Proofs Require Import JCTParityTransport JCTHalfOpenParity.
From NTS.Proofs Require Import JCTGenericStability JCTLevelJump JCTTrappedHalf.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §1  The kernel chain, composed and named: half-open parity is locally
       constant along complement paths of any closed ring.
   --------------------------------------------------------------------------- *)

Theorem ho_parity_locally_constant_holds : forall (r : Ring),
  ring_closed r -> ho_parity_locally_constant r.
Proof.
  intros r Hclosed.
  apply ho_kernel_of_level_stable.
  apply ho_level_stable_of_jump.
  apply ho_level_jump_holds.
  exact Hclosed.
Qed.

(* ---------------------------------------------------------------------------
   §2  The seam's hard direction, unconditional for closed rings.
   --------------------------------------------------------------------------- *)

Theorem point_in_ring_imp_geometric_cont : forall (r : Ring) (p : Point),
  ring_closed r ->
  ring_complement r p ->
  ray_avoids_vertices p r ->
  point_in_ring p r ->
  geometric_interior_cont p r.
Proof.
  intros r p Hclosed Hcompl Hrav Hpir.
  split; [ exact Hcompl | ].
  apply odd_parity_trapped; assumption.
Qed.

(* ---------------------------------------------------------------------------
   §3  The escape residual, and the seam derived from it.
   --------------------------------------------------------------------------- *)

(* THE LAST OPEN INGREDIENT OF H1: an even-parity off-ring point escapes.
   This is where simplicity is genuinely needed (a doubly-wound ring has
   even-parity trapped points); the trapped half above needs none. *)
Definition even_parity_escapes (r : Ring) (p : Point) : Prop :=
  ~ point_in_ring p r -> ~ in_bounded_component_cont r p.

Theorem parity_seam_offring_of_escape : forall (r : Ring) (p : Point),
  even_parity_escapes r p ->
  parity_characterises_interior_cont_offring p r.
Proof.
  intros r p Hesc.
  unfold parity_characterises_interior_cont_offring.
  intros _ Hclosed _ Hcompl _ Hrav.
  split.
  - (* geometric -> parity: decided, with the escape refuting the even case *)
    intros [_ Hbnd].
    destruct (point_in_ring_dec p r) as [Hin | Hnin]; [ exact Hin | ].
    exfalso. exact (Hesc Hnin Hbnd).
  - (* parity -> geometric: the trapped half *)
    intro Hpir.
    apply (point_in_ring_imp_geometric_cont r p Hclosed Hcompl Hrav Hpir).
Qed.

(* The conditional headline, ring-level: the corrected JCT seam holds for
   every simple closed ring and guarded off-ring point, given only the
   per-point escape. *)
Theorem point_in_ring_correct_of_escape : forall (r : Ring) (p : Point),
  ring_simple r ->
  ring_closed r ->
  ring_has_minimum_points r ->
  ring_complement r p ->
  no_horizontal_edge_at p r ->
  ray_avoids_vertices p r ->
  even_parity_escapes r p ->
  (point_in_ring p r <-> geometric_interior_cont p r).
Proof.
  intros r p Hs Hc Hm Hcompl Hnh Hrav Hesc.
  symmetry.
  exact (parity_seam_offring_of_escape r p Hesc Hs Hc Hm Hcompl Hnh Hrav).
Qed.

(* Sanity: the rectangle's total seam discharges the escape residual, so the
   general assembly is non-vacuous on a familiar family. *)
Example rect_escape_residual_discharged :
  even_parity_escapes (RectangleJCT.rect_ring 0 0 1 1) (mkPoint 5 5).
Proof.
  intro Hnin. intros [M [HM Hb]].
  (* (5,5) is strictly beyond the unit box: escape upward *)
  refine (RectangleOffringSeam.escape_beyond_y_high
            (RectangleJCT.rect_ring 0 0 1 1) (mkPoint 5 5) 1 _ _
            (ex_intro _ M (conj HM Hb))).
  - intros v Hv.
    destruct (RectangleOffringSeam.rect_image_bounds 0 0 1 1 v
                ltac:(lra) ltac:(lra) Hv) as [_ [_ Hy]].
    exact Hy.
  - cbn [py]. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions ho_parity_locally_constant_holds.
Print Assumptions point_in_ring_imp_geometric_cont.
Print Assumptions parity_seam_offring_of_escape.
Print Assumptions point_in_ring_correct_of_escape.
