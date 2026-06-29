(* ============================================================================
   NetTopologySuite.Proofs.HalfOpenTrapped
   ----------------------------------------------------------------------------
   HALF-OPEN MIGRATION, rung 1: the trapped half of the polygonal Jordan seam,
   stated in HALF-OPEN parity, needs NO ray-genericity guard.

   Motivation (structural guard reduction).  The corpus's interior seams are
   stated over the CLOSED strict-straddle `point_in_ring`, and they carry
   `ray_avoids_vertices` because the closed test miscounts at vertex-grazing
   heights (the diamond in JCT_VertexGrazingCounterexample.v).  The HALF-OPEN
   parity `point_in_ring_ho` is grazing-robust by construction.  The bridge
   between the two conventions (`point_in_ring_ho_agrees`) is exactly where the
   guard is consumed -- e.g. `odd_parity_trapped_of_ho_kernel` only uses
   `ray_avoids_vertices` to convert a closed input into the half-open invariant
   before running the unconditional kernel.

   Key observation: the kernel-level lemma `JCTParityTransport.invariant_traps`
   takes the invariant `Q p` DIRECTLY -- no closed parity, no guard.  Feeding the
   half-open parity straight in (rather than going through the closed-to-ho
   agreement) yields a GUARD-FREE trapped half:

     ho_trapped : ring_closed r -> point_in_ring_ho p r
                  -> in_bounded_component_cont r p.

   No `ray_avoids_vertices`, no `ring_complement`, no `no_horizontal_edge_at`.
   This is the half-open migration of the trapped direction: the guard the closed
   seam needed is gone once the statement is phrased in the robust convention.

   SCOPE (honest).  This migrates the TRAPPED half only.  The ESCAPE half
   (`even_parity_escapes` / `escape_descent`) still carries `ray_avoids_vertices`
   in its boundary-walk machinery, so the FULL biconditional is not yet
   guard-free; that escape-side migration is the remaining rung.  And any result
   phrased back over the CLOSED `point_in_ring` (hence `point_set`, which is
   built on it) must still cross `point_in_ring_ho_agrees` and pay the guard --
   so a true `point_set`-level drop additionally requires re-basing `point_set`
   on the half-open convention.

   Pure-R; classical-reals trio only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay.
From NTS.Proofs Require Import JordanCurveSeam PointInRingTangents.
From NTS.Proofs Require Import JCTHalfOpenParity JCTSeamAssembly JCTParityTransport.
From NTS.Proofs Require Import GeneralTriangleSeparation TriangleValidPolygon.
Import ListNotations.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The guard-free half-open trapped half.                                 *)
(* -------------------------------------------------------------------------- *)

(* `point_in_ring_ho` is a decidable, locally-constant (along complement paths),
   far-false invariant for any closed ring -- exactly the `parity_invariant_for`
   contract -- so `invariant_traps` traps an odd half-open-parity point with NO
   genericity guard. *)
Theorem ho_trapped : forall (r : Ring) (p : Point),
  ring_closed r ->
  point_in_ring_ho p r ->
  in_bounded_component_cont r p.
Proof.
  intros r p Hclosed Hho.
  apply (invariant_traps r p (fun q => point_in_ring_ho q r)).
  - intro pt. apply point_in_ring_ho_dec.
  - split.
    + exact (ho_parity_locally_constant_holds r Hclosed).
    + exact (ho_far_false r Hclosed).
  - exact Hho.
Qed.

(* Packaged as continuous geometric interiority (adding only off-ring, which is
   part of the geometric_interior_cont conjunction -- still no ray guard). *)
Corollary ho_geometric_interior_of_parity : forall (r : Ring) (p : Point),
  ring_closed r ->
  ring_complement r p ->
  point_in_ring_ho p r ->
  geometric_interior_cont p r.
Proof.
  intros r p Hclosed Hcompl Hho.
  split; [ exact Hcompl | apply ho_trapped; assumption ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Triangle instantiation: contrast with the guarded closed version.      *)
(*                                                                            *)
(* The closed seam needs the guard: `GeneralTriangleJCT.gtri_interior_in_ring` *)
(* and `RelateNG.gtri_point_in_ring_imp_pos` both require `ray_avoids_vertices`.*)
(* The half-open trapped half for the same triangle does not.                 *)
(* -------------------------------------------------------------------------- *)

Corollary tri_ho_trapped : forall ax ay bx by_ cx cy p,
  point_in_ring_ho p (gtri_ring ax ay bx by_ cx cy) ->
  in_bounded_component_cont (gtri_ring ax ay bx by_ cx cy) p.
Proof.
  intros ax ay bx by_ cx cy p Hho.
  apply ho_trapped; [ apply gtri_ring_closed | exact Hho ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions ho_trapped.
Print Assumptions ho_geometric_interior_of_parity.
Print Assumptions tri_ho_trapped.
