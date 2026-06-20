(* ============================================================================
   NetTopologySuite.Proofs.RelatePrepared
   ----------------------------------------------------------------------------
   Issue #67 S13: Prepared cache correctness (NTS#819 proof companion).

   `PreparedGeometry` wraps a Geometry with (initially trivial) memoisation.
   The key correctness obligation (independent of caching strategy):
     evaluate (prepare A) B  =  relate A B

   This is a refinement theorem once the base `relate` (RelateNG) is specified.

   Delivers:
     - PreparedGeometry record
     - prepare / evaluate
     - prepared_evaluate_agrees (initially trivial identity cache)

   Integration: RelateNG uses prepared as wrapper; oracle/driver remain lookup
   for differential but can call evaluate for compute-path tests.

   No `Admitted`, no new axioms.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import DE9IM Overlay RelateNG.

Record PreparedGeometry : Type := mkPrepared {
  pg_geom : Geometry;
  (* Future: cached indexes, noded fragments, strata bitmaps, etc.
     For now the cache is the identity (result must be identical either path). *)
  pg_cache : unit   (* placeholder *)
}.

Definition prepare (g : Geometry) : PreparedGeometry :=
  mkPrepared g tt.

Definition evaluate (pg : PreparedGeometry) (g : Geometry) : IntersectionMatrix :=
  relate (pg_geom pg) g.

(* The NTS#819 proof obligation: cache path agrees with direct relate. *)
Theorem prepared_evaluate_agrees :
  forall (pg : PreparedGeometry) (g : Geometry),
    evaluate pg g = relate (pg_geom pg) g.
Proof.
  intros pg g. unfold evaluate. reflexivity.
Qed.

(* Identity case: prepare(g) then evaluate against itself. *)
Theorem prepared_identity :
  forall g : Geometry,
    evaluate (prepare g) g = relate g g.
Proof.
  intro g. apply prepared_evaluate_agrees.
Qed.

Print Assumptions prepared_evaluate_agrees.
Print Assumptions prepared_identity.