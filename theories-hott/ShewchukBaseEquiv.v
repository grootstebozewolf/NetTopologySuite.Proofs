(* ============================================================================
   NetTopologySuite.HoTT.ShewchukBaseEquiv (skeleton)
   ----------------------------------------------------------------------------
   Placeholder for the first small HoTT equivalence in the recommended order
   from `docs/hott-rgr-tin-hobby-shewchuk-curve-pivot.md` (this RGR session).

   Shewchuk expansions are the foundational "preds base" (low risk, high
   reuse for orient/intersect used by Hobby noding, curve arcs, Voronoi
   Delaunay dual, TIN, etc.).

   Per RGR: start here with small equiv (e.g. TwoSum / basic expansion
   non-overlap in regime) + transport one property from archived classical
   (e.g. from B64_bridge or Orient_b64_exact).

   This file is the Green "attempt" starter for the chunked approach.
   Full work in follow-on bounded RGR (Red: pick concrete helper;
   Green: model NTS vs formal + Equiv using Univalence; Refactor: update
   pivot doc + add tests/oracle link).

   See also: theories-hott/VoronoiEquivalence.v (pilot), the RGR pivot docs,
   archive/theories-flocq/B64_*_Shewchuk*.v and B64_bridge.v for classical
   source to transport/re-express.

   One axiom: Univalence (justified for linkage/transport of exactness/
   error properties to NTS Robust* / .Curve).
   ========================================================================== *)

(* Minimal skeleton — expand in next session. *)
Axiom univalence : forall (A B : Type), Equiv A B -> A = B.  (* the one allowed *)

(* TODO next RGR: define formal expansion, NTS model (mirror C# RobustDeterminant
   or extracted), prove small equiv, transport e.g. "nonoverlap => sum nonoverlap"
   or small-int exactness. *)

(* Reference: archived B64_bridge.v for b64_plus etc. correctness that can
   be lifted. *)