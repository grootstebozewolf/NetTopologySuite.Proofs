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

(* HoTT primitives (inlined minimal for skeleton; shared with VoronoiEquivalence.v) *)
Record IsEquiv {A B} (f : A -> B) := mkIsEquiv
  { equiv_inv : B -> A
  ; equiv_sect : forall x : B, f (equiv_inv x) = x
  ; equiv_retr : forall x : A, equiv_inv (f x) = x
  ; equiv_adj : True  (* coherence placeholder *)
  }.

Record Equiv (A B : Type) := mkEquiv
  { equiv_fun : A -> B
  ; equiv_isequiv : IsEquiv equiv_fun
  }.

(* The one allowed axiom (Univalence) — justified for linkage/transport of
   exactness/error properties to NTS Robust* / .Curve per axiom-policy.md. *)
Axiom univalence : forall (A B : Type), Equiv A B -> A = B.

(* TODO next RGR: define formal expansion (e.g. from archived B64_Expansion.v),
   NTS model (mirror C# RobustDeterminant or extracted b64 ops), prove small
   equiv (e.g. TwoSum non-overlap), transport e.g. "nonoverlap => sum nonoverlap"
   or small-int exactness from archive/theories-flocq/B64_bridge.v + Orient_b64_exact.v.

   This is the Green 'attempt' starter for the chunked approach per
   hott-rgr-tin-hobby-shewchuk-curve-pivot.md (Shewchuk first as preds base). *)

(* Reference: archived B64_*_Shewchuk*.v , B64_bridge.v , B64_FastExpansionSum_Shewchuk.v
   for classical source to re-express/transport. Full equiv in follow-on bounded session. *)