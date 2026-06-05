(* ============================================================================
   NetTopologySuite.Proofs.Tin
   ----------------------------------------------------------------------------
   Adjacent-TIN merging: the formal counterpart of the headline novelty in

     Mariusz Zygmunt and Marta Rog,
     "New approach towards Digital Elevation Model data generalisation
      using the Douglas-Peucker algorithm and Delaunay triangulation
      based on characteristic boundary points",
     Measurement 260 (2026) 119849,
     doi: 10.1016/j.measurement.2025.119849.

   Their headline practical claim (paper Figs 8-9, conclusion 5) is that
   adjacent TINs built by their pipeline share boundary vertices and so
   merge seamlessly, because each side simplifies the SHARED boundary
   polyline with the same Douglas-Peucker algorithm at the same tolerance.

   The formal core of that claim does not actually need determinism of the
   simplifier:  even if two adjacent datasets choose different simp_star
   derivations (e.g. one runs the sequential variant, the other the parallel
   variant -- both in Zygmunt & Rog's experiments), they still agree on the
   boundary ENDPOINTS, because simp_star (and simp_star_perp) preserve the
   head and the last vertex unconditionally.  That's enough for the
   adjacent-merging property: the shared edge between the two TINs has
   matching corner vertices, which is the prerequisite for the edge to be
   detected as shared at all.

   The strict equality of *all* shared-edge vertices follows from
   determinism of the simplifier, which is an algorithm-level property
   layered on top of the simp_star spec.  This module proves the weaker
   "endpoints agree" theorem from simp_star alone, which gives the formal
   green light for any deterministic Douglas-Peucker realisation to inherit
   the adjacency guarantee.

   No Admitted, no Axiom (except the three classical-reals axioms inherited
   from the corpus's Real.v).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import List.
Import ListNotations.
From NTS.Proofs Require Import Distance Linearise Simplify.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* A TIN tagged with its source-derived boundary polyline.                    *)
(*                                                                            *)
(* The triangle list is opaque here; this module reasons only about the      *)
(* boundary.  A future slice that proves topological properties of the      *)
(* triangulation (Euler relation, edge-sharing) can specialise               *)
(* tt_triangles to a concrete representation built on Triangle.v.            *)
(* -------------------------------------------------------------------------- *)

Record TaggedTin : Type := mkTaggedTin
  { tt_triangles : list (Point * Point * Point);
    tt_boundary  : list Point }.

(* -------------------------------------------------------------------------- *)
(* Same-source predicate: both TINs' boundary polylines were obtained from   *)
(* the same `source` polyline via simp_star at tolerance eps.  Two adjacent  *)
(* datasets sharing a boundary polyline (as in Zygmunt & Rog's Fig 8)        *)
(* instantiate this predicate with `source` = the shared boundary.          *)
(* -------------------------------------------------------------------------- *)

Definition same_source_boundary
  (T1 T2 : TaggedTin) (source : list Point) (eps : R) : Prop :=
  simp_star eps source (tt_boundary T1) /\
  simp_star eps source (tt_boundary T2).

(* Perpendicular-distance variant of the same predicate.  Lets users pick
   the Douglas-Peucker flavour (chord-deficit or perp-line) on each side
   independently. *)
Definition same_source_boundary_perp
  (T1 T2 : TaggedTin) (source : list Point) (eps : R) : Prop :=
  simp_star_perp eps source (tt_boundary T1) /\
  simp_star_perp eps source (tt_boundary T2).

(* -------------------------------------------------------------------------- *)
(* Headline: same-source TINs share boundary endpoints.                       *)
(*                                                                            *)
(* The proof is a direct application of simp_star_preserves_head and         *)
(* simp_star_preserves_last from Simplify.v.  No new geometric content;     *)
(* the value is that the theorem statement explicitly names the property    *)
(* downstream TIN-building code can rely on.                                *)
(* -------------------------------------------------------------------------- *)

Theorem same_source_share_endpoints :
  forall (T1 T2 : TaggedTin) (source : list Point) (eps : R) (default : Point),
    same_source_boundary T1 T2 source eps ->
    hd default (tt_boundary T1) = hd default (tt_boundary T2) /\
    last (tt_boundary T1) default = last (tt_boundary T2) default.
Proof.
  intros T1 T2 source eps d [H1 H2].
  split.
  - transitivity (hd d source).
    + symmetry. apply (simp_star_preserves_head _ _ _ H1).
    + apply (simp_star_preserves_head _ _ _ H2).
  - transitivity (last source d).
    + symmetry. apply (simp_star_preserves_last _ _ _ d H1).
    + apply (simp_star_preserves_last _ _ _ d H2).
Qed.

Theorem same_source_share_endpoints_perp :
  forall (T1 T2 : TaggedTin) (source : list Point) (eps : R) (default : Point),
    same_source_boundary_perp T1 T2 source eps ->
    hd default (tt_boundary T1) = hd default (tt_boundary T2) /\
    last (tt_boundary T1) default = last (tt_boundary T2) default.
Proof.
  intros T1 T2 source eps d [H1 H2].
  split.
  - transitivity (hd d source).
    + symmetry. apply (simp_star_perp_preserves_head _ _ _ H1).
    + apply (simp_star_perp_preserves_head _ _ _ H2).
  - transitivity (last source d).
    + symmetry. apply (simp_star_perp_preserves_last _ _ _ d H1).
    + apply (simp_star_perp_preserves_last _ _ _ d H2).
Qed.

(* -------------------------------------------------------------------------- *)
(* Mixed-mode variant: one TIN simplified with the chord-deficit form,       *)
(* the other with the perpendicular-distance form (the parallel/sequential  *)
(* mode comparison in Zygmunt & Rog).  Endpoints still agree because both   *)
(* head/last preservation theorems share the source.                        *)
(* -------------------------------------------------------------------------- *)

Definition same_source_boundary_mixed
  (T1 T2 : TaggedTin) (source : list Point) (eps : R) : Prop :=
  simp_star eps source (tt_boundary T1) /\
  simp_star_perp eps source (tt_boundary T2).

Theorem same_source_share_endpoints_mixed :
  forall (T1 T2 : TaggedTin) (source : list Point) (eps : R) (default : Point),
    same_source_boundary_mixed T1 T2 source eps ->
    hd default (tt_boundary T1) = hd default (tt_boundary T2) /\
    last (tt_boundary T1) default = last (tt_boundary T2) default.
Proof.
  intros T1 T2 source eps d [H1 H2].
  split.
  - transitivity (hd d source).
    + symmetry. apply (simp_star_preserves_head _ _ _ H1).
    + apply (simp_star_perp_preserves_head _ _ _ H2).
  - transitivity (last source d).
    + symmetry. apply (simp_star_preserves_last _ _ _ d H1).
    + apply (simp_star_perp_preserves_last _ _ _ d H2).
Qed.

(* -------------------------------------------------------------------------- *)
(* Companion length-budget result: both simplifications return a polyline    *)
(* no longer than the source.  This is the "data reduction does not inflate *)
(* the boundary" companion to the endpoint-sharing theorem; it underwrites  *)
(* the 41-56 % triangle-count reduction Zygmunt & Rog observe (paper        *)
(* Table 5) without ever extending the boundary outside the source.         *)
(* -------------------------------------------------------------------------- *)

Theorem same_source_boundary_length_bounded :
  forall (T1 T2 : TaggedTin) (source : list Point) (eps : R),
    same_source_boundary T1 T2 source eps ->
    polyline_length (tt_boundary T1) <= polyline_length source /\
    polyline_length (tt_boundary T2) <= polyline_length source.
Proof.
  intros T1 T2 source eps [H1 H2].
  split.
  - apply (simp_star_length_monotone _ _ _ H1).
  - apply (simp_star_length_monotone _ _ _ H2).
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                               *)
(* -------------------------------------------------------------------------- *)

Print Assumptions same_source_share_endpoints.
Print Assumptions same_source_share_endpoints_perp.
Print Assumptions same_source_share_endpoints_mixed.
Print Assumptions same_source_boundary_length_bounded.
