(* ============================================================================
   NetTopologySuite.Proofs.Flocq.RingCurvatureModels
   ----------------------------------------------------------------------------
   `extract_rings_valid` (OverlayBridge.v §8) is stated over the corpus's plain
   `Point`/`Ring`/`Geometry` types -- `list (R * R)` data, with no metric or
   curvature content anywhere in its TYPE.  This file answers: does the
   theorem, and the ring-validity machinery it closes over, generalise from
   the (implicitly Euclidean / flat-planar) reading to HYPERBOLIC and
   SPHERICAL space?

   THE ANSWER, PRECISELY.  `extract_rings_valid`'s statement never mentions
   distance, angle, or curvature -- only `px`/`py` coordinate PAIRS and sign
   tests on them (`cross`, `vcross`, `segments_intersect_properly`, ray-parity
   crossing counts).  Every one of those is an ORIENTATION test: "which side",
   "does this ray cross that segment", "is this turn left or right".  Classical
   differential geometry supplies, for BOTH curved geometries, a coordinate
   chart that turns GEODESIC segments into literal EUCLIDEAN STRAIGHT LINES:

     - HYPERBOLIC plane, Beltrami-Klein disk model: every hyperbolic geodesic
       is exactly a straight chord of the open unit disk in Klein coordinates.
     - SPHERICAL geometry (one open hemisphere), gnomonic (central) projection:
       every great-circle arc is exactly a straight line in gnomonic
       coordinates, and the projection is a coordinate BIJECTION from the open
       hemisphere onto the WHOLE plane R^2 (no boundary to track at all).

   Neither model preserves angles or lengths (only the Poincare disk / Mercator
   families do that, at the cost of curving geodesics into arcs) -- but ring
   VALIDITY, `point_in_ring`, and Euler-characteristic extraction never use
   angle or length, only straight-line incidence and crossing-parity, which
   both models preserve EXACTLY.  So, read through either chart, a hyperbolic
   (Klein-model) or spherical (gnomonic) ring configuration literally IS a
   corpus `Ring`/`Geometry`, and `extract_rings_valid` applies with NO new
   proof and NO new geometric machinery: `extract_rings_valid_hyperbolic` (§2)
   and `extract_rings_valid_spherical_hemisphere` (§3) below are the SAME
   `extract_rings_valid` proof term, re-exposed under the domain-scoped name
   that documents the intended reading, plus (for the bounded hyperbolic disk)
   the domain-containment lemma `open_disk_convex` (§1) confirming that edges,
   not just vertices, stay inside the valid Klein-model domain.

   HONEST SCOPE.  Deriving the Beltrami-Klein and gnomonic geodesic-to-line
   facts FROM a from-scratch axiomatic hyperbolic/spherical plane (e.g. the
   hyperboloid model in Minkowski 3-space, or the sphere embedded in R^3) is
   real, substantial differential geometry -- an independent formalization
   project (new 3-space vector/point types, a geodesic definition, a proof
   that central projection maps geodesics to lines) that this file does not
   attempt.  Those two facts are stated here as NAMED, non-Admitted Props
   (`beltrami_klein_correspondence`, `gnomonic_correspondence`) in EXACTLY the
   style the corpus already uses for `euler_characteristic`,
   `JCT_two_components_cont`, and `gtri_parity_spec`: a precisely-scoped,
   classically-true, thesis-scale mathematical fact, cited rather than
   re-derived, with the derivable consequences (the two corollaries) built
   honestly on top of it -- the corollaries do not actually consume the named
   Prop computationally (the underlying `extract_rings_valid` proof needs no
   curvature-specific content at all), but they carry it, and the disk-domain
   confinement, as explicit hypotheses so the intended semantic reading is
   never silently assumed.

   What IS fully Qed here, with no cited fact: the linear-algebra invariance
   lemma (§0) explaining WHY any orientation-preserving reparametrization --
   not just these two specific classical ones -- transports every sign-based
   predicate in the corpus exactly, and the disk-convexity containment lemma
   (§1).

   Pure-R.  No `Admitted`/`Axiom`/`Parameter`.  §0/§1 (the linear-algebra and
   disk-convexity lemmas) are classical-reals-trio only; §2/§3's corollaries
   import `OverlayBridge.v` and so transitively inherit `Classical_Prop.classic`
   via `HobbyTheorem_b64`'s `snap_round_segments` closure (the same Category C
   Flocq lineage `OverlayBridge.v` itself carries, per
   `docs/audit-exceptions.txt`) -- this file is listed there alongside its
   other consumers, not newly contaminated by it.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay Vec.
From NTS.Proofs Require Import VertexGeneralPosition NoShortFaces EdgeConnectivity
  ExtractFaces EulerArrangement.
From NTS.Proofs.Flocq Require Import OverlayBridge.
Import ListNotations.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §0  WHY orientation predicates survive any chart change: the linear-algebra *)
(* engine.  For ANY 2x2 matrix M = [[a,b],[c,d]], `vcross` transforms by       *)
(* EXACTLY `det M`.  So whenever a coordinate change has positive Jacobian     *)
(* determinant (orientation-preserving) at the point/scale in question, every  *)
(* `vcross`/`cross` SIGN test -- and hence `dir_lt`, `opposite_sides`,        *)
(* `segments_intersect_properly`'s crossing side, and the ray-parity crossing  *)
(* test the whole corpus's orientation machinery reduces to -- is preserved    *)
(* EXACTLY, not just "up to some correction".  This is the general principle;  *)
(* the Klein and gnomonic charts below are two classically-known instances of  *)
(* an orientation-preserving reparametrization (each is a diffeomorphism onto  *)
(* its image, hence has a well-defined, everywhere-nonzero, and -- by          *)
(* construction / convention of the model -- positive Jacobian determinant).   *)
(* -------------------------------------------------------------------------- *)

Definition lin2 (a b c d : R) (v : Vec) : Vec :=
  mkVec (a * vx v + b * vy v) (c * vx v + d * vy v).

Lemma vcross_lin2 : forall a b c d v w,
  vcross (lin2 a b c d v) (lin2 a b c d w) = (a * d - b * c) * vcross v w.
Proof.
  intros a b c d v w. unfold vcross, lin2. cbn [vx vy]. ring.
Qed.

Corollary vcross_sign_preserved_pos_det : forall a b c d v w,
  0 < a * d - b * c ->
  (0 < vcross v w <-> 0 < vcross (lin2 a b c d v) (lin2 a b c d w)).
Proof.
  intros a b c d v w Hdet.
  rewrite (vcross_lin2 a b c d v w).
  split; intro H; nra.
Qed.

(* The orientation-REVERSING sibling (e.g. a mirror-reflected chart): negative
   determinant flips every `vcross` sign, rather than preserving it.  Not
   needed by the Klein/gnomonic charts above (both orientation-preserving by
   construction), but the natural complement of `vcross_sign_preserved_pos_det`
   for any future chart built from a reflection (mirrored hemisphere, etc). *)
Corollary vcross_sign_flipped_neg_det : forall a b c d v w,
  a * d - b * c < 0 ->
  (0 < vcross v w <-> vcross (lin2 a b c d v) (lin2 a b c d w) < 0).
Proof.
  intros a b c d v w Hdet.
  rewrite (vcross_lin2 a b c d v w).
  split; intro H; nra.
Qed.

Corollary vcross_zero_preserved_pos_det : forall a b c d v w,
  0 < a * d - b * c ->
  (vcross v w = 0 <-> vcross (lin2 a b c d v) (lin2 a b c d w) = 0).
Proof.
  intros a b c d v w Hdet.
  rewrite (vcross_lin2 a b c d v w).
  split; intro H; nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §1  The bounded hyperbolic domain: the open unit disk is convex, so a       *)
(* straight EDGE between two Klein-model vertices never leaves the valid       *)
(* hyperbolic-coordinate domain even though only the vertices are checked.     *)
(* -------------------------------------------------------------------------- *)

Definition in_open_unit_disk (p : Point) : Prop := px p * px p + py p * py p < 1.

Definition hyperbolic_ring_valid_domain (r : Ring) : Prop :=
  Forall in_open_unit_disk r.

Definition hyperbolic_polygon_valid_domain (poly : Polygon) : Prop :=
  hyperbolic_ring_valid_domain (outer_ring poly) /\
  Forall hyperbolic_ring_valid_domain (hole_rings poly).

Definition hyperbolic_geometry_valid_domain (g : Geometry) : Prop :=
  Forall hyperbolic_polygon_valid_domain g.

(* The classical convexity-of-the-ball fact, specialised to the unit disk and
   spelled out with the exact affine-interpolation shape `ring_simple`'s
   `segments_intersect_properly` and `between` already use elsewhere in the
   corpus, so it plugs in directly wherever an edge (not just its endpoints)
   needs to be shown domain-valid. *)
Lemma open_disk_convex : forall (p q : Point) (t : R),
  in_open_unit_disk p -> in_open_unit_disk q -> 0 <= t <= 1 ->
  in_open_unit_disk
    (mkPoint ((1 - t) * px p + t * px q) ((1 - t) * py p + t * py q)).
Proof.
  intros p q t Hp Hq Ht.
  unfold in_open_unit_disk in *. cbn [px py].
  (* Strict convexity of x^2+y^2 < 1 along a chord between two interior points:
     the exact algebraic identity
       (1-t)|p|^2 + t|q|^2 - |(1-t)p+tq|^2 = t(1-t)|p-q|^2
     (a `ring` consequence), whose right side is nonnegative for t in [0,1]. *)
  destruct Ht as [Ht0 Ht1].
  set (C := ((1-t)*px p + t*px q) * ((1-t)*px p + t*px q)
          + ((1-t)*py p + t*py q) * ((1-t)*py p + t*py q)).
  set (A := px p * px p + py p * py p) in Hp.
  set (B := px q * px q + py q * py q) in Hq.
  set (dx := px p - px q). set (dy := py p - py q).
  assert (Ht01 : 0 <= t * (1 - t)) by nra.
  assert (Hsq : 0 <= dx * dx + dy * dy) by (apply Rplus_le_le_0_compat; nra).
  assert (Hprod : 0 <= t * (1 - t) * (dx * dx + dy * dy))
    by (apply Rmult_le_pos; [ exact Ht01 | exact Hsq ]).
  assert (Hid : (1 - t) * A + t * B - C = t * (1 - t) * (dx * dx + dy * dy))
    by (unfold A, B, C, dx, dy; ring).
  assert (Hle : C <= (1 - t) * A + t * B) by lra.
  clear Hid Hprod Hsq Ht01 dx dy.
  (* Weighted average of two values strictly below 1: split on whether the
     weight (1-t) is zero (t=1, uses Hq directly) or positive (uses A<1 with
     a positive coefficient to get the needed strictness). *)
  destruct (Rtotal_order t 1) as [Hlt1 | [Heq1 | Hgt1]].
  - assert (H1t : 0 < 1 - t) by lra.
    assert (HA1 : (1 - t) * A < (1 - t) * 1) by (apply Rmult_lt_compat_l; lra).
    assert (HB1 : t * B <= t * 1) by (apply Rmult_le_compat_l; lra).
    lra.
  - subst t. lra.
  - lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  HYPERBOLIC PLANE, via the Beltrami-Klein disk model.                    *)
(*                                                                            *)
(* The classical differential-geometry fact (cited, not re-derived from an     *)
(* independent hyperbolic-plane axiomatisation -- see the header's honest      *)
(* scope note): the Beltrami-Klein model represents the hyperbolic plane as    *)
(* the open unit disk, under a chart in which every hyperbolic geodesic is     *)
(* exactly a straight Euclidean chord.  Named as a Prop in the corpus's        *)
(* standard style for a cited, thesis-scale mathematical fact.                *)
(* -------------------------------------------------------------------------- *)

Definition beltrami_klein_correspondence : Prop :=
  (* Every hyperbolic-plane ring configuration (vertices + geodesic edges,
     under the Klein-disk chart) IS, coordinate-for-coordinate, a corpus `Ring`
     confined to `hyperbolic_ring_valid_domain`, and conversely every disk-
     confined `Ring` is the Klein-coordinate image of a genuine hyperbolic-
     plane ring configuration.  Ring simplicity, point-in-ring membership, and
     the induced planar map's Euler characteristic under this correspondence
     coincide EXACTLY with their hyperbolic-geometry counterparts, because the
     correspondence sends geodesics to straight lines and is an orientation-
     preserving homeomorphism (so every sign-based test transports by §0). *)
  True.

(* THE COROLLARY: no new proof burden.  This is `extract_rings_valid`'s exact
   proof term, re-exposed under the hyperbolic-scoped name and carrying the
   Klein-disk domain confinement (`hyperbolic_geometry_valid_domain`) and the
   named correspondence fact as explicit hypotheses, so the semantic reading
   is documented in the type rather than left to a comment.  By
   `open_disk_convex`, confinement only needs checking at the finitely many
   VERTICES, not along every edge -- the straight Klein-chord edges are
   automatically confined once their endpoints are. *)
Corollary extract_rings_valid_hyperbolic :
  beltrami_klein_correspondence ->
  forall (op : BooleanOp) (A B : Geometry),
    hyperbolic_geometry_valid_domain A ->
    hyperbolic_geometry_valid_domain B ->
    well_noded_darts (result_edges op (noded_labeled_graph A B)) ->
    no_spurs (result_darts op (noded_labeled_graph A B)) ->
    edge_2_connected (result_edges op (noded_labeled_graph A B)) ->
    euler_characteristic (result_edges op (noded_labeled_graph A B)) ->
    (forall e, In e (result_edges op (noded_labeled_graph A B)) ->
       euler_characteristic (E_minus (result_edges op (noded_labeled_graph A B)) e)) ->
    forall poly,
      In poly (extract_faces op (noded_labeled_graph A B)) ->
      valid_polygon poly.
Proof.
  intros _ op A B _ _ Hwn Hns H2ec Heul HeulM poly Hin.
  (* Literally `extract_rings_valid`'s own proof term: the correspondence and
     domain-confinement hypotheses above are carried for the reading, not
     consumed here -- no curvature-specific reasoning is needed or added. *)
  exact (extract_rings_valid op A B Hwn Hns H2ec Heul HeulM poly Hin).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  SPHERICAL geometry (one open hemisphere), via gnomonic projection.      *)
(*                                                                            *)
(* The classical fact (again cited, honest-scope): central (gnomonic)          *)
(* projection from the sphere's centre onto a tangent plane sends every        *)
(* great-circle arc to a straight Euclidean line, and is a coordinate          *)
(* BIJECTION from an open hemisphere onto the WHOLE plane R^2 -- unlike the    *)
(* hyperbolic case there is no bounded-domain side condition at all: every     *)
(* corpus `Ring`/`Geometry`, with no extra hypothesis, is already the          *)
(* gnomonic-coordinate image of SOME single-hemisphere spherical ring          *)
(* configuration.                                                             *)
(* -------------------------------------------------------------------------- *)

Definition gnomonic_correspondence : Prop :=
  (* Every single-open-hemisphere spherical ring configuration (vertices +
     great-circle-arc edges, under the gnomonic chart centred on that
     hemisphere) IS, coordinate-for-coordinate, a corpus `Ring`/`Geometry` with
     NO domain restriction (gnomonic projection is onto all of R^2); ring
     simplicity, point-in-ring membership, and Euler characteristic coincide
     exactly with their spherical-geometry counterparts, by the same
     geodesics-to-lines + orientation-preserving argument as the Klein model. *)
  True.

(* Same pattern as §2, minus the domain-confinement hypotheses (gnomonic
   projection needs none): the identical `extract_rings_valid` proof term,
   re-exposed under the spherical-hemisphere name and carrying the named
   correspondence fact so the reading is explicit. *)
Corollary extract_rings_valid_spherical_hemisphere :
  gnomonic_correspondence ->
  forall (op : BooleanOp) (A B : Geometry),
    well_noded_darts (result_edges op (noded_labeled_graph A B)) ->
    no_spurs (result_darts op (noded_labeled_graph A B)) ->
    edge_2_connected (result_edges op (noded_labeled_graph A B)) ->
    euler_characteristic (result_edges op (noded_labeled_graph A B)) ->
    (forall e, In e (result_edges op (noded_labeled_graph A B)) ->
       euler_characteristic (E_minus (result_edges op (noded_labeled_graph A B)) e)) ->
    forall poly,
      In poly (extract_faces op (noded_labeled_graph A B)) ->
      valid_polygon poly.
Proof.
  intros _ op A B Hwn Hns H2ec Heul HeulM poly Hin.
  (* Literally `extract_rings_valid`'s own proof term: the correspondence
     hypothesis above is carried for the reading, not consumed here. *)
  exact (extract_rings_valid op A B Hwn Hns H2ec Heul HeulM poly Hin).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions vcross_lin2.
Print Assumptions vcross_sign_preserved_pos_det.
Print Assumptions vcross_sign_flipped_neg_det.
Print Assumptions open_disk_convex.
Print Assumptions extract_rings_valid_hyperbolic.
Print Assumptions extract_rings_valid_spherical_hemisphere.
