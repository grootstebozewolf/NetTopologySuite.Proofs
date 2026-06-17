(* ============================================================================
   NetTopologySuite.Proofs.RelateCurveInscribedGeometry
   ----------------------------------------------------------------------------
   Issue #67 (curve→matrix soundness): the curve geometry's dup-free Phase-3
   image, and its point-set agreement with the linearisation.

   `to_geometry cg n` linearises a CurveGeometry by `chord_approx_ring`, which
   carries a duplicated vertex at every segment join.  `inscribed_geometry cg n`
   is the same geometry built from the DEDUPLICATED inscribed control rings
   (`RelateCurveRingReduction.inscribed_ring`) instead.  Two facts make it the
   form to hand to the Phase-3 overlay / relate machinery:

     - `to_geometry_point_set_eq_inscribed` — for an adjacent curve geometry the
       two have the SAME point-set (so any point-set-level overlay/relate fact
       about the inscribed geometry transfers to the curve geometry verbatim);
     - `inscribed_geometry_{outer,hole}_ring_closed` — for a valid curve geometry
       every ring of the inscribed geometry is a `ring_closed` Phase-3 ring, with
       no join duplicates (the `valid_polygon` ring-closed conjunct, cleaner than
       the linearisation's).

   All `Qed`; no new `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Setoid.
From NTS.Proofs Require Import Distance Overlay CurveGeometry
  RelateCurveRingReduction.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The dup-free Phase-3 image of a curve geometry.                         *)
(* -------------------------------------------------------------------------- *)

Definition inscribed_geometry (cg : CurveGeometry) (n : nat) : Geometry :=
  map (fun cp => mkPolygon
                   (inscribed_ring (curve_outer cp) n)
                   (map (fun h => inscribed_ring h n) (curve_holes cp)))
      cg.

(* Membership in one inscribed polygon, unfolded to the per-hole form. *)
Lemma point_in_inscribed_polygon_iff :
  forall (cp : CurvePolygon) (n : nat) (p : Point),
    point_in_polygon p
      (mkPolygon (inscribed_ring (curve_outer cp) n)
                 (map (fun h => inscribed_ring h n) (curve_holes cp)))
    <-> point_in_ring p (inscribed_ring (curve_outer cp) n)
        /\ (forall h0, In h0 (curve_holes cp)
                       -> ~ point_in_ring p (inscribed_ring h0 n)).
Proof.
  intros cp n p. unfold point_in_polygon. cbn [outer_ring hole_rings]. split.
  - intros [Hout Hh]. split; [ exact Hout | ].
    intros h0 Hin0.
    exact (Hh (inscribed_ring h0 n)
              (in_map (fun h => inscribed_ring h n) (curve_holes cp) h0 Hin0)).
  - intros [Hout Hh]. split; [ exact Hout | ].
    intros h Hin. apply in_map_iff in Hin. destruct Hin as [h0 [Heq Hin0]]. subst h.
    exact (Hh h0 Hin0).
Qed.

Theorem point_in_inscribed_geometry_iff :
  forall (cg : CurveGeometry) (n : nat) (p : Point),
    point_set (inscribed_geometry cg n) p
    <-> exists cp, In cp cg
         /\ point_in_ring p (inscribed_ring (curve_outer cp) n)
         /\ (forall h0, In h0 (curve_holes cp)
                        -> ~ point_in_ring p (inscribed_ring h0 n)).
Proof.
  intros cg n p. unfold point_set, inscribed_geometry. split.
  - intros [poly [Hin Hpip]].
    apply in_map_iff in Hin. destruct Hin as [cp [Heq Hincp]]. subst poly.
    exists cp. split; [ exact Hincp | ].
    exact (proj1 (point_in_inscribed_polygon_iff cp n p) Hpip).
  - intros [cp [Hincp Hmem]].
    exists (mkPolygon (inscribed_ring (curve_outer cp) n)
                      (map (fun h => inscribed_ring h n) (curve_holes cp))).
    split.
    + apply in_map_iff. exists cp. split; [ reflexivity | exact Hincp ].
    + exact (proj2 (point_in_inscribed_polygon_iff cp n p) Hmem).
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Point-set agreement with the linearisation (the overlay bridge).        *)
(* -------------------------------------------------------------------------- *)

Theorem to_geometry_point_set_eq_inscribed :
  forall (cg : CurveGeometry) (n : nat) (p : Point),
    Forall curve_polygon_adjacent cg ->
    (point_set (to_geometry cg n) p <-> point_set (inscribed_geometry cg n) p).
Proof.
  intros cg n p Hadj.
  rewrite (point_in_curve_geometry_iff_inscribed cg n p Hadj).
  rewrite (point_in_inscribed_geometry_iff cg n p).
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The inscribed geometry's rings are closed (no join duplicates).         *)
(* -------------------------------------------------------------------------- *)

Theorem inscribed_geometry_outer_ring_closed :
  forall (cg : CurveGeometry) (n : nat) (cp : CurvePolygon),
    valid_curve_geometry cg -> In cp cg ->
    ring_closed (inscribed_ring (curve_outer cp) n).
Proof.
  intros cg n cp Hcg Hin.
  unfold valid_curve_geometry in Hcg. rewrite Forall_forall in Hcg.
  destruct (Hcg cp Hin) as [[_ [_ Hclosed]] _].
  apply inscribed_ring_closed. exact Hclosed.
Qed.

Theorem inscribed_geometry_hole_ring_closed :
  forall (cg : CurveGeometry) (n : nat) (cp : CurvePolygon) (h : CurveRing),
    valid_curve_geometry cg -> In cp cg -> In h (curve_holes cp) ->
    ring_closed (inscribed_ring h n).
Proof.
  intros cg n cp h Hcg Hin Hinh.
  unfold valid_curve_geometry in Hcg. rewrite Forall_forall in Hcg.
  destruct (Hcg cp Hin) as [_ Hholes].
  rewrite Forall_forall in Hholes.
  destruct (Hholes h Hinh) as [_ [_ Hclosed]].
  apply inscribed_ring_closed. exact Hclosed.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Relate payoff: set-level Intersects / Disjoint transfer to Phase-3.      *)
(*                                                                            *)
(* The OGC Intersects / Disjoint predicates are point-set defined, and a curve  *)
(* geometry's point-set equals its inscribed image's (§2), so deciding either   *)
(* predicate between curve geometries IS deciding it between the dup-free       *)
(* Phase-3 inscribed geometries — where the existing point-in-ring machinery    *)
(* applies.  (Defined locally over `point_set`; standard OGC set semantics.)    *)
(* -------------------------------------------------------------------------- *)

Definition geom_intersects (g1 g2 : Geometry) : Prop :=
  exists p, point_set g1 p /\ point_set g2 p.

Definition geom_disjoint (g1 g2 : Geometry) : Prop :=
  forall p, ~ (point_set g1 p /\ point_set g2 p).

Theorem curve_intersects_iff_inscribed :
  forall (A B : CurveGeometry) (n : nat),
    Forall curve_polygon_adjacent A -> Forall curve_polygon_adjacent B ->
    (geom_intersects (to_geometry A n) (to_geometry B n)
     <-> geom_intersects (inscribed_geometry A n) (inscribed_geometry B n)).
Proof.
  intros A B n HA HB. unfold geom_intersects. split.
  - intros [p [HpA HpB]]. exists p. split.
    + exact (proj1 (to_geometry_point_set_eq_inscribed A n p HA) HpA).
    + exact (proj1 (to_geometry_point_set_eq_inscribed B n p HB) HpB).
  - intros [p [HpA HpB]]. exists p. split.
    + exact (proj2 (to_geometry_point_set_eq_inscribed A n p HA) HpA).
    + exact (proj2 (to_geometry_point_set_eq_inscribed B n p HB) HpB).
Qed.

Theorem curve_disjoint_iff_inscribed :
  forall (A B : CurveGeometry) (n : nat),
    Forall curve_polygon_adjacent A -> Forall curve_polygon_adjacent B ->
    (geom_disjoint (to_geometry A n) (to_geometry B n)
     <-> geom_disjoint (inscribed_geometry A n) (inscribed_geometry B n)).
Proof.
  intros A B n HA HB. unfold geom_disjoint. split.
  - intros H p [HpA HpB]. apply (H p). split.
    + exact (proj2 (to_geometry_point_set_eq_inscribed A n p HA) HpA).
    + exact (proj2 (to_geometry_point_set_eq_inscribed B n p HB) HpB).
  - intros H p [HpA HpB]. apply (H p). split.
    + exact (proj1 (to_geometry_point_set_eq_inscribed A n p HA) HpA).
    + exact (proj1 (to_geometry_point_set_eq_inscribed B n p HB) HpB).
Qed.

(* Within / Contains are subset predicates over the point-sets, so they transfer
   the same way (A Within B = A's points all lie in B; A Contains B = B Within A). *)
Definition geom_within (g1 g2 : Geometry) : Prop :=
  forall p, point_set g1 p -> point_set g2 p.

Definition geom_contains (g1 g2 : Geometry) : Prop := geom_within g2 g1.

Theorem curve_within_iff_inscribed :
  forall (A B : CurveGeometry) (n : nat),
    Forall curve_polygon_adjacent A -> Forall curve_polygon_adjacent B ->
    (geom_within (to_geometry A n) (to_geometry B n)
     <-> geom_within (inscribed_geometry A n) (inscribed_geometry B n)).
Proof.
  intros A B n HA HB. unfold geom_within. split.
  - intros H p HiA.
    exact (proj1 (to_geometry_point_set_eq_inscribed B n p HB)
             (H p (proj2 (to_geometry_point_set_eq_inscribed A n p HA) HiA))).
  - intros H p HtA.
    exact (proj2 (to_geometry_point_set_eq_inscribed B n p HB)
             (H p (proj1 (to_geometry_point_set_eq_inscribed A n p HA) HtA))).
Qed.

Theorem curve_contains_iff_inscribed :
  forall (A B : CurveGeometry) (n : nat),
    Forall curve_polygon_adjacent A -> Forall curve_polygon_adjacent B ->
    (geom_contains (to_geometry A n) (to_geometry B n)
     <-> geom_contains (inscribed_geometry A n) (inscribed_geometry B n)).
Proof.
  intros A B n HA HB. unfold geom_contains.
  exact (curve_within_iff_inscribed B A n HB HA).
Qed.

(* Equals is point-set equality (faithful to OGC Equals); it transfers too. *)
Definition geom_equals (g1 g2 : Geometry) : Prop :=
  forall p, point_set g1 p <-> point_set g2 p.

Theorem curve_equals_iff_inscribed :
  forall (A B : CurveGeometry) (n : nat),
    Forall curve_polygon_adjacent A -> Forall curve_polygon_adjacent B ->
    (geom_equals (to_geometry A n) (to_geometry B n)
     <-> geom_equals (inscribed_geometry A n) (inscribed_geometry B n)).
Proof.
  intros A B n HA HB. unfold geom_equals. split; intros H p;
    pose proof (to_geometry_point_set_eq_inscribed A n p HA) as IA;
    pose proof (to_geometry_point_set_eq_inscribed B n p HB) as IB;
    pose proof (H p) as Hp; tauto.
Qed.

(* Set-theoretic CORE of Overlaps: the geometries meet, but neither is within the
   other.  Full OGC Overlaps additionally constrains the DIMENSION of the
   intersection (equal-dimension inputs, same-dimension meet) — and Crosses is
   likewise dimension-aware — which the point-set model does not express.  Only
   the dimension-free core is stated here; it transfers via the Intersects /
   Within transfers above.  Crosses / full Overlaps await a dimension predicate. *)
Definition geom_overlaps_core (g1 g2 : Geometry) : Prop :=
  geom_intersects g1 g2 /\ ~ geom_within g1 g2 /\ ~ geom_within g2 g1.

Theorem curve_overlaps_core_iff_inscribed :
  forall (A B : CurveGeometry) (n : nat),
    Forall curve_polygon_adjacent A -> Forall curve_polygon_adjacent B ->
    (geom_overlaps_core (to_geometry A n) (to_geometry B n)
     <-> geom_overlaps_core (inscribed_geometry A n) (inscribed_geometry B n)).
Proof.
  intros A B n HA HB. unfold geom_overlaps_core.
  rewrite (curve_intersects_iff_inscribed A B n HA HB).
  rewrite (curve_within_iff_inscribed A B n HA HB).
  rewrite (curve_within_iff_inscribed B A n HB HA).
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions to_geometry_point_set_eq_inscribed.
Print Assumptions inscribed_geometry_outer_ring_closed.
Print Assumptions inscribed_geometry_hole_ring_closed.
Print Assumptions curve_intersects_iff_inscribed.
Print Assumptions curve_disjoint_iff_inscribed.
Print Assumptions curve_within_iff_inscribed.
Print Assumptions curve_contains_iff_inscribed.
Print Assumptions curve_equals_iff_inscribed.
Print Assumptions curve_overlaps_core_iff_inscribed.
