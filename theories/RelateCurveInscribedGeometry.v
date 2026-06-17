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

From Stdlib Require Import Reals List.
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

(* -------------------------------------------------------------------------- *)
(* §5  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions to_geometry_point_set_eq_inscribed.
Print Assumptions inscribed_geometry_outer_ring_closed.
Print Assumptions inscribed_geometry_hole_ring_closed.
Print Assumptions curve_intersects_iff_inscribed.
Print Assumptions curve_disjoint_iff_inscribed.
