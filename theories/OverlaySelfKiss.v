(* ============================================================================
   NetTopologySuite.Proofs.OverlaySelfKiss
   ----------------------------------------------------------------------------
   G1 (CAP self, A ∩ A = A) is orthogonal to self-kiss (V1 pinch / figure-8).

   Self-kiss ≠ G1.  Two non-adjacent pieces of ∂A meet; the local open
   side-interiors stay disjoint.  That is not A ∩ A = A, and it is not
   “A kiss A” as existence.

   kiss (two-body T) ≠ self-kiss.  OverlayTouchRow's TOUCH / T_cap_not_2cell
   is the two-body sibling (A ∩ B pinches).  This cut is the one-body
   anti-collapse: a single figure-8 body can satisfy G1 and still pinch.

   Not CircGamma.  Not OverlayNGCurve wire.  Not a curved-polygon noding
   campaign.

   Qed package (concrete combinatorial witness):

     1. G1 holds on the fixture body (point-set CAP self).
     2. Self-kiss is present under the narrow Prop [self_kiss_vertex]:
        two non-adjacent ring edges share a vertex (the pinch).
     3. Anti-collapse: G1 does not imply absence of self-kiss
        ([G1_ne_selfkiss] / [g1_does_not_forbid_selfkiss]).

   The general Jordan / CurvePolygon self-kiss lift (two non-adjacent
   pieces of a possibly circular ∂A meet, open wedges disjoint) is the
   named QEX obligation [curved_polygon_selfkiss_qex] — domain +
   conclusion, not a flag, not discharged.

   Fixture: two CCW triangles sharing exactly the origin, otherwise
   disjoint open interiors, walked as one closed ring (figure-8 / bowtie).
   Same pinch vertex as JCT_Counterexample.bowtie; right-lobe order is
   CCW here.  The ring is [ring_simple] yet not [ring_vertices_distinct]
   — injectivity is a separate premise (Overlay.v).

   Pure-R.  Overlay + Distance + Orientation only.  No atan2, no Classic,
   no Admitted / Axiom / Parameter.

   WITNESS topic: overlay · claimId: ov-g1-ne-selfkiss · witness: figure8-bowtie
   board: OverlayNGCurve / G-family

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List.
From NTS.Proofs Require Import Distance Overlay Orientation.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Narrow self-kiss Prop (combinatorial; not a Jordan curve predicate).   *)
(* -------------------------------------------------------------------------- *)

Definition edge_incident (e : Edge) (v : Point) : Prop :=
  fst e = v \/ snd e = v.

(** Walk-successor pairs of a (possibly open) edge list. *)
Fixpoint adjacent_pairs (es : list Edge) : list (Edge * Edge) :=
  match es with
  | a :: rest =>
      match rest with
      | b :: _ => (a, b) :: adjacent_pairs rest
      | nil => nil
      end
  | nil => nil
  end.

(** Closing corner: last edge followed by first. *)
Definition wrap_pair (es : list Edge) : option (Edge * Edge) :=
  match es with
  | a :: rest =>
      match rev rest with
      | b :: _ => Some (b, a)
      | nil => None
      end
  | nil => None
  end.

(** Consecutive along the cyclic edge list, including wrap last→first. *)
Definition consecutive_ring_edges (r : Ring) (e1 e2 : Edge) : Prop :=
  In (e1, e2) (adjacent_pairs (ring_edges r)) \/
  wrap_pair (ring_edges r) = Some (e1, e2).

(** Pinch: two non-adjacent pieces of the boundary meet at [v]. *)
Definition self_kiss_vertex (r : Ring) (v : Point) : Prop :=
  exists e1 e2 : Edge,
    In e1 (ring_edges r) /\
    In e2 (ring_edges r) /\
    e1 <> e2 /\
    ~ consecutive_ring_edges r e1 e2 /\
    ~ consecutive_ring_edges r e2 e1 /\
    edge_incident e1 v /\
    edge_incident e2 v.

Definition geometry_self_kiss (A : Geometry) : Prop :=
  exists poly v,
    In poly A /\ self_kiss_vertex (outer_ring poly) v.

(** G1 on a Geometry: point-set CAP self (Overlay.boolean_op_intersection_self). *)
Definition g1_cap_self_geom (A : Geometry) : Prop :=
  forall p, boolean_op Intersection A A p <-> point_set A p.

(* -------------------------------------------------------------------------- *)
(* §2  Figure-8 fixture — two CCW triangles glued at the origin.              *)
(*                                                                            *)
(*   Triangle R:  (0,0) -> (1,-1) -> (1, 1) -> (0,0)                          *)
(*   Triangle L:  (0,0) -> (-1,1) -> (-1,-1) -> (0,0)                         *)
(*                                                                            *)
(* Walked as one ring: the origin is visited as closer, pinch, and closer.    *)
(* -------------------------------------------------------------------------- *)

Definition figure8_ring : Ring :=
  mkPoint 0 0
    :: mkPoint 1 (-1) :: mkPoint 1 1
    :: mkPoint 0 0
    :: mkPoint (-1) 1 :: mkPoint (-1) (-1)
    :: mkPoint 0 0 :: nil.

Definition figure8_pinch : Point := mkPoint 0 0.

Definition figure8_poly : Polygon := mkPolygon figure8_ring nil.

Definition figure8_geom : Geometry := [figure8_poly].

Definition figure8_eR : Edge := (mkPoint 0 0, mkPoint 1 (-1)).
Definition figure8_eL : Edge := (mkPoint 0 0, mkPoint (-1) 1).

Lemma figure8_ring_edges :
  ring_edges figure8_ring =
       figure8_eR
    :: (mkPoint 1 (-1), mkPoint 1 1)
    :: (mkPoint 1 1,    mkPoint 0 0)
    :: figure8_eL
    :: (mkPoint (-1) 1, mkPoint (-1) (-1))
    :: (mkPoint (-1) (-1), mkPoint 0 0)
    :: nil.
Proof. reflexivity. Qed.

Lemma figure8_right_ccw :
  0 < cross (mkPoint 0 0) (mkPoint 1 (-1)) (mkPoint 1 1).
Proof. unfold cross; cbn [px py]; lra. Qed.

Lemma figure8_left_ccw :
  0 < cross (mkPoint 0 0) (mkPoint (-1) 1) (mkPoint (-1) (-1)).
Proof. unfold cross; cbn [px py]; lra. Qed.

Lemma figure8_ring_closed : ring_closed figure8_ring.
Proof.
  exists (mkPoint 0 0),
    [mkPoint 1 (-1); mkPoint 1 1; mkPoint 0 0;
     mkPoint (-1) 1; mkPoint (-1) (-1)].
  reflexivity.
Qed.

Lemma figure8_min_points : ring_has_minimum_points figure8_ring.
Proof. unfold ring_has_minimum_points, figure8_ring. simpl. lia. Qed.

(* [ring_simple] forbids only proper (interior-interior) crossings.  The
   lobes meet only at the origin, an endpoint of every incident edge. *)
Lemma figure8_ring_simple : ring_simple figure8_ring.
Proof.
  intros e1 e2 H1 H2 Hne Hcross.
  rewrite figure8_ring_edges in H1, H2.
  simpl in H1, H2.
  destruct Hcross as [t [s [[Ht0 Ht1] [[Hs0 Hs1] [Hx Hy]]]]].
  destruct H1 as [E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]];
  destruct H2 as [E2|[E2|[E2|[E2|[E2|[E2|[]]]]]]];
    subst e1 e2; simpl in Hx, Hy, Hne;
    try (exfalso; apply Hne; reflexivity);
    nra.
Qed.

Lemma figure8_not_injective : ~ ring_vertices_distinct figure8_ring.
Proof.
  unfold ring_vertices_distinct, figure8_ring. simpl.
  intro H. apply NoDup_cons_iff in H. destruct H as [Hnin _].
  apply Hnin. right. right. left. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Open wedges at the pinch are nonempty and disjoint (no atan2).         *)
(* -------------------------------------------------------------------------- *)

(** Open right lobe: between y = −x, y = x and x = 1 (x > 0). *)
Definition figure8_right_open (p : Point) : Prop :=
  0 < px p + py p /\ px p < 1 /\ py p < px p.

(** Open left lobe: between y = x, y = −x and x = −1 (x < 0). *)
Definition figure8_left_open (p : Point) : Prop :=
  px p + py p < 0 /\ -1 < px p /\ px p < py p.

Lemma figure8_right_open_inhabited : figure8_right_open (mkPoint (1 / 2) 0).
Proof. unfold figure8_right_open; cbn [px py]; lra. Qed.

Lemma figure8_left_open_inhabited : figure8_left_open (mkPoint (-1 / 2) 0).
Proof. unfold figure8_left_open; cbn [px py]; lra. Qed.

Lemma figure8_open_wedges_disjoint :
  forall p, ~ (figure8_right_open p /\ figure8_left_open p).
Proof.
  intros p [[Hr _] [Hl _]]. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The pinch is a [self_kiss_vertex].                                     *)
(* -------------------------------------------------------------------------- *)

Lemma figure8_eR_in : In figure8_eR (ring_edges figure8_ring).
Proof. rewrite figure8_ring_edges. simpl. tauto. Qed.

Lemma figure8_eL_in : In figure8_eL (ring_edges figure8_ring).
Proof. rewrite figure8_ring_edges. simpl. tauto. Qed.

Lemma figure8_eR_ne_eL : figure8_eR <> figure8_eL.
Proof.
  intros H. injection H as _ Hy. inversion Hy. lra.
Qed.

Lemma figure8_adjacent_pairs :
  adjacent_pairs (ring_edges figure8_ring) =
    (figure8_eR, (mkPoint 1 (-1), mkPoint 1 1))
    :: ((mkPoint 1 (-1), mkPoint 1 1), (mkPoint 1 1, mkPoint 0 0))
    :: ((mkPoint 1 1, mkPoint 0 0), figure8_eL)
    :: (figure8_eL, (mkPoint (-1) 1, mkPoint (-1) (-1)))
    :: ((mkPoint (-1) 1, mkPoint (-1) (-1)), (mkPoint (-1) (-1), mkPoint 0 0))
    :: nil.
Proof. rewrite figure8_ring_edges. simpl. reflexivity. Qed.

Lemma figure8_wrap_pair :
  wrap_pair (ring_edges figure8_ring) =
    Some ((mkPoint (-1) (-1), mkPoint 0 0), figure8_eR).
Proof. rewrite figure8_ring_edges. simpl. reflexivity. Qed.

Ltac contra_pair H :=
  injection H; intros;
  repeat match goal with
  | H : figure8_eR = figure8_eL |- _ => apply figure8_eR_ne_eL in H; contradiction
  | H : figure8_eL = figure8_eR |- _ =>
      apply figure8_eR_ne_eL; symmetry; exact H
  | H : (?a, ?b) = (?c, ?d) |- _ => injection H; intros; clear H
  | H : mkPoint _ _ = mkPoint _ _ |- _ => inversion H; subst
  end;
  cbn in *; exfalso; lra.

Lemma figure8_eR_eL_not_consecutive :
  ~ consecutive_ring_edges figure8_ring figure8_eR figure8_eL.
Proof.
  intros [Hin | Hwrap].
  - rewrite figure8_adjacent_pairs in Hin.
    simpl in Hin.
    destruct Hin as [H | [H | [H | [H | [H | []]]]]]; contra_pair H.
  - rewrite figure8_wrap_pair in Hwrap.
    unfold figure8_eR, figure8_eL in Hwrap.
    inversion Hwrap.
    cbn in *; lra.
Qed.

Lemma figure8_eL_eR_not_consecutive :
  ~ consecutive_ring_edges figure8_ring figure8_eL figure8_eR.
Proof.
  intros [Hin | Hwrap].
  - rewrite figure8_adjacent_pairs in Hin.
    simpl in Hin.
    destruct Hin as [H | [H | [H | [H | [H | []]]]]]; contra_pair H.
  - rewrite figure8_wrap_pair in Hwrap.
    unfold figure8_eR, figure8_eL in Hwrap.
    inversion Hwrap.
    cbn in *; lra.
Qed.

Lemma figure8_self_kiss_vertex :
  self_kiss_vertex figure8_ring figure8_pinch.
Proof.
  exists figure8_eR, figure8_eL.
  repeat split.
  - apply figure8_eR_in.
  - apply figure8_eL_in.
  - apply figure8_eR_ne_eL.
  - apply figure8_eR_eL_not_consecutive.
  - apply figure8_eL_eR_not_consecutive.
  - unfold edge_incident, figure8_eR, figure8_pinch. left. reflexivity.
  - unfold edge_incident, figure8_eL, figure8_pinch. left. reflexivity.
Qed.

Lemma figure8_geometry_self_kiss : geometry_self_kiss figure8_geom.
Proof.
  exists figure8_poly, figure8_pinch.
  split.
  - simpl. left. reflexivity.
  - apply figure8_self_kiss_vertex.
Qed.

Lemma figure8_valid_polygon : valid_polygon figure8_poly.
Proof.
  unfold valid_polygon, figure8_poly. simpl.
  split; [apply figure8_ring_closed |].
  split; [apply figure8_ring_simple |].
  split; [apply figure8_min_points |].
  intros h Hin. simpl in Hin. contradiction.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  G1 on the same body, and the anti-collapse.                            *)
(* -------------------------------------------------------------------------- *)

Lemma figure8_g1 : g1_cap_self_geom figure8_geom.
Proof. intros p. apply boolean_op_intersection_self. Qed.

(* WITNESS {"claimId":"ov-g1-ne-selfkiss","topic":"overlay","lemma":"G1_ne_selfkiss","title":"G1 (CAP self) does not forbid self-kiss; figure-8 pinch witness","witness":"figure8-bowtie","board":"OverlayNGCurve / G-family"} *)

(** HEADLINE.  There is a geometry on which G1 holds and a self-kiss
    pinch is present.  G1 is point-set algebra and does not constrain
    boundary injectivity. *)
Theorem G1_ne_selfkiss :
  exists A : Geometry,
    g1_cap_self_geom A /\ geometry_self_kiss A.
Proof.
  exists figure8_geom.
  split; [apply figure8_g1 | apply figure8_geometry_self_kiss].
Qed.

(** Equivalent: refute “G1 ⇒ ¬self_kiss”. *)
Theorem g1_does_not_forbid_selfkiss :
  ~ (forall A : Geometry,
       g1_cap_self_geom A -> ~ geometry_self_kiss A).
Proof.
  intros H.
  apply (H figure8_geom figure8_g1 figure8_geometry_self_kiss).
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Named QEX — general CurvePolygon / Jordan self-kiss lift.              *)
(*                                                                            *)
(* Domain: a Jordan-style self-kiss predicate [self_kiss_cp] on geometries    *)
(* whose boundary may carry circular rings (SQL/MM CurvePolygon): two         *)
(* non-adjacent pieces of ∂A meet, and the open side-interiors at the         *)
(* meeting stay disjoint.                                                     *)
(*                                                                            *)
(* Conclusion: on this fixture that predicate agrees with the combinatorial   *)
(* specialisation [self_kiss_vertex] plus disjoint open wedges.               *)
(*                                                                            *)
(* Not CircGamma (no arc interpolant).  Not two-body [disks_touch].           *)
(* Not discharged: the corpus has no CP self-kiss predicate.                  *)
(* -------------------------------------------------------------------------- *)

Definition curved_polygon_selfkiss_qex (self_kiss_cp : Geometry -> Prop) : Prop :=
  self_kiss_cp figure8_geom <->
    (self_kiss_vertex figure8_ring figure8_pinch /\
     (forall p, ~ (figure8_right_open p /\ figure8_left_open p))).

(* -------------------------------------------------------------------------- *)
(* §7  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions figure8_g1.
Print Assumptions figure8_self_kiss_vertex.
Print Assumptions figure8_open_wedges_disjoint.
Print Assumptions figure8_ring_simple.
Print Assumptions figure8_not_injective.
Print Assumptions figure8_valid_polygon.
Print Assumptions G1_ne_selfkiss.
Print Assumptions g1_does_not_forbid_selfkiss.
