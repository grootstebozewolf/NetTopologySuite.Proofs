(* ============================================================================
   NetTopologySuite.Proofs.RelateCurveMatrix
   ----------------------------------------------------------------------------
   Issue #64 / JTS #1195 §7 (R-PR / CURVE_RELATE_MATRIX): the point-set DE-9IM
   SPECIFICATION + provable algebraic laws backing the `CURVE_RELATE_MATRIX`
   oracle mode, which COMPUTES a full 9-cell DE-9IM intersection matrix from two
   curve geometries (the existing `RELATE_MATRIX` / `RELATE_PREDICATE` modes only
   EVALUATE a supplied / cataloged matrix).  The direct generalization of the
   merged `HOLES_DISJOINT` (proofs#234): from a two-ring disjoint / nesting
   classifier to a full two-geometry matrix.

   TRUE OGC convention.  The matrix the oracle emits is the genuine geometric
   DE-9IM: two disjoint areal geometries -> "FF2FF1212" (IE=EI=2, BE=EB=1, EE=2),
   A-contains-B -> "212FF1FF2", overlap -> "212101212".  This makes the EE-always-
   nonempty law genuinely true.  NOTE: the repo's `DE9IM.v` `pat_disjoint`
   ("FF*FF*FF*", forcing EI=EB=F) and the `relate_matrix.ml` "FFFFFFFFF" pins are
   the OLDER non-OGC simplification and do NOT match the true matrix; this file
   uses a locally-defined OGC `pat_disjoint_ogc` ("FF*FF****") for the disjoint
   characterization and states the distinction openly.  The OGC-robust predicates
   (contains / overlaps / touches / intersects) agree with the repo patterns and
   are exhibited as constant witnesses.

   Honesty posture (same as POINT_IN_CURVE_RING / RING_ORIENTATION /
   HOLES_DISJOINT): this file proves a point-set / linearization-bridge DE-9IM
   *specification* (a Prop relating a matrix to the two geometries via existence
   of points in each stratum-intersection) PLUS its provable algebraic laws
   (well-formedness, exteriors-always-meet => EE nonempty, transpose-under-swap,
   the interior/boundary-meet "disjoint" characterization, partial
   disjoint/intersects consistency, and curated OGC witness matrices).  The
   topological "computed cell DIMENSION = true point-set dimension" correctness
   (the overlay-shaped II=2 part) is the deferred frontier, pinned by the
   adversarial oracle suite -- the only credible posture, as the proofs repo has
   no arc-aware overlay / noding of its own.

   Works over the point-set bridge (`RelateCurveRingReduction.v`) + the matrix
   algebra (`DE9IM.v`); no transcendental analysis, so no `Classical_Prop.classic`
   / `sin_lt_x`.  THREE-AXIOM (verified by `Print Assumptions` below).

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import List Reals Lra Lia.
From NTS.Proofs Require Import Distance Overlay CurveGeometry DE9IM Segment
  RelateCurveRingReduction.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  EE-always-nonempty: two bounded areal geometries have meeting exteriors.*)
(*                                                                            *)
(* The one analytic fact the laws need.  A LINEARISED `Geometry` is a finite   *)
(* list of polygons with finite vertex lists; a point whose y-coordinate       *)
(* exceeds every ring vertex's y crosses no ring edge (the rightward-ray       *)
(* crossing predicate needs a vertex strictly above), so it is outside every   *)
(* ring, hence in no polygon -- exterior to the whole geometry.  No arc-bulge   *)
(* vertex bound is needed: we take the max over the ACTUAL finite vertex list.  *)
(* -------------------------------------------------------------------------- *)

(* Any finite list of reals has an upper bound. *)
Lemma reals_have_ub : forall l : list R, exists b, forall y, In y l -> y <= b.
Proof.
  induction l as [| x xs IH].
  - exists 0. intros y [].
  - destruct IH as [b Hb]. exists (Rmax x b). intros y [Hy | Hy].
    + subst y. apply Rmax_l.
    + eapply Rle_trans; [ apply Hb; exact Hy | apply Rmax_r ].
Qed.

(* All ring-vertex y-coordinates of a geometry (a finite list). *)
Definition geom_ys (g : Geometry) : list R :=
  flat_map (fun poly =>
              flat_map (fun r => map py r) (outer_ring poly :: hole_rings poly))
           g.

Lemma vertex_py_in_geom_ys :
  forall (g : Geometry) poly r v,
    In poly g ->
    In r (outer_ring poly :: hole_rings poly) ->
    In v r ->
    In (py v) (geom_ys g).
Proof.
  intros g poly r v Hp Hr Hv. unfold geom_ys.
  apply in_flat_map. exists poly. split; [ exact Hp | ].
  apply in_flat_map. exists r. split; [ exact Hr | ].
  apply in_map; exact Hv.
Qed.

(* Both endpoints of an edge of a ring are vertices of that ring. *)
Lemma ring_edges_endpoints_in :
  forall (r : Ring) (e : Edge),
    In e (ring_edges r) -> In (fst e) r /\ In (snd e) r.
Proof.
  induction r as [| a r' IH]; intros e He.
  - inversion He.
  - destruct r' as [| b r'']; simpl in He.
    + inversion He.
    + destruct He as [Heq | Hin].
      * subst e; simpl. split; [ left; reflexivity | right; left; reflexivity ].
      * destruct (IH e Hin) as [H1 H2]. split; right; assumption.
Qed.

(* A point strictly above both endpoints of an edge does not cross it. *)
Lemma edge_not_cross_above :
  forall (p a b : Point), py a < py p -> py b < py p -> ~ edge_crosses_ray p (a, b).
Proof.
  intros p a b Ha Hb H. unfold edge_crosses_ray in H.
  destruct H as [ [[H1 H2] _] | [[H1 H2] _] ]; lra.
Qed.

(* No edge crossed => parity is not odd. *)
Lemma no_cross_not_odd :
  forall (p : Point) (es : list Edge),
    (forall e, In e es -> ~ edge_crosses_ray p e) ->
    ~ ray_parity_odd p es.
Proof.
  intros p es; induction es as [| e es' IH]; intros Hnc Hodd.
  - inversion Hodd.
  - inversion Hodd; subst.
    + eapply Hnc; [ left; reflexivity | eassumption ].
    + eapply IH; [ | eassumption ]. intros e0 H0. apply Hnc. right; exact H0.
Qed.

(* A point above every ring vertex is outside the ring. *)
Lemma above_all_not_in_ring :
  forall (p : Point) (r : Ring) (b : R),
    (forall v, In v r -> py v <= b) -> b < py p -> ~ point_in_ring p r.
Proof.
  intros p r b Hb Hp. unfold point_in_ring.
  apply no_cross_not_odd. intros e He.
  destruct (ring_edges_endpoints_in r e He) as [Hin1 Hin2].
  destruct e as [a c]; simpl in Hin1, Hin2.
  apply edge_not_cross_above.
  - eapply Rle_lt_trans; [ apply Hb; exact Hin1 | exact Hp ].
  - eapply Rle_lt_trans; [ apply Hb; exact Hin2 | exact Hp ].
Qed.

(* The headline boundedness fact: ANY two linearised geometries have a common
   exterior point (their exteriors meet -- the EE=2-class witness). *)
Theorem two_geometries_exterior_meet :
  forall A B : Geometry, exists p, ~ point_set A p /\ ~ point_set B p.
Proof.
  intros A B.
  destruct (reals_have_ub (geom_ys A ++ geom_ys B)) as [b Hb].
  exists (mkPoint 0 (b + 1)).
  assert (Hpy : b < py (mkPoint 0 (b + 1))) by (simpl; lra).
  split; intro Hin; destruct Hin as [poly [Hpoly [Houter _]]].
  - apply (above_all_not_in_ring (mkPoint 0 (b + 1)) (outer_ring poly) b);
      [ | exact Hpy | exact Houter ].
    intros v Hv. apply Hb. apply in_or_app. left.
    eapply vertex_py_in_geom_ys; [ exact Hpoly | left; reflexivity | exact Hv ].
  - apply (above_all_not_in_ring (mkPoint 0 (b + 1)) (outer_ring poly) b);
      [ | exact Hpy | exact Houter ].
    intros v Hv. apply Hb. apply in_or_app. right.
    eapply vertex_py_in_geom_ys; [ exact Hpoly | left; reflexivity | exact Hv ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Point-set DE-9IM specification (the bridge layer).                      *)
(*                                                                            *)
(* Three strata of a LINEARISED geometry; the boundary stratum is only needed  *)
(* to make the matrix full -- the proven laws use only interior / exterior.    *)
(* -------------------------------------------------------------------------- *)

Inductive Stratum : Type := SInt | SBnd | SExt.

(* Edges of a polygon = its outer-ring edges plus every hole-ring's edges. *)
Definition poly_edges (poly : Polygon) : list Edge :=
  ring_edges (outer_ring poly) ++ flat_map ring_edges (hole_rings poly).

Definition on_edge (p : Point) (e : Edge) : Prop := between (fst e) (snd e) p.

Definition geom_boundary (g : Geometry) (p : Point) : Prop :=
  exists poly, In poly g /\ exists e, In e (poly_edges poly) /\ on_edge p e.

Definition in_stratum (s : Stratum) (g : Geometry) (p : Point) : Prop :=
  match s with
  | SInt => point_set g p
  | SExt => ~ point_set g p
  | SBnd => geom_boundary g p
  end.

(* One matrix cell is well-specified: its value is a legal dimension, and it is
   nonempty exactly when the corresponding stratum-intersection is inhabited.
   The exact dimension NUMBER is NOT pinned (deferred / test-pinned). *)
Definition cell_ok (d : DimValue) (sX sY : Stratum) (A B : Geometry) : Prop :=
  dim_value_ok d /\
  (dim_nonempty d <-> exists p, in_stratum sX A p /\ in_stratum sY B p).

(* The full 9-cell specification (row-major II IB IE / BI BB BE / EI EB EE). *)
Definition geom_de9im_pointset (A B : Geometry) (m : IntersectionMatrix) : Prop :=
  cell_ok (im_ii m) SInt SInt A B /\
  cell_ok (im_ib m) SInt SBnd A B /\
  cell_ok (im_ie m) SInt SExt A B /\
  cell_ok (im_bi m) SBnd SInt A B /\
  cell_ok (im_bb m) SBnd SBnd A B /\
  cell_ok (im_be m) SBnd SExt A B /\
  cell_ok (im_ei m) SExt SInt A B /\
  cell_ok (im_eb m) SExt SBnd A B /\
  cell_ok (im_ee m) SExt SExt A B.

(* Curve-geometry wrappers: linearise at parameter n, then the geometry spec. *)
Definition cg_interior (cg : CurveGeometry) (n : nat) (p : Point) : Prop :=
  point_set (to_geometry cg n) p.
Definition cg_exterior (cg : CurveGeometry) (n : nat) (p : Point) : Prop :=
  ~ point_set (to_geometry cg n) p.
Definition cg_boundary (cg : CurveGeometry) (n : nat) (p : Point) : Prop :=
  geom_boundary (to_geometry cg n) p.

Definition curve_de9im_pointset (cgA cgB : CurveGeometry) (n : nat)
    (m : IntersectionMatrix) : Prop :=
  geom_de9im_pointset (to_geometry cgA n) (to_geometry cgB n) m.

(* -------------------------------------------------------------------------- *)
(* §3  Provable algebraic laws.                                               *)
(* -------------------------------------------------------------------------- *)

(* (1) Well-formedness. *)
Theorem geom_de9im_matrix_ok :
  forall A B m, geom_de9im_pointset A B m -> matrix_ok m.
Proof.
  intros A B m H.
  destruct H as [Hii [Hib [Hie [Hbi [Hbb [Hbe [Hei [Heb Hee]]]]]]]].
  unfold matrix_ok. repeat split;
    [ apply (proj1 Hii) | apply (proj1 Hib) | apply (proj1 Hie)
    | apply (proj1 Hbi) | apply (proj1 Hbb) | apply (proj1 Hbe)
    | apply (proj1 Hei) | apply (proj1 Heb) | apply (proj1 Hee) ].
Qed.

(* (2) Exteriors always meet => the EE cell is nonempty (the EE=2 class). *)
Theorem geom_de9im_ee_nonempty :
  forall A B m, geom_de9im_pointset A B m -> im_ee m <> None.
Proof.
  intros A B m H.
  destruct H as [_ [_ [_ [_ [_ [_ [_ [_ [_ Hee]]]]]]]]].
  apply Hee.
  destruct (two_geometries_exterior_meet A B) as [p [HA HB]].
  exists p. split; [ exact HA | exact HB ].
Qed.

(* (3) Transpose under swap (the symmetry headline). *)
Lemma exists_and_comm :
  forall P Q : Point -> Prop,
    (exists p, P p /\ Q p) <-> (exists p, Q p /\ P p).
Proof.
  intros P Q; split; intros [p [H1 H2]]; exists p; split; assumption.
Qed.

(* The swap is an involution, so this single forward implication discharges
   both directions of the transpose iff. *)
Lemma cell_ok_swap_imp :
  forall d sX sY A B, cell_ok d sX sY A B -> cell_ok d sY sX B A.
Proof.
  intros d sX sY A B [Hok Hiff]. split; [ exact Hok | ].
  eapply iff_trans; [ exact Hiff | apply exists_and_comm ].
Qed.

Theorem geom_de9im_pointset_transpose :
  forall A B m,
    geom_de9im_pointset A B m <->
    geom_de9im_pointset B A (matrix_transpose m).
Proof.
  intros A B m. unfold geom_de9im_pointset, matrix_transpose;
    cbn [im_ii im_ib im_ie im_bi im_bb im_be im_ei im_eb im_ee].
  split; intro H;
    repeat match goal with [ HH : _ /\ _ |- _ ] => destruct HH end;
    repeat (split; [ apply cell_ok_swap_imp; assumption | ]);
    apply cell_ok_swap_imp; assumption.
Qed.

(* (4) Disjoint characterization (OGC variant). ----------------------------- *)

(* The OGC "disjoint" pattern: only the four interior/boundary-meet cells are
   F; the exterior row/column is WILD (unlike DE9IM.v's stricter `pat_disjoint`,
   which forces EI=EB=F and so does NOT match a true areal disjoint matrix). *)
Definition pat_disjoint_ogc : IMPattern :=
  {| pat_ii := PFalse; pat_ib := PFalse; pat_ie := PWild;
     pat_bi := PFalse; pat_bb := PFalse; pat_be := PWild;
     pat_ei := PWild;  pat_eb := PWild;  pat_ee := PWild |}.

Definition im_disjoint_ogc (m : IntersectionMatrix) : Prop :=
  matrix_matches pat_disjoint_ogc m.

Definition im_no_ib_meet (m : IntersectionMatrix) : Prop :=
  im_ii m = None /\ im_ib m = None /\ im_bi m = None /\ im_bb m = None.

Lemma im_disjoint_ogc_iff_no_meet :
  forall m, im_disjoint_ogc m <-> im_no_ib_meet m.
Proof.
  intros m. unfold im_disjoint_ogc, im_no_ib_meet, matrix_matches,
    pat_disjoint_ogc; simpl. split.
  - intros (Hii & Hib & _ & Hbi & Hbb & _).
    repeat split;
      [ apply (proj1 (char_false_empty _) Hii)
      | apply (proj1 (char_false_empty _) Hib)
      | apply (proj1 (char_false_empty _) Hbi)
      | apply (proj1 (char_false_empty _) Hbb) ].
  - intros (Hii & Hib & Hbi & Hbb). repeat split; try exact I;
      [ apply (proj2 (char_false_empty _) Hii)
      | apply (proj2 (char_false_empty _) Hib)
      | apply (proj2 (char_false_empty _) Hbi)
      | apply (proj2 (char_false_empty _) Hbb) ].
Qed.

Lemma none_iff_not_nonempty :
  forall d : DimValue, d = None <-> ~ dim_nonempty d.
Proof.
  intros [n |]; unfold dim_nonempty; split; intro H.
  - discriminate.
  - exfalso. apply H. intro Hc. discriminate.
  - intro Hne. apply Hne. reflexivity.
  - reflexivity.
Qed.

Lemma cell_none_iff_empty :
  forall d sX sY A B,
    cell_ok d sX sY A B ->
    (d = None <-> ~ exists p, in_stratum sX A p /\ in_stratum sY B p).
Proof.
  intros d sX sY A B [_ Hiff]. split.
  - intros Hnone Hex. apply (proj2 Hiff) in Hex. apply Hex. exact Hnone.
  - intros Hnex. apply none_iff_not_nonempty. intro Hdn.
    apply Hnex. apply (proj1 Hiff). exact Hdn.
Qed.

(* The interior/boundary-meet cells are all empty exactly when the four
   stratum-intersections (II, IB, BI, BB) are uninhabited. *)
Theorem geom_de9im_no_meet_iff_strata_empty :
  forall A B m,
    geom_de9im_pointset A B m ->
    (im_no_ib_meet m <->
     ((~ exists p, point_set A p /\ point_set B p) /\
      (~ exists p, point_set A p /\ geom_boundary B p) /\
      (~ exists p, geom_boundary A p /\ point_set B p) /\
      (~ exists p, geom_boundary A p /\ geom_boundary B p))).
Proof.
  intros A B m H.
  destruct H as [Hii [Hib [_ [Hbi [Hbb _]]]]].
  pose proof (cell_none_iff_empty _ _ _ _ _ Hii) as Cii.
  pose proof (cell_none_iff_empty _ _ _ _ _ Hib) as Cib.
  pose proof (cell_none_iff_empty _ _ _ _ _ Hbi) as Cbi.
  pose proof (cell_none_iff_empty _ _ _ _ _ Hbb) as Cbb.
  simpl in Cii, Cib, Cbi, Cbb. unfold im_no_ib_meet.
  split.
  - intros (E1 & E2 & E3 & E4). repeat split;
      [ apply (proj1 Cii) | apply (proj1 Cib)
      | apply (proj1 Cbi) | apply (proj1 Cbb) ]; assumption.
  - intros (E1 & E2 & E3 & E4). repeat split;
      [ apply (proj2 Cii) | apply (proj2 Cib)
      | apply (proj2 Cbi) | apply (proj2 Cbb) ]; assumption.
Qed.

Theorem geom_de9im_disjoint_ogc_characterization :
  forall A B m,
    geom_de9im_pointset A B m ->
    (im_disjoint_ogc m <->
     ((~ exists p, point_set A p /\ point_set B p) /\
      (~ exists p, point_set A p /\ geom_boundary B p) /\
      (~ exists p, geom_boundary A p /\ point_set B p) /\
      (~ exists p, geom_boundary A p /\ geom_boundary B p))).
Proof.
  intros A B m H. eapply iff_trans;
    [ apply im_disjoint_ogc_iff_no_meet
    | apply geom_de9im_no_meet_iff_strata_empty; exact H ].
Qed.

(* (5) Honest partial consistency: an OGC-disjoint matrix never matches the
   interior-meet / boundary-meet `intersects` patterns (the same documented
   partial gap as DE9IM.v's `im_disjoint_not_intersects_partial`). *)
Theorem im_disjoint_ogc_not_intersects_partial :
  forall m,
    im_disjoint_ogc m ->
    ~ matrix_matches pat_intersects_0 m /\
    ~ matrix_matches pat_intersects_1 m /\
    ~ matrix_matches pat_intersects_4 m.
Proof.
  intros m H. apply im_disjoint_ogc_iff_no_meet in H.
  destruct H as (Hii & Hib & Hbi & Hbb).
  repeat split; intro Hc; unfold matrix_matches in Hc; simpl in Hc.
  - destruct Hc as [Ht _]. rewrite Hii in Ht. exact Ht.
  - destruct Hc as [_ [Ht _]]. rewrite Hib in Ht. exact Ht.
  - destruct Hc as [_ [_ [_ [_ [Ht _]]]]]. rewrite Hbb in Ht. exact Ht.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Curated TRUE-OGC witness matrices (constant; reflexivity-proved).       *)
(*                                                                            *)
(* These double as the `relate_matrix.ml` catalog literals and the Python      *)
(* suite's I1 expectations.  Each `_witness` is the named OGC-predicate fact.   *)
(* -------------------------------------------------------------------------- *)

(* Two disjoint disks: "FF2FF1212". *)
Definition cm_matrix_disjoint_disks : IntersectionMatrix :=
  {| im_ii := None;   im_ib := None;   im_ie := Some 2%nat;
     im_bi := None;   im_bb := None;   im_be := Some 1%nat;
     im_ei := Some 2%nat; im_eb := Some 1%nat; im_ee := Some 2%nat |}.

Lemma cm_matrix_disjoint_disks_witness :
  im_disjoint_ogc cm_matrix_disjoint_disks /\ matrix_ok cm_matrix_disjoint_disks.
Proof.
  split.
  - unfold im_disjoint_ogc, matrix_matches, pat_disjoint_ogc,
      cm_matrix_disjoint_disks; simpl. repeat split.
  - unfold matrix_ok, cm_matrix_disjoint_disks; simpl. repeat split; (exact I || lia).
Qed.

(* A strictly contains B: "212FF1FF2". *)
Definition cm_matrix_contains_disk : IntersectionMatrix :=
  {| im_ii := Some 2%nat; im_ib := Some 1%nat; im_ie := Some 2%nat;
     im_bi := None;   im_bb := None;   im_be := Some 1%nat;
     im_ei := None;   im_eb := None;   im_ee := Some 2%nat |}.

Lemma cm_matrix_contains_disk_witness :
  im_contains cm_matrix_contains_disk /\ matrix_ok cm_matrix_contains_disk.
Proof.
  split.
  - unfold im_contains, matrix_matches, pat_contains,
      cm_matrix_contains_disk; simpl. repeat split.
  - unfold matrix_ok, cm_matrix_contains_disk; simpl. repeat split; (exact I || lia).
Qed.

(* Two overlapping disks: "212101212". *)
Definition cm_matrix_overlapping_disks : IntersectionMatrix :=
  {| im_ii := Some 2%nat; im_ib := Some 1%nat; im_ie := Some 2%nat;
     im_bi := Some 1%nat; im_bb := Some 0%nat; im_be := Some 1%nat;
     im_ei := Some 2%nat; im_eb := Some 1%nat; im_ee := Some 2%nat |}.

Lemma cm_matrix_overlapping_disks_witness :
  im_overlaps cm_matrix_overlapping_disks /\ matrix_ok cm_matrix_overlapping_disks.
Proof.
  split.
  - left. unfold matrix_matches, pat_overlaps_pp_aa,
      cm_matrix_overlapping_disks; simpl. repeat split.
  - unfold matrix_ok, cm_matrix_overlapping_disks; simpl. repeat split; (exact I || lia).
Qed.

(* Two externally tangent disks (touch at one boundary point): "FF2F01212". *)
Definition cm_matrix_externally_tangent_disks : IntersectionMatrix :=
  {| im_ii := None;   im_ib := None;   im_ie := Some 2%nat;
     im_bi := None;   im_bb := Some 0%nat; im_be := Some 1%nat;
     im_ei := Some 2%nat; im_eb := Some 1%nat; im_ee := Some 2%nat |}.

Lemma cm_matrix_externally_tangent_disks_witness :
  im_touches cm_matrix_externally_tangent_disks /\
  ~ im_overlaps cm_matrix_externally_tangent_disks /\
  matrix_ok cm_matrix_externally_tangent_disks.
Proof.
  split; [ | split ].
  - right; left. unfold matrix_matches, pat_touches_1,
      cm_matrix_externally_tangent_disks; simpl. repeat split.
  - intros [H | H]; unfold matrix_matches in H; simpl in H;
      destruct H as [Ht _]; exact Ht.
  - unfold matrix_ok, cm_matrix_externally_tangent_disks; simpl.
    repeat split; (exact I || lia).
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Curve-level corollaries (transport the laws through `to_geometry`).     *)
(* -------------------------------------------------------------------------- *)

Theorem curve_de9im_matrix_ok :
  forall cgA cgB n m, curve_de9im_pointset cgA cgB n m -> matrix_ok m.
Proof. intros cgA cgB n m H. eapply geom_de9im_matrix_ok; exact H. Qed.

Theorem curve_de9im_ee_nonempty :
  forall cgA cgB n m, curve_de9im_pointset cgA cgB n m -> im_ee m <> None.
Proof. intros cgA cgB n m H. eapply geom_de9im_ee_nonempty; exact H. Qed.

Theorem curve_de9im_pointset_transpose :
  forall cgA cgB n m,
    curve_de9im_pointset cgA cgB n m <->
    curve_de9im_pointset cgB cgA n (matrix_transpose m).
Proof.
  intros cgA cgB n m. unfold curve_de9im_pointset.
  apply geom_de9im_pointset_transpose.
Qed.

(* The interior stratum is exactly the inscribed-ring membership of the merged
   bridge (`RelateCurveRingReduction.point_in_curve_geometry_iff_inscribed`) --
   this is what ties the abstract spec to the actual curve geometry. *)
Corollary cg_interior_iff_inscribed :
  forall (cg : CurveGeometry) (n : nat) (p : Point),
    Forall curve_polygon_adjacent cg ->
    (cg_interior cg n p <->
     exists cp, In cp cg
       /\ point_in_ring p (inscribed_ring (curve_outer cp) n)
       /\ (forall h0, In h0 (curve_holes cp)
                      -> ~ point_in_ring p (inscribed_ring h0 n))).
Proof.
  intros cg n p Hadj. unfold cg_interior.
  apply point_in_curve_geometry_iff_inscribed. exact Hadj.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions two_geometries_exterior_meet.
Print Assumptions geom_de9im_matrix_ok.
Print Assumptions geom_de9im_ee_nonempty.
Print Assumptions geom_de9im_pointset_transpose.
Print Assumptions geom_de9im_disjoint_ogc_characterization.
Print Assumptions im_disjoint_ogc_not_intersects_partial.
Print Assumptions cm_matrix_disjoint_disks_witness.
Print Assumptions cm_matrix_contains_disk_witness.
Print Assumptions cm_matrix_overlapping_disks_witness.
Print Assumptions cm_matrix_externally_tangent_disks_witness.
Print Assumptions curve_de9im_pointset_transpose.
Print Assumptions cg_interior_iff_inscribed.
