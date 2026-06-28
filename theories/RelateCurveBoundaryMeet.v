(* ============================================================================
   NetTopologySuite.Proofs.RelateCurveBoundaryMeet
   ----------------------------------------------------------------------------
   The lineal boundary-meet bridge for CURVE_RELATE_MATRIX.

   `RelateCurveMatrix.v` states the DE-9IM cells over the LINEARISED
   `to_geometry` strata (`geom_boundary` / `point_set`), whereas the contact
   kernels of `run_overlay_unified` / `run_curve_relate_matrix` are certified
   over `curve_segments_meet` (see `OverlayContactSound.v`, `RingContactSound.v`).
   This file supplies the missing bridge for the CHORD-CHORD (lineal) case --
   the one flagged as deferred in `RingContactSound.v` -- which is pure
   repackaging because a chord linearises to exactly itself:

     - `chord_approx_segment (CSChord p q) n = [p; q]` for ALL n
       (the densification level is inert for chords; `CurveGeometry.v`), so
     - a `CSChord p q` segment contributes the adjacent pair `p; q` to the
       flattened ring, hence the edge `(p, q)` to `ring_edges` (`Overlay.v`),
     - and `on_edge X (p,q) = between p q X = on_curve_segment (CSChord p q) X`.

   Result: a chord-chord contact verdict between the boundaries of two curve
   geometries makes their LINEARISED boundaries meet -- the im_bb cell is
   non-empty, and the OGC-disjoint relate pattern is refuted.  Coverage spans
   both the outer ring and the hole rings of each curve polygon.

   LINEAL EXACTNESS (foundation, §1b): for an all-chord ring/geometry the
   linearisation is `n`-independent (no sagitta error), so every ARC-specific
   relate frontier (sagitta densification error model, arc noding) simply does
   not apply to lineal inputs.

   HONEST SCOPE (boundary stratum, lineal only):
     - The BOUNDARY stratum is now closed for the lineal case (im_bb here;
       im_ee already general via two_geometries_exterior_meet).
     - The INTERIOR cells (im_ii / im_ib / im_bi) -- for lineal curves AND for
       straight-line geometries -- are gated on the deferred Jordan seam
       `RelateNG.point_set_characterises_geometric_interior`, which aligns the
       ray-parity `point_set` interior with the algebraic `0 < gtri` interior.
       That seam is the recommended (medium-debt) next frontier; it is NOT
       discharged here.
     - ARC boundary cells (the contact point lies on the true arc, not on a
       linearised chord edge) remain gated on the sagitta error model.

   3-axiom footprint (classical reals trio only); no Admitted.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals List.
Import ListNotations.
From NTS.Proofs Require Import Distance Segment Orientation Intersect
  Overlay CurveGeometry CurveLinearise CurveRingSimple OverlayContactSound
  DE9IM RelateCurveMatrix.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  List bridges: a chord's endpoints are an edge of its linearised ring.  *)
(*     (Pure list induction -- no geometry.)                                  *)
(* -------------------------------------------------------------------------- *)

(* Prepending a vertex never removes an existing ring edge. *)
Lemma ring_edges_in_cons :
  forall (e : Edge) (x : Point) (M : Ring),
    In e (ring_edges M) -> In e (ring_edges (x :: M)).
Proof.
  intros e x M H.
  destruct M as [| y M'].
  - simpl in H. contradiction.
  - simpl. right. exact H.
Qed.

(* Prepending any prefix preserves the edges of the suffix. *)
Lemma ring_edges_in_app :
  forall (L : Ring) (e : Edge) (M : Ring),
    In e (ring_edges M) -> In e (ring_edges (L ++ M)).
Proof.
  induction L as [| x L' IH]; intros e M H.
  - simpl. exact H.
  - simpl. apply ring_edges_in_cons. apply IH. exact H.
Qed.

(* Definitional unfolding of chord_approx_ring at a cons. *)
Lemma chord_approx_ring_cons :
  forall (s : CurveSegment) (r : CurveRing) (n : nat),
    chord_approx_ring (s :: r) n
    = chord_approx_segment s n ++ chord_approx_ring r n.
Proof. intros. reflexivity. Qed.

(* The headline list lemma: every chord segment of a ring contributes its
   endpoint pair as an edge of the linearised ring. *)
Lemma chord_edge_in_chord_approx_ring :
  forall (r : CurveRing) (p q : Point) (n : nat),
    In (CSChord p q) r ->
    In (p, q) (ring_edges (chord_approx_ring r n)).
Proof.
  induction r as [| s r' IH]; intros p q n Hin.
  - simpl in Hin. contradiction.
  - simpl in Hin. rewrite chord_approx_ring_cons.
    destruct Hin as [Heq | Hin'].
    + (* head segment IS the chord: [p;q] ++ rest = p :: q :: rest *)
      subst s. simpl. left. reflexivity.
    + (* chord is in the tail: edges of the suffix survive prepending *)
      apply ring_edges_in_app. apply IH. exact Hin'.
Qed.

(* -------------------------------------------------------------------------- *)
(* §1b  Lineal exactness: an all-chord ring/geometry linearises independent    *)
(*      of n (no sagitta error -- arc frontiers do not apply to lineal input). *)
(* -------------------------------------------------------------------------- *)

Definition lineal_ring (r : CurveRing) : Prop :=
  Forall (fun s => exists p q, s = CSChord p q) r.

Definition lineal_curve_polygon (cp : CurvePolygon) : Prop :=
  lineal_ring (curve_outer cp) /\ Forall lineal_ring (curve_holes cp).

Definition lineal_curve_geometry (cg : CurveGeometry) : Prop :=
  Forall lineal_curve_polygon cg.

Lemma chord_approx_ring_lineal_n_independent :
  forall (r : CurveRing),
    lineal_ring r ->
    forall n m, chord_approx_ring r n = chord_approx_ring r m.
Proof.
  intros r Hlin. induction Hlin as [| s r' Hhd Htl IH]; intros n m.
  - reflexivity.
  - destruct Hhd as [p [q Hs]]. subst s.
    rewrite !chord_approx_ring_cons. cbn [chord_approx_segment].
    rewrite (IH n m). reflexivity.
Qed.

Lemma to_geometry_lineal_n_independent :
  forall (cg : CurveGeometry),
    lineal_curve_geometry cg ->
    forall n m, to_geometry cg n = to_geometry cg m.
Proof.
  intros cg Hlin n m. unfold to_geometry.
  apply map_ext_in. intros cp Hcp.
  unfold lineal_curve_geometry in Hlin.
  rewrite Forall_forall in Hlin. specialize (Hlin cp Hcp).
  destruct Hlin as [Houter Hholes].
  cbn beta.
  assert (Ho : chord_approx_ring (curve_outer cp) n
             = chord_approx_ring (curve_outer cp) m)
    by (apply chord_approx_ring_lineal_n_independent; exact Houter).
  assert (Hhm : map (fun h => chord_approx_ring h n) (curve_holes cp)
              = map (fun h => chord_approx_ring h m) (curve_holes cp)).
  { apply map_ext_in. intros h Hin.
    apply chord_approx_ring_lineal_n_independent.
    rewrite Forall_forall in Hholes. apply Hholes. exact Hin. }
  rewrite Ho, Hhm. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The geom_boundary bridge (repackaging), outer ring and hole rings.     *)
(* -------------------------------------------------------------------------- *)

(* A point on a chord of a curve polygon's OUTER ring lies on the linearised
   geometry's boundary. *)
Lemma chord_on_outer_to_cg_boundary :
  forall (cg : CurveGeometry) (cp : CurvePolygon) (p q : Point) (n : nat) (X : Point),
    In cp cg ->
    In (CSChord p q) (curve_outer cp) ->
    between p q X ->
    cg_boundary cg n X.
Proof.
  intros cg cp p q n X Hcp Hseg Hbtw.
  unfold cg_boundary, geom_boundary.
  exists (mkPolygon (chord_approx_ring (curve_outer cp) n)
                    (map (fun h => chord_approx_ring h n) (curve_holes cp))).
  split.
  - (* the polygon is in to_geometry cg n *)
    unfold to_geometry. apply in_map_iff. exists cp. split; [ reflexivity | exact Hcp ].
  - exists (p, q). split.
    + unfold poly_edges. simpl. apply in_or_app. left.
      apply chord_edge_in_chord_approx_ring. exact Hseg.
    + unfold on_edge. simpl. exact Hbtw.
Qed.

(* A point on a chord of one of a curve polygon's HOLE rings is also on the
   linearised boundary (poly_edges includes every hole's ring_edges). *)
Lemma chord_on_hole_to_cg_boundary :
  forall (cg : CurveGeometry) (cp : CurvePolygon) (h : CurveRing)
         (p q : Point) (n : nat) (X : Point),
    In cp cg ->
    In h (curve_holes cp) ->
    In (CSChord p q) h ->
    between p q X ->
    cg_boundary cg n X.
Proof.
  intros cg cp h p q n X Hcp Hh Hseg Hbtw.
  unfold cg_boundary, geom_boundary.
  exists (mkPolygon (chord_approx_ring (curve_outer cp) n)
                    (map (fun h0 => chord_approx_ring h0 n) (curve_holes cp))).
  split.
  - unfold to_geometry. apply in_map_iff. exists cp. split; [ reflexivity | exact Hcp ].
  - exists (p, q). split.
    + unfold poly_edges. simpl. apply in_or_app. right.
      apply in_flat_map.
      exists (chord_approx_ring h n). split.
      * apply in_map_iff. exists h. split; [ reflexivity | exact Hh ].
      * apply chord_edge_in_chord_approx_ring. exact Hseg.
    + unfold on_edge. simpl. exact Hbtw.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2b  Unified boundary membership: a chord ANYWHERE on a curve polygon's     *)
(*      boundary (outer ring OR a hole ring).                                  *)
(* -------------------------------------------------------------------------- *)

Definition chord_in_cp_boundary (cp : CurvePolygon) (p q : Point) : Prop :=
  In (CSChord p q) (curve_outer cp) \/
  (exists h, In h (curve_holes cp) /\ In (CSChord p q) h).

Lemma chord_on_cp_boundary_to_cg_boundary :
  forall (cg : CurveGeometry) (cp : CurvePolygon) (p q : Point) (n : nat) (X : Point),
    In cp cg ->
    chord_in_cp_boundary cp p q ->
    between p q X ->
    cg_boundary cg n X.
Proof.
  intros cg cp p q n X Hcp Hb Hbtw.
  destruct Hb as [Houter | [h [Hh Hseg]]].
  - apply (chord_on_outer_to_cg_boundary cg cp p q n X Hcp Houter Hbtw).
  - apply (chord_on_hole_to_cg_boundary cg cp h p q n X Hcp Hh Hseg Hbtw).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Contact verdict ==> boundaries meet (reuse OverlayContactSound).        *)
(*     One theorem per chord-chord regime; chords may lie on outer OR holes.   *)
(* -------------------------------------------------------------------------- *)

Theorem curve_boundaries_meet_of_chord_chord_crossing :
  forall (cgA cgB : CurveGeometry) (n : nat) (cpA cpB : CurvePolygon)
         (A B C D : Point),
    In cpA cgA -> In cpB cgB ->
    chord_in_cp_boundary cpA A B ->
    chord_in_cp_boundary cpB C D ->
    cross A B C * cross A B D < 0 ->
    cross C D A * cross C D B < 0 ->
    exists X, cg_boundary cgA n X /\ cg_boundary cgB n X.
Proof.
  intros cgA cgB n cpA cpB A B C D HA HB HsA HsB H1 H2.
  destruct (chord_chord_contact_crossing_sound A B C D H1 H2) as [X [HAB HCD]].
  exists X. split.
  - apply (chord_on_cp_boundary_to_cg_boundary cgA cpA A B n X HA HsA HAB).
  - apply (chord_on_cp_boundary_to_cg_boundary cgB cpB C D n X HB HsB HCD).
Qed.

Theorem curve_boundaries_meet_of_chord_chord_collinear :
  forall (cgA cgB : CurveGeometry) (n : nat) (cpA cpB : CurvePolygon)
         (A B C D : Point),
    In cpA cgA -> In cpB cgB ->
    chord_in_cp_boundary cpA A B ->
    chord_in_cp_boundary cpB C D ->
    segments_1d_overlap A B C D ->
    exists X, cg_boundary cgA n X /\ cg_boundary cgB n X.
Proof.
  intros cgA cgB n cpA cpB A B C D HA HB HsA HsB Hov.
  destruct (chord_chord_contact_collinear_sound A B C D Hov) as [X [HAB HCD]].
  exists X. split.
  - apply (chord_on_cp_boundary_to_cg_boundary cgA cpA A B n X HA HsA HAB).
  - apply (chord_on_cp_boundary_to_cg_boundary cgB cpB C D n X HB HsB HCD).
Qed.

Theorem curve_boundaries_meet_of_chord_chord_endpoint :
  forall (cgA cgB : CurveGeometry) (n : nat) (cpA cpB : CurvePolygon)
         (A B C D : Point),
    In cpA cgA -> In cpB cgB ->
    chord_in_cp_boundary cpA A B ->
    chord_in_cp_boundary cpB C D ->
    (between C D A \/ between C D B \/ between A B C \/ between A B D) ->
    exists X, cg_boundary cgA n X /\ cg_boundary cgB n X.
Proof.
  intros cgA cgB n cpA cpB A B C D HA HB HsA HsB Hep.
  destruct (chord_chord_contact_endpoint_sound A B C D Hep) as [X [HAB HCD]].
  exists X. split.
  - apply (chord_on_cp_boundary_to_cg_boundary cgA cpA A B n X HA HsA HAB).
  - apply (chord_on_cp_boundary_to_cg_boundary cgB cpB C D n X HB HsB HCD).
Qed.

Theorem curve_boundaries_meet_of_chord_chord_shared_vertex :
  forall (cgA cgB : CurveGeometry) (n : nat) (cpA cpB : CurvePolygon)
         (A B C D : Point),
    In cpA cgA -> In cpB cgB ->
    chord_in_cp_boundary cpA A B ->
    chord_in_cp_boundary cpB C D ->
    (A = C \/ A = D \/ B = C \/ B = D) ->
    exists X, cg_boundary cgA n X /\ cg_boundary cgB n X.
Proof.
  intros cgA cgB n cpA cpB A B C D HA HB HsA HsB Hsv.
  destruct (chord_chord_contact_shared_vertex A B C D Hsv) as [X [HAB HCD]].
  exists X. split.
  - apply (chord_on_cp_boundary_to_cg_boundary cgA cpA A B n X HA HsA HAB).
  - apply (chord_on_cp_boundary_to_cg_boundary cgB cpB C D n X HB HsB HCD).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Generic relate verdicts from a boundary-boundary witness.               *)
(* -------------------------------------------------------------------------- *)

(* A boundary-boundary meet makes the im_bb cell non-empty. *)
Lemma bb_nonempty_of_boundary_meet :
  forall (cgA cgB : CurveGeometry) (n : nat) (m : IntersectionMatrix),
    geom_de9im_pointset (to_geometry cgA n) (to_geometry cgB n) m ->
    (exists X, cg_boundary cgA n X /\ cg_boundary cgB n X) ->
    dim_nonempty (im_bb m).
Proof.
  intros cgA cgB n m Hspec [X [HbA HbB]].
  destruct Hspec as [_ [_ [_ [_ [Hbb _]]]]].
  destruct Hbb as [_ Hiff]. apply (proj2 Hiff).
  exists X. unfold in_stratum. split.
  - unfold cg_boundary in HbA. exact HbA.
  - unfold cg_boundary in HbB. exact HbB.
Qed.

(* A boundary-boundary meet refutes the OGC-disjoint relate pattern. *)
Lemma not_disjoint_of_boundary_meet :
  forall (cgA cgB : CurveGeometry) (n : nat) (m : IntersectionMatrix),
    geom_de9im_pointset (to_geometry cgA n) (to_geometry cgB n) m ->
    (exists X, cg_boundary cgA n X /\ cg_boundary cgB n X) ->
    ~ im_disjoint_ogc m.
Proof.
  intros cgA cgB n m Hspec [X [HbA HbB]] Hdisj.
  pose proof (geom_de9im_disjoint_ogc_characterization _ _ _ Hspec) as Hchar.
  apply Hchar in Hdisj.
  destruct Hdisj as [_ [_ [_ Hnobb]]].
  apply Hnobb. exists X. split.
  - unfold cg_boundary in HbA. exact HbA.
  - unfold cg_boundary in HbB. exact HbB.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4b  Oracle-facing headlines: chord-chord contact ==> not OGC-disjoint.     *)
(*      Chords may lie on the outer ring OR a hole ring of either polygon.     *)
(* -------------------------------------------------------------------------- *)

Theorem curve_relate_not_disjoint_of_chord_chord_crossing :
  forall (cgA cgB : CurveGeometry) (n : nat) (cpA cpB : CurvePolygon)
         (A B C D : Point) (m : IntersectionMatrix),
    In cpA cgA -> In cpB cgB ->
    chord_in_cp_boundary cpA A B ->
    chord_in_cp_boundary cpB C D ->
    cross A B C * cross A B D < 0 ->
    cross C D A * cross C D B < 0 ->
    geom_de9im_pointset (to_geometry cgA n) (to_geometry cgB n) m ->
    ~ im_disjoint_ogc m.
Proof.
  intros cgA cgB n cpA cpB A B C D m HA HB HsA HsB H1 H2 Hspec.
  apply (not_disjoint_of_boundary_meet cgA cgB n m Hspec).
  apply (curve_boundaries_meet_of_chord_chord_crossing
           cgA cgB n cpA cpB A B C D HA HB HsA HsB H1 H2).
Qed.

Theorem curve_relate_not_disjoint_of_chord_chord_collinear :
  forall (cgA cgB : CurveGeometry) (n : nat) (cpA cpB : CurvePolygon)
         (A B C D : Point) (m : IntersectionMatrix),
    In cpA cgA -> In cpB cgB ->
    chord_in_cp_boundary cpA A B ->
    chord_in_cp_boundary cpB C D ->
    segments_1d_overlap A B C D ->
    geom_de9im_pointset (to_geometry cgA n) (to_geometry cgB n) m ->
    ~ im_disjoint_ogc m.
Proof.
  intros cgA cgB n cpA cpB A B C D m HA HB HsA HsB Hov Hspec.
  apply (not_disjoint_of_boundary_meet cgA cgB n m Hspec).
  apply (curve_boundaries_meet_of_chord_chord_collinear
           cgA cgB n cpA cpB A B C D HA HB HsA HsB Hov).
Qed.

Theorem curve_relate_not_disjoint_of_chord_chord_endpoint :
  forall (cgA cgB : CurveGeometry) (n : nat) (cpA cpB : CurvePolygon)
         (A B C D : Point) (m : IntersectionMatrix),
    In cpA cgA -> In cpB cgB ->
    chord_in_cp_boundary cpA A B ->
    chord_in_cp_boundary cpB C D ->
    (between C D A \/ between C D B \/ between A B C \/ between A B D) ->
    geom_de9im_pointset (to_geometry cgA n) (to_geometry cgB n) m ->
    ~ im_disjoint_ogc m.
Proof.
  intros cgA cgB n cpA cpB A B C D m HA HB HsA HsB Hep Hspec.
  apply (not_disjoint_of_boundary_meet cgA cgB n m Hspec).
  apply (curve_boundaries_meet_of_chord_chord_endpoint
           cgA cgB n cpA cpB A B C D HA HB HsA HsB Hep).
Qed.

Theorem curve_relate_not_disjoint_of_chord_chord_shared_vertex :
  forall (cgA cgB : CurveGeometry) (n : nat) (cpA cpB : CurvePolygon)
         (A B C D : Point) (m : IntersectionMatrix),
    In cpA cgA -> In cpB cgB ->
    chord_in_cp_boundary cpA A B ->
    chord_in_cp_boundary cpB C D ->
    (A = C \/ A = D \/ B = C \/ B = D) ->
    geom_de9im_pointset (to_geometry cgA n) (to_geometry cgB n) m ->
    ~ im_disjoint_ogc m.
Proof.
  intros cgA cgB n cpA cpB A B C D m HA HB HsA HsB Hsv Hspec.
  apply (not_disjoint_of_boundary_meet cgA cgB n m Hspec).
  apply (curve_boundaries_meet_of_chord_chord_shared_vertex
           cgA cgB n cpA cpB A B C D HA HB HsA HsB Hsv).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4c  Entry point keyed on RingContactSound's curve_segments_meet.           *)
(*      Bridges the two files' abstractions: a chord-chord meet (whatever       *)
(*      contact regime produced it) between two curve-polygon boundaries        *)
(*      yields a linearised boundary-boundary meet.                            *)
(* -------------------------------------------------------------------------- *)

Lemma curve_boundaries_meet_of_chord_segments_meet :
  forall (cgA cgB : CurveGeometry) (n : nat) (cpA cpB : CurvePolygon)
         (A B C D : Point),
    In cpA cgA -> In cpB cgB ->
    chord_in_cp_boundary cpA A B ->
    chord_in_cp_boundary cpB C D ->
    curve_segments_meet (CSChord A B) (CSChord C D) ->
    exists X, cg_boundary cgA n X /\ cg_boundary cgB n X.
Proof.
  intros cgA cgB n cpA cpB A B C D HA HB HsA HsB Hmeet.
  destruct Hmeet as [X [HAB HCD]].
  (* on_curve_segment (CSChord _ _) X reduces to between _ _ X *)
  simpl in HAB, HCD.
  exists X. split.
  - apply (chord_on_cp_boundary_to_cg_boundary cgA cpA A B n X HA HsA HAB).
  - apply (chord_on_cp_boundary_to_cg_boundary cgB cpB C D n X HB HsB HCD).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4d  Positive DE-9IM verdict: boundary-boundary INTERSECTION.               *)
(*      A boundary-boundary meet matches `pat_intersects_4` (pat_bb := PTrue), *)
(*      the positive form the relate oracle emits -- complementing the         *)
(*      negative `~ im_disjoint_ogc` verdicts of §4b.                          *)
(* -------------------------------------------------------------------------- *)

Lemma intersects_bb_of_boundary_meet :
  forall (cgA cgB : CurveGeometry) (n : nat) (m : IntersectionMatrix),
    geom_de9im_pointset (to_geometry cgA n) (to_geometry cgB n) m ->
    (exists X, cg_boundary cgA n X /\ cg_boundary cgB n X) ->
    matrix_matches pat_intersects_4 m.
Proof.
  intros cgA cgB n m Hspec Hmeet.
  unfold matrix_matches, pat_intersects_4; simpl.
  repeat split; try exact I.
  apply (proj2 (char_true_nonempty (im_bb m))).
  apply (bb_nonempty_of_boundary_meet cgA cgB n m Hspec Hmeet).
Qed.

Theorem curve_relate_intersects_of_chord_chord_crossing :
  forall (cgA cgB : CurveGeometry) (n : nat) (cpA cpB : CurvePolygon)
         (A B C D : Point) (m : IntersectionMatrix),
    In cpA cgA -> In cpB cgB ->
    chord_in_cp_boundary cpA A B ->
    chord_in_cp_boundary cpB C D ->
    cross A B C * cross A B D < 0 ->
    cross C D A * cross C D B < 0 ->
    geom_de9im_pointset (to_geometry cgA n) (to_geometry cgB n) m ->
    matrix_matches pat_intersects_4 m.
Proof.
  intros cgA cgB n cpA cpB A B C D m HA HB HsA HsB H1 H2 Hspec.
  apply (intersects_bb_of_boundary_meet cgA cgB n m Hspec).
  apply (curve_boundaries_meet_of_chord_chord_crossing
           cgA cgB n cpA cpB A B C D HA HB HsA HsB H1 H2).
Qed.

Theorem curve_relate_intersects_of_chord_chord_collinear :
  forall (cgA cgB : CurveGeometry) (n : nat) (cpA cpB : CurvePolygon)
         (A B C D : Point) (m : IntersectionMatrix),
    In cpA cgA -> In cpB cgB ->
    chord_in_cp_boundary cpA A B ->
    chord_in_cp_boundary cpB C D ->
    segments_1d_overlap A B C D ->
    geom_de9im_pointset (to_geometry cgA n) (to_geometry cgB n) m ->
    matrix_matches pat_intersects_4 m.
Proof.
  intros cgA cgB n cpA cpB A B C D m HA HB HsA HsB Hov Hspec.
  apply (intersects_bb_of_boundary_meet cgA cgB n m Hspec).
  apply (curve_boundaries_meet_of_chord_chord_collinear
           cgA cgB n cpA cpB A B C D HA HB HsA HsB Hov).
Qed.

Theorem curve_relate_intersects_of_chord_chord_endpoint :
  forall (cgA cgB : CurveGeometry) (n : nat) (cpA cpB : CurvePolygon)
         (A B C D : Point) (m : IntersectionMatrix),
    In cpA cgA -> In cpB cgB ->
    chord_in_cp_boundary cpA A B ->
    chord_in_cp_boundary cpB C D ->
    (between C D A \/ between C D B \/ between A B C \/ between A B D) ->
    geom_de9im_pointset (to_geometry cgA n) (to_geometry cgB n) m ->
    matrix_matches pat_intersects_4 m.
Proof.
  intros cgA cgB n cpA cpB A B C D m HA HB HsA HsB Hep Hspec.
  apply (intersects_bb_of_boundary_meet cgA cgB n m Hspec).
  apply (curve_boundaries_meet_of_chord_chord_endpoint
           cgA cgB n cpA cpB A B C D HA HB HsA HsB Hep).
Qed.

Theorem curve_relate_intersects_of_chord_chord_shared_vertex :
  forall (cgA cgB : CurveGeometry) (n : nat) (cpA cpB : CurvePolygon)
         (A B C D : Point) (m : IntersectionMatrix),
    In cpA cgA -> In cpB cgB ->
    chord_in_cp_boundary cpA A B ->
    chord_in_cp_boundary cpB C D ->
    (A = C \/ A = D \/ B = C \/ B = D) ->
    geom_de9im_pointset (to_geometry cgA n) (to_geometry cgB n) m ->
    matrix_matches pat_intersects_4 m.
Proof.
  intros cgA cgB n cpA cpB A B C D m HA HB HsA HsB Hsv Hspec.
  apply (intersects_bb_of_boundary_meet cgA cgB n m Hspec).
  apply (curve_boundaries_meet_of_chord_chord_shared_vertex
           cgA cgB n cpA cpB A B C D HA HB HsA HsB Hsv).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4e  Symmetry: the boundary-meet witness commutes, so every §4b/§4d verdict *)
(*      holds with cgA/cgB swapped (re-instantiate with the commuted witness;  *)
(*      pat_disjoint_ogc and pat_intersects_4 are themselves swap-symmetric).  *)
(* -------------------------------------------------------------------------- *)

Lemma boundary_meet_comm :
  forall (cgA cgB : CurveGeometry) (n : nat),
    (exists X, cg_boundary cgA n X /\ cg_boundary cgB n X) ->
    (exists X, cg_boundary cgB n X /\ cg_boundary cgA n X).
Proof. intros cgA cgB n [X [H1 H2]]. exists X. split; assumption. Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Audit footprint (must show only the classical-reals trio).             *)
(* -------------------------------------------------------------------------- *)

Print Assumptions chord_edge_in_chord_approx_ring.
Print Assumptions chord_approx_ring_lineal_n_independent.
Print Assumptions to_geometry_lineal_n_independent.
Print Assumptions chord_on_cp_boundary_to_cg_boundary.
Print Assumptions curve_boundaries_meet_of_chord_chord_crossing.
Print Assumptions curve_boundaries_meet_of_chord_chord_collinear.
Print Assumptions curve_boundaries_meet_of_chord_chord_endpoint.
Print Assumptions curve_boundaries_meet_of_chord_chord_shared_vertex.
Print Assumptions bb_nonempty_of_boundary_meet.
Print Assumptions not_disjoint_of_boundary_meet.
Print Assumptions curve_relate_not_disjoint_of_chord_chord_crossing.
Print Assumptions curve_relate_not_disjoint_of_chord_chord_collinear.
Print Assumptions curve_relate_not_disjoint_of_chord_chord_endpoint.
Print Assumptions curve_relate_not_disjoint_of_chord_chord_shared_vertex.
Print Assumptions curve_boundaries_meet_of_chord_segments_meet.
Print Assumptions intersects_bb_of_boundary_meet.
Print Assumptions curve_relate_intersects_of_chord_chord_crossing.
Print Assumptions curve_relate_intersects_of_chord_chord_collinear.
Print Assumptions curve_relate_intersects_of_chord_chord_endpoint.
Print Assumptions curve_relate_intersects_of_chord_chord_shared_vertex.
