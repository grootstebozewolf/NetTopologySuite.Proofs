(* ============================================================================
   NetTopologySuite.Proofs.RelatePrepared
   ----------------------------------------------------------------------------
   Issue #67 S13 / #574 / claimId 522-e: Prepared cache correctness
   (NTS#819 proof companion).

   `PreparedGeometry` wraps a Geometry with memoised rect bounds and
   triangle points.  `prepare` stores the extractors' results.  `evaluate`
   consults those cached A-coords (plus B extracted from the argument)
   and short-circuits to `aa_matrix_disjoint` only when the existing
   classifier already answers Disjoint.  Naive "boxes apart ⇒ disjoint"
   is unsound for triangles (`separated_b` has CCW guards); that is the
   Qex below, not the short-circuit.

   Agreement is not vacuous: it is stated over `prepare`, or over a
   `cache_coherent` premise, so a hand-corrupted cache cannot make it
   hold.  `evaluate_ignores_cache` is deleted — it no longer compiles.

   Named non-goal: `RelatePreparedCache*.v` is a separate segment-fold
   envelope / STRtree refinement lane.  It does not share these cache
   fields; consolidating the two is a later Refactor outcome.

   No `Admitted`, no new axioms.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Real DE9IM Distance Overlay Orientation RelateNG RelateAreaArea RelateMatrixRect RelateMatrixTriangle RelateAreaPoint GeneralTriangleSeparation.

Open Scope R_scope.

Record PreparedGeometry : Type := mkPrepared {
  pg_geom : Geometry;
  (* For rect geometries we cache the extracted bounds (non-trivial cache).
     None = trivial/unknown. This is the tiny NTS#819-style example for rects. *)
  pg_cache : option (R * R * R * R);
  (* Tiny non-identity cache extension for triangle points (6 coords). *)
  pg_tri_cache : option (R * R * R * R * R * R)
}.

Definition prepare (g : Geometry) : PreparedGeometry :=
  mkPrepared g (rect_geometry_bounds g) (triangle_geometry_points g).

(* Cache-consulting evaluate.  A's coords come from `pg_cache` /
   `pg_tri_cache`, not a re-extraction from `pg_geom`.  The short-circuit
   fires only when the existing classifier says Disjoint, so a CW pair
   whose boxes happen to be apart still declines — same as `relate`.
   Nested matches (not a pair-match) so `None` reduces without
   inspecting the other discriminee. *)
Definition evaluate_from_tri_cache
  (pg : PreparedGeometry) (g : Geometry) : IntersectionMatrix :=
  match pg_tri_cache pg with
  | Some (ax, ay, bx, by_, cx, cy) =>
      match triangle_geometry_points g with
      | Some (dx, dy, ex, ey, fx, fy) =>
          match triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy with
          | TPR_Disjoint => aa_matrix_disjoint
          | _ => relate (pg_geom pg) g
          end
      | None => relate (pg_geom pg) g
      end
  | None => relate (pg_geom pg) g
  end.

Definition evaluate (pg : PreparedGeometry) (g : Geometry) : IntersectionMatrix :=
  match pg_cache pg with
  | Some (ax0, ay0, ax1, ay1) =>
      match rect_geometry_bounds g with
      | Some (bx0, by0, bx1, by1) =>
          match rect_pair_regime ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 with
          | RPR_Disjoint => aa_matrix_disjoint
          | _ => relate (pg_geom pg) g
          end
      | None => evaluate_from_tri_cache pg g
      end
  | None => evaluate_from_tri_cache pg g
  end.

Lemma evaluate_from_tri_cache_none :
  forall pg g,
    pg_tri_cache pg = None ->
    evaluate_from_tri_cache pg g = relate (pg_geom pg) g.
Proof.
  intros pg g H. unfold evaluate_from_tri_cache. rewrite H. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Coherence: the stored bounds really are the extractors' results.           *)
(* -------------------------------------------------------------------------- *)

Definition cache_coherent (pg : PreparedGeometry) : Prop :=
  pg_cache pg = rect_geometry_bounds (pg_geom pg) /\
  pg_tri_cache pg = triangle_geometry_points (pg_geom pg).

Lemma prepare_cache_coherent :
  forall g, cache_coherent (prepare g).
Proof.
  intro g. split; reflexivity.
Qed.

Lemma rects_relate_disjoint_eq :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rects_relate ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 RPR_Disjoint =
    aa_matrix_disjoint.
Proof.
  intros. reflexivity.
Qed.

Lemma tris_relate_disjoint_eq :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    tris_relate ax ay bx by_ cx cy dx dy ex ey fx fy TPR_Disjoint =
    aa_matrix_disjoint.
Proof.
  intros. unfold tris_relate. apply triangle_pair_fill_disjoint_eq.
Qed.

(* A 5-point rect ring cannot also be a 4-point triangle ring. *)
Lemma extractors_not_both_some :
  forall g b t,
    rect_geometry_bounds g = Some b ->
    triangle_geometry_points g = Some t ->
    False.
Proof.
  intros g b t Hr Ht.
  unfold rect_geometry_bounds, triangle_geometry_points in *.
  destruct g as [|poly gtl]; [discriminate|].
  destruct gtl; [|discriminate].
  destruct (hole_rings poly); [|discriminate].
  destruct (outer_ring poly) as [|p0 r0]; [discriminate|].
  destruct p0. destruct r0 as [|p1 r1]; [discriminate|].
  destruct p1. destruct r1 as [|p2 r2]; [discriminate|].
  destruct p2. destruct r2 as [|p3 r3]; [discriminate|].
  destruct p3. destruct r3 as [|p4 r4].
  - discriminate.
  - destruct p4. destruct r4; discriminate.
Qed.

(* `relate` after the extractors, so agreement does not unfold the
   pair-match on `rect_geometry_bounds` (that match does not reduce
   when the other side is still a variable). *)
Lemma relate_extracted_rects :
  forall A B ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rect_geometry_bounds A = Some (ax0, ay0, ax1, ay1) ->
    rect_geometry_bounds B = Some (bx0, by0, bx1, by1) ->
    relate A B =
    rects_relate ax0 ay0 ax1 ay1 bx0 by0 bx1 by1
      (rect_pair_regime ax0 ay0 ax1 ay1 bx0 by0 bx1 by1).
Proof.
  intros A B ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 HA HB.
  unfold relate. rewrite HA, HB. reflexivity.
Qed.

Lemma relate_extracted_triangles :
  forall A B ax ay bx by_ cx cy dx dy ex ey fx fy,
    rect_geometry_bounds A = None ->
    triangle_geometry_points A = Some (ax, ay, bx, by_, cx, cy) ->
    triangle_geometry_points B = Some (dx, dy, ex, ey, fx, fy) ->
    relate A B =
    tris_relate ax ay bx by_ cx cy dx dy ex ey fx fy
      (triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy).
Proof.
  intros A B ax ay bx by_ cx cy dx dy ex ey fx fy HA Hta Htb.
  unfold relate. rewrite HA.
  destruct (rect_geometry_bounds B) as [bb|];
    rewrite Hta, Htb; reflexivity.
Qed.

(* Triangle-only path: A is not a rect, so evaluate goes to the tri cache. *)
Lemma evaluate_triangle_path_agrees :
  forall pg g,
    cache_coherent pg ->
    rect_geometry_bounds (pg_geom pg) = None ->
    evaluate pg g = relate (pg_geom pg) g.
Proof.
  intros pg g [Hc Htr] Ea.
  unfold evaluate. rewrite Hc, Ea.
  unfold evaluate_from_tri_cache. rewrite Htr.
  destruct (triangle_geometry_points (pg_geom pg)) as [ta|] eqn:Eta.
  2: reflexivity.
  destruct ta as [[[[[ax ay] bx] by_] cx] cy].
  destruct (triangle_geometry_points g) as [tb|] eqn:Etb.
  2: reflexivity.
  destruct tb as [[[[[dx dy] ex] ey] fx] fy].
  destruct (triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy)
    eqn:Tr;
    [ rewrite (relate_extracted_triangles (pg_geom pg) g ax ay bx by_ cx cy
                 dx dy ex ey fx fy Ea Eta Etb);
      rewrite Tr, tris_relate_disjoint_eq; reflexivity
    | reflexivity .. ].
Qed.

Theorem evaluate_coherent_agrees :
  forall pg g,
    cache_coherent pg ->
    evaluate pg g = relate (pg_geom pg) g.
Proof.
  intros pg g Hc.
  destruct (rect_geometry_bounds (pg_geom pg)) as [ab|] eqn:Ea;
    destruct (rect_geometry_bounds g) as [bb|] eqn:Eb.
  - destruct Hc as [Hcache Htr].
    unfold evaluate. rewrite Hcache, Ea.
    destruct ab as [[[ax0 ay0] ax1] ay1].
    rewrite Eb.
    destruct bb as [[[bx0 by0] bx1] by1].
    destruct (rect_pair_regime ax0 ay0 ax1 ay1 bx0 by0 bx1 by1)
      eqn:Rr.
    + rewrite (relate_extracted_rects (pg_geom pg) g ax0 ay0 ax1 ay1
                 bx0 by0 bx1 by1 Ea Eb).
      rewrite Rr, rects_relate_disjoint_eq. reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - (* A is a rect, B is not: rect arm misses. A cannot also be a
       triangle, so the tri cache is None and evaluate falls through. *)
    destruct Hc as [Hcache Htr].
    destruct (triangle_geometry_points (pg_geom pg)) as [ta|] eqn:Eta.
    + exfalso. eapply extractors_not_both_some; [exact Ea | exact Eta].
    + destruct ab as [[[ax0 ay0] ax1] ay1].
      unfold evaluate. rewrite Hcache, Ea, Eb.
      apply evaluate_from_tri_cache_none.
      exact Htr.
  - apply evaluate_triangle_path_agrees; [exact Hc | exact Ea].
  - apply evaluate_triangle_path_agrees; [exact Hc | exact Ea].
Qed.

(* WITNESS {"claimId":"522-e","topic":"relate","lemma":"prepared_evaluate_agrees","title":"Prepared evaluate agrees with relate when the cache is coherent","file":"theories/RelatePrepared.v","witness":"522-e-cache-consult","board":"#574"} *)
Theorem prepared_evaluate_agrees :
  forall (A B : Geometry),
    evaluate (prepare A) B = relate A B.
Proof.
  intros A B.
  transitivity (relate (pg_geom (prepare A)) B).
  - apply evaluate_coherent_agrees, prepare_cache_coherent.
  - reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Witness: a separated pair through the cache path equals one-shot relate,   *)
(* and the proof of evaluate = disjoint actually takes the short-circuit.     *)
(* -------------------------------------------------------------------------- *)

Lemma dispatch_pair_regime_disjoint :
  triangle_pair_regime 0 0 1 0 0 1 2 0 3 0 2 1 = TPR_Disjoint.
Proof.
  apply triangle_pair_regime_disjoint, dispatch_pair_separated_b.
Qed.

(* WITNESS topic: relate · claimId: 522-e · witness: 522-e-cache-consult *)
Theorem prepared_evaluate_cache_short_circuit :
  let A := triangle_geometry 0 0 1 0 0 1 in
  let B := triangle_geometry 2 0 3 0 2 1 in
  let pg := prepare A in
  pg_tri_cache pg = Some (0, 0, 1, 0, 0, 1) /\
  pg_cache pg = None /\
  triangle_pair_regime 0 0 1 0 0 1 2 0 3 0 2 1 = TPR_Disjoint /\
  evaluate pg B = aa_matrix_disjoint /\
  relate A B = aa_matrix_disjoint.
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact dispatch_pair_regime_disjoint|].
  split.
  - unfold evaluate, evaluate_from_tri_cache, prepare. simpl.
    rewrite dispatch_pair_regime_disjoint. reflexivity.
  - rewrite relate_on_triangles_dispatches.
    rewrite dispatch_pair_regime_disjoint.
    rewrite tris_relate_disjoint_eq. reflexivity.
Qed.

Lemma rect_pair_regime_unit_vs_shifted_disjoint :
  rect_pair_regime 0 0 1 1 2 0 3 1 = RPR_Disjoint.
Proof.
  unfold rect_pair_regime.
  destruct (Req_dec_T 1 2); try lra.
  destruct (Req_dec_T 1 0); try lra.
  destruct (Rlt_dec 0 2); try lra.
  destruct (Rlt_dec 3 1); try lra.
  reflexivity.
Qed.

Example prepared_rect_disjoint_cache_short_circuit :
  let A := rect_geometry 0 0 1 1 in
  let B := rect_geometry 2 0 3 1 in
  pg_cache (prepare A) = Some (0, 0, 1, 1) /\
  rect_pair_regime 0 0 1 1 2 0 3 1 = RPR_Disjoint /\
  evaluate (prepare A) B = aa_matrix_disjoint /\
  relate A B = aa_matrix_disjoint.
Proof.
  split; [reflexivity|].
  split; [exact rect_pair_regime_unit_vs_shifted_disjoint|].
  split.
  - unfold evaluate, prepare. simpl.
    rewrite rect_pair_regime_unit_vs_shifted_disjoint. reflexivity.
  - rewrite relate_on_rects_dispatches.
    rewrite rect_pair_regime_unit_vs_shifted_disjoint.
    rewrite rects_relate_disjoint_eq. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Stub-era corollaries, restated over the real evaluate.                     *)
(* -------------------------------------------------------------------------- *)

Theorem prepared_rect_evaluate_agrees :
  forall x0 y0 x1 y1 (g : Geometry),
    evaluate (prepare (rect_geometry x0 y0 x1 y1)) g =
    relate (rect_geometry x0 y0 x1 y1) g.
Proof.
  intros; apply prepared_evaluate_agrees.
Qed.

Example prepared_rect_touch_cached :
  let pg := prepare (rect_geometry 0 0 1 1) in
  let hole := rect_geometry 1 0 2 1 in
  evaluate pg hole = relate (pg_geom pg) hole.
Proof.
  apply prepared_rect_evaluate_agrees.
Qed.

Theorem prepared_triangle_evaluate_agrees :
  forall ax ay bx by_ cx cy (g : Geometry),
    evaluate (prepare (triangle_geometry ax ay bx by_ cx cy)) g =
    relate (triangle_geometry ax ay bx by_ cx cy) g.
Proof.
  intros; apply prepared_evaluate_agrees.
Qed.

Example prepared_triangle_touch_cached :
  let pg := prepare (triangle_geometry 0 0 1 0 0 1) in
  let b := triangle_geometry 1 0 1 1 0 1 in
  evaluate pg b = relate (pg_geom pg) b.
Proof.
  apply prepared_triangle_evaluate_agrees.
Qed.

Theorem prepared_identity :
  forall g : Geometry,
    evaluate (prepare g) g = relate g g.
Proof.
  intro g; apply prepared_evaluate_agrees.
Qed.

Example prepared_rect_has_bounds_cache :
  let pg := prepare (rect_geometry 0 0 1 1) in
  pg_cache pg = Some (0, 0, 1, 1).
Proof.
  reflexivity.
Qed.

Example prepared_triangle_has_points_cache :
  let pg := prepare (triangle_geometry 0 0 1 0 0 1) in
  pg_tri_cache pg = Some (0, 0, 1, 0, 0, 1).
Proof.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Qex: naive "boxes apart ⇒ disjoint" is unsound.  A CCW/CW pair can have    *)
(* strictly separated AABBs while `relate` (and the cache path) decline.      *)
(* The helper is local to the Qex; it is not used by `evaluate`.              *)
(* -------------------------------------------------------------------------- *)

Definition boxes_strictly_apart
  (ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 : R) : bool :=
  if Rlt_dec ax1 bx0 then true
  else if Rlt_dec bx1 ax0 then true
  else if Rlt_dec ay1 by0 then true
  else if Rlt_dec by1 ay0 then true
  else false.

Lemma boxes_apart_unit_vs_cw :
  boxes_strictly_apart 0 0 1 1 2 0 3 1 = true.
Proof.
  unfold boxes_strictly_apart.
  destruct (Rlt_dec 1 2) as [_ | Hn]; [reflexivity | exfalso; lra].
Qed.

Lemma cw_B_gdbl_nlt :
  ~ (0 < gdbl 2 0 2 1 3 0).
Proof. unfold gdbl; lra. Qed.

Lemma cw_pair_no_touch_edge :
  touch_edge_b (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
               (mkPoint 2 0) (mkPoint 2 1) (mkPoint 3 0) = false.
Proof.
  unfold touch_edge_b, shares_edge_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma cw_pair_no_contains :
  contains_b 0 0 1 0 0 1 2 0 2 1 3 0 = false.
Proof.
  unfold contains_b.
  destruct (Rlt_dec 0 (gdbl 0 0 1 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 0 0 1 0 0 1 (mkPoint 2 0))) as [Hlt | _];
    [ | reflexivity ].
  exfalso. unfold gtri in Hlt.
  assert (H : gsA 0 0 1 0 (mkPoint 2 0) = 0) by (unfold gsA; simpl; ring).
  rewrite H in Hlt.
  eapply Rlt_not_le in Hlt.
  apply Hlt. eapply Rle_trans; [apply Rmin_l_le | apply Rmin_l_le].
Qed.

Lemma cw_pair_no_partial_edge :
  touch_partial_edge_b
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint 2 0) (mkPoint 2 1) (mkPoint 3 0) = false.
Proof.
  unfold touch_partial_edge_b, some_vertex_on_open_edges,
         vertex_on_open_edges, on_open_seg_b, cross.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma cw_pair_no_onesided :
  touch_onesided_t_b
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint 2 0) (mkPoint 2 1) (mkPoint 3 0) = false.
Proof.
  unfold touch_onesided_t_b, some_vertex_on_open_edges,
         vertex_on_open_edges, on_open_seg_b, cross.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma touch_obtuse_vertex_b_false_of_non_ccw :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    ~ (0 < gdbl ax ay bx by_ cx cy)
    \/ ~ (0 < gdbl dx dy ex ey fx fy) ->
    touch_obtuse_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy = false.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy H.
  unfold touch_obtuse_vertex_b.
  destruct (Rlt_dec 0 (gdbl ax ay bx by_ cx cy)) as [HA | _];
    [| reflexivity ].
  destruct (Rlt_dec 0 (gdbl dx dy ex ey fx fy)) as [HB | _];
    [| reflexivity ].
  exfalso. destruct H as [Hn | Hn]; apply Hn; assumption.
Qed.

Lemma mixed_cone_vertex_b_false_of_non_ccw :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    ~ (0 < gdbl ax ay bx by_ cx cy)
    \/ ~ (0 < gdbl dx dy ex ey fx fy) ->
    mixed_cone_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy = false.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy H.
  unfold mixed_cone_vertex_b.
  destruct (Rlt_dec 0 (gdbl ax ay bx by_ cx cy)) as [HA | _];
    [| reflexivity ].
  destruct (Rlt_dec 0 (gdbl dx dy ex ey fx fy)) as [HB | _];
    [| reflexivity ].
  exfalso. destruct H as [Hn | Hn]; apply Hn; assumption.
Qed.

Lemma same_cone_vertex_b_false_of_non_ccw :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    ~ (0 < gdbl ax ay bx by_ cx cy)
    \/ ~ (0 < gdbl dx dy ex ey fx fy) ->
    same_cone_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy = false.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy H.
  unfold same_cone_vertex_b.
  destruct (Rlt_dec 0 (gdbl ax ay bx by_ cx cy)) as [HA | _];
    [| reflexivity ].
  destruct (Rlt_dec 0 (gdbl dx dy ex ey fx fy)) as [HB | _];
    [| reflexivity ].
  exfalso. destruct H as [Hn | Hn]; apply Hn; assumption.
Qed.

Lemma cw_pair_regime_unsupported :
  triangle_pair_regime 0 0 1 0 0 1 2 0 2 1 3 0 = TPR_Unsupported.
Proof.
  unfold triangle_pair_regime.
  rewrite cw_pair_no_touch_edge.
  rewrite cw_pair_no_contains.
  rewrite (overlap_b_false_of_non_ccw 0 0 1 0 0 1 2 0 2 1 3 0
             (or_intror cw_B_gdbl_nlt)).
  rewrite (separated_b_false_of_non_ccw 0 0 1 0 0 1 2 0 2 1 3 0
             (or_intror cw_B_gdbl_nlt)).
  rewrite (touch_vertex_b_false_of_non_ccw 0 0 1 0 0 1 2 0 2 1 3 0
             (or_intror cw_B_gdbl_nlt)).
  rewrite cw_pair_no_partial_edge.
  rewrite cw_pair_no_onesided.
  rewrite (touch_obtuse_vertex_b_false_of_non_ccw 0 0 1 0 0 1 2 0 2 1 3 0
             (or_intror cw_B_gdbl_nlt)).
  rewrite (mixed_cone_vertex_b_false_of_non_ccw 0 0 1 0 0 1 2 0 2 1 3 0
             (or_intror cw_B_gdbl_nlt)).
  rewrite (same_cone_vertex_b_false_of_non_ccw 0 0 1 0 0 1 2 0 2 1 3 0
             (or_intror cw_B_gdbl_nlt)).
  reflexivity.
Qed.

Theorem naive_box_disjoint_is_unsound :
  boxes_strictly_apart 0 0 1 1 2 0 3 1 = true /\
  relate (triangle_geometry 0 0 1 0 0 1)
         (triangle_geometry 2 0 2 1 3 0)
  = im_unsupported /\
  evaluate (prepare (triangle_geometry 0 0 1 0 0 1))
           (triangle_geometry 2 0 2 1 3 0)
  = im_unsupported.
Proof.
  split; [exact boxes_apart_unit_vs_cw|].
  split.
  - rewrite relate_on_triangles_dispatches.
    rewrite cw_pair_regime_unsupported.
    unfold tris_relate. apply triangle_pair_fill_unsupported_eq.
  - rewrite prepared_evaluate_agrees.
    rewrite relate_on_triangles_dispatches.
    rewrite cw_pair_regime_unsupported.
    unfold tris_relate. apply triangle_pair_fill_unsupported_eq.
Qed.

(* -------------------------------------------------------------------------- *)
(* Mutation: a hand-corrupted triangle cache short-circuits to disjoint       *)
(* while one-shot relate declines.  `cache_coherent` is what catches it.      *)
(* -------------------------------------------------------------------------- *)

(* Far cache vs the #577 T-junction B.  Relate of that pair is the landed
   decline `tjunction_pair_unsupported`; evaluate still short-circuits. *)
Lemma far_cache_separated_b :
  separated_b 10 0 11 0 10 1 1 0 3 0 2 1 = true.
Proof.
  unfold separated_b, some_edge_separates_b, edge_separates_b, opposite_sides_b.
  destruct (Rlt_dec 0 (gdbl 10 0 11 0 10 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 1 0 3 0 2 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  cbn [px py].
  (* (10,0)-(11,0) does not separate (B meets y=0). *)
  destruct (Rlt_dec (cross (mkPoint 10 0) (mkPoint 11 0) (mkPoint 10 1)
                    * cross (mkPoint 10 0) (mkPoint 11 0) (mkPoint 1 0)) 0)
    as [Hbot | _];
    [ exfalso; unfold cross in Hbot; cbn [px py] in Hbot; lra | ].
  (* (11,0)-(10,1) is same-side of B. *)
  destruct (Rlt_dec (cross (mkPoint 11 0) (mkPoint 10 1) (mkPoint 10 0)
                    * cross (mkPoint 11 0) (mkPoint 10 1) (mkPoint 1 0)) 0)
    as [Hbot | _];
    [ exfalso; unfold cross in Hbot; cbn [px py] in Hbot; lra | ].
  (* Vertical x=10, apex (11,0): B is strictly to the left. *)
  destruct (Rlt_dec (cross (mkPoint 10 1) (mkPoint 10 0) (mkPoint 11 0)
                    * cross (mkPoint 10 1) (mkPoint 10 0) (mkPoint 1 0)) 0)
    as [_ | Hn];
    [ | exfalso; apply Hn; unfold cross; cbn [px py]; lra ].
  destruct (Rlt_dec (cross (mkPoint 10 1) (mkPoint 10 0) (mkPoint 11 0)
                    * cross (mkPoint 10 1) (mkPoint 10 0) (mkPoint 3 0)) 0)
    as [_ | Hn];
    [ | exfalso; apply Hn; unfold cross; cbn [px py]; lra ].
  destruct (Rlt_dec (cross (mkPoint 10 1) (mkPoint 10 0) (mkPoint 11 0)
                    * cross (mkPoint 10 1) (mkPoint 10 0) (mkPoint 2 1)) 0)
    as [_ | Hn];
    [ | exfalso; apply Hn; unfold cross; cbn [px py]; lra ].
  reflexivity.
Qed.

Lemma far_cache_regime_disjoint :
  triangle_pair_regime 10 0 11 0 10 1 1 0 3 0 2 1 = TPR_Disjoint.
Proof.
  apply triangle_pair_regime_disjoint, far_cache_separated_b.
Qed.

Lemma aa_matrix_disjoint_neq_unsupported :
  aa_matrix_disjoint <> im_unsupported.
Proof.
  intro H.
  apply im_unsupported_not_disjoint.
  rewrite <- H.
  exact aa_matrix_disjoint_witness.
Qed.

Theorem corrupted_cache_disagrees :
  let A := triangle_geometry 0 0 2 0 0 1 in
  let B := triangle_geometry 1 0 3 0 2 1 in
  let pg := {| pg_geom := A;
               pg_cache := None;
               pg_tri_cache := Some (10, 0, 11, 0, 10, 1) |} in
  evaluate pg B = aa_matrix_disjoint /\
  relate A B = im_unsupported /\
  evaluate pg B <> relate A B /\
  ~ cache_coherent pg.
Proof.
  split.
  - unfold evaluate, evaluate_from_tri_cache. simpl.
    rewrite far_cache_regime_disjoint. reflexivity.
  - split.
    + rewrite relate_on_triangles_dispatches.
      unfold tris_relate.
      exact tjunction_pair_unsupported.
    + split.
      * rewrite relate_on_triangles_dispatches.
        unfold evaluate, evaluate_from_tri_cache. simpl.
        rewrite far_cache_regime_disjoint.
        unfold tris_relate.
        rewrite tjunction_pair_unsupported.
        exact aa_matrix_disjoint_neq_unsupported.
      * intros [_ Htr]. cbn in Htr.
        apply (f_equal
                 (fun o =>
                    match o with
                    | Some (((((x, _), _), _), _), _) => x
                    | None => 0
                    end)) in Htr.
        cbn in Htr. lra.
Qed.

(* Footers last so a mid-file failure is not buried under axiom dumps. *)
Print Assumptions prepared_evaluate_agrees.
Print Assumptions evaluate_coherent_agrees.
Print Assumptions prepare_cache_coherent.
Print Assumptions prepared_evaluate_cache_short_circuit.
Print Assumptions naive_box_disjoint_is_unsound.
Print Assumptions corrupted_cache_disagrees.
