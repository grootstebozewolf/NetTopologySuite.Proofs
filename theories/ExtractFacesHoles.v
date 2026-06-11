(* ============================================================================
   NetTopologySuite.Proofs.ExtractFacesHoles
   ----------------------------------------------------------------------------
   extract_rings_valid R5, slice 3h: WITH-HOLES EMISSION -- the first
   item of `docs/extract-faces.md` "What remains".

   Slice 3f (`FacePolygonHoles.v`) assembled the with-holes
   `valid_polygon` from face rings, isolating the residual to exactly
   one analytic input (`hole_inside_outer`); slice 3g
   (`ExtractFaces.v`) rewired the extractor to emit face polygons --
   but only HOLE-FREE ones.  This slice closes the emission gap: an
   extractor that emits polygons WITH holes, with the hole-to-shell
   NESTING supplied as an abstract oracle (the same
   spec-conditional-oracle discipline as the curve lane's `g1dec`:
   deciding which face nests inside which is point-set work the
   combinatorial layer cannot do, so the assignment is a parameter and
   every theorem is conditional only on its spec).

     - `hassign : Dart -> list Dart` -- the nesting oracle: for each
       shell dart, the representative darts of the faces nested inside
       it.  Slice 3e's orientation classifier (`FaceOrientation.v`,
       CCW/CW) is the intended combinatorial half of computing it; the
       analytic half is exactly the residual below.

     - `extract_faces_holes`: one polygon per surviving dart, outer
       ring the dart's face ring, holes the face rings of the assigned
       darts (periods computed by `face_period`, as in slice 3g).

     - `extract_faces_holes_valid` (HEADLINE): under slice 3g's three
       structural noder hypotheses (`fan_ok` / `pairwise_no_proper_cross`
       / `no_short_faces`) plus the oracle's two spec clauses --
       (i) WELL-FORMEDNESS: assigned darts are result darts, and
       (ii) NESTING: each assigned face ring is `hole_inside_outer`
       its shell's face ring -- every emitted polygon is
       `valid_polygon`.  Clause (ii) is the SOLE analytic input: the
       same single JCT-adjacent seam as
       `overlay_ng_correct_conditional` H1, exactly as the
       proof-structure doc's §4 prescribes, now carried by an emitting
       extractor rather than only by an assembly lemma.

     - `extract_faces_holes_nil` (coherence): with the empty
       assignment the extractor IS slice 3g's hole-free
       `extract_faces`.

     - `extract_faces_holes_label_fidelity` (+ the outer/hole
       edges-subset lemmas): every edge of every emitted ring -- outer
       or hole -- is (an orientation of) an op-kept labelled edge; the
       with-holes extractor invents no geometry.

   Pure assembly; no `Admitted` / `Axiom` / `Parameter`.  Axioms: the
   standard three-axiom classical-reals base, introduces none of its
   own.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import List Arith Lia.
From NTS.Proofs Require Import Distance Overlay OverlayGraph BufferAssembly
                               RingExtract RingSimple Vec Direction Azimuth
                               Dart DartAngularOrder DartNext DartNextSpec
                               DartNextInjective OrbitCycle DartFace FaceChain
                               FaceRingSimple FacePolygon FacePolygonHoles
                               ExtractFaces.

Import ListNotations.

Section HolesEmission.

  (* The nesting oracle: for each shell dart, the representative darts of    *)
  (* the faces assigned as its holes.  Abstract; theorems depend only on     *)
  (* the spec clauses carried by the headline.                               *)
  Variable hassign : Dart -> list Dart.

  (* Periods are computed, as in slice 3g.                                   *)
  Definition hole_specs (D : list Dart) (d : Dart) : list (Dart * nat) :=
    map (fun h => (h, face_period D h)) (hassign d).

  Definition face_polygon_holes_at (D : list Dart) (d : Dart) : Polygon :=
    mkPolygon (ring_of_chain (face_chain D d (face_period D d)))
              (map (hole_ring_of D) (hole_specs D d)).

  Definition extract_faces_holes (op : BooleanOp) (g : TopologyGraph)
      : Geometry :=
    map (face_polygon_holes_at (result_darts op g)) (result_darts op g).

  (* Coherence: the empty assignment recovers the hole-free extractor.       *)
  Lemma extract_faces_holes_nil :
    (forall d, hassign d = []) ->
    forall op g, extract_faces_holes op g = extract_faces op g.
  Proof.
    intros Hnil op g.
    unfold extract_faces_holes, extract_faces.
    apply map_ext. intros d.
    unfold face_polygon_holes_at, hole_specs.
    rewrite Hnil. cbn [map].
    reflexivity.
  Qed.

  (* HEADLINE: with-holes emission is valid, conditional on the noder's      *)
  (* three structural hypotheses and the oracle's spec -- whose nesting      *)
  (* clause is the lane's single analytic residual.                          *)
  Theorem extract_faces_holes_valid :
    forall op g,
      (forall v, fan_ok (outgoing v (result_darts op g))) ->
      pairwise_no_proper_cross (result_darts op g) ->
      no_short_faces (result_darts op g) ->
      (* oracle spec (i): well-formedness *)
      (forall d, In d (result_darts op g) ->
         forall h, In h (hassign d) -> In h (result_darts op g)) ->
      (* oracle spec (ii): nesting -- the sole analytic input *)
      (forall d, In d (result_darts op g) ->
         forall h, In h (hassign d) ->
         hole_inside_outer
           (ring_of_chain (face_chain (result_darts op g) d
                             (face_period (result_darts op g) d)))
           (hole_ring_of (result_darts op g)
              (h, face_period (result_darts op g) h))) ->
      forall poly, In poly (extract_faces_holes op g) -> valid_polygon poly.
  Proof.
    intros op g Hfan Hpw Hshort Hwf Hinside poly Hin.
    assert (Hok : arrangement_ok (result_darts op g))
      by (apply result_darts_arrangement_ok; exact Hfan).
    unfold extract_faces_holes in Hin. apply in_map_iff in Hin.
    destruct Hin as [d [Hpoly Hd]]. subst poly.
    unfold face_polygon_holes_at.
    destruct (face_period_spec (result_darts op g) Hok d Hd) as [_ Hret].
    apply (face_polygon_holes_valid (result_darts op g) Hok Hpw d Hd
             (face_period (result_darts op g) d)).
    - apply Hshort. exact Hd.
    - exact Hret.
    - (* oracle spec (i) discharges the hole-spec well-formedness *)
      intros s Hs.
      unfold hole_specs in Hs. apply in_map_iff in Hs.
      destruct Hs as [h [Hsh Hh]]. subst s. cbn [fst snd].
      assert (HhD : In h (result_darts op g)) by (exact (Hwf d Hd h Hh)).
      destruct (face_period_spec (result_darts op g) Hok h HhD) as [_ Hreth].
      split; [ exact HhD | ].
      split; [ apply Hshort; exact HhD | exact Hreth ].
    - (* oracle spec (ii) is exactly the per-hole nesting input *)
      intros s Hs.
      unfold hole_specs in Hs. apply in_map_iff in Hs.
      destruct Hs as [h [Hsh Hh]]. subst s.
      exact (Hinside d Hd h Hh).
  Qed.

  (* ------------------------------------------------------------------ *)
  (* §2  Label fidelity: the with-holes extractor invents no geometry,   *)
  (*     holes included (the slice-3g fidelity story, completed).        *)
  (* ------------------------------------------------------------------ *)

  Theorem extract_faces_holes_outer_edges_subset :
    forall op g,
      (forall v, fan_ok (outgoing v (result_darts op g))) ->
      forall poly, In poly (extract_faces_holes op g) ->
        forall e, In e (ring_edges (outer_ring poly)) ->
          In e (result_darts op g).
  Proof.
    intros op g Hfan poly Hin e He.
    assert (Hok : arrangement_ok (result_darts op g))
      by (apply result_darts_arrangement_ok; exact Hfan).
    unfold extract_faces_holes in Hin. apply in_map_iff in Hin.
    destruct Hin as [d [Hpoly Hd]]. subst poly.
    unfold face_polygon_holes_at in He. cbn [outer_ring] in He.
    destruct (face_period_spec (result_darts op g) Hok d Hd) as [Hge1 Hret].
    rewrite (ring_edges_of_closed_chain _
               (face_chain_closed_chain (result_darts op g) Hok d Hd
                  (face_period (result_darts op g) d) Hge1 Hret)) in He.
    exact (face_chain_subset (result_darts op g) (proj1 Hok)
             (face_period (result_darts op g) d) d Hd e He).
  Qed.

  Theorem extract_faces_holes_hole_edges_subset :
    forall op g,
      (forall v, fan_ok (outgoing v (result_darts op g))) ->
      (forall d, In d (result_darts op g) ->
         forall h, In h (hassign d) -> In h (result_darts op g)) ->
      forall poly, In poly (extract_faces_holes op g) ->
        forall hr, In hr (hole_rings poly) ->
          forall e, In e (ring_edges hr) ->
            In e (result_darts op g).
  Proof.
    intros op g Hfan Hwf poly Hin hr Hhr e He.
    assert (Hok : arrangement_ok (result_darts op g))
      by (apply result_darts_arrangement_ok; exact Hfan).
    unfold extract_faces_holes in Hin. apply in_map_iff in Hin.
    destruct Hin as [d [Hpoly Hd]]. subst poly.
    unfold face_polygon_holes_at in Hhr. cbn [hole_rings] in Hhr.
    apply in_map_iff in Hhr. destruct Hhr as [spec [Hsr Hspec]]. subst hr.
    unfold hole_specs in Hspec. apply in_map_iff in Hspec.
    destruct Hspec as [h [Hsh Hh]]. subst spec.
    assert (HhD : In h (result_darts op g)) by (exact (Hwf d Hd h Hh)).
    unfold hole_ring_of in He. cbn [fst snd] in He.
    destruct (face_period_spec (result_darts op g) Hok h HhD) as [Hge1 Hret].
    rewrite (ring_edges_of_closed_chain _
               (face_chain_closed_chain (result_darts op g) Hok h HhD
                  (face_period (result_darts op g) h) Hge1 Hret)) in He.
    exact (face_chain_subset (result_darts op g) (proj1 Hok)
             (face_period (result_darts op g) h) h HhD e He).
  Qed.

  (* The combined semantic bridge: every edge of every emitted ring --       *)
  (* outer or hole -- is (an orientation of) an op-kept labelled edge.       *)
  Corollary extract_faces_holes_label_fidelity :
    forall op g,
      (forall v, fan_ok (outgoing v (result_darts op g))) ->
      (forall d, In d (result_darts op g) ->
         forall h, In h (hassign d) -> In h (result_darts op g)) ->
      forall poly, In poly (extract_faces_holes op g) ->
        forall e,
          (In e (ring_edges (outer_ring poly)) \/
           exists hr, In hr (hole_rings poly) /\ In e (ring_edges hr)) ->
          exists l, (In (e, l) (tg_edges g) \/ In (twin e, l) (tg_edges g)) /\
                    edge_in_result op l = true.
  Proof.
    intros op g Hfan Hwf poly Hp e He.
    assert (Hd : In e (result_darts op g)).
    { destruct He as [He | [hr [Hhr He]]].
      - exact (extract_faces_holes_outer_edges_subset op g Hfan poly Hp e He).
      - exact (extract_faces_holes_hole_edges_subset op g Hfan Hwf poly Hp
                 hr Hhr e He). }
    apply in_result_darts_iff in Hd.
    destruct Hd as [Hd | Hd]; apply in_result_edges_iff in Hd;
      destruct Hd as [l [Hin Hlab]]; exists l.
    - split; [ left; exact Hin | exact Hlab ].
    - split; [ right; exact Hin | exact Hlab ].
  Qed.

End HolesEmission.

(* ========================================================================== *)
(* Axiom audit.  ALL headlines below are 3-axiom (classical-reals trio:      *)
(* sig_not_dec, sig_forall_dec, functional_extensionality_dep) or fewer.     *)
(* ========================================================================== *)

Print Assumptions extract_faces_holes_valid.
Print Assumptions extract_faces_holes_nil.
Print Assumptions extract_faces_holes_label_fidelity.
