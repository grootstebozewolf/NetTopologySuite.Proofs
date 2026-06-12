(* ============================================================================
   NetTopologySuite.Proofs.FaceTwinAware
   ----------------------------------------------------------------------------
   extract_rings_valid R5, bridge follow-up: steps (1)+(2) of the corrected
   discharge plan (docs/extract-faces-bridge.md §"corrected discharge plan").

   Slice 3i machine-checked that the extractors' H1
   `pairwise_no_proper_cross (result_darts op g)` is UNSATISFIABLE for any
   non-degenerate edge: `darts_of` carries every dart together with its twin,
   and a segment properly crosses its own reversal
   (ExtractFacesBridge.seg_properly_crosses_reversal).  This file lands the
   corrected shape:

     (1) `pairwise_no_proper_cross_twin_aware` -- the twin-aware simplicity
         predicate (reverse pairs excluded).  SATISFIABLE on `darts_of`:
         `darts_of_twin_aware` derives it from `pairwise_no_proper_cross` on
         the UNDIRECTED edge set, which is exactly the interface the
         geometric step (3) will discharge from a strengthened
         `fully_intersected`.
     (2) `face_twin_free` + the re-proved simplicity chain
         (`ring_simple_of_subset_twin_aware`, `face_ring_simple_twin_aware`,
         ... , `extract_faces_valid_twin_aware` and the with-holes mirror):
         the full-`D` appeal of FaceRingSimple.face_ring_simple is replaced
         by the twin-aware predicate plus per-face twin-freeness.

   CORRECTION to the plan doc's step-2 wording, found while building this
   slice: "a face ring of an arrangement_ok set with period >= 3 contains no
   dart together with its twin" is NOT provable as stated.  `next` wraps to
   the fan minimum (DartNext.v:148), so at a degree-1 tip
   `fstep D x = twin x`: an ANTENNA (a polygon with a dangling edge) has a
   face walk of period >= 3 that contains a twin pair while passing `fan_ok`
   (singleton fans are vacuously ok) and `no_short_faces`.
   `spur_breaks_face_twin_free` records the easy half (a spur step breaks
   twin-freeness); deriving `face_twin_free` from a no-spur / no-dangling-
   edge condition (the innermost-return induction) is its own follow-up
   rung.  Until then `face_twin_free` is carried as a named per-face
   hypothesis -- satisfiable, unlike the H1 it replaces.

   Pure dart + ring combinatorics plus one `lra` reparametrisation; no
   `Admitted` / `Axiom` / `Parameter`; allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Arith Lia.
From NTS.Proofs Require Import Distance Overlay OverlayGraph BufferAssembly
                               RingExtract RingSimple Vec Direction Azimuth
                               Dart DartAngularOrder DartNext DartNextSpec
                               DartNextInjective OrbitCycle DartFace FaceChain
                               FaceRingSimple FacePolygon FacePolygonHoles
                               ExtractFaces ExtractFacesHoles.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The twin-aware simplicity predicate (corrected-plan step 1).            *)
(* -------------------------------------------------------------------------- *)

Definition pairwise_no_proper_cross_twin_aware (D : list Dart) : Prop :=
  forall d1 d2 : Dart,
    In d1 D -> In d2 D -> d1 <> d2 -> d1 <> twin d2 ->
    ~ segments_intersect_properly (fst d1) (snd d1) (fst d2) (snd d2).

(* -------------------------------------------------------------------------- *)
(* §2  Reversal reparametrisation: proper crossing is stable under flipping    *)
(* either segment (t |-> 1-t / s |-> 1-s).                                     *)
(* -------------------------------------------------------------------------- *)

Lemma sip_swap_right :
  forall P0 P1 Q0 Q1 : Point,
    segments_intersect_properly P0 P1 Q1 Q0 ->
    segments_intersect_properly P0 P1 Q0 Q1.
Proof.
  intros P0 P1 Q0 Q1 (t & s & Ht & Hs & Hx & Hy).
  exists t, (1 - s). repeat split; try lra.
Qed.

Lemma sip_swap_left :
  forall P0 P1 Q0 Q1 : Point,
    segments_intersect_properly P1 P0 Q0 Q1 ->
    segments_intersect_properly P0 P1 Q0 Q1.
Proof.
  intros P0 P1 Q0 Q1 (t & s & Ht & Hs & Hx & Hy).
  exists (1 - t), s. repeat split; try lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Satisfiability: the undirected pairwise predicate lifts to the          *)
(* twin-aware predicate on `darts_of` -- the bridge target for step (3).       *)
(* -------------------------------------------------------------------------- *)

(* Decidable dart equality, inherited componentwise from `point_eq_dec`. *)
Lemma dart_eq_dec : forall d e : Dart, {d = e} + {d <> e}.
Proof.
  intros [a b] [c f].
  destruct (point_eq_dec a c) as [-> | Hac];
    [ destruct (point_eq_dec b f) as [-> | Hbf] | ].
  - left. reflexivity.
  - right. intro H. apply Hbf. inversion H. reflexivity.
  - right. intro H. apply Hac. inversion H. reflexivity.
Qed.

Lemma darts_of_twin_aware :
  forall E : list Edge,
    pairwise_no_proper_cross E ->
    pairwise_no_proper_cross_twin_aware (darts_of E).
Proof.
  intros E HE d1 d2 H1 H2 Hne Hnt Hsip.
  unfold darts_of in H1, H2.
  apply in_app_or in H1. apply in_app_or in H2.
  (* Reduce each dart to its underlying undirected edge. *)
  destruct H1 as [H1 | H1]; destruct H2 as [H2 | H2].
  - (* both original *)
    exact (HE d1 d2 H1 H2 Hne Hsip).
  - (* d2 = twin e2 *)
    apply in_map_iff in H2. destruct H2 as [e2 [He2 HinE2]]. subst d2.
    destruct (dart_eq_dec d1 e2) as [-> | Hne12].
    + (* d1 = e2: then d1 = twin (twin d1) -- excluded by Hnt *)
      apply Hnt. rewrite twin_involutive. reflexivity.
    + apply (HE d1 e2 H1 HinE2 Hne12).
      apply sip_swap_right. exact Hsip.
  - (* d1 = twin e1 *)
    apply in_map_iff in H1. destruct H1 as [e1 [He1 HinE1]]. subst d1.
    destruct (dart_eq_dec e1 d2) as [-> | Hne12].
    + (* e1 = d2: then d1 = twin d2 -- excluded by Hnt *)
      apply Hnt. reflexivity.
    + apply (HE e1 d2 HinE1 H2 Hne12).
      apply sip_swap_left. exact Hsip.
  - (* both twins *)
    apply in_map_iff in H1. destruct H1 as [e1 [He1 HinE1]]. subst d1.
    apply in_map_iff in H2. destruct H2 as [e2 [He2 HinE2]]. subst d2.
    destruct (dart_eq_dec e1 e2) as [-> | Hne12].
    + apply Hne. reflexivity.
    + apply (HE e1 e2 HinE1 HinE2 Hne12).
      apply sip_swap_left, sip_swap_right. exact Hsip.
Qed.

(* Sanity contrast with slice 3i's `darts_of_nondeg_not_pairwise`: the
   twin-aware predicate IS satisfiable on the darts of a non-degenerate
   edge set. *)
Corollary darts_of_singleton_twin_aware :
  forall e : Edge, pairwise_no_proper_cross_twin_aware (darts_of [e]).
Proof.
  intro e. apply darts_of_twin_aware.
  intros e1 e2 H1 H2 Hne.
  destruct H1 as [<- | []]. destruct H2 as [<- | []].
  exfalso. apply Hne. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Face twin-freeness and the re-proved simplicity chain (step 2).         *)
(* -------------------------------------------------------------------------- *)

(* No dart of the face walk appears together with its twin. *)
Definition face_twin_free (D : list Dart) (d : Dart) (n : nat) : Prop :=
  forall x, In x (dart_walk D d n) -> ~ In (twin x) (dart_walk D d n).

(* A face segment IS its dart (`Dart = Edge = Point*Point`). *)
Lemma map_seg_of_id : forall l : list Dart, map seg_of l = l.
Proof.
  induction l as [| x l IH]; cbn.
  - reflexivity.
  - rewrite IH. unfold seg_of, dbase, dtip.
    rewrite <- surjective_pairing. reflexivity.
Qed.

(* The twin-aware replacement for `ring_simple_of_subset D`: ring edges
   drawn from a twin-free window W of a twin-aware arrangement D. *)
Theorem ring_simple_of_subset_twin_aware :
  forall (D W : list Dart) (r : Ring),
    pairwise_no_proper_cross_twin_aware D ->
    (forall x, In x W -> In x D) ->
    (forall x, In x W -> ~ In (twin x) W) ->
    (forall e, In e (ring_edges r) -> In e W) ->
    ring_simple r.
Proof.
  intros D W r Hpw HWD Htf Hsub e1 e2 H1 H2 Hne.
  apply (Hpw e1 e2).
  - apply HWD, Hsub. exact H1.
  - apply HWD, Hsub. exact H2.
  - exact Hne.
  - intro Heq.
    apply (Htf e2 (Hsub _ H2)).
    rewrite <- Heq. exact (Hsub _ H1).
Qed.

(* face_ring_simple without the full-D pairwise appeal. *)
Theorem face_ring_simple_twin_aware :
  forall D, arrangement_ok D -> pairwise_no_proper_cross_twin_aware D ->
    forall d, In d D -> forall n, (1 <= n)%nat -> iter (fstep D) n d = d ->
    face_twin_free D d n ->
    ring_simple (ring_of_chain (face_chain D d n)).
Proof.
  intros D Hok Hpw d Hd n Hn Hret Htf.
  assert (Hcc : closed_chain (face_chain D d n))
    by (apply face_chain_closed_chain; assumption).
  apply (ring_simple_of_subset_twin_aware D (dart_walk D d n)).
  - exact Hpw.
  - intros x Hx. exact (dart_walk_subset D (proj1 Hok) n d Hd x Hx).
  - exact Htf.
  - intros e He.
    rewrite (ring_edges_of_closed_chain (face_chain D d n) Hcc) in He.
    unfold face_chain in He. rewrite map_seg_of_id in He. exact He.
Qed.

Theorem face_ring_combinatorial_valid_twin_aware :
  forall D, arrangement_ok D -> pairwise_no_proper_cross_twin_aware D ->
    forall d, In d D -> forall n, (3 <= n)%nat -> iter (fstep D) n d = d ->
    face_twin_free D d n ->
    ring_closed (ring_of_chain (face_chain D d n)) /\
    ring_has_minimum_points (ring_of_chain (face_chain D d n)) /\
    ring_simple (ring_of_chain (face_chain D d n)).
Proof.
  intros D Hok Hpw d Hd n Hn Hret Htf.
  destruct (face_ring_valid_shape D Hok d Hd n Hn Hret) as [Hcl [Hmin _]].
  repeat split.
  - exact Hcl.
  - exact Hmin.
  - apply face_ring_simple_twin_aware;
      [ exact Hok | exact Hpw | exact Hd | lia | exact Hret | exact Htf ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  The polygon layer, twin-aware.                                          *)
(* -------------------------------------------------------------------------- *)

Theorem face_polygon_valid_twin_aware :
  forall D, arrangement_ok D -> pairwise_no_proper_cross_twin_aware D ->
    forall d, In d D -> forall n, (3 <= n)%nat -> iter (fstep D) n d = d ->
    face_twin_free D d n ->
    valid_polygon (face_polygon D d n).
Proof.
  intros D Hok Hpw d Hd n Hn Hret Htf.
  destruct (face_ring_combinatorial_valid_twin_aware D Hok Hpw d Hd n Hn Hret Htf)
    as [Hcl [Hmin Hsimp]].
  unfold face_polygon, valid_polygon. cbn [outer_ring hole_rings].
  split; [ exact Hcl | ].
  split; [ exact Hsimp | ].
  split; [ exact Hmin | ].
  intros hr Hin. destruct Hin.
Qed.

Corollary face_outer_polygon_valid_twin_aware :
  forall D, arrangement_ok D -> pairwise_no_proper_cross_twin_aware D ->
    forall d, In d D -> forall n, (3 <= n)%nat -> iter (fstep D) n d = d ->
    face_twin_free D d n ->
    forall holes : list Ring,
      (forall h, In h holes ->
          ring_closed h /\ ring_simple h /\ ring_has_minimum_points h
          /\ hole_inside_outer (ring_of_chain (face_chain D d n)) h) ->
      valid_polygon (mkPolygon (ring_of_chain (face_chain D d n)) holes).
Proof.
  intros D Hok Hpw d Hd n Hn Hret Htf holes Hholes.
  destruct (face_ring_combinatorial_valid_twin_aware D Hok Hpw d Hd n Hn Hret Htf)
    as [Hcl [Hmin Hsi]].
  apply polygon_valid_of_rings; [ exact Hcl | exact Hsi | exact Hmin | exact Hholes ].
Qed.

(* Hole specs now carry per-hole twin-freeness alongside the period clause. *)
Theorem face_polygon_holes_valid_twin_aware :
  forall D, arrangement_ok D -> pairwise_no_proper_cross_twin_aware D ->
    forall d, In d D -> forall n, (3 <= n)%nat -> iter (fstep D) n d = d ->
    face_twin_free D d n ->
    forall (hspecs : list (Dart * nat)),
      (forall s, In s hspecs ->
          In (fst s) D /\ (3 <= snd s)%nat /\ iter (fstep D) (snd s) (fst s) = fst s
          /\ face_twin_free D (fst s) (snd s)) ->
      (forall s, In s hspecs ->
          hole_inside_outer (ring_of_chain (face_chain D d n)) (hole_ring_of D s)) ->
      valid_polygon (mkPolygon (ring_of_chain (face_chain D d n))
                               (map (hole_ring_of D) hspecs)).
Proof.
  intros D Hok Hpw d Hd n Hn Hret Htf hspecs Hspec Hinside.
  apply face_outer_polygon_valid_twin_aware; try assumption.
  intros h Hh. apply in_map_iff in Hh. destruct Hh as [s [Hs Hin]]. subst h.
  destruct (Hspec s Hin) as [HsD [Hsn [Hsret Hstf]]].
  destruct (face_ring_combinatorial_valid_twin_aware D Hok Hpw (fst s) HsD
              (snd s) Hsn Hsret Hstf) as [Hcl [Hmin Hsi]].
  split; [ exact Hcl | ]. split; [ exact Hsi | ]. split; [ exact Hmin | ].
  apply Hinside. exact Hin.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  The extractor headlines, twin-aware (the relocated obligations).        *)
(* These are the satisfiable bridge targets for corrected-plan step (3).       *)
(* -------------------------------------------------------------------------- *)

Theorem extract_faces_valid_twin_aware :
  forall op g,
    (forall v, fan_ok (outgoing v (result_darts op g))) ->
    pairwise_no_proper_cross_twin_aware (result_darts op g) ->
    no_short_faces (result_darts op g) ->
    (forall d, In d (result_darts op g) ->
       face_twin_free (result_darts op g) d (face_period (result_darts op g) d)) ->
    forall poly, In poly (extract_faces op g) -> valid_polygon poly.
Proof.
  intros op g Hfan Hpw Hmin Htf poly Hin.
  assert (Hok : arrangement_ok (result_darts op g))
    by (apply result_darts_arrangement_ok; exact Hfan).
  unfold extract_faces in Hin. apply in_map_iff in Hin.
  destruct Hin as [d [Hpoly Hd]]. subst poly.
  destruct (face_period_spec (result_darts op g) Hok d Hd) as [_ Hret].
  unfold face_polygon_at.
  apply (face_polygon_valid_twin_aware (result_darts op g) Hok Hpw d Hd
           (face_period (result_darts op g) d)).
  - apply Hmin. exact Hd.
  - exact Hret.
  - apply Htf. exact Hd.
Qed.

Theorem extract_faces_holes_valid_twin_aware :
  forall (hassign : Dart -> list Dart) (op : BooleanOp) (g : TopologyGraph),
    (forall v, fan_ok (outgoing v (result_darts op g))) ->
    pairwise_no_proper_cross_twin_aware (result_darts op g) ->
    no_short_faces (result_darts op g) ->
    (forall d, In d (result_darts op g) ->
       face_twin_free (result_darts op g) d (face_period (result_darts op g) d)) ->
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
    forall poly, In poly (extract_faces_holes hassign op g) -> valid_polygon poly.
Proof.
  intros hassign op g Hfan Hpw Hshort Htf Hwf Hinside poly Hin.
  assert (Hok : arrangement_ok (result_darts op g))
    by (apply result_darts_arrangement_ok; exact Hfan).
  unfold extract_faces_holes in Hin. apply in_map_iff in Hin.
  destruct Hin as [d [Hpoly Hd]]. subst poly.
  unfold face_polygon_holes_at.
  destruct (face_period_spec (result_darts op g) Hok d Hd) as [_ Hret].
  apply (face_polygon_holes_valid_twin_aware (result_darts op g) Hok Hpw d Hd
           (face_period (result_darts op g) d)).
  - apply Hshort. exact Hd.
  - exact Hret.
  - apply Htf. exact Hd.
  - intros s Hs.
    unfold hole_specs in Hs. apply in_map_iff in Hs.
    destruct Hs as [h [Hsh Hh]]. subst s. cbn [fst snd].
    assert (HhD : In h (result_darts op g)) by (exact (Hwf d Hd h Hh)).
    destruct (face_period_spec (result_darts op g) Hok h HhD) as [_ Hreth].
    split; [ exact HhD | ].
    split; [ apply Hshort; exact HhD | ].
    split; [ exact Hreth | apply Htf; exact HhD ].
  - intros s Hs.
    unfold hole_specs in Hs. apply in_map_iff in Hs.
    destruct Hs as [h [Hsh Hh]]. subst s.
    exact (Hinside d Hd h Hh).
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  The spur record (the honest half of the plan-doc correction).           *)
(*                                                                            *)
(* A spur step (`fstep D x = twin x`, i.e. a degree-1 tip) puts a twin pair    *)
(* in the walk immediately.  The converse programme -- deriving                *)
(* `face_twin_free` from a no-spur condition via the innermost-return          *)
(* induction -- is the next rung; the antenna configuration (header) shows     *)
(* `fan_ok` + `no_short_faces` alone do NOT suffice.                           *)
(* -------------------------------------------------------------------------- *)

Lemma spur_breaks_face_twin_free :
  forall D (x : Dart) (n : nat),
    (2 <= n)%nat ->
    fstep D x = twin x ->
    ~ face_twin_free D x n.
Proof.
  intros D x n Hn Hspur Htf.
  destruct n as [| [| k]]; [ lia | lia | ].
  apply (Htf x).
  - cbn. left. reflexivity.
  - cbn. rewrite Hspur. right. left. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure combinatorics + one lra reparametrisation; allowlist     *)
(* axioms only.                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions darts_of_twin_aware.
Print Assumptions ring_simple_of_subset_twin_aware.
Print Assumptions face_ring_simple_twin_aware.
Print Assumptions face_ring_combinatorial_valid_twin_aware.
Print Assumptions face_polygon_valid_twin_aware.
Print Assumptions face_polygon_holes_valid_twin_aware.
Print Assumptions extract_faces_valid_twin_aware.
Print Assumptions extract_faces_holes_valid_twin_aware.
Print Assumptions spur_breaks_face_twin_free.
