(* ============================================================================
   NetTopologySuite.Proofs.CurveMiterJoin
   ----------------------------------------------------------------------------
   Buffer/noder pipeline, Stage 2b-CURVE seam, rung 13 (issue #65):
   the MITER assembly -- the last open join flavour of the 2b row,
   emitted as TWO CHORDS through `BufferMiter.miter_apex`.

   JTS miters only line-segment corners (`OffsetCurveBuilder`); arc
   joins are round by nature.  The connector here mirrors that with a
   fallback, exactly like JTS's miter-limit behaviour degrades to
   bevel:

     - at a CHORD-CHORD join, emit the miter PAIR: offset-end ->
       `miter_apex` -> offset-start (two chords through the
       Cramer's-rule intersection of the two offset lines, the JTS#180
       object whose geometry `BufferMiter.v` already certifies);
     - at any join involving an arc, fall back to rung 12's BEVEL
       chord.

   Because every connector is made of chords whose endpoints are
   DEFINED as the neighbouring offset endpoints (and the shared apex),
   all splice facts are definitional, and connectors contribute
   nothing to arc validity -- so the headline keeps the bevel
   assembly's lean hypothesis set:

     - `curve_ring_offset_miter_valid` (HEADLINE): any valid compound
       ring offset within the per-arc safety bound assembles -- offset
       segments + miter pairs / bevel fallbacks at every non-G1 join,
       closing join included -- into a `valid_curve_ring`, under ring
       validity + per-arc safety + the G1-decision spec only.
     - `miter_connector_apex_sound` (geometric tie-in): at a
       chord-chord join with non-degenerate, non-parallel edges, the
       emitted apex is at signed perpendicular distance `d` from BOTH
       source edge lines (`BufferMiter.miter_apex_on_both_offsets`) --
       the defining miter property, attached to the emitted edges.
       The miter-limit cap (`BufferMiterAngle.miter_cap_iff_sin_half`,
       JTS#180) speaks about this same apex.
     - `curve_ring_offset_miter_preserves_chords`: all-chord input
       gives all-chord output -- the pure LINEAR miter emitter.
     - `miter_emit_ring_closed`: the stage-3 handoff, as before.
     - `offset_walk_miter_smooth_eq_map`: smooth-case coherence.

   With this, the 2b row's join EMISSION story is complete: round
   (rungs 5-8), bevel (rung 12), miter (this rung) -- each a walk
   whose output is a valid compound ring.

   Pure-R; THREE-AXIOM THROUGHOUT (classical-reals trio).  No
   `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Bool.
From NTS.Proofs Require Import Distance Vec CurveGeometry Overlay ArcChordApprox.
From NTS.Proofs Require Import ArcOffsetThreePoint CurveRingOffset CurveRoundJoin.
From NTS.Proofs Require Import CurveOffsetAssembly CurveBevelJoin CurveLinearise.
From NTS.Proofs Require Import BufferOffset BufferMiter.

Import ListNotations.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Generic chain-gluing bricks (hd/last over cons and app).               *)
(* -------------------------------------------------------------------------- *)

Lemma last_app_nonnil {A : Type} : forall (l C : list A) (dflt : A),
  C <> [] -> last (l ++ C) dflt = last C dflt.
Proof.
  induction l as [| a l' IH]; intros C dflt Hne.
  - reflexivity.
  - cbn [app].
    destruct (l' ++ C) as [| x M] eqn:E.
    + apply app_eq_nil in E as [_ Ec]. contradiction.
    + change (last (x :: M) dflt = last C dflt).
      rewrite <- E. apply IH. exact Hne.
Qed.

Lemma curve_ring_adjacent_cons : forall (x : CurveSegment) (C : CurveRing) s0,
  C <> [] ->
  curve_segment_end x = curve_segment_start (hd s0 C) ->
  curve_ring_adjacent C ->
  curve_ring_adjacent (x :: C).
Proof.
  intros x [| c C'] s0 Hne Hseam HC.
  - contradiction.
  - split; [ exact Hseam | exact HC ].
Qed.

Lemma curve_ring_adjacent_app : forall (l C : CurveRing) (s0 : CurveSegment),
  l <> [] -> C <> [] ->
  curve_ring_adjacent l -> curve_ring_adjacent C ->
  curve_segment_end (last l s0) = curve_segment_start (hd s0 C) ->
  curve_ring_adjacent (l ++ C).
Proof.
  induction l as [| a l' IH]; intros C s0 Hl HC Hadj HCadj Hseam.
  - contradiction.
  - destruct l' as [| b l''].
    + cbn [app].
      apply (curve_ring_adjacent_cons a C s0 HC Hseam HCadj).
    + destruct Hadj as [Hab Hadj'].
      cbn [app]. split.
      * exact Hab.
      * apply (IH C s0);
          [ discriminate | exact HC | exact Hadj' | exact HCadj
          | exact Hseam ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The miter assembly.                                                    *)
(* -------------------------------------------------------------------------- *)

Section MiterAssembly.

  Variable d : R.

  Variable g1dec : CurveSegment -> CurveSegment -> bool.
  Hypothesis g1dec_spec : forall s1 s2,
    g1dec s1 s2 = true <-> segment_norm_end s1 = segment_norm_start s2.

  (* The miter connector: at a chord-chord join, two chords through the      *)
  (* apex of the two offset lines; otherwise rung 12's bevel chord.           *)
  Definition miter_connector (s1 s2 : CurveSegment) : CurveRing :=
    match s1, s2 with
    | CSChord p q, CSChord p2 q2 =>
        [ CSChord (curve_segment_end (curve_segment_offset s1 d))
                  (miter_apex (curve_segment_end s1)
                              (seg_vec p q) (seg_vec p2 q2) d)
        ; CSChord (miter_apex (curve_segment_end s1)
                              (seg_vec p q) (seg_vec p2 q2) d)
                  (curve_segment_start (curve_segment_offset s2 d)) ]
    | _, _ => [ bevel_join d s1 s2 ]
    end.

  (* The connector's chain spec: nonempty, internally adjacent, splicing     *)
  (* the neighbouring offset endpoints, contributing only chords.             *)
  Lemma miter_connector_spec : forall s1 s2 s0,
    miter_connector s1 s2 <> [] /\
    curve_ring_adjacent (miter_connector s1 s2) /\
    curve_segment_start (hd s0 (miter_connector s1 s2)) =
      curve_segment_end (curve_segment_offset s1 d) /\
    curve_segment_end (last (miter_connector s1 s2) s0) =
      curve_segment_start (curve_segment_offset s2 d) /\
    curve_ring_arcs_valid (miter_connector s1 s2).
  Proof.
    intros s1 s2 s0.
    destruct s1 as [p q | a1]; destruct s2 as [p2 q2 | a2];
      cbn [miter_connector];
      [ (* chord-chord: the apex pair *)
        split; [ discriminate | ];
        split; [ split; [ reflexivity | exact I ] | ];
        split; [ reflexivity | ];
        split; [ reflexivity | ];
        constructor; [ exact I | constructor; [ exact I | constructor ] ]
      | (* the three bevel-fallback cases *)
        split; [ discriminate | ];
        split; [ exact I | ];
        split; [ reflexivity | ];
        split; [ reflexivity | ];
        constructor; [ exact I | constructor ] .. ].
  Qed.

  (* The geometric tie-in: the emitted apex is at signed perpendicular       *)
  (* distance d from BOTH source edge lines (the JTS#180 miter property).    *)
  Theorem miter_connector_apex_sound : forall (p q p2 q2 : Point),
    p <> q -> p2 <> q2 ->
    miter_det (seg_vec p q) (seg_vec p2 q2) <> 0 ->
    signed_perp_dist q (seg_vec p q)
      (miter_apex q (seg_vec p q) (seg_vec p2 q2) d) = d /\
    signed_perp_dist q (seg_vec p2 q2)
      (miter_apex q (seg_vec p q) (seg_vec p2 q2) d) = d.
  Proof.
    intros p q p2 q2 Hpq Hpq2 Hdet.
    apply miter_apex_on_both_offsets;
      [ apply seg_vec_nonzero; exact Hpq
      | apply seg_vec_nonzero; exact Hpq2
      | exact Hdet ].
  Qed.

  (* §2a  The walk.                                                           *)

  Fixpoint offset_walk_miter (r : CurveRing) : CurveRing :=
    match r with
    | [] => []
    | s1 :: rest =>
        match rest with
        | [] => [curve_segment_offset s1 d]
        | s2 :: _ =>
            if g1dec s1 s2
            then curve_segment_offset s1 d :: offset_walk_miter rest
            else curve_segment_offset s1 d
                   :: (miter_connector s1 s2 ++ offset_walk_miter rest)
        end
    end.

  Lemma offset_walk_miter_eq : forall s1 s2 rest',
    offset_walk_miter (s1 :: s2 :: rest') =
    if g1dec s1 s2
    then curve_segment_offset s1 d :: offset_walk_miter (s2 :: rest')
    else curve_segment_offset s1 d
           :: (miter_connector s1 s2 ++ offset_walk_miter (s2 :: rest')).
  Proof. reflexivity. Qed.

  Definition curve_ring_offset_miter (r : CurveRing) : CurveRing :=
    match r with
    | [] => []
    | s0 :: _ =>
        if g1dec (last r s0) s0
        then offset_walk_miter r
        else offset_walk_miter r ++ miter_connector (last r s0) s0
    end.

  Lemma offset_walk_miter_head : forall s rest,
    exists t, offset_walk_miter (s :: rest) = curve_segment_offset s d :: t.
  Proof.
    intros s [| s2 rest'].
    - exists []. reflexivity.
    - rewrite offset_walk_miter_eq.
      destruct (g1dec s s2); eexists; reflexivity.
  Qed.

  Lemma offset_walk_miter_nonnil : forall s rest,
    offset_walk_miter (s :: rest) <> [].
  Proof.
    intros s rest H.
    destruct (offset_walk_miter_head s rest) as [t Ht].
    rewrite Ht in H. discriminate.
  Qed.

  Lemma offset_walk_miter_last : forall r s0,
    r <> [] ->
    last (offset_walk_miter r) (curve_segment_offset s0 d) =
    curve_segment_offset (last r s0) d.
  Proof.
    induction r as [| s1 rest IH]; intros s0 Hne.
    - contradiction.
    - destruct rest as [| s2 rest'].
      + reflexivity.
      + rewrite offset_walk_miter_eq.
        rewrite (last_cons_cons s1 s2 rest').
        destruct (g1dec s1 s2).
        * destruct (offset_walk_miter_head s2 rest') as [t Ht].
          rewrite Ht. rewrite last_cons_cons. rewrite <- Ht.
          apply IH. discriminate.
        * destruct (miter_connector_spec s1 s2 s0) as [HneC _].
          destruct (miter_connector s1 s2) as [| c C'] eqn:Ec;
            [ exact (False_ind _ (HneC eq_refl)) | ].
          cbn [app].
          rewrite last_cons_cons.
          change (c :: C' ++ offset_walk_miter (s2 :: rest'))
            with ((c :: C') ++ offset_walk_miter (s2 :: rest')).
          rewrite (last_app_nonnil (c :: C') _ _
                     (offset_walk_miter_nonnil s2 rest')).
          apply IH. discriminate.
  Qed.

  (* §2b  Arc validity and adjacency of the walk.                            *)

  Lemma offset_walk_miter_arcs_valid : forall r,
    curve_ring_arcs_valid r ->
    ring_offset_safe r d ->
    curve_ring_arcs_valid (offset_walk_miter r).
  Proof.
    induction r as [| s1 rest IH]; intros Hv Hsafe.
    - constructor.
    - destruct rest as [| s2 rest'].
      + constructor; [ | constructor ].
        apply curve_segment_offset_arc_valid;
          [ exact (Forall_inv Hv) | exact (Forall_inv Hsafe) ].
      + assert (Hoff : segment_arc_valid (curve_segment_offset s1 d))
          by (apply curve_segment_offset_arc_valid;
              [ exact (Forall_inv Hv) | exact (Forall_inv Hsafe) ]).
        assert (Hrest : curve_ring_arcs_valid (offset_walk_miter (s2 :: rest')))
          by (apply IH;
              [ exact (Forall_inv_tail Hv) | exact (Forall_inv_tail Hsafe) ]).
        rewrite offset_walk_miter_eq. destruct (g1dec s1 s2) eqn:E.
        * constructor; assumption.
        * destruct (miter_connector_spec s1 s2 s1) as [_ [_ [_ [_ HCv]]]].
          constructor; [ exact Hoff | ].
          apply (proj2 (Forall_app _ _ _)).
          split; [ exact HCv | exact Hrest ].
  Qed.

  Lemma offset_walk_miter_adjacent : forall r,
    curve_ring_arcs_valid r ->
    curve_ring_adjacent r ->
    curve_ring_adjacent (offset_walk_miter r).
  Proof.
    induction r as [| s1 rest IH]; intros Hv Hadj.
    - exact I.
    - destruct rest as [| s2 rest'].
      + exact I.
      + destruct Hadj as [Hj Hadj'].
        assert (Hv1 := Forall_inv Hv).
        assert (Hv2 := Forall_inv (Forall_inv_tail Hv)).
        assert (Hrest : curve_ring_adjacent (offset_walk_miter (s2 :: rest')))
          by (apply IH; [ exact (Forall_inv_tail Hv) | exact Hadj' ]).
        destruct (offset_walk_miter_head s2 rest') as [t Ht].
        rewrite offset_walk_miter_eq. destruct (g1dec s1 s2) eqn:E.
        * rewrite Ht. split.
          -- apply (segment_join_offset_continuous s1 s2 d Hv1 Hv2 Hj).
             apply (proj1 (g1dec_spec s1 s2)). exact E.
          -- rewrite <- Ht. exact Hrest.
        * destruct (miter_connector_spec s1 s2
                      (curve_segment_offset s2 d))
            as [HneC [HCadj [Hhd [Hlast _]]]].
          apply (curve_ring_adjacent_cons _ _
                   (curve_segment_offset s2 d)).
          -- destruct (miter_connector s1 s2);
               [ exact (False_ind _ (HneC eq_refl)) | discriminate ].
          -- (* end (offset s1) = start (hd (C ++ walk)) = start (hd C) *)
             destruct (miter_connector s1 s2) as [| c C'] eqn:Ec;
               [ exact (False_ind _ (HneC eq_refl)) | ].
             cbn [hd app] in *.
             symmetry. exact Hhd.
          -- (* adjacent (C ++ walk) *)
             apply (curve_ring_adjacent_app _ _
                      (curve_segment_offset s2 d));
               [ exact HneC | apply offset_walk_miter_nonnil
               | exact HCadj | exact Hrest | ].
             rewrite Hlast. rewrite Ht. reflexivity.
  Qed.

  (* §2c  HEADLINE.                                                           *)

  Theorem curve_ring_offset_miter_valid : forall r,
    valid_curve_ring r ->
    ring_offset_safe r d ->
    valid_curve_ring (curve_ring_offset_miter r).
  Proof.
    intros r [Hv [Hadj Hcl]] Hsafe.
    destruct r as [| s0 rest]; [ contradiction | ].
    assert (Hne : s0 :: rest <> @nil CurveSegment) by discriminate.
    assert (Hin : In (last (s0 :: rest) s0) (s0 :: rest))
      by (apply last_in; exact Hne).
    assert (Hvlast : segment_arc_valid (last (s0 :: rest) s0))
      by (exact (proj1 (Forall_forall _ _) Hv _ Hin)).
    assert (Hv0 := Forall_inv Hv).
    assert (Hwv : curve_ring_arcs_valid (offset_walk_miter (s0 :: rest)))
      by (apply offset_walk_miter_arcs_valid; assumption).
    assert (Hwa : curve_ring_adjacent (offset_walk_miter (s0 :: rest)))
      by (apply offset_walk_miter_adjacent; assumption).
    destruct (offset_walk_miter_head s0 rest) as [t Ht].
    assert (Hwlast : last (offset_walk_miter (s0 :: rest))
                          (curve_segment_offset s0 d) =
                     curve_segment_offset (last (s0 :: rest) s0) d)
      by (apply offset_walk_miter_last; exact Hne).
    unfold curve_ring_offset_miter.
    destruct (g1dec (last (s0 :: rest) s0) s0) eqn:Ec.
    - (* G1 closing seam *)
      split; [ exact Hwv | split; [ exact Hwa | ] ].
      assert (Hseam : curve_segment_end
                        (last (offset_walk_miter (s0 :: rest))
                              (curve_segment_offset s0 d)) =
                      curve_segment_start (curve_segment_offset s0 d)).
      { rewrite Hwlast.
        apply (segment_join_offset_continuous _ _ d Hvlast Hv0 Hcl).
        apply (proj1 (g1dec_spec _ _)). exact Ec. }
      unfold curve_ring_closed.
      rewrite Ht in Hseam |- *.
      exact Hseam.
    - (* closing miter connector *)
      destruct (miter_connector_spec (last (s0 :: rest) s0) s0
                  (curve_segment_offset s0 d))
        as [HneC [HCadj [Hhd [Hlast HCv]]]].
      split; [ | split ].
      + apply (proj2 (Forall_app _ _ _)).
        split; [ exact Hwv | exact HCv ].
      + apply (curve_ring_adjacent_app _ _
                 (curve_segment_offset s0 d));
          [ rewrite Ht; discriminate | exact HneC
          | exact Hwa | exact HCadj | ].
        rewrite Hwlast. symmetry. exact Hhd.
      + unfold curve_ring_closed.
        rewrite Ht. cbn [app].
        change (curve_segment_offset s0 d
                  :: t ++ miter_connector (last (s0 :: rest) s0) s0)
          with ((curve_segment_offset s0 d :: t)
                  ++ miter_connector (last (s0 :: rest) s0) s0).
        rewrite (last_app_nonnil _ _ _ HneC).
        rewrite Hlast.
        reflexivity.
  Qed.

  (* §2d  All-chord preservation, stage-3 handoff, smooth coherence.          *)

  Lemma curve_ring_offset_miter_preserves_chords : forall r,
    Forall (fun s => match s with CSChord _ _ => True | CSArc _ => False end) r ->
    Forall (fun s => match s with CSChord _ _ => True | CSArc _ => False end)
           (curve_ring_offset_miter r).
  Proof.
    intros r Hc.
    assert (HC : forall s1 s2,
        Forall (fun s => match s with
                         | CSChord _ _ => True | CSArc _ => False end)
               (miter_connector s1 s2)).
    { intros [p q | a1] [p2 q2 | a2]; cbn [miter_connector];
        repeat constructor. }
    assert (Hwalk : forall r',
        Forall (fun s => match s with
                         | CSChord _ _ => True | CSArc _ => False end) r' ->
        Forall (fun s => match s with
                         | CSChord _ _ => True | CSArc _ => False end)
               (offset_walk_miter r')).
    { induction r' as [| s1 rest IH]; intros Hc'.
      - constructor.
      - destruct rest as [| s2 rest'].
        + constructor; [ | constructor ].
          destruct s1 as [p q | a]; [ exact I | exact (Forall_inv Hc') ].
        + rewrite offset_walk_miter_eq. destruct (g1dec s1 s2).
          * constructor.
            -- destruct s1 as [p q | a];
                 [ exact I | exact (Forall_inv Hc') ].
            -- apply IH. exact (Forall_inv_tail Hc').
          * constructor.
            -- destruct s1 as [p q | a];
                 [ exact I | exact (Forall_inv Hc') ].
            -- apply (proj2 (Forall_app _ _ _)).
               split; [ apply HC | ].
               apply IH. exact (Forall_inv_tail Hc'). }
    unfold curve_ring_offset_miter.
    destruct r as [| s0 rest]; [ constructor | ].
    destruct (g1dec (last (s0 :: rest) s0) s0).
    - apply Hwalk. exact Hc.
    - apply (proj2 (Forall_app _ _ _)).
      split; [ apply Hwalk; exact Hc | apply HC ].
  Qed.

  Theorem miter_emit_ring_closed : forall (r : CurveRing) (n : nat),
    valid_curve_ring r ->
    ring_offset_safe r d ->
    ring_closed (chord_approx_ring (curve_ring_offset_miter r) n).
  Proof.
    intros r n Hv Hs.
    apply chord_approx_ring_closed.
    destruct (curve_ring_offset_miter_valid r Hv Hs) as [_ [_ Hcl]].
    exact Hcl.
  Qed.

  Lemma offset_walk_miter_smooth_eq_map : forall r,
    ring_joins_normals_consistent r ->
    offset_walk_miter r = curve_ring_offset r d.
  Proof.
    induction r as [| s1 rest IH]; intros HG1.
    - reflexivity.
    - destruct rest as [| s2 rest'].
      + reflexivity.
      + destruct HG1 as [Hg HG1'].
        rewrite offset_walk_miter_eq.
        rewrite (proj2 (g1dec_spec s1 s2) Hg).
        change (curve_ring_offset (s1 :: s2 :: rest') d)
          with (curve_segment_offset s1 d
                  :: curve_ring_offset (s2 :: rest') d).
        f_equal.
        exact (IH HG1').
  Qed.

End MiterAssembly.

(* ========================================================================== *)
(* Axiom audit.  ALL headlines below are 3-axiom (classical-reals trio:      *)
(* sig_not_dec, sig_forall_dec, functional_extensionality_dep).              *)
(* ========================================================================== *)

Print Assumptions curve_ring_offset_miter_valid.
Print Assumptions miter_connector_apex_sound.
Print Assumptions curve_ring_offset_miter_preserves_chords.
Print Assumptions miter_emit_ring_closed.
Print Assumptions offset_walk_miter_smooth_eq_map.
