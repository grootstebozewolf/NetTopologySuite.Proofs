(* ============================================================================
   NetTopologySuite.Proofs.CurveBevelJoin
   ----------------------------------------------------------------------------
   Buffer/noder pipeline, Stage 2b-CURVE seam, rung 12 (issue #65):
   the BEVEL assembly -- the join-edge flavour rung 11 left open,
   emitted as CHORDS.

   The bevel join at a non-G1 join point is simply the chord from the
   incoming segment's offset endpoint to the outgoing segment's offset
   start -- no arc geometry, no normals, no sweep side.  That makes it
   the LEANEST total assembly:

     - it handles EVERY non-G1 join uniformly, U-turns included (the
       bevel of an anti-parallel join is the flat chord across the
       tear -- JTS's flat-cap/bevel behaviour);
     - its splice facts are REFLEXIVITY (the connector's endpoints are
       defined as the offset endpoints);
     - its connectors contribute nothing to arc validity (chords), so
       the headline needs neither chord non-degeneracy, nor `d <> 0`,
       nor the U-turn oracle, nor a sweep supplier -- only ring
       validity, the per-arc safety bound, and the G1 decision spec.

     - `curve_ring_offset_bevel_valid` (HEADLINE): any valid compound
       ring offset within the per-arc safety bound assembles -- offset
       segments + bevel chords at every non-G1 join, closing join
       included -- into a `valid_curve_ring`.
     - `bevel_join_nondeg` (quality fact, with the usual extra
       hypotheses): at a genuinely non-G1 join with `d <> 0` the bevel
       chord is non-degenerate -- its endpoints are `P + d*n1` vs
       `P + d*n2` with `n1 <> n2`.
     - `curve_ring_offset_bevel_preserves_chords`: on all-chord input
       the ENTIRE output is chords -- the pure LINEAR bevel-join
       offset emitter, no linearisation step needed at all.
     - `bevel_emit_ring_closed`: the chord-linearised output is a
       `ring_closed` Phase-3 ring (the stage-3 handoff, as in the
       round-join emitter).
     - `offset_walk_bevel_smooth_eq_map`: on all-G1 rings the walk
       inserts nothing (coherence, as before).

   MITER emission (two chords through `BufferMiter.miter_apex`)
   remains the one open join flavour; its corner geometry is proven in
   `BufferMiter.v`/`BufferMiterAngle.v`, and wiring the apex into this
   walk is the natural next slice of the 2b row.

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
From NTS.Proofs Require Import CurveOffsetAssembly CurveLinearise BufferOffset.

Import ListNotations.

Local Open Scope R_scope.

Section BevelAssembly.

  Variable d : R.

  Variable g1dec : CurveSegment -> CurveSegment -> bool.
  Hypothesis g1dec_spec : forall s1 s2,
    g1dec s1 s2 = true <-> segment_norm_end s1 = segment_norm_start s2.

  (* The bevel connector: the chord across the tear.                         *)
  Definition bevel_join (s1 s2 : CurveSegment) : CurveSegment :=
    CSChord (curve_segment_end (curve_segment_offset s1 d))
            (curve_segment_start (curve_segment_offset s2 d)).

  (* Its splice facts are definitional.                                       *)
  Lemma bevel_join_splice : forall s1 s2,
    curve_segment_end (curve_segment_offset s1 d) =
      curve_segment_start (bevel_join s1 s2) /\
    curve_segment_end (bevel_join s1 s2) =
      curve_segment_start (curve_segment_offset s2 d).
  Proof. intros s1 s2. split; reflexivity. Qed.

  (* Quality fact: at a genuinely non-G1 join with d <> 0 the bevel chord    *)
  (* is non-degenerate (endpoints P + d*n1 vs P + d*n2 with n1 <> n2).       *)
  Lemma bevel_join_nondeg : forall s1 s2,
    segment_arc_valid s1 -> segment_nondeg s1 ->
    segment_arc_valid s2 -> segment_nondeg s2 ->
    curve_segment_end s1 = curve_segment_start s2 ->
    g1dec s1 s2 = false ->
    d <> 0 ->
    segment_nondeg (bevel_join s1 s2).
  Proof.
    intros s1 s2 Hv1 Hn1 Hv2 Hn2 HP Hg1 Hd.
    cbn [bevel_join segment_nondeg].
    intros Heq.
    rewrite (curve_segment_offset_end s1 d Hv1) in Heq.
    rewrite (curve_segment_offset_start s2 d Hv2) in Heq.
    rewrite <- HP in Heq.
    set (P := curve_segment_end s1) in *.
    set (n1 := segment_norm_end s1) in *.
    set (n2 := segment_norm_start s2) in *.
    assert (Hx : px (pt_translate P (d * vx n1) (d * vy n1)) =
                 px (pt_translate P (d * vx n2) (d * vy n2)))
      by (rewrite Heq; reflexivity).
    assert (Hy : py (pt_translate P (d * vx n1) (d * vy n1)) =
                 py (pt_translate P (d * vx n2) (d * vy n2)))
      by (rewrite Heq; reflexivity).
    unfold pt_translate in Hx, Hy. cbn [px py] in Hx, Hy.
    assert (Hvx : d * (vx n1 - vx n2) = 0) by lra.
    assert (Hvy : d * (vy n1 - vy n2) = 0) by lra.
    assert (Hn : n1 = n2).
    { apply Vec_eq.
      - destruct (Rmult_integral _ _ Hvx); lra.
      - destruct (Rmult_integral _ _ Hvy); lra. }
    rewrite (proj2 (g1dec_spec s1 s2) Hn) in Hg1. discriminate.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The bevel walk (skeleton of the rung-6/8 walks, leaner connector).  *)
  (* ------------------------------------------------------------------ *)

  Fixpoint offset_walk_bevel (r : CurveRing) : CurveRing :=
    match r with
    | [] => []
    | s1 :: rest =>
        match rest with
        | [] => [curve_segment_offset s1 d]
        | s2 :: _ =>
            if g1dec s1 s2
            then curve_segment_offset s1 d :: offset_walk_bevel rest
            else curve_segment_offset s1 d :: bevel_join s1 s2
                   :: offset_walk_bevel rest
        end
    end.

  Lemma offset_walk_bevel_eq : forall s1 s2 rest',
    offset_walk_bevel (s1 :: s2 :: rest') =
    if g1dec s1 s2
    then curve_segment_offset s1 d :: offset_walk_bevel (s2 :: rest')
    else curve_segment_offset s1 d :: bevel_join s1 s2
           :: offset_walk_bevel (s2 :: rest').
  Proof. reflexivity. Qed.

  Definition curve_ring_offset_bevel (r : CurveRing) : CurveRing :=
    match r with
    | [] => []
    | s0 :: _ =>
        if g1dec (last r s0) s0
        then offset_walk_bevel r
        else offset_walk_bevel r ++ [bevel_join (last r s0) s0]
    end.

  Lemma offset_walk_bevel_head : forall s rest,
    exists t, offset_walk_bevel (s :: rest) = curve_segment_offset s d :: t.
  Proof.
    intros s [| s2 rest'].
    - exists []. reflexivity.
    - rewrite offset_walk_bevel_eq.
      destruct (g1dec s s2); eexists; reflexivity.
  Qed.

  Lemma offset_walk_bevel_last : forall r s0,
    r <> [] ->
    last (offset_walk_bevel r) (curve_segment_offset s0 d) =
    curve_segment_offset (last r s0) d.
  Proof.
    induction r as [| s1 rest IH]; intros s0 Hne.
    - contradiction.
    - destruct rest as [| s2 rest'].
      + reflexivity.
      + destruct (offset_walk_bevel_head s2 rest') as [t Ht].
        rewrite offset_walk_bevel_eq.
        rewrite (last_cons_cons s1 s2 rest').
        destruct (g1dec s1 s2); rewrite Ht.
        * rewrite last_cons_cons. rewrite <- Ht.
          apply IH. discriminate.
        * rewrite !last_cons_cons. rewrite <- Ht.
          apply IH. discriminate.
  Qed.

  Lemma offset_walk_bevel_arcs_valid : forall r,
    curve_ring_arcs_valid r ->
    ring_offset_safe r d ->
    curve_ring_arcs_valid (offset_walk_bevel r).
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
        assert (Hrest : curve_ring_arcs_valid (offset_walk_bevel (s2 :: rest')))
          by (apply IH;
              [ exact (Forall_inv_tail Hv) | exact (Forall_inv_tail Hsafe) ]).
        rewrite offset_walk_bevel_eq. destruct (g1dec s1 s2) eqn:E.
        * constructor; assumption.
        * constructor; [ exact Hoff | constructor; [ exact I | exact Hrest ] ].
  Qed.

  Lemma offset_walk_bevel_adjacent : forall r,
    curve_ring_arcs_valid r ->
    curve_ring_adjacent r ->
    curve_ring_adjacent (offset_walk_bevel r).
  Proof.
    induction r as [| s1 rest IH]; intros Hv Hadj.
    - exact I.
    - destruct rest as [| s2 rest'].
      + exact I.
      + destruct Hadj as [Hj Hadj'].
        assert (Hv1 := Forall_inv Hv).
        assert (Hv2 := Forall_inv (Forall_inv_tail Hv)).
        assert (Hrest : curve_ring_adjacent (offset_walk_bevel (s2 :: rest')))
          by (apply IH; [ exact (Forall_inv_tail Hv) | exact Hadj' ]).
        destruct (offset_walk_bevel_head s2 rest') as [t Ht].
        rewrite offset_walk_bevel_eq. destruct (g1dec s1 s2) eqn:E.
        * rewrite Ht. split.
          -- apply (segment_join_offset_continuous s1 s2 d Hv1 Hv2 Hj).
             apply (proj1 (g1dec_spec s1 s2)). exact E.
          -- rewrite <- Ht. exact Hrest.
        * destruct (bevel_join_splice s1 s2) as [Hsa Hse].
          rewrite Ht. split; [ exact Hsa | split ].
          -- exact Hse.
          -- rewrite <- Ht. exact Hrest.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* HEADLINE: bevel assembly preserves ring validity, with the LEANEST  *)
  (* hypothesis set of the three assemblies (no nondegeneracy, no        *)
  (* d <> 0, no U-turn oracle, no sweep supplier).                       *)
  (* ------------------------------------------------------------------ *)

  Theorem curve_ring_offset_bevel_valid : forall r,
    valid_curve_ring r ->
    ring_offset_safe r d ->
    valid_curve_ring (curve_ring_offset_bevel r).
  Proof.
    intros r [Hv [Hadj Hcl]] Hsafe.
    destruct r as [| s0 rest]; [ contradiction | ].
    assert (Hne : s0 :: rest <> @nil CurveSegment) by discriminate.
    assert (Hin : In (last (s0 :: rest) s0) (s0 :: rest))
      by (apply last_in; exact Hne).
    assert (Hvlast : segment_arc_valid (last (s0 :: rest) s0))
      by (exact (proj1 (Forall_forall _ _) Hv _ Hin)).
    assert (Hv0 := Forall_inv Hv).
    assert (Hwv : curve_ring_arcs_valid (offset_walk_bevel (s0 :: rest)))
      by (apply offset_walk_bevel_arcs_valid; assumption).
    assert (Hwa : curve_ring_adjacent (offset_walk_bevel (s0 :: rest)))
      by (apply offset_walk_bevel_adjacent; assumption).
    destruct (offset_walk_bevel_head s0 rest) as [t Ht].
    assert (Hwlast : last (offset_walk_bevel (s0 :: rest))
                          (curve_segment_offset s0 d) =
                     curve_segment_offset (last (s0 :: rest) s0) d)
      by (apply offset_walk_bevel_last; exact Hne).
    unfold curve_ring_offset_bevel.
    destruct (g1dec (last (s0 :: rest) s0) s0) eqn:Ec.
    - (* G1 closing seam *)
      split; [ exact Hwv | split; [ exact Hwa | ] ].
      assert (Hseam : curve_segment_end
                        (last (offset_walk_bevel (s0 :: rest))
                              (curve_segment_offset s0 d)) =
                      curve_segment_start (curve_segment_offset s0 d)).
      { rewrite Hwlast.
        apply (segment_join_offset_continuous _ _ d Hvlast Hv0 Hcl).
        apply (proj1 (g1dec_spec _ _)). exact Ec. }
      unfold curve_ring_closed.
      rewrite Ht in Hseam |- *.
      exact Hseam.
    - (* closing bevel chord *)
      destruct (bevel_join_splice (last (s0 :: rest) s0) s0) as [Hsa Hse].
      split; [ | split ].
      + apply (proj2 (Forall_app _ _ _)). split; [ exact Hwv | ].
        constructor; [ exact I | constructor ].
      + apply (curve_ring_adjacent_snoc _ _ (curve_segment_offset s0 d)).
        * rewrite Ht. discriminate.
        * exact Hwa.
        * rewrite Hwlast. exact Hsa.
      + unfold curve_ring_closed.
        rewrite Ht. cbn [app].
        assert (Hl : last (curve_segment_offset s0 d
                             :: t ++ [bevel_join (last (s0 :: rest) s0) s0])
                          (curve_segment_offset s0 d)
                     = bevel_join (last (s0 :: rest) s0) s0).
        { change (curve_segment_offset s0 d
                    :: t ++ [bevel_join (last (s0 :: rest) s0) s0])
            with ((curve_segment_offset s0 d :: t)
                    ++ [bevel_join (last (s0 :: rest) s0) s0]).
          apply last_snoc. }
        rewrite Hl.
        rewrite Hse.
        (* start (offset s2) with s2 := s0; need start of offset s0:
           the closing seam target is start (offset s0) -- definitional *)
        reflexivity.
  Qed.

  (* All-chord input gives ALL-CHORD output: the pure linear bevel emitter.  *)
  Lemma curve_ring_offset_bevel_preserves_chords : forall r,
    Forall (fun s => match s with CSChord _ _ => True | CSArc _ => False end) r ->
    Forall (fun s => match s with CSChord _ _ => True | CSArc _ => False end)
           (curve_ring_offset_bevel r).
  Proof.
    intros r Hc.
    assert (Hwalk : forall r',
        Forall (fun s => match s with
                         | CSChord _ _ => True | CSArc _ => False end) r' ->
        Forall (fun s => match s with
                         | CSChord _ _ => True | CSArc _ => False end)
               (offset_walk_bevel r')).
    { induction r' as [| s1 rest IH]; intros Hc'.
      - constructor.
      - destruct rest as [| s2 rest'].
        + constructor; [ | constructor ].
          destruct s1 as [p q | a]; [ exact I | exact (Forall_inv Hc') ].
        + rewrite offset_walk_bevel_eq. destruct (g1dec s1 s2).
          * constructor.
            -- destruct s1 as [p q | a];
                 [ exact I | exact (Forall_inv Hc') ].
            -- apply IH. exact (Forall_inv_tail Hc').
          * constructor.
            -- destruct s1 as [p q | a];
                 [ exact I | exact (Forall_inv Hc') ].
            -- constructor; [ exact I | ].
               apply IH. exact (Forall_inv_tail Hc'). }
    unfold curve_ring_offset_bevel.
    destruct r as [| s0 rest]; [ constructor | ].
    destruct (g1dec (last (s0 :: rest) s0) s0).
    - apply Hwalk. exact Hc.
    - apply (proj2 (Forall_app _ _ _)). split.
      + apply Hwalk. exact Hc.
      + constructor; [ exact I | constructor ].
  Qed.

  (* Stage-3 handoff: the bevel-assembled ring linearises closed.            *)
  Theorem bevel_emit_ring_closed : forall (r : CurveRing) (n : nat),
    valid_curve_ring r ->
    ring_offset_safe r d ->
    ring_closed (chord_approx_ring (curve_ring_offset_bevel r) n).
  Proof.
    intros r n Hv Hs.
    apply chord_approx_ring_closed.
    destruct (curve_ring_offset_bevel_valid r Hv Hs) as [_ [_ Hcl]].
    exact Hcl.
  Qed.

  (* Coherence: on an all-G1 ring the walk inserts nothing.                  *)
  Lemma offset_walk_bevel_smooth_eq_map : forall r,
    ring_joins_normals_consistent r ->
    offset_walk_bevel r = curve_ring_offset r d.
  Proof.
    induction r as [| s1 rest IH]; intros HG1.
    - reflexivity.
    - destruct rest as [| s2 rest'].
      + reflexivity.
      + destruct HG1 as [Hg HG1'].
        rewrite offset_walk_bevel_eq.
        rewrite (proj2 (g1dec_spec s1 s2) Hg).
        change (curve_ring_offset (s1 :: s2 :: rest') d)
          with (curve_segment_offset s1 d
                  :: curve_ring_offset (s2 :: rest') d).
        f_equal.
        exact (IH HG1').
  Qed.

End BevelAssembly.

(* ========================================================================== *)
(* Axiom audit.  ALL headlines below are 3-axiom (classical-reals trio:      *)
(* sig_not_dec, sig_forall_dec, functional_extensionality_dep).              *)
(* ========================================================================== *)

Print Assumptions curve_ring_offset_bevel_valid.
Print Assumptions bevel_join_nondeg.
Print Assumptions curve_ring_offset_bevel_preserves_chords.
Print Assumptions bevel_emit_ring_closed.
Print Assumptions offset_walk_bevel_smooth_eq_map.
