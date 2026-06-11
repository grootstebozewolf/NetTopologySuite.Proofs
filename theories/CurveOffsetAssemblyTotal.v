(* ============================================================================
   NetTopologySuite.Proofs.CurveOffsetAssemblyTotal
   ----------------------------------------------------------------------------
   Buffer/noder pipeline, Stage 2-CURVE seam, rung 8: TOTAL ASSEMBLY --
   the offset ring with NO join exclusions (issue #65 BUF-*; supersedes
   the no-U-turn restriction of `CurveOffsetAssembly.v` by threading
   `CurveSemicircle.v`'s semicircle through the walk).

   Rung 6's `curve_ring_offset_round_valid` carried two hypotheses
   about every join: not-G1-means-turn (via the round join's validity)
   and NO U-TURN (anti-parallel normals, where the round join's
   angular-midpoint normalisation divides by zero).  Rung 7 built the
   semicircle that fills exactly those U-turn gaps.  This file fuses
   them:

     - `join_connector s1 s2`: the three-way join policy -- nothing at
       a G1 join, the SEMICIRCLE (with a supplied sweep side `tsel`)
       at a U-turn join, the round join arc otherwise.  Both decisions
       (`g1dec`, `uturndec`) are abstract boolean oracles with
       correctness specs, like rung 6's `g1dec`: real-vector equality
       is not computable, extraction supplies the comparisons, and
       every theorem is conditional only on the specs.  The sweep-side
       supplier `tsel` carries the one genuinely geometric input a
       U-turn needs (both semicircles are admissible; the buffer picks
       the side away from the input); its spec demands only unit
       length and perpendicularity to the join normal, and
       `tsel_vperp_spec` shows the canonical `vperp` supplier
       satisfies it.

     - `curve_ring_offset_total_valid` (HEADLINE): for ANY valid
       compound ring with non-degenerate chords, offset within the
       per-arc safety bound and `d <> 0`, the assembled output --
       offset segments + three-way join connectors, including the
       closing join -- is again a `valid_curve_ring`.  No U-turn
       hypothesis, no turning hypothesis: every join configuration is
       handled.  This is the total structural story for emitting
       round-join buffer boundaries of compound curves as SQL/MM
       `CurvePolygon` rings.

     - `offset_walk_total_smooth_eq_map` (coherence): on an all-G1
       ring the walk still inserts nothing and equals rung 3's plain
       `curve_ring_offset`.

   FORWARD POINTER: with this file the JOIN story is complete -- no
   U-turn or turning exclusions remain (the once-conjectured
   "double-arc" U-turn treatment was refuted by rung 7: one semicircle
   suffices, and it is threaded through the walk here).  What remains
   on the #65 lane is qualitatively different work: `CurvePolygon`-level
   topology (hole/shell relations under offset) and the point-set
   Minkowski semantics bridge of `buffer-noder-pipeline.md` §3.

   Pure-R; THREE-AXIOM THROUGHOUT (classical-reals trio).  No
   `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Bool.
From NTS.Proofs Require Import Distance Vec Direction CurveGeometry ArcChordApprox.
From NTS.Proofs Require Import ArcOffsetThreePoint CurveRingOffset CurveRoundJoin.
From NTS.Proofs Require Import CurveOffsetAssembly CurveSemicircle BufferOffset.

Import ListNotations.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Anti-parallel normals, characterised.                                  *)
(* -------------------------------------------------------------------------- *)

Lemma vadd_eq_zero_iff_vneg : forall u v : Vec,
  vadd u v = vzero <-> v = vneg u.
Proof.
  intros u v. split; intros H.
  - assert (Hx : vx (vadd u v) = vx vzero) by (rewrite H; reflexivity).
    assert (Hy : vy (vadd u v) = vy vzero) by (rewrite H; reflexivity).
    unfold vadd, vzero in Hx, Hy. simpl in Hx, Hy.
    apply Vec_eq; unfold vneg; simpl; lra.
  - rewrite H. apply Vec_eq; unfold vadd, vneg, vzero; simpl; ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The total assembly walk.                                               *)
(* -------------------------------------------------------------------------- *)

Section TotalAssembly.

  Variable d : R.

  (* G1 decision (as in rung 6). *)
  Variable g1dec : CurveSegment -> CurveSegment -> bool.
  Hypothesis g1dec_spec : forall s1 s2,
    g1dec s1 s2 = true <-> segment_norm_end s1 = segment_norm_start s2.

  (* U-turn decision: are the join normals anti-parallel?                    *)
  Variable uturndec : CurveSegment -> CurveSegment -> bool.
  Hypothesis uturndec_spec : forall s1 s2,
    uturndec s1 s2 = true <->
    segment_norm_start s2 = vneg (segment_norm_end s1).

  (* Sweep-side supplier for U-turn semicircles: a unit vector               *)
  (* perpendicular to the incoming join normal.                              *)
  Variable tsel : CurveSegment -> CurveSegment -> Vec.
  Hypothesis tsel_spec : forall s1 s2,
    segment_arc_valid s1 -> segment_nondeg s1 ->
    vdot (tsel s1 s2) (tsel s1 s2) = 1 /\
    vdot (segment_norm_end s1) (tsel s1 s2) = 0.

  Lemma g1dec_false_ne' : forall s1 s2,
    g1dec s1 s2 = false ->
    segment_norm_end s1 <> segment_norm_start s2.
  Proof.
    intros s1 s2 Hf He.
    rewrite (proj2 (g1dec_spec s1 s2) He) in Hf. discriminate.
  Qed.

  Lemma uturndec_false_not_anti : forall s1 s2,
    uturndec s1 s2 = false ->
    vadd (segment_norm_end s1) (segment_norm_start s2) <> vzero.
  Proof.
    intros s1 s2 Hf Hz.
    rewrite (proj2 (uturndec_spec s1 s2)
               (proj1 (vadd_eq_zero_iff_vneg _ _) Hz)) in Hf.
    discriminate.
  Qed.

  (* The three-way join policy (G1 handled by the walk itself).              *)
  Definition join_connector (s1 s2 : CurveSegment) : CurveSegment :=
    if uturndec s1 s2
    then CSArc (semicircle_arc (curve_segment_end s1) d
                  (segment_norm_end s1) (tsel s1 s2))
    else CSArc (round_join_arc (curve_segment_end s1) d
                  (segment_norm_end s1) (segment_norm_start s2)).

  Fixpoint offset_walk_total (r : CurveRing) : CurveRing :=
    match r with
    | [] => []
    | s1 :: rest =>
        match rest with
        | [] => [curve_segment_offset s1 d]
        | s2 :: _ =>
            if g1dec s1 s2
            then curve_segment_offset s1 d :: offset_walk_total rest
            else curve_segment_offset s1 d :: join_connector s1 s2
                   :: offset_walk_total rest
        end
    end.

  Lemma offset_walk_total_eq : forall s1 s2 rest',
    offset_walk_total (s1 :: s2 :: rest') =
    if g1dec s1 s2
    then curve_segment_offset s1 d :: offset_walk_total (s2 :: rest')
    else curve_segment_offset s1 d :: join_connector s1 s2
           :: offset_walk_total (s2 :: rest').
  Proof. reflexivity. Qed.

  Definition curve_ring_offset_total (r : CurveRing) : CurveRing :=
    match r with
    | [] => []
    | s0 :: _ =>
        if g1dec (last r s0) s0
        then offset_walk_total r
        else offset_walk_total r ++ [join_connector (last r s0) s0]
    end.

  Lemma offset_walk_total_head : forall s rest,
    exists t, offset_walk_total (s :: rest) = curve_segment_offset s d :: t.
  Proof.
    intros s [| s2 rest'].
    - exists []. reflexivity.
    - rewrite offset_walk_total_eq.
      destruct (g1dec s s2); eexists; reflexivity.
  Qed.

  Lemma offset_walk_total_last : forall r s0,
    r <> [] ->
    last (offset_walk_total r) (curve_segment_offset s0 d) =
    curve_segment_offset (last r s0) d.
  Proof.
    induction r as [| s1 rest IH]; intros s0 Hne.
    - contradiction.
    - destruct rest as [| s2 rest'].
      + reflexivity.
      + destruct (offset_walk_total_head s2 rest') as [t Ht].
        rewrite offset_walk_total_eq.
        rewrite (last_cons_cons s1 s2 rest').
        destruct (g1dec s1 s2); rewrite Ht.
        * rewrite last_cons_cons. rewrite <- Ht.
          apply IH. discriminate.
        * rewrite !last_cons_cons. rewrite <- Ht.
          apply IH. discriminate.
  Qed.

  (* §2a  Validity of the three-way connector -- no U-turn hypothesis.       *)

  Lemma join_connector_arc_valid : forall s1 s2,
    segment_arc_valid s1 -> segment_nondeg s1 ->
    segment_arc_valid s2 -> segment_nondeg s2 ->
    g1dec s1 s2 = false ->
    d <> 0 ->
    segment_arc_valid (join_connector s1 s2).
  Proof.
    intros s1 s2 Hv1 Hn1 Hv2 Hn2 Hg1 Hd.
    unfold join_connector.
    destruct (uturndec s1 s2) eqn:Eu; cbn [segment_arc_valid].
    - (* U-turn: the semicircle, with the supplied sweep side *)
      destruct (tsel_spec s1 s2 Hv1 Hn1) as [Htu Htp].
      apply semicircle_arc_valid.
      + apply segment_norm_end_unit; assumption.
      + exact Htu.
      + exact Htp.
      + exact Hd.
    - (* genuine turn: the round join *)
      apply round_join_arc_valid.
      + apply segment_norm_end_unit; assumption.
      + apply segment_norm_start_unit; assumption.
      + apply g1dec_false_ne'. exact Hg1.
      + apply uturndec_false_not_anti. exact Eu.
      + exact Hd.
  Qed.

  (* §2b  Splice facts of the three-way connector.                           *)

  Lemma join_connector_splice : forall s1 s2,
    segment_arc_valid s1 -> segment_arc_valid s2 ->
    curve_segment_end s1 = curve_segment_start s2 ->
    curve_segment_end (curve_segment_offset s1 d) =
      curve_segment_start (join_connector s1 s2) /\
    curve_segment_end (join_connector s1 s2) =
      curve_segment_start (curve_segment_offset s2 d).
  Proof.
    intros s1 s2 Hv1 Hv2 HP.
    unfold join_connector.
    destruct (uturndec s1 s2) eqn:Eu.
    - (* U-turn semicircle *)
      destruct (semicircle_uturn_connects s1 s2 d (tsel s1 s2) Hv1 Hv2 HP
                  (proj1 (uturndec_spec s1 s2) Eu)) as [Hs He].
      split; [ symmetry; exact Hs | exact He ].
    - (* round join *)
      destruct (round_join_connects s1 s2 d Hv1 Hv2 HP) as [Hs He].
      split; [ symmetry; exact Hs | exact He ].
  Qed.

  (* §2c  The walk preserves arc validity and adjacency.                     *)

  Lemma offset_walk_total_arcs_valid : forall r,
    curve_ring_arcs_valid r ->
    Forall segment_nondeg r ->
    ring_offset_safe r d ->
    d <> 0 ->
    curve_ring_arcs_valid (offset_walk_total r).
  Proof.
    induction r as [| s1 rest IH]; intros Hv Hn Hsafe Hd.
    - constructor.
    - destruct rest as [| s2 rest'].
      + constructor; [ | constructor ].
        apply curve_segment_offset_arc_valid;
          [ exact (Forall_inv Hv) | exact (Forall_inv Hsafe) ].
      + assert (Hoff : segment_arc_valid (curve_segment_offset s1 d))
          by (apply curve_segment_offset_arc_valid;
              [ exact (Forall_inv Hv) | exact (Forall_inv Hsafe) ]).
        assert (Hrest : curve_ring_arcs_valid (offset_walk_total (s2 :: rest')))
          by (apply IH;
              [ exact (Forall_inv_tail Hv) | exact (Forall_inv_tail Hn)
              | exact (Forall_inv_tail Hsafe) | exact Hd ]).
        rewrite offset_walk_total_eq. destruct (g1dec s1 s2) eqn:E.
        * constructor; assumption.
        * constructor; [ exact Hoff | constructor; [ | exact Hrest ] ].
          apply join_connector_arc_valid;
            [ exact (Forall_inv Hv) | exact (Forall_inv Hn)
            | exact (Forall_inv (Forall_inv_tail Hv))
            | exact (Forall_inv (Forall_inv_tail Hn))
            | exact E | exact Hd ].
  Qed.

  Lemma offset_walk_total_adjacent : forall r,
    curve_ring_arcs_valid r ->
    curve_ring_adjacent r ->
    curve_ring_adjacent (offset_walk_total r).
  Proof.
    induction r as [| s1 rest IH]; intros Hv Hadj.
    - exact I.
    - destruct rest as [| s2 rest'].
      + exact I.
      + destruct Hadj as [Hj Hadj'].
        assert (Hv1 := Forall_inv Hv).
        assert (Hv2 := Forall_inv (Forall_inv_tail Hv)).
        assert (Hrest : curve_ring_adjacent (offset_walk_total (s2 :: rest')))
          by (apply IH; [ exact (Forall_inv_tail Hv) | exact Hadj' ]).
        destruct (offset_walk_total_head s2 rest') as [t Ht].
        rewrite offset_walk_total_eq. destruct (g1dec s1 s2) eqn:E.
        * rewrite Ht. split.
          -- apply (segment_join_offset_continuous s1 s2 d Hv1 Hv2 Hj).
             apply (proj1 (g1dec_spec s1 s2)). exact E.
          -- rewrite <- Ht. exact Hrest.
        * destruct (join_connector_splice s1 s2 Hv1 Hv2 Hj) as [Hsa Hse].
          rewrite Ht. split; [ exact Hsa | split ].
          -- exact Hse.
          -- rewrite <- Ht. exact Hrest.
  Qed.

  (* §2d  HEADLINE: the total assembly is a valid ring -- no join            *)
  (*       exclusions.                                                       *)

  Theorem curve_ring_offset_total_valid : forall r,
    valid_curve_ring r ->
    Forall segment_nondeg r ->
    ring_offset_safe r d ->
    d <> 0 ->
    valid_curve_ring (curve_ring_offset_total r).
  Proof.
    intros r [Hv [Hadj Hcl]] Hn Hsafe Hd.
    destruct r as [| s0 rest]; [ contradiction | ].
    assert (Hne : s0 :: rest <> @nil CurveSegment) by discriminate.
    assert (Hin : In (last (s0 :: rest) s0) (s0 :: rest))
      by (apply last_in; exact Hne).
    assert (Hvlast : segment_arc_valid (last (s0 :: rest) s0))
      by (exact (proj1 (Forall_forall _ _) Hv _ Hin)).
    assert (Hnlast : segment_nondeg (last (s0 :: rest) s0))
      by (exact (proj1 (Forall_forall _ _) Hn _ Hin)).
    assert (Hv0 := Forall_inv Hv).
    assert (Hn0 := Forall_inv Hn).
    assert (Hwv : curve_ring_arcs_valid (offset_walk_total (s0 :: rest)))
      by (apply offset_walk_total_arcs_valid; assumption).
    assert (Hwa : curve_ring_adjacent (offset_walk_total (s0 :: rest)))
      by (apply offset_walk_total_adjacent; assumption).
    destruct (offset_walk_total_head s0 rest) as [t Ht].
    assert (Hwlast : last (offset_walk_total (s0 :: rest))
                          (curve_segment_offset s0 d) =
                     curve_segment_offset (last (s0 :: rest) s0) d)
      by (apply offset_walk_total_last; exact Hne).
    unfold curve_ring_offset_total.
    destruct (g1dec (last (s0 :: rest) s0) s0) eqn:Ec.
    - (* G1 closing seam *)
      split; [ exact Hwv | split; [ exact Hwa | ] ].
      assert (Hseam : curve_segment_end
                        (last (offset_walk_total (s0 :: rest))
                              (curve_segment_offset s0 d)) =
                      curve_segment_start (curve_segment_offset s0 d)).
      { rewrite Hwlast.
        apply (segment_join_offset_continuous _ _ d Hvlast Hv0 Hcl).
        apply (proj1 (g1dec_spec _ _)). exact Ec. }
      unfold curve_ring_closed.
      rewrite Ht in Hseam |- *.
      exact Hseam.
    - (* closing connector (semicircle or round join) *)
      destruct (join_connector_splice (last (s0 :: rest) s0) s0
                  Hvlast Hv0 Hcl) as [Hsa Hse].
      split; [ | split ].
      + apply (proj2 (Forall_app _ _ _)). split; [ exact Hwv | ].
        constructor; [ | constructor ].
        apply join_connector_arc_valid; assumption.
      + apply (curve_ring_adjacent_snoc _ _ (curve_segment_offset s0 d)).
        * rewrite Ht. discriminate.
        * exact Hwa.
        * rewrite Hwlast. exact Hsa.
      + unfold curve_ring_closed.
        rewrite Ht. cbn [app].
        assert (Hl : last (curve_segment_offset s0 d
                             :: t ++ [join_connector (last (s0 :: rest) s0) s0])
                          (curve_segment_offset s0 d)
                     = join_connector (last (s0 :: rest) s0) s0).
        { change (curve_segment_offset s0 d
                    :: t ++ [join_connector (last (s0 :: rest) s0) s0])
            with ((curve_segment_offset s0 d :: t)
                    ++ [join_connector (last (s0 :: rest) s0) s0]).
          apply last_snoc. }
        rewrite Hl.
        exact Hse.
  Qed.

  (* §2e  Coherence with the smooth case.                                    *)

  Lemma offset_walk_total_smooth_eq_map : forall r,
    ring_joins_normals_consistent r ->
    offset_walk_total r = curve_ring_offset r d.
  Proof.
    induction r as [| s1 rest IH]; intros HG1.
    - reflexivity.
    - destruct rest as [| s2 rest'].
      + reflexivity.
      + destruct HG1 as [Hg HG1'].
        rewrite offset_walk_total_eq.
        rewrite (proj2 (g1dec_spec s1 s2) Hg).
        change (curve_ring_offset (s1 :: s2 :: rest') d)
          with (curve_segment_offset s1 d
                  :: curve_ring_offset (s2 :: rest') d).
        f_equal.
        exact (IH HG1').
  Qed.

End TotalAssembly.

(* -------------------------------------------------------------------------- *)
(* §3  The canonical sweep-side supplier satisfies tsel's spec.               *)
(* -------------------------------------------------------------------------- *)

Lemma tsel_vperp_spec : forall s1 s2 : CurveSegment,
  segment_arc_valid s1 -> segment_nondeg s1 ->
  vdot (cap_tangent (segment_norm_end s1))
       (cap_tangent (segment_norm_end s1)) = 1 /\
  vdot (segment_norm_end s1) (cap_tangent (segment_norm_end s1)) = 0.
Proof.
  intros s1 s2 Hv Hn.
  split.
  - apply cap_tangent_unit. apply segment_norm_end_unit; assumption.
  - apply cap_tangent_perp.
Qed.

(* ========================================================================== *)
(* Axiom audit.  ALL headlines below are 3-axiom (classical-reals trio:      *)
(* sig_not_dec, sig_forall_dec, functional_extensionality_dep).              *)
(* ========================================================================== *)

Print Assumptions curve_ring_offset_total_valid.
Print Assumptions join_connector_arc_valid.
Print Assumptions join_connector_splice.
Print Assumptions offset_walk_total_smooth_eq_map.
Print Assumptions tsel_vperp_spec.
Print Assumptions vadd_eq_zero_iff_vneg.
