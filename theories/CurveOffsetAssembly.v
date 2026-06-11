(* ============================================================================
   NetTopologySuite.Proofs.CurveOffsetAssembly
   ----------------------------------------------------------------------------
   Buffer/noder pipeline, Stage 2-CURVE seam, rung 6: ASSEMBLY -- splice
   round-join arcs into the segment-wise offset ring (issue #65 BUF-*;
   capstone of the offset lane opened by `ArcOffset.v` and continued
   through `ArcOffsetThreePoint.v`, `CurveRingOffset.v`,
   `CurveRoundJoin.v`).

   `CurveRingOffset.curve_ring_offset_valid` covered SMOOTH rings (every
   join G1 with consistent normals); its tear witness proved non-G1
   joins disconnect, and `CurveRoundJoin.round_join_arc` provides the
   gap-filling arc.  This file performs the splice and proves the
   assembled ring well-formed:

     - `offset_walk` / `curve_ring_offset_round`: walk the ring,
       emitting each segment's offset and -- exactly at the joins a
       supplied G1 DECISION `g1dec` flags as non-smooth -- the round
       join arc between them, including the closing join back to the
       ring's first segment.  `g1dec` is an abstract boolean oracle
       with a correctness spec (`g1dec s1 s2 = true <-> the normal
       fields agree`); real-coordinate equality is not computable, so
       the decision is a parameter the extracted implementation
       supplies (floating/rational comparison), and every theorem here
       is conditional only on its SPEC.

     - `curve_ring_offset_round_valid` (HEADLINE): for a valid compound
       ring with non-degenerate chords, offset within the per-arc
       safety bound (`-r < d`), with `d <> 0` and NO U-TURN joins
       (anti-parallel normals -- the S-curve boundary needs two arcs,
       out of scope), the assembled output is again a
       `valid_curve_ring`: every arc valid (offset arcs by rung 3's
       safety argument, join arcs by `round_join_arc_valid`), adjacent
       (offset-to-join splices by `round_join_connects`, G1 joins by
       `segment_join_offset_continuous`), and closed (the closing join
       or G1 closing seam).  This extends rung 4's capstone from
       smooth rings to ARBITRARY (non-U-turn) compound rings -- the
       full structural story for emitting round-join buffer boundaries
       as SQL/MM `CurvePolygon` rings.

     - `offset_walk_smooth_eq_map` (coherence): on an all-G1 ring the
       walk inserts nothing and equals rung 3's plain
       `curve_ring_offset` -- the assembly conservatively extends the
       smooth case.

   FORWARD POINTER: the no-U-turn hypothesis below is closed at the
   single-join level by `CurveSemicircle.semicircle_uturn_connects`
   (rung 7); threading that semicircle through this walk -- replacing
   `ring_no_uturn_joins` with a supplied per-join sweep side -- is the
   remaining assembly work, tracked in `audit-rgr-comparison.md` §7.

   Pure-R; THREE-AXIOM THROUGHOUT (classical-reals trio).  No
   `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Bool.
From NTS.Proofs Require Import Distance Vec CurveGeometry ArcChordApprox.
From NTS.Proofs Require Import ArcOffsetThreePoint CurveRingOffset CurveRoundJoin.
From NTS.Proofs Require Import BufferOffset.

Import ListNotations.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Per-segment predicates and small list helpers.                         *)
(* -------------------------------------------------------------------------- *)

(* Chords must be non-degenerate for their offset normal to be a unit        *)
(* vector; arcs need nothing extra here (validity covers them).              *)
Definition segment_nondeg (s : CurveSegment) : Prop :=
  match s with
  | CSChord p q => p <> q
  | CSArc _ => True
  end.

(* The per-arc offset safety bound (the Forall body of                       *)
(* CurveRingOffset.ring_offset_safe).                                        *)
Definition segment_offset_safe (s : CurveSegment) (d : R) : Prop :=
  match s with
  | CSChord _ _ => True
  | CSArc a => - arc_radius a < d
  end.

(* Unit-ness of the normal fields, uniformly over the segment kind.          *)
Lemma segment_norm_end_unit : forall s,
  segment_arc_valid s -> segment_nondeg s ->
  vdot (segment_norm_end s) (segment_norm_end s) = 1.
Proof.
  intros [p q | a] Hv Hn.
  - apply segment_norm_chord_unit. exact Hn.
  - apply segment_norm_end_unit_arc. exact Hv.
Qed.

Lemma segment_norm_start_unit : forall s,
  segment_arc_valid s -> segment_nondeg s ->
  vdot (segment_norm_start s) (segment_norm_start s) = 1.
Proof.
  intros [p q | a] Hv Hn.
  - exact (segment_norm_chord_unit p q Hn).
  - apply segment_norm_start_unit_arc. exact Hv.
Qed.

(* Offsetting one segment preserves per-segment arc validity (the           *)
(* per-element core of rung 3's curve_ring_offset_arcs_valid).               *)
Lemma curve_segment_offset_arc_valid : forall s d,
  segment_arc_valid s -> segment_offset_safe s d ->
  segment_arc_valid (curve_segment_offset s d).
Proof.
  intros [p q | a] d Hv Hsafe.
  - exact I.
  - apply arc_offset_arc_valid; assumption.
Qed.

(* One-step reduction of last over a two-cons prefix (definitional).         *)
Lemma last_cons_cons {A : Type} : forall (a b : A) (l : list A) (dflt : A),
  last (a :: b :: l) dflt = last (b :: l) dflt.
Proof. reflexivity. Qed.

Lemma last_snoc {A : Type} : forall (l : list A) (x dflt : A),
  last (l ++ [x]) dflt = x.
Proof.
  induction l as [| a l' IH]; intros x dflt.
  - reflexivity.
  - destruct l' as [| b l''].
    + reflexivity.
    + exact (IH x dflt).
Qed.

Lemma curve_ring_adjacent_snoc : forall (l : CurveRing) (x s0 : CurveSegment),
  l <> [] ->
  curve_ring_adjacent l ->
  curve_segment_end (last l s0) = curve_segment_start x ->
  curve_ring_adjacent (l ++ [x]).
Proof.
  induction l as [| a l' IH]; intros x s0 Hne Hadj Hlast.
  - contradiction.
  - destruct l' as [| b l''].
    + simpl. split; [ exact Hlast | exact I ].
    + destruct Hadj as [Hab Hadj'].
      simpl. split.
      * exact Hab.
      * apply (IH x s0); [ discriminate | exact Hadj' | exact Hlast ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The assembly walk.                                                     *)
(* -------------------------------------------------------------------------- *)

Section Assembly.

  Variable d : R.

  (* The G1 decision: an abstract boolean oracle for normal-field            *)
  (* equality.  Real equality is undecidable computably; the extracted       *)
  (* implementation supplies the comparison, and all theorems below          *)
  (* depend only on this spec.                                               *)
  Variable g1dec : CurveSegment -> CurveSegment -> bool.
  Hypothesis g1dec_spec : forall s1 s2,
    g1dec s1 s2 = true <-> segment_norm_end s1 = segment_norm_start s2.

  Lemma g1dec_false_ne : forall s1 s2,
    g1dec s1 s2 = false ->
    segment_norm_end s1 <> segment_norm_start s2.
  Proof.
    intros s1 s2 Hf He.
    rewrite (proj2 (g1dec_spec s1 s2) He) in Hf. discriminate.
  Qed.

  (* The round join between two consecutive offset segments, as a            *)
  (* CurveSegment (the CurveRoundJoin arc).                                  *)
  Definition join_arc (s1 s2 : CurveSegment) : CurveSegment :=
    CSArc (round_join_arc (curve_segment_end s1) d
             (segment_norm_end s1) (segment_norm_start s2)).

  Fixpoint offset_walk (r : CurveRing) : CurveRing :=
    match r with
    | [] => []
    | s1 :: rest =>
        match rest with
        | [] => [curve_segment_offset s1 d]
        | s2 :: _ =>
            if g1dec s1 s2
            then curve_segment_offset s1 d :: offset_walk rest
            else curve_segment_offset s1 d :: join_arc s1 s2 :: offset_walk rest
        end
    end.

  (* Definitional unfolding of the walk on a two-segment prefix (the         *)
  (* Section-local fixpoint does not refold under simpl/cbn).                 *)
  Lemma offset_walk_eq : forall s1 s2 rest',
    offset_walk (s1 :: s2 :: rest') =
    if g1dec s1 s2
    then curve_segment_offset s1 d :: offset_walk (s2 :: rest')
    else curve_segment_offset s1 d :: join_arc s1 s2
           :: offset_walk (s2 :: rest').
  Proof. reflexivity. Qed.

  (* The assembled offset ring: the walk plus, if the closing join (last     *)
  (* segment back to the first) is not G1, its round join arc.               *)
  Definition curve_ring_offset_round (r : CurveRing) : CurveRing :=
    match r with
    | [] => []
    | s0 :: _ =>
        if g1dec (last r s0) s0
        then offset_walk r
        else offset_walk r ++ [join_arc (last r s0) s0]
    end.

  (* The walk always starts with the first segment's offset.                 *)
  Lemma offset_walk_head : forall s rest,
    exists t, offset_walk (s :: rest) = curve_segment_offset s d :: t.
  Proof.
    intros s [| s2 rest'].
    - exists []. reflexivity.
    - rewrite offset_walk_eq. destruct (g1dec s s2); eexists; reflexivity.
  Qed.

  (* ... and ends with the last segment's offset (joins are interior).       *)
  Lemma offset_walk_last : forall r s0,
    r <> [] ->
    last (offset_walk r) (curve_segment_offset s0 d) =
    curve_segment_offset (last r s0) d.
  Proof.
    induction r as [| s1 rest IH]; intros s0 Hne.
    - contradiction.
    - destruct rest as [| s2 rest'].
      + reflexivity.
      + destruct (offset_walk_head s2 rest') as [t Ht].
        rewrite offset_walk_eq.
        rewrite (last_cons_cons s1 s2 rest').
        destruct (g1dec s1 s2); rewrite Ht.
        * rewrite last_cons_cons. rewrite <- Ht.
          apply IH. discriminate.
        * rewrite !last_cons_cons. rewrite <- Ht.
          apply IH. discriminate.
  Qed.

  (* §2a  Arc validity of everything the walk emits.                         *)

  Lemma join_arc_arc_valid : forall s1 s2,
    segment_arc_valid s1 -> segment_nondeg s1 ->
    segment_arc_valid s2 -> segment_nondeg s2 ->
    g1dec s1 s2 = false ->
    vadd (segment_norm_end s1) (segment_norm_start s2) <> vzero ->
    d <> 0 ->
    segment_arc_valid (join_arc s1 s2).
  Proof.
    intros s1 s2 Hv1 Hn1 Hv2 Hn2 Hf Hnut Hd.
    cbn [join_arc segment_arc_valid].
    apply round_join_arc_valid.
    - apply segment_norm_end_unit; assumption.
    - apply segment_norm_start_unit; assumption.
    - apply g1dec_false_ne. exact Hf.
    - exact Hnut.
    - exact Hd.
  Qed.

  (* No U-turn at any consecutive join (anti-parallel normals; the S-curve   *)
  (* boundary that needs TWO arcs).  Same recursion shape as adjacency.      *)
  Fixpoint ring_no_uturn_joins (r : CurveRing) : Prop :=
    match r with
    | [] => True
    | s1 :: rest =>
        match rest with
        | [] => True
        | s2 :: _ =>
            vadd (segment_norm_end s1) (segment_norm_start s2) <> vzero /\
            ring_no_uturn_joins rest
        end
    end.

  Definition ring_no_uturn_closing (r : CurveRing) : Prop :=
    match r with
    | [] => True
    | s :: _ =>
        vadd (segment_norm_end (last r s)) (segment_norm_start s) <> vzero
    end.

  Lemma offset_walk_arcs_valid : forall r,
    curve_ring_arcs_valid r ->
    Forall segment_nondeg r ->
    ring_offset_safe r d ->
    ring_no_uturn_joins r ->
    d <> 0 ->
    curve_ring_arcs_valid (offset_walk r).
  Proof.
    induction r as [| s1 rest IH]; intros Hv Hn Hsafe Hnut Hd.
    - constructor.
    - destruct rest as [| s2 rest'].
      + constructor; [ | constructor ].
        apply curve_segment_offset_arc_valid;
          [ exact (Forall_inv Hv) | exact (Forall_inv Hsafe) ].
      + destruct Hnut as [Hnut1 Hnut'].
        assert (Hoff : segment_arc_valid (curve_segment_offset s1 d))
          by (apply curve_segment_offset_arc_valid;
              [ exact (Forall_inv Hv) | exact (Forall_inv Hsafe) ]).
        assert (Hrest : curve_ring_arcs_valid (offset_walk (s2 :: rest')))
          by (apply IH;
              [ exact (Forall_inv_tail Hv) | exact (Forall_inv_tail Hn)
              | exact (Forall_inv_tail Hsafe) | exact Hnut' | exact Hd ]).
        rewrite offset_walk_eq. destruct (g1dec s1 s2) eqn:E.
        * constructor; assumption.
        * constructor; [ exact Hoff | constructor; [ | exact Hrest ] ].
          apply join_arc_arc_valid;
            [ exact (Forall_inv Hv) | exact (Forall_inv Hn)
            | exact (Forall_inv (Forall_inv_tail Hv))
            | exact (Forall_inv (Forall_inv_tail Hn))
            | exact E | exact Hnut1 | exact Hd ].
  Qed.

  (* §2b  Adjacency of the walk.                                             *)

  (* The two splice facts at a non-G1 join, in CurveSegment terms.           *)
  Lemma join_arc_splice : forall s1 s2,
    segment_arc_valid s1 -> segment_arc_valid s2 ->
    curve_segment_end s1 = curve_segment_start s2 ->
    curve_segment_end (curve_segment_offset s1 d) =
      curve_segment_start (join_arc s1 s2) /\
    curve_segment_end (join_arc s1 s2) =
      curve_segment_start (curve_segment_offset s2 d).
  Proof.
    intros s1 s2 Hv1 Hv2 HP.
    destruct (round_join_connects s1 s2 d Hv1 Hv2 HP) as [Hs He].
    split.
    - symmetry. exact Hs.
    - exact He.
  Qed.

  Lemma offset_walk_adjacent : forall r,
    curve_ring_arcs_valid r ->
    curve_ring_adjacent r ->
    curve_ring_adjacent (offset_walk r).
  Proof.
    induction r as [| s1 rest IH]; intros Hv Hadj.
    - exact I.
    - destruct rest as [| s2 rest'].
      + exact I.
      + destruct Hadj as [Hj Hadj'].
        assert (Hv1 := Forall_inv Hv).
        assert (Hv2 := Forall_inv (Forall_inv_tail Hv)).
        assert (Hrest : curve_ring_adjacent (offset_walk (s2 :: rest')))
          by (apply IH; [ exact (Forall_inv_tail Hv) | exact Hadj' ]).
        destruct (offset_walk_head s2 rest') as [t Ht].
        rewrite offset_walk_eq. destruct (g1dec s1 s2) eqn:E.
        * (* G1: direct seam *)
          rewrite Ht. split.
          -- apply (segment_join_offset_continuous s1 s2 d Hv1 Hv2 Hj).
             apply (proj1 (g1dec_spec s1 s2)). exact E.
          -- rewrite <- Ht. exact Hrest.
        * (* non-G1: offset s1 -> join arc -> offset s2 *)
          destruct (join_arc_splice s1 s2 Hv1 Hv2 Hj) as [Hsa Hse].
          rewrite Ht. split; [ exact Hsa | split ].
          -- exact Hse.
          -- rewrite <- Ht. exact Hrest.
  Qed.

  (* §2c  Closedness and the assembled headline.                             *)

  Theorem curve_ring_offset_round_valid : forall r,
    valid_curve_ring r ->
    Forall segment_nondeg r ->
    ring_offset_safe r d ->
    ring_no_uturn_joins r ->
    ring_no_uturn_closing r ->
    d <> 0 ->
    valid_curve_ring (curve_ring_offset_round r).
  Proof.
    intros r [Hv [Hadj Hcl]] Hn Hsafe Hnut Hnutc Hd.
    (* the ring is nonempty (closedness of [] is False) *)
    destruct r as [| s0 rest]; [ contradiction | ].
    assert (Hne : s0 :: rest <> @nil CurveSegment) by discriminate.
    (* per-segment facts about the LAST segment (for the closing join) *)
    assert (Hin : In (last (s0 :: rest) s0) (s0 :: rest))
      by (apply last_in; exact Hne).
    assert (Hvlast : segment_arc_valid (last (s0 :: rest) s0))
      by (exact (proj1 (Forall_forall _ _) Hv _ Hin)).
    assert (Hnlast : segment_nondeg (last (s0 :: rest) s0))
      by (exact (proj1 (Forall_forall _ _) Hn _ Hin)).
    assert (Hv0 := Forall_inv Hv).
    assert (Hn0 := Forall_inv Hn).
    (* shared facts about the walk *)
    assert (Hwv : curve_ring_arcs_valid (offset_walk (s0 :: rest)))
      by (apply offset_walk_arcs_valid; assumption).
    assert (Hwa : curve_ring_adjacent (offset_walk (s0 :: rest)))
      by (apply offset_walk_adjacent; assumption).
    destruct (offset_walk_head s0 rest) as [t Ht].
    assert (Hwlast : last (offset_walk (s0 :: rest))
                          (curve_segment_offset s0 d) =
                     curve_segment_offset (last (s0 :: rest) s0) d)
      by (apply offset_walk_last; exact Hne).
    unfold curve_ring_offset_round.
    destruct (g1dec (last (s0 :: rest) s0) s0) eqn:Ec.
    - (* G1 closing seam: the walk itself is the ring *)
      split; [ exact Hwv | split; [ exact Hwa | ] ].
      assert (Hseam : curve_segment_end
                        (last (offset_walk (s0 :: rest))
                              (curve_segment_offset s0 d)) =
                      curve_segment_start (curve_segment_offset s0 d)).
      { rewrite Hwlast.
        apply (segment_join_offset_continuous _ _ d Hvlast Hv0 Hcl).
        apply (proj1 (g1dec_spec _ _)). exact Ec. }
      unfold curve_ring_closed.
      rewrite Ht in Hseam |- *.
      exact Hseam.
    - (* non-G1 closing: append the closing join arc *)
      destruct (join_arc_splice (last (s0 :: rest) s0) s0 Hvlast Hv0 Hcl)
        as [Hsa Hse].
      split; [ | split ].
      + (* arcs valid: walk ++ [join] *)
        apply (proj2 (Forall_app _ _ _)). split; [ exact Hwv | ].
        constructor; [ | constructor ].
        apply join_arc_arc_valid; assumption.
      + (* adjacency: snoc the closing join onto the walk *)
        apply (curve_ring_adjacent_snoc _ _ (curve_segment_offset s0 d)).
        * rewrite Ht. discriminate.
        * exact Hwa.
        * rewrite Hwlast. exact Hsa.
      + (* closed: end of closing join = start of first offset segment *)
        unfold curve_ring_closed.
        rewrite Ht. cbn [app].
        assert (Hl : last (curve_segment_offset s0 d
                             :: t ++ [join_arc (last (s0 :: rest) s0) s0])
                          (curve_segment_offset s0 d)
                     = join_arc (last (s0 :: rest) s0) s0).
        { change (curve_segment_offset s0 d
                    :: t ++ [join_arc (last (s0 :: rest) s0) s0])
            with ((curve_segment_offset s0 d :: t)
                    ++ [join_arc (last (s0 :: rest) s0) s0]).
          apply last_snoc. }
        rewrite Hl.
        exact Hse.
  Qed.

  (* §2d  Coherence: on a smooth ring the walk inserts nothing and is        *)
  (* exactly rung 3's plain segment-wise offset.                             *)

  Lemma offset_walk_smooth_eq_map : forall r,
    ring_joins_normals_consistent r ->
    offset_walk r = curve_ring_offset r d.
  Proof.
    induction r as [| s1 rest IH]; intros HG1.
    - reflexivity.
    - destruct rest as [| s2 rest'].
      + reflexivity.
      + destruct HG1 as [Hn HG1'].
        rewrite offset_walk_eq.
        rewrite (proj2 (g1dec_spec s1 s2) Hn).
        change (curve_ring_offset (s1 :: s2 :: rest') d)
          with (curve_segment_offset s1 d
                  :: curve_ring_offset (s2 :: rest') d).
        f_equal.
        exact (IH HG1').
  Qed.

End Assembly.

(* ========================================================================== *)
(* Axiom audit.  ALL headlines below are 3-axiom (classical-reals trio:      *)
(* sig_not_dec, sig_forall_dec, functional_extensionality_dep).              *)
(* ========================================================================== *)

Print Assumptions curve_ring_offset_round_valid.
Print Assumptions offset_walk_arcs_valid.
Print Assumptions offset_walk_adjacent.
Print Assumptions join_arc_arc_valid.
Print Assumptions offset_walk_smooth_eq_map.
