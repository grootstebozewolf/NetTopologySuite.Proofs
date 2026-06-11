(* ============================================================================
   NetTopologySuite.Proofs.CurveCapWalk
   ----------------------------------------------------------------------------
   Buffer/noder pipeline, rung 14b (issue #65): the OPEN-CHAIN
   TWO-SIDED CAP WALK -- the last structural emission gap of the
   offset lane.  Buffer an open compound LINE (a chain: adjacent, not
   closed) by walking its left (+d) offset boundary, capping at the
   far end with the rung-7 semicircle, returning along the right (-d)
   boundary, and capping back at the start:

       ring  :=  left ++ [cap_far] ++ right ++ [cap_start]

   The load-bearing design choice, dictated by rung 14a's ORIENTATION
   WART: the right boundary is NOT "the offset of the reversed chain"
   (chords and arcs would need opposite signs); it is the REVERSAL of
   the forward (-d) walk,

       right := curve_ring_reverse (chain_walk (-d) c),

   so every structural fact about it falls out of 14a's reversal
   lemmas (`curve_ring_reverse_{arcs_valid,adjacent,hd,last}`), and no
   per-kind sign threading is needed at all.

     - `chain_walk`: the open walk -- per-segment offsets with chord
       connectors at non-G1 joins, NO closing join (this is what
       distinguishes a chain from a ring).
     - `cap_far` / `cap_start`: rung-7 semicircles at the chain's two
       endpoints (`semicircle_cap_connects` splices the far cap; the
       start cap's mirror splice is `cap_start_connects`).
     - `curve_chain_buffer_valid` (HEADLINE): for a nonempty, adjacent
       chain with valid arcs, non-degenerate chords, two-sided per-arc
       safety (`ring_offset_safe c d` AND `ring_offset_safe c (-d)`),
       and `d <> 0`, the assembled boundary is a CLOSED, VALID compound
       ring -- the two-sided buffer boundary of an open compound line,
       in SQL/MM form.

   With this, every Stage-2 emission of the buffer front-end -- closed
   rings (rungs 6-13) and open chains (this rung) -- produces a valid
   compound ring ready for linearisation and the proven noding spine.

   Pure-R; THREE-AXIOM THROUGHOUT (classical-reals trio).  No
   `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Bool.
From NTS.Proofs Require Import Distance Vec Direction CurveGeometry Overlay.
From NTS.Proofs Require Import ArcChordApprox ArcOffsetThreePoint CurveRingOffset.
From NTS.Proofs Require Import CurveOffsetAssembly CurveSemicircle CurveReverse.
From NTS.Proofs Require Import CurveLinearise CurveMiterJoin BufferOffset.

Import ListNotations.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Small list bricks.  The general app-glue (last_app_nonnil,            *)
(*     curve_ring_adjacent_{cons,app}) is imported from CurveMiterJoin;       *)
(*     only the two bricks unique to this file remain local.                  *)
(* -------------------------------------------------------------------------- *)

Lemma app_nonnil_r {A : Type} : forall (l m : list A),
  m <> [] -> l ++ m <> [].
Proof.
  intros [| a l'] m Hm.
  - exact Hm.
  - discriminate.
Qed.

Lemma hd_app_nonnil {A : Type} : forall (l m : list A) (dflt : A),
  l <> [] -> hd dflt (l ++ m) = hd dflt l.
Proof.
  intros [| a l'] m dflt Hl; [ contradiction | reflexivity ].
Qed.




(* -------------------------------------------------------------------------- *)
(* §2  The open chain walk (offsets + chord connectors, no closing join).     *)
(* -------------------------------------------------------------------------- *)

Section CapWalk.

  Variable d : R.

  Variable g1dec : CurveSegment -> CurveSegment -> bool.
  Hypothesis g1dec_spec : forall s1 s2,
    g1dec s1 s2 = true <-> segment_norm_end s1 = segment_norm_start s2.

  (* The chord connector across a tear, at a given signed distance.          *)
  Definition chain_join (d' : R) (s1 s2 : CurveSegment) : CurveSegment :=
    CSChord (curve_segment_end (curve_segment_offset s1 d'))
            (curve_segment_start (curve_segment_offset s2 d')).

  Fixpoint chain_walk (d' : R) (r : CurveRing) : CurveRing :=
    match r with
    | [] => []
    | s1 :: rest =>
        match rest with
        | [] => [curve_segment_offset s1 d']
        | s2 :: _ =>
            if g1dec s1 s2
            then curve_segment_offset s1 d' :: chain_walk d' rest
            else curve_segment_offset s1 d' :: chain_join d' s1 s2
                   :: chain_walk d' rest
        end
    end.

  Lemma chain_walk_eq : forall d' s1 s2 rest',
    chain_walk d' (s1 :: s2 :: rest') =
    if g1dec s1 s2
    then curve_segment_offset s1 d' :: chain_walk d' (s2 :: rest')
    else curve_segment_offset s1 d' :: chain_join d' s1 s2
           :: chain_walk d' (s2 :: rest').
  Proof. reflexivity. Qed.

  Lemma chain_walk_head : forall d' s rest,
    exists t, chain_walk d' (s :: rest) = curve_segment_offset s d' :: t.
  Proof.
    intros d' s [| s2 rest'].
    - exists []. reflexivity.
    - rewrite chain_walk_eq.
      destruct (g1dec s s2); eexists; reflexivity.
  Qed.

  Lemma chain_walk_nonnil : forall d' s rest,
    chain_walk d' (s :: rest) <> [].
  Proof.
    intros d' s rest H.
    destruct (chain_walk_head d' s rest) as [t Ht].
    rewrite Ht in H. discriminate.
  Qed.

  Lemma chain_walk_last : forall d' r s0,
    r <> [] ->
    last (chain_walk d' r) (curve_segment_offset s0 d') =
    curve_segment_offset (last r s0) d'.
  Proof.
    intros d'.
    induction r as [| s1 rest IH]; intros s0 Hne.
    - contradiction.
    - destruct rest as [| s2 rest'].
      + reflexivity.
      + rewrite chain_walk_eq.
        rewrite (last_cons_cons s1 s2 rest').
        destruct (chain_walk_head d' s2 rest') as [t Ht].
        destruct (g1dec s1 s2); rewrite Ht.
        * rewrite last_cons_cons. rewrite <- Ht.
          apply IH. discriminate.
        * rewrite !last_cons_cons. rewrite <- Ht.
          apply IH. discriminate.
  Qed.

  Lemma chain_walk_arcs_valid : forall d' r,
    curve_ring_arcs_valid r ->
    ring_offset_safe r d' ->
    curve_ring_arcs_valid (chain_walk d' r).
  Proof.
    intros d'.
    induction r as [| s1 rest IH]; intros Hv Hsafe.
    - constructor.
    - destruct rest as [| s2 rest'].
      + constructor; [ | constructor ].
        apply curve_segment_offset_arc_valid;
          [ exact (Forall_inv Hv) | exact (Forall_inv Hsafe) ].
      + assert (Hoff : segment_arc_valid (curve_segment_offset s1 d'))
          by (apply curve_segment_offset_arc_valid;
              [ exact (Forall_inv Hv) | exact (Forall_inv Hsafe) ]).
        assert (Hrest : curve_ring_arcs_valid (chain_walk d' (s2 :: rest')))
          by (apply IH;
              [ exact (Forall_inv_tail Hv) | exact (Forall_inv_tail Hsafe) ]).
        rewrite chain_walk_eq. destruct (g1dec s1 s2) eqn:E.
        * constructor; assumption.
        * constructor; [ exact Hoff | constructor; [ exact I | exact Hrest ] ].
  Qed.

  Lemma chain_walk_adjacent : forall d' r,
    curve_ring_arcs_valid r ->
    curve_ring_adjacent r ->
    curve_ring_adjacent (chain_walk d' r).
  Proof.
    intros d'.
    induction r as [| s1 rest IH]; intros Hv Hadj.
    - exact I.
    - destruct rest as [| s2 rest'].
      + exact I.
      + destruct Hadj as [Hj Hadj'].
        assert (Hv1 := Forall_inv Hv).
        assert (Hv2 := Forall_inv (Forall_inv_tail Hv)).
        assert (Hrest : curve_ring_adjacent (chain_walk d' (s2 :: rest')))
          by (apply IH; [ exact (Forall_inv_tail Hv) | exact Hadj' ]).
        destruct (chain_walk_head d' s2 rest') as [t Ht].
        rewrite chain_walk_eq. destruct (g1dec s1 s2) eqn:E.
        * rewrite Ht. split.
          -- apply (segment_join_offset_continuous s1 s2 d' Hv1 Hv2 Hj).
             apply (proj1 (g1dec_spec s1 s2)). exact E.
          -- rewrite <- Ht. exact Hrest.
        * rewrite Ht. split; [ reflexivity | split ].
          -- reflexivity.
          -- rewrite <- Ht. exact Hrest.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* §3  The caps.                                                       *)
  (* ------------------------------------------------------------------ *)

  Definition cap_far (s : CurveSegment) : CurveSegment :=
    CSArc (semicircle_arc (curve_segment_end s) d
             (segment_norm_end s)
             (cap_tangent (segment_norm_end s))).

  Definition cap_start (s : CurveSegment) : CurveSegment :=
    CSArc (semicircle_arc (curve_segment_start s) (- d)
             (segment_norm_start s)
             (cap_tangent (segment_norm_start s))).

  (* Far cap: rung 7's semicircle_cap_connects splices it directly.      *)
  Lemma cap_far_connects : forall s,
    segment_arc_valid s ->
    curve_segment_start (cap_far s) =
      curve_segment_end (curve_segment_offset s d) /\
    curve_segment_end (cap_far s) =
      curve_segment_end (curve_segment_offset s (- d)).
  Proof.
    intros s Hv.
    destruct (semicircle_cap_connects s d (cap_tangent (segment_norm_end s))
                Hv) as [Hs He].
    split; [ exact Hs | exact He ].
  Qed.

  (* Start cap: the mirror splice at the chain's start point.            *)
  Lemma cap_start_connects : forall s,
    segment_arc_valid s ->
    curve_segment_start (cap_start s) =
      curve_segment_start (curve_segment_offset s (- d)) /\
    curve_segment_end (cap_start s) =
      curve_segment_start (curve_segment_offset s d).
  Proof.
    intros s Hv.
    split.
    - cbn [cap_start curve_segment_start].
      rewrite (curve_segment_offset_start s (- d) Hv).
      reflexivity.
    - cbn [cap_start curve_segment_end].
      rewrite (curve_segment_offset_start s d Hv).
      unfold semicircle_arc. cbn [arc_end].
      apply point_eq; unfold pt_translate; cbn [px py]; ring.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* §4  The two-sided buffer boundary of an open chain.                 *)
  (* ------------------------------------------------------------------ *)

  Definition curve_chain_buffer (c : CurveRing) : CurveRing :=
    match c with
    | [] => []
    | s0 :: _ =>
        chain_walk d c
          ++ [cap_far (last c s0)]
          ++ curve_ring_reverse (chain_walk (- d) c)
          ++ [cap_start s0]
    end.

  Theorem curve_chain_buffer_valid : forall c,
    c <> [] ->
    curve_ring_arcs_valid c ->
    Forall segment_nondeg c ->
    curve_ring_adjacent c ->
    ring_offset_safe c d ->
    ring_offset_safe c (- d) ->
    d <> 0 ->
    valid_curve_ring (curve_chain_buffer c).
  Proof.
    intros c Hcne Hv Hn Hadj Hsp Hsm Hd.
    destruct c as [| s0 rest]; [ contradiction | ]. clear Hcne.
    destruct (chain_walk_head d s0 rest) as [tW HtW].
    destruct (chain_walk_head (- d) s0 rest) as [tM HtM].
    unfold curve_chain_buffer.
    set (slast := last (s0 :: rest) s0) in *.
    assert (Hin : In slast (s0 :: rest))
      by (apply last_in; discriminate).
    assert (Hvlast : segment_arc_valid slast)
      by (exact (proj1 (Forall_forall _ _) Hv _ Hin)).
    assert (Hnlast : segment_nondeg slast)
      by (exact (proj1 (Forall_forall _ _) Hn _ Hin)).
    assert (Hv0 := Forall_inv Hv).
    assert (Hn0 := Forall_inv Hn).
    set (W := chain_walk d (s0 :: rest)) in *.
    set (M := chain_walk (- d) (s0 :: rest)) in *.
    set (RV := curve_ring_reverse M).
    set (CF := cap_far slast).
    set (CS := cap_start s0).
    (* --- block facts --- *)
    assert (HWne : W <> []) by (apply chain_walk_nonnil).
    assert (HMne : M <> []) by (apply chain_walk_nonnil).
    assert (HRVne : RV <> []).
    { unfold RV. rewrite HtM. apply curve_ring_reverse_nonnil. }
    assert (HXne : [CF] ++ RV ++ [CS] <> @nil CurveSegment) by discriminate.
    assert (HYne : RV ++ [CS] <> @nil CurveSegment)
      by (apply app_nonnil_r; discriminate).
    assert (HCFv : segment_arc_valid CF).
    { unfold CF, cap_far. cbn [segment_arc_valid].
      apply semicircle_arc_valid.
      - apply segment_norm_end_unit; assumption.
      - apply cap_tangent_unit. apply segment_norm_end_unit; assumption.
      - apply cap_tangent_perp.
      - exact Hd. }
    assert (HCSv : segment_arc_valid CS).
    { unfold CS, cap_start. cbn [segment_arc_valid].
      apply semicircle_arc_valid.
      - apply segment_norm_start_unit; assumption.
      - apply cap_tangent_unit. apply segment_norm_start_unit; assumption.
      - apply cap_tangent_perp.
      - lra. }
    assert (HWadj : curve_ring_adjacent W)
      by (unfold W; apply chain_walk_adjacent; assumption).
    assert (HRVadj : curve_ring_adjacent RV).
    { unfold RV. apply curve_ring_reverse_adjacent.
      unfold M. apply chain_walk_adjacent; assumption. }
    assert (HWlast : last W CS = curve_segment_offset slast d).
    { unfold W.
      rewrite (last_default_irrel _ CS (curve_segment_offset s0 d)
                 (chain_walk_nonnil d s0 rest)).
      apply (chain_walk_last d (s0 :: rest) s0). discriminate. }
    assert (HRVlast : last RV CS =
                      rev_segment (curve_segment_offset s0 (- d))).
    { unfold RV. rewrite HtM. apply curve_ring_reverse_last. }
    assert (HRVhd : hd CS RV =
                    rev_segment (curve_segment_offset slast (- d))).
    { unfold RV. rewrite HtM.
      rewrite curve_ring_reverse_hd.
      rewrite <- HtM.
      f_equal.
      apply (chain_walk_last (- d) (s0 :: rest) s0). discriminate. }
    (* --- seams --- *)
    assert (S1 : curve_segment_end (last W CS) = curve_segment_start CF).
    { rewrite HWlast. symmetry.
      exact (proj1 (cap_far_connects slast Hvlast)). }
    assert (S2 : curve_segment_end CF = curve_segment_start (hd CS RV)).
    { rewrite HRVhd. rewrite rev_segment_start.
      exact (proj2 (cap_far_connects slast Hvlast)). }
    assert (S3 : curve_segment_end (last RV CS) = curve_segment_start CS).
    { rewrite HRVlast. rewrite rev_segment_end. symmetry.
      exact (proj1 (cap_start_connects s0 Hv0)). }
    split; [ | split ].
    - (* arcs valid *)
      apply (proj2 (Forall_app _ _ _)). split.
      { unfold W. apply chain_walk_arcs_valid; assumption. }
      apply (proj2 (Forall_app _ _ _)). split.
      { constructor; [ exact HCFv | constructor ]. }
      apply (proj2 (Forall_app _ _ _)). split.
      { unfold RV. apply curve_ring_reverse_arcs_valid.
        unfold M. apply chain_walk_arcs_valid; assumption. }
      { constructor; [ exact HCSv | constructor ]. }
    - (* adjacency: glue the four blocks *)
      apply (curve_ring_adjacent_app W _ CS HWne HXne HWadj).
      + (* adjacent ([CF] ++ RV ++ [CS]) *)
        change ([CF] ++ RV ++ [CS]) with (CF :: (RV ++ [CS])).
        apply (curve_ring_adjacent_cons CF _ CS HYne).
        * rewrite (hd_app_nonnil RV [CS] CS HRVne). exact S2.
        * apply (curve_ring_adjacent_app RV [CS] CS HRVne
                   ltac:(discriminate) HRVadj I).
          cbn [hd]. exact S3.
      + (* seam W -> CF *)
        change ([CF] ++ RV ++ [CS]) with (CF :: (RV ++ [CS])).
        cbn [hd]. exact S1.
    - (* closed: end of cap_start = start of the first offset segment *)
      rewrite HtW. cbn [curve_ring_closed app].
      assert (Hlast :
          last (curve_segment_offset s0 d
                  :: tW ++ CF :: RV ++ [CS])
               (curve_segment_offset s0 d) = CS).
      { change (curve_segment_offset s0 d
                  :: tW ++ CF :: RV ++ [CS])
          with ((curve_segment_offset s0 d :: tW)
                  ++ (CF :: RV ++ [CS])).
        rewrite (last_app_nonnil _ _ _ HXne).
        rewrite (last_cons_nonnil CF _ _ HYne).
        rewrite (last_app_nonnil RV [CS] _ ltac:(discriminate)).
        reflexivity. }
      rewrite Hlast.
      exact (proj2 (cap_start_connects s0 Hv0)).
  Qed.

End CapWalk.

(* ========================================================================== *)
(* Axiom audit.  ALL headlines below are 3-axiom (classical-reals trio:      *)
(* sig_not_dec, sig_forall_dec, functional_extensionality_dep).              *)
(* ========================================================================== *)

Print Assumptions curve_chain_buffer_valid.
Print Assumptions cap_start_connects.
Print Assumptions cap_far_connects.
Print Assumptions chain_walk_adjacent.
