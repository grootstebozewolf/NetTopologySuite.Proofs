(* ============================================================================
   NetTopologySuite.Proofs.CurveOffsetEmit
   ----------------------------------------------------------------------------
   Buffer/noder pipeline, rung 11 (issue #65, forward pointer P3): the
   STAGE-2 -> STAGE-3 HANDOFF -- the offset front-end's emitted edge
   list is a closed Phase-3 ring.

   `buffer-noder-pipeline.md` §2.2 specifies the front-end contract:
   emit a closed raw buffer curve (`offset_curve : ... -> list edges`)
   and feed it to the proven snap-rounding noder "with zero change".
   The curve lane built the emitter (rungs 3-10:
   `curve_ring_offset_total`, joins and caps included); the spine
   consumes Phase-3 `Ring`s via the Option-B linearisation
   (`CurveGeometry.chord_approx_ring`).  This file closes the seam
   between them:

     - `curve_segment_offset_chord_is_offset_seg` (coherence with the
       LINEAR pipeline): on a chord, the curve front-end's per-segment
       offset IS `BufferOffset.offset_seg` -- definitionally.  The
       curve emitter conservatively extends the linear stage-2a seam.

     - `curve_ring_offset_all_chord`: the segment-wise map preserves
       all-chord rings (joins are what introduce arcs).

     - `offset_emit_ring_closed` (HEADLINE): for any valid compound
       ring under the rung-8 side conditions, the assembled offset
       ring's chord linearisation is a `ring_closed` Phase-3 ring --
       the emitted edge list CLOSES, which is the structural contract
       stage 3 (noding) needs from stage 2.  Composition of
       `curve_ring_offset_total_valid` (rung 8) with
       `CurveLinearise.chord_approx_ring_closed`.

     - `linear_offset_emit_ring_closed` (the P3 discharge): the same,
       specialised to ALL-CHORD input -- the LINEAR pipeline's
       round-join offset emitter, with join arcs linearised, emits a
       closed edge ring.  This discharges the round-join flavour of
       the linear "emitted join/cap edge list" gap
       (`buffer-noder-pipeline.md` rows 2b/2c).  The remainders this
       header once carried have since landed: bevel and miter join
       emission in `CurveBevelJoin.v` / `CurveMiterJoin.v` (rungs
       12-13, each with its own `*_emit_ring_closed` handoff), and
       the open-chain two-sided cap walk in `CurveCapWalk.v`
       (rung 14b).

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
From NTS.Proofs Require Import CurveOffsetAssembly CurveSemicircle.
From NTS.Proofs Require Import CurveOffsetAssemblyTotal CurveLinearise.
From NTS.Proofs Require Import BufferOffset.

Import ListNotations.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Coherence with the linear pipeline.                                    *)
(* -------------------------------------------------------------------------- *)

(* On a chord, the curve front-end's per-segment offset is exactly the       *)
(* linear stage-2a offset segment.                                            *)
Lemma curve_segment_offset_chord_is_offset_seg : forall (p q : Point) (d : R),
  curve_segment_offset (CSChord p q) d =
  CSChord (fst (offset_seg p q d)) (snd (offset_seg p q d)).
Proof. reflexivity. Qed.

Definition segment_is_chord (s : CurveSegment) : Prop :=
  match s with
  | CSChord _ _ => True
  | CSArc _ => False
  end.

(* The segment-wise map preserves all-chord rings (only JOINS add arcs).     *)
Lemma curve_ring_offset_all_chord : forall (r : CurveRing) (d : R),
  Forall segment_is_chord r ->
  Forall segment_is_chord (curve_ring_offset r d).
Proof.
  induction r as [| s rest IH]; intros d Hc.
  - constructor.
  - simpl. constructor.
    + destruct s as [p q | a]; [ exact I | exact (Forall_inv Hc) ].
    + apply IH. exact (Forall_inv_tail Hc).
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The handoff headline: the emitted edge list closes.                    *)
(* -------------------------------------------------------------------------- *)

Section Emit.

  Variable d : R.

  Variable g1dec : CurveSegment -> CurveSegment -> bool.
  Hypothesis g1dec_spec : forall s1 s2,
    g1dec s1 s2 = true <-> segment_norm_end s1 = segment_norm_start s2.

  Variable uturndec : CurveSegment -> CurveSegment -> bool.
  Hypothesis uturndec_spec : forall s1 s2,
    uturndec s1 s2 = true <->
    segment_norm_start s2 = vneg (segment_norm_end s1).

  Variable tsel : CurveSegment -> CurveSegment -> Vec.
  Hypothesis tsel_spec : forall s1 s2,
    segment_arc_valid s1 -> segment_nondeg s1 ->
    vdot (tsel s1 s2) (tsel s1 s2) = 1 /\
    vdot (segment_norm_end s1) (tsel s1 s2) = 0.

  (* The emitted Phase-3 ring: assemble (rung 8), then linearise (Option B). *)
  Definition offset_emit_ring (r : CurveRing) (n : nat) : Ring :=
    chord_approx_ring (curve_ring_offset_total d g1dec uturndec tsel r) n.

  Theorem offset_emit_ring_closed : forall (r : CurveRing) (n : nat),
    valid_curve_ring r ->
    Forall segment_nondeg r ->
    ring_offset_safe r d ->
    d <> 0 ->
    ring_closed (offset_emit_ring r n).
  Proof.
    intros r n Hv Hn Hs Hd.
    unfold offset_emit_ring.
    apply chord_approx_ring_closed.
    destruct (curve_ring_offset_total_valid d g1dec g1dec_spec
                uturndec uturndec_spec tsel tsel_spec r Hv Hn Hs Hd)
      as [_ [_ Hclosed]].
    exact Hclosed.
  Qed.

  (* The P3 discharge: the LINEAR round-join offset emitter -- all-chord     *)
  (* input, join arcs linearised -- emits a closed edge ring.                 *)
  Theorem linear_offset_emit_ring_closed : forall (r : CurveRing) (n : nat),
    Forall segment_is_chord r ->
    valid_curve_ring r ->
    Forall segment_nondeg r ->
    d <> 0 ->
    ring_closed (offset_emit_ring r n).
  Proof.
    intros r n Hchord Hv Hn Hd.
    apply offset_emit_ring_closed; try assumption.
    (* all-chord rings satisfy the per-arc safety bound vacuously *)
    clear Hv Hn.
    induction r as [| s rest IH].
    - constructor.
    - constructor.
      + destruct s as [p q | a];
          [ exact I | destruct (Forall_inv Hchord) ].
      + apply IH. exact (Forall_inv_tail Hchord).
  Qed.

End Emit.

(* ========================================================================== *)
(* Axiom audit.  ALL headlines below are 3-axiom (classical-reals trio:      *)
(* sig_not_dec, sig_forall_dec, functional_extensionality_dep).              *)
(* ========================================================================== *)

Print Assumptions curve_segment_offset_chord_is_offset_seg.
Print Assumptions curve_ring_offset_all_chord.
Print Assumptions offset_emit_ring_closed.
Print Assumptions linear_offset_emit_ring_closed.
