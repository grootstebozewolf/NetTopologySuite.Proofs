(* ============================================================================
   NetTopologySuite.Proofs.HostCircChordOracle
   ----------------------------------------------------------------------------
   NTS/JTS: MCIndexNoder mixed segment (LineString chord × CircularString).
   claimId: 0007-host-circ-chord-oracle

   Host 𝓘 on MkCirc × MkChord and the reverse. In scope
   (|Δθ| < 2π, nondegenerate chord) a Hit is on both curves, and every
   such incidence is a Hit. Full-span eggs and degenerate chords Decline
   by name. circ×circ stays the existing host arm (Decline is False).
   first_cook_scope does not gain the mixed arms.

   The locked CC LS+CS joint is a host Hit, so the ∀-bag loop does not
   StepIDecline on that pair. The joint is already a vertex of both
   pieces, so it is not a progress_hit. An interior hit of the same
   locked quarter (F1) is a bag_progress_step and the children keep
   same_support.

   3-axiom host. No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import
  Distance SheetHenCook SheetHenBag ZetaHostHit ZetaEggBridge
  CircularCookMkCirc IntakeWalker.
Import ListNotations.
Local Open Scope R_scope.
Local Open Scope list_scope.

(* -------------------------------------------------------------------------- *)
(* Soundness and completeness, both argument orders.                          *)
(* -------------------------------------------------------------------------- *)

Lemma I_ok_circ_chord_hit_sound :
  forall c s p ti tj,
    I_ok (MkCirc c) (MkChord s) (IHit p ti tj) ->
    on_circ c ti p /\ on_chord s tj p.
Proof.
  intros c s p ti tj H. destruct H as [_ H]. exact H.
Qed.

Lemma I_ok_chord_circ_hit_sound :
  forall s c p ti tj,
    I_ok (MkChord s) (MkCirc c) (IHit p ti tj) ->
    on_chord s ti p /\ on_circ c tj p.
Proof.
  intros s c p ti tj H. destruct H as [_ H]. exact H.
Qed.

Lemma I_ok_circ_chord_hit_complete :
  forall c s p ti tj,
    circ_chord_host_scope c s ->
    on_circ c ti p ->
    on_chord s tj p ->
    I_ok (MkCirc c) (MkChord s) (IHit p ti tj).
Proof.
  intros c s p ti tj Hs Hc Hh.
  unfold I_ok. split; [exact Hs|]. split; [exact Hc|exact Hh].
Qed.

Lemma I_ok_chord_circ_hit_complete :
  forall s c p ti tj,
    circ_chord_host_scope c s ->
    on_chord s ti p ->
    on_circ c tj p ->
    I_ok (MkChord s) (MkCirc c) (IHit p ti tj).
Proof.
  intros s c p ti tj Hs Hh Hc.
  unfold I_ok. split; [exact Hs|]. split; [exact Hh|exact Hc].
Qed.

Lemma I_ok_circ_chord_no_miss :
  forall c s p ti tj,
    circ_chord_host_scope c s ->
    on_circ c ti p ->
    on_chord s tj p ->
    exists p' ti' tj',
      I_ok (MkCirc c) (MkChord s) (IHit p' ti' tj').
Proof.
  intros c s p ti tj Hs Hc Hh.
  exists p, ti, tj.
  apply I_ok_circ_chord_hit_complete; assumption.
Qed.

Lemma I_ok_chord_circ_no_miss :
  forall s c p ti tj,
    circ_chord_host_scope c s ->
    on_chord s ti p ->
    on_circ c tj p ->
    exists p' ti' tj',
      I_ok (MkChord s) (MkCirc c) (IHit p' ti' tj').
Proof.
  intros s c p ti tj Hs Hh Hc.
  exists p, ti, tj.
  apply I_ok_chord_circ_hit_complete; assumption.
Qed.

Lemma I_ok_circ_chord_empty_sound :
  forall c s,
    I_ok (MkCirc c) (MkChord s) IEmpty ->
    ~ exists X t1 t2, on_circ c t1 X /\ on_chord s t2 X.
Proof.
  intros c s H. destruct H as [_ H]. exact H.
Qed.

Lemma I_ok_chord_circ_empty_sound :
  forall s c,
    I_ok (MkChord s) (MkCirc c) IEmpty ->
    ~ exists X t1 t2, on_chord s t1 X /\ on_circ c t2 X.
Proof.
  intros s c H. destruct H as [_ H]. exact H.
Qed.

Lemma circ_chord_in_scope_not_decline :
  forall c s,
    circ_chord_host_scope c s ->
    ~ I_ok (MkCirc c) (MkChord s) IDecline /\
    ~ I_ok (MkChord s) (MkCirc c) IDecline.
Proof.
  intros c s Hs. split; intro H; apply H; exact Hs.
Qed.

(* Chart hit (host_circ_chord_hit_ok) is a host Hit. *)
Lemma zeta_seg_hit_I_ok :
  forall (c : CircularEgg) (s : ChordEgg) (z : R),
    circ_r c <> 0 ->
    circ_sweep c <> 0 ->
    circ_open_span c ->
    chord_nondeg s ->
    zeta_seg_hit c s z ->
    I_ok (MkCirc c) (MkChord s)
      (IHit (zeta_pt (circ_o c) (egg_pole c) z)
            (t_of_zeta c z) (egg_tj c s z)).
Proof.
  intros c s z Hr Hs Hsp Hnd Hz.
  destruct (host_circ_chord_hit_ok c s Hr Hs Hsp z Hnd Hz) as [Hc Hch].
  apply I_ok_circ_chord_hit_complete.
  - split; assumption.
  - exact Hc.
  - exact Hch.
Qed.

(* -------------------------------------------------------------------------- *)
(* Named declines. Full-span and a degenerate chord are not demoted.          *)
(* circ×circ is already a host arm: Decline is False.                         *)
(* -------------------------------------------------------------------------- *)

Lemma full_span_not_open :
  ~ circ_open_span locked_full_circle_egg.
