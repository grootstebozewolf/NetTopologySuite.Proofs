(* ============================================================================
   NetTopologySuite.Proofs.SheetHenDonutBag
   ----------------------------------------------------------------------------
   ADR-0007 letters after Accept: the locked donut bag (claimId
   0007-linear-donut-bag) and ρ on that bag only (claimId 0007-linear-donut-rho).

   The bag is the LINEAR donut: oracle/cp_ring_simple_tests.txt's square
   shell (0,0)(10,0)(10,10)(0,10) + square hole (3,3)(7,3)(7,7)(3,7) read as
   eight MkChord on the default sheet. It is not a CurvePolygon with an arc
   in it: eight MkChord; 28 pairs; host I_ok only; no EggCircularArc
   (linear_donut_no_arc). T3's chord x arc fixture (SidecarCircIotaTags.v)
   is not a member of this bag; the mixed cook is not exercised here.

   T4 — the machine, finite, on this linear bag. Every one of the 28
   unordered pairs is Hit / Empty by the named host 𝓘 (I_ok on MkChord ×
   MkChord): the eight adjacent-edge pairs Hit at their shared corner
   (t ∈ {0,1} on both), the two opposite-side pairs of each ring and all
   sixteen shell × hole pairs are Empty. Decline never occurs. No pair uses
   pairwise_nodable_shadow: linear_donut_pairs_classified is I_ok on each
   pair, not the shadow predicate.

   T5 — ρ on this bag only: already noded; corner shares only; width
   conserved; does not discharge LeftoverBagTermArm. Every Hit is at
   parameters in {0,1}, a corner two chickens already share, so one pass of
   host one-steps splits nothing strictly and there is no interior crossing
   to node. This is not the bag loop. General ρ (Parks) stays QEX.

   Not touched: host I_ok, first_cook_scope, sidecar cooks, the oracle wire.

   WITNESS topic: overlay · claimId: 0007-donut-bag · witness: 0007-linear-donut-bag
   board: ADR-0007
   3-axiom host lane (Stdlib Reals). No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Segment SheetHenCook.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The eight eggs.                                                        *)
(* -------------------------------------------------------------------------- *)

Definition s0 : ChordEgg := mkChordEgg (mkPoint 0 0)   (mkPoint 10 0).
Definition s1 : ChordEgg := mkChordEgg (mkPoint 10 0)  (mkPoint 10 10).
Definition s2 : ChordEgg := mkChordEgg (mkPoint 10 10) (mkPoint 0 10).
Definition s3 : ChordEgg := mkChordEgg (mkPoint 0 10)  (mkPoint 0 0).
Definition h0 : ChordEgg := mkChordEgg (mkPoint 3 3)   (mkPoint 7 3).
Definition h1 : ChordEgg := mkChordEgg (mkPoint 7 3)   (mkPoint 7 7).
Definition h2 : ChordEgg := mkChordEgg (mkPoint 7 7)   (mkPoint 3 7).
Definition h3 : ChordEgg := mkChordEgg (mkPoint 3 7)   (mkPoint 3 3).

Definition linear_donut_bag : list ChordEgg := [s0; s1; s2; s3; h0; h1; h2; h3].

Definition linear_donut_egg (i : nat) : ChordEgg := nth i linear_donut_bag s0.

(* -------------------------------------------------------------------------- *)
(* §2  The named verdict on every pair.                                       *)
(* -------------------------------------------------------------------------- *)

(* Adjacent edges Hit at the shared corner; everything else is Empty. *)
Definition linear_donut_verdict (i j : nat) : IResult :=
  match i, j with
  | 0%nat, 1%nat => IHit (mkPoint 10 0) 1 0
  | 1%nat, 2%nat => IHit (mkPoint 10 10) 1 0
  | 2%nat, 3%nat => IHit (mkPoint 0 10) 1 0
  | 0%nat, 3%nat => IHit (mkPoint 0 0) 0 1
  | 4%nat, 5%nat => IHit (mkPoint 7 3) 1 0
  | 5%nat, 6%nat => IHit (mkPoint 7 7) 1 0
  | 6%nat, 7%nat => IHit (mkPoint 3 7) 1 0
  | 4%nat, 7%nat => IHit (mkPoint 3 3) 0 1
  | _, _ => IEmpty
  end.

Definition linear_donut_pairs : list (nat * nat) :=
  [(0,1)%nat;(0,2)%nat;(0,3)%nat;(0,4)%nat;(0,5)%nat;(0,6)%nat;(0,7)%nat;
   (1,2)%nat;(1,3)%nat;(1,4)%nat;(1,5)%nat;(1,6)%nat;(1,7)%nat;
   (2,3)%nat;(2,4)%nat;(2,5)%nat;(2,6)%nat;(2,7)%nat;
   (3,4)%nat;(3,5)%nat;(3,6)%nat;(3,7)%nat;
   (4,5)%nat;(4,6)%nat;(4,7)%nat;
   (5,6)%nat;(5,7)%nat;
   (6,7)%nat].

Lemma linear_donut_no_arc :
  Forall (fun e => egg_class (MkChord e) = EggChord /\ egg_class (MkChord e) <> EggCircularArc)
         linear_donut_bag.
Proof. repeat (apply Forall_cons); try apply Forall_nil. all: split; [reflexivity | discriminate]. Qed.

Lemma linear_donut_pairs_count : length linear_donut_pairs = 28%nat.
Proof. reflexivity. Qed.

(* Empty: an axis-aligned coordinate of one edge is pinned outside the
   coordinate range of the other. *)
Ltac linear_donut_empty :=
  intros [X [[t [Ht0 [Ht1 [Hx Hy]]]] [s [Hs0 [Hs1 [Hx' Hy']]]]]];
  cbn [px py ce_p0 ce_p1] in *; lra.

(* Hit at a shared corner: both on_chord at t ∈ {0,1}. *)
Ltac linear_donut_hit :=
  unfold on_chord, chord_eval; cbn [px py ce_p0 ce_p1];
  split; (split; [split; lra | apply (f_equal2 mkPoint); lra]).

(* WITNESS {"claimId":"0007-linear-donut-bag","topic":"overlay","lemma":"linear_donut_pairs_classified","title":"linear donut bag (eight MkChord, no EggCircularArc): all 28 unordered pairs of the square shell + square hole chords are Hit or Empty by host I_ok on MkChord x MkChord, named per pair by linear_donut_verdict; no Decline; no pair uses pairwise_nodable_shadow; T3 chord x arc fixture is not a member","file":"theories/SheetHenDonutBag.v","witness":"0007-linear-donut-bag","board":"ADR-0007"} *)
Theorem linear_donut_pairs_classified :
  Forall (fun ij => I_ok (MkChord (linear_donut_egg (fst ij))) (MkChord (linear_donut_egg (snd ij)))
                         (linear_donut_verdict (fst ij) (snd ij)))
         linear_donut_pairs.
Proof.
  unfold linear_donut_pairs. repeat (apply Forall_cons); try apply Forall_nil.
  all: unfold linear_donut_egg, linear_donut_bag, linear_donut_verdict, I_ok; cbn [nth fst snd].
  all: unfold s0, s1, s2, s3, h0, h1, h2, h3.
  all: first [ linear_donut_hit | linear_donut_empty ].
Qed.

Lemma linear_donut_no_decline :
  Forall (fun ij => linear_donut_verdict (fst ij) (snd ij) <> IDecline) linear_donut_pairs.
Proof. unfold linear_donut_pairs. repeat (apply Forall_cons); try apply Forall_nil. all: discriminate. Qed.

(* -------------------------------------------------------------------------- *)
(* §3  T5: ρ on this bag — every Hit is at a corner, width is constant.       *)
(* -------------------------------------------------------------------------- *)

Definition corner_hit (o : IResult) : Prop :=
  match o with
  | IHit _ ti tj => (ti = 0 \/ ti = 1) /\ (tj = 0 \/ tj = 1)
  | IEmpty => True
  | IDecline => False
  end.

(* WITNESS {"claimId":"0007-linear-donut-rho","topic":"overlay","lemma":"linear_donut_noded_on_S","title":"rho on the linear donut bag: every pair verdict is Empty or a Hit at parameters in {0,1}; already noded; corner shares only","file":"theories/SheetHenDonutBag.v","witness":"0007-linear-donut-bag","board":"ADR-0007"} *)
Theorem linear_donut_noded_on_S :
  Forall (fun ij => corner_hit (linear_donut_verdict (fst ij) (snd ij))) linear_donut_pairs.
Proof.
  unfold linear_donut_pairs. repeat (apply Forall_cons); try apply Forall_nil.
  all: cbn [linear_donut_verdict fst snd corner_hit]; try exact I.
  all: split; solve [left; lra | right; lra].
Qed.

(* A corner split leaves one leftover of the parent's full width and one of
   width 0: no strict decrease, and nothing to node. *)
Lemma corner_split_width_constant :
  forall t, (t = 0 \/ t = 1) ->
    leftover_width 0 t + leftover_width t 1 = leftover_width 0 1
    /\ (leftover_width 0 t = leftover_width 0 1 \/ leftover_width t 1 = leftover_width 0 1).
Proof.
  intros t [H | H]; subst; unfold leftover_width.
  - rewrite Rminus_0_r, Rabs_R0, Rminus_0_r. split; [lra | right; reflexivity].
  - replace (1 - 0) with 1 by lra. rewrite Rminus_diag, Rabs_R0. split; [lra | left; reflexivity].
Qed.

(* T5 on the linear donut bag only: already noded; corner shares only; width
   conserved; does not discharge LeftoverBagTermArm. Not the bag loop. *)
(* WITNESS {"claimId":"0007-linear-donut-rho","topic":"overlay","lemma":"ticket_0007_linear_donut_rho_qed_or_qex","title":"rho on the linear donut bag only: already noded, corner shares only, width conserved (QED); or width does not drop on an interior Hit (QEX); discharged QED on the constant-and-already-noded arm; does not discharge LeftoverBagTermArm, which stays the Parks QEX","file":"theories/SheetHenDonutBag.v","witness":"0007-linear-donut-bag","board":"ADR-0007"} *)
Theorem ticket_0007_linear_donut_rho_qed_or_qex :
  (Forall (fun ij => corner_hit (linear_donut_verdict (fst ij) (snd ij))) linear_donut_pairs
   /\ (forall t, (t = 0 \/ t = 1) ->
         leftover_width 0 t + leftover_width t 1 = leftover_width 0 1
         /\ (leftover_width 0 t = leftover_width 0 1 \/ leftover_width t 1 = leftover_width 0 1))
   /\ cook_loop_status = LoopObligation
   /\ cook_loop_status <> LoopDischarged)
  \/
  (exists ij, In ij linear_donut_pairs /\ ~ corner_hit (linear_donut_verdict (fst ij) (snd ij))).
Proof.
  left.
  split; [exact linear_donut_noded_on_S |].
  split; [exact corner_split_width_constant |].
  split; [exact cook_loop_is_obligation | exact cook_loop_not_discharged].
Qed.

Print Assumptions linear_donut_pairs_classified.
Print Assumptions linear_donut_no_decline.
Print Assumptions linear_donut_noded_on_S.
Print Assumptions ticket_0007_linear_donut_rho_qed_or_qex.
