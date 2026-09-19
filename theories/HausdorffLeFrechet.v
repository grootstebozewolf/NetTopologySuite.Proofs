(* ============================================================================
   NetTopologySuite.Proofs.HausdorffLeFrechet
   ----------------------------------------------------------------------------
   #423 next honest slice: DISCRETE DIRECTED HAUSDORFF ≤ DISCRETE FRECHET
   on finite point lists (claimId 423-hausdorff-le-frechet).

   Huttenlocher-Klanderman-Rucklidge (IEEE PAMI 1993) eq (2) vs
   Eiter-Mannila (1994) / Meinert (arXiv:2404.05708) eq (1), squared
   convention (sqrt-free; max/min commute with monotone squaring).
   JTS/NTS DiscreteHausdorffDistance vs DiscreteFrechetDistance:

     h_sq(A,B)  = max_{a in A} min_{b in B} dist_sq a b
     dF_sq(A,B) = min over monotone couplings of the max pairwise leash.

   A coupling is a two-frogs walk (start on heads; advance frog 1,
   frog 2, or both; end on last stones).  Every such walk covers A and
   lands each A-stone on some B-stone, so the max-min is a lower bound
   on that walk's leash; the attained min-leash is therefore at least h.

   Proved here from the existing 423-a / 423-b surfaces (not reminted):
     (cover)     coupling_covers_A / coupling_pair_in_B
     (leash)     max_pair_dist_sq_ge
     (project)   coupling_projects_to_max_min
     (headline)  hausdorff_sq_le_frechet_sq
     (witness)   man_dog_frechet_dominates_hausdorff
                 stones A = [(0,0)] vs B = [(0,2);(3,0)]
                 dF_sq = 9 > 4 = directed_hausdorff_sq
                 (Claim423b lone-frog pin, lifted)

   ticket_423_hausdorff_le_frechet_qed_or_qex LEFT.
   Not: 423-a / 423-b remint; not densify ticket-10 line 2 (PR #812);
   Linearise.hausdorff_le is not used.

   WITNESS topic: metric · claimId: 423-hausdorff-le-frechet
   3-axiom (Stdlib Reals). No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance HausdorffDiscrete FrechetDiscrete.
Import ListNotations.
Open Scope R_scope.

(* WITNESS {"claimId":"423-hausdorff-le-frechet","topic":"metric","lemma":"hausdorff_sq_le_frechet_sq","title":"Discrete directed Hausdorff_sq is at most discrete Frechet_sq on nonempty finite point lists","file":"theories/HausdorffLeFrechet.v","witness":"423-hausdorff-le-frechet"} *)

(* -------------------------------------------------------------------------- *)
(* §1  A coupling covers every A-stone and lands it on a B-stone.             *)
(* -------------------------------------------------------------------------- *)

Lemma coupling_A_nonempty : forall A B c, coupling A B c -> A <> nil.
Proof. intros A B c H; destruct H; discriminate. Qed.

Lemma coupling_B_nonempty : forall A B c, coupling A B c -> B <> nil.
Proof. intros A B c H; destruct H; discriminate. Qed.

Lemma coupling_covers_A : forall A B c,
    coupling A B c -> forall a, In a A -> exists b, In (a, b) c.
Proof.
  intros A B c H. induction H; intros p Hin.
  - destruct Hin as [-> | []]. exists b. left. reflexivity.
  - destruct Hin as [-> | Hin].
    + exists b. left. reflexivity.
    + destruct (IHcoupling p Hin) as [b' Hb'].
      exists b'. right. exact Hb'.
  - destruct Hin as [-> | Hin].
    + exists b. left. reflexivity.
    + destruct (IHcoupling p Hin) as [b' Hb'].
      exists b'. right. exact Hb'.
  - destruct Hin as [-> | Hin].
    + exists b. left. reflexivity.
    + destruct (IHcoupling p Hin) as [b' Hb'].
      exists b'. right. exact Hb'.
Qed.

Lemma coupling_pair_in_B : forall A B c a b,
    coupling A B c -> In (a, b) c -> In b B.
Proof.
  intros A B c a0 b0 H Hin. induction H.
  - destruct Hin as [Heq | []]. inversion Heq. left. reflexivity.
  - destruct Hin as [Heq | Hin].
    + inversion Heq. left. reflexivity.
    + apply IHcoupling. exact Hin.
  - destruct Hin as [Heq | Hin].
    + inversion Heq. left. reflexivity.
    + right. apply IHcoupling. exact Hin.
  - destruct Hin as [Heq | Hin].
    + inversion Heq. left. reflexivity.
    + right. apply IHcoupling. exact Hin.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Every emitted pair is bounded by the coupling leash.                   *)
(* -------------------------------------------------------------------------- *)

Lemma max_pair_dist_sq_ge : forall c a b,
    In (a, b) c -> dist_sq a b <= max_pair_dist_sq c.
Proof.
  induction c as [| p c' IH]; intros a b Hin.
  - destruct Hin.
  - destruct p as [a0 b0].
    destruct Hin as [Heq | Hin].
    + inversion Heq; subst.
      destruct c' as [| p' c''].
      * apply Rle_refl.
      * cbn. apply Rmax_l.
    + destruct c' as [| p' c''].
      * destruct Hin.
      * cbn. eapply Rle_trans; [ apply IH; exact Hin | apply Rmax_r ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Projection: the max-min is a lower bound on every coupling leash.      *)
(* -------------------------------------------------------------------------- *)

Lemma coupling_projects_to_max_min : forall A B c,
    coupling A B c ->
    directed_hausdorff_sq A B <= max_pair_dist_sq c.
Proof.
  intros A B c Hc.
  assert (HA : A <> nil) by (eapply coupling_A_nonempty; exact Hc).
  destruct (ddh_attained A B HA) as [a [Ha Heq]].
  rewrite Heq.
  destruct (coupling_covers_A A B c Hc a Ha) as [b HinC].
  assert (Hb : In b B) by (eapply coupling_pair_in_B; [ exact Hc | exact HinC ]).
  eapply Rle_trans.
  - apply min_dist_sq_to_le. exact Hb.
  - apply max_pair_dist_sq_ge. exact HinC.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Headline: discrete directed Hausdorff_sq ≤ discrete Frechet_sq.        *)
(* -------------------------------------------------------------------------- *)

Theorem hausdorff_sq_le_frechet_sq : forall A B,
    A <> nil ->
    B <> nil ->
    directed_hausdorff_sq A B <= dF_sq A B.
Proof.
  intros A B HA HB.
  destruct (dF_attained A B HA HB) as [c [Hc Heq]].
  rewrite <- Heq.
  apply coupling_projects_to_max_min. exact Hc.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Locked man-dog / stones witness: Frechet strictly dominates.           *)
(*     Claim423b pin: lone frog on [(0,0)] must visit both stones             *)
(*     [(0,2);(3,0)], so dF_sq = 9 while directed Hausdorff_sq = 4.           *)
(* -------------------------------------------------------------------------- *)

Definition stones_A : list Point := [mkPoint 0 0].
Definition stones_B : list Point := [mkPoint 0 2; mkPoint 3 0].

Ltac pin_crunch :=
  unfold Rmax, Rmin;
  repeat match goal with
         | |- context [Rle_dec ?x ?y] => destruct (Rle_dec x y)
         end;
  lra.

Lemma stones_ddh_sq : directed_hausdorff_sq stones_A stones_B = 4.
Proof.
  unfold stones_A, stones_B. cbn. unfold dist_sq. cbn. pin_crunch.
Qed.

Lemma stones_dF_sq : dF_sq stones_A stones_B = 9.
Proof.
  unfold stones_A, stones_B. cbn. unfold dist_sq. cbn. pin_crunch.
Qed.

(* WITNESS {"claimId":"423-hausdorff-le-frechet","topic":"metric","lemma":"man_dog_frechet_dominates_hausdorff","title":"Locked man-dog / stones witness: dF_sq [(0,0)] [(0,2);(3,0)] = 9 > 4 = directed_hausdorff_sq","file":"theories/HausdorffLeFrechet.v","witness":"423-hausdorff-le-frechet"} *)
Theorem man_dog_frechet_dominates_hausdorff :
  directed_hausdorff_sq stones_A stones_B = 4 /\
  dF_sq stones_A stones_B = 9 /\
  directed_hausdorff_sq stones_A stones_B < dF_sq stones_A stones_B.
Proof.
  split; [ exact stones_ddh_sq | ].
  split; [ exact stones_dF_sq | ].
  rewrite stones_ddh_sq, stones_dF_sq. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Ticket stop.                                                           *)
(* -------------------------------------------------------------------------- *)

Inductive HausdorffLeFrechetPark : Type :=
| CouplingProjectsToMaxMin
| FrechetDominatesHausdorffGeneral.

Definition hausdorff_le_frechet_park_inhabits
  (_ : HausdorffLeFrechetPark) : Prop := False.

(* WITNESS {"claimId":"423-hausdorff-le-frechet","topic":"metric","lemma":"ticket_423_hausdorff_le_frechet_qed_or_qex","title":"#423 Hausdorff ≤ Frechet (discrete): directed_hausdorff_sq ≤ dF_sq on nonempty lists and the locked man-dog / stones witness 4 < 9 (QED); or CouplingProjectsToMaxMin / FrechetDominatesHausdorffGeneral stays a named missing constructor (QEX); discharged QED","file":"theories/HausdorffLeFrechet.v","witness":"423-hausdorff-le-frechet"} *)
Theorem ticket_423_hausdorff_le_frechet_qed_or_qex :
  ((forall A B : list Point,
      A <> nil -> B <> nil ->
      directed_hausdorff_sq A B <= dF_sq A B)
   /\ directed_hausdorff_sq stones_A stones_B = 4
   /\ dF_sq stones_A stones_B = 9
   /\ directed_hausdorff_sq stones_A stones_B < dF_sq stones_A stones_B)
  \/
  hausdorff_le_frechet_park_inhabits CouplingProjectsToMaxMin.
Proof.
  left.
  split; [ exact hausdorff_sq_le_frechet_sq | ].
  exact man_dog_frechet_dominates_hausdorff.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions hausdorff_sq_le_frechet_sq.
Print Assumptions man_dog_frechet_dominates_hausdorff.
Print Assumptions ticket_423_hausdorff_le_frechet_qed_or_qex.
