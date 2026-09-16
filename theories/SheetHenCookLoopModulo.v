(* ============================================================================
   NetTopologySuite.Proofs.SheetHenCookLoopModulo
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: Parks ρ modulo the named QEX
   (claimId 0007-rho-modulo-qex).

   Parks ρ (#759, SheetHenCookLoop.v, witness 0007-rho-bag-loop) stays
   QEX. Missing ctor LeftoverBagTermArm =
     leftover_quad_width_decreases
     ∧ leftover_quad_kiss_arm
     ∧ leftover_quad_share_mint_arm.
   Each conjunct uninhabited. cook_loop_status stays LoopObligation.
   This letter does not inhabit LeftoverBagTermArm and does not flip
   LoopDischarged.

   Constructive cook, given that hole:
     * leftover_span — one parent chord on [t0,t1]
     * leftover_egg — leftover_half of that span (𝓘 egg)
     * leftover_span_bag — frontier of unsplit leftover eggs
     * leftover_bag_step — pair of leftover eggs: interior 𝓘 Hit
       splits both, or Decline leaves the bag
     * leftover_bag_nstep — fuel of leftover_bag_step
   A successful Hit-split requires leftover_pair_step_ok (two distinct
   leftover eggs + leftover_egg_interior + I_ok IHit). Pairwise
   leftover_width decrease justifies each child; leftover_quad_width
   bag-sum stays conserved (not a measure). leftover_quad is one
   pairwise Hit-split of two parent leftover_spans. I.8 leftovers_ab
   = leftovers_ba is reused as packaging, not reminted as bag
   Discharge. No densify: a caller-chosen interior of one span is
   not a leftover-pair Hit.

   Kiss / ShareOne / MintTwo stay the QEX arms (CRV-TOUCH / identity).
   They are not leftover_bag_step constructors.

   QED: leftover-pair Hit-split / Decline step; leftover_quad as
   one pair Hit; n-step cook on the locked crossing.
   QEX: LeftoverBagTermArm / LoopObligation restated unchanged.

   Honesty fences:
     Do not fake LoopDischarged. Do not remint I.8 / pairwise as bag
     discharge. Do not remint leftover_quad_width as a bag measure.
     Do not remint CircGamma / ι / mixed_joint_params / first_cook
     expand / Multi bags as ρ. Host CircGamma is CircGammaDischarged
     (MkCirc). First cook stays chord–chord. Not a CRV-TOUCH kiss
     procedure.

   WITNESS topic: overlay · claimId: 0007-rho-modulo-qex
   witness: 0007-rho-modulo-qex
   board: ADR-0007
   3-axiom host. No Axiom / Parameter / stub.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra Arith.
From NTS.Proofs Require Import Distance SheetHenCook SheetHenCookLoop.
Local Open Scope R_scope.

(* WITNESS: campaign=rho rung=modulo-qex claim=0007-rho-modulo-qex
   file=theories/SheetHenCookLoopModulo.v
   kind=QED-modulo-named-park
   park=LeftoverBagTermArm
   not=LoopDischarged,leftover_quad_width-measure,I.8-bag-Discharge
   not=CRV-TOUCH,CircGamma-remint,Multi-bags,first-cook-expand,densify *)

(* -------------------------------------------------------------------------- *)
(* Leftover span: one parent chord restricted to [t0, t1].                    *)
(* leftover_egg is that leftover as an 𝓘 chord egg (leftover_half).           *)
(* -------------------------------------------------------------------------- *)

Record leftover_span : Type := mkLeftoverSpan {
  ls_parent : ChordEgg;
  ls_t0 : R;
  ls_t1 : R
}.

Definition leftover_span_width (s : leftover_span) : R :=
  leftover_width (ls_t0 s) (ls_t1 s).

Definition leftover_span_ok (s : leftover_span) : Prop :=
  ls_t0 s < ls_t1 s.

(* Local leftover-egg parameter. 𝓘 Hit on leftover eggs uses this. *)
Definition leftover_egg_interior (u : R) : Prop :=
  0 < u < 1.

Definition leftover_span_parent (c : ChordEgg) : leftover_span :=
  mkLeftoverSpan c 0 1.

Definition leftover_egg (s : leftover_span) : ChordEgg :=
  leftover_half (ls_parent s) (ls_t0 s) (ls_t1 s).

(* Local leftover parameter u ∈ (0,1) maps to the parent interval. *)
Definition leftover_span_at (s : leftover_span) (u : R) : R :=
  ls_t0 s + u * (ls_t1 s - ls_t0 s).

Definition leftover_span_lo (s : leftover_span) (u : R) : leftover_span :=
  mkLeftoverSpan (ls_parent s) (ls_t0 s) (leftover_span_at s u).

Definition leftover_span_hi (s : leftover_span) (u : R) : leftover_span :=
  mkLeftoverSpan (ls_parent s) (leftover_span_at s u) (ls_t1 s).

Lemma leftover_half_parent :
  forall c, leftover_half c 0 1 = c.
Proof.
  intros [p0 p1].
  unfold leftover_half.
  rewrite chord_eval_at_0, chord_eval_at_1.
  reflexivity.
Qed.

Lemma leftover_egg_parent :
  forall c, leftover_egg (leftover_span_parent c) = c.
Proof.
  intros c.
  unfold leftover_egg, leftover_span_parent.
  simpl.
  apply leftover_half_parent.
Qed.

Lemma leftover_span_parent_ok :
  forall c, leftover_span_ok (leftover_span_parent c).
Proof.
  intros c.
  unfold leftover_span_ok, leftover_span_parent.
  simpl.
  lra.
Qed.

Lemma leftover_span_parent_width :
  forall c, leftover_span_width (leftover_span_parent c) = 1.
Proof.
  intros c.
  unfold leftover_span_parent, leftover_span_width.
  exact leftover_width_parent.
Qed.

Lemma leftover_span_parent_at :
  forall c u, leftover_span_at (leftover_span_parent c) u = u.
Proof.
  intros c u.
  unfold leftover_span_at, leftover_span_parent.
  simpl.
  ring.
Qed.

(* Pairwise leftover_width decrease on one leftover egg, under a
   leftover-egg interior parameter. Not leftover_quad_width_decreases. *)
Lemma leftover_span_split_width :
  forall s u,
    leftover_span_ok s ->
    leftover_egg_interior u ->
    leftover_span_width (leftover_span_lo s u)
      + leftover_span_width (leftover_span_hi s u)
      = leftover_span_width s /\
    leftover_span_width (leftover_span_lo s u)
      < leftover_span_width s /\
    leftover_span_width (leftover_span_hi s u)
      < leftover_span_width s.
Proof.
  intros [c t0 t1] u Hok [Hlo Hhi].
  unfold leftover_span_ok in Hok.
  simpl in Hok.
  unfold leftover_span_lo, leftover_span_hi, leftover_span_at,
         leftover_span_width, leftover_width.
  simpl.
  assert (H0 : 0 <= u * (t1 - t0)) by (apply Rmult_le_pos; lra).
  assert (H1 : 0 <= (1 - u) * (t1 - t0)) by (apply Rmult_le_pos; lra).
  assert (H2 : 0 <= t1 - t0) by lra.
  replace (t0 + u * (t1 - t0) - t0) with (u * (t1 - t0)) by ring.
  replace (t1 - (t0 + u * (t1 - t0))) with ((1 - u) * (t1 - t0)) by ring.
  rewrite (Rabs_pos_eq (u * (t1 - t0)) H0).
  rewrite (Rabs_pos_eq ((1 - u) * (t1 - t0)) H1).
  rewrite (Rabs_pos_eq (t1 - t0) H2).
  split; [ring|].
  split.
  - rewrite <- (Rmult_1_l (t1 - t0)) at 2.
    apply Rmult_lt_compat_r; lra.
  - rewrite <- (Rmult_1_l (t1 - t0)) at 2.
    apply Rmult_lt_compat_r; lra.
Qed.

Lemma leftover_span_parent_split_recovers_pairwise :
  forall u,
    leftover_egg_interior u ->
    leftover_span_width (leftover_span_lo (leftover_span_parent diag_ab) u)
      < leftover_span_width (leftover_span_parent diag_ab) /\
    leftover_span_width (leftover_span_hi (leftover_span_parent diag_ab) u)
      < leftover_span_width (leftover_span_parent diag_ab).
Proof.
  intros u Hu.
  destruct (leftover_span_split_width (leftover_span_parent diag_ab) u
              (leftover_span_parent_ok diag_ab) Hu) as [_ Hch].
  exact Hch.
Qed.

(* -------------------------------------------------------------------------- *)
(* leftover_quad is one pairwise Hit-split of two parent leftover_spans.      *)
(* I.8 leftovers_ab = leftovers_ba is packaging, not bag Discharge.           *)
(* -------------------------------------------------------------------------- *)

Inductive leftover_span_bag : Type :=
| LBagNil
| LBagCons (s : leftover_span) (rest : leftover_span_bag).

Fixpoint lbag_count (b : leftover_span_bag) : nat :=
  match b with
  | LBagNil => 0
  | LBagCons _ r => S (lbag_count r)
  end.

Fixpoint lbag_sum (b : leftover_span_bag) : R :=
  match b with
  | LBagNil => 0
  | LBagCons s r => leftover_span_width s + lbag_sum r
  end.

Definition leftover_quad_as_bag (c1 c2 : ChordEgg) (ti tj : R)
  : leftover_span_bag :=
  LBagCons (mkLeftoverSpan c1 0 ti)
    (LBagCons (mkLeftoverSpan c1 ti 1)
      (LBagCons (mkLeftoverSpan c2 0 tj)
        (LBagCons (mkLeftoverSpan c2 tj 1) LBagNil))).

Lemma leftover_quad_as_bag_count :
  forall c1 c2 ti tj,
    lbag_count (leftover_quad_as_bag c1 c2 ti tj) = 4%nat.
Proof.
  intros c1 c2 ti tj.
  reflexivity.
Qed.

Lemma leftover_quad_as_bag_sum :
  forall c1 c2 ti tj,
    lbag_sum (leftover_quad_as_bag c1 c2 ti tj) = leftover_quad_width ti tj.
Proof.
  intros c1 c2 ti tj.
  unfold leftover_quad_as_bag, leftover_quad_width, leftover_span_width.
  simpl.
  rewrite Rplus_0_r.
  rewrite <- Rplus_assoc.
  rewrite <- Rplus_assoc.
  reflexivity.
Qed.

Lemma leftover_quad_as_bag_is_one_hit :
  forall c1 c2 ti tj,
    leftovers_ab c1 c2 ti tj =
      (leftover_egg (mkLeftoverSpan c1 0 ti),
       leftover_egg (mkLeftoverSpan c1 ti 1),
       leftover_egg (mkLeftoverSpan c2 0 tj),
       leftover_egg (mkLeftoverSpan c2 tj 1)) /\
    leftovers_ab c1 c2 ti tj = leftovers_ba c1 c2 ti tj /\
    lbag_count (leftover_quad_as_bag c1 c2 ti tj) = 4%nat.
Proof.
  intros c1 c2 ti tj.
  split; [reflexivity|].
  split; [apply split_step_confluent|].
  reflexivity.
Qed.

Lemma leftover_quad_as_bag_sum_conserved :
  forall c1 c2 ti tj,
    0 < ti < 1 ->
    0 < tj < 1 ->
    lbag_sum (leftover_quad_as_bag c1 c2 ti tj) =
    leftover_width 0 1 + leftover_width 0 1.
Proof.
  intros c1 c2 ti tj Hti Htj.
  rewrite leftover_quad_as_bag_sum.
  apply leftover_quad_width_conserved; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Pair Hit on two leftover eggs, or Decline and leave the bag.               *)
(* leftover_pair_step_ok is required for a successful replace/split.          *)
(* -------------------------------------------------------------------------- *)

Definition leftover_pair_hit (a b : leftover_span) (p : Point) (ua ub : R)
  : Prop :=
  leftover_span_ok a /\
  leftover_span_ok b /\
  leftover_egg_interior ua /\
  leftover_egg_interior ub /\
  I_ok (MkChord (leftover_egg a)) (MkChord (leftover_egg b)) (IHit p ua ub).

Fixpoint lbag_nth (b : leftover_span_bag) (n : nat) : option leftover_span :=
  match b, n with
  | LBagNil, _ => None
  | LBagCons s _, O => Some s
  | LBagCons _ r, S n' => lbag_nth r n'
  end.

Fixpoint lbag_remove (b : leftover_span_bag) (n : nat) : leftover_span_bag :=
  match b, n with
  | LBagNil, _ => LBagNil
  | LBagCons _ r, O => r
  | LBagCons s r, S n' => LBagCons s (lbag_remove r n')
  end.

Definition lbag_remove_two (b : leftover_span_bag) (i j : nat)
  : leftover_span_bag :=
  if Nat.ltb i j
  then lbag_remove (lbag_remove b j) i
  else lbag_remove (lbag_remove b i) j.

Definition lbag_pair_replace (b : leftover_span_bag) (i j : nat) (ua ub : R)
  : option leftover_span_bag :=
  match lbag_nth b i, lbag_nth b j with
  | Some a, Some bsp =>
      if Nat.eqb i j then None
      else
        Some
          (LBagCons (leftover_span_lo a ua)
            (LBagCons (leftover_span_hi a ua)
              (LBagCons (leftover_span_lo bsp ub)
                (LBagCons (leftover_span_hi bsp ub)
                  (lbag_remove_two b i j)))))
  | _, _ => None
  end.

Definition leftover_pair_step_ok (b : leftover_span_bag) (i j : nat)
  (p : Point) (ua ub : R) : Prop :=
  exists a bsp,
    lbag_nth b i = Some a /\
    lbag_nth b j = Some bsp /\
    i <> j /\
    leftover_pair_hit a bsp p ua ub.

Definition leftover_pair_decline (b : leftover_span_bag) (i j : nat) : Prop :=
  exists a bsp,
    lbag_nth b i = Some a /\
    lbag_nth b j = Some bsp /\
    i <> j /\
    (forall p ua ub, ~ leftover_pair_hit a bsp p ua ub).

Lemma leftover_pair_replace_some :
  forall b i j p ua ub,
    leftover_pair_step_ok b i j p ua ub ->
    exists b', lbag_pair_replace b i j ua ub = Some b'.
Proof.
  intros b i j p ua ub [a [bsp [Ha [Hb [Hne _]]]]].
  unfold lbag_pair_replace.
  rewrite Ha, Hb.
  apply Nat.eqb_neq in Hne.
  rewrite Hne.
  eexists.
  reflexivity.
Qed.

Lemma lbag_sum_remove :
  forall b n s,
    lbag_nth b n = Some s ->
    lbag_sum (lbag_remove b n) + leftover_span_width s = lbag_sum b.
Proof.
  induction b as [|s0 rest IH]; intros n s Hnth.
  - discriminate.
  - destruct n as [|n'].
    + simpl in Hnth.
      inversion Hnth.
      subst s0.
      simpl.
      rewrite Rplus_comm.
      reflexivity.
    + simpl in Hnth.
      simpl.
      rewrite Rplus_assoc.
      rewrite (IH n' s Hnth).
      reflexivity.
Qed.

Lemma lbag_nth_remove_before :
  forall b i j a,
    (i < j)%nat ->
    lbag_nth b i = Some a ->
    lbag_nth (lbag_remove b j) i = Some a.
Proof.
  induction b as [|s0 rest IH]; intros i j a Hij Hnth.
  - discriminate.
  - destruct j as [|j'].
    + inversion Hij.
    + destruct i as [|i'].
      * simpl in Hnth.
        inversion Hnth.
        subst s0.
        reflexivity.
      * simpl in Hnth.
        apply Nat.succ_lt_mono in Hij.
        simpl.
        apply (IH i' j' a Hij Hnth).
Qed.

Lemma lbag_pair_replace_sum :
  forall b i j p ua ub b',
    leftover_pair_step_ok b i j p ua ub ->
    lbag_pair_replace b i j ua ub = Some b' ->
    lbag_sum b' = lbag_sum b.
Proof.
  intros b i j p ua ub b' [a [bsp [Ha [Hb [Hne Hhit]]]]] Hrep.
  unfold lbag_pair_replace in Hrep.
  rewrite Ha, Hb in Hrep.
  assert (Hneqb : Nat.eqb i j = false) by (apply Nat.eqb_neq; exact Hne).
  rewrite Hneqb in Hrep.
  inversion Hrep.
  subst b'.
  destruct Hhit as [Hoka [Hokb [Hua [Hub _]]]].
  destruct (leftover_span_split_width a ua Hoka Hua) as [Hsuma _].
  destruct (leftover_span_split_width bsp ub Hokb Hub) as [Hsumb _].
  cbn [lbag_sum].
  match goal with
  | |- ?LoA + (?HiA + (?LoB + (?HiB + ?Rest))) = _ =>
      replace (LoA + (HiA + (LoB + (HiB + Rest))))
        with ((LoA + HiA) + ((LoB + HiB) + Rest)) by ring
  end.
  rewrite Hsuma, Hsumb.
  unfold lbag_remove_two.
  destruct (Nat.ltb i j) eqn:Hlt.
  - apply Nat.ltb_lt in Hlt.
    assert (Hai : lbag_nth (lbag_remove b j) i = Some a).
    { apply lbag_nth_remove_before; assumption. }
    pose proof (lbag_sum_remove (lbag_remove b j) i a Hai) as Hra.
    pose proof (lbag_sum_remove b j bsp Hb) as Hrb.
    lra.
  - apply Nat.ltb_ge in Hlt.
    assert (Hij : (j < i)%nat).
    { apply Nat.le_neq.
      split; [exact Hlt|].
      apply not_eq_sym.
      exact Hne. }
    assert (Hbj : lbag_nth (lbag_remove b i) j = Some bsp).
    { apply lbag_nth_remove_before; assumption. }
    pose proof (lbag_sum_remove (lbag_remove b i) j bsp Hbj) as Hrb.
    pose proof (lbag_sum_remove b i a Ha) as Hra.
    lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* leftover_bag_step: Hit-split both leftover eggs, or Decline (identity).    *)
(* Fuel is leftover_bag_nstep — not LoopDischarged.                           *)
(* -------------------------------------------------------------------------- *)

Inductive leftover_bag_step : leftover_span_bag -> leftover_span_bag -> Prop :=
| LStepHit : forall b b' i j p ua ub,
    leftover_pair_step_ok b i j p ua ub ->
    lbag_pair_replace b i j ua ub = Some b' ->
    leftover_bag_step b b'
| LStepDecline : forall b i j,
    leftover_pair_decline b i j ->
    leftover_bag_step b b.

Inductive leftover_bag_nstep
  : nat -> leftover_span_bag -> leftover_span_bag -> Prop :=
| LNstepZ : forall b, leftover_bag_nstep 0 b b
| LNstepS : forall n b b' b'',
    leftover_bag_step b b' ->
    leftover_bag_nstep n b' b'' ->
    leftover_bag_nstep (S n) b b''.

Definition leftover_bag_cook_fuel (n : nat)
  (b b' : leftover_span_bag) : Prop :=
  leftover_bag_nstep n b b'.

Lemma leftover_bag_cook_fuel_zero :
  forall b, leftover_bag_cook_fuel 0 b b.
Proof.
  intros b.
  apply LNstepZ.
Qed.

Lemma leftover_bag_step_hit_sum :
  forall b b',
    leftover_bag_step b b' ->
    (exists i j p ua ub,
       leftover_pair_step_ok b i j p ua ub /\
       lbag_pair_replace b i j ua ub = Some b') ->
    lbag_sum b' = lbag_sum b.
Proof.
  intros b b' _ [i [j [p [ua [ub [Hok Hrep]]]]]].
  eapply lbag_pair_replace_sum; eassumption.
Qed.

Lemma leftover_bag_step_decline_id :
  forall b i j,
    leftover_pair_decline b i j ->
    leftover_bag_step b b /\
    lbag_sum b = lbag_sum b /\
    lbag_count b = lbag_count b.
Proof.
  intros b i j Hd.
  split; [apply (LStepDecline b i j Hd)|].
  split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked crossing: two parent leftover eggs Hit-split to leftover_quad.      *)
(* A leftover-quad pair that only meets at the join Declines.                 *)
(* -------------------------------------------------------------------------- *)

Definition locked_parent_bag : leftover_span_bag :=
  LBagCons (leftover_span_parent diag_ab)
    (LBagCons (leftover_span_parent diag_cd) LBagNil).

Definition locked_quad_bag : leftover_span_bag :=
  leftover_quad_as_bag diag_ab diag_cd (1 / 2) (1 / 2).

Lemma locked_parent_pair_hit :
  leftover_pair_hit
    (leftover_span_parent diag_ab)
    (leftover_span_parent diag_cd)
    cross_pt (1 / 2) (1 / 2).
Proof.
  unfold leftover_pair_hit.
  split; [apply leftover_span_parent_ok|].
  split; [apply leftover_span_parent_ok|].
  split; [unfold leftover_egg_interior; lra|].
  split; [unfold leftover_egg_interior; lra|].
  rewrite leftover_egg_parent.
  rewrite leftover_egg_parent.
  exact crossing_I_ok.
Qed.

Lemma locked_parent_step_ok :
  leftover_pair_step_ok locked_parent_bag 0 1
    cross_pt (1 / 2) (1 / 2).
Proof.
  exists (leftover_span_parent diag_ab), (leftover_span_parent diag_cd).
  split; [reflexivity|].
  split; [reflexivity|].
  split; [discriminate|].
  exact locked_parent_pair_hit.
Qed.

Lemma locked_parent_replace :
  lbag_pair_replace locked_parent_bag 0 1 (1 / 2) (1 / 2) =
  Some locked_quad_bag.
Proof.
  unfold lbag_pair_replace, locked_parent_bag, locked_quad_bag,
         leftover_quad_as_bag, leftover_span_lo, leftover_span_hi,
         lbag_remove_two.
  simpl.
  rewrite !leftover_span_parent_at.
  reflexivity.
Qed.

Lemma locked_hit_step :
  leftover_bag_step locked_parent_bag locked_quad_bag.
Proof.
  apply (LStepHit locked_parent_bag locked_quad_bag 0 1
           cross_pt (1 / 2) (1 / 2)).
  - exact locked_parent_step_ok.
  - exact locked_parent_replace.
Qed.

Lemma locked_hit_nstep :
  leftover_bag_cook_fuel 1 locked_parent_bag locked_quad_bag.
Proof.
  unfold leftover_bag_cook_fuel.
  apply (LNstepS 0 locked_parent_bag locked_quad_bag locked_quad_bag).
  - exact locked_hit_step.
  - apply LNstepZ.
Qed.

Lemma locked_hit_sum :
  lbag_sum locked_quad_bag = lbag_sum locked_parent_bag.
Proof.
  apply (lbag_pair_replace_sum locked_parent_bag 0 1
           cross_pt (1 / 2) (1 / 2) locked_quad_bag).
  - exact locked_parent_step_ok.
  - exact locked_parent_replace.
Qed.

Lemma locked_hit_not_quad_measure :
  lbag_sum locked_quad_bag = leftover_quad_width (1 / 2) (1 / 2) /\
  leftover_quad_width (1 / 2) (1 / 2) = leftover_width 0 1 + leftover_width 0 1.
Proof.
  split.
  - apply leftover_quad_as_bag_sum.
  - apply leftover_quad_width_conserved; lra.
Qed.

Lemma locked_A_lo_egg :
  leftover_egg (mkLeftoverSpan diag_ab 0 (1 / 2)) =
  mkChordEgg (mkPoint 0 0) (mkPoint 1 1).
Proof.
  unfold leftover_egg, leftover_half, diag_ab, chord_eval.
  simpl.
  apply (f_equal2 mkChordEgg); apply (f_equal2 mkPoint); field.
Qed.

Lemma locked_B_lo_egg :
  leftover_egg (mkLeftoverSpan diag_cd 0 (1 / 2)) =
  mkChordEgg (mkPoint 0 2) (mkPoint 1 1).
Proof.
  unfold leftover_egg, leftover_half, diag_cd, chord_eval.
  simpl.
  apply (f_equal2 mkChordEgg); apply (f_equal2 mkPoint); field.
Qed.

Lemma locked_quad_pair_no_interior_hit :
  forall p ua ub,
    ~ leftover_pair_hit
        (mkLeftoverSpan diag_ab 0 (1 / 2))
        (mkLeftoverSpan diag_cd 0 (1 / 2))
        p ua ub.
Proof.
  intros p ua ub [Hoka [Hokb [Hua [Hub Hok]]]].
  unfold leftover_egg_interior in Hua, Hub.
  rewrite locked_A_lo_egg, locked_B_lo_egg in Hok.
  unfold I_ok, on_chord, chord_eval in Hok.
  destruct Hok as [[_ Ha] [_ Hb]].
  simpl in Ha, Hb.
  rewrite Ha in Hb.
  inversion Hb.
  lra.
Qed.

Lemma locked_quad_decline :
  leftover_pair_decline locked_quad_bag 0 2.
Proof.
  exists (mkLeftoverSpan diag_ab 0 (1 / 2)),
         (mkLeftoverSpan diag_cd 0 (1 / 2)).
  split; [reflexivity|].
  split; [reflexivity|].
  split; [discriminate|].
  exact locked_quad_pair_no_interior_hit.
Qed.

Lemma locked_decline_step :
  leftover_bag_step locked_quad_bag locked_quad_bag.
Proof.
  apply (LStepDecline locked_quad_bag 0 2).
  exact locked_quad_decline.
Qed.

Lemma locked_decline_nstep :
  leftover_bag_cook_fuel 1 locked_quad_bag locked_quad_bag.
Proof.
  unfold leftover_bag_cook_fuel.
  apply (LNstepS 0 locked_quad_bag locked_quad_bag locked_quad_bag).
  - exact locked_decline_step.
  - apply LNstepZ.
Qed.

Lemma leftover_modulo_park_unchanged :
  cook_loop_status = LoopObligation /\
  cook_loop_status <> LoopDischarged /\
  ~ leftover_bag_term_arm /\
  LeftoverBagTermArm = leftover_bag_term_arm /\
  leftover_bag_term_arm =
    (leftover_quad_width_decreases
     /\ leftover_quad_kiss_arm
     /\ leftover_quad_share_mint_arm).
Proof.
  split; [exact cook_loop_is_obligation|].
  split; [exact cook_loop_not_discharged|].
  split; [exact leftover_bag_term_arm_missing|].
  split; [reflexivity|].
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-rho-modulo-qex","topic":"overlay","lemma":"ticket_0007_rho_modulo_step_qed_or_qex","title":"rho modulo QEX: leftover-pair interior Hit-split strictly decreases each child leftover_width (QED) or leftover_quad_width_decreases (QEX); discharged QED; pairwise width on leftover eggs, not leftover_quad bag-sum; kiss/share/mint stay QEX arms","file":"theories/SheetHenCookLoopModulo.v","witness":"0007-rho-modulo-qex","board":"ADR-0007"} *)
Theorem ticket_0007_rho_modulo_step_qed_or_qex :
  (forall s u,
     leftover_span_ok s ->
     leftover_egg_interior u ->
     leftover_span_width (leftover_span_lo s u)
       + leftover_span_width (leftover_span_hi s u)
       = leftover_span_width s /\
     leftover_span_width (leftover_span_lo s u)
       < leftover_span_width s /\
     leftover_span_width (leftover_span_hi s u)
       < leftover_span_width s)
  \/ leftover_quad_width_decreases.
Proof.
  left.
  exact leftover_span_split_width.
Qed.

(* WITNESS {"claimId":"0007-rho-modulo-qex","topic":"overlay","lemma":"ticket_0007_rho_modulo_bag_qed_or_qex","title":"rho modulo QEX: leftover_quad is one leftover-pair Hit of two parent leftover_spans and leftovers_ab equals leftovers_ba (QED) or leftover_quad_width_decreases (QEX); discharged QED; bag-sum is leftover_quad_width, not a measure; I.8 reused as packaging not reminted","file":"theories/SheetHenCookLoopModulo.v","witness":"0007-rho-modulo-qex","board":"ADR-0007"} *)
Theorem ticket_0007_rho_modulo_bag_qed_or_qex :
  (leftover_bag_cook_fuel 1 locked_parent_bag locked_quad_bag /\
   leftover_pair_step_ok locked_parent_bag 0 1
     cross_pt (1 / 2) (1 / 2) /\
   leftovers_ab diag_ab diag_cd (1 / 2) (1 / 2) =
     leftovers_ba diag_ab diag_cd (1 / 2) (1 / 2) /\
   lbag_count locked_quad_bag = 4%nat /\
   lbag_sum locked_quad_bag = leftover_quad_width (1 / 2) (1 / 2))
  \/ leftover_quad_width_decreases.
Proof.
  left.
  split; [exact locked_hit_nstep|].
  split; [exact locked_parent_step_ok|].
  split; [apply split_step_confluent|].
  split; [reflexivity|].
  apply leftover_quad_as_bag_sum.
Qed.

(* WITNESS {"claimId":"0007-rho-modulo-qex","topic":"overlay","lemma":"ticket_0007_rho_modulo_iter_qed_or_qex","title":"rho modulo QEX: leftover-pair cook Hit-splits the locked parent bag and Declines on a leftover-quad join pair (QED) or cook_loop is LoopDischarged (QEX); discharged QED; leftover_pair_step_ok required for Hit; Decline leaves the bag; LoopObligation stands","file":"theories/SheetHenCookLoopModulo.v","witness":"0007-rho-modulo-qex","board":"ADR-0007"} *)
Theorem ticket_0007_rho_modulo_iter_qed_or_qex :
  (leftover_bag_cook_fuel 0 locked_parent_bag locked_parent_bag /\
   leftover_bag_cook_fuel 1 locked_parent_bag locked_quad_bag /\
   leftover_pair_step_ok locked_parent_bag 0 1
     cross_pt (1 / 2) (1 / 2) /\
   leftover_bag_cook_fuel 1 locked_quad_bag locked_quad_bag /\
   leftover_pair_decline locked_quad_bag 0 2 /\
   lbag_sum locked_quad_bag = lbag_sum locked_parent_bag /\
   cook_loop_status = LoopObligation /\
   cook_loop_status <> LoopDischarged)
  \/ cook_loop_status = LoopDischarged.
Proof.
  left.
  split; [apply leftover_bag_cook_fuel_zero|].
  split; [exact locked_hit_nstep|].
  split; [exact locked_parent_step_ok|].
  split; [exact locked_decline_nstep|].
  split; [exact locked_quad_decline|].
  split; [exact locked_hit_sum|].
  split; [exact cook_loop_is_obligation|].
  exact cook_loop_not_discharged.
Qed.

(* WITNESS {"claimId":"0007-rho-modulo-qex","topic":"overlay","lemma":"ticket_0007_rho_modulo_park_qed_or_qex","title":"rho modulo QEX: LeftoverBagTermArm inhabits leftover_quad_width_decreases and kiss/share/mint leftover-quad rewrites (QED) or that ctor stays missing and cook_loop stays LoopObligation (QEX); discharged QEX; same LeftoverBagTermArm hole as 0007-rho-bag-loop; do not fake LoopDischarged","file":"theories/SheetHenCookLoopModulo.v","witness":"0007-rho-modulo-qex","board":"ADR-0007"} *)
Theorem ticket_0007_rho_modulo_park_qed_or_qex :
  cook_loop_ctor_inhabits CookLoopBagTerm
  \/
  (cook_loop_status = LoopObligation
   /\ cook_loop_status <> LoopDischarged
   /\ ~ leftover_bag_term_arm
   /\ LeftoverBagTermArm = leftover_bag_term_arm
   /\ leftover_bag_term_arm =
        (leftover_quad_width_decreases
         /\ leftover_quad_kiss_arm
         /\ leftover_quad_share_mint_arm)
   /\ ~ leftover_quad_width_decreases
   /\ ~ leftover_quad_kiss_arm
   /\ ~ leftover_quad_share_mint_arm).
Proof.
  right.
  destruct leftover_modulo_park_unchanged as [Hob [Hnd [Hmiss [Heq Hdef]]]].
  split; [exact Hob|].
  split; [exact Hnd|].
  split; [exact Hmiss|].
  split; [exact Heq|].
  split; [exact Hdef|].
  split; [exact leftover_quad_width_does_not_decrease|].
  split; [exact leftover_quad_kiss_arm_missing|].
  exact leftover_quad_share_mint_arm_missing.
Qed.

Print Assumptions leftover_span_split_width.
Print Assumptions leftover_span_parent_split_recovers_pairwise.
Print Assumptions leftover_egg_parent.
Print Assumptions leftover_quad_as_bag_count.
Print Assumptions leftover_quad_as_bag_sum.
Print Assumptions leftover_quad_as_bag_is_one_hit.
Print Assumptions leftover_quad_as_bag_sum_conserved.
Print Assumptions leftover_pair_replace_some.
Print Assumptions lbag_pair_replace_sum.
Print Assumptions leftover_bag_cook_fuel_zero.
Print Assumptions locked_parent_pair_hit.
Print Assumptions locked_hit_nstep.
Print Assumptions locked_hit_sum.
Print Assumptions locked_hit_not_quad_measure.
Print Assumptions locked_quad_decline.
Print Assumptions locked_decline_nstep.
Print Assumptions leftover_modulo_park_unchanged.
Print Assumptions ticket_0007_rho_modulo_step_qed_or_qex.
Print Assumptions ticket_0007_rho_modulo_bag_qed_or_qex.
Print Assumptions ticket_0007_rho_modulo_iter_qed_or_qex.
Print Assumptions ticket_0007_rho_modulo_park_qed_or_qex.
