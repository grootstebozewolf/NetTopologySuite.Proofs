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
     * leftover_item — inductive leftover cook (Unsplit | HitSplit)
     * leftover_span_bag — frontier of unsplit spans
     * leftover_bag_cook_fuel — stepwise Hit-split iterator (fuel)
   Hit-split steps are justified by pairwise leftover_width decrease
   (interior_hit_splits_width on an arbitrary leftover, not on the
   conserved leftover_quad_width bag-sum). leftover_quad is one
   pairwise Hit-split packaged as two leftover_item trees / a 4-span
   frontier. I.8 leftovers_ab = leftovers_ba is reused, not reminted
   as bag Discharge.

   Kiss / ShareOne / MintTwo stay the QEX arms (CRV-TOUCH / identity).
   They are not leftover_item constructors and not leftover_width
   decrease.

   QED: pairwise Hit-split step; leftover_quad as inductive bag;
   fuel iterator on Hit-split only.
   QEX: LeftoverBagTermArm / LoopObligation restated unchanged.

   Honesty fences:
     Do not fake LoopDischarged. Do not remint I.8 / pairwise as bag
     discharge. Do not remint leftover_quad_width as a bag measure
     (frontier sum stays conserved). Do not remint CircGamma / ι /
     mixed_joint_params / first_cook expand / Multi bags as ρ.
     Host CircGamma is CircGammaDischarged (MkCirc). First cook stays
     chord–chord. Not a CRV-TOUCH kiss procedure.

   WITNESS topic: overlay · claimId: 0007-rho-modulo-qex
   witness: 0007-rho-modulo-qex
   board: ADR-0007
   3-axiom host. No Axiom / Parameter / stub.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance SheetHenCook SheetHenCookLoop.
Local Open Scope R_scope.

(* WITNESS: campaign=rho rung=modulo-qex claim=0007-rho-modulo-qex
   file=theories/SheetHenCookLoopModulo.v
   kind=QED-modulo-named-park
   park=LeftoverBagTermArm
   not=LoopDischarged,leftover_quad_width-measure,I.8-bag-Discharge
   not=CRV-TOUCH,CircGamma-remint,Multi-bags,first-cook-expand *)

(* -------------------------------------------------------------------------- *)
(* Leftover span: one parent chord restricted to [t0, t1].                    *)
(* -------------------------------------------------------------------------- *)

Record leftover_span : Type := mkLeftoverSpan {
  ls_parent : ChordEgg;
  ls_t0 : R;
  ls_t1 : R
}.

Definition leftover_span_width (s : leftover_span) : R :=
  leftover_width (ls_t0 s) (ls_t1 s).

Definition leftover_span_interior (s : leftover_span) (t : R) : Prop :=
  ls_t0 s < t < ls_t1 s.

Definition leftover_span_parent (c : ChordEgg) : leftover_span :=
  mkLeftoverSpan c 0 1.

Definition leftover_span_chord (s : leftover_span) : ChordEgg :=
  leftover_half (ls_parent s) (ls_t0 s) (ls_t1 s).

Definition leftover_span_split (s : leftover_span) (t : R)
  : leftover_span * leftover_span :=
  (mkLeftoverSpan (ls_parent s) (ls_t0 s) t,
   mkLeftoverSpan (ls_parent s) t (ls_t1 s)).

Lemma leftover_span_parent_width :
  forall c, leftover_span_width (leftover_span_parent c) = 1.
Proof.
  intros c.
  unfold leftover_span_parent, leftover_span_width.
  exact leftover_width_parent.
Qed.

(* Pairwise leftover_width decrease on an arbitrary leftover. This is
   interior_hit_splits_width, not leftover_quad_width_decreases. *)
Definition leftover_span_lo (s : leftover_span) (t : R) : leftover_span :=
  mkLeftoverSpan (ls_parent s) (ls_t0 s) t.

Definition leftover_span_hi (s : leftover_span) (t : R) : leftover_span :=
  mkLeftoverSpan (ls_parent s) t (ls_t1 s).

Lemma leftover_span_split_fst_snd :
  forall s t,
    fst (leftover_span_split s t) = leftover_span_lo s t /\
    snd (leftover_span_split s t) = leftover_span_hi s t.
Proof.
  intros s t.
  split; reflexivity.
Qed.

Lemma leftover_span_split_width :
  forall s t,
    leftover_span_interior s t ->
    leftover_span_width (leftover_span_lo s t)
      + leftover_span_width (leftover_span_hi s t)
      = leftover_span_width s /\
    leftover_span_width (leftover_span_lo s t)
      < leftover_span_width s /\
    leftover_span_width (leftover_span_hi s t)
      < leftover_span_width s.
Proof.
  intros [c t0 t1] t Hint.
  unfold leftover_span_interior in Hint.
  simpl in Hint.
  destruct Hint as [Hlo Hhi].
  unfold leftover_span_lo, leftover_span_hi, leftover_span_width, leftover_width.
  simpl.
  assert (H0 : 0 <= t - t0) by lra.
  assert (H1 : 0 <= t1 - t) by lra.
  assert (H2 : 0 <= t1 - t0) by lra.
  rewrite (Rabs_pos_eq (t - t0) H0).
  rewrite (Rabs_pos_eq (t1 - t) H1).
  rewrite (Rabs_pos_eq (t1 - t0) H2).
  split; [lra|].
  split; lra.
Qed.

Lemma leftover_span_parent_split_recovers_pairwise :
  forall t,
    0 < t < 1 ->
    leftover_span_interior (leftover_span_parent diag_ab) t /\
    leftover_span_width (fst (leftover_span_split (leftover_span_parent diag_ab) t))
      < leftover_span_width (leftover_span_parent diag_ab) /\
    leftover_span_width (snd (leftover_span_split (leftover_span_parent diag_ab) t))
      < leftover_span_width (leftover_span_parent diag_ab).
Proof.
  intros t Ht.
  assert (Hint : leftover_span_interior (leftover_span_parent diag_ab) t).
  { unfold leftover_span_parent, leftover_span_interior. simpl. exact Ht. }
  split; [exact Hint|].
  destruct (leftover_span_split_width (leftover_span_parent diag_ab) t Hint)
    as [_ [Hlo Hhi]].
  destruct (leftover_span_split_fst_snd (leftover_span_parent diag_ab) t) as [Hf Hs].
  rewrite Hf, Hs.
  split; [exact Hlo|exact Hhi].
Qed.

Lemma leftover_span_chord_is_half :
  forall c t0 t1,
    leftover_span_chord (mkLeftoverSpan c t0 t1) = leftover_half c t0 t1.
Proof.
  intros c t0 t1.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Inductive leftover cook. HitSplit is the only cook constructor.            *)
(* Kiss / ShareOne / MintTwo are not constructors here.                       *)
(* -------------------------------------------------------------------------- *)

Inductive leftover_item : Type :=
| LUnsplit (s : leftover_span)
| LHitSplit (s : leftover_span) (t : R) (lo hi : leftover_item).

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

Fixpoint lbag_app (a b : leftover_span_bag) : leftover_span_bag :=
  match a with
  | LBagNil => b
  | LBagCons s r => LBagCons s (lbag_app r b)
  end.

Fixpoint leftover_item_frontier (it : leftover_item) : leftover_span_bag :=
  match it with
  | LUnsplit s => LBagCons s LBagNil
  | LHitSplit _ _ lo hi =>
      lbag_app (leftover_item_frontier lo) (leftover_item_frontier hi)
  end.

(* leftover_quad as one pairwise Hit-split: two leftover_item trees. *)
Definition leftover_quad_cook (c1 c2 : ChordEgg) (ti tj : R)
  : leftover_item * leftover_item :=
  (LHitSplit (leftover_span_parent c1) ti
     (LUnsplit (mkLeftoverSpan c1 0 ti))
     (LUnsplit (mkLeftoverSpan c1 ti 1)),
   LHitSplit (leftover_span_parent c2) tj
     (LUnsplit (mkLeftoverSpan c2 0 tj))
     (LUnsplit (mkLeftoverSpan c2 tj 1))).

Definition leftover_quad_as_bag (c1 c2 : ChordEgg) (ti tj : R)
  : leftover_span_bag :=
  LBagCons (mkLeftoverSpan c1 0 ti)
    (LBagCons (mkLeftoverSpan c1 ti 1)
      (LBagCons (mkLeftoverSpan c2 0 tj)
        (LBagCons (mkLeftoverSpan c2 tj 1) LBagNil))).

Lemma leftover_quad_cook_frontier :
  forall c1 c2 ti tj,
    lbag_app
      (leftover_item_frontier (fst (leftover_quad_cook c1 c2 ti tj)))
      (leftover_item_frontier (snd (leftover_quad_cook c1 c2 ti tj)))
    = leftover_quad_as_bag c1 c2 ti tj.
Proof.
  intros c1 c2 ti tj.
  reflexivity.
Qed.

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

(* leftover_quad 4-tuple is the four leftover_span chords. I.8 reused. *)
Lemma leftover_quad_as_bag_is_one_hit :
  forall c1 c2 ti tj,
    leftovers_ab c1 c2 ti tj =
      (leftover_span_chord (mkLeftoverSpan c1 0 ti),
       leftover_span_chord (mkLeftoverSpan c1 ti 1),
       leftover_span_chord (mkLeftoverSpan c2 0 tj),
       leftover_span_chord (mkLeftoverSpan c2 tj 1)) /\
    leftovers_ab c1 c2 ti tj = leftovers_ba c1 c2 ti tj /\
    lbag_count (leftover_quad_as_bag c1 c2 ti tj) = 4%nat.
Proof.
  intros c1 c2 ti tj.
  split; [reflexivity|].
  split; [apply split_step_confluent|].
  reflexivity.
Qed.

(* Frontier sum of leftover_quad is leftover_quad_width: conserved, not
   a well-founded bag measure. Pairwise child width still decreases. *)
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
(* Stepwise Hit-split iterator. Fuel is not LoopDischarged.                   *)
(* -------------------------------------------------------------------------- *)

Fixpoint lbag_nth (b : leftover_span_bag) (n : nat) : option leftover_span :=
  match b, n with
  | LBagNil, _ => None
  | LBagCons s _, O => Some s
  | LBagCons _ r, S n' => lbag_nth r n'
  end.

Fixpoint lbag_replace_split (b : leftover_span_bag) (n : nat) (t : R)
  : option leftover_span_bag :=
  match b, n with
  | LBagNil, _ => None
  | LBagCons s r, O =>
      Some (LBagCons (leftover_span_lo s t) (LBagCons (leftover_span_hi s t) r))
  | LBagCons s r, S n' =>
      match lbag_replace_split r n' t with
      | None => None
      | Some r' => Some (LBagCons s r')
      end
  end.

Inductive leftover_plan : Type :=
| PlanNil
| PlanCons (idx : nat) (t : R) (rest : leftover_plan).

Fixpoint leftover_bag_cook_fuel (fuel : nat) (b : leftover_span_bag)
  (pl : leftover_plan) : leftover_span_bag :=
  match fuel, pl with
  | O, _ => b
  | S _, PlanNil => b
  | S fuel', PlanCons idx t rest =>
      match lbag_replace_split b idx t with
      | Some b' => leftover_bag_cook_fuel fuel' b' rest
      | None => leftover_bag_cook_fuel fuel' b rest
      end
  end.

Definition leftover_plan_ok (b : leftover_span_bag) (idx : nat) (t : R) : Prop :=
  exists s, lbag_nth b idx = Some s /\ leftover_span_interior s t.

Lemma leftover_bag_cook_fuel_zero :
  forall b pl, leftover_bag_cook_fuel 0 b pl = b.
Proof.
  intros b pl.
  reflexivity.
Qed.

Lemma leftover_bag_cook_fuel_nil :
  forall n b, leftover_bag_cook_fuel n b PlanNil = b.
Proof.
  intros n b.
  destruct n; reflexivity.
Qed.

Lemma lbag_replace_split_some :
  forall b n s t,
    lbag_nth b n = Some s ->
    exists b', lbag_replace_split b n t = Some b'.
Proof.
  induction b as [|s0 rest IH]; intros n s t Hnth.
  - discriminate.
  - destruct n as [|n'].
    + exists (LBagCons (leftover_span_lo s0 t)
                (LBagCons (leftover_span_hi s0 t) rest)).
      reflexivity.
    + simpl in Hnth.
      destruct (IH n' s t Hnth) as [rest' Hr].
      exists (LBagCons s0 rest').
      simpl.
      rewrite Hr.
      reflexivity.
Qed.

Lemma lbag_replace_split_count :
  forall b n t b',
    lbag_replace_split b n t = Some b' ->
    lbag_count b' = S (lbag_count b).
Proof.
  induction b as [|s0 rest IH]; intros n t b' Hrep.
  - discriminate.
  - destruct n as [|n'].
    + simpl in Hrep.
      inversion Hrep.
      reflexivity.
    + simpl in Hrep.
      destruct (lbag_replace_split rest n' t) as [rest'|] eqn:Hr.
      * inversion Hrep.
        simpl.
        rewrite (IH n' t rest' Hr).
        reflexivity.
      * discriminate.
Qed.

Lemma lbag_replace_split_sum :
  forall b n t b' s,
    lbag_nth b n = Some s ->
    leftover_span_interior s t ->
    lbag_replace_split b n t = Some b' ->
    lbag_sum b' = lbag_sum b.
Proof.
  induction b as [|s0 rest IH]; intros n t b' s Hnth Hint Hrep.
  - discriminate.
  - destruct n as [|n'].
    + inversion Hnth.
      subst s0.
      inversion Hrep.
      subst b'.
      destruct (leftover_span_split_width s t Hint) as [Hsum _].
      cbn [lbag_sum].
      rewrite <- Rplus_assoc.
      rewrite Hsum.
      reflexivity.
    + simpl in Hnth.
      simpl in Hrep.
      destruct (lbag_replace_split rest n' t) as [rest'|] eqn:Hr.
      * inversion Hrep.
        subst b'.
        simpl.
        rewrite (IH n' t rest' s Hnth Hint Hr).
        reflexivity.
      * discriminate.
Qed.

(* Locked crossing pair: leftover_quad of diag_ab × diag_cd at 1/2. *)
Definition locked_rho_bag : leftover_span_bag :=
  leftover_quad_as_bag diag_ab diag_cd (1 / 2) (1 / 2).

Definition locked_rho_plan : leftover_plan :=
  PlanCons 0 (1 / 4) PlanNil.

Lemma locked_rho_bag_count :
  lbag_count locked_rho_bag = 4%nat.
Proof.
  reflexivity.
Qed.

Lemma locked_rho_nth0 :
  lbag_nth locked_rho_bag 0 = Some (mkLeftoverSpan diag_ab 0 (1 / 2)).
Proof.
  reflexivity.
Qed.

Lemma locked_rho_plan_ok :
  leftover_plan_ok locked_rho_bag 0 (1 / 4).
Proof.
  exists (mkLeftoverSpan diag_ab 0 (1 / 2)).
  split; [reflexivity|].
  unfold leftover_span_interior.
  simpl.
  lra.
Qed.

Lemma locked_rho_cook_zero :
  leftover_bag_cook_fuel 0 locked_rho_bag locked_rho_plan = locked_rho_bag.
Proof.
  reflexivity.
Qed.

Lemma locked_rho_replace :
  lbag_replace_split locked_rho_bag 0 (1 / 4) =
  Some
    (LBagCons (mkLeftoverSpan diag_ab 0 (1 / 4))
      (LBagCons (mkLeftoverSpan diag_ab (1 / 4) (1 / 2))
        (LBagCons (mkLeftoverSpan diag_ab (1 / 2) 1)
          (LBagCons (mkLeftoverSpan diag_cd 0 (1 / 2))
            (LBagCons (mkLeftoverSpan diag_cd (1 / 2) 1) LBagNil))))).
Proof.
  reflexivity.
Qed.

Lemma locked_rho_cook_one_count :
  lbag_count (leftover_bag_cook_fuel 1 locked_rho_bag locked_rho_plan) = 5%nat.
Proof.
  reflexivity.
Qed.

Lemma locked_rho_cook_one_sum :
  lbag_sum (leftover_bag_cook_fuel 1 locked_rho_bag locked_rho_plan)
  = lbag_sum locked_rho_bag.
Proof.
  apply (lbag_replace_split_sum locked_rho_bag 0 (1 / 4)
           (leftover_bag_cook_fuel 1 locked_rho_bag locked_rho_plan)
           (mkLeftoverSpan diag_ab 0 (1 / 2))).
  - exact locked_rho_nth0.
  - unfold leftover_span_interior; simpl; lra.
  - rewrite locked_rho_replace.
    reflexivity.
Qed.

Lemma locked_rho_cook_one_not_quad_measure :
  lbag_sum (leftover_bag_cook_fuel 1 locked_rho_bag locked_rho_plan)
  = leftover_quad_width (1 / 2) (1 / 2) /\
  leftover_quad_width (1 / 2) (1 / 2) = leftover_width 0 1 + leftover_width 0 1.
Proof.
  split.
  - rewrite locked_rho_cook_one_sum.
    unfold locked_rho_bag.
    apply leftover_quad_as_bag_sum.
  - apply leftover_quad_width_conserved; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Fence: cook ctor is Hit-split only. Kiss / share / mint stay QEX.          *)
(* -------------------------------------------------------------------------- *)

Inductive LeftoverModuloCookCtor : Type :=
| LeftoverModuloHitSplit.

Definition leftover_modulo_cook_ctor : LeftoverModuloCookCtor :=
  LeftoverModuloHitSplit.

Lemma leftover_modulo_cook_is_hit_split :
  leftover_modulo_cook_ctor = LeftoverModuloHitSplit.
Proof.
  reflexivity.
Qed.

Lemma leftover_modulo_cook_not_kiss :
  leftover_modulo_cook_ctor = LeftoverModuloHitSplit /\
  ~ leftover_quad_kiss_arm.
Proof.
  split; [reflexivity|exact leftover_quad_kiss_arm_missing].
Qed.

Lemma leftover_modulo_cook_not_share_mint :
  leftover_modulo_cook_ctor = LeftoverModuloHitSplit /\
  ~ leftover_quad_share_mint_arm.
Proof.
  split; [reflexivity|exact leftover_quad_share_mint_arm_missing].
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

(* WITNESS {"claimId":"0007-rho-modulo-qex","topic":"overlay","lemma":"ticket_0007_rho_modulo_step_qed_or_qex","title":"rho modulo QEX: leftover_span Hit-split strictly decreases each child leftover_width (QED) or leftover_quad_width_decreases (QEX); discharged QED; pairwise width, not leftover_quad bag-sum; kiss/share/mint stay QEX arms","file":"theories/SheetHenCookLoopModulo.v","witness":"0007-rho-modulo-qex","board":"ADR-0007"} *)
Theorem ticket_0007_rho_modulo_step_qed_or_qex :
  (forall s t,
     leftover_span_interior s t ->
     leftover_span_width (leftover_span_lo s t)
       + leftover_span_width (leftover_span_hi s t)
       = leftover_span_width s /\
     leftover_span_width (leftover_span_lo s t)
       < leftover_span_width s /\
     leftover_span_width (leftover_span_hi s t)
       < leftover_span_width s)
  \/ leftover_quad_width_decreases.
Proof.
  left.
  exact leftover_span_split_width.
Qed.

(* WITNESS {"claimId":"0007-rho-modulo-qex","topic":"overlay","lemma":"ticket_0007_rho_modulo_bag_qed_or_qex","title":"rho modulo QEX: leftover_quad is one Hit-split leftover_item pair / 4-span bag and leftovers_ab equals leftovers_ba (QED) or leftover_quad_width_decreases (QEX); discharged QED; bag-sum is leftover_quad_width, not a measure; I.8 reused not reminted","file":"theories/SheetHenCookLoopModulo.v","witness":"0007-rho-modulo-qex","board":"ADR-0007"} *)
Theorem ticket_0007_rho_modulo_bag_qed_or_qex :
  (forall c1 c2 ti tj,
     leftover_item_frontier (fst (leftover_quad_cook c1 c2 ti tj)) =
       LBagCons (mkLeftoverSpan c1 0 ti)
         (LBagCons (mkLeftoverSpan c1 ti 1) LBagNil) /\
     leftover_item_frontier (snd (leftover_quad_cook c1 c2 ti tj)) =
       LBagCons (mkLeftoverSpan c2 0 tj)
         (LBagCons (mkLeftoverSpan c2 tj 1) LBagNil) /\
     leftovers_ab c1 c2 ti tj = leftovers_ba c1 c2 ti tj /\
     lbag_count (leftover_quad_as_bag c1 c2 ti tj) = 4%nat /\
     lbag_sum (leftover_quad_as_bag c1 c2 ti tj) = leftover_quad_width ti tj)
  \/ leftover_quad_width_decreases.
Proof.
  left.
  intros c1 c2 ti tj.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [apply split_step_confluent|].
  split; [reflexivity|].
  apply leftover_quad_as_bag_sum.
Qed.

(* WITNESS {"claimId":"0007-rho-modulo-qex","topic":"overlay","lemma":"ticket_0007_rho_modulo_iter_qed_or_qex","title":"rho modulo QEX: fuel Hit-split iterator steps the locked leftover_quad bag (QED) or cook_loop is LoopDischarged (QEX); discharged QED; fuel is not bag-term; ctor is LeftoverModuloHitSplit only; LoopObligation stands","file":"theories/SheetHenCookLoopModulo.v","witness":"0007-rho-modulo-qex","board":"ADR-0007"} *)
Theorem ticket_0007_rho_modulo_iter_qed_or_qex :
  (leftover_bag_cook_fuel 0 locked_rho_bag locked_rho_plan = locked_rho_bag /\
   leftover_plan_ok locked_rho_bag 0 (1 / 4) /\
   lbag_count (leftover_bag_cook_fuel 1 locked_rho_bag locked_rho_plan) = 5%nat /\
   lbag_sum (leftover_bag_cook_fuel 1 locked_rho_bag locked_rho_plan)
     = lbag_sum locked_rho_bag /\
   leftover_modulo_cook_ctor = LeftoverModuloHitSplit /\
   cook_loop_status = LoopObligation /\
   cook_loop_status <> LoopDischarged)
  \/ cook_loop_status = LoopDischarged.
Proof.
  left.
  split; [exact locked_rho_cook_zero|].
  split; [exact locked_rho_plan_ok|].
  split; [exact locked_rho_cook_one_count|].
  split; [exact locked_rho_cook_one_sum|].
  split; [exact leftover_modulo_cook_is_hit_split|].
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
   /\ ~ leftover_quad_share_mint_arm
   /\ leftover_modulo_cook_ctor = LeftoverModuloHitSplit).
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
  split; [exact leftover_quad_share_mint_arm_missing|].
  exact leftover_modulo_cook_is_hit_split.
Qed.

Print Assumptions leftover_span_split_width.
Print Assumptions leftover_span_parent_split_recovers_pairwise.
Print Assumptions leftover_quad_cook_frontier.
Print Assumptions leftover_quad_as_bag_count.
Print Assumptions leftover_quad_as_bag_sum.
Print Assumptions leftover_quad_as_bag_is_one_hit.
Print Assumptions leftover_quad_as_bag_sum_conserved.
Print Assumptions leftover_bag_cook_fuel_zero.
Print Assumptions leftover_bag_cook_fuel_nil.
Print Assumptions lbag_replace_split_some.
Print Assumptions lbag_replace_split_count.
Print Assumptions lbag_replace_split_sum.
Print Assumptions locked_rho_plan_ok.
Print Assumptions locked_rho_cook_one_count.
Print Assumptions locked_rho_cook_one_sum.
Print Assumptions locked_rho_cook_one_not_quad_measure.
Print Assumptions leftover_modulo_cook_not_kiss.
Print Assumptions leftover_modulo_cook_not_share_mint.
Print Assumptions leftover_modulo_park_unchanged.
Print Assumptions ticket_0007_rho_modulo_step_qed_or_qex.
Print Assumptions ticket_0007_rho_modulo_bag_qed_or_qex.
Print Assumptions ticket_0007_rho_modulo_iter_qed_or_qex.
Print Assumptions ticket_0007_rho_modulo_park_qed_or_qex.
