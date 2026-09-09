(* ============================================================================
   NetTopologySuite.Proofs.CircularCookSplit
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: feed a circular Hit (with parameters)
   into a same-shape cook step as the chord lane's split(t).

   CircularCookHit already constructs (h*, p*, tᵢ, tⱼ) on locked discs
   with γ(t)=p*. This sidecar splits each full-circle interpolant at
   those t values and records incidence on the Hit's hen.

   QED: locked (0,0)/(7,0) r=5 plus-root Hit cooks; leftovers meet at
   p+; leftover γ stays on the parent circle.
   I.7 / MintTwo: p− is a second Hit, not optional. Allocation across
   the two radical roots is MintTwo (hen+, hen−). Leftover shared
   endpoint is Hit incidence, not a kiss.
   QEX: Touch / Empty / Decline allocate no hen (kiss is a fenced
   scope arm — not a CRV-TOUCH kiss decision). Host try_cook_hit still
   declines circular eggs (Adr0007NodingEpic.v :
   ticket_0007_circ_host_cook_qed_or_qex). CircGamma stays QEX
   (CircularCook.v : circular_gamma_is_qex).

   I.1 Fence: the four objects are pairwise unequal by observation
   on the locked Z^6 witness — not a type synonym. Touch ≠ IHit;
   circular Empty ≠ Decline. Host I_gloss stays QEX.

   I.2 ∀ Hit soundness lives in CircularCookHit.v; I.3 ∀ Empty /
   Decline lives in CircularCookEmpty.v (classifier, γ_full).
   This sidecar cook stays locked — I.3 does not drop the cook
   lock and does not start I.8–I.10.

   Honesty fences:
     constructed chord–chord 𝓘 ≠ I_circles_z / I_CIRCULAR ≠ this
     sidecar cook ≠ glossary 𝓘 with host γ / t.
     Not first cook scope. Not a noder. Not ArcSplitAtNode (that is
     the N-AA chord-sign partition lane). Not a remint of
     CurveSegment / Exact* / Dart / Hobby / leftover_width.
     Do not fake atan2-free host γ.

   WITNESS topic: overlay · claimId: 0007
   witness: 0007-circ-cook / 0007-I.7-mint-two / 0007-I.1-fence
     / 0007-I.2-hit-sound / 0007-I.3-empty-decline
     (Hit ∀ in CircularCookHit; Empty/Decline ∀ in CircularCookEmpty)
   board: ADR-0007
   4-axiom (atan2 / Classical_Prop.classic via CircularCookHit).
   No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import ZArith Reals Lra.
From NTS.Proofs Require Import Distance SheetHenCook ArcArcCircles
  CircularCookZ CircularCook CircularCookHit.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Full-circle leftover interpolants. Not Egg. Not CircularArc. Not a         *)
(* remint of ArcSplitAtNode / chord_split leftovers.                          *)
(* -------------------------------------------------------------------------- *)

Record CircLeftover : Type := mkCircLeftover {
  cl_O : Point;
  cl_r : R;
  cl_t0 : R;
  cl_t1 : R
}.

Definition circ_leftover_eval (cl : CircLeftover) (u : R) : Point :=
  circ_gamma (cl_O cl) (cl_r cl) ((1 - u) * cl_t0 cl + u * cl_t1 cl).

Definition circ_split (O : Point) (r t : R) : CircLeftover * CircLeftover :=
  (mkCircLeftover O r 0 t, mkCircLeftover O r t 1).

Lemma circ_split_left_reparam :
  forall O r t u,
    circ_leftover_eval (fst (circ_split O r t)) u = circ_gamma O r (u * t).
Proof.
  intros O r t u.
  unfold circ_leftover_eval, circ_split.
  simpl.
  apply f_equal.
  ring.
Qed.

Lemma circ_split_right_reparam :
  forall O r t u,
    circ_leftover_eval (snd (circ_split O r t)) u =
    circ_gamma O r (t + u * (1 - t)).
Proof.
  intros O r t u.
  unfold circ_leftover_eval, circ_split.
  simpl.
  apply f_equal.
  ring.
Qed.

Lemma circ_split_join :
  forall O r t,
    circ_leftover_eval (fst (circ_split O r t)) 1 = circ_gamma O r t /\
    circ_leftover_eval (snd (circ_split O r t)) 0 = circ_gamma O r t.
Proof.
  intros O r t.
  rewrite circ_split_left_reparam, circ_split_right_reparam.
  split; [apply f_equal; ring | apply f_equal; ring].
Qed.

Lemma circ_split_ends :
  forall O r t,
    circ_leftover_eval (fst (circ_split O r t)) 0 = circ_gamma O r 0 /\
    circ_leftover_eval (snd (circ_split O r t)) 1 = circ_gamma O r 1.
Proof.
  intros O r t.
  rewrite circ_split_left_reparam, circ_split_right_reparam.
  split; [apply f_equal; ring | apply f_equal; ring].
Qed.

Lemma circ_gamma_on_circle :
  forall O r t,
    dist_sq O (circ_gamma O r t) = r * r.
Proof.
  intros O r t.
  unfold circ_gamma, dist_sq.
  cbn [px py].
  replace (px O - (px O + r * cos (2 * PI * t)))
    with (- r * cos (2 * PI * t)) by ring.
  replace (py O - (py O + r * sin (2 * PI * t)))
    with (- r * sin (2 * PI * t)) by ring.
  replace ((- r * cos (2 * PI * t)) * (- r * cos (2 * PI * t))
           + (- r * sin (2 * PI * t)) * (- r * sin (2 * PI * t)))
    with (r * r * (sin (2 * PI * t) * sin (2 * PI * t)
                   + cos (2 * PI * t) * cos (2 * PI * t))) by ring.
  pose proof (sin2_cos2 (2 * PI * t)) as Hpyth.
  unfold Rsqr in Hpyth.
  rewrite Hpyth.
  ring.
Qed.

Lemma circ_leftover_on_circle :
  forall cl u,
    dist_sq (cl_O cl) (circ_leftover_eval cl u) = cl_r cl * cl_r cl.
Proof.
  intros cl u.
  unfold circ_leftover_eval.
  apply circ_gamma_on_circle.
Qed.

(* -------------------------------------------------------------------------- *)
(* Same-shape cook step: one Hit root → leftovers on both circles, one hen.   *)
(* -------------------------------------------------------------------------- *)

Record CircCookedPair : Type := mkCircCookedPair {
  ccp_hen : Hen;
  ccp_L1 : CircLeftover;
  ccp_R1 : CircLeftover;
  ccp_L2 : CircLeftover;
  ccp_R2 : CircLeftover
}.

Definition cook_circ_root
  (O1 : Point) (r1 : R) (O2 : Point) (r2 : R)
  (ti tj : R) (h : Hen) : CircCookedPair :=
  mkCircCookedPair h
    (fst (circ_split O1 r1 ti))
    (snd (circ_split O1 r1 ti))
    (fst (circ_split O2 r2 tj))
    (snd (circ_split O2 r2 tj)).

Definition circ_cooked_meets (cp : CircCookedPair) (p : Point) : Prop :=
  circ_leftover_eval (ccp_L1 cp) 1 = p /\
  circ_leftover_eval (ccp_R1 cp) 0 = p /\
  circ_leftover_eval (ccp_L2 cp) 1 = p /\
  circ_leftover_eval (ccp_R2 cp) 0 = p.

Definition circ_cooked_ok
  (cp : CircCookedPair) (h : Hen) (p : Point) : Prop :=
  ccp_hen cp = h /\ circ_cooked_meets cp p.

Definition try_cook_circ_hit
  (O1 : Point) (r1 : R) (O2 : Point) (r2 : R)
  (o : ICircG) (h : Hen) : option CircCookedPair :=
  match o with
  | ICircGHit _ _ ti tj _ _ _ _ =>
      Some (cook_circ_root O1 r1 O2 r2 ti tj h)
  | ICircGEmpty => None
  | ICircGTouch _ _ _ _ => None
  | ICircGDecline => None
  end.

Lemma try_cook_circ_hit_empty_none :
  forall O1 r1 O2 r2 h,
    try_cook_circ_hit O1 r1 O2 r2 ICircGEmpty h = None.
Proof.
  intros. reflexivity.
Qed.

Lemma try_cook_circ_hit_decline_none :
  forall O1 r1 O2 r2 h,
    try_cook_circ_hit O1 r1 O2 r2 ICircGDecline h = None.
Proof.
  intros. reflexivity.
Qed.

Lemma try_cook_circ_hit_touch_none :
  forall O1 r1 O2 r2 h p ti tj,
    try_cook_circ_hit O1 r1 O2 r2 (ICircGTouch h p ti tj) h = None.
Proof.
  intros. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked plus-root cook.                                                     *)
(* -------------------------------------------------------------------------- *)

Definition locked_ti_plus : R := circ_t locked_O1 locked_p_plus.
Definition locked_tj_plus : R := circ_t locked_O2 locked_p_plus.

Definition cooked_circ_plus : CircCookedPair :=
  cook_circ_root locked_O1 locked_r locked_O2 locked_r
    locked_ti_plus locked_tj_plus hen_plus.

Lemma locked_plus_gamma :
  circ_gamma locked_O1 locked_r locked_ti_plus = locked_p_plus /\
  circ_gamma locked_O2 locked_r locked_tj_plus = locked_p_plus.
Proof.
  unfold locked_ti_plus, locked_tj_plus.
  destruct locked_hit_plus_on_gamma as [[_ H1] [_ H2]].
  split; [symmetry; exact H1 | symmetry; exact H2].
Qed.

Lemma cooked_circ_plus_ok :
  circ_cooked_ok cooked_circ_plus hen_plus locked_p_plus.
Proof.
  unfold circ_cooked_ok, cooked_circ_plus.
  split; [reflexivity|].
  unfold circ_cooked_meets, cook_circ_root.
  cbn [ccp_L1 ccp_R1 ccp_L2 ccp_R2].
  destruct locked_plus_gamma as [Hp1 Hp2].
  rewrite !circ_split_left_reparam, !circ_split_right_reparam.
  replace (1 * locked_ti_plus) with locked_ti_plus by ring.
  replace (locked_ti_plus + 0 * (1 - locked_ti_plus))
    with locked_ti_plus by ring.
  replace (1 * locked_tj_plus) with locked_tj_plus by ring.
  replace (locked_tj_plus + 0 * (1 - locked_tj_plus))
    with locked_tj_plus by ring.
  repeat split; assumption.
Qed.

Lemma cooked_circ_plus_try :
  try_cook_circ_hit locked_O1 locked_r locked_O2 locked_r
    (I_circles_gamma 0 0 5 7 0 5) hen_plus = Some cooked_circ_plus.
Proof.
  unfold try_cook_circ_hit, cooked_circ_plus, cook_circ_root,
         locked_ti_plus, locked_tj_plus.
  rewrite locked_I_circles_gamma_hit.
  reflexivity.
Qed.

Lemma locked_circ_empty_none :
  try_cook_circ_hit locked_O1 locked_r locked_O2 locked_r
    (I_circles_gamma 0 0 5 20 0 5) hen_plus = None.
Proof.
  unfold try_cook_circ_hit.
  rewrite locked_I_circles_gamma_empty.
  reflexivity.
Qed.

Lemma locked_circ_decline_none :
  try_cook_circ_hit locked_O1 locked_r locked_O2 locked_r
    (I_circles_gamma 0 0 5 0 0 5) hen_plus = None.
Proof.
  unfold try_cook_circ_hit.
  rewrite locked_I_circles_gamma_decline.
  reflexivity.
Qed.

(* Touch / kiss: fenced scope arm. Does not pick a CRV-TOUCH procedure. *)
Lemma locked_circ_touch_none :
  try_cook_circ_hit locked_O1 locked_r kiss_O2 locked_r
    (I_circles_gamma 0 0 5 10 0 5) hen_plus = None.
Proof.
  unfold try_cook_circ_hit.
  rewrite locked_I_circles_gamma_touch.
  reflexivity.
Qed.

Lemma locked_circ_internal_kiss_none :
  try_cook_circ_hit locked_O1 locked_r ikiss_O2 ikiss_r2
    (I_circles_gamma 0 0 5 3 0 2) hen_plus = None.
Proof.
  unfold try_cook_circ_hit.
  rewrite locked_I_circles_gamma_internal_kiss.
  reflexivity.
Qed.

Lemma circular_gamma_host_still_qex :
  circular_gamma_status = CircGammaQEX.
Proof.
  exact circular_gamma_is_qex.
Qed.

Lemma circular_still_not_first_cook_scope :
  ~ first_cook_scope EggCircularArc EggCircularArc.
Proof.
  exact circular_not_first_cook_scope.
Qed.

(* -------------------------------------------------------------------------- *)
(* I.7 / MintTwo: p− is a second Hit. Allocation across both radical          *)
(* roots is MintTwo. Shared leftover endpoint ≠ kiss. Empty / Decline /       *)
(* Touch still mint nothing. Not a CRV-TOUCH tangency procedure.              *)
(* -------------------------------------------------------------------------- *)

Definition locked_ti_minus : R := circ_t locked_O1 locked_p_minus.
Definition locked_tj_minus : R := circ_t locked_O2 locked_p_minus.

Definition cooked_circ_minus : CircCookedPair :=
  cook_circ_root locked_O1 locked_r locked_O2 locked_r
    locked_ti_minus locked_tj_minus hen_minus.

Lemma locked_minus_gamma :
  circ_gamma locked_O1 locked_r locked_ti_minus = locked_p_minus /\
  circ_gamma locked_O2 locked_r locked_tj_minus = locked_p_minus.
Proof.
  unfold locked_ti_minus, locked_tj_minus.
  destruct locked_hit_minus_on_gamma as [[_ H1] [_ H2]].
  split; [symmetry; exact H1 | symmetry; exact H2].
Qed.

Lemma cooked_circ_minus_ok :
  circ_cooked_ok cooked_circ_minus hen_minus locked_p_minus.
Proof.
  unfold circ_cooked_ok, cooked_circ_minus.
  split; [reflexivity|].
  unfold circ_cooked_meets, cook_circ_root.
  cbn [ccp_L1 ccp_R1 ccp_L2 ccp_R2].
  destruct locked_minus_gamma as [Hp1 Hp2].
  rewrite !circ_split_left_reparam, !circ_split_right_reparam.
  replace (1 * locked_ti_minus) with locked_ti_minus by ring.
  replace (locked_ti_minus + 0 * (1 - locked_ti_minus))
    with locked_ti_minus by ring.
  replace (1 * locked_tj_minus) with locked_tj_minus by ring.
  replace (locked_tj_minus + 0 * (1 - locked_tj_minus))
    with locked_tj_minus by ring.
  repeat split; assumption.
Qed.

Lemma hen_plus_neq_hen_minus : hen_plus <> hen_minus.
Proof.
  discriminate.
Qed.

Lemma locked_radical_a :
  radical_axis_a locked_O1 locked_O2 locked_r locked_r = 7 / 2.
Proof.
  unfold radical_axis_a, locked_r.
  rewrite locked_centers_dist. field.
Qed.

Lemma locked_radical_ux : radical_axis_ux locked_O1 locked_O2 = 1.
Proof.
  unfold radical_axis_ux. rewrite locked_centers_dist.
  unfold locked_O1, locked_O2. cbn [px py]. field.
Qed.

Lemma locked_radical_uy : radical_axis_uy locked_O1 locked_O2 = 0.
Proof.
  unfold radical_axis_uy. rewrite locked_centers_dist.
  unfold locked_O1, locked_O2. cbn [px py]. field.
Qed.

Lemma locked_h2 :
  locked_r * locked_r
    - radical_axis_a locked_O1 locked_O2 locked_r locked_r
      * radical_axis_a locked_O1 locked_O2 locked_r locked_r
  = 51 / 4.
Proof.
  rewrite locked_radical_a. unfold locked_r. field.
Qed.

Lemma locked_h_pos :
  0 < radical_axis_h locked_O1 locked_O2 locked_r locked_r.
Proof.
  unfold radical_axis_h. rewrite locked_h2. apply sqrt_lt_R0. lra.
Qed.

Lemma locked_p_plus_coords :
  px locked_p_plus = 7 / 2 /\
  py locked_p_plus = radical_axis_h locked_O1 locked_O2 locked_r locked_r.
Proof.
  unfold locked_p_plus, radical_point_plus.
  rewrite locked_radical_a, locked_radical_ux, locked_radical_uy.
  unfold locked_O1. cbn [px py]. split; ring.
Qed.

Lemma locked_p_minus_coords :
  px locked_p_minus = 7 / 2 /\
  py locked_p_minus = - radical_axis_h locked_O1 locked_O2 locked_r locked_r.
Proof.
  unfold locked_p_minus, radical_point_minus.
  rewrite locked_radical_a, locked_radical_ux, locked_radical_uy.
  unfold locked_O1. cbn [px py]. split; ring.
Qed.

Lemma locked_p_plus_neq_minus : locked_p_plus <> locked_p_minus.
Proof.
  intro Heq.
  apply (f_equal py) in Heq.
  destruct locked_p_plus_coords as [_ Hp].
  destruct locked_p_minus_coords as [_ Hm].
  rewrite Hp, Hm in Heq.
  pose proof locked_h_pos as Hh.
  lra.
Qed.

Record CircCookedMintTwo : Type := mkCircCookedMintTwo {
  ccm_id : CookIdDecision;
  ccm_plus : CircCookedPair;
  ccm_minus : CircCookedPair
}.

Definition cook_circ_hit_mint_two
  (O1 : Point) (r1 : R) (O2 : Point) (r2 : R)
  (ti_p tj_p : R) (h_p : Hen)
  (ti_m tj_m : R) (h_m : Hen) : CircCookedMintTwo :=
  mkCircCookedMintTwo
    (MintTwo h_p h_m)
    (cook_circ_root O1 r1 O2 r2 ti_p tj_p h_p)
    (cook_circ_root O1 r1 O2 r2 ti_m tj_m h_m).

Definition try_cook_circ_hit_mint_two
  (O1 : Point) (r1 : R) (O2 : Point) (r2 : R)
  (o : ICircG) : option CircCookedMintTwo :=
  match o with
  | ICircGHit hp _ tip tjp hm _ tim tjm =>
      Some (cook_circ_hit_mint_two O1 r1 O2 r2 tip tjp hp tim tjm hm)
  | ICircGEmpty => None
  | ICircGTouch _ _ _ _ => None
  | ICircGDecline => None
  end.

Definition circ_mint_two_ok
  (cm : CircCookedMintTwo) (hp hm : Hen) (pp pm : Point) : Prop :=
  ccm_id cm = MintTwo hp hm
  /\ apply_id_decision (ccm_id cm) = (hp, hm)
  /\ fst (apply_id_decision (ccm_id cm)) <> snd (apply_id_decision (ccm_id cm))
  /\ circ_cooked_ok (ccm_plus cm) hp pp
  /\ circ_cooked_ok (ccm_minus cm) hm pm
  /\ pp <> pm.

Definition cooked_circ_mint_two : CircCookedMintTwo :=
  cook_circ_hit_mint_two locked_O1 locked_r locked_O2 locked_r
    locked_ti_plus locked_tj_plus hen_plus
    locked_ti_minus locked_tj_minus hen_minus.

Lemma cooked_circ_mint_two_ok :
  circ_mint_two_ok cooked_circ_mint_two
    hen_plus hen_minus locked_p_plus locked_p_minus.
Proof.
  unfold circ_mint_two_ok, cooked_circ_mint_two, cook_circ_hit_mint_two,
         apply_id_decision.
  cbn [ccm_id ccm_plus ccm_minus].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact hen_plus_neq_hen_minus|].
  split; [exact cooked_circ_plus_ok|].
  split; [exact cooked_circ_minus_ok|].
  exact locked_p_plus_neq_minus.
Qed.

Lemma cooked_circ_mint_two_try :
  try_cook_circ_hit_mint_two locked_O1 locked_r locked_O2 locked_r
    (I_circles_gamma 0 0 5 7 0 5) = Some cooked_circ_mint_two.
Proof.
  unfold try_cook_circ_hit_mint_two, cooked_circ_mint_two,
         cook_circ_hit_mint_two, locked_ti_plus, locked_tj_plus,
         locked_ti_minus, locked_tj_minus.
  rewrite locked_I_circles_gamma_hit.
  reflexivity.
Qed.

Lemma try_cook_circ_hit_mint_two_empty_none :
  forall O1 r1 O2 r2,
    try_cook_circ_hit_mint_two O1 r1 O2 r2 ICircGEmpty = None.
Proof.
  intros. reflexivity.
Qed.

Lemma try_cook_circ_hit_mint_two_decline_none :
  forall O1 r1 O2 r2,
    try_cook_circ_hit_mint_two O1 r1 O2 r2 ICircGDecline = None.
Proof.
  intros. reflexivity.
Qed.

Lemma try_cook_circ_hit_mint_two_touch_none :
  forall O1 r1 O2 r2 h p ti tj,
    try_cook_circ_hit_mint_two O1 r1 O2 r2 (ICircGTouch h p ti tj) = None.
Proof.
  intros. reflexivity.
Qed.

Lemma locked_circ_mint_two_empty_none :
  try_cook_circ_hit_mint_two locked_O1 locked_r locked_O2 locked_r
    (I_circles_gamma 0 0 5 20 0 5) = None.
Proof.
  unfold try_cook_circ_hit_mint_two.
  rewrite locked_I_circles_gamma_empty.
  reflexivity.
Qed.

Lemma locked_circ_mint_two_decline_none :
  try_cook_circ_hit_mint_two locked_O1 locked_r locked_O2 locked_r
    (I_circles_gamma 0 0 5 0 0 5) = None.
Proof.
  unfold try_cook_circ_hit_mint_two.
  rewrite locked_I_circles_gamma_decline.
  reflexivity.
Qed.

Lemma locked_circ_mint_two_touch_none :
  try_cook_circ_hit_mint_two locked_O1 locked_r kiss_O2 locked_r
    (I_circles_gamma 0 0 5 10 0 5) = None.
Proof.
  unfold try_cook_circ_hit_mint_two.
  rewrite locked_I_circles_gamma_touch.
  reflexivity.
Qed.

(* Leftover join at p* is Hit incidence. Two leftover pieces sharing
   that endpoint is not a kiss / Touch. Distinct radical roots stay
   two Hits — not a collapsed tangency. *)
Lemma leftover_shared_endpoint_not_touch :
  circ_cooked_meets cooked_circ_plus locked_p_plus
  /\ circ_cooked_meets cooked_circ_minus locked_p_minus
  /\ locked_p_plus <> locked_p_minus
  /\ I_circles_gamma 0 0 5 7 0 5 <>
       ICircGTouch hen_plus locked_p_plus locked_ti_plus locked_tj_plus.
Proof.
  split; [exact (proj2 cooked_circ_plus_ok)|].
  split; [exact (proj2 cooked_circ_minus_ok)|].
  split; [exact locked_p_plus_neq_minus|].
  rewrite locked_I_circles_gamma_hit.
  discriminate.
Qed.

(* Host try_cook_hit still declines circular eggs — same cook step. *)
Lemma host_try_cook_hit_still_none :
  forall p ti tj h,
    try_cook_hit circular_ck1 circular_ck2 (IHit p ti tj) h = None.
Proof.
  exact try_cook_hit_circular_hit_none.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_circ_split_qed_or_qex","title":"Locked circular Hit plus-root leftovers meet at p+ after split(t) (QED) or the join fails (QEX); discharged QED","file":"theories/CircularCookSplit.v","witness":"0007-circ-cook","board":"ADR-0007"} *)

Theorem ticket_0007_circ_split_qed_or_qex :
  (circ_leftover_eval (fst (circ_split locked_O1 locked_r locked_ti_plus)) 1
     = locked_p_plus
   /\ circ_leftover_eval (snd (circ_split locked_O1 locked_r locked_ti_plus)) 0
        = locked_p_plus
   /\ circ_leftover_eval (fst (circ_split locked_O2 locked_r locked_tj_plus)) 1
        = locked_p_plus
   /\ circ_leftover_eval (snd (circ_split locked_O2 locked_r locked_tj_plus)) 0
        = locked_p_plus
   /\ dist_sq locked_O1 locked_p_plus = locked_r * locked_r)
  \/
  circ_gamma locked_O1 locked_r locked_ti_plus <> locked_p_plus.
Proof.
  left.
  destruct (circ_split_join locked_O1 locked_r locked_ti_plus) as [H1 H2].
  destruct (circ_split_join locked_O2 locked_r locked_tj_plus) as [H3 H4].
  destruct locked_plus_gamma as [Hp1 Hp2].
  split; [rewrite H1; exact Hp1|].
  split; [rewrite H2; exact Hp1|].
  split; [rewrite H3; exact Hp2|].
  split; [rewrite H4; exact Hp2|].
  exact (proj1 locked_radical_on_circles).
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_circ_cook_step_qed_or_qex","title":"Locked circular Hit feeds the sidecar cook (QED) or try_cook_circ_hit declines a Hit (QEX); discharged QED on plus-root leftovers meeting at p+","file":"theories/CircularCookSplit.v","witness":"0007-circ-cook","board":"ADR-0007"} *)

Theorem ticket_0007_circ_cook_step_qed_or_qex :
  (try_cook_circ_hit locked_O1 locked_r locked_O2 locked_r
     (I_circles_gamma 0 0 5 7 0 5) hen_plus = Some cooked_circ_plus
   /\ circ_cooked_ok cooked_circ_plus hen_plus locked_p_plus
   /\ circular_gamma_status = CircGammaQEX)
  \/
  try_cook_circ_hit locked_O1 locked_r locked_O2 locked_r
    (I_circles_gamma 0 0 5 7 0 5) hen_plus = None.
Proof.
  left.
  split; [exact cooked_circ_plus_try|].
  split; [exact cooked_circ_plus_ok|].
  exact circular_gamma_host_still_qex.
Qed.

(* Touch / Empty / Decline cook (QED) or they allocate no hen (QEX).
   Discharged QEX — kiss stays a fenced scope arm, not a kiss procedure. *)
(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_circ_cook_scope_qed_or_qex","title":"Circular Touch/Empty/Decline cook (QED) or allocate no hen (QEX); discharged QEX; kiss is a fenced scope arm","file":"theories/CircularCookSplit.v","witness":"0007-circ-cook","board":"ADR-0007"} *)

Theorem ticket_0007_circ_cook_scope_qed_or_qex :
  (forall O1 r1 O2 r2 o h, try_cook_circ_hit O1 r1 O2 r2 o h <> None)
  \/
  (try_cook_circ_hit locked_O1 locked_r kiss_O2 locked_r
     (I_circles_gamma 0 0 5 10 0 5) hen_plus = None
   /\ try_cook_circ_hit locked_O1 locked_r locked_O2 locked_r
        (I_circles_gamma 0 0 5 20 0 5) hen_plus = None
   /\ try_cook_circ_hit locked_O1 locked_r locked_O2 locked_r
        (I_circles_gamma 0 0 5 0 0 5) hen_plus = None).
Proof.
  right.
  split; [exact locked_circ_touch_none|].
  split; [exact locked_circ_empty_none|].
  exact locked_circ_decline_none.
Qed.

Print Assumptions circ_split_join.
Print Assumptions circ_gamma_on_circle.
Print Assumptions cooked_circ_plus_ok.
Print Assumptions cooked_circ_plus_try.
Print Assumptions locked_circ_touch_none.
Print Assumptions circular_gamma_host_still_qex.
Print Assumptions host_try_cook_hit_still_none.
Print Assumptions ticket_0007_circ_split_qed_or_qex.
Print Assumptions ticket_0007_circ_cook_step_qed_or_qex.
Print Assumptions ticket_0007_circ_cook_scope_qed_or_qex.

(* -------------------------------------------------------------------------- *)
(* I.7 ticket-named QED ∨ QEX stops.                                          *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_circ_minus_qed_or_qex","title":"Locked circular Hit minus-root leftovers meet at p- after split(t) (QED) or the join fails (QEX); discharged QED; I.7 p- is a second Hit","file":"theories/CircularCookSplit.v","witness":"0007-I.7-mint-two","board":"ADR-0007"} *)

Theorem ticket_0007_circ_minus_qed_or_qex :
  (circ_leftover_eval (fst (circ_split locked_O1 locked_r locked_ti_minus)) 1
     = locked_p_minus
   /\ circ_leftover_eval (snd (circ_split locked_O1 locked_r locked_ti_minus)) 0
        = locked_p_minus
   /\ circ_leftover_eval (fst (circ_split locked_O2 locked_r locked_tj_minus)) 1
        = locked_p_minus
   /\ circ_leftover_eval (snd (circ_split locked_O2 locked_r locked_tj_minus)) 0
        = locked_p_minus
   /\ dist_sq locked_O1 locked_p_minus = locked_r * locked_r)
  \/
  circ_gamma locked_O1 locked_r locked_ti_minus <> locked_p_minus.
Proof.
  left.
  destruct (circ_split_join locked_O1 locked_r locked_ti_minus) as [H1 H2].
  destruct (circ_split_join locked_O2 locked_r locked_tj_minus) as [H3 H4].
  destruct locked_minus_gamma as [Hp1 Hp2].
  split; [rewrite H1; exact Hp1|].
  split; [rewrite H2; exact Hp1|].
  split; [rewrite H3; exact Hp2|].
  split; [rewrite H4; exact Hp2|].
  exact (proj1 (proj2 (proj2 locked_radical_on_circles))).
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_circ_mint_two_qed_or_qex","title":"Locked circular Hit allocates MintTwo across p+ and p- (QED) or try_cook_circ_hit_mint_two declines a Hit (QEX); discharged QED; I.7","file":"theories/CircularCookSplit.v","witness":"0007-I.7-mint-two","board":"ADR-0007"} *)

Theorem ticket_0007_circ_mint_two_qed_or_qex :
  (try_cook_circ_hit_mint_two locked_O1 locked_r locked_O2 locked_r
     (I_circles_gamma 0 0 5 7 0 5) = Some cooked_circ_mint_two
   /\ circ_mint_two_ok cooked_circ_mint_two
        hen_plus hen_minus locked_p_plus locked_p_minus
   /\ circular_gamma_status = CircGammaQEX)
  \/
  try_cook_circ_hit_mint_two locked_O1 locked_r locked_O2 locked_r
    (I_circles_gamma 0 0 5 7 0 5) = None.
Proof.
  left.
  split; [exact cooked_circ_mint_two_try|].
  split; [exact cooked_circ_mint_two_ok|].
  exact circular_gamma_host_still_qex.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_circ_shared_neq_kiss_qed_or_qex","title":"Leftover shared endpoint is Hit incidence not Touch (QED) or the join is a kiss (QEX); discharged QED; I.7 shared endpoint neq kiss","file":"theories/CircularCookSplit.v","witness":"0007-I.7-mint-two","board":"ADR-0007"} *)

Theorem ticket_0007_circ_shared_neq_kiss_qed_or_qex :
  (circ_cooked_meets cooked_circ_plus locked_p_plus
   /\ circ_cooked_meets cooked_circ_minus locked_p_minus
   /\ locked_p_plus <> locked_p_minus
   /\ I_circles_gamma 0 0 5 7 0 5 <>
        ICircGTouch hen_plus locked_p_plus locked_ti_plus locked_tj_plus)
  \/
  I_circles_gamma 0 0 5 7 0 5 =
    ICircGTouch hen_plus locked_p_plus locked_ti_plus locked_tj_plus.
Proof.
  left.
  exact leftover_shared_endpoint_not_touch.
Qed.

(* Touch / Empty / Decline still allocate no hen under MintTwo (QED)
   or they mint nothing (QEX). Discharged QEX — same fence as #686. *)
(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_circ_mint_two_scope_qed_or_qex","title":"MintTwo Circular Touch/Empty/Decline cook (QED) or allocate no hen (QEX); discharged QEX; I.7 Empty/Decline/Touch mint nothing","file":"theories/CircularCookSplit.v","witness":"0007-I.7-mint-two","board":"ADR-0007"} *)

Theorem ticket_0007_circ_mint_two_scope_qed_or_qex :
  (forall O1 r1 O2 r2 o, try_cook_circ_hit_mint_two O1 r1 O2 r2 o <> None)
  \/
  (try_cook_circ_hit_mint_two locked_O1 locked_r kiss_O2 locked_r
     (I_circles_gamma 0 0 5 10 0 5) = None
   /\ try_cook_circ_hit_mint_two locked_O1 locked_r locked_O2 locked_r
        (I_circles_gamma 0 0 5 20 0 5) = None
   /\ try_cook_circ_hit_mint_two locked_O1 locked_r locked_O2 locked_r
        (I_circles_gamma 0 0 5 0 0 5) = None).
Proof.
  right.
  split; [exact locked_circ_mint_two_touch_none|].
  split; [exact locked_circ_mint_two_empty_none|].
  exact locked_circ_mint_two_decline_none.
Qed.

Print Assumptions cooked_circ_minus_ok.
Print Assumptions cooked_circ_mint_two_ok.
Print Assumptions leftover_shared_endpoint_not_touch.
Print Assumptions ticket_0007_circ_minus_qed_or_qex.
Print Assumptions ticket_0007_circ_mint_two_qed_or_qex.
Print Assumptions ticket_0007_circ_shared_neq_kiss_qed_or_qex.
Print Assumptions ticket_0007_circ_mint_two_scope_qed_or_qex.

(* -------------------------------------------------------------------------- *)
(* I.1 Fence: four objects pairwise unequal by observation, not a             *)
(* type synonym. Touch ≠ IHit. Circular Empty ≠ Decline. Host                 *)
(* I_gloss / CircGamma stays QEX.                                             *)
(*                                                                            *)
(*   1. I_circles_z / I_CIRCULAR — Z^6 classifier; hens 0/1; no t            *)
(*   2. I_circles_gamma — locked full-circle witness with t on γ_full        *)
(*   3. sidecar cook — same IResult-shaped cook, sidecar Γ                   *)
(*   4. I_gloss — host I_ok + CircGamma; undefined while CircGamma QEX       *)
(* -------------------------------------------------------------------------- *)

(* z ≠ gamma: same Z^6 input. z Hit is hens-only; gamma Hit carries t
   with γ(t)=p*. *)
Lemma i1_z_neq_gamma_obs :
  I_circles_z 0 0 5 7 0 5 = IZHit hen_plus hen_minus
  /\ I_circles_gamma 0 0 5 7 0 5 =
       ICircGHit hen_plus locked_p_plus
         (circ_t locked_O1 locked_p_plus) (circ_t locked_O2 locked_p_plus)
         hen_minus locked_p_minus
         (circ_t locked_O1 locked_p_minus) (circ_t locked_O2 locked_p_minus)
  /\ on_full_circle locked_O1 locked_r
       (circ_t locked_O1 locked_p_plus) locked_p_plus.
Proof.
  split; [exact locked_I_circles_z_hit|].
  split; [exact locked_I_circles_gamma_hit|].
  exact (proj1 locked_hit_plus_on_gamma).
Qed.

(* z ≠ sidecar: Z classifies hens; sidecar cooks leftovers. *)
Lemma i1_z_neq_sidecar_obs :
  I_circles_z 0 0 5 7 0 5 = IZHit hen_plus hen_minus
  /\ try_cook_circ_hit_mint_two locked_O1 locked_r locked_O2 locked_r
       (I_circles_gamma 0 0 5 7 0 5) = Some cooked_circ_mint_two.
Proof.
  split; [exact locked_I_circles_z_hit|].
  exact cooked_circ_mint_two_try.
Qed.

(* z ≠ I_gloss: Z Hit is defined; host CircGamma is QEX. *)
Lemma i1_z_neq_gloss_obs :
  I_circles_z 0 0 5 7 0 5 = IZHit hen_plus hen_minus
  /\ circular_gamma_status = CircGammaQEX.
Proof.
  split; [exact locked_I_circles_z_hit|].
  exact circular_gamma_host_still_qex.
Qed.

(* gamma ≠ sidecar: classifier Hit vs cook leftovers; Empty does
   not cook. *)
Lemma i1_gamma_neq_sidecar_obs :
  I_circles_gamma 0 0 5 7 0 5 =
    ICircGHit hen_plus locked_p_plus
      (circ_t locked_O1 locked_p_plus) (circ_t locked_O2 locked_p_plus)
      hen_minus locked_p_minus
      (circ_t locked_O1 locked_p_minus) (circ_t locked_O2 locked_p_minus)
  /\ try_cook_circ_hit_mint_two locked_O1 locked_r locked_O2 locked_r
       (I_circles_gamma 0 0 5 7 0 5) = Some cooked_circ_mint_two
  /\ try_cook_circ_hit_mint_two locked_O1 locked_r locked_O2 locked_r
       (I_circles_gamma 0 0 5 20 0 5) = None.
Proof.
  split; [exact locked_I_circles_gamma_hit|].
  split; [exact cooked_circ_mint_two_try|].
  exact locked_circ_mint_two_empty_none.
Qed.

(* gamma ≠ I_gloss: sidecar t on γ_full; host CircGamma QEX. *)
Lemma i1_gamma_neq_gloss_obs :
  on_full_circle locked_O1 locked_r
    (circ_t locked_O1 locked_p_plus) locked_p_plus
  /\ circular_gamma_status = CircGammaQEX.
Proof.
  split; [exact (proj1 locked_hit_plus_on_gamma)|].
  exact circular_gamma_host_still_qex.
Qed.

(* sidecar ≠ I_gloss: sidecar cooks; host try_cook_hit is None. *)
Lemma i1_sidecar_neq_gloss_obs :
  try_cook_circ_hit_mint_two locked_O1 locked_r locked_O2 locked_r
    (I_circles_gamma 0 0 5 7 0 5) = Some cooked_circ_mint_two
  /\ (forall p ti tj h,
        try_cook_hit circular_ck1 circular_ck2 (IHit p ti tj) h = None)
  /\ circular_gamma_status = CircGammaQEX.
Proof.
  split; [exact cooked_circ_mint_two_try|].
  split; [exact host_try_cook_hit_still_none|].
  exact circular_gamma_host_still_qex.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_i1_fence_qed_or_qex","title":"Four I objects are pairwise unequal by locked observation (QED) or they collapse (QEX); discharged QED; I.1 fence not a type synonym","file":"theories/CircularCookSplit.v","witness":"0007-I.1-fence","board":"ADR-0007"} *)

Theorem ticket_0007_i1_fence_qed_or_qex :
  ((I_circles_z 0 0 5 7 0 5 = IZHit hen_plus hen_minus
    /\ I_circles_gamma 0 0 5 7 0 5 =
         ICircGHit hen_plus locked_p_plus
           (circ_t locked_O1 locked_p_plus) (circ_t locked_O2 locked_p_plus)
           hen_minus locked_p_minus
           (circ_t locked_O1 locked_p_minus) (circ_t locked_O2 locked_p_minus)
    /\ on_full_circle locked_O1 locked_r
         (circ_t locked_O1 locked_p_plus) locked_p_plus)
   /\ (I_circles_z 0 0 5 7 0 5 = IZHit hen_plus hen_minus
       /\ try_cook_circ_hit_mint_two locked_O1 locked_r locked_O2 locked_r
            (I_circles_gamma 0 0 5 7 0 5) = Some cooked_circ_mint_two)
   /\ (I_circles_z 0 0 5 7 0 5 = IZHit hen_plus hen_minus
       /\ circular_gamma_status = CircGammaQEX)
   /\ (I_circles_gamma 0 0 5 7 0 5 =
         ICircGHit hen_plus locked_p_plus
           (circ_t locked_O1 locked_p_plus) (circ_t locked_O2 locked_p_plus)
           hen_minus locked_p_minus
           (circ_t locked_O1 locked_p_minus) (circ_t locked_O2 locked_p_minus)
       /\ try_cook_circ_hit_mint_two locked_O1 locked_r locked_O2 locked_r
            (I_circles_gamma 0 0 5 7 0 5) = Some cooked_circ_mint_two
       /\ try_cook_circ_hit_mint_two locked_O1 locked_r locked_O2 locked_r
            (I_circles_gamma 0 0 5 20 0 5) = None)
   /\ (on_full_circle locked_O1 locked_r
         (circ_t locked_O1 locked_p_plus) locked_p_plus
       /\ circular_gamma_status = CircGammaQEX)
   /\ (try_cook_circ_hit_mint_two locked_O1 locked_r locked_O2 locked_r
         (I_circles_gamma 0 0 5 7 0 5) = Some cooked_circ_mint_two
       /\ (forall p ti tj h,
             try_cook_hit circular_ck1 circular_ck2 (IHit p ti tj) h = None)
       /\ circular_gamma_status = CircGammaQEX))
  \/
  (circular_gamma_status = CircGammaDischarged
   /\ I_circles_z 0 0 5 7 0 5 = IZDecline).
Proof.
  left.
  split; [exact i1_z_neq_gamma_obs|].
  split; [exact i1_z_neq_sidecar_obs|].
  split; [exact i1_z_neq_gloss_obs|].
  split; [exact i1_gamma_neq_sidecar_obs|].
  split; [exact i1_gamma_neq_gloss_obs|].
  exact i1_sidecar_neq_gloss_obs.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_touch_neq_ihit_qed_or_qex","title":"Circular Touch differs from proper-cross Hit (QED) or the kiss is a Hit (QEX); discharged QED; I.1 Touch neq IHit","file":"theories/CircularCookSplit.v","witness":"0007-I.1-fence","board":"ADR-0007"} *)

Theorem ticket_0007_touch_neq_ihit_qed_or_qex :
  (I_circles_z 0 0 5 10 0 5 = IZTouch hen_plus
   /\ I_circles_z 0 0 5 7 0 5 = IZHit hen_plus hen_minus
   /\ IZTouch hen_plus <> IZHit hen_plus hen_minus
   /\ I_circles_gamma 0 0 5 10 0 5 =
        ICircGTouch hen_plus kiss_p
          (circ_t locked_O1 kiss_p) (circ_t kiss_O2 kiss_p)
   /\ I_circles_gamma 0 0 5 7 0 5 =
        ICircGHit hen_plus locked_p_plus
          (circ_t locked_O1 locked_p_plus) (circ_t locked_O2 locked_p_plus)
          hen_minus locked_p_minus
          (circ_t locked_O1 locked_p_minus) (circ_t locked_O2 locked_p_minus)
   /\ ICircGTouch hen_plus kiss_p
        (circ_t locked_O1 kiss_p) (circ_t kiss_O2 kiss_p) <>
      ICircGHit hen_plus locked_p_plus
        (circ_t locked_O1 locked_p_plus) (circ_t locked_O2 locked_p_plus)
        hen_minus locked_p_minus
        (circ_t locked_O1 locked_p_minus) (circ_t locked_O2 locked_p_minus))
  \/
  I_circles_z 0 0 5 10 0 5 = IZHit hen_plus hen_minus.
Proof.
  left.
  split; [exact locked_external_kiss_is_touch|].
  split; [exact locked_I_circles_z_hit|].
  split; [apply IZTouch_neq_IZHit|].
  split; [exact locked_I_circles_gamma_touch|].
  split; [exact locked_I_circles_gamma_hit|].
  apply ICircGTouch_neq_ICircGHit.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_empty_neq_decline_circ_qed_or_qex","title":"Circular Empty differs from Decline (QED) or they coincide (QEX); discharged QED; I.1 circular Empty neq Decline","file":"theories/CircularCookSplit.v","witness":"0007-I.1-fence","board":"ADR-0007"} *)

Theorem ticket_0007_empty_neq_decline_circ_qed_or_qex :
  (I_circles_z 0 0 5 20 0 5 = IZEmpty
   /\ I_circles_z 0 0 5 0 0 5 = IZDecline
   /\ IZEmpty <> IZDecline
   /\ I_circles_gamma 0 0 5 20 0 5 = ICircGEmpty
   /\ I_circles_gamma 0 0 5 0 0 5 = ICircGDecline
   /\ ICircGEmpty <> ICircGDecline)
  \/
  IZEmpty = IZDecline.
Proof.
  left.
  split; [exact locked_disjoint_is_empty|].
  split; [exact locked_coincident_is_decline|].
  split; [exact IZEmpty_neq_IZDecline|].
  split; [exact locked_I_circles_gamma_empty|].
  split; [exact locked_I_circles_gamma_decline|].
  exact ICircGEmpty_neq_ICircGDecline.
Qed.

Print Assumptions i1_z_neq_gamma_obs.
Print Assumptions i1_sidecar_neq_gloss_obs.
Print Assumptions ticket_0007_i1_fence_qed_or_qex.
Print Assumptions ticket_0007_touch_neq_ihit_qed_or_qex.
Print Assumptions ticket_0007_empty_neq_decline_circ_qed_or_qex.
