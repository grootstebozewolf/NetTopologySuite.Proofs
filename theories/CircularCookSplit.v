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
   QEX: Touch / Empty / Decline allocate no hen (kiss is a fenced
   scope arm — not a CRV-TOUCH kiss decision). Host try_cook_hit still
   declines circular eggs (Adr0007NodingEpic.v :
   ticket_0007_circ_host_cook_qed_or_qex). CircGamma stays QEX
   (CircularCook.v : circular_gamma_is_qex).

   Honesty fences:
     constructed chord–chord 𝓘 ≠ I_circles_z / I_CIRCULAR ≠ this
     sidecar cook ≠ glossary 𝓘 with host γ / t.
     Not first cook scope. Not a noder. Not ArcSplitAtNode (that is
     the N-AA chord-sign partition lane). Not a remint of
     CurveSegment / Exact* / Dart / Hobby / leftover_width.
     Do not fake atan2-free host γ.

   WITNESS topic: overlay · claimId: 0007 · witness: 0007-circ-cook
   board: ADR-0007
   4-axiom (atan2 / Classical_Prop.classic via CircularCookHit).
   No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import ZArith Reals Lra.
From NTS.Proofs Require Import Distance SheetHenCook CircularCookZ
  CircularCook CircularCookHit.
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
  let s1 := circ_split O1 r1 ti in
  let s2 := circ_split O2 r2 tj in
  mkCircCookedPair h (fst s1) (snd s1) (fst s2) (snd s2).

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
  unfold circ_cooked_ok, circ_cooked_meets, cooked_circ_plus,
         cook_circ_root.
  split; [reflexivity|].
  destruct (circ_split_join locked_O1 locked_r locked_ti_plus) as [HL1 HR1].
  destruct (circ_split_join locked_O2 locked_r locked_tj_plus) as [HL2 HR2].
  destruct locked_plus_gamma as [Hp1 Hp2].
  repeat split.
  - rewrite HL1. exact Hp1.
  - rewrite HR1. exact Hp1.
  - rewrite HL2. exact Hp2.
  - rewrite HR2. exact Hp2.
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
