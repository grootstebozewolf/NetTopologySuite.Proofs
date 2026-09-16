(* ============================================================================
   NetTopologySuite.Proofs.CircularCookLeftoverTwoHit
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: circular leftover bag for |H|=2
   plus noded G on those leftovers (claimId 0007-circ-leftover-two-hit).

   Depth-first curve lane. Reuses the *shape* of the chord leftover bag
   (#760 pair step gated by interior 𝓘 Hit, Decline idle; #761 hit
   count). Does not remint chord ρ as LoopDischarged. Does not reuse
   leftover_quad_width. Does not claim ∀-bag decrease — only the locked
   vesica lens is inhabited (measure 2 → 1 → 0).

   Unique circ×circ Hit already splits and stays circular
   (CircularCookMkCirc / cook_hit_circs). This letter is the two
   interior Hits case: open windows contain both circle–circle points.

   QED: two-Hit circ bag steps on the locked lens + noded G on that
   example. Endpoint-only meets Decline. Cocircular overlap Decline,
   not a Hit. After the two Hits, leftover pairs have no interior Hit;
   leftover circular eggs meet only at the two point-hens.
   QEX: general circ bag-term / LoopDischarged-for-circ, kiss/share
   identity, chord LeftoverBagTermArm. cook_loop_status stays
   LoopObligation.

   Honesty fences:
     Do not fake LoopDischarged. Do not remint leftover_quad_width.
     Do not remint CircGamma / ι / first-cook expand / NURBS / Overlay.
     Host CircGamma is CircGammaDischarged (MkCirc). Reuse circ_split /
     I_ok / cook_hit_circs. Sidecar I_circles_gamma / CircLeftover are
     not this host bag. Not OverlayNG / C API / GEOS.

   WITNESS topic: overlay · claimId: 0007-circ-leftover-two-hit
   witness: 0007-circ-leftover-two-hit
   board: ADR-0007
   3-axiom host. No Axiom / Parameter / stub.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List Rtrigo_calc Rtrigo_facts Psatz.
From NTS.Proofs Require Import Distance SheetHenCook CircularCookMkCirc.
From NTS.Proofs Require Import SheetHenCookLoop.
Import ListNotations.
Local Open Scope R_scope.

(* WITNESS: campaign=circ-leftover rung=two-hit claim=0007-circ-leftover-two-hit
   file=theories/CircularCookLeftoverTwoHit.v
   kind=QED-locked-lens-QEX-general
   park=LeftoverBagTermArm
   measure=2-1-0
   not=LoopDischarged,leftover_quad_width,forall-bag-decrease
   not=kiss-share-as-width,CircGamma-remint,Overlay,NURBS
   note=letter-not-rho-discharge *)

(* -------------------------------------------------------------------------- *)
(* Circ leftover span: one parent CircularEgg restricted to [t0, t1].         *)
(* leftover egg reuses host circ_split reparam (children stay circular).      *)
(* -------------------------------------------------------------------------- *)

Record circ_leftover_span : Type := mkCircLeftoverSpan {
  cls_parent : CircularEgg;
  cls_t0 : R;
  cls_t1 : R
}.

Definition circ_leftover_span_ok (s : circ_leftover_span) : Prop :=
  cls_t0 s < cls_t1 s.

Definition circ_leftover_interior (u : R) : Prop :=
  0 < u < 1.

Definition circ_leftover_span_parent (c : CircularEgg) : circ_leftover_span :=
  mkCircLeftoverSpan c 0 1.

Definition circ_leftover_egg (s : circ_leftover_span) : CircularEgg :=
  mkCircularEgg (circ_o (cls_parent s)) (circ_r (cls_parent s))
    (circ_theta0 (cls_parent s) + cls_t0 s * circ_sweep (cls_parent s))
    ((cls_t1 s - cls_t0 s) * circ_sweep (cls_parent s)).

Definition circ_leftover_span_at (s : circ_leftover_span) (u : R) : R :=
  cls_t0 s + u * (cls_t1 s - cls_t0 s).

Definition circ_leftover_span_lo (s : circ_leftover_span) (u : R)
  : circ_leftover_span :=
  mkCircLeftoverSpan (cls_parent s) (cls_t0 s) (circ_leftover_span_at s u).

Definition circ_leftover_span_hi (s : circ_leftover_span) (u : R)
  : circ_leftover_span :=
  mkCircLeftoverSpan (cls_parent s) (circ_leftover_span_at s u) (cls_t1 s).

Definition circ_same_circle (c1 c2 : CircularEgg) : Prop :=
  circ_o c1 = circ_o c2 /\ circ_r c1 = circ_r c2.

Definition circ_parent_open (s : circ_leftover_span) (t : R) : Prop :=
  cls_t0 s < t < cls_t1 s.

Lemma circ_leftover_egg_or :
  forall s,
    circ_o (circ_leftover_egg s) = circ_o (cls_parent s) /\
    circ_r (circ_leftover_egg s) = circ_r (cls_parent s).
Proof.
  intros s. unfold circ_leftover_egg. cbn. split; reflexivity.
Qed.

Lemma circ_leftover_eval_parent :
  forall s u,
    circ_eval (circ_leftover_egg s) u =
    circ_eval (cls_parent s) (circ_leftover_span_at s u).
Proof.
  intros [c t0 t1] u.
  unfold circ_leftover_egg, circ_leftover_span_at, circ_eval.
  cbn [circ_o circ_r circ_theta0 circ_sweep cls_parent cls_t0 cls_t1].
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma circ_leftover_egg_parent :
  forall c, circ_leftover_egg (circ_leftover_span_parent c) = c.
Proof.
  intros [o r th sw].
  unfold circ_leftover_egg, circ_leftover_span_parent.
  cbn.
  apply (f_equal2
           (fun th' sw' => mkCircularEgg o r th' sw'));
    ring.
Qed.

Lemma circ_leftover_span_parent_ok :
  forall c, circ_leftover_span_ok (circ_leftover_span_parent c).
Proof.
  intros c. unfold circ_leftover_span_ok, circ_leftover_span_parent. simpl. lra.
Qed.

Lemma circ_leftover_span_parent_at :
  forall c u, circ_leftover_span_at (circ_leftover_span_parent c) u = u.
Proof.
  intros c u.
  unfold circ_leftover_span_at, circ_leftover_span_parent.
  simpl. ring.
Qed.

Lemma circ_leftover_split_matches_circ_split :
  forall c t,
    circ_leftover_egg (circ_leftover_span_lo (circ_leftover_span_parent c) t)
    = fst (circ_split c t) /\
    circ_leftover_egg (circ_leftover_span_hi (circ_leftover_span_parent c) t)
    = snd (circ_split c t).
Proof.
  intros [o r th sw] t.
  unfold circ_leftover_egg, circ_leftover_span_lo, circ_leftover_span_hi,
         circ_leftover_span_at, circ_leftover_span_parent, circ_split.
  cbn. split; apply (f_equal2 (fun th' sw' => mkCircularEgg o r th' sw')); ring.
Qed.

Lemma circ_leftover_children_stay_circular :
  forall s u,
    egg_class (MkCirc (circ_leftover_egg (circ_leftover_span_lo s u)))
    = EggCircularArc /\
    egg_class (MkCirc (circ_leftover_egg (circ_leftover_span_hi s u)))
    = EggCircularArc.
Proof.
  intros s u. split; reflexivity.
Qed.

Lemma unique_mkcirc_children_circular :
  egg_class (ck_egg (cp_left1 cooked_mkcirc)) = EggCircularArc /\
  egg_class (ck_egg (cp_right1 cooked_mkcirc)) = EggCircularArc /\
  egg_class (ck_egg (cp_left2 cooked_mkcirc)) = EggCircularArc /\
  egg_class (ck_egg (cp_right2 cooked_mkcirc)) = EggCircularArc.
Proof.
  repeat split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Pair Hit on two leftover circ eggs, or Decline and leave the bag.          *)
(* Interior 𝓘 Hit (0<u<1). Cocircular overlap is not a Hit.                  *)
(* -------------------------------------------------------------------------- *)

Definition circ_leftover_pair_hit
  (a b : circ_leftover_span) (p : Point) (ua ub : R) : Prop :=
  circ_leftover_span_ok a /\
  circ_leftover_span_ok b /\
  circ_leftover_interior ua /\
  circ_leftover_interior ub /\
  ~ circ_same_circle (circ_leftover_egg a) (circ_leftover_egg b) /\
  I_ok (MkCirc (circ_leftover_egg a)) (MkCirc (circ_leftover_egg b))
       (IHit p ua ub).

Inductive circ_leftover_bag : Type :=
| CBagNil
| CBagCons (s : circ_leftover_span) (rest : circ_leftover_bag).

Fixpoint cbag_count (b : circ_leftover_bag) : nat :=
  match b with
  | CBagNil => 0
  | CBagCons _ r => S (cbag_count r)
  end.

Fixpoint cbag_nth (b : circ_leftover_bag) (n : nat)
  : option circ_leftover_span :=
  match b, n with
  | CBagNil, _ => None
  | CBagCons s _, O => Some s
  | CBagCons _ r, S n' => cbag_nth r n'
  end.

Fixpoint cbag_remove (b : circ_leftover_bag) (n : nat)
  : circ_leftover_bag :=
  match b, n with
  | CBagNil, _ => CBagNil
  | CBagCons _ r, O => r
  | CBagCons s r, S n' => CBagCons s (cbag_remove r n')
  end.

Definition cbag_remove_two (b : circ_leftover_bag) (i j : nat)
  : circ_leftover_bag :=
  if Nat.ltb i j
  then cbag_remove (cbag_remove b j) i
  else cbag_remove (cbag_remove b i) j.

Definition cbag_pair_replace
  (b : circ_leftover_bag) (i j : nat) (ua ub : R)
  : option circ_leftover_bag :=
  match cbag_nth b i, cbag_nth b j with
  | Some a, Some bsp =>
      if Nat.eqb i j then None
      else
        Some
          (CBagCons (circ_leftover_span_lo a ua)
            (CBagCons (circ_leftover_span_hi a ua)
              (CBagCons (circ_leftover_span_lo bsp ub)
                (CBagCons (circ_leftover_span_hi bsp ub)
                  (cbag_remove_two b i j)))))
  | _, _ => None
  end.

Definition circ_leftover_pair_step_ok
  (b : circ_leftover_bag) (i j : nat) (p : Point) (ua ub : R) : Prop :=
  exists a bsp,
    cbag_nth b i = Some a /\
    cbag_nth b j = Some bsp /\
    i <> j /\
    circ_leftover_pair_hit a bsp p ua ub.

Definition circ_leftover_pair_decline
  (b : circ_leftover_bag) (i j : nat) : Prop :=
  exists a bsp,
    cbag_nth b i = Some a /\
    cbag_nth b j = Some bsp /\
    i <> j /\
    (forall p ua ub, ~ circ_leftover_pair_hit a bsp p ua ub).

Inductive circ_leftover_bag_step
  : circ_leftover_bag -> circ_leftover_bag -> Prop :=
| CStepHit : forall b b' i j p ua ub,
    circ_leftover_pair_step_ok b i j p ua ub ->
    cbag_pair_replace b i j ua ub = Some b' ->
    circ_leftover_bag_step b b'
| CStepDecline : forall b i j,
    circ_leftover_pair_decline b i j ->
    circ_leftover_bag_step b b.

(* Measure: count of (i,j,p) interior Hits, i<j. Not leftover_quad_width. *)
Definition circ_leftover_hit_occ
  (b : circ_leftover_bag) (i j : nat) (p : Point) : Prop :=
  (i < j)%nat /\
  exists ua ub, circ_leftover_pair_step_ok b i j p ua ub.

Definition circ_leftover_hit_listing
  (b : circ_leftover_bag) (hits : list (nat * nat * Point)) : Prop :=
  (forall ijp, In ijp hits ->
     circ_leftover_hit_occ b (fst (fst ijp)) (snd (fst ijp)) (snd ijp)) /\
  (forall i j p, circ_leftover_hit_occ b i j p -> In (i, j, p) hits) /\
  NoDup hits.

Definition circ_leftover_bag_measure
  (b : circ_leftover_bag) (n : nat) : Prop :=
  exists hits, circ_leftover_hit_listing b hits /\ length hits = n.

Lemma circ_leftover_bag_measure_nat_wf :
  well_founded Nat.lt.
Proof.
  exact Nat.lt_wf_0.
Qed.

Lemma cbag_nth_some_lt :
  forall b n s,
    cbag_nth b n = Some s ->
    (n < cbag_count b)%nat.
Proof.
  induction b as [|s0 rest IH]; intros n s Hnth.
  - discriminate.
  - destruct n as [|n'].
    + simpl. lia.
    + simpl in Hnth. apply IH in Hnth. simpl. lia.
Qed.

Lemma circ_leftover_hit_occ_bounded :
  forall b i j p,
    circ_leftover_hit_occ b i j p ->
    (i < j < cbag_count b)%nat.
Proof.
  intros b i j p [Hij [ua [ub [a [bsp [Ha [Hb _]]]]]]].
  split; [exact Hij|].
  apply cbag_nth_some_lt in Hb.
  exact Hb.
Qed.

Lemma circ_leftover_hit_listing_same_in :
  forall b h1 h2 ijp,
    circ_leftover_hit_listing b h1 ->
    circ_leftover_hit_listing b h2 ->
    In ijp h1 <-> In ijp h2.
Proof.
  intros b h1 h2 ijp [Hs1 [Hc1 _]] [Hs2 [Hc2 _]].
  split; intros Hin.
  - apply Hs1 in Hin. destruct ijp as [[i j] p]. simpl in Hin. apply Hc2. exact Hin.
  - apply Hs2 in Hin. destruct ijp as [[i j] p]. simpl in Hin. apply Hc1. exact Hin.
Qed.

Lemma circ_leftover_bag_measure_unique :
  forall b n m,
    circ_leftover_bag_measure b n ->
    circ_leftover_bag_measure b m ->
    n = m.
Proof.
  intros b n m [h1 [L1 E1]] [h2 [L2 E2]].
  subst n m.
  apply Nat.le_antisymm.
  - apply NoDup_incl_length.
    + destruct L1 as [_ [_ N1]]. exact N1.
    + intros x Hx.
      apply (proj1 (circ_leftover_hit_listing_same_in b h1 h2 x L1 L2)).
      exact Hx.
  - apply NoDup_incl_length.
    + destruct L2 as [_ [_ N2]]. exact N2.
    + intros x Hx.
      apply (proj1 (circ_leftover_hit_listing_same_in b h2 h1 x L2 L1)).
      exact Hx.
Qed.

(* Locked-only decrease. Not a ∀-bag measure. *)
Definition circ_leftover_bag_term_forall : Prop :=
  forall b b' n m,
    circ_leftover_bag_step b b' ->
    circ_leftover_bag_measure b n ->
    circ_leftover_bag_measure b' m ->
    (m < n)%nat.

(* -------------------------------------------------------------------------- *)
(* Locked vesica: unit circles (0,0) and (1,0), right/left semicircles.       *)
(* Both circle–circle points sit in the open windows.                         *)
(* -------------------------------------------------------------------------- *)

Definition locked_twohit_A : CircularEgg :=
  mkCircularEgg (mkPoint 0 0) 1 (- (PI / 2)) PI.

Definition locked_twohit_B : CircularEgg :=
  mkCircularEgg (mkPoint 1 0) 1 (PI / 2) PI.

Definition locked_p_plus : Point :=
  mkPoint (1 / 2) (sqrt 3 / 2).

Definition locked_p_minus : Point :=
  mkPoint (1 / 2) (- sqrt 3 / 2).

Definition locked_twohit_A_span : circ_leftover_span :=
  circ_leftover_span_parent locked_twohit_A.

Definition locked_twohit_B_span : circ_leftover_span :=
  circ_leftover_span_parent locked_twohit_B.

Definition locked_circ_parent_bag : circ_leftover_bag :=
  CBagCons locked_twohit_A_span (CBagCons locked_twohit_B_span CBagNil).

Lemma point_eq_xy :
  forall p q, px p = px q -> py p = py q -> p = q.
Proof.
  intros [x1 y1] [x2 y2] Hx Hy. simpl in *. subst. reflexivity.
Qed.

Lemma sin_neg_on_neg :
  forall x, - PI < x < 0 -> sin x < 0.
Proof.
  intros x [Hlo Hhi].
  apply sin_lt_0_var; lra.
Qed.

Lemma locked_twohit_A_at_0 :
  circ_eval locked_twohit_A 0 = mkPoint 0 (-1).
Proof.
  unfold circ_eval, locked_twohit_A.
  cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  rewrite Rmult_0_l, Rplus_0_r, cos_neg, sin_neg, cos_PI2, sin_PI2.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma locked_twohit_A_at_1 :
  circ_eval locked_twohit_A 1 = mkPoint 0 1.
Proof.
  unfold circ_eval, locked_twohit_A.
  cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  replace (- (PI / 2) + 1 * PI) with (PI / 2) by (pose proof PI_RGT_0; field).
  rewrite cos_PI2, sin_PI2.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma locked_twohit_B_at_0 :
  circ_eval locked_twohit_B 0 = mkPoint 1 1.
Proof.
  unfold circ_eval, locked_twohit_B.
  cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  rewrite Rmult_0_l, Rplus_0_r, cos_PI2, sin_PI2.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma locked_twohit_B_at_1 :
  circ_eval locked_twohit_B 1 = mkPoint 1 (-1).
Proof.
  unfold circ_eval, locked_twohit_B.
  cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  replace (PI / 2 + 1 * PI) with (PI + PI / 2) by (pose proof PI_RGT_0; field).
  rewrite cos_plus, sin_plus, cos_PI, sin_PI, cos_PI2, sin_PI2.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma locked_A_angle_plus :
  - (PI / 2) + (5 / 6) * PI = PI / 3.
Proof.
  pose proof PI_RGT_0. field; lra.
Qed.

Lemma locked_A_angle_minus :
  - (PI / 2) + (1 / 6) * PI = - (PI / 3).
Proof.
  pose proof PI_RGT_0. field; lra.
Qed.

Lemma locked_B_angle_plus :
  PI / 2 + (1 / 6) * PI = 2 * PI / 3.
Proof.
  pose proof PI_RGT_0. field; lra.
Qed.

Lemma locked_B_angle_minus :
  PI / 2 + (5 / 6) * PI = 4 * PI / 3.
Proof.
  pose proof PI_RGT_0. field; lra.
Qed.

Lemma cos_4PI3 : cos (4 * PI / 3) = - (1 / 2).
Proof.
  replace (4 * PI / 3) with (PI + PI / 3) by (pose proof PI_RGT_0; field; lra).
  rewrite cos_plus, cos_PI, sin_PI, cos_PI3, sin_PI3. ring.
Qed.

Lemma sin_4PI3 : sin (4 * PI / 3) = - (sqrt 3 / 2).
Proof.
  replace (4 * PI / 3) with (PI + PI / 3) by (pose proof PI_RGT_0; field; lra).
  rewrite sin_plus, cos_PI, sin_PI, cos_PI3, sin_PI3. ring.
Qed.

Lemma locked_twohit_A_at_plus :
  circ_eval locked_twohit_A (5 / 6) = locked_p_plus.
Proof.
  unfold circ_eval, locked_twohit_A, locked_p_plus.
  cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  rewrite locked_A_angle_plus, cos_PI3, sin_PI3.
  apply (f_equal2 mkPoint); field.
Qed.

Lemma locked_twohit_A_at_minus :
  circ_eval locked_twohit_A (1 / 6) = locked_p_minus.
Proof.
  unfold circ_eval, locked_twohit_A, locked_p_minus.
  cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  rewrite locked_A_angle_minus, cos_neg, sin_neg, cos_PI3, sin_PI3.
  apply (f_equal2 mkPoint); field.
Qed.

Lemma locked_twohit_B_at_plus :
  circ_eval locked_twohit_B (1 / 6) = locked_p_plus.
Proof.
  unfold circ_eval, locked_twohit_B, locked_p_plus.
  cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  rewrite locked_B_angle_plus, cos_2PI3, sin_2PI3.
  apply (f_equal2 mkPoint); field.
Qed.

Lemma locked_twohit_B_at_minus :
  circ_eval locked_twohit_B (5 / 6) = locked_p_minus.
Proof.
  unfold circ_eval, locked_twohit_B, locked_p_minus.
  cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  rewrite locked_B_angle_minus, cos_4PI3, sin_4PI3.
  apply (f_equal2 mkPoint); field.
Qed.

Lemma locked_p_plus_neq_minus :
  locked_p_plus <> locked_p_minus.
Proof.
  unfold locked_p_plus, locked_p_minus. intros H. injection H as Hy.
  pose proof (Rlt_0_sqrt 3 ltac:(lra)) as Hs.
  lra.
Qed.

Lemma locked_on_A_plus :
  on_circ locked_twohit_A (5 / 6) locked_p_plus.
Proof.
  unfold on_circ. split; [lra|].
  symmetry. exact locked_twohit_A_at_plus.
Qed.

Lemma locked_on_A_minus :
  on_circ locked_twohit_A (1 / 6) locked_p_minus.
Proof.
  unfold on_circ. split; [lra|].
  symmetry. exact locked_twohit_A_at_minus.
Qed.

Lemma locked_on_B_plus :
  on_circ locked_twohit_B (1 / 6) locked_p_plus.
Proof.
  unfold on_circ. split; [lra|].
  symmetry. exact locked_twohit_B_at_plus.
Qed.

Lemma locked_on_B_minus :
  on_circ locked_twohit_B (5 / 6) locked_p_minus.
Proof.
  unfold on_circ. split; [lra|].
  symmetry. exact locked_twohit_B_at_minus.
Qed.

Lemma locked_twohit_I_ok_plus :
  I_ok (MkCirc locked_twohit_A) (MkCirc locked_twohit_B)
       (IHit locked_p_plus (5 / 6) (1 / 6)).
Proof.
  unfold I_ok. split; [exact locked_on_A_plus | exact locked_on_B_plus].
Qed.

Lemma locked_twohit_I_ok_minus :
  I_ok (MkCirc locked_twohit_A) (MkCirc locked_twohit_B)
       (IHit locked_p_minus (1 / 6) (5 / 6)).
Proof.
  unfold I_ok. split; [exact locked_on_A_minus | exact locked_on_B_minus].
Qed.

Lemma locked_A_B_not_same_circle :
  ~ circ_same_circle locked_twohit_A locked_twohit_B.
Proof.
  intros [Ho _].
  unfold locked_twohit_A, locked_twohit_B in Ho.
  cbn in Ho. injection Ho as Hx.
  lra.
Qed.

Lemma locked_leftover_eggs_not_same :
  ~ circ_same_circle
      (circ_leftover_egg locked_twohit_A_span)
      (circ_leftover_egg locked_twohit_B_span).
Proof.
  rewrite circ_leftover_egg_parent, circ_leftover_egg_parent.
  exact locked_A_B_not_same_circle.
Qed.

(* Two unit circles meet only at p+ / p-. *)
Lemma two_unit_circles_x :
  forall p,
    dist_sq (mkPoint 0 0) p = 1 ->
    dist_sq (mkPoint 1 0) p = 1 ->
    px p = 1 / 2.
Proof.
  intros p HA HB.
  unfold dist_sq in HA, HB. cbn in HA, HB.
  assert (Hsub : (0 - px p) * (0 - px p) - (1 - px p) * (1 - px p) = 0)
    by lra.
  replace ((0 - px p) * (0 - px p) - (1 - px p) * (1 - px p))
    with (2 * px p - 1) in Hsub by ring.
  lra.
Qed.

Lemma two_unit_circles_y2 :
  forall p,
    dist_sq (mkPoint 0 0) p = 1 ->
    px p = 1 / 2 ->
    py p * py p = 3 / 4.
Proof.
  intros p HA Hx.
  unfold dist_sq in HA. cbn in HA.
  rewrite Hx in HA. lra.
Qed.

Lemma rsqr_three_quarters :
  forall y, y * y = 3 / 4 -> y = sqrt 3 / 2 \/ y = - (sqrt 3 / 2).
Proof.
  intros y Hy.
  assert (Hsq : Rsqr y = Rsqr (sqrt 3 / 2)).
  { unfold Rsqr.
    replace (sqrt 3 / 2 * (sqrt 3 / 2)) with (sqrt 3 * sqrt 3 / 4) by field.
    rewrite sqrt_sqrt; lra. }
  apply Rsqr_eq_abs_0 in Hsq.
  assert (Hpos : 0 <= sqrt 3 / 2).
  { apply Rmult_le_pos; [apply sqrt_pos|].
    apply Rlt_le, Rinv_0_lt_compat. lra. }
  rewrite (Rabs_right (sqrt 3 / 2) (Rle_ge _ _ Hpos)) in Hsq.
  destruct (Rle_dec 0 y) as [Hy0|Hy0].
  - rewrite (Rabs_right y (Rle_ge _ _ Hy0)) in Hsq. left. exact Hsq.
  - rewrite (Rabs_left y ltac:(lra)) in Hsq. right. lra.
Qed.

Lemma locked_centers_radii :
  circ_o locked_twohit_A = mkPoint 0 0 /\
  circ_o locked_twohit_B = mkPoint 1 0 /\
  circ_r locked_twohit_A = 1 /\
  circ_r locked_twohit_B = 1.
Proof.
  repeat split; reflexivity.
Qed.

Lemma locked_meet_is_plus_or_minus :
  forall p tA tB,
    on_circ locked_twohit_A tA p ->
    on_circ locked_twohit_B tB p ->
    p = locked_p_plus \/ p = locked_p_minus.
Proof.
  intros p tA tB [HA rngA] [HB rngB].
  subst p.
  pose proof (circ_eval_on_circle locked_twohit_A tA) as DA.
  pose proof (circ_eval_on_circle locked_twohit_B tB) as DB.
  destruct locked_centers_radii as [OA [OB [RA RB]]].
  rewrite OA, RA in DA. rewrite OB, RB in DB.
  replace (1 * 1) with 1 in DA by ring.
  replace (1 * 1) with 1 in DB by ring.
  set (q := circ_eval locked_twohit_A tA).
  fold q in DA, DB, rngB.
  rewrite rngB in DB.
  pose proof (two_unit_circles_x q DA DB) as Hx.
  pose proof (two_unit_circles_y2 q DA Hx) as Hy2.
  destruct (rsqr_three_quarters (py q) Hy2) as [Hy|Hy].
  - left. unfold locked_p_plus. apply point_eq_xy; [exact Hx|exact Hy].
  - right. unfold locked_p_minus. apply point_eq_xy; [exact Hx|exact Hy].
Qed.

Lemma cos_strict_dec_0_PI :
  forall x y, 0 <= x < y <= PI -> cos y < cos x.
Proof.
  intros x y [Hx [Hxy Hy]].
  set (d := y - x).
  assert (Hdpos : 0 < d) by (unfold d; lra).
  assert (Hdhi : d <= PI) by (unfold d; lra).
  replace y with (x + d) by (unfold d; ring).
  rewrite cos_plus.
  apply Rminus_gt_0_lt.
  replace (cos x - (cos x * cos d - sin x * sin d))
    with (cos x * (1 - cos d) + sin x * sin d) by ring.
  replace d with (2 * (d / 2)) by field.
  rewrite cos_2a_sin, sin_2a.
  unfold Rsqr.
  replace (cos x * (2 * (sin (d / 2) * sin (d / 2)))
           + sin x * (2 * sin (d / 2) * cos (d / 2)))
    with (2 * sin (d / 2) *
          (cos x * sin (d / 2) + sin x * cos (d / 2))) by ring.
  rewrite <- sin_plus.
  assert (Hs : 0 < sin (d / 2)).
  { apply sin_gt_0; pose proof PI_RGT_0; lra. }
  assert (Hs2 : 0 < sin (x + d / 2)).
  { apply sin_gt_0; pose proof PI_RGT_0; lra. }
  nra.
Qed.

Lemma cos_inj_0_PI :
  forall x y,
    0 <= x <= PI ->
    0 <= y <= PI ->
    cos x = cos y ->
    x = y.
Proof.
  intros x y Hx Hy Heq.
  destruct (Rtotal_order x y) as [Hlt|[Heqxy|Hgt]].
  - assert (Hdec : cos y < cos x)
      by (apply cos_strict_dec_0_PI; lra).
    lra.
  - exact Heqxy.
  - assert (Hdec : cos x < cos y)
      by (apply cos_strict_dec_0_PI; lra).
    lra.
Qed.

Lemma locked_A_eval_trig :
  forall t,
    circ_eval locked_twohit_A t =
    mkPoint (sin (t * PI)) (- cos (t * PI)).
Proof.
  intros t.
  unfold circ_eval, locked_twohit_A.
  cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  replace (- (PI / 2) + t * PI) with (t * PI - PI / 2)
    by (pose proof PI_RGT_0; field).
  rewrite cos_minus, sin_minus, cos_PI2, sin_PI2.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma locked_B_eval_trig :
  forall t,
    circ_eval locked_twohit_B t =
    mkPoint (1 - sin (t * PI)) (cos (t * PI)).
Proof.
  intros t.
  unfold circ_eval, locked_twohit_B.
  cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  replace (PI / 2 + t * PI) with (t * PI + PI / 2)
    by (pose proof PI_RGT_0; field).
  rewrite cos_plus, sin_plus, cos_PI2, sin_PI2.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma locked_A_eval_inj :
  forall t1 t2,
    0 <= t1 <= 1 ->
    0 <= t2 <= 1 ->
    circ_eval locked_twohit_A t1 = circ_eval locked_twohit_A t2 ->
    t1 = t2.
Proof.
  intros t1 t2 Ht1 Ht2 Heq.
  rewrite locked_A_eval_trig, locked_A_eval_trig in Heq.
  injection Heq as _ Hc.
  apply (f_equal Ropp) in Hc.
  rewrite Ropp_involutive, Ropp_involutive in Hc.
  pose proof PI_RGT_0 as HP.
  assert (Ha : 0 <= t1 * PI <= PI) by (split; nra).
  assert (Hb : 0 <= t2 * PI <= PI) by (split; nra).
  apply cos_inj_0_PI in Hc; [|exact Ha|exact Hb].
  apply Rmult_eq_reg_r in Hc; [exact Hc|lra].
Qed.

Lemma locked_B_eval_inj :
  forall t1 t2,
    0 <= t1 <= 1 ->
    0 <= t2 <= 1 ->
    circ_eval locked_twohit_B t1 = circ_eval locked_twohit_B t2 ->
    t1 = t2.
Proof.
  intros t1 t2 Ht1 Ht2 Heq.
  rewrite locked_B_eval_trig, locked_B_eval_trig in Heq.
  injection Heq as _ Hc.
  pose proof PI_RGT_0 as HP.
  assert (Ha : 0 <= t1 * PI <= PI) by (split; nra).
  assert (Hb : 0 <= t2 * PI <= PI) by (split; nra).
  apply cos_inj_0_PI in Hc; [|exact Ha|exact Hb].
  apply Rmult_eq_reg_r in Hc; [exact Hc|lra].
Qed.

Lemma locked_on_A_plus_t :
  forall t, on_circ locked_twohit_A t locked_p_plus -> t = 5 / 6.
Proof.
  intros t [Ht He].
  rewrite <- locked_twohit_A_at_plus in He.
  apply locked_A_eval_inj; [exact Ht|lra|exact He].
Qed.

Lemma locked_on_A_minus_t :
  forall t, on_circ locked_twohit_A t locked_p_minus -> t = 1 / 6.
Proof.
  intros t [Ht He].
  rewrite <- locked_twohit_A_at_minus in He.
  apply locked_A_eval_inj; [exact Ht|lra|exact He].
Qed.

Lemma locked_on_B_plus_t :
  forall t, on_circ locked_twohit_B t locked_p_plus -> t = 1 / 6.
Proof.
  intros t [Ht He].
  rewrite <- locked_twohit_B_at_plus in He.
  apply locked_B_eval_inj; [exact Ht|lra|exact He].
Qed.

Lemma locked_on_B_minus_t :
  forall t, on_circ locked_twohit_B t locked_p_minus -> t = 5 / 6.
Proof.
  intros t [Ht He].
  rewrite <- locked_twohit_B_at_minus in He.
  apply locked_B_eval_inj; [exact Ht|lra|exact He].
Qed.

Lemma circ_leftover_on_parent :
  forall s t p,
    on_circ (circ_leftover_egg s) t p ->
    on_circ (cls_parent s) (circ_leftover_span_at s t) p /\
    (circ_leftover_interior t ->
     circ_leftover_span_ok s ->
     circ_parent_open s (circ_leftover_span_at s t)).
Proof.
  intros s t p [Ht He].
  rewrite circ_leftover_eval_parent in He.
  split.
  - unfold on_circ. split.
    + unfold circ_leftover_span_at.
      destruct Ht as [Hlo Hhi].
      split.
      * nra.
      * nra.
    + exact He.
  - intros [Hilo Hihi] Hok.
    unfold circ_parent_open, circ_leftover_span_at, circ_leftover_span_ok in *.
    split; nra.
Qed.

Lemma locked_span_A_parent :
  forall s, cls_parent s = locked_twohit_A ->
    circ_o (circ_leftover_egg s) = mkPoint 0 0 /\
    circ_r (circ_leftover_egg s) = 1.
Proof.
  intros s Hp.
  destruct (circ_leftover_egg_or s) as [Ho Hr].
  rewrite Hp in Ho, Hr.
  unfold locked_twohit_A in Ho, Hr. cbn in Ho, Hr.
  split; assumption.
Qed.

Lemma locked_span_B_parent :
  forall s, cls_parent s = locked_twohit_B ->
    circ_o (circ_leftover_egg s) = mkPoint 1 0 /\
    circ_r (circ_leftover_egg s) = 1.
Proof.
  intros s Hp.
  destruct (circ_leftover_egg_or s) as [Ho Hr].
  rewrite Hp in Ho, Hr.
  unfold locked_twohit_B in Ho, Hr. cbn in Ho, Hr.
  split; assumption.
Qed.

Lemma locked_A_B_leftover_not_same :
  forall sa sb,
    cls_parent sa = locked_twohit_A ->
    cls_parent sb = locked_twohit_B ->
    ~ circ_same_circle (circ_leftover_egg sa) (circ_leftover_egg sb).
Proof.
  intros sa sb Ha Hb [Ho _].
  destruct (locked_span_A_parent sa Ha) as [Oa _].
  destruct (locked_span_B_parent sb Hb) as [Ob _].
  rewrite Oa, Ob in Ho. injection Ho as Hx. lra.
Qed.

Lemma locked_pair_hit_is_root :
  forall sa sb p ua ub,
    cls_parent sa = locked_twohit_A ->
    cls_parent sb = locked_twohit_B ->
    circ_leftover_pair_hit sa sb p ua ub ->
    (p = locked_p_plus /\
     circ_parent_open sa (5 / 6) /\
     circ_parent_open sb (1 / 6)) \/
    (p = locked_p_minus /\
     circ_parent_open sa (1 / 6) /\
     circ_parent_open sb (5 / 6)).
Proof.
  intros sa sb p ua ub Ha Hb [Hoka [Hokb [Hua [Hub [_ Hok]]]]].
  unfold I_ok in Hok.
  destruct Hok as [onA onB].
  pose proof (circ_leftover_on_parent sa ua p onA) as [onPA openA].
  pose proof (circ_leftover_on_parent sb ub p onB) as [onPB openB].
  rewrite Ha in onPA. rewrite Hb in onPB.
  pose proof (locked_meet_is_plus_or_minus p _ _ onPA onPB) as Hm.
  destruct Hm as [Hp|Hp].
  - left. subst p.
    pose proof (locked_on_A_plus_t _ onPA) as tA.
    pose proof (locked_on_B_plus_t _ onPB) as tB.
    rewrite tA in openA. rewrite tB in openB.
    split; [reflexivity|].
    split; [apply openA; [exact Hua|exact Hoka]|apply openB; [exact Hub|exact Hokb]].
  - right. subst p.
    pose proof (locked_on_A_minus_t _ onPA) as tA.
    pose proof (locked_on_B_minus_t _ onPB) as tB.
    rewrite tA in openA. rewrite tB in openB.
    split; [reflexivity|].
    split; [apply openA; [exact Hua|exact Hoka]|apply openB; [exact Hub|exact Hokb]].
Qed.

Lemma locked_pair_hit_from_open_plus :
  forall sa sb,
    cls_parent sa = locked_twohit_A ->
    cls_parent sb = locked_twohit_B ->
    circ_leftover_span_ok sa ->
    circ_leftover_span_ok sb ->
    circ_parent_open sa (5 / 6) ->
    circ_parent_open sb (1 / 6) ->
    circ_leftover_pair_hit sa sb locked_p_plus
      ((5 / 6 - cls_t0 sa) / (cls_t1 sa - cls_t0 sa))
      ((1 / 6 - cls_t0 sb) / (cls_t1 sb - cls_t0 sb)).
Proof.
  intros sa sb Ha Hb Hoka Hokb Oa Ob.
  unfold circ_leftover_span_ok in Hoka, Hokb.
  unfold circ_parent_open in Oa, Ob.
  set (ua := (5 / 6 - cls_t0 sa) / (cls_t1 sa - cls_t0 sa)).
  set (ub := (1 / 6 - cls_t0 sb) / (cls_t1 sb - cls_t0 sb)).
  assert (Hua : circ_leftover_interior ua).
  { unfold circ_leftover_interior, ua. split.
    - apply Rdiv_lt_0_compat; lra.
    - apply (Rmult_lt_reg_r (cls_t1 sa - cls_t0 sa)); lra. }
  assert (Hub : circ_leftover_interior ub).
  { unfold circ_leftover_interior, ub. split.
    - apply Rdiv_lt_0_compat; lra.
    - apply (Rmult_lt_reg_r (cls_t1 sb - cls_t0 sb)); lra. }
  assert (Hat : circ_leftover_span_at sa ua = 5 / 6).
  { unfold circ_leftover_span_at, ua. field; lra. }
  assert (Hbt : circ_leftover_span_at sb ub = 1 / 6).
  { unfold circ_leftover_span_at, ub. field; lra. }
  unfold circ_leftover_pair_hit.
  split; [exact Hoka|].
  split; [exact Hokb|].
  split; [exact Hua|].
  split; [exact Hub|].
  split; [apply (locked_A_B_leftover_not_same sa sb Ha Hb)|].
  unfold I_ok.
  split.
  - unfold on_circ. split; [unfold circ_leftover_interior in Hua; lra|].
    rewrite circ_leftover_eval_parent, Hat, Ha.
    symmetry. exact locked_twohit_A_at_plus.
  - unfold on_circ. split; [unfold circ_leftover_interior in Hub; lra|].
    rewrite circ_leftover_eval_parent, Hbt, Hb.
    symmetry. exact locked_twohit_B_at_plus.
Qed.

Lemma locked_pair_hit_from_open_minus :
  forall sa sb,
    cls_parent sa = locked_twohit_A ->
    cls_parent sb = locked_twohit_B ->
    circ_leftover_span_ok sa ->
    circ_leftover_span_ok sb ->
    circ_parent_open sa (1 / 6) ->
    circ_parent_open sb (5 / 6) ->
    circ_leftover_pair_hit sa sb locked_p_minus
      ((1 / 6 - cls_t0 sa) / (cls_t1 sa - cls_t0 sa))
      ((5 / 6 - cls_t0 sb) / (cls_t1 sb - cls_t0 sb)).
Proof.
  intros sa sb Ha Hb Hoka Hokb Oa Ob.
  unfold circ_leftover_span_ok in Hoka, Hokb.
  unfold circ_parent_open in Oa, Ob.
  set (ua := (1 / 6 - cls_t0 sa) / (cls_t1 sa - cls_t0 sa)).
  set (ub := (5 / 6 - cls_t0 sb) / (cls_t1 sb - cls_t0 sb)).
  assert (Hua : circ_leftover_interior ua).
  { unfold circ_leftover_interior, ua. split.
    - apply Rdiv_lt_0_compat; lra.
    - apply (Rmult_lt_reg_r (cls_t1 sa - cls_t0 sa)); lra. }
  assert (Hub : circ_leftover_interior ub).
  { unfold circ_leftover_interior, ub. split.
    - apply Rdiv_lt_0_compat; lra.
    - apply (Rmult_lt_reg_r (cls_t1 sb - cls_t0 sb)); lra. }
  assert (Hat : circ_leftover_span_at sa ua = 1 / 6).
  { unfold circ_leftover_span_at, ua. field; lra. }
  assert (Hbt : circ_leftover_span_at sb ub = 5 / 6).
  { unfold circ_leftover_span_at, ub. field; lra. }
  unfold circ_leftover_pair_hit.
  split; [exact Hoka|].
  split; [exact Hokb|].
  split; [exact Hua|].
  split; [exact Hub|].
  split; [apply (locked_A_B_leftover_not_same sa sb Ha Hb)|].
  unfold I_ok.
  split.
  - unfold on_circ. split; [unfold circ_leftover_interior in Hua; lra|].
    rewrite circ_leftover_eval_parent, Hat, Ha.
    symmetry. exact locked_twohit_A_at_minus.
  - unfold on_circ. split; [unfold circ_leftover_interior in Hub; lra|].
    rewrite circ_leftover_eval_parent, Hbt, Hb.
    symmetry. exact locked_twohit_B_at_minus.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked bags: parent |H|=2, after first split 1, after second 0.            *)
(* -------------------------------------------------------------------------- *)

Definition locked_A_lo : circ_leftover_span :=
  mkCircLeftoverSpan locked_twohit_A 0 (5 / 6).

Definition locked_A_hi : circ_leftover_span :=
  mkCircLeftoverSpan locked_twohit_A (5 / 6) 1.

Definition locked_B_lo : circ_leftover_span :=
  mkCircLeftoverSpan locked_twohit_B 0 (1 / 6).

Definition locked_B_hi : circ_leftover_span :=
  mkCircLeftoverSpan locked_twohit_B (1 / 6) 1.

Definition locked_circ_mid_bag : circ_leftover_bag :=
  CBagCons locked_A_lo
    (CBagCons locked_A_hi
      (CBagCons locked_B_lo
        (CBagCons locked_B_hi CBagNil))).

Definition locked_A0 : circ_leftover_span :=
  mkCircLeftoverSpan locked_twohit_A 0 (1 / 6).

Definition locked_A1 : circ_leftover_span :=
  mkCircLeftoverSpan locked_twohit_A (1 / 6) (5 / 6).

Definition locked_A2 : circ_leftover_span :=
  mkCircLeftoverSpan locked_twohit_A (5 / 6) 1.

Definition locked_B0 : circ_leftover_span :=
  mkCircLeftoverSpan locked_twohit_B 0 (1 / 6).

Definition locked_B1 : circ_leftover_span :=
  mkCircLeftoverSpan locked_twohit_B (1 / 6) (5 / 6).

Definition locked_B2 : circ_leftover_span :=
  mkCircLeftoverSpan locked_twohit_B (5 / 6) 1.

Definition locked_circ_final_bag : circ_leftover_bag :=
  CBagCons locked_A0
    (CBagCons locked_A1
      (CBagCons locked_B1
        (CBagCons locked_B2
          (CBagCons locked_A2
            (CBagCons locked_B0 CBagNil))))).

Lemma locked_parent_plus_hit :
  circ_leftover_pair_hit locked_twohit_A_span locked_twohit_B_span
    locked_p_plus (5 / 6) (1 / 6).
Proof.
  rewrite <- (circ_leftover_span_parent_at locked_twohit_A (5 / 6)).
  rewrite <- (circ_leftover_span_parent_at locked_twohit_B (1 / 6)).
  replace (5 / 6) with
    ((5 / 6 - cls_t0 locked_twohit_A_span)
     / (cls_t1 locked_twohit_A_span - cls_t0 locked_twohit_A_span))
    by (unfold locked_twohit_A_span, circ_leftover_span_parent; simpl; field).
  replace (1 / 6) with
    ((1 / 6 - cls_t0 locked_twohit_B_span)
     / (cls_t1 locked_twohit_B_span - cls_t0 locked_twohit_B_span))
    by (unfold locked_twohit_B_span, circ_leftover_span_parent; simpl; field).
  apply locked_pair_hit_from_open_plus.
  - reflexivity.
  - reflexivity.
  - apply circ_leftover_span_parent_ok.
  - apply circ_leftover_span_parent_ok.
  - unfold circ_parent_open, locked_twohit_A_span, circ_leftover_span_parent.
    simpl. lra.
  - unfold circ_parent_open, locked_twohit_B_span, circ_leftover_span_parent.
    simpl. lra.
Qed.

Lemma locked_parent_minus_hit :
  circ_leftover_pair_hit locked_twohit_A_span locked_twohit_B_span
    locked_p_minus (1 / 6) (5 / 6).
Proof.
  replace (1 / 6) with
    ((1 / 6 - cls_t0 locked_twohit_A_span)
     / (cls_t1 locked_twohit_A_span - cls_t0 locked_twohit_A_span))
    by (unfold locked_twohit_A_span, circ_leftover_span_parent; simpl; field).
  replace (5 / 6) with
    ((5 / 6 - cls_t0 locked_twohit_B_span)
     / (cls_t1 locked_twohit_B_span - cls_t0 locked_twohit_B_span))
    by (unfold locked_twohit_B_span, circ_leftover_span_parent; simpl; field).
  apply locked_pair_hit_from_open_minus.
  - reflexivity.
  - reflexivity.
  - apply circ_leftover_span_parent_ok.
  - apply circ_leftover_span_parent_ok.
  - unfold circ_parent_open, locked_twohit_A_span, circ_leftover_span_parent.
    simpl. lra.
  - unfold circ_parent_open, locked_twohit_B_span, circ_leftover_span_parent.
    simpl. lra.
Qed.

Lemma locked_parent_plus_step_ok :
  circ_leftover_pair_step_ok locked_circ_parent_bag 0 1
    locked_p_plus (5 / 6) (1 / 6).
Proof.
  exists locked_twohit_A_span, locked_twohit_B_span.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [discriminate|].
  exact locked_parent_plus_hit.
Qed.

Lemma locked_parent_minus_step_ok :
  circ_leftover_pair_step_ok locked_circ_parent_bag 0 1
    locked_p_minus (1 / 6) (5 / 6).
Proof.
  exists locked_twohit_A_span, locked_twohit_B_span.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [discriminate|].
  exact locked_parent_minus_hit.
Qed.

Lemma locked_parent_replace :
  cbag_pair_replace locked_circ_parent_bag 0 1 (5 / 6) (1 / 6) =
  Some locked_circ_mid_bag.
Proof.
  unfold cbag_pair_replace, locked_circ_parent_bag, locked_circ_mid_bag,
         locked_A_lo, locked_A_hi, locked_B_lo, locked_B_hi,
         locked_twohit_A_span, locked_twohit_B_span,
         circ_leftover_span_lo, circ_leftover_span_hi,
         circ_leftover_span_at, circ_leftover_span_parent, cbag_remove_two.
  simpl.
  apply f_equal.
  apply (f_equal2 CBagCons).
  { apply (f_equal2 mkCircLeftoverSpan); [reflexivity|]; field. }
  apply (f_equal2 CBagCons).
  { apply (f_equal2 (mkCircLeftoverSpan locked_twohit_A)); field. }
  apply (f_equal2 CBagCons).
  { apply (f_equal2 mkCircLeftoverSpan); [reflexivity|]; field. }
  apply (f_equal2 CBagCons).
  { apply (f_equal2 (mkCircLeftoverSpan locked_twohit_B)); field. }
  reflexivity.
Qed.

Lemma locked_circ_hit_step_first :
  circ_leftover_bag_step locked_circ_parent_bag locked_circ_mid_bag.
Proof.
  apply (CStepHit locked_circ_parent_bag locked_circ_mid_bag 0 1
           locked_p_plus (5 / 6) (1 / 6)).
  - exact locked_parent_plus_step_ok.
  - exact locked_parent_replace.
Qed.

Lemma locked_mid_minus_hit :
  circ_leftover_pair_hit locked_A_lo locked_B_hi
    locked_p_minus (1 / 5) (4 / 5).
Proof.
  replace (1 / 5) with
    ((1 / 6 - cls_t0 locked_A_lo) / (cls_t1 locked_A_lo - cls_t0 locked_A_lo))
    by (unfold locked_A_lo; simpl; field).
  replace (4 / 5) with
    ((5 / 6 - cls_t0 locked_B_hi) / (cls_t1 locked_B_hi - cls_t0 locked_B_hi))
    by (unfold locked_B_hi; simpl; field).
  apply locked_pair_hit_from_open_minus.
  - reflexivity.
  - reflexivity.
  - unfold circ_leftover_span_ok, locked_A_lo. simpl. lra.
  - unfold circ_leftover_span_ok, locked_B_hi. simpl. lra.
  - unfold circ_parent_open, locked_A_lo. simpl. lra.
  - unfold circ_parent_open, locked_B_hi. simpl. lra.
Qed.

Lemma locked_mid_minus_step_ok :
  circ_leftover_pair_step_ok locked_circ_mid_bag 0 3
    locked_p_minus (1 / 5) (4 / 5).
Proof.
  exists locked_A_lo, locked_B_hi.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [discriminate|].
  exact locked_mid_minus_hit.
Qed.

Lemma locked_mid_replace :
  cbag_pair_replace locked_circ_mid_bag 0 3 (1 / 5) (4 / 5) =
  Some locked_circ_final_bag.
Proof.
  unfold cbag_pair_replace, locked_circ_mid_bag, locked_circ_final_bag,
         locked_A_lo, locked_A_hi, locked_B_lo, locked_B_hi,
         locked_A0, locked_A1, locked_A2, locked_B0, locked_B1, locked_B2,
         circ_leftover_span_lo, circ_leftover_span_hi,
         circ_leftover_span_at, cbag_remove_two.
  simpl.
  apply f_equal.
  apply (f_equal2 CBagCons).
  { apply (f_equal2 mkCircLeftoverSpan); [reflexivity|]; field. }
  apply (f_equal2 CBagCons).
  { apply (f_equal2 (mkCircLeftoverSpan locked_twohit_A)); field. }
  apply (f_equal2 CBagCons).
  { apply (f_equal2 (mkCircLeftoverSpan locked_twohit_B)); field. }
  apply (f_equal2 CBagCons).
  { apply (f_equal2 (mkCircLeftoverSpan locked_twohit_B)); field. }
  apply (f_equal2 CBagCons); reflexivity.
Qed.

Lemma locked_circ_hit_step_second :
  circ_leftover_bag_step locked_circ_mid_bag locked_circ_final_bag.
Proof.
  apply (CStepHit locked_circ_mid_bag locked_circ_final_bag 0 3
           locked_p_minus (1 / 5) (4 / 5)).
  - exact locked_mid_minus_step_ok.
  - exact locked_mid_replace.
Qed.

Lemma locked_mid_children_circular :
  egg_class (MkCirc (circ_leftover_egg locked_A_lo)) = EggCircularArc /\
  egg_class (MkCirc (circ_leftover_egg locked_A_hi)) = EggCircularArc /\
  egg_class (MkCirc (circ_leftover_egg locked_B_lo)) = EggCircularArc /\
  egg_class (MkCirc (circ_leftover_egg locked_B_hi)) = EggCircularArc.
Proof.
  repeat split; reflexivity.
Qed.

(* Same-circle leftover pair cannot Hit. *)
Lemma circ_same_parent_no_hit :
  forall a b p ua ub,
    cls_parent a = cls_parent b ->
    ~ circ_leftover_pair_hit a b p ua ub.
Proof.
  intros a b p ua ub Hp [_ [_ [_ [_ [Hsame _]]]]].
  apply Hsame.
  destruct (circ_leftover_egg_or a) as [Oa Ra].
  destruct (circ_leftover_egg_or b) as [Ob Rb].
  rewrite Hp in Oa, Ra.
  unfold circ_same_circle. split; congruence.
Qed.

Lemma locked_cocircular_overlap_decline :
  forall p ua ub,
    ~ circ_leftover_pair_hit
        locked_twohit_A_span locked_twohit_A_span p ua ub.
Proof.
  intros p ua ub.
  apply circ_same_parent_no_hit.
  reflexivity.
Qed.

Lemma locked_span_ok_A_lo :
  circ_leftover_span_ok locked_A_lo.
Proof. unfold circ_leftover_span_ok, locked_A_lo. simpl. lra. Qed.

Lemma locked_span_ok_A_hi :
  circ_leftover_span_ok locked_A_hi.
Proof. unfold circ_leftover_span_ok, locked_A_hi. simpl. lra. Qed.

Lemma locked_span_ok_B_lo :
  circ_leftover_span_ok locked_B_lo.
Proof. unfold circ_leftover_span_ok, locked_B_lo. simpl. lra. Qed.

Lemma locked_span_ok_B_hi :
  circ_leftover_span_ok locked_B_hi.
Proof. unfold circ_leftover_span_ok, locked_B_hi. simpl. lra. Qed.

Lemma locked_mid_endpoint_pair_decline :
  forall p ua ub,
    ~ circ_leftover_pair_hit locked_A_hi locked_B_lo p ua ub.
Proof.
  intros p ua ub Hhit.
  pose proof (locked_pair_hit_is_root locked_A_hi locked_B_lo p ua ub
                eq_refl eq_refl Hhit) as H.
  unfold circ_parent_open, locked_A_hi, locked_B_lo in H.
  simpl in H.
  destruct H as [[_ [Oa Ob]]|[_ [Oa Ob]]]; lra.
Qed.

Lemma locked_endpoint_only_decline :
  circ_leftover_pair_decline locked_circ_mid_bag 1 2.
Proof.
  exists locked_A_hi, locked_B_lo.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [discriminate|].
  exact locked_mid_endpoint_pair_decline.
Qed.

Lemma locked_circ_decline_idle :
  circ_leftover_bag_step locked_circ_mid_bag locked_circ_mid_bag.
Proof.
  apply (CStepDecline locked_circ_mid_bag 1 2).
  exact locked_endpoint_only_decline.
Qed.

(* Parent listing: the one pair carries both Hits. *)
Lemma locked_parent_nth :
  cbag_nth locked_circ_parent_bag 0 = Some locked_twohit_A_span /\
  cbag_nth locked_circ_parent_bag 1 = Some locked_twohit_B_span.
Proof.
  split; reflexivity.
Qed.

Lemma locked_parent_only_pair :
  forall i j p,
    circ_leftover_hit_occ locked_circ_parent_bag i j p ->
    i = 0%nat /\ j = 1%nat /\
    (p = locked_p_plus \/ p = locked_p_minus).
Proof.
  intros i j p Hocc.
  pose proof (circ_leftover_hit_occ_bounded _ _ _ _ Hocc) as Hbnd.
  change (cbag_count locked_circ_parent_bag) with 2%nat in Hbnd.
  assert (i = 0%nat /\ j = 1%nat) as [Hi Hj] by lia.
  subst i j.
  destruct Hocc as [_ [ua [ub [a [bsp [Ha [Hb [_ Hhit]]]]]]]].
  destruct locked_parent_nth as [H0 H1].
  rewrite H0 in Ha. rewrite H1 in Hb.
  inversion Ha. inversion Hb. subst a bsp.
  unfold locked_twohit_A_span, locked_twohit_B_span,
         circ_leftover_span_parent in Hhit.
  pose proof (locked_pair_hit_is_root
                (circ_leftover_span_parent locked_twohit_A)
                (circ_leftover_span_parent locked_twohit_B)
                p ua ub eq_refl eq_refl Hhit) as Hroot.
  destruct Hroot as [[Hp _]|[Hp _]]; auto.
Qed.

Lemma locked_parent_term_measure :
  circ_leftover_bag_measure locked_circ_parent_bag 2.
Proof.
  exists [(0%nat, 1%nat, locked_p_plus); (0%nat, 1%nat, locked_p_minus)].
  split; [|reflexivity].
  split.
  - intros ijp Hin.
    destruct Hin as [H1|[H2|Hnil]]; [| |contradiction].
    + inversion H1. subst ijp. simpl.
      split; [lia|]. exists (5 / 6), (1 / 6).
      exact locked_parent_plus_step_ok.
    + inversion H2. subst ijp. simpl.
      split; [lia|]. exists (1 / 6), (5 / 6).
      exact locked_parent_minus_step_ok.
  - split.
    + intros i j p Hocc.
      pose proof (locked_parent_only_pair i j p Hocc) as [Hi [Hj Hp]].
      subst i j.
      destruct Hp as [Hp|Hp]; subst p; [left|right; left]; reflexivity.
    + apply NoDup_cons.
      * intros H. destruct H as [Heq|Hnil]; [|contradiction].
        inversion Heq. exact (locked_p_plus_neq_minus H0).
      * apply NoDup_cons; [intros H; inversion H|apply NoDup_nil].
Qed.

Lemma locked_mid_nth :
  cbag_nth locked_circ_mid_bag 0 = Some locked_A_lo /\
  cbag_nth locked_circ_mid_bag 1 = Some locked_A_hi /\
  cbag_nth locked_circ_mid_bag 2 = Some locked_B_lo /\
  cbag_nth locked_circ_mid_bag 3 = Some locked_B_hi.
Proof.
  repeat split; reflexivity.
Qed.

Lemma locked_A_lo_no_plus_open :
  ~ circ_parent_open locked_A_lo (5 / 6).
Proof. unfold circ_parent_open, locked_A_lo. simpl. lra. Qed.

Lemma locked_A_hi_no_root_open :
  ~ circ_parent_open locked_A_hi (5 / 6) /\
  ~ circ_parent_open locked_A_hi (1 / 6).
Proof. unfold circ_parent_open, locked_A_hi. simpl. split; lra. Qed.

Lemma locked_B_lo_no_root_open :
  ~ circ_parent_open locked_B_lo (1 / 6) /\
  ~ circ_parent_open locked_B_lo (5 / 6).
Proof. unfold circ_parent_open, locked_B_lo. simpl. split; lra. Qed.

Lemma locked_B_hi_no_plus_open :
  ~ circ_parent_open locked_B_hi (1 / 6).
Proof. unfold circ_parent_open, locked_B_hi. simpl. lra. Qed.

Lemma locked_mid_cross_no_hit :
  forall sa sb p ua ub,
    ((sa = locked_A_lo /\ sb = locked_B_lo) \/
     (sa = locked_A_hi /\ sb = locked_B_lo) \/
     (sa = locked_A_hi /\ sb = locked_B_hi)) ->
    ~ circ_leftover_pair_hit sa sb p ua ub.
Proof.
  intros sa sb p ua ub Hcase Hhit.
  assert (Ha : cls_parent sa = locked_twohit_A).
  { destruct Hcase as [H|[[H|H]]]; subst; reflexivity. }
  assert (Hb : cls_parent sb = locked_twohit_B).
  { destruct Hcase as [H|[[H|H]]]; subst; reflexivity. }
  pose proof (locked_pair_hit_is_root sa sb p ua ub Ha Hb Hhit) as Hroot.
  destruct Hcase as [[Haeq Hbeq]|[[Haeq Hbeq]|[Haeq Hbeq]]]; subst sa sb.
  - destruct Hroot as [[_ [Oa Ob]]|[_ [Oa Ob]]].
    + exact (locked_A_lo_no_plus_open Oa).
    + destruct locked_B_lo_no_root_open as [_ Hn]. exact (Hn Ob).
  - exact (locked_mid_endpoint_pair_decline p ua ub Hhit).
  - destruct Hroot as [[_ [Oa Ob]]|[_ [Oa Ob]]].
    + destruct locked_A_hi_no_root_open as [Hn _]. exact (Hn Oa).
    + destruct locked_A_hi_no_root_open as [_ Hn]. exact (Hn Oa).
Qed.

Lemma locked_mid_only_minus :
  forall i j p,
    circ_leftover_hit_occ locked_circ_mid_bag i j p ->
    i = 0%nat /\ j = 3%nat /\ p = locked_p_minus.
Proof.
  intros i j p Hocc.
  pose proof (circ_leftover_hit_occ_bounded _ _ _ _ Hocc) as Hbnd.
  change (cbag_count locked_circ_mid_bag) with 4%nat in Hbnd.
  destruct Hocc as [Hij [ua [ub [a [bsp [Ha [Hb [Hne Hhit]]]]]]]].
  destruct locked_mid_nth as [N0 [N1 [N2 N3]]].
  destruct i as [|i0].
  - destruct j as [|j0]; [lia|].
    destruct j0 as [|j1].
    + rewrite N0 in Ha. rewrite N1 in Hb.
      inversion Ha. inversion Hb. subst a bsp.
      exact (circ_same_parent_no_hit _ _ p ua ub eq_refl Hhit).
    + destruct j1 as [|j2].
      * rewrite N0 in Ha. rewrite N2 in Hb.
        inversion Ha. inversion Hb. subst a bsp.
        exact (locked_mid_cross_no_hit locked_A_lo locked_B_lo p ua ub
                 (or_introl (conj eq_refl eq_refl)) Hhit).
      * destruct j2 as [|j3]; [|lia].
        rewrite N0 in Ha. rewrite N3 in Hb.
        inversion Ha. inversion Hb. subst a bsp.
        pose proof (locked_pair_hit_is_root locked_A_lo locked_B_hi p ua ub
                      eq_refl eq_refl Hhit) as Hroot.
        destruct Hroot as [[Hp [Oa _]]|[Hp _]].
        -- exfalso. exact (locked_A_lo_no_plus_open Oa).
        -- split; [reflexivity|]. split; [reflexivity|exact Hp].
  - destruct i0 as [|i1].
    + destruct j as [|j0]; [lia|].
      destruct j0 as [|j1]; [lia|].
      destruct j1 as [|j2].
      * rewrite N1 in Ha. rewrite N2 in Hb.
        inversion Ha. inversion Hb. subst a bsp.
        exact (locked_mid_cross_no_hit locked_A_hi locked_B_lo p ua ub
                 (or_intror (or_introl (conj eq_refl eq_refl))) Hhit).
      * destruct j2 as [|j3]; [|lia].
        rewrite N1 in Ha. rewrite N3 in Hb.
        inversion Ha. inversion Hb. subst a bsp.
        exact (locked_mid_cross_no_hit locked_A_hi locked_B_hi p ua ub
                 (or_intror (or_intror (conj eq_refl eq_refl))) Hhit).
    + destruct i1 as [|i2]; [|lia].
      destruct j as [|j0]; [lia|].
      destruct j0 as [|j1]; [lia|].
      destruct j1 as [|j2]; [lia|].
      destruct j2 as [|j3]; [|lia].
      rewrite N2 in Ha. rewrite N3 in Hb.
      inversion Ha. inversion Hb. subst a bsp.
      exact (circ_same_parent_no_hit _ _ p ua ub eq_refl Hhit).
Qed.

Lemma locked_mid_term_measure :
  circ_leftover_bag_measure locked_circ_mid_bag 1.
Proof.
  exists [(0%nat, 3%nat, locked_p_minus)].
  split; [|reflexivity].
  split.
  - intros ijp Hin.
    destruct Hin as [Heq|Hnil]; [|contradiction].
    inversion Heq. subst ijp. simpl.
    split; [lia|]. exists (1 / 5), (4 / 5).
    exact locked_mid_minus_step_ok.
  - split.
    + intros i j p Hocc.
      pose proof (locked_mid_only_minus i j p Hocc) as [Hi [Hj Hp]].
      subst i j p. left. reflexivity.
    + apply NoDup_cons; [intros H; inversion H|apply NoDup_nil].
Qed.

Lemma locked_final_nth :
  cbag_nth locked_circ_final_bag 0 = Some locked_A0 /\
  cbag_nth locked_circ_final_bag 1 = Some locked_A1 /\
  cbag_nth locked_circ_final_bag 2 = Some locked_B1 /\
  cbag_nth locked_circ_final_bag 3 = Some locked_B2 /\
  cbag_nth locked_circ_final_bag 4 = Some locked_A2 /\
  cbag_nth locked_circ_final_bag 5 = Some locked_B0.
Proof.
  repeat split; reflexivity.
Qed.

Lemma locked_final_span_no_root_open :
  forall s,
    (s = locked_A0 \/ s = locked_A1 \/ s = locked_A2 \/
     s = locked_B0 \/ s = locked_B1 \/ s = locked_B2) ->
    ~ circ_parent_open s (1 / 6) /\ ~ circ_parent_open s (5 / 6).
Proof.
  intros s Hs.
  unfold circ_parent_open, locked_A0, locked_A1, locked_A2,
         locked_B0, locked_B1, locked_B2 in *.
  repeat (destruct Hs as [Heq|Hs]; [subst s; simpl; split; lra|]).
  contradiction.
Qed.

Lemma locked_final_span_parent :
  forall s,
    (s = locked_A0 \/ s = locked_A1 \/ s = locked_A2) ->
    cls_parent s = locked_twohit_A.
Proof.
  intros s [H|[H|H]]; subst; reflexivity.
Qed.

Lemma locked_final_span_parent_B :
  forall s,
    (s = locked_B0 \/ s = locked_B1 \/ s = locked_B2) ->
    cls_parent s = locked_twohit_B.
Proof.
  intros s [H|[H|H]]; subst; reflexivity.
Qed.

Lemma locked_final_nth_span :
  forall i s,
    cbag_nth locked_circ_final_bag i = Some s ->
    s = locked_A0 \/ s = locked_A1 \/ s = locked_A2 \/
    s = locked_B0 \/ s = locked_B1 \/ s = locked_B2.
Proof.
  intros i s Hs.
  pose proof (cbag_nth_some_lt locked_circ_final_bag i s Hs) as Hi.
  change (cbag_count locked_circ_final_bag) with 6%nat in Hi.
  destruct locked_final_nth as [N0 [N1 [N2 [N3 [N4 N5]]]]].
  destruct i as [|i0].
  - rewrite N0 in Hs. inversion Hs. subst. left. reflexivity.
  - destruct i0 as [|i1].
    + rewrite N1 in Hs. inversion Hs. subst. right. left. reflexivity.
    + destruct i1 as [|i2].
      * rewrite N2 in Hs. inversion Hs. subst.
        right. right. right. right. left. reflexivity.
      * destruct i2 as [|i3].
        -- rewrite N3 in Hs. inversion Hs. subst.
           right. right. right. right. right. left. reflexivity.
        -- destruct i3 as [|i4].
           ++ rewrite N4 in Hs. inversion Hs. subst.
              right. right. left. reflexivity.
           ++ destruct i4 as [|i5]; [|lia].
              rewrite N5 in Hs. inversion Hs. subst.
              right. right. right. left. reflexivity.
Qed.

Lemma locked_final_is_A :
  forall s,
    s = locked_A0 \/ s = locked_A1 \/ s = locked_A2 ->
    cls_parent s = locked_twohit_A.
Proof.
  intros s [H|[H|H]]; subst; reflexivity.
Qed.

Lemma locked_final_is_B :
  forall s,
    s = locked_B0 \/ s = locked_B1 \/ s = locked_B2 ->
    cls_parent s = locked_twohit_B.
Proof.
  intros s [H|[H|H]]; subst; reflexivity.
Qed.

Lemma locked_final_pair_no_hit :
  forall a bsp p ua ub,
    (a = locked_A0 \/ a = locked_A1 \/ a = locked_A2 \/
     a = locked_B0 \/ a = locked_B1 \/ a = locked_B2) ->
    (bsp = locked_A0 \/ bsp = locked_A1 \/ bsp = locked_A2 \/
     bsp = locked_B0 \/ bsp = locked_B1 \/ bsp = locked_B2) ->
    ~ circ_leftover_pair_hit a bsp p ua ub.
Proof.
  intros a bsp p ua ub Ha Hb Hhit.
  assert (PA : cls_parent a = locked_twohit_A \/
               cls_parent a = locked_twohit_B).
  { destruct Ha as [H|[H|[H|[H|[H|H]]]]]; subst; [left|left|left|right|right|right];
      reflexivity. }
  assert (PB : cls_parent bsp = locked_twohit_A \/
               cls_parent bsp = locked_twohit_B).
  { destruct Hb as [H|[H|[H|[H|[H|H]]]]]; subst; [left|left|left|right|right|right];
      reflexivity. }
  destruct PA as [PA|PA]; destruct PB as [PB|PB].
  - apply (circ_same_parent_no_hit a bsp p ua ub); congruence.
  - pose proof (locked_pair_hit_is_root a bsp p ua ub PA PB Hhit) as Hroot.
    destruct Hroot as [[_ [Oa Ob]]|[_ [Oa Ob]]].
    + apply (proj2 (locked_final_span_no_root_open a Ha)). exact Oa.
    + apply (proj1 (locked_final_span_no_root_open a Ha)). exact Oa.
  - destruct Hhit as [Hoka [Hokb [Hua [Hub [Hsame Hok]]]]].
    unfold I_ok in Hok. destruct Hok as [onB onA].
    pose proof (circ_leftover_on_parent a ua p onB) as [onPA openA].
    pose proof (circ_leftover_on_parent bsp ub p onA) as [onPB openB].
    rewrite PA in onPA. rewrite PB in onPB.
    pose proof (locked_meet_is_plus_or_minus p _ _ onPB onPA) as Hm.
    destruct Hm as [Hp|Hp].
    + subst p.
      pose proof (locked_on_B_plus_t _ onPA) as tB.
      rewrite tB in openA.
      apply (proj1 (locked_final_span_no_root_open a Ha)).
      apply openA; [exact Hua|exact Hoka].
    + subst p.
      pose proof (locked_on_B_minus_t _ onPA) as tB.
      rewrite tB in openA.
      apply (proj2 (locked_final_span_no_root_open a Ha)).
      apply openA; [exact Hua|exact Hoka].
  - apply (circ_same_parent_no_hit a bsp p ua ub); congruence.
Qed.

Lemma locked_final_no_hit_occ :
  forall i j p, ~ circ_leftover_hit_occ locked_circ_final_bag i j p.
Proof.
  intros i j p [Hij [ua [ub [a [bsp [Ha [Hb [_ Hhit]]]]]]]].
  apply (locked_final_pair_no_hit a bsp p ua ub).
  - apply (locked_final_nth_span i a Ha).
  - apply (locked_final_nth_span j bsp Hb).
  - exact Hhit.
Qed.

Lemma locked_final_term_measure :
  circ_leftover_bag_measure locked_circ_final_bag 0.
Proof.
  exists [].
  split; [|reflexivity].
  split.
  - intros ijp Hin. contradiction.
  - split.
    + intros i j p Hocc. exact (locked_final_no_hit_occ i j p Hocc).
    + apply NoDup_nil.
Qed.

Lemma locked_circ_measure_first_decreases :
  forall n m,
    circ_leftover_bag_measure locked_circ_parent_bag n ->
    circ_leftover_bag_measure locked_circ_mid_bag m ->
    (m < n)%nat.
Proof.
  intros n m Hn Hm.
  pose proof (circ_leftover_bag_measure_unique
                locked_circ_parent_bag n 2 Hn locked_parent_term_measure) as En.
  pose proof (circ_leftover_bag_measure_unique
                locked_circ_mid_bag m 1 Hm locked_mid_term_measure) as Em.
  subst n m. lia.
Qed.

Lemma locked_circ_measure_second_decreases :
  forall n m,
    circ_leftover_bag_measure locked_circ_mid_bag n ->
    circ_leftover_bag_measure locked_circ_final_bag m ->
    (m < n)%nat.
Proof.
  intros n m Hn Hm.
  pose proof (circ_leftover_bag_measure_unique
                locked_circ_mid_bag n 1 Hn locked_mid_term_measure) as En.
  pose proof (circ_leftover_bag_measure_unique
                locked_circ_final_bag m 0 Hm locked_final_term_measure) as Em.
  subst n m. lia.
Qed.

Lemma circ_leftover_bag_measure_decline_idle :
  forall b i j n,
    circ_leftover_pair_decline b i j ->
    circ_leftover_bag_step b b /\
    (circ_leftover_bag_measure b n -> circ_leftover_bag_measure b n).
Proof.
  intros b i j n Hd.
  split.
  - apply (CStepDecline b i j Hd).
  - intros Hm. exact Hm.
Qed.

(* -------------------------------------------------------------------------- *)
(* Noded G after the two Hits. Two point-hens (p+, p*) and leftover           *)
(* circular eggs as chickens between hens. Not Overlay.                       *)
(* -------------------------------------------------------------------------- *)

Record CircNodedG : Type := mkCircNodedG {
  cng_sheet : Sheet;
  cng_hen_plus : Hen;
  cng_hen_minus : Hen;
  cng_p_plus : Point;
  cng_p_minus : Point;
  cng_cks : list Chicken
}.

Definition locked_hen_plus : Hen := 4%nat.
Definition locked_hen_minus : Hen := 5%nat.

Definition locked_ck_A0 : Chicken :=
  mkChicken 0%nat locked_hen_minus (MkCirc (circ_leftover_egg locked_A0)).
Definition locked_ck_A1 : Chicken :=
  mkChicken locked_hen_minus locked_hen_plus
    (MkCirc (circ_leftover_egg locked_A1)).
Definition locked_ck_A2 : Chicken :=
  mkChicken locked_hen_plus 1%nat (MkCirc (circ_leftover_egg locked_A2)).
Definition locked_ck_B0 : Chicken :=
  mkChicken 2%nat locked_hen_plus (MkCirc (circ_leftover_egg locked_B0)).
Definition locked_ck_B1 : Chicken :=
  mkChicken locked_hen_plus locked_hen_minus
    (MkCirc (circ_leftover_egg locked_B1)).
Definition locked_ck_B2 : Chicken :=
  mkChicken locked_hen_minus 3%nat (MkCirc (circ_leftover_egg locked_B2)).

Definition locked_noded_g : CircNodedG :=
  mkCircNodedG default_sheet locked_hen_plus locked_hen_minus
    locked_p_plus locked_p_minus
    [locked_ck_A0; locked_ck_A1; locked_ck_A2;
     locked_ck_B0; locked_ck_B1; locked_ck_B2].

Definition circ_on_chicken (c : Chicken) (t : R) (p : Point) : Prop :=
  match ck_egg c with
  | MkCirc e => on_circ e t p
  | _ => False
  end.

Definition at_hen_endpoint (e : CircularEgg) (p : Point) : Prop :=
  p = circ_start e \/ p = circ_end e.

Definition circ_edge_meet (e1 e2 : CircularEgg) (p : Point) : Prop :=
  exists t1 t2, on_circ e1 t1 p /\ on_circ e2 t2 p.

Definition locked_noded_eggs : list CircularEgg :=
  [circ_leftover_egg locked_A0; circ_leftover_egg locked_A1;
   circ_leftover_egg locked_A2; circ_leftover_egg locked_B0;
   circ_leftover_egg locked_B1; circ_leftover_egg locked_B2].

Lemma locked_noded_hens_are_the_two_hits :
  cng_p_plus locked_noded_g = locked_p_plus /\
  cng_p_minus locked_noded_g = locked_p_minus /\
  cng_hen_plus locked_noded_g = locked_hen_plus /\
  cng_hen_minus locked_noded_g = locked_hen_minus.
Proof.
  repeat split; reflexivity.
Qed.

Lemma locked_noded_chickens_circular :
  forall c, In c (cng_cks locked_noded_g) ->
    egg_class (ck_egg c) = EggCircularArc.
Proof.
  intros c Hin.
  unfold locked_noded_g in Hin. simpl in Hin.
  repeat (destruct Hin as [Heq|Hin]; [subst c; reflexivity|]).
  contradiction.
Qed.

Lemma locked_noded_pairs_no_interior_hit :
  circ_leftover_bag_measure locked_circ_final_bag 0.
Proof.
  exact locked_final_term_measure.
Qed.

Lemma locked_leftover_start_end :
  forall s,
    circ_start (circ_leftover_egg s) =
      circ_eval (cls_parent s) (cls_t0 s) /\
    circ_end (circ_leftover_egg s) =
      circ_eval (cls_parent s) (cls_t1 s).
Proof.
  intros s.
  unfold circ_start, circ_end.
  rewrite circ_leftover_eval_parent, circ_leftover_eval_parent.
  unfold circ_leftover_span_at.
  split; apply f_equal; ring.
Qed.

Lemma locked_A0_endpoints :
  circ_start (circ_leftover_egg locked_A0) = circ_eval locked_twohit_A 0 /\
  circ_end (circ_leftover_egg locked_A0) = locked_p_minus.
Proof.
  destruct (locked_leftover_start_end locked_A0) as [Hs He].
  unfold locked_A0 in Hs, He. simpl in Hs, He.
  rewrite locked_twohit_A_at_minus in He.
  split; [exact Hs|exact He].
Qed.

Lemma locked_A1_endpoints :
  circ_start (circ_leftover_egg locked_A1) = locked_p_minus /\
  circ_end (circ_leftover_egg locked_A1) = locked_p_plus.
Proof.
  destruct (locked_leftover_start_end locked_A1) as [Hs He].
  unfold locked_A1 in Hs, He. simpl in Hs, He.
  rewrite locked_twohit_A_at_minus in Hs.
  rewrite locked_twohit_A_at_plus in He.
  split; [exact Hs|exact He].
Qed.

Lemma locked_A2_endpoints :
  circ_start (circ_leftover_egg locked_A2) = locked_p_plus /\
  circ_end (circ_leftover_egg locked_A2) = circ_eval locked_twohit_A 1.
Proof.
  destruct (locked_leftover_start_end locked_A2) as [Hs He].
  unfold locked_A2 in Hs, He. simpl in Hs, He.
  rewrite locked_twohit_A_at_plus in Hs.
  split; [exact Hs|exact He].
Qed.

Lemma locked_B0_endpoints :
  circ_start (circ_leftover_egg locked_B0) = circ_eval locked_twohit_B 0 /\
  circ_end (circ_leftover_egg locked_B0) = locked_p_plus.
Proof.
  destruct (locked_leftover_start_end locked_B0) as [Hs He].
  unfold locked_B0 in Hs, He. simpl in Hs, He.
  rewrite locked_twohit_B_at_plus in He.
  split; [exact Hs|exact He].
Qed.

Lemma locked_B1_endpoints :
  circ_start (circ_leftover_egg locked_B1) = locked_p_plus /\
  circ_end (circ_leftover_egg locked_B1) = locked_p_minus.
Proof.
  destruct (locked_leftover_start_end locked_B1) as [Hs He].
  unfold locked_B1 in Hs, He. simpl in Hs, He.
  rewrite locked_twohit_B_at_plus in Hs.
  rewrite locked_twohit_B_at_minus in He.
  split; [exact Hs|exact He].
Qed.

Lemma locked_B2_endpoints :
  circ_start (circ_leftover_egg locked_B2) = locked_p_minus /\
  circ_end (circ_leftover_egg locked_B2) = circ_eval locked_twohit_B 1.
Proof.
  destruct (locked_leftover_start_end locked_B2) as [Hs He].
  unfold locked_B2 in Hs, He. simpl in Hs, He.
  rewrite locked_twohit_B_at_minus in Hs.
  split; [exact Hs|exact He].
Qed.

Lemma locked_on_leftover_parent_t :
  forall s t p,
    on_circ (circ_leftover_egg s) t p ->
    0 <= circ_leftover_span_at s t <= 1 ->
    on_circ (cls_parent s) (circ_leftover_span_at s t) p.
Proof.
  intros s t p Hon _.
  apply (proj1 (circ_leftover_on_parent s t p Hon)).
Qed.

Lemma locked_noded_meet_only_at_hens :
  forall e1 e2 p,
    In e1 locked_noded_eggs ->
    In e2 locked_noded_eggs ->
    e1 <> e2 ->
    circ_edge_meet e1 e2 p ->
    at_hen_endpoint e1 p /\ at_hen_endpoint e2 p.
Proof.
  intros e1 e2 p Hin1 Hin2 Hne [t1 [t2 [Hon1 Hon2]]].
  unfold locked_noded_eggs in Hin1, Hin2.
  simpl in Hin1, Hin2.
  assert (span_of : forall e,
      In e locked_noded_eggs ->
      exists s, e = circ_leftover_egg s /\
        (s = locked_A0 \/ s = locked_A1 \/ s = locked_A2 \/
         s = locked_B0 \/ s = locked_B1 \/ s = locked_B2)).
  { intros e Hin.
    unfold locked_noded_eggs in Hin. simpl in Hin.
    repeat (destruct Hin as [Heq|Hin];
            [subst e; eexists; split; [reflexivity|auto 10]|]).
    contradiction. }
  destruct (span_of e1 Hin1) as [s1 [He1 Hs1]].
  destruct (span_of e2 Hin2) as [s2 [He2 Hs2]].
  subst e1 e2.
  pose proof (circ_leftover_on_parent s1 t1 p Hon1) as [onP1 open1].
  pose proof (circ_leftover_on_parent s2 t2 p Hon2) as [onP2 open2].
  assert (Hcls1 : cls_parent s1 = locked_twohit_A \/
                  cls_parent s1 = locked_twohit_B).
  { destruct Hs1 as [H|[H|[H|[H|[H|H]]]]]; subst; auto. }
  assert (Hcls2 : cls_parent s2 = locked_twohit_A \/
                  cls_parent s2 = locked_twohit_B).
  { destruct Hs2 as [H|[H|[H|[H|[H|H]]]]]; subst; auto. }
  assert (Ht1c : 0 <= t1 <= 1) by (destruct Hon1 as [Ht _]; exact Ht).
  assert (Ht2c : 0 <= t2 <= 1) by (destruct Hon2 as [Ht _]; exact Ht).
  destruct Hcls1 as [P1|P1]; destruct Hcls2 as [P2|P2].
  - rewrite P1 in onP1. rewrite P2 in onP2.
    unfold on_circ in onP1, onP2.
    destruct onP1 as [rng1 Ev1]. destruct onP2 as [rng2 Ev2].
    rewrite Ev2 in Ev1.
    apply locked_A_eval_inj in Ev1; [|exact rng1|exact rng2].
    assert (t0t1 : cls_t0 s1 <= circ_leftover_span_at s1 t1 <= cls_t1 s1).
    { unfold circ_leftover_span_at. nra. }
    assert (t0t2 : cls_t0 s2 <= circ_leftover_span_at s2 t2 <= cls_t1 s2).
    { unfold circ_leftover_span_at. nra. }
    rewrite Ev1 in t0t1.
    unfold at_hen_endpoint.
    destruct (locked_leftover_start_end s1) as [St1 En1].
    destruct (locked_leftover_start_end s2) as [St2 En2].
    unfold circ_leftover_span_at in Ev1, t0t1, t0t2.
    assert (Hjoin : circ_leftover_span_at s1 t1 = cls_t0 s1 \/
                    circ_leftover_span_at s1 t1 = cls_t1 s1).
    { unfold circ_leftover_span_at in *.
      destruct Hs1 as [H1|[H1|[H1|[H1|[H1|H1]]]]];
      destruct Hs2 as [H2|[H2|[H2|[H2|[H2|H2]]]]];
      subst s1 s2; simpl in *;
      try (exfalso; apply Hne; reflexivity);
      try lra. }
    unfold circ_leftover_span_at in Hjoin.
    split.
    + destruct Hjoin as [Hj|Hj].
      * left. rewrite St1. apply f_equal. unfold circ_leftover_span_at in Ev1.
        rewrite <- Hj. unfold circ_leftover_span_at. reflexivity.
      * right. rewrite En1. apply f_equal. rewrite <- Hj.
        unfold circ_leftover_span_at. reflexivity.
    + rewrite Ev1 in t0t2.
      assert (Hjoin2 : circ_leftover_span_at s2 t2 = cls_t0 s2 \/
                       circ_leftover_span_at s2 t2 = cls_t1 s2).
      { unfold circ_leftover_span_at in *.
        destruct Hs1 as [H1|[H1|[H1|[H1|[H1|H1]]]]];
        destruct Hs2 as [H2|[H2|[H2|[H2|[H2|H2]]]]];
        subst s1 s2; simpl in *;
        try (exfalso; apply Hne; reflexivity);
        try lra. }
      destruct Hjoin2 as [Hj|Hj].
      * left. rewrite St2. apply f_equal. rewrite <- Hj.
        unfold circ_leftover_span_at. reflexivity.
      * right. rewrite En2. apply f_equal. rewrite <- Hj.
        unfold circ_leftover_span_at. reflexivity.
  - rewrite P1 in onP1. rewrite P2 in onP2.
    pose proof (locked_meet_is_plus_or_minus p _ _ onP1 onP2) as Hm.
    unfold at_hen_endpoint.
    destruct (locked_leftover_start_end s1) as [St1 En1].
    destruct (locked_leftover_start_end s2) as [St2 En2].
    destruct Hm as [Hp|Hp]; subst p.
    + split.
      * destruct Hs1 as [H|[H|[H|[H|[H|H]]]]]; subst s1;
          try (right; rewrite En1; unfold locked_A0, locked_A1, locked_A2,
               locked_B0, locked_B1, locked_B2 in En1; simpl in En1;
               rewrite ?locked_twohit_A_at_plus, ?locked_twohit_B_at_plus;
               reflexivity);
          try (left; rewrite St1; unfold locked_A2, locked_B0, locked_B1,
               locked_A0, locked_A1, locked_B2 in St1; simpl in St1;
               rewrite ?locked_twohit_A_at_plus, ?locked_twohit_B_at_plus;
               reflexivity).
        -- (* A0 does not contain p+ *)
           pose proof (locked_on_A_plus_t (circ_leftover_span_at locked_A0 t1)
                         onP1) as Ht.
           unfold circ_leftover_span_at, locked_A0 in Ht. simpl in Ht. lra.
        -- pose proof (locked_on_A_plus_t (circ_leftover_span_at locked_A1 t1)
                         onP1) as Ht.
           unfold circ_leftover_span_at, locked_A1 in Ht. simpl in Ht.
           right. rewrite En1. unfold locked_A1. simpl.
           rewrite locked_twohit_A_at_plus. reflexivity.
        -- left. rewrite St1. unfold locked_A2. simpl.
           rewrite locked_twohit_A_at_plus. reflexivity.
        -- pose proof (locked_on_B_plus_t (circ_leftover_span_at locked_B2 t1)
                         onP1) as Ht.
           unfold circ_leftover_span_at, locked_B2 in Ht. simpl in Ht. lra.
      * destruct Hs2 as [H|[H|[H|[H|[H|H]]]]]; subst s2;
          try (right; rewrite En2; unfold locked_A0, locked_A1, locked_A2,
               locked_B0, locked_B1, locked_B2 in En2; simpl in En2;
               rewrite ?locked_twohit_A_at_plus, ?locked_twohit_B_at_plus;
               reflexivity);
          try (left; rewrite St2; unfold locked_A2, locked_B0, locked_B1,
               locked_A0, locked_A1, locked_B2 in St2; simpl in St2;
               rewrite ?locked_twohit_A_at_plus, ?locked_twohit_B_at_plus;
               reflexivity).
        -- pose proof (locked_on_B_plus_t (circ_leftover_span_at locked_B0 t2)
                         onP2) as Ht.
           unfold circ_leftover_span_at, locked_B0 in Ht. simpl in Ht.
           right. rewrite En2. unfold locked_B0. simpl.
           rewrite locked_twohit_B_at_plus. reflexivity.
        -- left. rewrite St2. unfold locked_B1. simpl.
           rewrite locked_twohit_B_at_plus. reflexivity.
        -- pose proof (locked_on_B_plus_t (circ_leftover_span_at locked_B2 t2)
                         onP2) as Ht.
           unfold circ_leftover_span_at, locked_B2 in Ht. simpl in Ht. lra.
    + split.
      * destruct Hs1 as [H|[H|[H|[H|[H|H]]]]]; subst s1.
        -- right. apply locked_A0_endpoints.
        -- left. apply locked_A1_endpoints.
        -- pose proof (locked_on_A_minus_t (circ_leftover_span_at locked_A2 t1)
                         onP1) as Ht.
           unfold circ_leftover_span_at, locked_A2 in Ht. simpl in Ht. lra.
        -- pose proof (locked_on_B_minus_t (circ_leftover_span_at locked_B0 t1)
                         onP1) as Ht.
           unfold circ_leftover_span_at, locked_B0 in Ht. simpl in Ht. lra.
        -- right. apply locked_B1_endpoints.
        -- left. apply locked_B2_endpoints.
      * destruct Hs2 as [H|[H|[H|[H|[H|H]]]]]; subst s2.
        -- right. apply locked_A0_endpoints.
        -- left. apply locked_A1_endpoints.
        -- pose proof (locked_on_A_minus_t (circ_leftover_span_at locked_A2 t2)
                         onP2) as Ht.
           unfold circ_leftover_span_at, locked_A2 in Ht. simpl in Ht. lra.
        -- pose proof (locked_on_B_minus_t (circ_leftover_span_at locked_B0 t2)
                         onP2) as Ht.
           unfold circ_leftover_span_at, locked_B0 in Ht. simpl in Ht. lra.
        -- right. apply locked_B1_endpoints.
        -- left. apply locked_B2_endpoints.
  - rewrite P1 in onP1. rewrite P2 in onP2.
    pose proof (locked_meet_is_plus_or_minus p _ _ onP2 onP1) as Hm.
    unfold at_hen_endpoint.
    destruct Hm as [Hp|Hp]; subst p.
    + split.
      * destruct Hs1 as [H|[H|[H|[H|[H|H]]]]]; subst s1.
        -- pose proof (locked_on_B_plus_t (circ_leftover_span_at locked_A0 t1)
                         onP1) as Ht.
           unfold circ_leftover_span_at, locked_A0 in Ht. simpl in Ht. lra.
        -- pose proof (locked_on_B_plus_t (circ_leftover_span_at locked_A1 t1)
                         onP1) as Ht.
           unfold circ_leftover_span_at, locked_A1 in Ht. simpl in Ht. lra.
        -- pose proof (locked_on_B_plus_t (circ_leftover_span_at locked_A2 t1)
                         onP1) as Ht.
           unfold circ_leftover_span_at, locked_A2 in Ht. simpl in Ht. lra.
        -- right. apply locked_B0_endpoints.
        -- left. apply locked_B1_endpoints.
        -- pose proof (locked_on_B_plus_t (circ_leftover_span_at locked_B2 t1)
                         onP1) as Ht.
           unfold circ_leftover_span_at, locked_B2 in Ht. simpl in Ht. lra.
      * destruct Hs2 as [H|[H|[H|[H|[H|H]]]]]; subst s2.
        -- pose proof (locked_on_A_plus_t (circ_leftover_span_at locked_A0 t2)
                         onP2) as Ht.
           unfold circ_leftover_span_at, locked_A0 in Ht. simpl in Ht. lra.
        -- right. apply locked_A1_endpoints.
        -- left. apply locked_A2_endpoints.
        -- pose proof (locked_on_A_plus_t (circ_leftover_span_at locked_B0 t2)
                         onP2) as Ht.
           unfold circ_leftover_span_at, locked_B0 in Ht. simpl in Ht. lra.
        -- pose proof (locked_on_A_plus_t (circ_leftover_span_at locked_B1 t2)
                         onP2) as Ht.
           unfold circ_leftover_span_at, locked_B1 in Ht. simpl in Ht. lra.
        -- pose proof (locked_on_A_plus_t (circ_leftover_span_at locked_B2 t2)
                         onP2) as Ht.
           unfold circ_leftover_span_at, locked_B2 in Ht. simpl in Ht. lra.
    + split.
      * destruct Hs1 as [H|[H|[H|[H|[H|H]]]]]; subst s1.
        -- pose proof (locked_on_B_minus_t (circ_leftover_span_at locked_A0 t1)
                         onP1) as Ht.
           unfold circ_leftover_span_at, locked_A0 in Ht. simpl in Ht. lra.
        -- pose proof (locked_on_B_minus_t (circ_leftover_span_at locked_A1 t1)
                         onP1) as Ht.
           unfold circ_leftover_span_at, locked_A1 in Ht. simpl in Ht. lra.
        -- pose proof (locked_on_B_minus_t (circ_leftover_span_at locked_A2 t1)
                         onP1) as Ht.
           unfold circ_leftover_span_at, locked_A2 in Ht. simpl in Ht. lra.
        -- pose proof (locked_on_B_minus_t (circ_leftover_span_at locked_B0 t1)
                         onP1) as Ht.
           unfold circ_leftover_span_at, locked_B0 in Ht. simpl in Ht. lra.
        -- right. apply locked_B1_endpoints.
        -- left. apply locked_B2_endpoints.
      * destruct Hs2 as [H|[H|[H|[H|[H|H]]]]]; subst s2.
        -- right. apply locked_A0_endpoints.
        -- left. apply locked_A1_endpoints.
        -- pose proof (locked_on_A_minus_t (circ_leftover_span_at locked_A2 t2)
                         onP2) as Ht.
           unfold circ_leftover_span_at, locked_A2 in Ht. simpl in Ht. lra.
        -- pose proof (locked_on_A_minus_t (circ_leftover_span_at locked_B0 t2)
                         onP2) as Ht.
           unfold circ_leftover_span_at, locked_B0 in Ht. simpl in Ht. lra.
        -- pose proof (locked_on_A_minus_t (circ_leftover_span_at locked_B1 t2)
                         onP2) as Ht.
           unfold circ_leftover_span_at, locked_B1 in Ht. simpl in Ht. lra.
        -- pose proof (locked_on_A_minus_t (circ_leftover_span_at locked_B2 t2)
                         onP2) as Ht.
           unfold circ_leftover_span_at, locked_B2 in Ht. simpl in Ht. lra.
  - rewrite P1 in onP1. rewrite P2 in onP2.
    unfold on_circ in onP1, onP2.
    destruct onP1 as [rng1 Ev1]. destruct onP2 as [rng2 Ev2].
    rewrite Ev2 in Ev1.
    apply locked_B_eval_inj in Ev1; [|exact rng1|exact rng2].
    unfold at_hen_endpoint.
    destruct (locked_leftover_start_end s1) as [St1 En1].
    destruct (locked_leftover_start_end s2) as [St2 En2].
    assert (Hjoin : circ_leftover_span_at s1 t1 = cls_t0 s1 \/
                    circ_leftover_span_at s1 t1 = cls_t1 s1).
    { unfold circ_leftover_span_at in *.
      destruct Hs1 as [H1|[H1|[H1|[H1|[H1|H1]]]]];
      destruct Hs2 as [H2|[H2|[H2|[H2|[H2|H2]]]]];
      subst s1 s2; simpl in *;
      try (exfalso; apply Hne; reflexivity);
      try lra. }
    split.
    + destruct Hjoin as [Hj|Hj].
      * left. rewrite St1. apply f_equal. rewrite <- Hj.
        unfold circ_leftover_span_at. reflexivity.
      * right. rewrite En1. apply f_equal. rewrite <- Hj.
        unfold circ_leftover_span_at. reflexivity.
    + assert (Hjoin2 : circ_leftover_span_at s2 t2 = cls_t0 s2 \/
                       circ_leftover_span_at s2 t2 = cls_t1 s2).
      { unfold circ_leftover_span_at in *.
        destruct Hs1 as [H1|[H1|[H1|[H1|[H1|H1]]]]];
        destruct Hs2 as [H2|[H2|[H2|[H2|[H2|H2]]]]];
        subst s1 s2; simpl in *;
        try (exfalso; apply Hne; reflexivity);
        try lra. }
      destruct Hjoin2 as [Hj|Hj].
      * left. rewrite St2. apply f_equal. rewrite <- Hj.
        unfold circ_leftover_span_at. reflexivity.
      * right. rewrite En2. apply f_equal. rewrite <- Hj.
        unfold circ_leftover_span_at. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Park: this letter does not flip cook_loop_status / LeftoverBagTermArm.     *)
(* -------------------------------------------------------------------------- *)

Lemma circ_leftover_park_unchanged :
  cook_loop_status = LoopObligation /\
  cook_loop_status <> LoopDischarged /\
  ~ leftover_bag_term_arm /\
  LeftoverBagTermArm = leftover_bag_term_arm /\
  leftover_bag_term_arm =
    (leftover_quad_width_decreases
     /\ leftover_quad_kiss_arm
     /\ leftover_quad_share_mint_arm) /\
  ~ leftover_quad_width_decreases /\
  ~ leftover_quad_kiss_arm /\
  ~ leftover_quad_share_mint_arm.
Proof.
  split; [exact cook_loop_is_obligation|].
  split; [exact cook_loop_not_discharged|].
  split; [exact leftover_bag_term_arm_missing|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact leftover_quad_width_does_not_decrease|].
  split; [exact leftover_quad_kiss_arm_missing|].
  exact leftover_quad_share_mint_arm_missing.
Qed.

(* General circ bag-term / LoopDischarged-for-circ stays missing. *)
Definition circ_leftover_loop_discharged : Prop :=
  cook_loop_status = LoopDischarged.

Lemma circ_leftover_loop_discharged_missing :
  ~ circ_leftover_loop_discharged.
Proof.
  unfold circ_leftover_loop_discharged.
  exact cook_loop_not_discharged.
Qed.

Definition circ_leftover_general_term : Prop :=
  circ_leftover_bag_term_forall
  /\ leftover_quad_kiss_arm
  /\ leftover_quad_share_mint_arm.

Lemma circ_leftover_general_term_missing :
  ~ circ_leftover_general_term.
Proof.
  intros [_ [Hk _]].
  exact (leftover_quad_kiss_arm_missing Hk).
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-circ-leftover-two-hit","topic":"overlay","lemma":"ticket_0007_circ_leftover_two_hit_qed_or_qex","title":"circ leftover |H|=2: locked vesica measure 2 to 1 to 0 on two interior Hits, children stay circular, endpoint-only and cocircular overlap Decline, noded G leftover pairs have no interior Hit and edges meet only at the two point-hens (QED) or leftover_quad_width_decreases (QEX); discharged QED; locked lens only, not forall-bag decrease; not leftover_quad_width","file":"theories/CircularCookLeftoverTwoHit.v","witness":"0007-circ-leftover-two-hit","board":"ADR-0007"} *)
Theorem ticket_0007_circ_leftover_two_hit_qed_or_qex :
  (circ_leftover_bag_measure locked_circ_parent_bag 2 /\
   circ_leftover_bag_measure locked_circ_mid_bag 1 /\
   circ_leftover_bag_measure locked_circ_final_bag 0 /\
   circ_leftover_bag_step locked_circ_parent_bag locked_circ_mid_bag /\
   circ_leftover_bag_step locked_circ_mid_bag locked_circ_final_bag /\
   circ_leftover_pair_step_ok locked_circ_parent_bag 0 1
     locked_p_plus (5 / 6) (1 / 6) /\
   circ_leftover_pair_step_ok locked_circ_parent_bag 0 1
     locked_p_minus (1 / 6) (5 / 6) /\
   egg_class (MkCirc (circ_leftover_egg locked_A_lo)) = EggCircularArc /\
   egg_class (ck_egg (cp_left1 cooked_mkcirc)) = EggCircularArc /\
   circ_leftover_pair_decline locked_circ_mid_bag 1 2 /\
   (forall p ua ub,
      ~ circ_leftover_pair_hit locked_twohit_A_span
          locked_twohit_A_span p ua ub) /\
   CircNodedG = CircNodedG /\
   cng_p_plus locked_noded_g = locked_p_plus /\
   cng_p_minus locked_noded_g = locked_p_minus /\
   circ_leftover_bag_measure locked_circ_final_bag 0 /\
   (forall e1 e2 p,
      In e1 locked_noded_eggs ->
      In e2 locked_noded_eggs ->
      e1 <> e2 ->
      circ_edge_meet e1 e2 p ->
      at_hen_endpoint e1 p /\ at_hen_endpoint e2 p) /\
   well_founded Nat.lt)
  \/ leftover_quad_width_decreases.
Proof.
  left.
  split; [exact locked_parent_term_measure|].
  split; [exact locked_mid_term_measure|].
  split; [exact locked_final_term_measure|].
  split; [exact locked_circ_hit_step_first|].
  split; [exact locked_circ_hit_step_second|].
  split; [exact locked_parent_plus_step_ok|].
  split; [exact locked_parent_minus_step_ok|].
  split; [reflexivity|].
  split; [apply (proj1 unique_mkcirc_children_circular)|].
  split; [exact locked_endpoint_only_decline|].
  split; [exact locked_cocircular_overlap_decline|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact locked_final_term_measure|].
  split; [exact locked_noded_meet_only_at_hens|].
  exact circ_leftover_bag_measure_nat_wf.
Qed.

(* WITNESS {"claimId":"0007-circ-leftover-two-hit","topic":"overlay","lemma":"ticket_0007_circ_leftover_two_hit_park_qed_or_qex","title":"circ leftover |H|=2 park: general circ bag-term / LoopDischarged-for-circ and kiss/share identity inhabit (QED) or those stay missing, chord LeftoverBagTermArm stays missing, and cook_loop stays LoopObligation (QEX); discharged QEX; this letter is not rho discharge","file":"theories/CircularCookLeftoverTwoHit.v","witness":"0007-circ-leftover-two-hit","board":"ADR-0007"} *)
Theorem ticket_0007_circ_leftover_two_hit_park_qed_or_qex :
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
   /\ ~ circ_leftover_loop_discharged
   /\ ~ circ_leftover_general_term).
Proof.
  right.
  destruct circ_leftover_park_unchanged as [H1 [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]].
  repeat split; try assumption.
  - exact circ_leftover_loop_discharged_missing.
  - exact circ_leftover_general_term_missing.
Qed.

Print Assumptions circ_leftover_bag_measure_nat_wf.
Print Assumptions circ_leftover_eval_parent.
Print Assumptions circ_leftover_split_matches_circ_split.
Print Assumptions unique_mkcirc_children_circular.
Print Assumptions locked_twohit_I_ok_plus.
Print Assumptions locked_twohit_I_ok_minus.
Print Assumptions locked_meet_is_plus_or_minus.
Print Assumptions locked_circ_hit_step_first.
Print Assumptions locked_circ_hit_step_second.
Print Assumptions locked_parent_term_measure.
Print Assumptions locked_mid_term_measure.
Print Assumptions locked_final_term_measure.
Print Assumptions locked_circ_measure_first_decreases.
Print Assumptions locked_circ_measure_second_decreases.
Print Assumptions locked_cocircular_overlap_decline.
Print Assumptions locked_endpoint_only_decline.
Print Assumptions locked_noded_meet_only_at_hens.
Print Assumptions circ_leftover_park_unchanged.
Print Assumptions ticket_0007_circ_leftover_two_hit_qed_or_qex.
Print Assumptions ticket_0007_circ_leftover_two_hit_park_qed_or_qex.

