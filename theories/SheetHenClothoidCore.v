(* ============================================================================
   NetTopologySuite.Proofs.SheetHenClothoidEgg
   ----------------------------------------------------------------------------
   Host clothoid gamma. ISO/IEC 13249-3 ST_Clothoid (concept 4.2.11,
   type 7.8.1 rules 8-15, ST_StartPoint / ST_EndPoint 7.8.9 / 7.8.10)
   says the start and end points are calculated from the placement,
   the scale factor and the two distances, and does not print a
   formula. The parameterisation below is OUR choice, not an ISO
   formula. It is the oracle K token (oracle/driver.ml): one tangent
   at the inflection, scale A, distances sd and ed along the arc.

   Placement: origin LOCATION plus exactly two reference vectors
   (rule 12). Heading and position, with s the signed arc length from
   the inflection:
     phi(s) = phi0 + sigma * s^2 / (2 A^2)
     P(s)   = LOCATION + integral_0^s (cos phi(u), sin phi(u)) du
   phi0 is the direction of the first reference vector (its unit
   vector; no atan2). sigma is the sign of ref1 x ref2: +1 when the
   cross is nonnegative, otherwise -1. sigma = +1 is the oracle
   heading phi(s) = phi0 + s^2 / (2 A^2); the oracle token has no
   second vector, and the right-handed frame is that choice. The
   second vector is carried and used only for this handedness sign.
   Equivalent normalised form, sigma = +1 only:
     P = LOCATION + R(phi0) * A * sqrt(pi)
           * (C(s / (A * sqrt(pi))), S(s / (A * sqrt(pi))))
   where C and S are the Fresnel integrals of cos(pi t^2 / 2) and
   sin(pi t^2 / 2). Host eval is planar (rules 10-11, the 3D reading
   of the placement, are out of scope):
     gamma(t) = P(sd + t * (ed - sd)), t in [0,1].
   Rule 8: cloth_m0 and cloth_m1 are both None or both Some.
   Rule 9: the egg is measured exactly in the both-Some case.
   Endpoints are not stored. cloth_p0 / cloth_p1 are gamma(0) / gamma(1).
   Raw mkClothoidEgg cannot store a stale endpoint; cloth_wf is the
   constraint (A > 0, first vector nonzero, the two vectors not
   parallel, rule 8). Split is a sub-window of the same placement and
   A; child measures are None (a sub-arc does not inherit M).
   A = 0 is a total degenerate (Rinv 0 = 0), not well-formed.
   sd = ed is a constant gamma. The zero window sd = ed = 0 sits at
   LOCATION.

   CIRCLE-class intake exception: the example5 WKT seed was the chord
   (0,0)-(1,0). The locked bag is the law (parameterised WKT intake
   of arbitrary A, sd, ed is out of scope); its points are gamma ends
   of locked_clothoid_egg, not that chord seed.
   claimId: 0007-clothoid-first-cook / 0007-intake-mkclothoid
   WITNESS topic: overlay · board: ADR-0007.
   Stdlib RiemannInt. Print Assumptions of lemmas that mention
   cloth_eval include Classical_Prop.classic (Category C), same
   mechanism as ClothoidFresnelInhab. No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals RiemannInt Ranalysis1 Rtrigo1 Rtrigo_alt
  Ratan Lra Arith.Factorial.
From Stdlib Require Import Ranalysis_reg.
From NTS.Proofs Require Import Distance.
Local Open Scope R_scope.

Record AffPlace : Type := mkAffPlace {
  aff_loc : Point;
  aff_ref1 : Point;
  aff_ref2 : Point
}.

Record ClothoidEgg : Type := mkClothoidEgg {
  cloth_place : AffPlace;
  cloth_A : R;
  cloth_sd : R;
  cloth_ed : R;
  cloth_m0 : option R;
  cloth_m1 : option R
}.

Definition mk_cloth (pl : AffPlace) (A sd ed : R) (m0 m1 : option R)
  : ClothoidEgg :=
  mkClothoidEgg pl A sd ed m0 m1.

Definition aff_h2 (pl : AffPlace) : R :=
  px (aff_ref1 pl) * px (aff_ref1 pl) + py (aff_ref1 pl) * py (aff_ref1 pl).

Definition aff_cross (pl : AffPlace) : R :=
  px (aff_ref1 pl) * py (aff_ref2 pl) - py (aff_ref1 pl) * px (aff_ref2 pl).

Definition cloth_h2 (c : ClothoidEgg) : R := aff_h2 (cloth_place c).
Definition cloth_cross (c : ClothoidEgg) : R := aff_cross (cloth_place c).

Definition cloth_sigma (c : ClothoidEgg) : R :=
  if Rle_dec 0 (cloth_cross c) then 1 else -1.

Definition cloth_hypot (c : ClothoidEgg) : R := sqrt (cloth_h2 c).

Definition cloth_cos0 (c : ClothoidEgg) : R :=
  px (aff_ref1 (cloth_place c)) / cloth_hypot c.

Definition cloth_sin0 (c : ClothoidEgg) : R :=
  py (aff_ref1 (cloth_place c)) / cloth_hypot c.

Definition cloth_psi (c : ClothoidEgg) (s : R) : R :=
  cloth_sigma c * s * s / (2 * cloth_A c * cloth_A c).

Definition cloth_vx (c : ClothoidEgg) (s : R) : R :=
  cloth_cos0 c * cos (cloth_psi c s) - cloth_sin0 c * sin (cloth_psi c s).

Definition cloth_vy (c : ClothoidEgg) (s : R) : R :=
  cloth_sin0 c * cos (cloth_psi c s) + cloth_cos0 c * sin (cloth_psi c s).

Definition cloth_th (c : ClothoidEgg) (t : R) : R :=
  cloth_psi c (cloth_sd c + t * (cloth_ed c - cloth_sd c)).

Lemma cont_id : forall x, continuity_pt id x.
Proof.
  intro x. apply derivable_continuous_pt. apply derivable_pt_id.
Qed.

Lemma cloth_psi_cont : forall c x, continuity_pt (cloth_psi c) x.
Proof.
  intros c x.
  apply continuity_pt_locally_ext with
    (f := mult_real_fct
            (cloth_sigma c * / (2 * cloth_A c * cloth_A c))
            (fun s => s * s))
    (a := 1).
  - lra.
  - intros y _. unfold cloth_psi, Rdiv, mult_real_fct. ring.
  - apply continuity_pt_scal.
    apply continuity_pt_mult; apply cont_id.
Qed.

Lemma cloth_vx_cont : forall c x, continuity_pt (cloth_vx c) x.
Proof.
  intros c x. unfold cloth_vx.
  apply continuity_pt_minus.
  - apply continuity_pt_mult.
    + apply continuity_pt_const. intros a b. reflexivity.
    + change (continuity_pt (comp cos (cloth_psi c)) x).
      apply continuity_pt_comp; [apply cloth_psi_cont | apply continuity_cos].
  - apply continuity_pt_mult.
    + apply continuity_pt_const. intros a b. reflexivity.
    + change (continuity_pt (comp sin (cloth_psi c)) x).
      apply continuity_pt_comp; [apply cloth_psi_cont | apply continuity_sin].
Qed.

Lemma cloth_vy_cont : forall c x, continuity_pt (cloth_vy c) x.
Proof.
  intros c x. unfold cloth_vy.
  apply continuity_pt_plus.
  - apply continuity_pt_mult.
    + apply continuity_pt_const. intros a b. reflexivity.
    + change (continuity_pt (comp cos (cloth_psi c)) x).
      apply continuity_pt_comp; [apply cloth_psi_cont | apply continuity_cos].
  - apply continuity_pt_mult.
    + apply continuity_pt_const. intros a b. reflexivity.
    + change (continuity_pt (comp sin (cloth_psi c)) x).
      apply continuity_pt_comp; [apply cloth_psi_cont | apply continuity_sin].
Qed.

Definition RInt_cont (sigma : R -> R)
    (Hcont : forall x, continuity_pt sigma x) (a b : R) : R :=
  match Rle_dec a b with
  | left Hab =>
      RiemannInt
        (@continuity_implies_RiemannInt sigma a b Hab (fun x _ => Hcont x))
  | right Hn =>
      - RiemannInt
          (@continuity_implies_RiemannInt sigma b a
             (Rlt_le _ _ (Rnot_le_lt _ _ Hn)) (fun x _ => Hcont x))
  end.

Lemma RInt_cont_ext :
  forall sigma1 sigma2 H1 H2 a b,
    (forall x, sigma1 x = sigma2 x) ->
    RInt_cont sigma1 H1 a b = RInt_cont sigma2 H2 a b.
Proof.
  intros sigma1 sigma2 H1 H2 a b Heq.
  unfold RInt_cont.
  destruct (Rle_dec a b) as [Hab|Hn].
  - apply RiemannInt_P18; [exact Hab | intros x _; apply Heq].
  - f_equal. apply RiemannInt_P18.
    + apply Rlt_le. apply Rnot_le_lt. exact Hn.
    + intros x _; apply Heq.
Qed.

Lemma RInt_cont_prfirr :
  forall sigma H1 H2 a b, RInt_cont sigma H1 a b = RInt_cont sigma H2 a b.
Proof.
  intros. apply RInt_cont_ext. intros. reflexivity.
Qed.

Lemma RInt_cont_le :
  forall sigma H a b (Hab : a <= b) (pr : Riemann_integrable sigma a b),
    RInt_cont sigma H a b = RiemannInt pr.
Proof.
  intros sigma H a b Hab pr.
  unfold RInt_cont.
  destruct (Rle_dec a b) as [Hle|Hn].
  - apply RiemannInt_P5.
  - exfalso. apply Hn. exact Hab.
Qed.

Lemma RInt_cont_point :
  forall sigma H a, RInt_cont sigma H a a = 0.
Proof.
  intros sigma H a.
  unfold RInt_cont.
  destruct (Rle_dec a a) as [Ha|Hn].
  - apply RiemannInt_P9.
  - exfalso. apply Hn. apply Rle_refl.
Qed.

Lemma RInt_cont_split0 :
  forall sigma H a b, 0 <= a -> a <= b ->
    RInt_cont sigma H 0 b =
      RInt_cont sigma H 0 a + RInt_cont sigma H a b.
Proof.
  intros sigma H a b Ha Hab.
  assert (H0b : 0 <= b) by lra.
  pose (pr0a := @continuity_implies_RiemannInt sigma 0 a Ha (fun x _ => H x)).
  pose (prab := @continuity_implies_RiemannInt sigma a b Hab (fun x _ => H x)).
  pose (pr0b := @continuity_implies_RiemannInt sigma 0 b H0b (fun x _ => H x)).
  rewrite (RInt_cont_le sigma H 0 a Ha pr0a).
  rewrite (RInt_cont_le sigma H a b Hab prab).
  rewrite (RInt_cont_le sigma H 0 b H0b pr0b).
  symmetry. apply RiemannInt_P26.
Qed.

Lemma RInt_cont_bound :
  forall sigma H a b l u, a <= b ->
    (forall x, a < x < b -> l <= sigma x <= u) ->
    l * (b - a) <= RInt_cont sigma H a b <= u * (b - a).
Proof.
  intros sigma H a b l u Hab Hub.
  pose (pr := @continuity_implies_RiemannInt sigma a b Hab (fun x _ => H x)).
  rewrite (RInt_cont_le sigma H a b Hab pr).
  apply RiemannInt_const_bound; [exact Hab | exact Hub].
Qed.

Lemma RInt_cont_ge0 :
  forall sigma H a b, a <= b ->
    (forall x, a < x < b -> 0 <= sigma x) ->
    0 <= RInt_cont sigma H a b.
Proof.
  intros sigma H a b Hab Hpos.
  pose (pr := @continuity_implies_RiemannInt sigma a b Hab (fun x _ => H x)).
  pose (pr0 := RiemannInt_P14 a b 0).
  rewrite (RInt_cont_le sigma H a b Hab pr).
  assert (Hz : RiemannInt pr0 = 0).
  { rewrite (RiemannInt_P15 pr0). ring. }
  rewrite <- Hz.
  apply RiemannInt_P19; [exact Hab |].
  intros x Hx. unfold fct_cte. apply Hpos. exact Hx.
Qed.

Lemma Riemann_scal_int :
  forall (f : R -> R) (k a b : R)
    (pr : Riemann_integrable f a b)
    (prk : Riemann_integrable (fun x => k * f x) a b),
    a <= b -> RiemannInt prk = k * RiemannInt pr.
Proof.
  intros f k a b pr prk Hab.
  pose (pr0 := RiemannInt_P14 a b 0).
  pose (prs := @RiemannInt_P10 (fct_cte 0) f a b k pr0 pr).
  assert (He : RiemannInt prk = RiemannInt prs).
  { apply RiemannInt_P18; [exact Hab |].
    intros x _. unfold fct_cte. ring. }
  rewrite He.
  rewrite (@RiemannInt_P12 (fct_cte 0) f a b k pr0 pr prs Hab).
  rewrite (RiemannInt_P15 pr0).
  ring.
Qed.

Lemma RInt_cont_swap :
  forall sigma H a b (Hba : b <= a) (pr : Riemann_integrable sigma b a),
    a <> b ->
    RInt_cont sigma H a b = - RiemannInt pr.
Proof.
  intros sigma H a b Hba pr Hne.
  unfold RInt_cont.
  destruct (Rle_dec a b) as [Hab|Hn].
  - assert (a = b) by lra. contradiction.
  - f_equal. apply RiemannInt_P5.
Qed.

Lemma RInt_cont_opp :
  forall sigma (H : forall x, continuity_pt sigma x)
    (Ho : forall x, continuity_pt (fun x => - sigma x) x) a b,
    RInt_cont (fun x => - sigma x) Ho a b = - RInt_cont sigma H a b.
Proof.
  intros sigma H Ho a b.
  destruct (Rle_dec a b) as [Hab|Hn].
  - pose (pr := @continuity_implies_RiemannInt sigma a b Hab (fun x _ => H x)).
    pose (pro := @continuity_implies_RiemannInt (fun x => - sigma x) a b Hab
                   (fun x _ => Ho x)).
    assert (prk : Riemann_integrable (fun x => -1 * sigma x) a b).
    { apply Riemann_integrable_ext with (f := fun x => - sigma x).
      - intros x _. ring.
      - exact pro. }
    rewrite (RInt_cont_le _ Ho a b Hab pro).
    rewrite (RInt_cont_le _ H a b Hab pr).
    assert (He : RiemannInt pro = RiemannInt prk).
    { apply RiemannInt_P18; [exact Hab |]. intros x _. ring. }
    rewrite He.
    rewrite (Riemann_scal_int sigma (-1) a b pr prk Hab).
    ring.
  - assert (Hba : b <= a).
    { apply Rlt_le. apply Rnot_le_lt. exact Hn. }
    assert (Hne : a <> b) by lra.
    pose (pr := @continuity_implies_RiemannInt sigma b a Hba (fun x _ => H x)).
    pose (pro := @continuity_implies_RiemannInt (fun x => - sigma x) b a Hba
                   (fun x _ => Ho x)).
    assert (prk : Riemann_integrable (fun x => -1 * sigma x) b a).
    { apply Riemann_integrable_ext with (f := fun x => - sigma x).
      - intros x _. ring.
      - exact pro. }
    rewrite (RInt_cont_swap _ Ho a b Hba pro Hne).
    rewrite (RInt_cont_swap _ H a b Hba pr Hne).
    assert (He : RiemannInt pro = RiemannInt prk).
    { apply RiemannInt_P18; [exact Hba |]. intros x _. ring. }
    rewrite He.
    rewrite (Riemann_scal_int sigma (-1) b a pr prk Hba).
    ring.
Qed.

Definition cloth_Px (c : ClothoidEgg) (s : R) : R :=
  px (aff_loc (cloth_place c)) + RInt_cont (cloth_vx c) (cloth_vx_cont c) 0 s.

Definition cloth_Py (c : ClothoidEgg) (s : R) : R :=
  py (aff_loc (cloth_place c)) + RInt_cont (cloth_vy c) (cloth_vy_cont c) 0 s.

Definition cloth_P (c : ClothoidEgg) (s : R) : Point :=
  mkPoint (cloth_Px c s) (cloth_Py c s).

Definition cloth_s (c : ClothoidEgg) (t : R) : R :=
  cloth_sd c + t * (cloth_ed c - cloth_sd c).

Definition cloth_eval (c : ClothoidEgg) (t : R) : Point :=
  cloth_P c (cloth_s c t).

Definition cloth_p0 (c : ClothoidEgg) : Point := cloth_eval c 0.
Definition cloth_p1 (c : ClothoidEgg) : Point := cloth_eval c 1.

Definition on_cloth (c : ClothoidEgg) (t : R) (p : Point) : Prop :=
  0 <= t <= 1 /\ p = cloth_eval c t.

Definition cloth_measures_ok (c : ClothoidEgg) : Prop :=
  (cloth_m0 c = None /\ cloth_m1 c = None) \/
  (exists a b, cloth_m0 c = Some a /\ cloth_m1 c = Some b).

Definition cloth_wf (c : ClothoidEgg) : Prop :=
  0 < cloth_A c /\ cloth_h2 c <> 0 /\ cloth_cross c <> 0 /\ cloth_measures_ok c.

Lemma cloth_wf_mk :
  forall pl A sd ed m0 m1,
    0 < A ->
    aff_h2 pl <> 0 ->
    aff_cross pl <> 0 ->
    (m0 = None /\ m1 = None) \/
    (exists x y, m0 = Some x /\ m1 = Some y) ->
    cloth_wf (mk_cloth pl A sd ed m0 m1).
Proof.
  intros pl A sd ed m0 m1 HA Hh Hc Hm.
  unfold cloth_wf, cloth_measures_ok, mk_cloth.
  cbn [cloth_A cloth_h2 cloth_cross cloth_place cloth_m0 cloth_m1].
  unfold cloth_h2, cloth_cross. cbn.
  repeat split; try assumption.
Qed.

Lemma cloth_eval_at_0 :
  forall c, cloth_eval c 0 = cloth_p0 c.
Proof.
  intros c. unfold cloth_p0. reflexivity.
Qed.

Lemma cloth_wf_of_p1 :
  forall c, cloth_wf c -> cloth_p1 c = cloth_eval c 1.
Proof.
  intros c _. unfold cloth_p1. reflexivity.
Qed.

Lemma cloth_eval_at_1_mk :
  forall pl A sd ed m0 m1,
    cloth_p1 (mk_cloth pl A sd ed m0 m1)
      = cloth_eval (mk_cloth pl A sd ed m0 m1) 1.
Proof.
  intros. unfold cloth_p1. reflexivity.
Qed.

Definition cloth_split (c : ClothoidEgg) (t : R) : ClothoidEgg * ClothoidEgg :=
  let mid := cloth_sd c + t * (cloth_ed c - cloth_sd c) in
  (mk_cloth (cloth_place c) (cloth_A c) (cloth_sd c) mid None None,
   mk_cloth (cloth_place c) (cloth_A c) mid (cloth_ed c) None None).

Lemma cloth_P_child :
  forall c t s,
    cloth_P (fst (cloth_split c t)) s = cloth_P c s /\
    cloth_P (snd (cloth_split c t)) s = cloth_P c s.
Proof.
  intros c t s.
  unfold cloth_P, cloth_Px, cloth_Py, cloth_split, mk_cloth.
  cbn [fst snd cloth_place].
  split; apply f_equal2; apply f_equal; apply RInt_cont_prfirr.
Qed.

Lemma cloth_split_eval_left :
  forall c t u,
    cloth_eval (fst (cloth_split c t)) u = cloth_eval c (t * u).
Proof.
  intros c t u.
  unfold cloth_eval.
  assert (Hs : cloth_s (fst (cloth_split c t)) u = cloth_s c (t * u)).
  { unfold cloth_s, cloth_split, mk_cloth.
    cbn [fst cloth_sd cloth_ed]. ring. }
  rewrite Hs.
  apply (proj1 (cloth_P_child c t (cloth_s c (t * u)))).
Qed.

Lemma cloth_split_eval_right :
  forall c t u,
    cloth_eval (snd (cloth_split c t)) u = cloth_eval c (t + (1 - t) * u).
Proof.
  intros c t u.
  unfold cloth_eval.
  assert (Hs : cloth_s (snd (cloth_split c t)) u = cloth_s c (t + (1 - t) * u)).
  { unfold cloth_s, cloth_split, mk_cloth.
    cbn [snd cloth_sd cloth_ed]. ring. }
  rewrite Hs.
  apply (proj2 (cloth_P_child c t _)).
Qed.

Lemma cloth_split_join :
  forall c t,
    cloth_eval (fst (cloth_split c t)) 1 = cloth_eval c t /\
    cloth_eval (snd (cloth_split c t)) 0 = cloth_eval c t.
Proof.
  intros c t. split.
  - rewrite cloth_split_eval_left. rewrite Rmult_1_r. reflexivity.
  - rewrite cloth_split_eval_right. rewrite Rmult_0_r, Rplus_0_r. reflexivity.
Qed.

Lemma cloth_split_left_start :
  forall c t, cloth_eval (fst (cloth_split c t)) 0 = cloth_eval c 0.
Proof.
  intros c t. rewrite cloth_split_eval_left. rewrite Rmult_0_r. reflexivity.
Qed.

Lemma cloth_split_right_end :
  forall c t, cloth_eval (snd (cloth_split c t)) 1 = cloth_eval c 1.
Proof.
  intros c t.
  rewrite cloth_split_eval_right.
  replace (t + (1 - t) * 1) with 1 by ring.
  reflexivity.
Qed.

Lemma cloth_wf_split_left :
  forall c t, cloth_wf c -> cloth_wf (fst (cloth_split c t)).
Proof.
  intros c t H.
  unfold cloth_split. cbn [fst].
  apply cloth_wf_mk.
  - apply H.
  - apply H.
  - apply H.
  - left. split; reflexivity.
Qed.

Lemma cloth_wf_split_right :
  forall c t, cloth_wf c -> cloth_wf (snd (cloth_split c t)).
Proof.
  intros c t H.
  unfold cloth_split. cbn [snd].
  apply cloth_wf_mk; try apply H.
  left. split; reflexivity.
Qed.

Lemma cloth_eval_L0 :
  forall pl A s m0 m1 t,
    cloth_eval (mk_cloth pl A s s m0 m1) t
      = cloth_eval (mk_cloth pl A s s m0 m1) 0.
Proof.
  intros pl A s m0 m1 t.
  unfold cloth_eval, cloth_s, mk_cloth.
  cbn [cloth_sd cloth_ed].
  replace (s + t * (s - s)) with s by ring.
  replace (s + 0 * (s - s)) with s by ring.
  reflexivity.
Qed.

Lemma cloth_eval_kappa0 :
  forall pl A m0 m1 t,
    cloth_eval (mk_cloth pl A 0 0 m0 m1) t = aff_loc pl.
Proof.
  intros pl A m0 m1 t.
  rewrite cloth_eval_L0.
  unfold cloth_eval, cloth_P, cloth_Px, cloth_Py, cloth_s, mk_cloth.
  cbn [cloth_sd cloth_ed cloth_place aff_loc].
  replace (0 + 0 * (0 - 0)) with 0 by ring.
  rewrite RInt_cont_point, RInt_cont_point.
  destruct (aff_loc pl) as [x y].
  cbn [px py].
  apply (f_equal2 mkPoint); ring.
Qed.
