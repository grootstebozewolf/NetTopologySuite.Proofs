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
   The integral is LipInt (dyadic Riemann sums, 3-axiom). No
   RiemannInt. No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance LipInt.
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

(* Lipschitz constant of phi on the window between 0 and s.
   |phi'(u)| = |u| / A^2 <= |s| / A^2. A = 0 is the total degenerate. *)
Definition cloth_phi_K (c : ClothoidEgg) (s : R) : R :=
  Rabs s / (cloth_A c * cloth_A c).

Lemma cloth_sigma_abs : forall c, Rabs (cloth_sigma c) = 1.
Proof.
  intro c. unfold cloth_sigma.
  destruct (Rle_dec 0 (cloth_cross c)).
  - rewrite Rabs_right; lra.
  - rewrite Rabs_left; lra.
Qed.

Lemma cloth_phi_K_nonneg : forall c s, 0 <= cloth_phi_K c s.
Proof.
  intros c s. unfold cloth_phi_K, Rdiv.
  apply Rmult_le_pos; [apply Rabs_pos|].
  set (AA := cloth_A c * cloth_A c).
  assert (Hnn : 0 <= AA) by (unfold AA; nra).
  destruct (Req_EM_T AA 0) as [->|Hnz].
  - rewrite Rinv_0. lra.
  - apply Rlt_le, Rinv_0_lt_compat. lra.
Qed.

Lemma cloth_window_abs : forall s x,
  Rmin 0 s <= x <= Rmax 0 s -> Rabs x <= Rabs s.
Proof.
  intros s x Hx.
  destruct (Rle_dec 0 s) as [Hs|Hs].
  - rewrite (Rmin_left 0 s), (Rmax_right 0 s) in Hx by lra.
    rewrite (Rabs_right x), (Rabs_right s) by lra. lra.
  - assert (Hneg : s < 0) by (apply Rnot_le_lt; exact Hs).
    rewrite (Rmin_right 0 s), (Rmax_left 0 s) in Hx by lra.
    rewrite (Rabs_left1 x), (Rabs_left s) by lra. lra.
Qed.

Lemma cloth_psi_lip : forall c s x y,
  Rmin 0 s <= x <= Rmax 0 s -> Rmin 0 s <= y <= Rmax 0 s ->
  Rabs (cloth_psi c x - cloth_psi c y)
    <= cloth_phi_K c s * Rabs (x - y).
Proof.
  intros c s x y Hx Hy.
  set (AA := cloth_A c * cloth_A c).
  destruct (Req_EM_T AA 0) as [Hz|Hnz].
  - assert (H0 : forall t, cloth_psi c t = 0).
    { intro t. unfold cloth_psi, Rdiv.
      assert (E : 2 * cloth_A c * cloth_A c = 0).
      { unfold AA in Hz.
        replace (2 * cloth_A c * cloth_A c) with (2 * (cloth_A c * cloth_A c)) by ring.
        rewrite Hz. ring. }
      rewrite E, Rinv_0. ring. }
    rewrite !H0. unfold cloth_phi_K, Rdiv. unfold AA in Hz.
    rewrite Hz, Rinv_0, Rminus_diag, Rabs_R0. lra.
  - assert (Hpos : 0 < AA).
    { assert (0 <= AA) by (unfold AA; nra). lra. }
    assert (HA : cloth_A c <> 0).
    { intro HzA. apply Hnz. unfold AA. rewrite HzA. ring. }
    assert (Hinv : 0 < / (2 * AA)).
    { apply Rinv_0_lt_compat. lra. }
    unfold cloth_psi, cloth_phi_K, Rdiv.
    assert (E :
      (cloth_sigma c * x * x) * / (2 * cloth_A c * cloth_A c) -
      (cloth_sigma c * y * y) * / (2 * cloth_A c * cloth_A c)
      = cloth_sigma c * ((x - y) * (x + y)) * / (2 * AA)).
    { unfold AA. field. exact HA. }
    rewrite E. clear E.
    rewrite !Rabs_mult.
    rewrite cloth_sigma_abs.
    assert (Habs : Rabs (/ (2 * AA)) = / (2 * AA)).
    { apply Rabs_pos_eq. apply Rlt_le. exact Hinv. }
    rewrite Habs. clear Habs.
    assert (Hxy : Rabs (x + y) <= 2 * Rabs s).
    { eapply Rle_trans; [apply Rabs_triang|].
      pose proof (cloth_window_abs s x Hx).
      pose proof (cloth_window_abs s y Hy). nra. }
    apply Rle_trans with
      ((1 * (Rabs (x - y) * (2 * Rabs s))) * / (2 * AA)).
    + apply Rmult_le_compat_r; [apply Rlt_le; exact Hinv|].
      apply Rmult_le_compat_l; [lra|].
      apply Rmult_le_compat_l; [apply Rabs_pos| exact Hxy].
    + unfold AA. right. field. exact HA.
Qed.

Lemma cloth_cos_psi_lip : forall c s x y,
  Rmin 0 s <= x <= Rmax 0 s -> Rmin 0 s <= y <= Rmax 0 s ->
  Rabs (cos (cloth_psi c x) - cos (cloth_psi c y))
    <= cloth_phi_K c s * Rabs (x - y).
Proof.
  intros c s x y Hx Hy.
  eapply Rle_trans; [apply cos_lip | apply cloth_psi_lip; assumption].
Qed.

Lemma cloth_sin_psi_lip : forall c s x y,
  Rmin 0 s <= x <= Rmax 0 s -> Rmin 0 s <= y <= Rmax 0 s ->
  Rabs (sin (cloth_psi c x) - sin (cloth_psi c y))
    <= cloth_phi_K c s * Rabs (x - y).
Proof.
  intros c s x y Hx Hy.
  eapply Rle_trans; [apply sin_lip | apply cloth_psi_lip; assumption].
Qed.

Definition cloth_Icos (c : ClothoidEgg) (s : R) : R :=
  int_seg (fun u => cos (cloth_psi c u)) (cloth_phi_K c s) 0 s
    (cloth_phi_K_nonneg c s) (cloth_cos_psi_lip c s).

Definition cloth_Isin (c : ClothoidEgg) (s : R) : R :=
  int_seg (fun u => sin (cloth_psi c u)) (cloth_phi_K c s) 0 s
    (cloth_phi_K_nonneg c s) (cloth_sin_psi_lip c s).

Lemma cloth_psi_same_place :
  forall pl A sd ed sd' ed' m0 m1 m0' m1' u,
    cloth_psi (mk_cloth pl A sd ed m0 m1) u =
    cloth_psi (mk_cloth pl A sd' ed' m0' m1') u.
Proof.
  intros. unfold cloth_psi, cloth_sigma, cloth_cross, mk_cloth. cbn. reflexivity.
Qed.

Lemma cloth_Icos_same_place :
  forall pl A sd ed sd' ed' m0 m1 m0' m1' s,
    cloth_Icos (mk_cloth pl A sd ed m0 m1) s =
    cloth_Icos (mk_cloth pl A sd' ed' m0' m1') s.
Proof.
  intros.
  set (c1 := mk_cloth pl A sd ed m0 m1).
  set (c2 := mk_cloth pl A sd' ed' m0' m1').
  unfold cloth_Icos, cloth_phi_K. cbn [cloth_A].
  set (L := Rabs s / (A * A)).
  transitivity (int_seg (fun u => cos (cloth_psi c1 u)) L 0 s
                  (cloth_phi_K_nonneg c2 s) (cloth_cos_psi_lip c1 s)).
  - apply int_seg_pi.
  - apply int_seg_ext. intros u _. reflexivity.
Qed.

Lemma cloth_Isin_same_place :
  forall pl A sd ed sd' ed' m0 m1 m0' m1' s,
    cloth_Isin (mk_cloth pl A sd ed m0 m1) s =
    cloth_Isin (mk_cloth pl A sd' ed' m0' m1') s.
Proof.
  intros.
  set (c1 := mk_cloth pl A sd ed m0 m1).
  set (c2 := mk_cloth pl A sd' ed' m0' m1').
  unfold cloth_Isin, cloth_phi_K. cbn [cloth_A].
  set (L := Rabs s / (A * A)).
  transitivity (int_seg (fun u => sin (cloth_psi c1 u)) L 0 s
                  (cloth_phi_K_nonneg c2 s) (cloth_sin_psi_lip c1 s)).
  - apply int_seg_pi.
  - apply int_seg_ext. intros u _. reflexivity.
Qed.

Lemma cloth_cos0_same :
  forall pl A sd ed sd' ed' m0 m1 m0' m1',
    cloth_cos0 (mk_cloth pl A sd ed m0 m1) =
    cloth_cos0 (mk_cloth pl A sd' ed' m0' m1').
Proof.
  intros. unfold cloth_cos0, cloth_hypot, cloth_h2, mk_cloth. cbn. reflexivity.
Qed.

Lemma cloth_sin0_same :
  forall pl A sd ed sd' ed' m0 m1 m0' m1',
    cloth_sin0 (mk_cloth pl A sd ed m0 m1) =
    cloth_sin0 (mk_cloth pl A sd' ed' m0' m1').
Proof.
  intros. unfold cloth_sin0, cloth_hypot, cloth_h2, mk_cloth. cbn. reflexivity.
Qed.


Definition cloth_Px (c : ClothoidEgg) (s : R) : R :=
  px (aff_loc (cloth_place c))
    + cloth_cos0 c * cloth_Icos c s - cloth_sin0 c * cloth_Isin c s.

Definition cloth_Py (c : ClothoidEgg) (s : R) : R :=
  py (aff_loc (cloth_place c))
    + cloth_sin0 c * cloth_Icos c s + cloth_cos0 c * cloth_Isin c s.

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
  destruct c as [pl A sd ed m0 m1].
  unfold cloth_split. cbn [fst snd cloth_place cloth_A cloth_sd cloth_ed].
  set (mid := sd + t * (ed - sd)).
  unfold cloth_P, cloth_Px, cloth_Py.
  cbn [cloth_place aff_loc cloth_cos0 cloth_sin0].
  rewrite (cloth_Icos_same_place pl A sd mid sd ed None None m0 m1 s).
  rewrite (cloth_Isin_same_place pl A sd mid sd ed None None m0 m1 s).
  rewrite (cloth_cos0_same pl A sd mid sd ed None None m0 m1).
  rewrite (cloth_sin0_same pl A sd mid sd ed None None m0 m1).
  rewrite (cloth_Icos_same_place pl A mid ed sd ed None None m0 m1 s).
  rewrite (cloth_Isin_same_place pl A mid ed sd ed None None m0 m1 s).
  rewrite (cloth_cos0_same pl A mid ed sd ed None None m0 m1).
  rewrite (cloth_sin0_same pl A mid ed sd ed None None m0 m1).
  split; reflexivity.
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
  unfold cloth_eval, cloth_s, cloth_P, cloth_Px, cloth_Py, cloth_Icos, cloth_Isin, mk_cloth.
  cbn [cloth_sd cloth_ed cloth_place aff_loc].
  assert (Hz : 0 + 0 * (0 - 0) = 0) by ring.
  rewrite Hz.
  rewrite !int_seg_point.
  destruct (aff_loc pl) as [x y].
  cbn [px py].
  apply (f_equal2 mkPoint); ring.
Qed.
