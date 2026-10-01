(* ============================================================================
   NetTopologySuite.Proofs.ClothoidEnvelope
   ----------------------------------------------------------------------------
   AABB of a host clothoid. World heading is α + ψ(s), and ψ is
   quadratic in the station, so the knots where the heading is an
   integer multiple of π/2 are the explicit stations ±√disc. Odd
   multiples (vx = 0) and even multiples (vy = 0) are separate
   chains. Each open interval between consecutive knots has constant
   sign of the coordinate derivative, by IVT against an interior
   zero, and envelope_aabb reads the image off those knots.

   claimId: 0007-clothoid-envelope
   witness: clothoid_envelope
   3-axiom host. No Admitted / Axiom / Parameter. No Rolle.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List ZArith.
From Stdlib Require Import Ranalysis1.
From NTS.Proofs Require Import SheetHenClothoidCore ClothoidTangent
  ClothoidAxis ClothoidKnots MetricEnvelope.
Import ListNotations.
Local Open Scope R_scope.

Lemma cont_ext : forall f g, (forall x, f x = g x) -> continuity g -> continuity f.
Proof.
  intros f g Heq Hg x.
  unfold continuity_pt, continue_in, limit1_in, limit_in, R_dist in *.
  intros eps Heps.
  destruct (Hg x eps Heps) as [alp [Halp Hlim]].
  exists alp. split; [exact Halp|].
  intros y Hy. rewrite !Heq. apply Hlim. exact Hy.
Qed.

Lemma continuity_psi : forall c, continuity (cloth_psi c).
Proof.
  intro c.
  apply cont_ext with (g := fun s =>
    (cloth_sigma c * / (2 * cloth_A c * cloth_A c)) * (s * s)).
  - intro s. unfold cloth_psi, Rdiv. ring.
  - apply continuity_mult.
    + apply continuity_const. unfold constant. intros. reflexivity.
    + apply continuity_mult; apply derivable_continuous, derivable_id.
Qed.

Lemma continuity_cos_psi : forall c, continuity (fun s => cos (cloth_psi c s)).
Proof.
  intro c. change (continuity (comp cos (cloth_psi c))).
  apply continuity_comp; [apply continuity_psi | apply continuity_cos].
Qed.

Lemma continuity_sin_psi : forall c, continuity (fun s => sin (cloth_psi c s)).
Proof.
  intro c. change (continuity (comp sin (cloth_psi c))).
  apply continuity_comp; [apply continuity_psi | apply continuity_sin].
Qed.

Lemma continuity_vx : forall c, continuity (cloth_vx c).
Proof.
  intro c.
  apply cont_ext with (g := fun s =>
    cloth_cos0 c * cos (cloth_psi c s) - cloth_sin0 c * sin (cloth_psi c s)).
  - intro. reflexivity.
  - apply continuity_minus.
    + apply continuity_scal. apply continuity_cos_psi.
    + apply continuity_scal. apply continuity_sin_psi.
Qed.

Lemma continuity_vy : forall c, continuity (cloth_vy c).
Proof.
  intro c.
  apply cont_ext with (g := fun s =>
    cloth_sin0 c * cos (cloth_psi c s) + cloth_cos0 c * sin (cloth_psi c s)).
  - intro. reflexivity.
  - apply continuity_plus.
    + apply continuity_scal. apply continuity_cos_psi.
    + apply continuity_scal. apply continuity_sin_psi.
Qed.

Lemma ivt_cross : forall f x y,
  continuity f -> x < y -> f x < 0 -> 0 < f y ->
  exists z, x < z < y /\ f z = 0.
Proof.
  intros f x y Hc Hxy Hx Hy.
  destruct (IVT f x y Hc Hxy Hx Hy) as [z [Hz Ez]].
  exists z. split; [| exact Ez].
  destruct Hz as [Hxz Hzy]. split.
  - destruct Hxz as [Hlt|Heq]; [exact Hlt| subst z; exfalso; lra].
  - destruct Hzy as [Hlt|Heq]; [exact Hlt| subst z; exfalso; lra].
Qed.

Lemma sign_holds : forall f a b,
  a < b -> continuity f ->
  (forall t, a < t < b -> f t <> 0) ->
  forall t, a <= t <= b -> 0 < f ((a + b) / 2) -> 0 <= f t.
Proof.
  intros f a b Hab Hc Hnz t Ht Hm.
  destruct (Rle_lt_dec 0 (f t)) as [Hnn|Hneg]; [exact Hnn|].
  set (m := (a + b) / 2) in *.
  assert (Hmab : a < m < b) by (unfold m; lra).
  destruct (Rtotal_order t m) as [Hlt|[Heq|Hgt]].
  - destruct (ivt_cross f t m Hc Hlt Hneg Hm) as [z [Hz Ez]].
    exfalso. apply (Hnz z); [| exact Ez]. split; lra.
  - subst t. lra.
  - assert (Hc' : continuity (fun z => - f z)) by (apply continuity_opp; exact Hc).
    destruct (ivt_cross (fun z => - f z) m t Hc' Hgt) as [z [Hz Ez]].
    + lra.
    + lra.
    + exfalso. apply (Hnz z); [| lra]. split; lra.
Qed.

Fixpoint signs_of (f' : R -> R) (knots : list R) : list bool :=
  match knots with
  | a :: xs =>
      match xs with
      | b :: _ =>
          (if Rle_dec 0 (f' ((a + b) / 2)) then true else false)
            :: signs_of f' xs
      | [] => []
      end
  | [] => []
  end.

Lemma consecutive_tail : forall x xs a b,
  consecutive xs a b -> consecutive (x :: xs) a b.
Proof.
  intros x xs a b Hc.
  destruct xs as [|y rest]; [simpl in Hc; contradiction|].
  simpl. right. exact Hc.
Qed.

Lemma chain_build : forall f f' knots,
  strict_inc knots ->
  (forall s, derivable_pt_lim f s (f' s)) ->
  continuity f' ->
  (forall a b t, consecutive knots a b -> a < t < b -> f' t <> 0) ->
  chain_ok f f' knots (signs_of f' knots).
Proof.
  intros f f' knots. induction knots as [|a ks IH]; intros Hs Hder Hcont Hgap.
  - simpl. exact I.
  - destruct ks as [|b rest].
    + simpl. exact I.
    + simpl. split.
      * assert (Hab : a < b) by (simpl in Hs; exact (proj1 Hs)).
        assert (Hopen : forall t, a < t < b -> f' t <> 0).
        { intros t Ht. apply (Hgap a b t); [| exact Ht]. simpl. left. split; reflexivity. }
        destruct (Rle_dec 0 (f' ((a + b) / 2))) as [Hle|Hlt].
        -- apply piece_up.
           ++ intros t _. apply Hder.
           ++ intros t Ht.
              apply (sign_holds f' a b Hab Hcont Hopen t Ht).
              destruct (Rle_lt_or_eq_dec _ _ Hle) as [Hp|Heq]; [exact Hp|].
              exfalso. apply (Hopen ((a + b) / 2)); [| symmetry; exact Heq]. lra.
        -- apply piece_down.
           ++ intros t _. apply Hder.
           ++ intros t Ht.
              assert (Hneg : f' ((a + b) / 2) < 0) by (apply Rnot_le_lt; exact Hlt).
              assert (Hopp : 0 <= - f' t).
              { apply (sign_holds (fun z => - f' z) a b Hab).
                - apply continuity_opp. exact Hcont.
                - intros z Hz Ez. apply (Hopen z Hz). lra.
                - exact Ht.
                - lra. }
              lra.
      * apply IH.
        -- simpl in Hs. exact (proj2 Hs).
        -- exact Hder.
        -- exact Hcont.
        -- intros a0 b0 t Hc0 Ht. apply (Hgap a0 b0 t); [| exact Ht].
           apply consecutive_tail. exact Hc0.
Qed.

Lemma is_interior_in : forall knots q, is_interior knots q -> In q knots.
Proof.
  induction knots as [|a ks IH]; intros q H; simpl in H; try contradiction.
  destruct ks as [|b rest]; [contradiction|].
  destruct rest as [|c rest']; [contradiction|].
  destruct H as [->|H].
  - right. left. reflexivity.
  - right. apply IH. exact H.
Qed.

Lemma interior_crit_zeros : forall f' knots,
  (forall q, is_interior knots q -> f' q = 0) ->
  interior_crit f' knots.
Proof.
  intros f' knots H. induction knots as [|a ks IH].
  - simpl. exact I.
  - destruct ks as [|b rest]; [simpl; exact I|].
    destruct rest as [|c rest']; [simpl; exact I|].
    simpl. split.
    + apply H. simpl. left. reflexivity.
    + apply IH. intros q Hq. apply H. simpl. right. exact Hq.
Qed.

Lemma is_interior_frame : forall lo (mid : list R) hi q,
  is_interior (lo :: mid ++ [hi]) q <-> In q mid.
Proof.
  intros lo mid hi q. revert lo.
  induction mid as [|m ms IH]; intros lo.
  - simpl. split; intro H; contradiction.
  - destruct ms as [|m2 ms'].
    + simpl. split.
      * intros [->|H]; [left; reflexivity | contradiction].
      * intros [->|[]]. left. reflexivity.
    + simpl. rewrite (IH m). split.
      * intros [->|H]; [left; reflexivity | right; exact H].
      * intros [->|H]; [left; reflexivity | right; exact H].
Qed.

Lemma in_frame : forall (lo : R) (mid : list R) (hi q : R),
  In q (lo :: mid ++ [hi]) -> q = lo \/ In q mid \/ q = hi.
Proof.
  intros lo mid hi q Hin. simpl in Hin. destruct Hin as [->|Hin].
  - left. reflexivity.
  - apply in_app_or in Hin. destruct Hin as [Hin|[->|[]]].
    + right. left. exact Hin.
    + right. right. reflexivity.
Qed.

Lemma knots_in_window : forall c axis q,
  In q (cloth_axis_knots c axis) -> cloth_lo c <= q <= cloth_hi c.
Proof.
  intros c axis q Hin.
  destruct (Req_EM_T (cloth_lo c) (cloth_hi c)) as [Heq|Hne].
  - rewrite (knots_point c axis Heq) in Hin. simpl in Hin.
    destruct Hin as [Hq|[]]. subst q. rewrite Heq. split; apply Rle_refl.
  - rewrite (knots_frame_mid c axis Hne) in Hin.
    destruct (in_frame _ _ _ _ Hin) as [Hq|[Hinm|Hq]].
    + subst q. split; [apply Rle_refl | apply lo_le_hi].
    + destruct (mid_in_open c axis q Hinm) as [H1 H2]. split; apply Rlt_le; assumption.
    + subst q. split; [apply lo_le_hi | apply Rle_refl].
Qed.

Lemma interior_heading : forall c axis q,
  cloth_wf c -> is_interior (cloth_axis_knots c axis) q ->
  exists k, Z.odd k = axis /\
    cloth_heading c q = IZR k * PI / 2 /\
    q * q = cloth_disc c (cloth_theta c k).
Proof.
  intros c axis q Hwf Hi.
  assert (Hne : cloth_lo c <> cloth_hi c).
  { intro Heq. rewrite (knots_point c axis Heq) in Hi. simpl in Hi. contradiction. }
  rewrite (knots_frame_mid c axis Hne) in Hi.
  apply (proj1 (is_interior_frame (cloth_lo c) (cloth_mid c axis) (cloth_hi c) q)) in Hi.
  apply (mid_root c axis q Hwf Hi).
Qed.

Lemma vx_at_interior : forall c q,
  cloth_wf c -> is_interior (cloth_axis_knots c true) q -> cloth_vx c q = 0.
Proof.
  intros c q Hwf Hi.
  destruct (interior_heading c true q Hwf Hi) as [k [Hod [Hh _]]].
  rewrite (vx_heading c q (env_h2 c Hwf)), Hh. apply cos_k_half_odd. exact Hod.
Qed.

Lemma vy_at_interior : forall c q,
  cloth_wf c -> is_interior (cloth_axis_knots c false) q -> cloth_vy c q = 0.
Proof.
  intros c q Hwf Hi.
  destruct (interior_heading c false q Hwf Hi) as [k [Hod [Hh _]]].
  assert (Hev : Z.even k = true) by (apply odd_false_even; exact Hod).
  rewrite (vy_heading c q (env_h2 c Hwf)), Hh. apply sin_k_half_even. exact Hev.
Qed.

Lemma open_zero_interior : forall c axis s,
  cloth_wf c -> cloth_lo c < s < cloth_hi c ->
  (exists k, cloth_heading c s = IZR k * PI / 2 /\ Z.odd k = axis) ->
  is_interior (cloth_axis_knots c axis) s.
Proof.
  intros c axis s Hwf Hop [k [Hh Hod]].
  assert (Hle : cloth_lo c <= s <= cloth_hi c) by lra.
  assert (Hne : cloth_lo c <> cloth_hi c) by lra.
  rewrite (knots_frame_mid c axis Hne).
  apply (proj2 (is_interior_frame (cloth_lo c) (cloth_mid c axis) (cloth_hi c) s)).
  apply cands_in_mid; [exact Hop|].
  apply (heading_root_in_cands c axis s k Hwf Hle Hh Hod).
Qed.

Lemma vx_zero_interior : forall c s,
  cloth_wf c -> cloth_lo c < s < cloth_hi c -> cloth_vx c s = 0 ->
  is_interior (cloth_axis_knots c true) s.
Proof.
  intros c s Hwf Hop Hz.
  assert (Hcos : cos (cloth_heading c s) = 0).
  { rewrite <- (vx_heading c s (env_h2 c Hwf)). exact Hz. }
  destruct (cos_zero_shift _ Hcos) as [k [Hh Hod]].
  apply (open_zero_interior c true s Hwf Hop).
  exists k. split; assumption.
Qed.

Lemma vy_zero_interior : forall c s,
  cloth_wf c -> cloth_lo c < s < cloth_hi c -> cloth_vy c s = 0 ->
  is_interior (cloth_axis_knots c false) s.
Proof.
  intros c s Hwf Hop Hz.
  assert (Hsin : sin (cloth_heading c s) = 0).
  { rewrite <- (vy_heading c s (env_h2 c Hwf)). exact Hz. }
  destruct (sin_zero_shift _ Hsin) as [k [Hh Hev]].
  assert (Hod : Z.odd k = false) by (apply even_odd_false; exact Hev).
  apply (open_zero_interior c false s Hwf Hop).
  exists k. split; assumption.
Qed.

Lemma deriv_gap : forall c axis (f' : R -> R) a b t,
  (forall s, cloth_lo c < s < cloth_hi c -> f' s = 0 ->
     is_interior (cloth_axis_knots c axis) s) ->
  consecutive (cloth_axis_knots c axis) a b ->
  a < t < b -> f' t <> 0.
Proof.
  intros c axis f' a b t Hint Hc Ht Hz.
  assert (Hop : cloth_lo c < t < cloth_hi c).
  { destruct (consecutive_in _ a b Hc) as [Ha Hb].
    destruct (knots_in_window c axis a Ha) as [Hlo _].
    destruct (knots_in_window c axis b Hb) as [_ Hhi]. lra. }
  assert (Hi : is_interior (cloth_axis_knots c axis) t) by (apply Hint; [exact Hop| exact Hz]).
  apply (consecutive_gap (cloth_axis_knots c axis) a b t (knots_strict c axis) Hc Ht).
  apply is_interior_in. exact Hi.
Qed.

Lemma chain_vx : forall c, cloth_wf c ->
  chain_ok (cloth_Px c) (cloth_vx c)
    (cloth_axis_knots c true) (signs_of (cloth_vx c) (cloth_axis_knots c true)).
Proof.
  intros c Hwf. apply chain_build.
  - apply knots_strict.
  - apply cloth_Px_deriv.
  - apply continuity_vx.
  - intros a b t Hc Ht.
    apply (deriv_gap c true (cloth_vx c) a b t); [| exact Hc | exact Ht].
    intros s Hs Hz. apply vx_zero_interior; assumption.
Qed.

Lemma chain_vy : forall c, cloth_wf c ->
  chain_ok (cloth_Py c) (cloth_vy c)
    (cloth_axis_knots c false) (signs_of (cloth_vy c) (cloth_axis_knots c false)).
Proof.
  intros c Hwf. apply chain_build.
  - apply knots_strict.
  - apply cloth_Py_deriv.
  - apply continuity_vy.
  - intros a b t Hc Ht.
    apply (deriv_gap c false (cloth_vy c) a b t); [| exact Hc | exact Ht].
    intros s Hs Hz. apply vy_zero_interior; assumption.
Qed.

Lemma crit_vx : forall c, cloth_wf c ->
  interior_crit (cloth_vx c) (cloth_axis_knots c true).
Proof.
  intros c Hwf. apply interior_crit_zeros. intros q Hq. apply vx_at_interior; assumption.
Qed.

Lemma crit_vy : forall c, cloth_wf c ->
  interior_crit (cloth_vy c) (cloth_axis_knots c false).
Proof.
  intros c Hwf. apply interior_crit_zeros. intros q Hq. apply vy_at_interior; assumption.
Qed.

(* WITNESS {"claimId":"0007-clothoid-envelope","topic":"curves","lemma":"clothoid_envelope","title":"Clothoid AABB knots are the explicit heading multiples of pi/2","file":"theories/ClothoidEnvelope.v","witness":"clothoid_envelope","board":"ADR-0007"} *)
Theorem clothoid_envelope : forall c,
  cloth_wf c ->
  let kx := cloth_axis_knots c true in
  let ky := cloth_axis_knots c false in
  (forall q, is_interior kx q -> cloth_vx c q = 0) /\
  (forall q, is_interior ky q -> cloth_vy c q = 0) /\
  (forall t, match kx with
             | [] => True
             | a :: _ =>
                 a <= t <= rlast kx ->
                 rmin_list (map (cloth_Px c) kx) <= cloth_Px c t <=
                 rmax_list (map (cloth_Px c) kx)
             end) /\
  (forall t, match ky with
             | [] => True
             | a :: _ =>
                 a <= t <= rlast ky ->
                 rmin_list (map (cloth_Py c) ky) <= cloth_Py c t <=
                 rmax_list (map (cloth_Py c) ky)
             end) /\
  (forall q, is_interior kx q ->
     exists k, Z.odd k = true /\
       cloth_heading c q = IZR k * PI / 2 /\
       q * q = cloth_disc c (cloth_theta c k)) /\
  (forall q, is_interior ky q ->
     exists k, Z.even k = true /\
       cloth_heading c q = IZR k * PI / 2 /\
       q * q = cloth_disc c (cloth_theta c k)) /\
  (forall s, cloth_lo c < s < cloth_hi c -> cloth_vx c s = 0 ->
     is_interior kx s) /\
  (forall s, cloth_lo c < s < cloth_hi c -> cloth_vy c s = 0 ->
     is_interior ky s).
Proof.
  intros c Hwf.
  set (kx := cloth_axis_knots c true).
  set (ky := cloth_axis_knots c false).
  cbn zeta.
  destruct (envelope_aabb (cloth_Px c) (cloth_Py c) (cloth_vx c) (cloth_vy c)
              kx (signs_of (cloth_vx c) kx) ky (signs_of (cloth_vy c) ky)
              (chain_vx c Hwf) (crit_vx c Hwf)
              (chain_vy c Hwf) (crit_vy c Hwf))
    as [Hx0 [Hy0 [Hxim Hyim]]].
  split; [exact Hx0|].
  split; [exact Hy0|].
  split; [exact Hxim|].
  split; [exact Hyim|].
  split; [| split; [| split]].
  - intros q Hq. apply (interior_heading c true q Hwf Hq).
  - intros q Hq.
    destruct (interior_heading c false q Hwf Hq) as [k [Hod [Hh Hsq]]].
    exists k. split; [| split; assumption].
    apply odd_false_even. exact Hod.
  - intros s Hs Hz. apply vx_zero_interior; assumption.
  - intros s Hs Hz. apply vy_zero_interior; assumption.
Qed.

Print Assumptions cont_ext.
Print Assumptions continuity_psi.
Print Assumptions continuity_cos_psi.
Print Assumptions continuity_sin_psi.
Print Assumptions continuity_vx.
Print Assumptions continuity_vy.
Print Assumptions ivt_cross.
Print Assumptions sign_holds.
Print Assumptions consecutive_tail.
Print Assumptions chain_build.
Print Assumptions is_interior_in.
Print Assumptions interior_crit_zeros.
Print Assumptions is_interior_frame.
Print Assumptions in_frame.
Print Assumptions knots_in_window.
Print Assumptions interior_heading.
Print Assumptions vx_at_interior.
Print Assumptions vy_at_interior.
Print Assumptions open_zero_interior.
Print Assumptions vx_zero_interior.
Print Assumptions vy_zero_interior.
Print Assumptions deriv_gap.
Print Assumptions chain_vx.
Print Assumptions chain_vy.
Print Assumptions crit_vx.
Print Assumptions crit_vy.
Print Assumptions clothoid_envelope.
