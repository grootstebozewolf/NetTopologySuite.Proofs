(* ============================================================================
   NetTopologySuite.Proofs.MetricGreen
   ----------------------------------------------------------------------------
   Member-level Green identity for the area formula, on LipInt.

   For a CircularEgg, γ(t) = circ_eval e t on [0,1],
     ½ ∫₀¹ (x y' − y x') dt
       = ½ edge_cross(γ(0), γ(1)) + segment_area (circ_r) (circ_sweep).
   The integral is int_seg. The primitive's derivative is the density;
   on the window [−1, 2] both 0 and 1 are interior, so lip_ftc is
   two-sided on [0,1] and deriv_zero_const gives FTC-2. A chord is the
   constant density edge_cross, so its integral is the cross. Summing
   members, members_area is ½ ∮ (x dy − y dx) along the chain.

   General LipInt analysis under the #886 amendment (ADR-0001), not a
   Fresnel result. lint_leibniz is not used. No RiemannInt, no MVT, no Rolle.

   Deferrals, named: clothoid and NURBS Green members. The arc envelope
   instance (breakpoints at multiples of π/2 in [θ₀, θ₀+Δθ]) is not this
   file.

   WITNESS topic: metric · claimId: 0001-metric-green
   · witness: members_area_is_green
   board: ADR-0001
   No Admitted / Axiom / Parameter.
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Ranalysis1 List.
From NTS.Proofs Require Import
  Distance LipInt LipIntFTC RealMonotone ArcArea RingArea979 SheetHenCircEgg MetricArea.
Import ListNotations.
Local Open Scope R_scope.

Lemma deriv_pt_sub :
  forall (f g : R -> R) (x lf lg : R),
    derivable_pt_lim f x lf ->
    derivable_pt_lim g x lg ->
    derivable_pt_lim (fun z => f z - g z) x (lf - lg).
Proof.
  intros f g x lf lg Hf Hg.
  eapply derivable_pt_lim_ext.
  - intros z. unfold minus_fct. reflexivity.
  - apply derivable_pt_lim_minus; assumption.
Qed.

Lemma int_seg_const :
  forall c L a b (HL : 0 <= L)
    (Hlip : forall x y,
       Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
       Rabs ((fun _ : R => c) x - (fun _ : R => c) y) <= L * Rabs (x - y)),
    a <= b ->
    int_seg (fun _ : R => c) L a b HL Hlip = (b - a) * c.
Proof.
  intros c L a b HL Hlip Hab.
  unfold int_seg.
  destruct (Rle_dec a b) as [Hab'|Hn]; [| exfalso; exact (Hn Hab)].
  apply lint_const.
Qed.

Lemma const_lip :
  forall (c L a b : R), 0 <= L ->
    forall x y,
      Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
      Rabs ((fun _ : R => c) x - (fun _ : R => c) y) <= L * Rabs (x - y).
Proof.
  intros c L a b HL x y _ _.
  rewrite Rminus_diag, Rabs_R0.
  apply Rmult_le_pos; [exact HL | apply Rabs_pos].
Qed.

Section Egg.
Variable e : CircularEgg.

Let ox : R := px (circ_o e).
Let oy : R := py (circ_o e).
Let r : R := circ_r e.
Let a0 : R := circ_theta0 e.
Let s : R := circ_sweep e.

Definition phi (t : R) : R := a0 + t * s.

Definition arc_x (t : R) : R := ox + r * cos (phi t).
Definition arc_y (t : R) : R := oy + r * sin (phi t).
Definition arc_dx (t : R) : R := - r * s * sin (phi t).
Definition arc_dy (t : R) : R := r * s * cos (phi t).

Definition green_density (t : R) : R :=
  arc_x t * arc_dy t - arc_y t * arc_dx t.

Definition green_prim (t : R) : R :=
  ox * r * sin (phi t) - oy * r * cos (phi t) + r * r * s * t.

Definition green_L : R :=
  Rabs (r * s * ox) * Rabs s + Rabs (r * s * oy) * Rabs s.

Lemma density_trig : forall t,
  green_density t =
    r * s * (ox * cos (phi t) + oy * sin (phi t)) + r * r * s.
Proof.
  intros t. unfold green_density, arc_x, arc_y, arc_dx, arc_dy.
  pose proof (sin2_cos2 (phi t)) as Hcs. unfold Rsqr in Hcs.
  replace ((ox + r * cos (phi t)) * (r * s * cos (phi t))
           - (oy + r * sin (phi t)) * (- r * s * sin (phi t)))
    with (r * s * (ox * cos (phi t) + oy * sin (phi t))
          + r * r * s * (sin (phi t) * sin (phi t)
                         + cos (phi t) * cos (phi t))) by ring.
  rewrite Hcs. ring.
Qed.

Lemma green_HL : 0 <= green_L.
Proof.
  unfold green_L.
  apply Rplus_le_le_0_compat; apply Rmult_le_pos; apply Rabs_pos.
Qed.

Lemma green_lip : forall x y, -1 <= x <= 2 -> -1 <= y <= 2 ->
  Rabs (green_density x - green_density y) <= green_L * Rabs (x - y).
Proof.
  intros x y _ _.
  assert (Ed : green_density x - green_density y =
    (r * s * ox) * (cos (phi x) - cos (phi y))
    + (r * s * oy) * (sin (phi x) - sin (phi y))).
  { rewrite !density_trig. ring. }
  rewrite Ed.
  eapply Rle_trans; [apply Rabs_triang |].
  rewrite (Rabs_mult (r * s * ox)), (Rabs_mult (r * s * oy)).
  assert (Hc : Rabs (cos (phi x) - cos (phi y)) <= Rabs s * Rabs (x - y)).
  { eapply Rle_trans; [apply cos_lip |].
    unfold phi.
    replace ((a0 + x * s) - (a0 + y * s)) with (s * (x - y)) by ring.
    rewrite Rabs_mult. apply Rle_refl. }
  assert (Hs : Rabs (sin (phi x) - sin (phi y)) <= Rabs s * Rabs (x - y)).
  { eapply Rle_trans; [apply sin_lip |].
    unfold phi.
    replace ((a0 + x * s) - (a0 + y * s)) with (s * (x - y)) by ring.
    rewrite Rabs_mult. apply Rle_refl. }
  eapply Rle_trans.
  - apply Rplus_le_compat.
    + apply Rmult_le_compat_l; [apply Rabs_pos | exact Hc].
    + apply Rmult_le_compat_l; [apply Rabs_pos | exact Hs].
  - unfold green_L.
    replace (Rabs (r * s * ox) * (Rabs s * Rabs (x - y))
             + Rabs (r * s * oy) * (Rabs s * Rabs (x - y)))
      with ((Rabs (r * s * ox) * Rabs s + Rabs (r * s * oy) * Rabs s)
            * Rabs (x - y)) by ring.
    apply Rle_refl.
Qed.

Lemma green_lip_01 : forall x y,
  Rmin 0 1 <= x <= Rmax 0 1 -> Rmin 0 1 <= y <= Rmax 0 1 ->
  Rabs (green_density x - green_density y) <= green_L * Rabs (x - y).
Proof.
  intros x y Hx Hy.
  apply green_lip.
  - split.
    + apply Rle_trans with (Rmin 0 1); [| exact (proj1 Hx)].
      apply Rmin_glb; lra.
    + apply Rle_trans with (Rmax 0 1); [exact (proj2 Hx) |].
      apply Rmax_lub; lra.
  - split.
    + apply Rle_trans with (Rmin 0 1); [| exact (proj1 Hy)].
      apply Rmin_glb; lra.
    + apply Rle_trans with (Rmax 0 1); [exact (proj2 Hy) |].
      apply Rmax_lub; lra.
Qed.

Lemma phi_deriv : forall t, derivable_pt_lim phi t s.
Proof.
  intros t.
  replace s with (0 + s * 1) by ring.
  apply derivable_pt_lim_ext with
    (f := plus_fct (fct_cte a0) (mult_real_fct s (fun z : R => z))).
  - intros z. unfold phi, plus_fct, fct_cte, mult_real_fct. ring.
  - apply derivable_pt_lim_plus.
    + apply derivable_pt_lim_const.
    + apply derivable_pt_lim_scal.
      eapply derivable_pt_lim_ext; [| apply derivable_pt_lim_id].
      intros z. unfold id. reflexivity.
Qed.

Lemma sin_phi_deriv : forall t,
  derivable_pt_lim (fun u => sin (phi u)) t (cos (phi t) * s).
Proof.
  intros t.
  apply derivable_pt_lim_ext with (f := comp sin phi).
  - intros z. unfold comp. reflexivity.
  - apply derivable_pt_lim_comp; [apply phi_deriv | apply derivable_pt_lim_sin].
Qed.

Lemma cos_phi_deriv : forall t,
  derivable_pt_lim (fun u => cos (phi u)) t ((- sin (phi t)) * s).
Proof.
  intros t.
  apply derivable_pt_lim_ext with (f := comp cos phi).
  - intros z. unfold comp. reflexivity.
  - apply derivable_pt_lim_comp; [apply phi_deriv | apply derivable_pt_lim_cos].
Qed.

Lemma green_prim_deriv : forall t, derivable_pt_lim green_prim t (green_density t).
Proof.
  intros t.
  replace (green_density t) with
    ((ox * r) * (cos (phi t) * s)
     + - ((oy * r) * ((- sin (phi t)) * s))
     + (r * r * s) * 1).
  - apply derivable_pt_lim_ext with
      (f := fun z => (ox * r) * sin (phi z)
                     + - ((oy * r) * cos (phi z))
                     + (r * r * s) * z).
    + intros z. unfold green_prim. ring.
    + apply derivable_pt_lim_plus.
      * apply derivable_pt_lim_plus.
        -- apply derivable_pt_lim_scal. apply sin_phi_deriv.
        -- apply derivable_pt_lim_opp.
           apply derivable_pt_lim_scal. apply cos_phi_deriv.
      * apply derivable_pt_lim_scal.
        eapply derivable_pt_lim_ext; [| apply derivable_pt_lim_id].
        intros z. unfold id. reflexivity.
  - rewrite density_trig. ring.
Qed.

Definition greenF : R -> R :=
  lipF green_density (-1) 2 green_L green_HL green_lip.

Lemma arc_int_prim :
  int_seg green_density green_L 0 1 green_HL green_lip_01
  = green_prim 1 - green_prim 0.
Proof.
  assert (H01 : -1 <= 0 <= 2) by (split; lra).
  assert (H11 : -1 <= 1 <= 2) by (split; lra).
  assert (HderH : forall t, 0 <= t <= 1 ->
            derivable_pt_lim (fun z => green_prim z - greenF z) t 0).
  { intros t Ht.
    assert (Hopen : -1 < t < 2) by lra.
    assert (Hf := lip_ftc green_density (-1) 2 green_L green_HL green_lip t Hopen).
    assert (Hd := green_prim_deriv t).
    assert (Hsub := deriv_pt_sub green_prim greenF t (green_density t) (green_density t) Hd Hf).
    replace 0 with (green_density t - green_density t) by ring.
    exact Hsub. }
  assert (Hz : forall t, 0 <= t <= 1 -> 0 = 0) by (intros; reflexivity).
  assert (Heq : green_prim 1 - greenF 1 = green_prim 0 - greenF 0).
  { apply (deriv_zero_const (fun z => green_prim z - greenF z) (fun _ => 0) 0 1 1 0).
    - exact HderH.
    - intros t _. reflexivity.
    - split; [lra | apply Rle_refl].
    - split; [apply Rle_refl | lra]. }
  assert (Einc : green_prim 1 - green_prim 0 = greenF 1 - greenF 0).
  { replace (green_prim 1 - green_prim 0)
      with ((green_prim 1 - greenF 1) - (green_prim 0 - greenF 0)
            + (greenF 1 - greenF 0)) by ring.
    rewrite Heq. ring. }
  assert (Hch : lipPrim green_density (-1) 2 green_L green_HL green_lip 0 1
                = greenF 1 - greenF 0).
  { unfold greenF. apply lipPrim_chasles; assumption. }
  assert (Hseg : lipPrim green_density (-1) 2 green_L green_HL green_lip 0 1
                 = int_seg green_density green_L 0 1 green_HL
                     (clip_on green_density (-1) 2 green_L green_lip 0 1 H01 H11)).
  { apply lipPrim_as_seg. }
  rewrite Einc. rewrite <- Hch. rewrite Hseg. apply int_seg_pi.
Qed.

Lemma prim_increment :
  green_prim 1 - green_prim 0 =
    ox * r * (sin (a0 + s) - sin a0)
    + oy * r * (cos a0 - cos (a0 + s))
    + r * r * s.
Proof.
  unfold green_prim, phi.
  replace (a0 + 1 * s) with (a0 + s) by ring.
  replace (a0 + 0 * s) with a0 by ring.
  ring.
Qed.

Lemma cross_arc_trig :
  edge_cross (circ_eval e 0) (circ_eval e 1) =
    r * ox * (sin (a0 + s) - sin a0)
    + r * oy * (cos a0 - cos (a0 + s))
    + r * r * sin s.
Proof.
  unfold edge_cross, circ_eval. cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  unfold ox, oy, r, a0, s.
  replace (circ_theta0 e + 0 * circ_sweep e) with (circ_theta0 e) by ring.
  replace (circ_theta0 e + 1 * circ_sweep e) with (circ_theta0 e + circ_sweep e) by ring.
  set (ca := cos (circ_theta0 e)).
  set (sa := sin (circ_theta0 e)).
  set (cb := cos (circ_theta0 e + circ_sweep e)).
  set (sb := sin (circ_theta0 e + circ_sweep e)).
  set (rr := circ_r e).
  set (sx := px (circ_o e)).
  set (sy := py (circ_o e)).
  set (sw := circ_sweep e).
  assert (Hs : ca * sb - sa * cb = sin sw).
  { unfold ca, sa, cb, sb, sw.
    replace (cos (circ_theta0 e) * sin (circ_theta0 e + circ_sweep e)
             - sin (circ_theta0 e) * cos (circ_theta0 e + circ_sweep e))
      with (sin (circ_theta0 e + circ_sweep e) * cos (circ_theta0 e)
            - cos (circ_theta0 e + circ_sweep e) * sin (circ_theta0 e)) by ring.
    rewrite <- (sin_minus (circ_theta0 e + circ_sweep e) (circ_theta0 e)).
    replace ((circ_theta0 e + circ_sweep e) - circ_theta0 e)
      with (circ_sweep e) by ring.
    reflexivity. }
  replace ((sx + rr * ca) * (sy + rr * sb) - (sx + rr * cb) * (sy + rr * sa))
    with (rr * sx * (sb - sa) + rr * sy * (ca - cb) + rr * rr * (ca * sb - sa * cb))
    by ring.
  rewrite Hs. ring.
Qed.

Lemma arc_green_segment :
  int_seg green_density green_L 0 1 green_HL green_lip_01 / 2
  = edge_cross (circ_eval e 0) (circ_eval e 1) / 2
    + segment_area r s.
Proof.
  rewrite arc_int_prim. rewrite prim_increment. rewrite cross_arc_trig.
  unfold segment_area. field.
Qed.

End Egg.

Definition chord_density (p q : Point) (t : R) : R :=
  (px p + t * (px q - px p)) * (py q - py p)
  - (py p + t * (py q - py p)) * (px q - px p).

Lemma chord_density_const : forall p q t, chord_density p q t = edge_cross p q.
Proof. intros p q t. unfold chord_density, edge_cross. ring. Qed.

Lemma chord_HL : 0 <= 0.
Proof. apply Rle_refl. Qed.

Lemma chord_lip : forall p q x y,
  Rmin 0 1 <= x <= Rmax 0 1 -> Rmin 0 1 <= y <= Rmax 0 1 ->
  Rabs (chord_density p q x - chord_density p q y) <= 0 * Rabs (x - y).
Proof.
  intros p q x y _ _.
  rewrite !chord_density_const. rewrite Rminus_diag, Rabs_R0.
  apply Rmult_le_pos; [apply Rle_refl | apply Rabs_pos].
Qed.

Lemma chord_green_segment : forall p q,
  int_seg (chord_density p q) 0 0 1 chord_HL (chord_lip p q)
  = edge_cross p q.
Proof.
  intros p q.
  assert (Hext : int_seg (chord_density p q) 0 0 1 chord_HL (chord_lip p q)
                 = int_seg (fun _ : R => edge_cross p q) 0 0 1 chord_HL
                     (const_lip (edge_cross p q) 0 0 1 chord_HL)).
  { apply int_seg_ext. intros x _. apply chord_density_const. }
  rewrite Hext.
  rewrite (int_seg_const (edge_cross p q) 0 0 1 chord_HL
            (const_lip (edge_cross p q) 0 0 1 chord_HL) Rle_0_1).
  ring.
Qed.

Definition member_green (m : area_member) : R :=
  match m with
  | MChord p q => int_seg (chord_density p q) 0 0 1 chord_HL (chord_lip p q)
  | MArc egg => int_seg (green_density egg) (green_L egg) 0 1 (green_HL egg) (green_lip_01 egg)
  end.

Lemma member_green_contrib : forall m,
  member_green m / 2 = member_cross m / 2 + member_bulge m.
Proof.
  intros m. destruct m as [p q|egg].
  - simpl. rewrite chord_green_segment. rewrite Rplus_0_r. reflexivity.
  - unfold member_green, member_cross, member_bulge, member_start, member_end.
    rewrite arc_green_segment. reflexivity.
Qed.

Lemma split_halves : forall a b c d : R,
  (a + c) / 2 + (b + d) = a / 2 + b + (c / 2 + d).
Proof. intros. field. Qed.

Lemma sum_div2 : forall a b : R, a / 2 + b / 2 = (a + b) / 2.
Proof. intros. field. Qed.

Fixpoint greens (ms : list area_member) : R :=
  match ms with
  | [] => 0
  | m :: t => member_green m + greens t
  end.

(* WITNESS {"claimId":"0001-metric-green","topic":"metric","lemma":"members_area_is_green","title":"Member areas are Green integrals","file":"theories/MetricGreen.v","witness":"members_area_is_green","board":"ADR-0001"} *)
Theorem members_area_is_green : forall ms,
  members_area ms = greens ms / 2.
Proof.
  induction ms as [|m ms IH].
  - unfold members_area, crosses, bulges, greens.
    replace (0 / 2) with 0 by field. ring.
  - unfold members_area. simpl crosses. simpl bulges. simpl greens.
    assert (Hm := member_green_contrib m).
    unfold members_area in IH.
    rewrite split_halves. rewrite <- Hm. rewrite IH. apply sum_div2.
Qed.

Print Assumptions deriv_pt_sub.
Print Assumptions int_seg_const.
Print Assumptions const_lip.
Print Assumptions density_trig.
Print Assumptions green_HL.
Print Assumptions green_lip.
Print Assumptions green_lip_01.
Print Assumptions phi_deriv.
Print Assumptions sin_phi_deriv.
Print Assumptions cos_phi_deriv.
Print Assumptions green_prim_deriv.
Print Assumptions arc_int_prim.
Print Assumptions prim_increment.
Print Assumptions cross_arc_trig.
Print Assumptions arc_green_segment.
Print Assumptions chord_density_const.
Print Assumptions chord_HL.
Print Assumptions chord_lip.
Print Assumptions chord_green_segment.
Print Assumptions member_green_contrib.
Print Assumptions split_halves.
Print Assumptions sum_div2.
Print Assumptions members_area_is_green.
