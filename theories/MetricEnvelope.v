(* ============================================================================
   NetTopologySuite.Proofs.MetricEnvelope
   ----------------------------------------------------------------------------
   Generic axis-aligned envelope of a C1 coordinate. The caller supplies
   the knots and the sign of the derivative on each piece. RealMonotone
   (deriv_nonneg_incr, deriv_pt_opp) puts the image of each piece between
   its endpoint values, so the image of the chain sits between the min
   and the max of the values at the knots.

   An interior knot is an axis-aligned tangent: interior_crit says the
   derivative is zero there. This file does not prove that such a zero
   exists. Existence is Rolle, and Rolle prints classic.

   The two coordinates of a plane curve are independent chains. Their
   partitions may differ. The empty chain is no segment. A singleton
   chain is the point case: the parameter equals that knot.

   Deferrals, named:
     * Rolle / IVT existence of γ'_x = 0 or γ'_y = 0 is not proved.
     * per-type files (arc, clothoid, NURBS) exhibit the knots.
     * an equality-form mean value (Δγ = γ'(c) Δt) is not proved.

   WITNESS topic: metric · claimId: 0001-metric-envelope
   · witness: envelope_aabb
   board: ADR-0001
   No Admitted / Axiom / Parameter.
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import RealMonotone.
Import ListNotations.
Local Open Scope R_scope.

Inductive piece_ok (f f' : R -> R) : R -> R -> bool -> Prop :=
| piece_up : forall a b,
    (forall t, a <= t <= b -> derivable_pt_lim f t (f' t)) ->
    (forall t, a <= t <= b -> 0 <= f' t) ->
    piece_ok f f' a b true
| piece_down : forall a b,
    (forall t, a <= t <= b -> derivable_pt_lim f t (f' t)) ->
    (forall t, a <= t <= b -> f' t <= 0) ->
    piece_ok f f' a b false.

Fixpoint chain_ok (f f' : R -> R) (knots : list R) (signs : list bool) : Prop :=
  match knots with
  | a :: ((b :: _) as rest) =>
      match signs with
      | s :: ss => piece_ok f f' a b s /\ chain_ok f f' rest ss
      | [] => False
      end
  | _ =>
      match signs with
      | [] => True
      | _ => False
      end
  end.

Fixpoint interior_crit (f' : R -> R) (knots : list R) : Prop :=
  match knots with
  | _ :: ((b :: (_ :: _)) as tail) => f' b = 0 /\ interior_crit f' tail
  | _ => True
  end.

Fixpoint is_interior (knots : list R) (q : R) : Prop :=
  match knots with
  | _ :: ((b :: (_ :: _)) as tail) => q = b \/ is_interior tail q
  | _ => False
  end.

Fixpoint rmin_list (l : list R) : R :=
  match l with
  | [] => 0
  | x :: xs =>
      match xs with
      | [] => x
      | _ => Rmin x (rmin_list xs)
      end
  end.

Fixpoint rmax_list (l : list R) : R :=
  match l with
  | [] => 0
  | x :: xs =>
      match xs with
      | [] => x
      | _ => Rmax x (rmax_list xs)
      end
  end.

Fixpoint rlast (l : list R) : R :=
  match l with
  | [] => 0
  | x :: xs =>
      match xs with
      | [] => x
      | _ => rlast xs
      end
  end.

Lemma rmin_cons_tail : forall x y xs,
  rmin_list (x :: y :: xs) = Rmin x (rmin_list (y :: xs)).
Proof. intros. simpl. destruct xs; reflexivity. Qed.

Lemma rmin_le_head : forall x xs, rmin_list (x :: xs) <= x.
Proof.
  intros x xs. destruct xs; simpl; [apply Rle_refl | apply Rmin_l].
Qed.

Lemma rmin_le_tail : forall x xs, xs <> [] ->
  rmin_list (x :: xs) <= rmin_list xs.
Proof.
  intros x xs Hne. destruct xs as [|y ys]; [contradiction|]. simpl. apply Rmin_r.
Qed.

Lemma rmin_front : forall a b xs, rmin_list (a :: b :: xs) <= Rmin a b.
Proof.
  intros a b xs. rewrite rmin_cons_tail.
  assert (Hhead : rmin_list (b :: xs) <= b) by apply rmin_le_head.
  apply Rmin_glb.
  - apply Rmin_l.
  - eapply Rle_trans; [apply Rmin_r | exact Hhead].
Qed.

Lemma rmax_ge_head : forall x xs, x <= rmax_list (x :: xs).
Proof.
  intros x xs. destruct xs; simpl; [apply Rle_refl | apply Rmax_l].
Qed.

Lemma rmax_ge_tail : forall x xs, xs <> [] ->
  rmax_list xs <= rmax_list (x :: xs).
Proof.
  intros x xs Hne. destruct xs as [|y ys]; [contradiction|]. simpl. apply Rmax_r.
Qed.

Lemma rmax_front : forall a b xs, Rmax a b <= rmax_list (a :: b :: xs).
Proof.
  intros a b xs.
  assert (Ha : a <= rmax_list (a :: b :: xs)) by apply rmax_ge_head.
  assert (Hb0 : b <= rmax_list (b :: xs)) by apply rmax_ge_head.
  assert (Hb1 : rmax_list (b :: xs) <= rmax_list (a :: b :: xs)).
  { apply rmax_ge_tail. discriminate. }
  apply Rmax_lub; [exact Ha | eapply Rle_trans; [exact Hb0 | exact Hb1]].
Qed.

Lemma rlast_cons : forall a b xs, rlast (a :: b :: xs) = rlast (b :: xs).
Proof. intros. simpl. destruct xs; reflexivity. Qed.

Lemma piece_in_ends :
  forall f f' a b (s : bool) x,
    piece_ok f f' a b s ->
    a <= x <= b ->
    Rmin (f a) (f b) <= f x <= Rmax (f a) (f b).
Proof.
  intros f f' a b s x Hok Hx.
  destruct Hok as [a b Hder Hnn | a b Hder Hnp].
  - assert (Hlo : f a <= f x).
    { apply (deriv_nonneg_incr f f' a b a x Hder Hnn);
        [apply Rle_refl | exact (proj1 Hx) | exact (proj2 Hx)]. }
    assert (Hhi : f x <= f b).
    { apply (deriv_nonneg_incr f f' a b x b Hder Hnn);
        [exact (proj1 Hx) | exact (proj2 Hx) | apply Rle_refl]. }
    split.
    + eapply Rle_trans; [apply Rmin_l | exact Hlo].
    + eapply Rle_trans; [exact Hhi | apply Rmax_r].
  - assert (HderN : forall t, a <= t <= b ->
             derivable_pt_lim (fun z => - f z) t (- f' t)).
    { intros t Ht. apply deriv_pt_opp. apply Hder. exact Ht. }
    assert (Hnn : forall t, a <= t <= b -> 0 <= - f' t).
    { intros t Ht. assert (Hf : f' t <= 0) by (apply Hnp; exact Ht).
      apply Ropp_le_contravar in Hf. rewrite Ropp_0 in Hf. exact Hf. }
    assert (Hlo : - f a <= - f x).
    { apply (deriv_nonneg_incr (fun z => - f z) (fun t => - f' t) a b a x
              HderN Hnn); [apply Rle_refl | exact (proj1 Hx) | exact (proj2 Hx)]. }
    assert (Hhi : - f x <= - f b).
    { apply (deriv_nonneg_incr (fun z => - f z) (fun t => - f' t) a b x b
              HderN Hnn); [exact (proj1 Hx) | exact (proj2 Hx) | apply Rle_refl]. }
    apply Ropp_le_contravar in Hlo. rewrite !Ropp_involutive in Hlo.
    apply Ropp_le_contravar in Hhi. rewrite !Ropp_involutive in Hhi.
    split.
    + eapply Rle_trans; [apply Rmin_r | exact Hhi].
    + eapply Rle_trans; [exact Hlo | apply Rmax_l].
Qed.

Lemma chain_image :
  forall f f' a rest signs x,
    chain_ok f f' (a :: rest) signs ->
    a <= x <= rlast (a :: rest) ->
    rmin_list (map f (a :: rest)) <= f x <= rmax_list (map f (a :: rest)).
Proof.
  intros f f' a rest. revert a.
  induction rest as [|b ks IH]; intros a signs x Hok Hx.
  - assert (Ex : x = a) by (simpl in Hx; lra). subst x.
    simpl. split; apply Rle_refl.
  - destruct signs as [|s ss].
    + simpl in Hok. contradiction.
    + simpl in Hok. destruct Hok as [Hpiece Htail].
      destruct (Rle_lt_dec x b) as [Hxb|Hbx].
      * assert (Haxb : a <= x <= b).
        { split; [exact (proj1 Hx) | exact Hxb]. }
        destruct (piece_in_ends f f' a b s x Hpiece Haxb) as [Hlo Hhi].
        split.
        -- eapply Rle_trans; [| exact Hlo]. apply rmin_front.
        -- eapply Rle_trans; [exact Hhi |]. apply rmax_front.
      * assert (Htailb : b <= x <= rlast (b :: ks)).
        { split; [apply Rlt_le; exact Hbx |].
          rewrite <- (rlast_cons a b ks). exact (proj2 Hx). }
        destruct (IH b ss x Htail Htailb) as [Hlo Hhi].
        split.
        -- eapply Rle_trans; [| exact Hlo].
           apply rmin_le_tail. discriminate.
        -- eapply Rle_trans; [exact Hhi |].
           apply rmax_ge_tail. discriminate.
Qed.

Lemma interior_zero :
  forall f' q knots,
    interior_crit f' knots -> is_interior knots q -> f' q = 0.
Proof.
  intros f' q knots. revert q.
  induction knots as [|a knots IH]; intros q Hc Hi; simpl in Hi; try contradiction.
  destruct knots as [|b rest]; [contradiction|].
  destruct rest as [|c rest]; [contradiction|].
  simpl in Hc. destruct Hc as [Hb Hc'].
  destruct Hi as [->|Hi]; [exact Hb |].
  apply (IH q); assumption.
Qed.

Lemma envelope_coord :
  forall f f' knots signs,
    chain_ok f f' knots signs ->
    interior_crit f' knots ->
    (forall q, is_interior knots q -> f' q = 0) /\
    (forall x, match knots with
               | [] => True
               | a :: _ => a <= x <= rlast knots ->
                   rmin_list (map f knots) <= f x <= rmax_list (map f knots)
               end).
Proof.
  intros f f' knots signs Hok Hcrit. split.
  - intros q Hq. apply interior_zero with (knots := knots); assumption.
  - intros x. destruct knots as [|a rest].
    + exact I.
    + intros Hx. apply chain_image with (f' := f') (signs := signs); assumption.
Qed.

(* WITNESS {"claimId":"0001-metric-envelope","topic":"metric","lemma":"envelope_aabb","title":"AABB of a C1 segment is the knot envelope","file":"theories/MetricEnvelope.v","witness":"envelope_aabb","board":"ADR-0001"} *)
Theorem envelope_aabb :
  forall gx gy vx vy kx sx ky sy,
    chain_ok gx vx kx sx ->
    interior_crit vx kx ->
    chain_ok gy vy ky sy ->
    interior_crit vy ky ->
    (forall q, is_interior kx q -> vx q = 0) /\
    (forall q, is_interior ky q -> vy q = 0) /\
    (forall t, match kx with
               | [] => True
               | a :: _ => a <= t <= rlast kx ->
                   rmin_list (map gx kx) <= gx t <= rmax_list (map gx kx)
               end) /\
    (forall t, match ky with
               | [] => True
               | a :: _ => a <= t <= rlast ky ->
                   rmin_list (map gy ky) <= gy t <= rmax_list (map gy ky)
               end).
Proof.
  intros gx gy vx vy kx sx ky sy Hkx Hcx Hky Hcy.
  destruct (envelope_coord gx vx kx sx Hkx Hcx) as [Hx0 Hxim].
  destruct (envelope_coord gy vy ky sy Hky Hcy) as [Hy0 Hyim].
  split; [exact Hx0 | split; [exact Hy0 | split; [exact Hxim | exact Hyim]]].
Qed.

Print Assumptions piece_in_ends.
Print Assumptions chain_image.
Print Assumptions interior_zero.
Print Assumptions envelope_coord.
Print Assumptions envelope_aabb.
