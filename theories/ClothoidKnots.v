(* ============================================================================
   NetTopologySuite.Proofs.ClothoidKnots
   ----------------------------------------------------------------------------
   The explicit station list where a host clothoid's heading is an
   integer multiple of π/2, restricted to the open window (sd, ed)
   and closed by the window ends. Odd multiples are the vx = 0 knots;
   even multiples are the vy = 0 knots. The list is strictly increasing.

   claimId: none. The envelope letter is ClothoidEnvelope.clothoid_envelope.
   3-axiom host. No Admitted / Axiom / Parameter. No Rolle.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List ZArith Bool.
From NTS.Proofs Require Import SheetHenClothoidCore ClothoidAxis.
Import ListNotations.
Local Open Scope R_scope.

Fixpoint nondec (l : list R) : Prop :=
  match l with
  | [] => True
  | x :: xs =>
      match xs with
      | [] => True
      | y :: _ => x <= y /\ nondec xs
      end
  end.

Fixpoint strict_inc (l : list R) : Prop :=
  match l with
  | [] => True
  | x :: xs =>
      match xs with
      | [] => True
      | y :: _ => x < y /\ strict_inc xs
      end
  end.

Fixpoint rinsert (x : R) (l : list R) : list R :=
  match l with
  | [] => [x]
  | y :: ys => if Rle_dec x y then x :: l else y :: rinsert x ys
  end.

Fixpoint rsort (l : list R) : list R :=
  match l with
  | [] => []
  | x :: xs => rinsert x (rsort xs)
  end.

Fixpoint rdedup (l : list R) : list R :=
  match l with
  | [] => []
  | x :: xs =>
      match rdedup xs with
      | [] => [x]
      | y :: ys => if Req_EM_T x y then y :: ys else x :: y :: ys
      end
  end.

Lemma rinsert_In : forall x y l, In y (rinsert x l) <-> y = x \/ In y l.
Proof.
  intros x y l. induction l as [|z l IH]; simpl.
  - split.
    + intros [->|[]]. left. reflexivity.
    + intros [->|[]]. left. reflexivity.
  - destruct (Rle_dec x z).
    + simpl. split.
      * intros [->|[->|H]]; [left; reflexivity | right; left; reflexivity | right; right; exact H].
      * intros [->|[->|H]]; [left; reflexivity | right; left; reflexivity | right; right; exact H].
    + simpl. rewrite IH. split.
      * intros [->|[->|H]]; [right; left; reflexivity | left; reflexivity | right; right; exact H].
      * intros [->|[->|H]]; [right; left; reflexivity | left; reflexivity | right; right; exact H].
Qed.

Lemma rsort_In : forall y l, In y (rsort l) <-> In y l.
Proof.
  intros y l. induction l as [|x l IH]; simpl.
  - split; intro H; exact H.
  - rewrite rinsert_In, IH. split.
    + intros [->|H]; [left; reflexivity | right; exact H].
    + intros [->|H]; [left; reflexivity | right; exact H].
Qed.

Lemma rinsert_nondec : forall x l, nondec l -> nondec (rinsert x l).
Proof.
  intros x l H. induction l as [|y l IH].
  - simpl. exact I.
  - simpl. destruct (Rle_dec x y) as [Hxy|Hyx].
    + destruct l as [|z l'].
      * simpl. split; [exact Hxy| exact I].
      * simpl in H. destruct H as [Hyz Hl]. simpl. split; [exact Hxy|]. split; [exact Hyz| exact Hl].
    + assert (Hyx' : y < x) by (apply Rnot_le_lt; exact Hyx).
      destruct l as [|z l'].
      * simpl. split; [apply Rlt_le; exact Hyx'| exact I].
      * simpl in H. destruct H as [Hyz Hl].
        destruct (Rle_dec x z) as [Hxz|Hzx].
        -- assert (E : rinsert x (z :: l') = x :: z :: l').
           { simpl. destruct (Rle_dec x z) as [C|C]; [reflexivity| exfalso; apply C; exact Hxz]. }
           rewrite E. simpl. split; [apply Rlt_le; exact Hyx'|].
           split; [exact Hxz| exact Hl].
        -- assert (E : rinsert x (z :: l') = z :: rinsert x l').
           { simpl. destruct (Rle_dec x z) as [C|C]; [exfalso; apply Hzx; exact C| reflexivity]. }
           specialize (IH Hl). rewrite E in IH. rewrite E.
           simpl. split; [exact Hyz| exact IH].
Qed.

Lemma rsort_nondec : forall l, nondec (rsort l).
Proof.
  induction l as [|x l IH]; simpl; [exact I|]. apply rinsert_nondec. exact IH.
Qed.

Lemma nondec_prefix_le : forall x l y, nondec (x :: l) -> In y l -> x <= y.
Proof.
  intros x l y. revert x. induction l as [|z l IH]; intros x Hs Hin.
  - contradiction.
  - simpl in Hin. destruct Hin as [->|Hin].
    + simpl in Hs. exact (proj1 Hs).
    + apply Rle_trans with z.
      * simpl in Hs. exact (proj1 Hs).
      * apply IH; [| exact Hin]. simpl in Hs. exact (proj2 Hs).
Qed.

Lemma rdedup_In : forall x l, In x (rdedup l) <-> In x l.
Proof.
  intros x l. induction l as [|y l IH].
  - simpl. split; intro H; exact H.
  - destruct (rdedup l) as [|z zs] eqn:Ez; simpl; rewrite Ez; simpl.
    + split.
      * intros [->|[]]. left. reflexivity.
      * intros [->|H].
        -- left. reflexivity.
        -- apply (proj2 IH) in H. contradiction.
    + destruct (Req_EM_T y z) as [->|Hne].
      * simpl. split.
        -- intro H. right. apply (proj1 IH). exact H.
        -- intros [->|H].
           ++ left. reflexivity.
           ++ apply (proj2 IH). exact H.
      * simpl. split.
        -- intros [->|[->|H]].
           ++ left. reflexivity.
           ++ right. apply (proj1 IH). left. reflexivity.
           ++ right. apply (proj1 IH). right. exact H.
        -- intros [->|H].
           ++ left. reflexivity.
           ++ destruct (proj2 IH H) as [->|Hin].
              ** right. left. reflexivity.
              ** right. right. exact Hin.
Qed.

Lemma rdedup_strict : forall l, nondec l -> strict_inc (rdedup l).
Proof.
  induction l as [|x l IH]; intros Hs.
  - simpl. exact I.
  - simpl. destruct (rdedup l) as [|y ys] eqn:Ey.
    + simpl. exact I.
    + destruct (Req_EM_T x y) as [->|Hne].
      * apply IH.
        destruct l as [|z l']; [simpl in Ey; discriminate|]. simpl in Hs. exact (proj2 Hs).
      * assert (Hle : x <= y).
        { apply nondec_prefix_le with (l := l); [exact Hs|].
          apply (proj1 (rdedup_In y l)). rewrite Ey. left. reflexivity. }
        assert (Hlt : x < y).
        { destruct (Rle_lt_or_eq_dec x y Hle) as [H|H]; [exact H|].
          exfalso. exact (Hne H). }
        simpl. split; [exact Hlt|].
        apply IH.
        destruct l as [|z l']; [simpl in Ey; discriminate|]. simpl in Hs. exact (proj2 Hs).
Qed.

Lemma strict_lt_in : forall x l y, strict_inc (x :: l) -> In y l -> x < y.
Proof.
  intros x l y. revert x. induction l as [|z l IH]; intros x Hs Hin.
  - contradiction.
  - simpl in Hin. destruct Hin as [->|Hin].
    + simpl in Hs. exact (proj1 Hs).
    + apply Rlt_trans with z.
      * simpl in Hs. exact (proj1 Hs).
      * apply IH; [| exact Hin]. simpl in Hs. exact (proj2 Hs).
Qed.

Fixpoint consecutive (l : list R) (a b : R) : Prop :=
  match l with
  | x :: xs =>
      match xs with
      | y :: _ => (x = a /\ y = b) \/ consecutive xs a b
      | [] => False
      end
  | [] => False
  end.

Lemma consecutive_in : forall l a b,
  consecutive l a b -> In a l /\ In b l.
Proof.
  intros l. induction l as [|x xs IH]; intros a b Hc.
  - simpl in Hc. contradiction.
  - destruct xs as [|y rest]; [simpl in Hc; contradiction|].
    simpl in Hc. destruct Hc as [[-> ->]|Hc].
    + split; [left; reflexivity | right; left; reflexivity].
    + destruct (IH a b Hc) as [Ha Hb].
      split; right; assumption.
Qed.

Lemma consecutive_gap : forall l a b t,
  strict_inc l -> consecutive l a b -> a < t < b -> ~ In t l.
Proof.
  intros l. induction l as [|x xs IH]; intros a b t Hs Hc Ht Hin.
  - simpl in Hc. contradiction.
  - destruct xs as [|y rest]; [simpl in Hc; contradiction|].
    simpl in Hc. destruct Hc as [[-> ->]|Hc].
    + simpl in Hin. destruct Hin as [->|[->|Hin]].
      * lra.
      * lra.
      * assert (b < t).
        { apply (strict_lt_in b rest t); [| exact Hin]. simpl in Hs. exact (proj2 Hs). }
        lra.
    + simpl in Hin. destruct Hin as [Ex|Hin].
      * subst x.
        destruct (consecutive_in (y :: rest) a b Hc) as [Ha _].
        assert (t < a) by (apply (strict_lt_in t (y :: rest) a Hs Ha)). lra.
      * apply (IH a b t); try assumption.
        simpl in Hs. exact (proj2 Hs).
Qed.

Fixpoint cloth_cands_of (c : ClothoidEgg) (axis : bool) (ks : list Z) : list R :=
  match ks with
  | [] => []
  | k :: rest =>
      let d := cloth_disc c (cloth_theta c k) in
      let tail := cloth_cands_of c axis rest in
      if Bool.eqb (Z.odd k) axis then
        if Rle_dec 0 d then sqrt d :: (- sqrt d) :: tail else tail
      else tail
  end.

Lemma cands_fwd : forall c axis ks k s,
  In k ks -> Z.odd k = axis -> 0 <= cloth_disc c (cloth_theta c k) ->
  s = sqrt (cloth_disc c (cloth_theta c k)) \/
  s = - sqrt (cloth_disc c (cloth_theta c k)) ->
  In s (cloth_cands_of c axis ks).
Proof.
  intros c axis ks. induction ks as [|k0 ks IH]; intros k s Hin Hod Hd Hs.
  - contradiction.
  - simpl. destruct Hin as [<-|Hin].
    + rewrite Hod, eqb_reflx.
      destruct (Rle_dec 0 (cloth_disc c (cloth_theta c k0))) as [Hok|Hbad].
      * destruct Hs as [E|E]; subst s; simpl; [left; reflexivity | right; left; reflexivity].
      * exfalso. exact (Hbad Hd).
    + specialize (IH k s Hin Hod Hd Hs).
      destruct (Bool.eqb (Z.odd k0) axis) eqn:He.
      * destruct (Rle_dec 0 (cloth_disc c (cloth_theta c k0))) as [_|].
        -- simpl. right. right. exact IH.
        -- exact IH.
      * exact IH.
Qed.

Lemma cands_bwd : forall c axis ks s,
  In s (cloth_cands_of c axis ks) ->
  exists k, In k ks /\ Z.odd k = axis /\
    0 <= cloth_disc c (cloth_theta c k) /\
    (s = sqrt (cloth_disc c (cloth_theta c k)) \/
     s = - sqrt (cloth_disc c (cloth_theta c k))).
Proof.
  intros c axis ks. induction ks as [|k ks IH]; intros s Hin.
  - simpl in Hin. contradiction.
  - simpl in Hin. destruct (Bool.eqb (Z.odd k) axis) eqn:He.
    + apply eqb_prop in He.
      destruct (Rle_dec 0 (cloth_disc c (cloth_theta c k))) as [Hd|Hd].
      * simpl in Hin. destruct Hin as [E|[E|Hin]].
        -- subst s. exists k. split; [left; reflexivity|]. split; [exact He|].
           split; [exact Hd|]. left. reflexivity.
        -- subst s. exists k. split; [left; reflexivity|]. split; [exact He|].
           split; [exact Hd|]. right. reflexivity.
        -- destruct (IH s Hin) as [k' [Hin' Hrest]].
           exists k'. split; [right; exact Hin'| exact Hrest].
      * destruct (IH s Hin) as [k' [Hin' Hrest]].
        exists k'. split; [right; exact Hin'| exact Hrest].
    + destruct (IH s Hin) as [k' [Hin' Hrest]].
      exists k'. split; [right; exact Hin'| exact Hrest].
Qed.

Definition cloth_cands (c : ClothoidEgg) (axis : bool) : list R :=
  cloth_cands_of c axis (k_range (k_bound c)).

Definition in_open (lo hi s : R) : bool :=
  if Rlt_dec lo s then if Rlt_dec s hi then true else false else false.

Lemma in_open_spec : forall lo hi s, in_open lo hi s = true <-> lo < s < hi.
Proof.
  intros lo hi s. unfold in_open. split.
  - destruct (Rlt_dec lo s) as [H1|H1]; [| discriminate].
    destruct (Rlt_dec s hi) as [H2|H2]; [| discriminate].
    intros _. split; assumption.
  - intros [H1 H2].
    destruct (Rlt_dec lo s) as [_|Hbad]; [| exfalso; exact (Hbad H1)].
    destruct (Rlt_dec s hi) as [_|Hbad]; [| exfalso; exact (Hbad H2)].
    reflexivity.
Qed.

Definition cloth_mid (c : ClothoidEgg) (axis : bool) : list R :=
  rdedup (rsort (filter (in_open (cloth_lo c) (cloth_hi c)) (cloth_cands c axis))).

Definition cloth_axis_knots (c : ClothoidEgg) (axis : bool) : list R :=
  let lo := cloth_lo c in
  let hi := cloth_hi c in
  if Req_EM_T lo hi then [lo]
  else lo :: cloth_mid c axis ++ [hi].

Lemma lo_le_hi : forall c, cloth_lo c <= cloth_hi c.
Proof.
  intro c. unfold cloth_lo, cloth_hi.
  apply Rle_trans with (cloth_sd c); [apply Rmin_l | apply Rmax_l].
Qed.

Lemma knots_point : forall c axis,
  cloth_lo c = cloth_hi c -> cloth_axis_knots c axis = [cloth_lo c].
Proof.
  intros c axis Heq. unfold cloth_axis_knots.
  destruct (Req_EM_T (cloth_lo c) (cloth_hi c)) as [_|Hne]; [reflexivity | contradiction].
Qed.

Lemma knots_frame_mid : forall c axis,
  cloth_lo c <> cloth_hi c ->
  cloth_axis_knots c axis = cloth_lo c :: cloth_mid c axis ++ [cloth_hi c].
Proof.
  intros c axis Hne. unfold cloth_axis_knots.
  destruct (Req_EM_T (cloth_lo c) (cloth_hi c)) as [Heq|Hne']; [contradiction | reflexivity].
Qed.

Lemma mid_strict : forall c axis, strict_inc (cloth_mid c axis).
Proof.
  intros c axis. unfold cloth_mid. apply rdedup_strict. apply rsort_nondec.
Qed.

Lemma mid_in_open : forall c axis s,
  In s (cloth_mid c axis) -> cloth_lo c < s < cloth_hi c.
Proof.
  intros c axis s Hin. unfold cloth_mid in Hin.
  apply (proj1 (rdedup_In s _)) in Hin.
  apply (proj1 (rsort_In s _)) in Hin.
  apply filter_In in Hin. destruct Hin as [_ Ho].
  apply in_open_spec. exact Ho.
Qed.

Lemma cands_in_mid : forall c axis s,
  cloth_lo c < s < cloth_hi c ->
  In s (cloth_cands c axis) ->
  In s (cloth_mid c axis).
Proof.
  intros c axis s Hop Hin. unfold cloth_mid.
  apply (proj2 (rdedup_In s _)).
  apply (proj2 (rsort_In s _)).
  apply filter_In. split; [exact Hin|].
  apply in_open_spec. exact Hop.
Qed.

Lemma snoc_strict : forall mid hi,
  strict_inc mid -> (forall q, In q mid -> q < hi) -> strict_inc (mid ++ [hi]).
Proof.
  induction mid as [|m ms IH]; intros hi Hs Hhi.
  - simpl. exact I.
  - simpl. destruct ms as [|m2 ms'].
    + simpl. split; [apply Hhi; left; reflexivity | exact I].
    + simpl in Hs. destruct Hs as [Hm Hms]. split; [exact Hm|].
      apply IH; [exact Hms|]. intros q Hq. apply Hhi. right. exact Hq.
Qed.

Lemma cons_frame_strict : forall lo mid hi,
  lo < hi -> strict_inc mid ->
  (forall q, In q mid -> lo < q < hi) ->
  strict_inc (lo :: mid ++ [hi]).
Proof.
  intros lo mid hi Hlh Hs Hin.
  assert (Htail : strict_inc (mid ++ [hi])).
  { apply snoc_strict; [exact Hs|]. intros q Hq. exact (proj2 (Hin q Hq)). }
  destruct mid as [|m ms].
  - simpl. split; [exact Hlh | exact I].
  - simpl. split.
    + exact (proj1 (Hin m (or_introl eq_refl))).
    + exact Htail.
Qed.

Lemma knots_strict : forall c axis, strict_inc (cloth_axis_knots c axis).
Proof.
  intros c axis. unfold cloth_axis_knots.
  destruct (Req_EM_T (cloth_lo c) (cloth_hi c)) as [->|Hne].
  - simpl. exact I.
  - assert (Hlt : cloth_lo c < cloth_hi c).
    { pose proof (lo_le_hi c) as Hle. apply Rnot_le_lt. intro Hge. apply Hne. lra. }
    apply cons_frame_strict; [exact Hlt | apply (mid_strict c axis) |].
    intros q Hq. apply (mid_in_open c axis). exact Hq.
Qed.

Lemma heading_in_range : forall c s k,
  cloth_wf c -> cloth_lo c <= s <= cloth_hi c ->
  cloth_heading c s = IZR k * PI / 2 ->
  In k (k_range (k_bound c)).
Proof.
  intros c s k Hwf Hs Heq.
  apply k_range_spec.
  apply (proj1 (Z.abs_le k (Z.of_nat (k_bound c)))).
  apply (heading_k_bound c s k Hwf Hs Heq).
Qed.

Lemma heading_root_in_cands : forall c axis s k,
  cloth_wf c -> cloth_lo c <= s <= cloth_hi c ->
  cloth_heading c s = IZR k * PI / 2 -> Z.odd k = axis ->
  In s (cloth_cands c axis).
Proof.
  intros c axis s k Hwf Hs Heq Hod.
  assert (Hd : s * s = cloth_disc c (cloth_theta c k))
    by (apply disc_of_heading; assumption).
  assert (Hnn : 0 <= cloth_disc c (cloth_theta c k)).
  { rewrite <- Hd. apply Rle_0_sqr. }
  apply cands_fwd with (k := k).
  - apply heading_in_range with (s := s); assumption.
  - exact Hod.
  - exact Hnn.
  - apply sqrt_pm; assumption.
Qed.

Lemma mid_root : forall c axis s,
  cloth_wf c -> In s (cloth_mid c axis) ->
  exists k, Z.odd k = axis /\
    cloth_heading c s = IZR k * PI / 2 /\
    s * s = cloth_disc c (cloth_theta c k).
Proof.
  intros c axis s Hwf Hin.
  unfold cloth_mid in Hin.
  apply (proj1 (rdedup_In s _)) in Hin.
  apply (proj1 (rsort_In s _)) in Hin.
  apply filter_In in Hin. destruct Hin as [Hcands _].
  unfold cloth_cands in Hcands.
  destruct (cands_bwd c axis _ s Hcands) as [k [_ [Hod [Hnn Hs]]]].
  exists k. split; [exact Hod|]. split.
  - apply heading_of_disc; [apply env_A_pos; exact Hwf | apply cand_square; assumption].
  - apply cand_square; assumption.
Qed.

Print Assumptions rinsert_In.
Print Assumptions rsort_In.
Print Assumptions rinsert_nondec.
Print Assumptions rsort_nondec.
Print Assumptions nondec_prefix_le.
Print Assumptions rdedup_In.
Print Assumptions rdedup_strict.
Print Assumptions strict_lt_in.
Print Assumptions consecutive_in.
Print Assumptions consecutive_gap.
Print Assumptions cands_fwd.
Print Assumptions cands_bwd.
Print Assumptions in_open_spec.
Print Assumptions lo_le_hi.
Print Assumptions knots_point.
Print Assumptions knots_frame_mid.
Print Assumptions mid_strict.
Print Assumptions mid_in_open.
Print Assumptions cands_in_mid.
Print Assumptions snoc_strict.
Print Assumptions cons_frame_strict.
Print Assumptions knots_strict.
Print Assumptions heading_in_range.
Print Assumptions heading_root_in_cands.
Print Assumptions mid_root.
