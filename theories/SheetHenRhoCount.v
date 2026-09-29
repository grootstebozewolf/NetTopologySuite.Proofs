(* ============================================================================
   NetTopologySuite.Proofs.SheetHenRhoCount
   ----------------------------------------------------------------------------
   Letter 2 slice: candidate lists and ρ.
   SheetHenRho.v is the Require Export umbrella. claimId: none.
   Does not remint 0007-forall-bag. 3-axiom host.
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From NTS.Proofs Require Export SheetHenRhoCarrier.
From Stdlib Require Import Reals Lra Lia List PeanoNat Bool Permutation ZArith.
From NTS.Proofs Require Import
  Distance Polynomial CircleChart SheetHenCookCore SheetHenCircEgg
  SheetHenBag ChartLineQuadratic HostCircChordOracle Atan2.
Import ListNotations.
Local Open Scope R_scope.
Local Open Scope list_scope.

(* -------------------------------------------------------------------------- *)
(* Explicit candidates. Overlap uses the convex hull of window-endpoint keys. *)
(* -------------------------------------------------------------------------- *)
Definition chord_dd (c : ChordEgg) : R :=
  chord_dx c * chord_dx c + chord_dy c * chord_dy c.
Definition quad_roots (a b c : R) : list R :=
  if req_b a 0 then nil
  else let d := discriminant a b c in
       if Rlt_dec d 0 then nil
       else if req_b d 0 then [(- b) / (2 * a)]
       else [(- b + sqrt d) / (2 * a); (- b - sqrt d) / (2 * a)].
Definition line_circle_pts (s : ChordEgg) (c : CircularEgg) : list Point :=
  if req_b (lc_qa s) 0 then if req_b (lc_qc s c) 0 then [ce_p0 s] else nil
  else map (chord_eval s) (quad_roots (lc_qa s) (lc_qb s c) (lc_qc s c)).
Definition cramer_t (a b : ChordEgg) : R :=
  cross2 (px (ce_p0 b) - px (ce_p0 a)) (py (ce_p0 b) - py (ce_p0 a))
         (chord_dx b) (chord_dy b)
  / cross2 (chord_dx a) (chord_dy a) (chord_dx b) (chord_dy b).
Definition line_line_pts (a b : ChordEgg) : list Point :=
  if req_b (cross2 (chord_dx a) (chord_dy a) (chord_dx b) (chord_dy b)) 0
  then nil else [chord_eval a (cramer_t a b)].
Definition same_line_b (a b : ChordEgg) : bool :=
  let dax := chord_dx a in let day := chord_dy a in
  let dbx := chord_dx b in let dby := chord_dy b in
  let vx := px (ce_p0 b) - px (ce_p0 a) in
  let vy := py (ce_p0 b) - py (ce_p0 a) in
  if negb (req_b dax 0 && req_b day 0) then
    req_b (cross2 dax day dbx dby) 0 && req_b (cross2 dax day vx vy) 0
  else if negb (req_b dbx 0 && req_b dby 0) then req_b (cross2 dbx dby vx vy) 0
  else pt_eqb (ce_p0 a) (ce_p0 b).
Definition same_circle_b (a b : CircularEgg) : bool :=
  pt_eqb (circ_o a) (circ_o b) && req_b (circ_r a * circ_r a) (circ_r b * circ_r b).
Definition on_both_b (c1 c2 : CircularEgg) (p : Point) : bool :=
  req_b (dist_sq (circ_o c1) p) (circ_r c1 * circ_r c1) &&
  req_b (dist_sq (circ_o c2) p) (circ_r c2 * circ_r c2).
Definition circle_circle_pts (c1 c2 : CircularEgg) : list Point :=
  if rle_b (dist (circ_o c1) (circ_o c2)) 0 then nil
  else filter (on_both_b c1 c2)
    [radical_point_plus (circ_o c1) (circ_o c2) (circ_r c1) (circ_r c2);
     radical_point_minus (circ_o c1) (circ_o c2) (circ_r c1) (circ_r c2)].
Definition align_k (target src : R) : Z :=
  Int_part ((target - src) / (2 * PI) + / 2).
Definition key_param (ref src : BagSupport) (t : R) : R :=
  match ref, src with
  | SuppChord rc, SuppChord sc =>
      if req_b (chord_dd rc) 0 then 0 else
      ((px (chord_eval sc t) - px (ce_p0 rc)) * chord_dx rc +
       (py (chord_eval sc t) - py (ce_p0 rc)) * chord_dy rc) / chord_dd rc
  | SuppCircle rc, SuppCircle sc =>
      let phase := if rle_b 0 (circ_r rc * circ_r sc) then 0 else PI in
      let kk := align_k (circ_theta0 rc) (circ_theta0 sc + phase) in
      circ_theta0 sc + t * circ_sweep sc + phase + 2 * PI * IZR kk
  | _, _ => 0
  end.
Definition point_of_key (ref : BagSupport) (k : R) : Point :=
  match ref with
  | SuppChord rc => if req_b (chord_dd rc) 0 then ce_p0 rc else chord_eval rc k
  | SuppCircle rc =>
      if req_b (circ_sweep rc) 0 then circ_eval rc 0
      else circ_eval rc ((k - circ_theta0 rc) / circ_sweep rc)
  end.
Definition piece_keys (ref src : BagSupport) (pc : BagPiece) : list R :=
  if support_eqb (bp_support pc) src then
    [key_param ref src (win_lo (bp_window pc)); key_param ref src (win_hi (bp_window pc))]
  else nil.
Definition all_keys (ref src : BagSupport) (pcs : list BagPiece) : list R :=
  flat_map (piece_keys ref src) pcs.
Fixpoint rmin_list (xs : list R) : R :=
  match xs with
  | nil => 0
  | x :: tl => match tl with nil => x | _ => Rmin x (rmin_list tl) end
  end.
Fixpoint rmax_list (xs : list R) : R :=
  match xs with
  | nil => 0
  | x :: tl => match tl with nil => x | _ => Rmax x (rmax_list tl) end
  end.
Definition overlap_pts (pcs : list BagPiece) (s1 s2 : BagSupport) : list Point :=
  match all_keys s1 s1 pcs, all_keys s1 s2 pcs with
  | k1 :: ks1, k2 :: ks2 =>
      let lo := Rmax (rmin_list (k1 :: ks1)) (rmin_list (k2 :: ks2)) in
      let hi := Rmin (rmax_list (k1 :: ks1)) (rmax_list (k2 :: ks2)) in
      if rle_b lo hi then dedup [point_of_key s1 lo; point_of_key s1 hi] else nil
  | _, _ => nil
  end.
Theorem overlap_endpoints_le_2 : forall pcs s1 s2,
  (length (overlap_pts pcs s1 s2) <= 2)%nat.
Proof.
  intros pcs s1 s2. unfold overlap_pts.
  destruct (all_keys s1 s1 pcs) as [|k1 ks1]; [simpl; lia|].
  destruct (all_keys s1 s2 pcs) as [|k2 ks2]; [simpl; lia|].
  destruct (rle_b (Rmax (rmin_list (k1 :: ks1)) (rmin_list (k2 :: ks2)))
                  (Rmin (rmax_list (k1 :: ks1)) (rmax_list (k2 :: ks2)))).
  - eapply Nat.le_trans; [apply dedup_length_le|]. cbn. lia.
  - cbn. lia.
Qed.
Definition raw_pts (pcs : list BagPiece) (s1 s2 : BagSupport) : list Point :=
  match s1, s2 with
  | SuppChord a, SuppChord b =>
      if same_line_b a b then overlap_pts pcs s1 s2 else line_line_pts a b
  | SuppChord a, SuppCircle c => line_circle_pts a c
  | SuppCircle c, SuppChord a => line_circle_pts a c
  | SuppCircle a, SuppCircle b =>
      if same_circle_b a b then overlap_pts pcs s1 s2 else circle_circle_pts a b
  end.
Lemma rmin_lb : forall xs y, In y xs -> rmin_list xs <= y.
Proof.
  induction xs as [|x tl IH]; intros y Hin; simpl in Hin; [contradiction|].
  destruct tl as [|z tl]; simpl.
  - destruct Hin as [->|[]]; lra.
  - destruct Hin as [->|Hin]; [apply Rmin_l|].
    apply Rle_trans with (rmin_list (z :: tl)); [apply Rmin_r| apply IH; exact Hin].
Qed.
Lemma rmin_in : forall xs, xs <> nil -> In (rmin_list xs) xs.
Proof.
  induction xs as [|x tl IH]; intros Hn; [congruence|].
  destruct tl as [|z tl]; simpl; [left; reflexivity|].
  destruct (Rle_dec x (rmin_list (z :: tl))) as [Hx|Hx].
  - rewrite Rmin_left by exact Hx. left. reflexivity.
  - rewrite Rmin_right by (apply Rlt_le, Rnot_le_lt; exact Hx).
    right. apply IH. discriminate.
Qed.
Lemma rmax_ub : forall xs y, In y xs -> y <= rmax_list xs.
Proof.
  induction xs as [|x tl IH]; intros y Hin; simpl in Hin; [contradiction|].
  destruct tl as [|z tl]; simpl.
  - destruct Hin as [->|[]]; lra.
  - destruct Hin as [->|Hin]; [apply Rmax_l|].
    apply Rle_trans with (rmax_list (z :: tl)); [apply IH; exact Hin| apply Rmax_r].
Qed.
Lemma rmax_in : forall xs, xs <> nil -> In (rmax_list xs) xs.
Proof.
  induction xs as [|x tl IH]; intros Hn; [congruence|].
  destruct tl as [|z tl]; simpl; [left; reflexivity|].
  destruct (Rle_dec (rmax_list (z :: tl)) x) as [Hx|Hx].
  - rewrite Rmax_left by exact Hx. left. reflexivity.
  - rewrite Rmax_right by (apply Rlt_le, Rnot_le_lt; exact Hx).
    right. apply IH. discriminate.
Qed.
Lemma key_affine : forall ref src lo hi u,
  key_param ref src (lo + u * (hi - lo)) =
  key_param ref src lo + u * (key_param ref src hi - key_param ref src lo).
Proof.
  intros ref src lo hi u. destruct ref as [rc|rc]; destruct src as [sc|sc]; simpl; try ring.
  - destruct (req_b (chord_dd rc) 0) eqn:Ed; [ring|].
    assert (Hd : chord_dd rc <> 0).
    { intro Z. unfold req_b in Ed. destruct (Req_EM_T (chord_dd rc) 0); congruence. }
    field. exact Hd.
Qed.
Lemma key_between : forall ref src lo hi u, 0 <= u <= 1 ->
  Rmin (key_param ref src lo) (key_param ref src hi) <=
  key_param ref src (lo + u * (hi - lo)) <=
  Rmax (key_param ref src lo) (key_param ref src hi).
Proof.
  intros ref src lo hi u Hu. rewrite key_affine.
  set (x := key_param ref src lo). set (y := key_param ref src hi).
  destruct (Rle_dec x y) as [Hxy|Hxy].
  - rewrite Rmin_left, Rmax_right by exact Hxy. split; nra.
  - assert (Hyx : y <= x) by lra. rewrite Rmin_right, Rmax_left by exact Hyx. split; nra.
Qed.
Lemma split_ends : forall pc u h, piece_realizes pc ->
  bp_support (fst (split_piece pc u h)) = bp_support pc /\
  bp_support (snd (split_piece pc u h)) = bp_support pc /\
  win_lo (bp_window (fst (split_piece pc u h))) = win_lo (bp_window pc) /\
  win_hi (bp_window (fst (split_piece pc u h))) = win_abs (bp_window pc) u /\
  win_lo (bp_window (snd (split_piece pc u h))) = win_abs (bp_window pc) u /\
  win_hi (bp_window (snd (split_piece pc u h))) = win_hi (bp_window pc).
Proof.
  intros [[src dst egg] sup w prov] u h Hr.
  destruct sup as [c|c]; destruct egg as [ch|ci|cl|co|nu];
    unfold piece_realizes in Hr; simpl in Hr; try contradiction.
  - subst ch. simpl. repeat split; reflexivity.
  - subst ci. simpl. repeat split; reflexivity.
Qed.
Lemma piece_key_end : forall ref src pc,
  bp_support pc = src ->
  In (key_param ref src (win_lo (bp_window pc))) (piece_keys ref src pc) /\
  In (key_param ref src (win_hi (bp_window pc))) (piece_keys ref src pc).
Proof.
  intros ref src pc Hs. unfold piece_keys. rewrite Hs, support_eqb_refl. simpl. auto.
Qed.
Lemma in_all_of : forall ref src pcs pc k,
  In pc pcs -> In k (piece_keys ref src pc) -> In k (all_keys ref src pcs).
Proof.
  intros. unfold all_keys. apply in_flat_map. exists pc. split; assumption.
Qed.
Lemma old_key_in_new : forall ref s pcs i j a b ti tj h k,
  nth_error pcs i = Some a -> nth_error pcs j = Some b -> i <> j ->
  piece_realizes a -> piece_realizes b ->
  In k (all_keys ref s pcs) ->
  In k (all_keys ref s (progress_pieces pcs i j a b ti tj h)).
Proof.
  intros ref s pcs i j a b ti tj h k Hi Hj Hij Hra Hrb Hin.
  apply in_flat_map in Hin. destruct Hin as [pc [Hpc Hk]].
  destruct (In_nth_error _ _ Hpc) as [idx Hidx].
  destruct (split_ends a ti h Hra) as [Sa1 [Sa2 [La1 [La2 [La3 La4]]]]].
  destruct (split_ends b tj h Hrb) as [Sb1 [Sb2 [Lb1 [Lb2 [Lb3 Lb4]]]]].
  destruct (Nat.eq_dec idx i) as [->|Ni].
  - assert (Epc : pc = a) by (rewrite Hidx in Hi; inversion Hi; reflexivity). subst pc.
    unfold piece_keys in Hk. destruct (support_eqb (bp_support a) s) eqn:Eb;
      simpl in Hk; [| contradiction].
    destruct Hk as [Ek|[Ek|[]]].
    + apply (in_all_of _ _ _ (fst (split_piece a ti h))).
      * unfold progress_pieces, cooked_four. apply in_or_app. left. simpl. left. reflexivity.
      * unfold piece_keys. rewrite Sa1, Eb. simpl. left. rewrite La1. exact Ek.
    + apply (in_all_of _ _ _ (snd (split_piece a ti h))).
      * unfold progress_pieces, cooked_four. apply in_or_app. left. simpl. right. left. reflexivity.
      * unfold piece_keys. rewrite Sa2, Eb. simpl. right. left. rewrite La4. exact Ek.
  - destruct (Nat.eq_dec idx j) as [->|Nj].
    + assert (Epc : pc = b) by (rewrite Hidx in Hj; inversion Hj; reflexivity). subst pc.
      unfold piece_keys in Hk. destruct (support_eqb (bp_support b) s) eqn:Eb;
        simpl in Hk; [| contradiction].
      destruct Hk as [Ek|[Ek|[]]].
      * apply (in_all_of _ _ _ (fst (split_piece b tj h))).
        -- unfold progress_pieces, cooked_four. apply in_or_app. left. simpl. right. right. left. reflexivity.
        -- unfold piece_keys. rewrite Sb1, Eb. simpl. left. rewrite Lb1. exact Ek.
      * apply (in_all_of _ _ _ (snd (split_piece b tj h))).
        -- unfold progress_pieces, cooked_four. apply in_or_app. left. simpl. right. right. right. left. reflexivity.
        -- unfold piece_keys. rewrite Sb2, Eb. simpl. right. left. rewrite Lb4. exact Ek.
    + apply (in_all_of _ _ _ pc); [| exact Hk].
      unfold progress_pieces. apply in_or_app. right.
      apply (drop_pair_keeps i j pcs idx pc); assumption.
Qed.
Lemma parent_bound : forall ref s pcs pc u h k,
  In pc pcs -> piece_realizes pc -> 0 <= u <= 1 ->
  In k (piece_keys ref s (fst (split_piece pc u h)) ++
        piece_keys ref s (snd (split_piece pc u h))) ->
  match all_keys ref s pcs with
  | nil => False
  | _ => rmin_list (all_keys ref s pcs) <= k /\ k <= rmax_list (all_keys ref s pcs)
  end.
Proof.
  intros ref s pcs pc u h k Hin Hr Hu Hk. apply in_app_or in Hk. destruct Hk as [Hk|Hk].
  - unfold piece_keys in Hk.
    destruct (support_eqb (bp_support (fst (split_piece pc u h))) s) eqn:Eb;
      simpl in Hk; [| contradiction].
    destruct (split_ends pc u h Hr) as [S1 [_ [L1 [Mid [_ _]]]]].
    apply support_eqb_true in Eb. rewrite S1 in Eb.
    destruct (piece_key_end ref s pc Eb) as [Ilo Ihi].
    assert (Alo : In (key_param ref s (win_lo (bp_window pc))) (all_keys ref s pcs))
      by (apply in_all_of with pc; assumption).
    assert (Ahi : In (key_param ref s (win_hi (bp_window pc))) (all_keys ref s pcs))
      by (apply in_all_of with pc; assumption).
    destruct (all_keys ref s pcs) as [|? ?] eqn:E; [simpl in Alo; contradiction|].
    destruct Hk as [Ek|[Ek|[]]].
    + rewrite <- Ek, L1. split; [apply rmin_lb; exact Alo| apply rmax_ub; exact Alo].
    + rewrite <- Ek, Mid.
      assert (Hb := key_between ref s (win_lo (bp_window pc)) (win_hi (bp_window pc)) u Hu).
      replace (win_lo (bp_window pc) + u * (win_hi (bp_window pc) - win_lo (bp_window pc)))
        with (win_abs (bp_window pc) u) in Hb by (unfold win_abs; ring).
      destruct Hb as [Hlo Hhi]. split.
      * apply Rle_trans with (Rmin (key_param ref s (win_lo (bp_window pc)))
                                   (key_param ref s (win_hi (bp_window pc)))); [| exact Hlo].
        apply Rmin_glb; [apply rmin_lb; exact Alo| apply rmin_lb; exact Ahi].
      * apply Rle_trans with (Rmax (key_param ref s (win_lo (bp_window pc)))
                                   (key_param ref s (win_hi (bp_window pc)))); [exact Hhi|].
        apply Rmax_lub; [apply rmax_ub; exact Alo| apply rmax_ub; exact Ahi].
  - unfold piece_keys in Hk.
    destruct (support_eqb (bp_support (snd (split_piece pc u h))) s) eqn:Eb;
      simpl in Hk; [| contradiction].
    destruct (split_ends pc u h Hr) as [_ [S2 [_ [_ [Mid Hhi]]]]].
    apply support_eqb_true in Eb. rewrite S2 in Eb.
    destruct (piece_key_end ref s pc Eb) as [Ilo Ihi].
    assert (Alo : In (key_param ref s (win_lo (bp_window pc))) (all_keys ref s pcs))
      by (apply in_all_of with pc; assumption).
    assert (Ahi : In (key_param ref s (win_hi (bp_window pc))) (all_keys ref s pcs))
      by (apply in_all_of with pc; assumption).
    destruct (all_keys ref s pcs) as [|? ?] eqn:E; [simpl in Alo; contradiction|].
    destruct Hk as [Ek|[Ek|[]]].
    + rewrite <- Ek, Mid.
      assert (Hb := key_between ref s (win_lo (bp_window pc)) (win_hi (bp_window pc)) u Hu).
      replace (win_lo (bp_window pc) + u * (win_hi (bp_window pc) - win_lo (bp_window pc)))
        with (win_abs (bp_window pc) u) in Hb by (unfold win_abs; ring).
      destruct Hb as [Hblo Hbhi]. split.
      * apply Rle_trans with (Rmin (key_param ref s (win_lo (bp_window pc)))
                                   (key_param ref s (win_hi (bp_window pc)))); [| exact Hblo].
        apply Rmin_glb; [apply rmin_lb; exact Alo| apply rmin_lb; exact Ahi].
      * apply Rle_trans with (Rmax (key_param ref s (win_lo (bp_window pc)))
                                   (key_param ref s (win_hi (bp_window pc)))); [exact Hbhi|].
        apply Rmax_lub; [apply rmax_ub; exact Alo| apply rmax_ub; exact Ahi].
    + rewrite <- Ek, Hhi. split; [apply rmin_lb; exact Ahi| apply rmax_ub; exact Ahi].
Qed.
Lemma new_key_bound : forall ref s pcs i j a b ti tj h k,
  nth_error pcs i = Some a -> nth_error pcs j = Some b -> i <> j ->
  piece_realizes a -> piece_realizes b -> 0 <= ti <= 1 -> 0 <= tj <= 1 ->
  In k (all_keys ref s (progress_pieces pcs i j a b ti tj h)) ->
  match all_keys ref s pcs with
  | nil => False
  | _ => rmin_list (all_keys ref s pcs) <= k /\ k <= rmax_list (all_keys ref s pcs)
  end.
Proof.
  intros ref s pcs i j a b ti tj h k Hi Hj Hij Hra Hrb Hti Htj Hin.
  apply in_flat_map in Hin. destruct Hin as [pc [Hpc Hk]].
  unfold progress_pieces in Hpc. apply in_app_or in Hpc. destruct Hpc as [H4|Hdrop].
  - unfold cooked_four in H4. simpl in H4.
    destruct H4 as [<-|[<-|[<-|[<-|[]]]]].
    + apply (parent_bound ref s pcs a ti h k (nth_error_In _ _ Hi) Hra Hti).
      apply in_or_app. left. exact Hk.
    + apply (parent_bound ref s pcs a ti h k (nth_error_In _ _ Hi) Hra Hti).
      apply in_or_app. right. exact Hk.
    + apply (parent_bound ref s pcs b tj h k (nth_error_In _ _ Hj) Hrb Htj).
      apply in_or_app. left. exact Hk.
    + apply (parent_bound ref s pcs b tj h k (nth_error_In _ _ Hj) Hrb Htj).
      apply in_or_app. right. exact Hk.
  - assert (Hold : In k (all_keys ref s pcs)).
    { apply in_all_of with pc; [| exact Hk]. exact (filter_idx_In _ _ _ _ _ Hdrop). }
    destruct (all_keys ref s pcs) as [|? ?] eqn:E; [simpl in Hold; contradiction|].
    split; [apply rmin_lb; exact Hold| apply rmax_ub; exact Hold].
Qed.
Lemma hull_progress : forall ref s pcs i j a b ti tj h,
  nth_error pcs i = Some a -> nth_error pcs j = Some b -> i <> j ->
  piece_realizes a -> piece_realizes b -> 0 <= ti <= 1 -> 0 <= tj <= 1 ->
  let ks := all_keys ref s pcs in
  let ks' := all_keys ref s (progress_pieces pcs i j a b ti tj h) in
  rmin_list ks = rmin_list ks' /\ rmax_list ks = rmax_list ks' /\
  (ks = nil <-> ks' = nil).
Proof.
  intros ref s pcs i j a b ti tj h Hi Hj Hij Hra Hrb Hti Htj ks ks'.
  assert (Hold : forall k, In k ks -> In k ks').
  { intros k Hk. apply old_key_in_new with (i:=i) (j:=j) (a:=a) (b:=b) (ti:=ti) (tj:=tj) (h:=h); assumption. }
  assert (Hnew : forall k, In k ks' ->
    match ks with nil => False | _ => rmin_list ks <= k /\ k <= rmax_list ks end).
  { intros k Hk. apply new_key_bound with (i:=i) (j:=j) (a:=a) (b:=b) (ti:=ti) (tj:=tj) (h:=h); assumption. }
  destruct ks as [|x xs] eqn:Eks.
  - assert (N : ks' = nil).
    { destruct ks' as [|y ys]; [reflexivity|]. exfalso. apply (Hnew y). left. reflexivity. }
    rewrite N. simpl. split; [reflexivity| split; [reflexivity| tauto]].
  - assert (Hin : In (rmin_list (x :: xs)) ks') by (apply Hold, rmin_in; discriminate).
    assert (Hne' : ks' <> nil) by (intro Z; rewrite Z in Hin; simpl in Hin; contradiction).
    assert (Hrm : rmin_list ks' <= rmin_list (x :: xs)) by (apply rmin_lb; exact Hin).
    assert (Hrm2 : rmin_list (x :: xs) <= rmin_list ks').
    { pose proof (rmin_in ks' Hne') as Hm. destruct (Hnew _ Hm) as [H1 _]. exact H1. }
    assert (HinM : In (rmax_list (x :: xs)) ks') by (apply Hold, rmax_in; discriminate).
    assert (HrM : rmax_list (x :: xs) <= rmax_list ks') by (apply rmax_ub; exact HinM).
    assert (HrM2 : rmax_list ks' <= rmax_list (x :: xs)).
    { pose proof (rmax_in ks' Hne') as Hm. destruct (Hnew _ Hm) as [_ H2]. exact H2. }
    split; [lra| split; [lra| split; [intro; discriminate| intro Z; rewrite Z in Hne'; congruence]]].
Qed.

Lemma overlap_eq : forall pcs pcs' s1 s2,
  rmin_list (all_keys s1 s1 pcs) = rmin_list (all_keys s1 s1 pcs') ->
  rmax_list (all_keys s1 s1 pcs) = rmax_list (all_keys s1 s1 pcs') ->
  (all_keys s1 s1 pcs = nil <-> all_keys s1 s1 pcs' = nil) ->
  rmin_list (all_keys s1 s2 pcs) = rmin_list (all_keys s1 s2 pcs') ->
  rmax_list (all_keys s1 s2 pcs) = rmax_list (all_keys s1 s2 pcs') ->
  (all_keys s1 s2 pcs = nil <-> all_keys s1 s2 pcs' = nil) ->
  overlap_pts pcs s1 s2 = overlap_pts pcs' s1 s2.
Proof.
  intros pcs pcs' s1 s2 R1 X1 N1 R2 X2 N2. unfold overlap_pts.
  destruct (all_keys s1 s1 pcs) eqn:A, (all_keys s1 s1 pcs') eqn:B.
  - reflexivity.
  - exfalso. assert (E : r :: l = nil) by (apply (proj1 N1); reflexivity). discriminate.
  - exfalso. assert (E : r :: l = nil) by (apply (proj2 N1); reflexivity). discriminate.
  - destruct (all_keys s1 s2 pcs) eqn:C, (all_keys s1 s2 pcs') eqn:D.
    + reflexivity.
    + exfalso. assert (E : r1 :: l1 = nil) by (apply (proj1 N2); reflexivity). discriminate.
    + exfalso. assert (E : r1 :: l1 = nil) by (apply (proj2 N2); reflexivity). discriminate.
    + rewrite R1, X1, R2, X2. reflexivity.
Qed.

Lemma raw_progress : forall pcs i j a b ti tj h s1 s2,
  nth_error pcs i = Some a -> nth_error pcs j = Some b -> i <> j ->
  piece_realizes a -> piece_realizes b -> 0 <= ti <= 1 -> 0 <= tj <= 1 ->
  raw_pts (progress_pieces pcs i j a b ti tj h) s1 s2 = raw_pts pcs s1 s2.
Proof.
  intros pcs i j a b ti tj h s1 s2 Hi Hj Hij Hra Hrb Hti Htj.
  destruct (hull_progress s1 s1 pcs i j a b ti tj h Hi Hj Hij Hra Hrb Hti Htj) as [M1 [X1 N1]].
  destruct (hull_progress s1 s2 pcs i j a b ti tj h Hi Hj Hij Hra Hrb Hti Htj) as [M2 [X2 N2]].
  destruct s1 as [c1|c1]; destruct s2 as [c2|c2]; simpl.
  - destruct (same_line_b c1 c2).
    + symmetry. apply overlap_eq; assumption.
    + reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (same_circle_b c1 c2).
    + symmetry. apply overlap_eq; assumption.
    + reflexivity.
Qed.
Definition chord_param (c : ChordEgg) (p : Point) : R :=
  ((px p - px (ce_p0 c)) * chord_dx c + (py p - py (ce_p0 c)) * chord_dy c) / chord_dd c.
Definition in_window_chord_b (c : ChordEgg) (w : Window) (p : Point) : bool :=
  if req_b (chord_dd c) 0 then pt_eqb p (ce_p0 c) && rle_b (win_lo w) (win_hi w)
  else let t := chord_param c p in
       (pt_eqb p (chord_eval c t) && rle_b (win_lo w) t) && rle_b t (win_hi w).
Lemma chord_eval_deg : forall c t, chord_dd c = 0 -> chord_eval c t = ce_p0 c.
Proof.
  intros c t Hz. destruct (chord_eval_lin c t) as [Hx Hy].
  destruct (sum_of_squares_zero _ _ Hz) as [Dx Dy].
  apply pt_eq_coords; [rewrite Hx, Dx | rewrite Hy, Dy]; ring.
Qed.
Lemma chord_param_eval : forall c t, chord_dd c <> 0 -> chord_param c (chord_eval c t) = t.
Proof.
  intros c t Hd. destruct (chord_eval_lin c t) as [Hx Hy].
  unfold chord_param, chord_dd in *. rewrite Hx, Hy.
  apply (Rmult_eq_reg_r (chord_dx c * chord_dx c + chord_dy c * chord_dy c)).
  - unfold Rdiv. rewrite Rmult_assoc, (Rinv_l _ Hd), Rmult_1_r. ring.
  - exact Hd.
Qed.
Lemma in_window_chord_spec : forall c w p,
  in_window_chord_b c w p = true <-> window_pts (SuppChord c) w p.
Proof.
  intros c w p. unfold in_window_chord_b, window_pts, support_at.
  destruct (req_b (chord_dd c) 0) eqn:Hd.
  - apply req_b_true in Hd. split.
    + intro H. apply andb_prop in H. destruct H as [Hp Hlo].
      apply pt_eqb_true in Hp. apply rle_b_true in Hlo.
      exists (win_lo w). split; [split; [apply Rle_refl | exact Hlo] |].
      rewrite (chord_eval_deg c (win_lo w) Hd). exact Hp.
    + intros [t [Ht Hp]]. apply andb_true_intro. split.
      * apply pt_eqb_true. rewrite Hp, (chord_eval_deg c t Hd). reflexivity.
      * apply rle_b_true. destruct Ht as [H1 H2]. lra.
  - split.
    + intro H. apply andb_prop in H. destruct H as [H1 Ht2].
      apply andb_prop in H1. destruct H1 as [Hp Ht1].
      exists (chord_param c p). split; [split; apply rle_b_true; assumption |].
      apply pt_eqb_true in Hp. exact Hp.
    + intros [u [Hu Hp]].
      assert (Hdd : chord_dd c <> 0).
      { intro Z. unfold req_b in Hd. destruct (Req_EM_T (chord_dd c) 0); congruence. }
      assert (Et : chord_param c p = u) by (rewrite Hp; apply chord_param_eval; exact Hdd).
      apply andb_true_intro. split; [apply andb_true_intro; split |].
      * apply pt_eqb_true. rewrite Et. exact Hp.
      * apply rle_b_true. rewrite Et. exact (proj1 Hu).
      * apply rle_b_true. rewrite Et. exact (proj2 Hu).
Qed.
Lemma lattice_in : forall t0 sig lo hi (m : Z), 0 < sig ->
  lo <= t0 + IZR m * sig /\ t0 + IZR m * sig <= hi ->
  let n := ceil_Z ((lo - t0) / sig) in
  lo <= t0 + IZR n * sig /\ t0 + IZR n * sig <= hi.
Proof.
  intros t0 sig lo hi m Hs [Hlo Hhi] n.
  set (x := (lo - t0) / sig).
  destruct (ceil_bounds x) as [Hcx Hcy].
  assert (Hx : x <= IZR m).
  { unfold x. eapply Rmult_le_reg_l; [exact Hs |].
    replace (sig * ((lo - t0) / sig)) with (lo - t0) by (field; lra). lra. }
  assert (Hnm : (n <= m)%Z).
  { unfold n. destruct (Z_le_gt_dec (ceil_Z x) m) as [Hle|Hgt]; [exact Hle| exfalso].
    assert (E : IZR (m + 1) <= IZR (ceil_Z x)) by (apply IZR_le; lia).
    rewrite plus_IZR in E. change (IZR 1) with 1 in E. lra. }
  assert (Ein : IZR n <= IZR m) by (apply IZR_le; exact Hnm).
  assert (Elo : lo = t0 + x * sig) by (unfold x; field; lra).
  split.
  - rewrite Elo. apply Rplus_le_compat_l. apply Rmult_le_compat_r; [lra |].
    unfold n. exact Hcx.
  - apply Rle_trans with (t0 + IZR m * sig); [| exact Hhi].
    apply Rplus_le_compat_l. apply Rmult_le_compat_r; lra.
Qed.
Lemma atan_reduce : forall r alpha, r <> 0 ->
  (if rle_b 0 r then atan2 (r * sin alpha) (r * cos alpha)
   else atan2 (- (r * sin alpha)) (- (r * cos alpha))) = reduce_angle alpha.
Proof.
  intros r alpha Hr. destruct (reduce_angle_spec alpha) as [Hrng [Hc Hs]].
  set (beta := reduce_angle alpha).
  assert (Hb : atan2 (sin beta) (cos beta) = beta) by (apply atan2_sin_cos; exact Hrng).
  destruct (rle_b 0 r) eqn:Hrle.
  - apply rle_b_true in Hrle. assert (Hpos : 0 < r) by lra.
    rewrite <- Hc, <- Hs. unfold beta.
    rewrite (atan2_pos_scale r (sin (reduce_angle alpha)) (cos (reduce_angle alpha)) Hpos).
    fold beta. exact Hb.
  - assert (Hneg : r < 0).
    { apply Rnot_le_lt. intro Hle. apply rle_b_true in Hle. rewrite Hle in Hrle. discriminate. }
    replace (- (r * sin alpha)) with ((- r) * sin alpha) by ring.
    replace (- (r * cos alpha)) with ((- r) * cos alpha) by ring.
    assert (Hpos : 0 < - r) by lra.
    rewrite <- Hc, <- Hs. unfold beta.
    rewrite (atan2_pos_scale (- r) (sin (reduce_angle alpha)) (cos (reduce_angle alpha)) Hpos).
    fold beta. exact Hb.
Qed.
Lemma circ_eval_abs_shift : forall c t (d : Z), circ_sweep c <> 0 ->
  circ_eval c (t + IZR d * (2 * PI / Rabs (circ_sweep c))) = circ_eval c t.
Proof.
  intros c t d Hs. unfold circ_eval. set (sw := circ_sweep c) in *.
  assert (Hnz : sw <> 0) by exact Hs. apply pt_eq_coords; cbn.
  - replace (circ_theta0 c + (t + IZR d * (2 * PI / Rabs sw)) * sw)
      with (circ_theta0 c + t * sw + IZR d * (2 * PI / Rabs sw) * sw) by ring.
    destruct (Rle_dec 0 sw) as [Hp|Hn].
    + rewrite (Rabs_pos_eq sw Hp).
      replace (IZR d * (2 * PI / sw) * sw) with (2 * IZR d * PI) by (field; exact Hnz).
      rewrite cos_period_Z. reflexivity.
    +       assert (Hlt : sw < 0) by (apply Rnot_le_lt; exact Hn).
      rewrite (Rabs_left sw Hlt).
      replace (IZR d * (2 * PI / - sw) * sw) with (2 * (- IZR d) * PI) by (field; exact Hnz).
      replace (circ_theta0 c + t * sw + 2 * (- IZR d) * PI)
        with (circ_theta0 c + t * sw + 2 * IZR (- d) * PI) by (rewrite opp_IZR; ring).
      rewrite cos_period_Z. reflexivity.
  - replace (circ_theta0 c + (t + IZR d * (2 * PI / Rabs sw)) * sw)
      with (circ_theta0 c + t * sw + IZR d * (2 * PI / Rabs sw) * sw) by ring.
    destruct (Rle_dec 0 sw) as [Hp|Hn].
    + rewrite (Rabs_pos_eq sw Hp).
      replace (IZR d * (2 * PI / sw) * sw) with (2 * IZR d * PI) by (field; exact Hnz).
      rewrite sin_period_Z. reflexivity.
    +       assert (Hlt : sw < 0) by (apply Rnot_le_lt; exact Hn).
      rewrite (Rabs_left sw Hlt).
      replace (IZR d * (2 * PI / - sw) * sw) with (2 * (- IZR d) * PI) by (field; exact Hnz).
      replace (circ_theta0 c + t * sw + 2 * (- IZR d) * PI)
        with (circ_theta0 c + t * sw + 2 * IZR (- d) * PI) by (rewrite opp_IZR; ring).
      rewrite sin_period_Z. reflexivity.
Qed.
Lemma circ_rep_true : forall c w p t,
  circ_r c <> 0 -> circ_sweep c <> 0 -> win_lo w <= t <= win_hi w -> p = circ_eval c t ->
  let lo := win_lo w in let hi := win_hi w in
  let r := circ_r c in let sw := circ_sweep c in
  let vx := px p - px (circ_o c) in let vy := py p - py (circ_o c) in
  let ang := if rle_b 0 r then atan2 vy vx else atan2 (- vy) (- vx) in
  let t0 := (ang - circ_theta0 c) / sw in
  let sig := 2 * PI / Rabs sw in
  let ts := t0 + IZR (ceil_Z ((lo - t0) / sig)) * sig in
  (rle_b lo ts && rle_b ts hi) && pt_eqb p (circ_eval c ts) = true.
Proof.
  intros c w p t Hr Hs Ht Hp. cbv zeta.
  set (lo := win_lo w). set (hi := win_hi w). set (r := circ_r c). set (sw := circ_sweep c).
  set (vx := px p - px (circ_o c)). set (vy := py p - py (circ_o c)).
  set (alpha := circ_theta0 c + t * sw).
  assert (Hvx : vx = r * cos alpha).
  { unfold vx, alpha, r, sw. rewrite Hp. unfold circ_eval. cbn. ring. }
  assert (Hvy : vy = r * sin alpha).
  { unfold vy, alpha, r, sw. rewrite Hp. unfold circ_eval. cbn. ring. }
  set (ang := if rle_b 0 r then atan2 vy vx else atan2 (- vy) (- vx)).
  assert (Hang : ang = reduce_angle alpha).
  { unfold ang. rewrite Hvx, Hvy. apply atan_reduce. exact Hr. }
  destruct (reduce_angle_period alpha) as [k Hk]. rewrite <- Hang in Hk.
  assert (Esw : t * sw = ang - circ_theta0 c + 2 * PI * IZR k).
  { replace (t * sw) with (alpha - circ_theta0 c) by (unfold alpha; ring).
    rewrite Hk. ring. }
  assert (Et : t = (ang - circ_theta0 c) / sw + IZR k * (2 * PI) / sw).
  { apply (Rmult_eq_reg_r sw); [| exact Hs]. unfold Rdiv. rewrite Rmult_plus_distr_r.
    rewrite !Rmult_assoc, !(Rinv_l sw Hs), !Rmult_1_r. rewrite Esw. ring. }
  set (t0 := (ang - circ_theta0 c) / sw). set (sig := 2 * PI / Rabs sw).
  assert (Hsig : 0 < sig).
  { unfold sig. apply Rdiv_lt_0_compat; [pose proof PI_RGT_0; lra | apply Rabs_pos_lt; exact Hs]. }
  assert (Hm : exists m : Z, t = t0 + IZR m * sig).
  { destruct (Rle_dec 0 sw) as [Hp0|Hn].
    - exists k. unfold t0, sig. rewrite (Rabs_pos_eq sw Hp0), Et.
      replace (IZR k * (2 * PI) / sw) with (IZR k * (2 * PI / sw)) by (field; exact Hs).
      ring.
    - assert (Hlt : sw < 0) by (apply Rnot_le_lt; exact Hn).
      exists (- k)%Z. unfold t0, sig. rewrite (Rabs_left sw Hlt), Et, opp_IZR.
      replace (IZR k * (2 * PI) / sw) with (- IZR k * (2 * PI / - sw)) by (field; exact Hs).
      ring. }
  destruct Hm as [m Hm].
  set (n := ceil_Z ((lo - t0) / sig)). set (ts := t0 + IZR n * sig).
  assert (Hin : lo <= ts /\ ts <= hi).
  { unfold ts, n. pose proof (lattice_in t0 sig lo hi m Hsig) as HL.
    rewrite <- Hm in HL. specialize (HL Ht). cbv zeta in HL. exact HL. }
  assert (Ets : ts = t + IZR (n - m) * sig).
  { unfold ts. rewrite Hm.
    replace (IZR n) with (IZR m + IZR (n - m)).
    - ring.
    - replace (n - m)%Z with (n + Z.opp m)%Z by lia. rewrite plus_IZR, opp_IZR. ring. }
  assert (Ev : circ_eval c ts = circ_eval c t).
  { rewrite Ets. unfold sig, sw. apply circ_eval_abs_shift. exact Hs. }
  apply andb_true_intro. split.
  - apply andb_true_intro. split; apply rle_b_true; tauto.
  - apply pt_eqb_true. rewrite Ev. exact Hp.
Qed.
Definition in_window_circ_b (c : CircularEgg) (w : Window) (p : Point) : bool :=
  let lo := win_lo w in let hi := win_hi w in
  let r := circ_r c in let sw := circ_sweep c in
  let vx := px p - px (circ_o c) in let vy := py p - py (circ_o c) in
  if negb (req_b (vx * vx + vy * vy) (r * r)) then false
  else if req_b r 0 then rle_b lo hi
  else if req_b sw 0 then pt_eqb p (circ_eval c lo) && rle_b lo hi
  else
    let ang := if rle_b 0 r then atan2 vy vx else atan2 (- vy) (- vx) in
    let t0 := (ang - circ_theta0 c) / sw in
    let sig := 2 * PI / Rabs sw in
    let ts := t0 + IZR (ceil_Z ((lo - t0) / sig)) * sig in
    (rle_b lo ts && rle_b ts hi) && pt_eqb p (circ_eval c ts).
Lemma in_window_circ_spec : forall c w p,
  in_window_circ_b c w p = true <-> window_pts (SuppCircle c) w p.
Proof.
  intros c w p. split.
  - intro Hb. unfold in_window_circ_b in Hb. cbv zeta in Hb.
    destruct (negb (req_b ((px p - px (circ_o c)) * (px p - px (circ_o c)) +
                           (py p - py (circ_o c)) * (py p - py (circ_o c)))
                          (circ_r c * circ_r c))) eqn:Hd; [discriminate|].
    apply negb_false_iff in Hd. apply req_b_true in Hd.
    destruct (req_b (circ_r c) 0) eqn:Hr.
    + apply req_b_true in Hr. apply rle_b_true in Hb.
      exists (win_lo w). split; [split; [apply Rle_refl| exact Hb]|].
      rewrite Hr in Hd. replace (0 * 0) with 0 in Hd by ring.
      destruct (sum_of_squares_zero _ _ Hd) as [Zx Zy].
      apply pt_eq_coords; unfold circ_eval; cbn; rewrite Hr.
      * assert (Ex : px p = px (circ_o c)) by lra. rewrite Ex. ring.
      * assert (Ey : py p = py (circ_o c)) by lra. rewrite Ey. ring.
    + destruct (req_b (circ_sweep c) 0) eqn:Hs.
      * apply andb_prop in Hb. destruct Hb as [Hp0 Hle].
        apply pt_eqb_true in Hp0. apply rle_b_true in Hle.
        exists (win_lo w). split; [split; [apply Rle_refl| exact Hle]| exact Hp0].
      * apply andb_prop in Hb. destruct Hb as [Hrng Hp0].
        apply andb_prop in Hrng. destruct Hrng as [Hlo Hhi].
        apply rle_b_true in Hlo. apply rle_b_true in Hhi. apply pt_eqb_true in Hp0.
        match type of Hlo with _ <= ?ts => exists ts end.
        split; [split; [exact Hlo| exact Hhi]| exact Hp0].
  - intros [t [Ht Hp]]. unfold support_at in Hp. unfold in_window_circ_b. cbv zeta.
    assert (Hon : (px p - px (circ_o c)) * (px p - px (circ_o c)) +
                  (py p - py (circ_o c)) * (py p - py (circ_o c)) =
                  circ_r c * circ_r c).
    { rewrite Hp. replace ((px (circ_eval c t) - px (circ_o c)) *
                           (px (circ_eval c t) - px (circ_o c)) +
                           (py (circ_eval c t) - py (circ_o c)) *
                           (py (circ_eval c t) - py (circ_o c)))
        with (dist_sq (circ_o c) (circ_eval c t)) by (unfold dist_sq; ring).
      apply circ_eval_carrier. }
    rewrite Hon.
    assert (Ereq : req_b (circ_r c * circ_r c) (circ_r c * circ_r c) = true)
      by (apply req_b_true; reflexivity).
    rewrite Ereq. cbn [negb].
    destruct (req_b (circ_r c) 0) eqn:Hr.
    + apply rle_b_true. destruct Ht as [H1 H2]. lra.
    + destruct (req_b (circ_sweep c) 0) eqn:Hs.
      * apply req_b_true in Hs. apply andb_true_intro. split.
        -- apply pt_eqb_true. rewrite Hp. unfold circ_eval.
           apply pt_eq_coords; cbn; rewrite Hs;
           replace (circ_theta0 c + t * 0) with (circ_theta0 c + win_lo w * 0) by ring;
           reflexivity.
        -- apply rle_b_true. destruct Ht as [H1 H2]. lra.
      * assert (Hr0 : circ_r c <> 0).
        { intro Z. apply (proj2 (req_b_true _ _)) in Z. rewrite Hr in Z. discriminate. }
        assert (Hs0 : circ_sweep c <> 0).
        { intro Z. apply (proj2 (req_b_true _ _)) in Z. rewrite Hs in Z. discriminate. }
        apply (circ_rep_true c w p t Hr0 Hs0 Ht Hp).
Qed.
Definition in_window_b (s : BagSupport) (w : Window) (p : Point) : bool :=
  match s with
  | SuppChord c => in_window_chord_b c w p
  | SuppCircle c => in_window_circ_b c w p
  end.
Lemma in_window_spec : forall s w p, in_window_b s w p = true <-> window_pts s w p.
Proof.
  intros [c|c]; [apply in_window_chord_spec| apply in_window_circ_spec].
Qed.
Definition in_image_b (pcs : list BagPiece) (s : BagSupport) (p : Point) : bool :=
  existsb (fun pc => support_eqb (bp_support pc) s && in_window_b s (bp_window pc) p) pcs.
Lemma in_image_spec : forall pcs s p,
  in_image_b pcs s p = true <-> support_image pcs s p.
Proof.
  intros pcs s p. unfold in_image_b, support_image. split.
  - intro H. apply existsb_exists in H. destruct H as [pc [Hin Hb]].
    apply andb_prop in Hb. destruct Hb as [Hs Hw].
    exists pc. split; [exact Hin|]. split; [apply support_eqb_true; exact Hs|].
    apply in_window_spec. exact Hw.
  - intros [pc [Hin [Hs Hw]]]. apply existsb_exists. exists pc. split; [exact Hin|].
    apply andb_true_intro. split; [apply support_eqb_true; exact Hs|].
    apply in_window_spec. exact Hw.
Qed.
Definition endpoint_b (pc : BagPiece) (p : Point) : bool :=
  pt_eqb p (support_at (bp_support pc) (win_lo (bp_window pc))) ||
  pt_eqb p (support_at (bp_support pc) (win_hi (bp_window pc))).
Lemma endpoint_spec : forall pc p, endpoint_b pc p = true <-> piece_endpoint pc p.
Proof.
  intros pc p. unfold endpoint_b, piece_endpoint. split.
  - intro H. apply orb_prop in H. destruct H as [H|H]; apply pt_eqb_true in H; [left|right]; exact H.
  - intros [H|H]; apply orb_true_intro; [left|right]; apply pt_eqb_true; exact H.
Qed.
Definition vertex_b (pcs : list BagPiece) (s : BagSupport) (p : Point) : bool :=
  existsb (fun pc => support_eqb (bp_support pc) s && endpoint_b pc p) pcs.
Lemma vertex_spec : forall pcs s p, vertex_b pcs s p = true <-> family_vertex pcs s p.
Proof.
  intros pcs s p. unfold vertex_b, family_vertex. split.
  - intro H. apply existsb_exists in H. destruct H as [pc [Hin Hb]].
    apply andb_prop in Hb. destruct Hb as [Hs He].
    exists pc. split; [exact Hin|]. split; [apply support_eqb_true; exact Hs|].
    apply endpoint_spec. exact He.
  - intros [pc [Hin [Hs He]]]. apply existsb_exists. exists pc. split; [exact Hin|].
    apply andb_true_intro. split; [apply support_eqb_true; exact Hs|].
    apply endpoint_spec. exact He.
Qed.
Definition keep_b (pcs : list BagPiece) (s1 s2 : BagSupport) (p : Point) : bool :=
  (in_image_b pcs s1 p && in_image_b pcs s2 p) &&
  negb (vertex_b pcs s1 p && vertex_b pcs s2 p).
Definition counted (pcs : list BagPiece) (s1 s2 : BagSupport) : list Point :=
  let '(a, b) := canon2 s1 s2 in dedup (filter (keep_b pcs a b) (raw_pts pcs a b)).
Lemma counted_sym : forall pcs s1 s2, counted pcs s1 s2 = counted pcs s2 s1.
Proof. intros. unfold counted. rewrite canon_swap. reflexivity. Qed.
Definition rho_pcs (pcs : list BagPiece) : nat :=
  pair_sum (supports_of pcs) (fun x y => length (counted pcs x y)).
Definition rho (b : SheetBag) : nat :=
  match b with BagLive _ pcs => rho_pcs pcs | BagDeclined _ => 0%nat end.
Lemma supports_progress_perm : forall pcs i j a b ti tj h,
  nth_error pcs i = Some a -> nth_error pcs j = Some b -> i <> j ->
  piece_realizes a -> piece_realizes b ->
  Permutation (supports_of (progress_pieces pcs i j a b ti tj h)) (supports_of pcs).
Proof.
  intros pcs i j a b ti tj h Hi Hj Hij Hra Hrb.
  apply NoDup_Permutation; try apply supports_NoDup. intro s. rewrite !supports_in. split.
  - intros [pc [Hin Hs]]. unfold progress_pieces in Hin. apply in_app_or in Hin.
    destruct Hin as [Hf|Hk].
    + unfold cooked_four in Hf. simpl in Hf.
      destruct Hf as [<-|[<-|[<-|[<-|[]]]]].
      * destruct (split_ends a ti h Hra) as [Ea _]. exists a.
        split; [exact (nth_error_In _ _ Hi)|]. rewrite <- Ea. exact Hs.
      * destruct (split_ends a ti h Hra) as [_ [Ea _]]. exists a.
        split; [exact (nth_error_In _ _ Hi)|]. rewrite <- Ea. exact Hs.
      * destruct (split_ends b tj h Hrb) as [Eb _]. exists b.
        split; [exact (nth_error_In _ _ Hj)|]. rewrite <- Eb. exact Hs.
      * destruct (split_ends b tj h Hrb) as [_ [Eb _]]. exists b.
        split; [exact (nth_error_In _ _ Hj)|]. rewrite <- Eb. exact Hs.
    + exists pc. split; [exact (filter_idx_In _ _ _ _ _ Hk)| exact Hs].
  - intros [pc [Hin Hs]]. destruct (In_nth_error _ _ Hin) as [k Hk].
    destruct (Nat.eq_dec k i) as [->|Hki].
    + assert (Epc : pc = a) by (rewrite Hk in Hi; inversion Hi; reflexivity). subst pc.
      destruct (split_ends a ti h Hra) as [Ea _].
      exists (fst (split_piece a ti h)). split.
      * unfold progress_pieces. apply in_or_app. left. unfold cooked_four. simpl. left. reflexivity.
      * rewrite Ea. exact Hs.
    + destruct (Nat.eq_dec k j) as [->|Hkj].
      * assert (Epc : pc = b) by (rewrite Hk in Hj; inversion Hj; reflexivity). subst pc.
        destruct (split_ends b tj h Hrb) as [Eb _].
        exists (fst (split_piece b tj h)). split.
        { unfold progress_pieces. apply in_or_app. left. unfold cooked_four.
          simpl. right. right. left. reflexivity. }
        rewrite Eb. exact Hs.
      * exists pc. split.
        { unfold progress_pieces. apply in_or_app. right.
          apply (drop_pair_keeps i j pcs k pc); assumption. }
        exact Hs.
Qed.
Lemma keep_step : forall pcs i j a b p0 ti tj h s1 s2 p,
  nth_error pcs i = Some a -> nth_error pcs j = Some b -> i <> j ->
  piece_wf a -> piece_wf b ->
  I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck b)) (IHit p0 ti tj) ->
  progress_hit pcs a b (IHit p0 ti tj) ->
  keep_b (progress_pieces pcs i j a b ti tj h) s1 s2 p = true ->
  keep_b pcs s1 s2 p = true.
Proof.
  intros pcs i j a b p0 ti tj h s1 s2 p Hi Hj Hij Hwfa Hwfb Hok Hpr Hkeep.
  unfold progress_hit in Hpr.
  set (pcs' := progress_pieces pcs i j a b ti tj h) in *.
  unfold keep_b in Hkeep. apply andb_prop in Hkeep. destruct Hkeep as [Himg Hneg].
  apply andb_prop in Himg. destruct Himg as [Hi1 Hi2]. apply negb_true_iff in Hneg.
  apply andb_true_intro. split.
  - apply andb_true_intro. split; apply in_image_spec;
      apply (proj2 (progress_preserves_support_image pcs i j a b p0 ti tj h _ p
        Hi Hj Hij Hwfa Hwfb Hok)); apply in_image_spec; assumption.
  - apply negb_true_iff.
    destruct (vertex_b pcs s1 p && vertex_b pcs s2 p) eqn:Ev; [| reflexivity].
    exfalso. apply andb_prop in Ev. destruct Ev as [V1b V2b].
    apply vertex_spec in V1b. apply vertex_spec in V2b.
    assert (N1 : family_vertex pcs' s1 p)
      by (eapply progress_vertices_mono; eassumption).
    assert (N2 : family_vertex pcs' s2 p)
      by (eapply progress_vertices_mono; eassumption).
    destruct (progress_vertices_only_adds pcs i j a b p0 ti tj h s1 p Hi Hj Hwfa Hwfb Hok N1)
      as [_| Heq].
    + assert (Bad : vertex_b pcs' s1 p && vertex_b pcs' s2 p = true)
        by (apply andb_true_intro; split; apply vertex_spec; assumption).
      rewrite Bad in Hneg. discriminate.
    + assert (Bad : vertex_b pcs' s1 p && vertex_b pcs' s2 p = true)
        by (apply andb_true_intro; split; apply vertex_spec; assumption).
      subst p. rewrite Bad in Hneg. discriminate.
Qed.
Theorem rho_step_nonincreasing : forall b b', bag_step b b' -> (rho b' <= rho b)%nat.
Proof.
  intros b b' [Hp|Hd].
  - destruct Hp as [sh pcs i j a b0 p ti tj h Hi Hj Hij Hwfa Hwfb Hok Hpr].
    simpl. set (pcs' := progress_pieces pcs i j a b0 ti tj h). unfold rho_pcs.
    destruct (hit_param_in_unit a b0 p ti tj (proj1 Hwfa) (proj1 Hwfb) Hok) as [Hti Htj].
    assert (Hperm : Permutation (supports_of pcs') (supports_of pcs)).
    { apply (supports_progress_perm pcs i j a b0 ti tj h Hi Hj Hij (proj1 Hwfa) (proj1 Hwfb)). }
    assert (Hsym : forall x y, length (counted pcs' x y) = length (counted pcs' y x)).
    { intros x y. f_equal. apply counted_sym. }
    rewrite (pair_sum_perm _ _ _ Hperm Hsym). apply pair_sum_le. intros x y.
    unfold counted. destruct (canon2 x y) as [u v].
    assert (Er : raw_pts pcs' u v = raw_pts pcs u v).
    { apply (raw_progress pcs i j a b0 ti tj h u v Hi Hj Hij (proj1 Hwfa) (proj1 Hwfb) Hti Htj). }
    rewrite Er. apply dedup_filter_length. intros q Hq.
    apply (keep_step pcs i j a b0 p ti tj h u v q); assumption.
  - destruct Hd; simpl; [apply Nat.le_0_l| apply Nat.le_refl].
Qed.
Print Assumptions overlap_endpoints_le_2.
Print Assumptions rmin_lb.
Print Assumptions rmin_in.
Print Assumptions rmax_ub.
Print Assumptions rmax_in.
Print Assumptions key_affine.
Print Assumptions key_between.
Print Assumptions split_ends.
Print Assumptions piece_key_end.
Print Assumptions in_all_of.
Print Assumptions old_key_in_new.
Print Assumptions parent_bound.
Print Assumptions new_key_bound.
Print Assumptions hull_progress.
Print Assumptions overlap_eq.
Print Assumptions raw_progress.
Print Assumptions chord_eval_deg.
Print Assumptions chord_param_eval.
Print Assumptions in_window_chord_spec.
Print Assumptions lattice_in.
Print Assumptions atan_reduce.
Print Assumptions circ_eval_abs_shift.
Print Assumptions circ_rep_true.
Print Assumptions in_window_circ_spec.
Print Assumptions in_window_spec.
Print Assumptions in_image_spec.
Print Assumptions endpoint_spec.
Print Assumptions vertex_spec.
Print Assumptions counted_sym.
Print Assumptions supports_progress_perm.
Print Assumptions keep_step.
Print Assumptions rho_step_nonincreasing.
