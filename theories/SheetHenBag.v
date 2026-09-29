(* ============================================================================
   NetTopologySuite.Proofs.SheetHenBag
   ----------------------------------------------------------------------------
   ∀-bag letter 1 of 6 (#816). Owner decision: name the arm ∀-bag.
   Freeze-neutral: definitions and the support/window invariant only.
   claimId: 0007-forall-bag

   JTS/NTS: noding bag (MCIndexNoder / NodedSegmentString iteration).
   Reuses Sheet, Hen, Chicken, Egg, 𝓘 (IResult), I_ok, IHit, IEmpty,
   IDecline, chord_split, circ_split. Does not remint LeftoverBagTermArm
   or LoopDischarged. The width-refutation lemmas in SheetHenCookLoop
   stay where they are.

   Year-1 support is the original chord or circle. Split pieces copy it.
   same_support is Leibniz equality on that carrier (not a geometric
   line quotient). A window is a closed parameter interval on the
   support. 𝓘 parameters are relative to the piece; the absolute
   parameter is win_abs = lo + u·(hi−lo).

   MkNurbs and MkClothoid are BagIntakeDecline at intake. That judgement
   is not oracle IDecline (DeclineTag). On a progress IHit both pieces
   are replaced by cooked chord_split / circ_split pieces. The new
   vertex is ShareOne (share_one_same_hen): one hen on every new joint,
   not MintTwo.

   bag_step supersedes leftover_bag_step (SheetHenCookLoopModulo,
   LStepHit | LStepDecline; HostRhoModuloKissShare shows there is no
   third constructor) and circ_leftover_bag_step (CStepHit |
   CStepDecline). Those Decline constructors are identity. This Decline
   is fail-closed: a live bag becomes BagDeclined, and that state only
   stutters. IEmpty does not step. circ_leftover_bag_term_forall stays
   unproved and unrefuted; this letter does not inhabit it. The locked
   vesica |H|=2 measure stays the QED in CircularCookLeftoverTwoHit.

   TODO letter 3: StepCoincide is not a bag_step constructor. Identical
   support and window collapse to one egg carrying both provenance
   labels — the slot is coincide_same / coincide_prov.

   3-axiom host. No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra List PeanoNat Bool.
From NTS.Proofs Require Import Distance SheetHenCook.
Import ListNotations.
Local Open Scope R_scope.
Local Open Scope list_scope.

(* -------------------------------------------------------------------------- *)
(* Support: the original chord or circle. Pieces inherit the value.           *)
(* -------------------------------------------------------------------------- *)

Inductive BagSupport : Type :=
| SuppChord : ChordEgg -> BagSupport
| SuppCircle : CircularEgg -> BagSupport.

Definition same_support (s1 s2 : BagSupport) : Prop := s1 = s2.

Lemma same_support_refl : forall s, same_support s s.
Proof. intros s. reflexivity. Qed.

Lemma same_support_sym : forall s1 s2, same_support s1 s2 -> same_support s2 s1.
Proof. intros s1 s2 H. unfold same_support in *. symmetry. exact H. Qed.

Definition support_at (s : BagSupport) (t : R) : Point :=
  match s with
  | SuppChord c => chord_eval c t
  | SuppCircle c => circ_eval c t
  end.

(* -------------------------------------------------------------------------- *)
(* Window: closed parameter interval on a support.                            *)
(* -------------------------------------------------------------------------- *)

Record Window : Type := mkWindow {
  win_lo : R;
  win_hi : R
}.

Definition window_ordered (w : Window) : Prop := win_lo w <= win_hi w.

Definition win_abs (w : Window) (u : R) : R :=
  win_lo w + u * (win_hi w - win_lo w).

Definition sub_lo (w : Window) (u : R) : Window :=
  mkWindow (win_lo w) (win_abs w u).

Definition sub_hi (w : Window) (u : R) : Window :=
  mkWindow (win_abs w u) (win_hi w).

Definition window_chord (c : ChordEgg) (w : Window) : ChordEgg :=
  mkChordEgg (chord_eval c (win_lo w)) (chord_eval c (win_hi w)).

Definition window_circ (c : CircularEgg) (w : Window) : CircularEgg :=
  mkCircularEgg (circ_o c) (circ_r c)
    (circ_theta0 c + win_lo w * circ_sweep c)
    ((win_hi w - win_lo w) * circ_sweep c).

Definition window_pts (s : BagSupport) (w : Window) (p : Point) : Prop :=
  exists t, win_lo w <= t <= win_hi w /\ p = support_at s t.

(* -------------------------------------------------------------------------- *)
(* Piece: chicken (egg + hens) plus support, window, provenance labels.       *)
(* -------------------------------------------------------------------------- *)

Record BagPiece : Type := mkBagPiece {
  bp_ck : Chicken;
  bp_support : BagSupport;
  bp_window : Window;
  bp_prov : list Hen
}.

Definition piece_realizes (pc : BagPiece) : Prop :=
  match bp_support pc, ck_egg (bp_ck pc) with
  | SuppChord c, MkChord e => e = window_chord c (bp_window pc)
  | SuppCircle c, MkCirc e => e = window_circ c (bp_window pc)
  | _, _ => False
  end.

Definition piece_wf (pc : BagPiece) : Prop :=
  piece_realizes pc /\ window_ordered (bp_window pc).

Definition piece_endpoint (pc : BagPiece) (p : Point) : Prop :=
  p = support_at (bp_support pc) (win_lo (bp_window pc)) \/
  p = support_at (bp_support pc) (win_hi (bp_window pc)).

(* -------------------------------------------------------------------------- *)
(* Intake. BagIntakeDecline is not IDecline. Year-1 accepts chord-on-chord   *)
(* and circle-on-circle only. NURBS, clothoid, tags, and class mismatch       *)
(* decline here, before any oracle call.                                      *)
(* -------------------------------------------------------------------------- *)

Inductive BagIntake : Type :=
| BagTaken : BagPiece -> BagIntake
| BagIntakeDecline : BagIntake.

Definition bag_intake (ck : Chicken) (sup : BagSupport) (w : Window)
    (prov : list Hen) : BagIntake :=
  match ck_egg ck, sup with
  | MkChord _, SuppChord _ => BagTaken (mkBagPiece ck sup w prov)
  | MkCirc _, SuppCircle _ => BagTaken (mkBagPiece ck sup w prov)
  | _, _ => BagIntakeDecline
  end.

Inductive DeclineTag : Type :=
| TagIntakeDecline
| TagIDecline.

Definition intake_decline_tag (r : BagIntake) : option DeclineTag :=
  match r with
  | BagIntakeDecline => Some TagIntakeDecline
  | BagTaken _ => None
  end.

Definition oracle_decline_tag (o : IResult) : option DeclineTag :=
  match o with
  | IDecline => Some TagIDecline
  | _ => None
  end.

Lemma intake_decline_neq_IDecline :
  intake_decline_tag BagIntakeDecline <> oracle_decline_tag IDecline.
Proof. discriminate. Qed.

Lemma nurbs_declined_at_intake :
  forall ck n sup w prov,
    ck_egg ck = MkNurbs n ->
    bag_intake ck sup w prov = BagIntakeDecline.
Proof.
  intros [src dst egg] n sup w prov He.
  simpl in He. subst egg. destruct sup; reflexivity.
Qed.

Lemma clothoid_declined_at_intake :
  forall ck c sup w prov,
    ck_egg ck = MkClothoid c ->
    bag_intake ck sup w prov = BagIntakeDecline.
Proof.
  intros [src dst egg] c sup w prov He.
  simpl in He. subst egg. destruct sup; reflexivity.
Qed.

Lemma out_of_scope_declined_at_intake :
  forall ck cl sup w prov,
    ck_egg ck = MkOutOfScope cl ->
    bag_intake ck sup w prov = BagIntakeDecline.
Proof.
  intros [src dst egg] cl sup w prov He.
  simpl in He. subst egg. destruct sup; reflexivity.
Qed.

Lemma chord_on_circle_declines :
  forall ck c circ w prov,
    ck_egg ck = MkChord c ->
    bag_intake ck (SuppCircle circ) w prov = BagIntakeDecline.
Proof.
  intros [src dst egg] c circ w prov He.
  simpl in He. subst egg. reflexivity.
Qed.

Lemma chord_intake_taken :
  forall src dst e c w prov,
    exists pc,
      bag_intake (mkChicken src dst (MkChord e)) (SuppChord c) w prov =
      BagTaken pc.
Proof.
  intros src dst e c w prov.
  eexists. reflexivity.
Qed.

Lemma circ_intake_taken :
  forall src dst e c w prov,
    exists pc,
      bag_intake (mkChicken src dst (MkCirc e)) (SuppCircle c) w prov =
      BagTaken pc.
Proof.
  intros src dst e c w prov.
  eexists. reflexivity.
Qed.

Lemma realizing_not_nurbs :
  forall pc n, piece_realizes pc -> ck_egg (bp_ck pc) <> MkNurbs n.
Proof.
  intros [[src dst egg] sup w prov] n Hr.
  destruct sup; destruct egg; simpl in Hr; try contradiction; discriminate.
Qed.

Lemma realizing_not_clothoid :
  forall pc c, piece_realizes pc -> ck_egg (bp_ck pc) <> MkClothoid c.
Proof.
  intros [[src dst egg] sup w prov] c Hr.
  destruct sup; destruct egg; simpl in Hr; try contradiction; discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Letter 3 slot. Not a bag_step constructor. Identical support and window    *)
(* collapse to one egg; the merged piece carries both provenance lists.       *)
(* -------------------------------------------------------------------------- *)

Definition coincide_same (a b : BagPiece) : Prop :=
  same_support (bp_support a) (bp_support b) /\
  bp_window a = bp_window b.

Definition coincide_prov (a b : BagPiece) : list Hen :=
  bp_prov a ++ bp_prov b.

Lemma coincide_prov_keeps_left :
  forall a b h, In h (bp_prov a) -> In h (coincide_prov a b).
Proof.
  intros a b h H. unfold coincide_prov. apply in_or_app. left. exact H.
Qed.

Lemma coincide_prov_keeps_right :
  forall a b h, In h (bp_prov b) -> In h (coincide_prov a b).
Proof.
  intros a b h H. unfold coincide_prov. apply in_or_app. right. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* Cooked split. Children copy the support. Windows are sub_lo / sub_hi.      *)
(* Eggs are chord_split / circ_split. The new vertex is ShareOne h.           *)
(* -------------------------------------------------------------------------- *)

Definition split_piece (pc : BagPiece) (u : R) (h : Hen) : BagPiece * BagPiece :=
  let ck := bp_ck pc in
  let sup := bp_support pc in
  let prov := bp_prov pc in
  let wl := sub_lo (bp_window pc) u in
  let wr := sub_hi (bp_window pc) u in
  match ck_egg ck with
  | MkChord e =>
      let s := chord_split e u in
      (mkBagPiece (mkChicken (ck_src ck) h (MkChord (fst s))) sup wl prov,
       mkBagPiece (mkChicken h (ck_dst ck) (MkChord (snd s))) sup wr prov)
  | MkCirc e =>
      let s := circ_split e u in
      (mkBagPiece (mkChicken (ck_src ck) h (MkCirc (fst s))) sup wl prov,
       mkBagPiece (mkChicken h (ck_dst ck) (MkCirc (snd s))) sup wr prov)
  | _ => (pc, pc)
  end.

Lemma split_preserves_same_support :
  forall pc u h,
    same_support (bp_support (fst (split_piece pc u h))) (bp_support pc) /\
    same_support (bp_support (snd (split_piece pc u h))) (bp_support pc).
Proof.
  intros [[src dst egg] sup w prov] u h.
  destruct egg; simpl; split; reflexivity.
Qed.

Lemma split_piece_chord_cook :
  forall src dst e sup w prov u h,
    let pc := mkBagPiece (mkChicken src dst (MkChord e)) sup w prov in
    ck_egg (bp_ck (fst (split_piece pc u h))) = MkChord (fst (chord_split e u)) /\
    ck_src (bp_ck (fst (split_piece pc u h))) = src /\
    ck_dst (bp_ck (fst (split_piece pc u h))) = h /\
    ck_egg (bp_ck (snd (split_piece pc u h))) = MkChord (snd (chord_split e u)) /\
    ck_src (bp_ck (snd (split_piece pc u h))) = h /\
    ck_dst (bp_ck (snd (split_piece pc u h))) = dst.
Proof.
  intros. unfold pc. simpl. repeat split; reflexivity.
Qed.

Lemma split_piece_circ_cook :
  forall src dst e sup w prov u h,
    let pc := mkBagPiece (mkChicken src dst (MkCirc e)) sup w prov in
    ck_egg (bp_ck (fst (split_piece pc u h))) = MkCirc (fst (circ_split e u)) /\
    ck_src (bp_ck (fst (split_piece pc u h))) = src /\
    ck_dst (bp_ck (fst (split_piece pc u h))) = h /\
    ck_egg (bp_ck (snd (split_piece pc u h))) = MkCirc (snd (circ_split e u)) /\
    ck_src (bp_ck (snd (split_piece pc u h))) = h /\
    ck_dst (bp_ck (snd (split_piece pc u h))) = dst.
Proof.
  intros. unfold pc. simpl. repeat split; reflexivity.
Qed.

Lemma chord_window_eval :
  forall c w u,
    chord_eval (window_chord c w) u = chord_eval c (win_abs w u).
Proof.
  intros [p0 p1] [lo hi] u.
  unfold window_chord, chord_eval, win_abs. simpl.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma circ_window_eval :
  forall c w u,
    circ_eval (window_circ c w) u = circ_eval c (win_abs w u).
Proof.
  intros c [lo hi] u.
  unfold window_circ, circ_eval, win_abs. cbn.
  apply (f_equal2 mkPoint).
  - replace (circ_theta0 c + lo * circ_sweep c +
             u * ((hi - lo) * circ_sweep c))
      with (circ_theta0 c + (lo + u * (hi - lo)) * circ_sweep c) by ring.
    reflexivity.
  - replace (circ_theta0 c + lo * circ_sweep c +
             u * ((hi - lo) * circ_sweep c))
      with (circ_theta0 c + (lo + u * (hi - lo)) * circ_sweep c) by ring.
    reflexivity.
Qed.

Lemma subwindow_ordered :
  forall w u,
    window_ordered w ->
    0 <= u <= 1 ->
    window_ordered (sub_lo w u) /\ window_ordered (sub_hi w u).
Proof.
  intros [lo hi] u Hord Hu.
  unfold window_ordered, sub_lo, sub_hi, win_abs in *.
  simpl in *.
  destruct Hu as [Hu0 Hu1].
  assert (Hgap : 0 <= hi - lo).
  { pose proof (Rle_minus _ _ Hord) as Hm.
    apply Ropp_le_contravar in Hm.
    replace (- 0) with 0 in Hm by ring.
    replace (- (lo - hi)) with (hi - lo) in Hm by ring.
    exact Hm. }
  split.
  - replace lo with (lo + 0) at 1 by ring.
    apply Rplus_le_compat_l. apply Rmult_le_pos; assumption.
  - apply Rle_trans with (lo + 1 * (hi - lo)).
    + apply Rplus_le_compat_l.
      apply Rmult_le_compat_r; [exact Hgap|exact Hu1].
    + replace (lo + 1 * (hi - lo)) with hi by ring.
      apply Rle_refl.
Qed.

Lemma chord_split_windows :
  forall c w u,
    fst (chord_split (window_chord c w) u) = window_chord c (sub_lo w u) /\
    snd (chord_split (window_chord c w) u) = window_chord c (sub_hi w u).
Proof.
  intros c w u. split.
  - unfold chord_split. cbn [fst].
    unfold window_chord at 3. cbn.
    apply f_equal2.
    + unfold window_chord. cbn. reflexivity.
    + unfold sub_lo, win_abs. cbn. apply chord_window_eval.
  - unfold chord_split. cbn [snd].
    unfold window_chord at 3. cbn.
    apply f_equal2.
    + unfold sub_hi, win_abs. cbn. apply chord_window_eval.
    + unfold window_chord. cbn. reflexivity.
Qed.

Lemma circ_split_windows :
  forall c w u,
    fst (circ_split (window_circ c w) u) = window_circ c (sub_lo w u) /\
    snd (circ_split (window_circ c w) u) = window_circ c (sub_hi w u).
Proof.
  intros c [lo hi] u.
  unfold window_circ, circ_split, sub_lo, sub_hi, win_abs. cbn.
  split.
  - replace (u * ((hi - lo) * circ_sweep c))
      with (((lo + u * (hi - lo)) - lo) * circ_sweep c) by ring.
    reflexivity.
  - replace (circ_theta0 c + lo * circ_sweep c +
             u * ((hi - lo) * circ_sweep c))
      with (circ_theta0 c + (lo + u * (hi - lo)) * circ_sweep c) by ring.
    replace ((1 - u) * ((hi - lo) * circ_sweep c))
      with ((hi - (lo + u * (hi - lo))) * circ_sweep c) by ring.
    reflexivity.
Qed.

Lemma window_split_union :
  forall s w u p,
    window_ordered w ->
    0 <= u <= 1 ->
    window_pts s w p <->
    window_pts s (sub_lo w u) p \/ window_pts s (sub_hi w u) p.
Proof.
  intros s [lo hi] u p Hord Hu.
  unfold window_ordered in Hord. simpl in Hord.
  unfold window_pts, sub_lo, sub_hi, win_abs. simpl.
  destruct (subwindow_ordered (mkWindow lo hi) u Hord Hu) as [HloOrd HhiOrd].
  unfold window_ordered, sub_lo, sub_hi, win_abs in HloOrd, HhiOrd.
  simpl in HloOrd, HhiOrd.
  assert (Hlo : lo <= lo + u * (hi - lo)) by exact HloOrd.
  assert (Hhi : lo + u * (hi - lo) <= hi) by exact HhiOrd.
  split.
  - intros [t [Ht Hp]].
    destruct (Rle_lt_dec t (lo + u * (hi - lo))) as [Hle|Hlt].
    + left. exists t. split; [|exact Hp].
      destruct Ht as [Htlo Hthi]. split; [exact Htlo|exact Hle].
    + right. exists t. split; [|exact Hp].
      destruct Ht as [Htlo Hthi]. split; [apply Rlt_le; exact Hlt|exact Hthi].
  - intros [[t [Ht Hp]]|[t [Ht Hp]]].
    + exists t. split; [|exact Hp].
      destruct Ht as [Htlo Htabs]. split; [exact Htlo|].
      apply Rle_trans with (lo + u * (hi - lo)); [exact Htabs|exact Hhi].
    + exists t. split; [|exact Hp].
      destruct Ht as [Htabs Hthi]. split; [|exact Hthi].
      apply Rle_trans with (lo + u * (hi - lo)); [exact Hlo|exact Htabs].
Qed.

Lemma split_windows_sub :
  forall pc u h,
    piece_realizes pc ->
    bp_support (fst (split_piece pc u h)) = bp_support pc /\
    bp_support (snd (split_piece pc u h)) = bp_support pc /\
    bp_window (fst (split_piece pc u h)) = sub_lo (bp_window pc) u /\
    bp_window (snd (split_piece pc u h)) = sub_hi (bp_window pc) u.
Proof.
  intros [[src dst egg] sup w prov] u h Hr.
  destruct sup as [c|c]; destruct egg as [e|e|e|e|e];
    simpl in Hr; try contradiction; simpl; repeat split; reflexivity.
Qed.

Lemma split_window_iff :
  forall pc u h p,
    piece_wf pc ->
    0 <= u <= 1 ->
    window_pts (bp_support pc) (bp_window pc) p <->
    window_pts (bp_support (fst (split_piece pc u h)))
               (bp_window (fst (split_piece pc u h))) p \/
    window_pts (bp_support (snd (split_piece pc u h)))
               (bp_window (snd (split_piece pc u h))) p.
Proof.
  intros pc u h p [Hr Ho] Hu.
  destruct (split_windows_sub pc u h Hr) as [Hs1 [Hs2 [Hw1 Hw2]]].
  rewrite Hs1, Hs2, Hw1, Hw2.
  apply window_split_union; assumption.
Qed.

Lemma split_piece_wf :
  forall pc u h,
    piece_wf pc ->
    0 <= u <= 1 ->
    piece_wf (fst (split_piece pc u h)) /\
    piece_wf (snd (split_piece pc u h)).
Proof.
  intros pc u h [Hr Ho] Hu.
  destruct pc as [[src dst egg] sup w prov].
  destruct (subwindow_ordered w u Ho Hu) as [HordL HordR].
  unfold piece_realizes in Hr.
  destruct sup as [c|c]; destruct egg as [e|e|e|e|e]; simpl in Hr; try contradiction.
  - subst e. simpl.
    destruct (chord_split_windows c w u) as [HL HR].
    unfold piece_wf, piece_realizes. simpl.
    split.
    + split; [exact HL|exact HordL].
    + split; [exact HR|exact HordR].
  - subst e. simpl.
    destruct (circ_split_windows c w u) as [HL HR].
    unfold piece_wf, piece_realizes. simpl.
    split.
    + split; [exact HL|exact HordL].
    + split; [exact HR|exact HordR].
Qed.

Lemma hit_param_in_unit :
  forall a b p ti tj,
    piece_realizes a ->
    piece_realizes b ->
    I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck b)) (IHit p ti tj) ->
    0 <= ti <= 1 /\ 0 <= tj <= 1.
Proof.
  intros a b p ti tj Ha Hb Hok.
  destruct a as [[sa da ea] supa wa pa].
  destruct b as [[sb db eb] supb wb pb].
  unfold piece_realizes in Ha, Hb. unfold I_ok in Hok.
  destruct supa as [ca|ca]; destruct ea as [ea|ea|ea|ea|ea];
    simpl in Ha, Hb, Hok; try contradiction.
  - subst ea.
    destruct supb as [cb|cb].
    + destruct eb as [eb|eb|eb|eb|eb]; simpl in Hb, Hok; try contradiction.
      subst eb.
      destruct Hok as [[Hti _] [Htj _]].
      split; assumption.
    + destruct eb as [eb|eb|eb|eb|eb]; simpl in Hb, Hok; try contradiction.
      subst eb.
      destruct Hok as [_ [[Hti _] [Htj _]]].
      split; assumption.
  - subst ea.
    destruct supb as [cb|cb].
    + destruct eb as [eb|eb|eb|eb|eb]; simpl in Hb, Hok; try contradiction.
      subst eb.
      destruct Hok as [_ [[Hti _] [Htj _]]].
      split; assumption.
    + destruct eb as [eb|eb|eb|eb|eb]; simpl in Hb, Hok; try contradiction.
      subst eb.
      destruct Hok as [[Hti _] [Htj _]].
      split; assumption.
Qed.

Lemma hit_at_abs :
  forall a b p ti tj,
    piece_realizes a ->
    piece_realizes b ->
    I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck b)) (IHit p ti tj) ->
    p = support_at (bp_support a) (win_abs (bp_window a) ti) /\
    p = support_at (bp_support b) (win_abs (bp_window b) tj).
Proof.
  intros a b p ti tj Ha Hb Hok.
  destruct a as [[sa da ea] supa wa pa].
  destruct b as [[sb db eb] supb wb pb].
  unfold piece_realizes in Ha, Hb. unfold I_ok in Hok.
  destruct supa as [ca|ca]; destruct ea as [ea|ea|ea|ea|ea];
    simpl in Ha, Hb, Hok; try contradiction.
  - subst ea.
    destruct supb as [cb|cb].
    + destruct eb as [eb|eb|eb|eb|eb]; simpl in Hb, Hok; try contradiction.
      subst eb.
      destruct Hok as [[_ Hp1] [_ Hp2]].
      split.
      * rewrite Hp1. unfold support_at. simpl. apply chord_window_eval.
      * rewrite Hp2. unfold support_at. simpl. apply chord_window_eval.
    + destruct eb as [eb|eb|eb|eb|eb]; simpl in Hb, Hok; try contradiction.
      subst eb.
      destruct Hok as [_ [[_ Hp1] [_ Hp2]]].
      split.
      * rewrite Hp1. unfold support_at. simpl. apply chord_window_eval.
      * rewrite Hp2. unfold support_at. simpl. apply circ_window_eval.
  - subst ea.
    destruct supb as [cb|cb].
    + destruct eb as [eb|eb|eb|eb|eb]; simpl in Hb, Hok; try contradiction.
      subst eb.
      destruct Hok as [_ [[_ Hp1] [_ Hp2]]].
      split.
      * rewrite Hp1. unfold support_at. simpl. apply circ_window_eval.
      * rewrite Hp2. unfold support_at. simpl. apply chord_window_eval.
    + destruct eb as [eb|eb|eb|eb|eb]; simpl in Hb, Hok; try contradiction.
      subst eb.
      destruct Hok as [[_ Hp1] [_ Hp2]].
      split.
      * rewrite Hp1. unfold support_at. simpl. apply circ_window_eval.
      * rewrite Hp2. unfold support_at. simpl. apply circ_window_eval.
Qed.

Lemma split_keeps_endpoints :
  forall pc u h p,
    piece_endpoint pc p ->
    piece_endpoint (fst (split_piece pc u h)) p \/
    piece_endpoint (snd (split_piece pc u h)) p.
Proof.
  intros [[src dst egg] sup w prov] u h p Hep.
  unfold piece_endpoint in Hep. simpl in Hep.
  destruct egg; simpl; unfold piece_endpoint; simpl.
  - destruct Hep as [Hep|Hep].
    + left. left. exact Hep.
    + right. right. exact Hep.
  - destruct Hep as [Hep|Hep].
    + left. left. exact Hep.
    + right. right. exact Hep.
  - left. exact Hep.
  - left. exact Hep.
  - left. exact Hep.
Qed.

Lemma split_child_endpoint_account :
  forall pc u h p,
    (piece_endpoint (fst (split_piece pc u h)) p ->
       piece_endpoint pc p \/
       p = support_at (bp_support pc) (win_abs (bp_window pc) u)) /\
    (piece_endpoint (snd (split_piece pc u h)) p ->
       piece_endpoint pc p \/
       p = support_at (bp_support pc) (win_abs (bp_window pc) u)).
Proof.
  intros [[src dst egg] sup w prov] u h p.
  unfold piece_endpoint. simpl.
  destruct egg; simpl; split; intro Hep; unfold piece_endpoint in Hep; simpl in Hep.
  - destruct Hep as [Hep|Hep].
    + left. left. exact Hep.
    + right. exact Hep.
  - destruct Hep as [Hep|Hep].
    + right. exact Hep.
    + left. right. exact Hep.
  - destruct Hep as [Hep|Hep].
    + left. left. exact Hep.
    + right. exact Hep.
  - destruct Hep as [Hep|Hep].
    + right. exact Hep.
    + left. right. exact Hep.
  - left. exact Hep.
  - left. exact Hep.
  - left. exact Hep.
  - left. exact Hep.
  - left. exact Hep.
  - left. exact Hep.
Qed.

(* -------------------------------------------------------------------------- *)
(* Bag. Finite piece list on a sheet, or a failed-closed decline.             *)
(* -------------------------------------------------------------------------- *)

Inductive SheetBag : Type :=
| BagLive : Sheet -> list BagPiece -> SheetBag
| BagDeclined : Sheet -> SheetBag.

Definition bag_sheet (b : SheetBag) : Sheet :=
  match b with
  | BagLive sh _ => sh
  | BagDeclined sh => sh
  end.

Definition bag_inv (b : SheetBag) : Prop :=
  match b with
  | BagDeclined _ => True
  | BagLive _ pcs => forall pc, In pc pcs -> piece_wf pc
  end.

Definition support_image (pcs : list BagPiece) (s : BagSupport) (p : Point) : Prop :=
  exists pc, In pc pcs /\ bp_support pc = s /\ window_pts s (bp_window pc) p.

Definition family_vertex (pcs : list BagPiece) (s : BagSupport) (p : Point) : Prop :=
  exists pc, In pc pcs /\ bp_support pc = s /\ piece_endpoint pc p.

(* Progress hit: an IHit whose point is not already a vertex of both
   supports' piece families. IEmpty and IDecline are not progress. *)
Definition progress_hit (pcs : list BagPiece) (a b : BagPiece) (o : IResult) : Prop :=
  match o with
  | IHit p _ _ =>
      ~ (family_vertex pcs (bp_support a) p /\
         family_vertex pcs (bp_support b) p)
  | IEmpty => False
  | IDecline => False
  end.

Definition bag_noded (b : SheetBag) : Prop :=
  match b with
  | BagDeclined _ => True
  | BagLive _ pcs =>
      forall i j a b0 o,
        nth_error pcs i = Some a ->
        nth_error pcs j = Some b0 ->
        i <> j ->
        I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck b0)) o ->
        ~ progress_hit pcs a b0 o
  end.

Fixpoint filter_idx {A : Type} (keep : nat -> bool) (l : list A) (n : nat)
  : list A :=
  match l with
  | nil => nil
  | x :: xs =>
      if keep n then x :: filter_idx keep xs (S n)
      else filter_idx keep xs (S n)
  end.

Definition keep_other_idx (i j : nat) : nat -> bool :=
  fun k => negb (orb (Nat.eqb k i) (Nat.eqb k j)).

Definition drop_pair (i j : nat) (l : list BagPiece) : list BagPiece :=
  filter_idx (keep_other_idx i j) l 0.

Definition cooked_four (a b : BagPiece) (ti tj : R) (h : Hen) : list BagPiece :=
  [fst (split_piece a ti h); snd (split_piece a ti h);
   fst (split_piece b tj h); snd (split_piece b tj h)].

Definition progress_pieces (pcs : list BagPiece) (i j : nat)
    (a b : BagPiece) (ti tj : R) (h : Hen) : list BagPiece :=
  cooked_four a b ti tj h ++ drop_pair i j pcs.

Inductive bag_progress_step : SheetBag -> SheetBag -> Prop :=
| StepProgress :
    forall (sh : Sheet) (pcs : list BagPiece) (i j : nat)
           (a b : BagPiece) (p : Point) (ti tj : R) (h : Hen),
      nth_error pcs i = Some a ->
      nth_error pcs j = Some b ->
      i <> j ->
      piece_wf a ->
      piece_wf b ->
      I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck b)) (IHit p ti tj) ->
      progress_hit pcs a b (IHit p ti tj) ->
      bag_progress_step
        (BagLive sh pcs)
        (BagLive sh (progress_pieces pcs i j a b ti tj h)).

Inductive bag_decline_step : SheetBag -> SheetBag -> Prop :=
| StepIDecline :
    forall (sh : Sheet) (pcs : list BagPiece) (i j : nat) (a b : BagPiece),
      nth_error pcs i = Some a ->
      nth_error pcs j = Some b ->
      i <> j ->
      I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck b)) IDecline ->
      bag_decline_step (BagLive sh pcs) (BagDeclined sh)
| StepDeclineAbsorb :
    forall sh, bag_decline_step (BagDeclined sh) (BagDeclined sh).

(* Hit or Decline only, same shape as leftover_bag_step / circ_leftover_bag_step.
   No coincide constructor (letter 3). Decline is not the identity step. *)
Definition bag_step (b b' : SheetBag) : Prop :=
  bag_progress_step b b' \/ bag_decline_step b b'.

Lemma bag_step_progress_or_decline :
  forall b b',
    bag_step b b' ->
    bag_progress_step b b' \/ bag_decline_step b b'.
Proof. intros b b' H. exact H. Qed.

Lemma split_joints_share_one :
  forall pc u h,
    piece_realizes pc ->
    ck_dst (bp_ck (fst (split_piece pc u h))) =
      fst (apply_id_decision (ShareOne h)) /\
    ck_src (bp_ck (snd (split_piece pc u h))) =
      snd (apply_id_decision (ShareOne h)).
Proof.
  intros [[src dst egg] sup w prov] u h Hr.
  destruct sup as [c|c]; destruct egg as [e|e|e|e|e];
    simpl in Hr; try contradiction; simpl; split; reflexivity.
Qed.

Lemma progress_pair_share_one :
  forall a b ua ub h,
    piece_realizes a ->
    piece_realizes b ->
    fst (apply_id_decision (ShareOne h)) =
      snd (apply_id_decision (ShareOne h)) /\
    ck_dst (bp_ck (fst (split_piece a ua h))) = h /\
    ck_src (bp_ck (snd (split_piece a ua h))) = h /\
    ck_dst (bp_ck (fst (split_piece b ub h))) = h /\
    ck_src (bp_ck (snd (split_piece b ub h))) = h.
Proof.
  intros a b ua ub h Ha Hb.
  destruct (split_joints_share_one a ua h Ha) as [HaL HaR].
  destruct (split_joints_share_one b ub h Hb) as [HbL HbR].
  unfold apply_id_decision in *. simpl in *.
  split. { exact (share_one_same_hen h). }
  repeat split; assumption.
Qed.

(* LStepDecline / CStepDecline leave the bag. A live IDecline does not. *)
Lemma live_decline_not_identity :
  forall sh pcs,
    ~ bag_decline_step (BagLive sh pcs) (BagLive sh pcs).
Proof.
  intros sh pcs H.
  inversion H.
Qed.

Lemma filter_idx_In :
  forall (A : Type) (keep : nat -> bool) (l : list A) (n : nat) (x : A),
    In x (filter_idx keep l n) -> In x l.
Proof.
  intros A keep l.
  induction l as [|hd tl IH]; intros n x H.
  - simpl in H. contradiction.
  - simpl in H. destruct (keep n) eqn:Ek.
    + destruct H as [->|H].
      * left. reflexivity.
      * right. eapply IH. exact H.
    + right. eapply IH. exact H.
Qed.

Lemma keep_other_idx_true :
  forall i j k, k <> i -> k <> j -> keep_other_idx i j k = true.
Proof.
  intros i j k Hi Hj. unfold keep_other_idx.
  apply negb_true_iff. apply orb_false_iff. split.
  - apply Nat.eqb_neq. exact Hi.
  - apply Nat.eqb_neq. exact Hj.
Qed.

Lemma filter_idx_keep_In :
  forall (A : Type) (keep : nat -> bool) (l : list A) (n k : nat) (x : A),
    nth_error l k = Some x ->
    keep (Nat.add n k) = true ->
    In x (filter_idx keep l n).
Proof.
  intros A keep l.
  induction l as [|hd tl IH]; intros n k x Hk Hkeep.
  - destruct k; simpl in Hk; discriminate.
  - destruct k as [|k'].
    + simpl in Hk. inversion Hk. subst hd.
      simpl. rewrite Nat.add_0_r in Hkeep. rewrite Hkeep.
      left. reflexivity.
    + simpl in Hk. simpl.
      rewrite Nat.add_succ_r in Hkeep.
      rewrite <- Nat.add_succ_l in Hkeep.
      destruct (keep n) eqn:Ek.
      * right. eapply IH; eauto.
      * eapply IH; eauto.
Qed.

Lemma drop_pair_keeps :
  forall i j pcs k pc,
    nth_error pcs k = Some pc ->
    k <> i ->
    k <> j ->
    In pc (drop_pair i j pcs).
Proof.
  intros i j pcs k pc Hk Hi Hj.
  apply (filter_idx_keep_In _ (keep_other_idx i j) pcs 0 k pc Hk).
  rewrite Nat.add_0_l. apply keep_other_idx_true; assumption.
Qed.

Lemma step_preserves_sheet :
  forall b b', bag_step b b' -> bag_sheet b = bag_sheet b'.
Proof.
  intros b b' [H|H].
  - destruct H. reflexivity.
  - destruct H; reflexivity.
Qed.

Lemma step_preserves_inv :
  forall b b',
    bag_inv b ->
    bag_step b b' ->
    bag_inv b'.
Proof.
  intros b b' Hinv [Hprog|Hdec].
  - destruct Hprog
      as [sh pcs i j a b0 p ti tj h Hi Hj Hij Hwfa Hwfb Hok Hpr].
    unfold bag_inv. intros pc Hin.
    destruct (hit_param_in_unit a b0 p ti tj (proj1 Hwfa) (proj1 Hwfb) Hok)
      as [Hti Htj].
    apply in_app_or in Hin.
    destruct Hin as [Hfour|Hkeep].
    + unfold cooked_four in Hfour. simpl in Hfour.
      destruct Hfour as [<-|[<-|[<-|[<-|[]]]]].
      * exact (proj1 (split_piece_wf a ti h Hwfa Hti)).
      * exact (proj2 (split_piece_wf a ti h Hwfa Hti)).
      * exact (proj1 (split_piece_wf b0 tj h Hwfb Htj)).
      * exact (proj2 (split_piece_wf b0 tj h Hwfb Htj)).
    + apply filter_idx_In in Hkeep.
      unfold bag_inv in Hinv. apply Hinv. exact Hkeep.
  - destruct Hdec; exact I.
Qed.

Lemma progress_preserves_support_image :
  forall pcs i j a b p0 ti tj h s p,
    nth_error pcs i = Some a ->
    nth_error pcs j = Some b ->
    i <> j ->
    piece_wf a ->
    piece_wf b ->
    I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck b)) (IHit p0 ti tj) ->
    support_image pcs s p <->
    support_image (progress_pieces pcs i j a b ti tj h) s p.
Proof.
  intros pcs i j a b p0 ti tj h s p Hi Hj Hij Hwfa Hwfb Hok.
  destruct (hit_param_in_unit a b p0 ti tj (proj1 Hwfa) (proj1 Hwfb) Hok)
    as [Hti Htj].
  split.
  - intros [pc [Hin [Hs Hpt]]].
    destruct (In_nth_error pcs pc Hin) as [k Hk].
    destruct (Nat.eq_dec k i) as [->|Hki].
    + assert (E : pc = a).
      { rewrite Hk in Hi. inversion Hi. subst. reflexivity. }
      subst pc. rewrite <- Hs in Hpt.
      destruct (proj1 (split_window_iff a ti h p Hwfa Hti) Hpt) as [Hfst|Hsnd].
      * destruct (split_preserves_same_support a ti h) as [Eq _].
        unfold same_support in Eq.
        rewrite Eq in Hfst. rewrite Hs in Hfst.
        exists (fst (split_piece a ti h)).
        split.
        { unfold progress_pieces. apply in_or_app. left.
          unfold cooked_four. simpl. left. reflexivity. }
        split. { rewrite Eq. exact Hs. }
        exact Hfst.
      * destruct (split_preserves_same_support a ti h) as [_ Eq].
        unfold same_support in Eq.
        rewrite Eq in Hsnd. rewrite Hs in Hsnd.
        exists (snd (split_piece a ti h)).
        split.
        { unfold progress_pieces. apply in_or_app. left.
          unfold cooked_four. simpl. right. left. reflexivity. }
        split. { rewrite Eq. exact Hs. }
        exact Hsnd.
    + destruct (Nat.eq_dec k j) as [->|Hkj].
      * assert (E : pc = b).
        { rewrite Hk in Hj. inversion Hj. subst. reflexivity. }
        subst pc. rewrite <- Hs in Hpt.
        destruct (proj1 (split_window_iff b tj h p Hwfb Htj) Hpt) as [Hfst|Hsnd].
        -- destruct (split_preserves_same_support b tj h) as [Eq _].
           unfold same_support in Eq.
           rewrite Eq in Hfst. rewrite Hs in Hfst.
           exists (fst (split_piece b tj h)).
           split.
           { unfold progress_pieces. apply in_or_app. left.
             unfold cooked_four. simpl. right. right. left. reflexivity. }
           split. { rewrite Eq. exact Hs. }
           exact Hfst.
        -- destruct (split_preserves_same_support b tj h) as [_ Eq].
           unfold same_support in Eq.
           rewrite Eq in Hsnd. rewrite Hs in Hsnd.
           exists (snd (split_piece b tj h)).
           split.
           { unfold progress_pieces. apply in_or_app. left.
             unfold cooked_four. simpl. right. right. right. left. reflexivity. }
           split. { rewrite Eq. exact Hs. }
           exact Hsnd.
      * exists pc.
        split.
        { unfold progress_pieces. apply in_or_app. right.
          apply (drop_pair_keeps i j pcs k pc); assumption. }
        split; assumption.
  - intros [pc [Hin [Hs Hpt]]].
    unfold progress_pieces in Hin. apply in_app_or in Hin.
    destruct Hin as [Hfour|Hkeep].
    + unfold cooked_four in Hfour. simpl in Hfour.
      destruct Hfour as [<-|[<-|[<-|[<-|[]]]]].
      * destruct (split_window_iff a ti h p Hwfa Hti) as [_ Hback].
        assert (Hpt1 :
          window_pts (bp_support (fst (split_piece a ti h)))
                     (bp_window (fst (split_piece a ti h))) p).
        { rewrite Hs. exact Hpt. }
        specialize (Hback (or_introl Hpt1)).
        destruct (split_preserves_same_support a ti h) as [Eq _].
        unfold same_support in Eq.
        rewrite <- Eq in Hback. rewrite Hs in Hback.
        exists a.
        split. { exact (nth_error_In pcs i Hi). }
        split. { rewrite <- Eq. exact Hs. }
        exact Hback.
      * destruct (split_window_iff a ti h p Hwfa Hti) as [_ Hback].
        assert (Hpt1 :
          window_pts (bp_support (snd (split_piece a ti h)))
                     (bp_window (snd (split_piece a ti h))) p).
        { rewrite Hs. exact Hpt. }
        specialize (Hback (or_intror Hpt1)).
        destruct (split_preserves_same_support a ti h) as [_ Eq].
        unfold same_support in Eq.
        rewrite <- Eq in Hback. rewrite Hs in Hback.
        exists a.
        split. { exact (nth_error_In pcs i Hi). }
        split. { rewrite <- Eq. exact Hs. }
        exact Hback.
      * destruct (split_window_iff b tj h p Hwfb Htj) as [_ Hback].
        assert (Hpt1 :
          window_pts (bp_support (fst (split_piece b tj h)))
                     (bp_window (fst (split_piece b tj h))) p).
        { rewrite Hs. exact Hpt. }
        specialize (Hback (or_introl Hpt1)).
        destruct (split_preserves_same_support b tj h) as [Eq _].
        unfold same_support in Eq.
        rewrite <- Eq in Hback. rewrite Hs in Hback.
        exists b.
        split. { exact (nth_error_In pcs j Hj). }
        split. { rewrite <- Eq. exact Hs. }
        exact Hback.
      * destruct (split_window_iff b tj h p Hwfb Htj) as [_ Hback].
        assert (Hpt1 :
          window_pts (bp_support (snd (split_piece b tj h)))
                     (bp_window (snd (split_piece b tj h))) p).
        { rewrite Hs. exact Hpt. }
        specialize (Hback (or_intror Hpt1)).
        destruct (split_preserves_same_support b tj h) as [_ Eq].
        unfold same_support in Eq.
        rewrite <- Eq in Hback. rewrite Hs in Hback.
        exists b.
        split. { exact (nth_error_In pcs j Hj). }
        split. { rewrite <- Eq. exact Hs. }
        exact Hback.
    + exists pc.
      split. { exact (filter_idx_In _ _ _ _ _ Hkeep). }
      split; assumption.
Qed.

Lemma progress_vertices_mono :
  forall pcs i j a b ti tj h s p,
    nth_error pcs i = Some a ->
    nth_error pcs j = Some b ->
    i <> j ->
    family_vertex pcs s p ->
    family_vertex (progress_pieces pcs i j a b ti tj h) s p.
Proof.
  intros pcs i j a b ti tj h s p Hi Hj Hij [pc [Hin [Hs Hep]]].
  destruct (In_nth_error pcs pc Hin) as [k Hk].
  destruct (Nat.eq_dec k i) as [->|Hki].
  - assert (E : pc = a).
    { rewrite Hk in Hi. inversion Hi. subst. reflexivity. }
    subst pc.
    destruct (split_keeps_endpoints a ti h p Hep) as [H1|H2].
    + exists (fst (split_piece a ti h)).
      split.
      { unfold progress_pieces. apply in_or_app. left.
        unfold cooked_four. simpl. left. reflexivity. }
      split.
      { destruct (split_preserves_same_support a ti h) as [Eq _].
        unfold same_support in Eq. rewrite Eq. exact Hs. }
      exact H1.
    + exists (snd (split_piece a ti h)).
      split.
      { unfold progress_pieces. apply in_or_app. left.
        unfold cooked_four. simpl. right. left. reflexivity. }
      split.
      { destruct (split_preserves_same_support a ti h) as [_ Eq].
        unfold same_support in Eq. rewrite Eq. exact Hs. }
      exact H2.
  - destruct (Nat.eq_dec k j) as [->|Hkj].
    + assert (E : pc = b).
      { rewrite Hk in Hj. inversion Hj. subst. reflexivity. }
      subst pc.
      destruct (split_keeps_endpoints b tj h p Hep) as [H1|H2].
      * exists (fst (split_piece b tj h)).
        split.
        { unfold progress_pieces. apply in_or_app. left.
          unfold cooked_four. simpl. right. right. left. reflexivity. }
        split.
        { destruct (split_preserves_same_support b tj h) as [Eq _].
          unfold same_support in Eq. rewrite Eq. exact Hs. }
        exact H1.
      * exists (snd (split_piece b tj h)).
        split.
        { unfold progress_pieces. apply in_or_app. left.
          unfold cooked_four. simpl. right. right. right. left. reflexivity. }
        split.
        { destruct (split_preserves_same_support b tj h) as [_ Eq].
          unfold same_support in Eq. rewrite Eq. exact Hs. }
        exact H2.
    + exists pc.
      split.
      { unfold progress_pieces. apply in_or_app. right.
        apply (drop_pair_keeps i j pcs k pc); assumption. }
      split; assumption.
Qed.

Lemma progress_vertices_only_adds :
  forall pcs i j a b p0 ti tj h s p,
    nth_error pcs i = Some a ->
    nth_error pcs j = Some b ->
    piece_wf a ->
    piece_wf b ->
    I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck b)) (IHit p0 ti tj) ->
    family_vertex (progress_pieces pcs i j a b ti tj h) s p ->
    family_vertex pcs s p \/ p = p0.
Proof.
  intros pcs i j a b p0 ti tj h s p Hi Hj Hwfa Hwfb Hok [pc [Hin [Hs Hep]]].
  destruct (hit_at_abs a b p0 ti tj (proj1 Hwfa) (proj1 Hwfb) Hok) as [HaAbs HbAbs].
  unfold progress_pieces in Hin. apply in_app_or in Hin.
  destruct Hin as [Hfour|Hkeep].
  - unfold cooked_four in Hfour. simpl in Hfour.
    destruct Hfour as [<-|[<-|[<-|[<-|[]]]]].
    + destruct (split_child_endpoint_account a ti h p) as [Hacc _].
      destruct (Hacc Hep) as [Hold|Hnew].
      * left. exists a.
        split. { exact (nth_error_In pcs i Hi). }
        split.
        { destruct (split_preserves_same_support a ti h) as [Eq _].
          unfold same_support in Eq. rewrite <- Eq. exact Hs. }
        exact Hold.
      * right. rewrite Hnew. symmetry. exact HaAbs.
    + destruct (split_child_endpoint_account a ti h p) as [_ Hacc].
      destruct (Hacc Hep) as [Hold|Hnew].
      * left. exists a.
        split. { exact (nth_error_In pcs i Hi). }
        split.
        { destruct (split_preserves_same_support a ti h) as [_ Eq].
          unfold same_support in Eq. rewrite <- Eq. exact Hs. }
        exact Hold.
      * right. rewrite Hnew. symmetry. exact HaAbs.
    + destruct (split_child_endpoint_account b tj h p) as [Hacc _].
      destruct (Hacc Hep) as [Hold|Hnew].
      * left. exists b.
        split. { exact (nth_error_In pcs j Hj). }
        split.
        { destruct (split_preserves_same_support b tj h) as [Eq _].
          unfold same_support in Eq. rewrite <- Eq. exact Hs. }
        exact Hold.
      * right. rewrite Hnew. symmetry. exact HbAbs.
    + destruct (split_child_endpoint_account b tj h p) as [_ Hacc].
      destruct (Hacc Hep) as [Hold|Hnew].
      * left. exists b.
        split. { exact (nth_error_In pcs j Hj). }
        split.
        { destruct (split_preserves_same_support b tj h) as [_ Eq].
          unfold same_support in Eq. rewrite <- Eq. exact Hs. }
        exact Hold.
      * right. rewrite Hnew. symmetry. exact HbAbs.
  - left. exists pc.
    split. { exact (filter_idx_In _ _ _ _ _ Hkeep). }
    split; assumption.
Qed.

Lemma decline_absorbing :
  forall sh b,
    bag_step (BagDeclined sh) b ->
    b = BagDeclined sh.
Proof.
  intros sh b [Hprog|Hdec].
  - inversion Hprog.
  - inversion Hdec; subst; reflexivity.
Qed.

Lemma noded_no_progress_step :
  forall b b',
    bag_noded b ->
    ~ bag_progress_step b b'.
Proof.
  intros b b' Hn Hstep.
  destruct Hstep
    as [sh pcs i j a b0 p ti tj h Hi Hj Hij Hwfa Hwfb Hok Hpr].
  simpl in Hn.
  exact (Hn i j a b0 (IHit p ti tj) Hi Hj Hij Hok Hpr).
Qed.

Lemma noded_live_step_declines :
  forall sh pcs b',
    bag_noded (BagLive sh pcs) ->
    bag_step (BagLive sh pcs) b' ->
    bag_decline_step (BagLive sh pcs) b'.
Proof.
  intros sh pcs b' Hn [Hp|Hd].
  - exfalso. exact (noded_no_progress_step _ _ Hn Hp).
  - exact Hd.
Qed.

Lemma iempty_not_progress :
  forall pcs a b, ~ progress_hit pcs a b IEmpty.
Proof. intros pcs a b H. simpl in H. exact H. Qed.

Lemma idecline_not_progress :
  forall pcs a b, ~ progress_hit pcs a b IDecline.
Proof. intros pcs a b H. simpl in H. exact H. Qed.

Lemma empty_bag_noded :
  forall sh, bag_noded (BagLive sh nil).
Proof.
  intros sh i j a b0 o Hi. destruct i; discriminate.
Qed.

Lemma declined_bag_noded :
  forall sh, bag_noded (BagDeclined sh).
Proof. intros sh. exact I. Qed.

Print Assumptions same_support_refl.
Print Assumptions same_support_sym.
Print Assumptions intake_decline_neq_IDecline.
Print Assumptions nurbs_declined_at_intake.
Print Assumptions clothoid_declined_at_intake.
Print Assumptions out_of_scope_declined_at_intake.
Print Assumptions chord_on_circle_declines.
Print Assumptions chord_intake_taken.
Print Assumptions circ_intake_taken.
Print Assumptions realizing_not_nurbs.
Print Assumptions realizing_not_clothoid.
Print Assumptions coincide_prov_keeps_left.
Print Assumptions coincide_prov_keeps_right.
Print Assumptions split_preserves_same_support.
Print Assumptions split_piece_chord_cook.
Print Assumptions split_piece_circ_cook.
Print Assumptions chord_window_eval.
Print Assumptions circ_window_eval.
Print Assumptions subwindow_ordered.
Print Assumptions chord_split_windows.
Print Assumptions circ_split_windows.
Print Assumptions window_split_union.
Print Assumptions split_windows_sub.
Print Assumptions split_window_iff.
Print Assumptions split_piece_wf.
Print Assumptions hit_param_in_unit.
Print Assumptions hit_at_abs.
Print Assumptions split_keeps_endpoints.
Print Assumptions split_child_endpoint_account.
Print Assumptions filter_idx_In.
Print Assumptions keep_other_idx_true.
Print Assumptions filter_idx_keep_In.
Print Assumptions drop_pair_keeps.
Print Assumptions bag_step_progress_or_decline.
Print Assumptions split_joints_share_one.
Print Assumptions progress_pair_share_one.
Print Assumptions live_decline_not_identity.
Print Assumptions step_preserves_sheet.
Print Assumptions step_preserves_inv.
Print Assumptions progress_preserves_support_image.
Print Assumptions progress_vertices_mono.
Print Assumptions progress_vertices_only_adds.
Print Assumptions decline_absorbing.
Print Assumptions noded_no_progress_step.
Print Assumptions noded_live_step_declines.
Print Assumptions iempty_not_progress.
Print Assumptions idecline_not_progress.
Print Assumptions empty_bag_noded.
Print Assumptions declined_bag_noded.
