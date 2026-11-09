(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_CarryCleanTarget
   ----------------------------------------------------------------------------
   carry_clean_priest_target, unconditionally: for every finite Priest-valid
   e, f with abs_sum e + abs_sum f <= 2^(emax-5), carry_clean
   (fast_expansion_sum e f) is nonoverlapping.  Promoted from the probe lane
   (docs/h1-vacuity/ZeroElim.v, PR #1014) for #1015.  The bridge Definitions
   of B64_CarryCleanCore.v are discharged here (no file keeps them as
   hypotheses); carry_clean_fes_priest_nonoverlap is the unfolded form for
   consumers.

   Zero inputs and the carry_clean bridges.

   A Priest chain of length >= 2 has no zero entry (priest_nonoverlapping_R
   needs normalized, hence nonzero, mantissas), so a zero input is exactly a
   singleton chain [0].  Zeros sort first (abs 0), and TwoSum(g, 0) = (g, 0)
   exactly, so
       drop_zeros (fast_expansion_sum e f)
     = drop_zeros (fast_expansion_sum (drop_zeros e) (drop_zeros f)).
   With cascade_reachable_shape (nonzero inputs) this discharges both bridge
   Definitions of B64_CarryCleanCore:
       fes_priest_carry_pattern, fes_priest_reduction_nonoverlap
   the second via UNIQUENESS of carry_pattern block decompositions (the
   Definition quantifies over every bs with that pattern), and hence
   carry_clean_priest_target, unconditionally.

   topic: binary64
   claimId: carry-clean-priest-target
   witness: carry_clean_priest_target_proved

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human-reviewed (PR #1014).
     Assisted-by: Claude
   ========================================================================== *)
From Stdlib Require Import Reals ZArith Lia Lra List Permutation.
From Flocq Require Import IEEE754.Binary Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_lib B64_Pff_bridge
     B64_Expansion B64_FastExpansionSum B64_Overlap_Hierarchy B64_CarryCleanAlgo
     B64_CarryCleanCore B64_CarryCleanLadder B64_CarryCleanOneBit B64_FastExpansionSum_Shewchuk
     B64_CarryCleanRung4 B64_Priest_FES_counterexample.
From NTS.Proofs.Flocq Require Import B64_CarryCleanCascade.
Import ListNotations.
Local Open Scope R_scope.
Local Abbreviation b2r := (Binary.B2R prec emax).

Definition fes_list (l : list binary64) : list binary64 :=
  match l with
  | nil => nil
  | x :: xs => let '(hs, q) := b64_grow_expansion_aux x xs in q :: rev hs
  end.

Lemma fes_list_def : forall e f, fast_expansion_sum e f = fes_list (sort_by_abs (e ++ f)).
Proof. intros e f. reflexivity. Qed.

(* ---- zeros sort to the front --------------------------------------------- *)

Lemma ins_pass : forall x zs T,
  Forall (fun z => b64_is_zero z = true) zs -> b2r x <> 0 ->
  insert_by_abs x (zs ++ T) = zs ++ insert_by_abs x T.
Proof.
  intros x zs T Hz Hx. induction zs as [| z zs IH]; [ reflexivity | ].
  inversion Hz as [| ? ? Hz1 Hz2]; subst. cbn [app].
  rewrite insert_by_abs_gt; [ rewrite IH by exact Hz2; reflexivity | ].
  rewrite (b64_is_zero_R z Hz1), Rabs_R0. apply Rabs_pos_lt. exact Hx.
Qed.

Lemma sort_zero_prefix : forall l, Forall b64_fin l ->
  exists zs, Forall (fun z => b64_is_zero z = true) zs /\
             sort_by_abs l = zs ++ sort_by_abs (drop_zeros l).
Proof.
  induction l as [| x l IH]; intro F.
  - exists []. split; [ constructor | reflexivity ].
  - inversion F as [| ? ? Fx Fl]; subst. destruct (IH Fl) as (zs & Hz & Hs).
    cbn [sort_by_abs]. rewrite Hs.
    destruct (b64_is_zero x) eqn:Ex.
    + exists (x :: zs). split; [ constructor; assumption | ].
      rewrite (drop_zeros_cons_zero x l Ex). cbn [app].
      destruct (zs ++ sort_by_abs (drop_zeros l)) as [| w t] eqn:Ew.
      * reflexivity.
      * apply insert_by_abs_le. rewrite (b64_is_zero_R x Ex), Rabs_R0. apply Rabs_pos.
    + destruct (b64_nz_of_not_zero x Fx Ex) as [_ Nx].
      exists zs. split; [ exact Hz | ].
      rewrite (drop_zeros_cons_nz x l Ex). cbn [sort_by_abs].
      apply ins_pass; assumption.
Qed.

(* ---- TwoSum with a zero accumulator ------------------------------------- *)

Lemma ts_zero_acc : forall g q,
  b64_TwoSum_safe g q -> b64_fin g -> b2r q = 0 ->
  b2r (fst (b64_TwoSum g q)) = b2r g /\ b64_fin (fst (b64_TwoSum g q)) /\
  b64_is_zero (snd (b64_TwoSum g q)) = true.
Proof.
  intros g q S Fg Hq.
  destruct (ts_facts g q S) as (FQ & Fh & RQ & Hex & _ & _). cbv zeta in *.
  assert (HQ : b2r (fst (b64_TwoSum g q)) = b2r g).
  { rewrite RQ, Hq, Rplus_0_r. apply round_generic;
      [ auto with typeclass_instances | apply Binary.generic_format_B2R ]. }
  split; [ exact HQ | split; [ exact FQ | ] ].
  apply b64_is_zero_true; [ exact Fh | lra ].
Qed.

Lemma drop_zeros_app_zero : forall l h, b64_is_zero h = true -> drop_zeros (l ++ [h]) = drop_zeros l.
Proof.
  intros l h Hh. unfold drop_zeros. rewrite filter_app. cbn [filter]. rewrite Hh. cbn [negb]. rewrite app_nil_r. reflexivity.
Qed.

(* a zero accumulator absorbs a zero prefix, then the first nonzero input
   exactly: the whole cascade equals the nonzero cascade up to zero errors. *)
Lemma cascade_zero_prefix : forall zs q nz,
  Forall (fun z => b64_fin z /\ b64_is_zero z = true) zs ->
  Forall (fun y => b64_fin y /\ b64_is_zero y = false) nz ->
  b64_fin q -> b64_is_zero q = true ->
  cascade_safe q (zs ++ nz) ->
  drop_zeros (let '(hs, qf) := b64_grow_expansion_aux q (zs ++ nz) in qf :: rev hs)
  = drop_zeros (fes_list nz).
Proof.
  induction zs as [| z zs IH]; intros q nz Hzs Hnz Fq Zq Hsafe.
  - cbn [app] in *. destruct nz as [| y ys].
    + cbn [b64_grow_expansion_aux fes_list rev app]. rewrite (drop_zeros_cons_zero q [] Zq). reflexivity.
    + inversion Hnz as [| ? ? (Fy & Zy) Hys]; subst.
      destruct Hsafe as [S1 S2].
      destruct (ts_zero_acc y q S1 Fy (b64_is_zero_R q Zq)) as (HQ & FQ & Zh).
      assert (Ey : fst (b64_TwoSum y q) = y).
      { apply b64_eq_of_R; [ exact FQ | exact Fy | exact HQ | ].
        pose proof (b64_nz_of_not_zero y Fy Zy) as [_ N]. rewrite HQ. exact N. }
      cbn [b64_grow_expansion_aux fes_list].
      destruct (b64_TwoSum y q) as [Qn h] eqn:Et. cbn [fst snd] in *. subst Qn.
      destruct (b64_grow_expansion_aux y ys) as [hs qf] eqn:Eg.
      cbn [rev]. replace (qf :: rev hs ++ [h]) with ((qf :: rev hs) ++ [h]) by reflexivity.
      rewrite drop_zeros_app_zero by exact Zh. reflexivity.
  - inversion Hzs as [| ? ? (Fz & Zz) Hzs']; subst.
    cbn [app] in Hsafe |- *. destruct Hsafe as [S1 S2].
    destruct (ts_zero_acc z q S1 Fz (b64_is_zero_R q Zq)) as (HQ & FQ & Zh).
    cbn [b64_grow_expansion_aux].
    destruct (b64_TwoSum z q) as [Qn h] eqn:Et. cbn [fst snd] in *.
    assert (ZQn : b64_is_zero Qn = true) by (apply b64_is_zero_true; [ exact FQ | rewrite HQ; apply (b64_is_zero_R z Zz) ]).
    specialize (IH Qn nz Hzs' Hnz FQ ZQn S2).
    destruct (b64_grow_expansion_aux Qn (zs ++ nz)) as [hs qf] eqn:Eg.
    cbn [rev]. replace (qf :: rev hs ++ [h]) with ((qf :: rev hs) ++ [h]) by reflexivity.
    rewrite drop_zeros_app_zero by exact Zh. exact IH.
Qed.

Lemma Forall_drop_zeros_nz : forall l, Forall b64_fin l ->
  Forall (fun y => b64_fin y /\ b64_is_zero y = false) (drop_zeros l).
Proof.
  intros l F. rewrite Forall_forall in *. intros x Hx. unfold drop_zeros in Hx.
  apply filter_In in Hx as [Hin Hf]. split; [ apply F, Hin | ].
  destruct (b64_is_zero x); [ discriminate | reflexivity ].
Qed.

Lemma fes_drop_zeros_eq : forall e f,
  Forall b64_fin e -> Forall b64_fin f ->
  abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
  drop_zeros (fast_expansion_sum e f)
  = drop_zeros (fast_expansion_sum (drop_zeros e) (drop_zeros f)).
Proof.
  intros e f Fe Ff Hov.
  assert (Fef : Forall b64_fin (e ++ f)) by (apply Forall_app; split; assumption).
  destruct (sort_zero_prefix (e ++ f) Fef) as (zs & Hz & Hs).
  pose proof (fes_cascade_safe e f Fe Ff Hov) as C.
  assert (Hdz : drop_zeros (e ++ f) = drop_zeros e ++ drop_zeros f) by (unfold drop_zeros; apply filter_app).
  rewrite fes_list_def at 1. rewrite fes_list_def. rewrite <- Hdz. rewrite Hs. rewrite Hs in C.
  destruct zs as [| z zs'].
  - reflexivity.
  - cbn [app] in C |- *. inversion Hz as [| ? ? Zz Hz']; subst.
    assert (Fs : Forall b64_fin (sort_by_abs (e ++ f))) by (apply sort_by_abs_Forall; exact Fef).
    rewrite Hs in Fs. cbn [app] in Fs. inversion Fs as [| ? ? Fz Fs']; subst.
    apply Forall_app in Fs' as [Fzs Fnz].
    assert (HZ : Forall (fun z => b64_fin z /\ b64_is_zero z = true) zs').
    { rewrite Forall_forall in *. intros x Hx. split; [ apply Fzs, Hx | apply Hz', Hx ]. }
    assert (HN : Forall (fun y => b64_fin y /\ b64_is_zero y = false) (sort_by_abs (drop_zeros (e ++ f)))).
    { pose proof (Forall_drop_zeros_nz (e ++ f) Fef) as D.
      apply (sort_by_abs_Forall (fun y => b64_fin y /\ b64_is_zero y = false)). exact D. }
    pose proof (cascade_zero_prefix zs' z (sort_by_abs (drop_zeros (e ++ f))) HZ HN Fz Zz C) as A.
    cbn [fes_list]. exact A.
Qed.

(* ---- a Priest chain has a zero entry only when it is a singleton [0] ------ *)

Lemma priest_pair_nz : forall a b, priest_nonoverlapping_b64 a b -> b2r a <> 0 /\ b2r b <> 0.
Proof.
  intros a b (mx & my & kx & ky & Hx & Hy & Hmx & Hmy & _).
  assert (P : 0 < bpow radix2 (prec - 1)) by apply bpow_gt_0.
  split.
  - rewrite Hx. intro H. apply Rmult_integral in H as [H | H].
    + rewrite H, Rabs_R0 in Hmx. lra.
    + pose proof (bpow_gt_0 radix2 kx). lra.
  - rewrite Hy. intro H. apply Rmult_integral in H as [H | H].
    + rewrite H, Rabs_R0 in Hmy. lra.
    + pose proof (bpow_gt_0 radix2 ky). lra.
Qed.

Lemma chain_nz_or_single : forall e, priest_chain e ->
  e = [] \/ (exists z, e = [z] /\ b2r z = 0) \/ Forall (fun x => b2r x <> 0) e.
Proof.
  induction e as [| a [| b r] IH]; intro H.
  - left. reflexivity.
  - destruct (Req_dec (b2r a) 0) as [Z | NZ].
    + right; left. exists a. split; [ reflexivity | exact Z ].
    + right; right. constructor; [ exact NZ | constructor ].
  - cbn [priest_chain] in H. destruct H as [Hp Hc].
    destruct (priest_pair_nz a b Hp) as [Na Nb].
    destruct (IH Hc) as [E | [(z & Ez & Zz) | F]].
    + discriminate E.
    + injection Ez as <- <-. exfalso. exact (Nb Zz).
    + right; right. constructor; assumption.
Qed.

Lemma filter_all : forall (l : list binary64),
  Forall (fun x => b64_is_zero x = false) l -> drop_zeros l = l.
Proof.
  induction l as [| x l IH]; intro H; [ reflexivity | ].
  inversion H as [| ? ? Hx Hl]; subst. rewrite (drop_zeros_cons_nz x l Hx), IH by exact Hl. reflexivity.
Qed.

Lemma chain_drop_zeros : forall e, priest_chain e -> Forall b64_fin e ->
  (Forall (fun x => b2r x <> 0) e /\ drop_zeros e = e) \/ (drop_zeros e = [] /\ abs_sum e = 0).
Proof.
  intros e Hc Hf. destruct (chain_nz_or_single e Hc) as [E | [(z & Ez & Zz) | F]].
  - right. subst. split; reflexivity.
  - right. subst. inversion Hf as [| ? ? Fz _]; subst.
    split; [ rewrite (drop_zeros_cons_zero z [] (b64_is_zero_true z Fz Zz)); reflexivity | ].
    cbn [abs_sum]. rewrite Zz, Rabs_R0. lra.
  - left. split; [ exact F | ]. apply filter_all.
    rewrite Forall_forall in *. intros x Hx. apply b64_is_zero_false; [ apply Hf, Hx | apply F, Hx ].
Qed.

(* ---- nonzero inputs: cascade_reachable_shape ------------------------------ *)

Lemma fes_shape_nz : forall e f,
  priest_chain e -> priest_chain f -> Forall b64_fin e -> Forall b64_fin f ->
  Forall (fun x => b2r x <> 0) (e ++ f) ->
  abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
  exists bs, drop_zeros (fast_expansion_sum e f) = flat_map cblock_expand bs
             /\ carry_shape bs /\ pairs_aligned bs.
Proof.
  intros e f Pe Pf Fe Ff Nz Hov.
  rewrite fes_list_def.
  destruct (sort_by_abs (e ++ f)) as [| x0 xs] eqn:Hs.
  - exists []. split; [ reflexivity | split; [ split; [ constructor | split; [ exact I | exact I ] ] | exact I ] ].
  - assert (HH : cascade_hyps e f x0 xs) by (repeat split; assumption).
    destruct (cascade_reachable_shape e f x0 xs HH) as (bs & Hb & Hsh & Hal).
    exists bs. split; [ | split; assumption ].
    rewrite <- Hb. cbn [fes_list]. unfold cascade_out.
    destruct (b64_grow_expansion_aux x0 xs) as [hs q]. rewrite app_nil_r. reflexivity.
Qed.

Theorem fes_shape_all : forall e f,
  priest_chain e -> priest_chain f -> Forall b64_fin e -> Forall b64_fin f ->
  abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
  exists bs, drop_zeros (fast_expansion_sum e f) = flat_map cblock_expand bs
             /\ carry_shape bs /\ pairs_aligned bs.
Proof.
  intros e f Pe Pf Fe Ff Hov.
  rewrite (fes_drop_zeros_eq e f Fe Ff Hov).
  assert (Fd : forall l, Forall b64_fin l -> Forall b64_fin (drop_zeros l))
    by (intros l F; rewrite Forall_forall in *; intros x Hx; apply F; unfold drop_zeros in Hx; apply filter_In in Hx; exact (proj1 Hx)).
  pose proof (abs_sum_nonneg e) as Ae. pose proof (abs_sum_nonneg f) as Af.
  destruct (chain_drop_zeros e Pe Fe) as [(Nze & De) | (De & Ae0)];
  destruct (chain_drop_zeros f Pf Ff) as [(Nzf & Df) | (Df & Af0)];
    rewrite ?De, ?Df.
  - exact (fes_shape_nz e f Pe Pf Fe Ff (proj2 (Forall_app _ _ _) (conj Nze Nzf)) Hov).
  - refine (fes_shape_nz e [] Pe I Fe (Forall_nil _) _ _).
    + rewrite app_nil_r. exact Nze.
    + cbn [abs_sum]. lra.
  - refine (fes_shape_nz [] f I Pf (Forall_nil _) Ff _ _).
    + cbn [app]. exact Nzf.
    + cbn [abs_sum]. lra.
  - refine (fes_shape_nz [] [] I I (Forall_nil _) (Forall_nil _) (Forall_nil _) _).
    cbn [abs_sum]. pose proof (bpow_gt_0 radix2 (emax - 5)). lra.
Qed.

Theorem fes_priest_carry_pattern_proved : fes_priest_carry_pattern.
Proof.
  intros e f Pe Pf Fe Ff Hov. destruct (fes_shape_all e f Pe Pf Fe Ff Hov) as (bs & Hb & (Ok & Dec & _) & _).
  exists bs. split; [ exact Hb | split; assumption ].
Qed.


(* ---- uniqueness of carry_pattern block decompositions: B64_CarryCleanRung4 *)
(*      pattern_unique (same statement; the probe's duplicate is dropped).    *)

Theorem fes_priest_reduction_nonoverlap_proved : fes_priest_reduction_nonoverlap.
Proof.
  intros e f Pe Pf Fe Ff Hov bs Hbs Hpat.
  destruct (fes_shape_all e f Pe Pf Fe Ff Hov) as (bs0 & Hb0 & Hshape & _).
  destruct Hshape as (Ok0 & Dec0 & No0).
  assert (E : bs = bs0).
  { apply pattern_unique; [ exact Hpat | split; assumption | ]. rewrite <- Hbs, Hb0. reflexivity. }
  subst bs0. exact No0.
Qed.

Theorem carry_clean_priest_target_proved : carry_clean_priest_target.
Proof.
  exact (carry_clean_priest_target_of_bridge fes_priest_carry_pattern_proved fes_priest_reduction_nonoverlap_proved).
Qed.

(* The target, unfolded: what a consumer applies. *)
Corollary carry_clean_fes_priest_nonoverlap :
  forall e f : list binary64,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    nonoverlapping_chain (carry_clean (fast_expansion_sum e f)).
Proof. exact carry_clean_priest_target_proved. Qed.

Print Assumptions carry_clean_priest_target_proved.
Print Assumptions carry_clean_fes_priest_nonoverlap.
