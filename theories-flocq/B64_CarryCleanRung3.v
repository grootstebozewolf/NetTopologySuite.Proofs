(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_CarryCleanRung3
   ----------------------------------------------------------------------------
   Rung 3 of the carry_clean bridge (B64_CarryClean.v): FOUR components in
   total, i.e. three chained TwoSums.

   THE ARGUMENT.  Sort the four components by magnitude, g1 <= .. <= g4, and
   let (Q2, h2) = TwoSum(g2, g1), (Q3, h3) = TwoSum(g3, Q2),
   (Q4, h4) = TwoSum(g4, Q3); the output is [Q4; h4; h3; h2].
     1. Keys (Priest + pigeonhole): any three of the four components contain
        two from one Priest expansion.  On {g1, g2, g3} that gives
        |g1| < ulp(g3); on {g2, g3, g4} it gives |g2| < ulp(g4)
        (`priest_keys4`).
     2. |h2| < 2^c2, and h3 is a multiple of 2^c2 (c2 = min(cexp g3, cexp Q2)),
        as on rung 2.
     3. |Q2| < 2 ulp(g4) (both summands are below ulp(g4)), so
        |h3| < ulp(g4): with B = 2^(mag g4), |g3 + Q2| < B + ulp(g4); below B
        the error is at most half an ulp of g4, from B up the error is at
        most the distance to B (`rn_err_lt_ulp_top`).  Also |h3| < 2^(cexp Q3).
     4. So with c1 = min(cexp g4, max(c2, cexp Q3)): Q4 and h4 are multiples
        of 2^c1, and h3, h2 are below it.  The output is LAYERED: each
        component is a multiple of a power of two that bounds everything
        after it (`layered`), apart from the head pair, which TwoSum
        separates by half an ulp.  A layered list without its zeros is
        strictly decreasing and nonoverlapping, so all blocks are singles.

   PROVED HERE, at total length 4:
     fes_carry_pattern_rung3          part (a): fes_priest_carry_pattern_n 4
     fes_reduction_nonoverlap_rung3   part (b): fes_priest_reduction_nonoverlap_n 4,
                                      for EVERY decomposition (`desc_all_singles`)
     carry_clean_priest_target_rung3  the target for every total <= 4
   The Priest hypothesis enters only through `priest_keys4`; everything
   after it is `fes4_shape_of_keys`, which takes the two key bounds and
   |g3| <= |g4| -- not the full ordering -- as hypotheses.  Overflow margin
   2^(emax-5).

   NOT COVERED.  Five or more components.  In the harness windows
   (tests/CarryCleanExhaustive, TOTAL argument) twins and anti pairs first
   occur at total length 5, so the next rung cannot be all singles: carry
   and cancel do real work there.  Neither key alone suffices in the p-bit
   model: dropping either one admits overlapping outputs
   (tests/CarryCleanExhaustive/keys4_tight.c, results in its header; no
   binary64 witness is pinned).

   NTS / JTS COUNTERPART.  None in-library (JTS/NTS use `CGAlgorithmsDD`,
   double-double); this lane serves the corpus's exact orientation.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; reviewed on PR #987 (2026-10-31).
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra List Permutation.
From Flocq Require Import IEEE754.Binary Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
     B64_Pff_bridge B64_Expansion B64_FastExpansionSum
     B64_FastExpansionSum_Shewchuk B64_Overlap_Hierarchy B64_CarryCleanAlgo
     B64_CarryCleanCore B64_CarryCleanRung2.

Import ListNotations.
Local Open Scope R_scope.

Local Abbreviation b2r := (Binary.B2R prec emax).

(* --------------------------------------------------------------------------
   Order statistics of four components.
   -------------------------------------------------------------------------- *)

Definition ord4 (g1 g2 g3 g4 : binary64) : Prop :=
  b64_abs_le g1 g2 /\ b64_abs_le g2 g3 /\ b64_abs_le g3 g4.

Lemma sort4_ord :
  forall l g1 g2 g3 g4, sort_by_abs l = [g1; g2; g3; g4] -> ord4 g1 g2 g3 g4.
Proof.
  intros l g1 g2 g3 g4 Hs.
  pose proof (sort_by_abs_sorted l) as Hsort. rewrite Hs in Hsort.
  inversion Hsort as [ | | ? ? ? H12 Hs23 ]; subst.
  inversion Hs23 as [ | | ? ? ? H23 Hs34 ]; subst.
  inversion Hs34 as [ | | ? ? ? H34 _ ]; subst.
  unfold ord4, b64_abs_le. auto.
Qed.

Lemma ord4_bounds :
  forall l g1 g2 g3 g4, Permutation l [g1; g2; g3; g4] -> ord4 g1 g2 g3 g4 ->
    forall y, In y l -> b64_abs_le g1 y /\ b64_abs_le y g4.
Proof.
  intros l g1 g2 g3 g4 Hp (H12 & H23 & H34) y Hy.
  assert (Hin : In y [g1; g2; g3; g4]) by (eapply Permutation_in; eassumption).
  unfold b64_abs_le in *.
  destruct Hin as [<- | [<- | [<- | [<- | []]]]]; split; lra.
Qed.

(* Two components at distinct positions: one of them is at least g2, and
   one of them is at most g3. *)
Lemma ord4_two :
  forall l g1 g2 g3 g4 x y rest,
    Permutation l [g1; g2; g3; g4] -> ord4 g1 g2 g3 g4 ->
    Permutation l (x :: y :: rest) ->
    (b64_abs_le g2 x \/ b64_abs_le g2 y) /\ (b64_abs_le x g3 \/ b64_abs_le y g3).
Proof.
  intros l g1 g2 g3 g4 x y rest Hp (H12 & H23 & H34) Hxy.
  assert (Hp' : Permutation (x :: y :: rest) [g1; g2; g3; g4])
    by (eapply Permutation_trans; [ apply Permutation_sym; exact Hxy | exact Hp ]).
  assert (Hx : In x [g1; g2; g3; g4])
    by (eapply Permutation_in; [ exact Hp' | left; reflexivity ]).
  unfold b64_abs_le in *. split.
  - destruct (Rle_or_lt (Rabs (b2r g2)) (Rabs (b2r x))) as [Hle | Hlt];
      [ left; exact Hle | right ].
    (* x is below g2, so it takes the first position *)
    destruct Hx as [<- | [<- | [<- | [<- | []]]]]; try lra.
    apply Permutation_cons_inv in Hp'.
    assert (Hy : In y [g2; g3; g4])
      by (eapply Permutation_in; [ exact Hp' | left; reflexivity ]).
    destruct Hy as [<- | [<- | [<- | []]]]; lra.
  - destruct (Rle_or_lt (Rabs (b2r x)) (Rabs (b2r g3))) as [Hle | Hlt];
      [ left; exact Hle | right ].
    (* x is above g3, so it takes the last position *)
    destruct Hx as [<- | [<- | [<- | [<- | []]]]]; try lra.
    change [g1; g2; g3; g4] with ([g1; g2; g3] ++ g4 :: []) in Hp'.
    apply Permutation_cons_app_inv in Hp'. rewrite app_nil_r in Hp'.
    assert (Hy : In y [g1; g2; g3])
      by (eapply Permutation_in; [ exact Hp' | left; reflexivity ]).
    destruct Hy as [<- | [<- | [<- | []]]]; lra.
Qed.

(* --------------------------------------------------------------------------
   The keys: |g1| < ulp(g3) and |g2| < ulp(g4).
   -------------------------------------------------------------------------- *)

Definition keys4 (g1 g2 g3 g4 : binary64) : Prop :=
  b2r g3 <> 0 /\ b2r g4 <> 0
  /\ Rabs (b2r g1) < ulp radix2 b64_fexp (b2r g3)
  /\ Rabs (b2r g2) < ulp radix2 b64_fexp (b2r g4).

Lemma ulp_mono :
  forall x y : binary64, b64_abs_le x y ->
    ulp radix2 b64_fexp (b2r x) <= ulp radix2 b64_fexp (b2r y).
Proof. intros x y H. exact (ulp_le radix2 b64_fexp (b2r x) (b2r y) H). Qed.

Lemma ulp_le_abs_b64 :
  forall x : binary64, b2r x <> 0 -> ulp radix2 b64_fexp (b2r x) <= Rabs (b2r x).
Proof. intros x Hx. apply b64_ulp_le_abs; [ exact Hx | apply Binary.generic_format_B2R ]. Qed.

Lemma keys_of_perm :
  forall e f g1 g2 g3 g4,
    priest_chain e -> priest_chain f ->
    (length e + length f = 4)%nat -> (length f <= length e)%nat ->
    Permutation (e ++ f) [g1; g2; g3; g4] -> ord4 g1 g2 g3 g4 ->
    keys4 g1 g2 g3 g4.
Proof.
  intros e f g1 g2 g3 g4 He Hf Hlen Hle Hp Hord.
  pose proof (ord4_bounds _ _ _ _ _ Hp Hord) as Hb.
  pose proof Hord as (H12 & H23 & H34).
  unfold keys4, b64_abs_le in *.
  destruct e as [| a1 [| a2 [| a3 [| a4 [| a5 e']]]]];
    destruct f as [| b1 [| b2 [| b3 f']]];
    cbn [length] in Hlen, Hle; try lia; cbn [priest_chain] in He, Hf.
  - (* (2, 2) *)
    destruct He as (P12 & _). destruct Hf as (Q12 & _).
    destruct (priest_pair_lt_ulp _ _ P12) as [A1 U2].
    destruct (priest_pair_lt_ulp _ _ Q12) as [C1 V2].
    destruct (Hb a1 ltac:(cbn; tauto)) as [_ B1].
    destruct (Hb b1 ltac:(cbn; tauto)) as [_ D1].
    destruct (Hb a2 ltac:(cbn; tauto)) as [B2 _].
    destruct (Hb b2 ltac:(cbn; tauto)) as [D2 _].
    pose proof (Rabs_pos_lt _ A1). pose proof (Rabs_pos_lt _ C1).
    pose proof (ulp_mono _ _ B1). pose proof (ulp_mono _ _ D1).
    assert (Pk : Permutation [a1; a2; b1; b2] [a1; b1; a2; b2])
      by (apply perm_skip, perm_swap).
    assert (Pj : Permutation [a1; a2; b1; b2] [a2; b2; a1; b1]).
    { eapply perm_trans; [ apply perm_swap | apply perm_skip ].
      change [a1; b1; b2] with ([a1; b1] ++ [b2]).
      apply Permutation_sym, Permutation_cons_append. }
    destruct (ord4_two _ _ _ _ _ a1 b1 [a2; b2] Hp Hord Pk) as [_ [K | K]];
    destruct (ord4_two _ _ _ _ _ a2 b2 [a1; b1] Hp Hord Pj) as [[J | J] _];
    pose proof (ulp_mono _ _ K); unfold b64_abs_le in *;
    repeat split; try (intro Hz; rewrite Hz, Rabs_R0 in *; lra); lra.
  - (* (3, 1) *)
    destruct He as (P12 & P23 & _).
    destruct (priest_pair_lt_ulp _ _ P12) as [A1 U2].
    destruct (priest_pair_lt_ulp _ _ P23) as [A2 U3].
    pose proof (ulp_le_abs_b64 a2 A2).
    destruct (Hb a1 ltac:(cbn; tauto)) as [_ B1].
    destruct (Hb a2 ltac:(cbn; tauto)) as [B2 _].
    destruct (Hb a3 ltac:(cbn; tauto)) as [B3 _].
    pose proof (Rabs_pos_lt _ A1). pose proof (Rabs_pos_lt _ A2).
    pose proof (ulp_mono _ _ B1).
    destruct (ord4_two _ _ _ _ _ a1 a2 [a3; b1] Hp Hord (Permutation_refl _))
      as [_ [K | K]];
    destruct (ord4_two _ _ _ _ _ a2 a3 [a1; b1] Hp Hord
                (Permutation_middle [a2; a3] [b1] a1)) as [[J | J] _];
    pose proof (ulp_mono _ _ K); unfold b64_abs_le in *;
    repeat split; try (intro Hz; rewrite Hz, Rabs_R0 in *; lra); lra.
  - (* (4, 0) *)
    destruct He as (P12 & P23 & P34 & _).
    destruct (priest_pair_lt_ulp _ _ P12) as [A1 U2].
    destruct (priest_pair_lt_ulp _ _ P23) as [A2 U3].
    destruct (priest_pair_lt_ulp _ _ P34) as [A3 U4].
    pose proof (ulp_le_abs_b64 a2 A2). pose proof (ulp_le_abs_b64 a3 A3).
    destruct (Hb a1 ltac:(cbn; tauto)) as [_ B1].
    destruct (Hb a3 ltac:(cbn; tauto)) as [B3 _].
    destruct (Hb a4 ltac:(cbn; tauto)) as [B4 _].
    pose proof (Rabs_pos_lt _ A1). pose proof (Rabs_pos_lt _ A2).
    pose proof (ulp_mono _ _ B1).
    destruct (ord4_two _ _ _ _ _ a1 a2 [a3; a4] Hp Hord (Permutation_refl _))
      as [_ [K | K]];
    destruct (ord4_two _ _ _ _ _ a3 a4 [a1; a2] Hp Hord
                (Permutation_app_comm [a1; a2] [a3; a4])) as [[J | J] _];
    pose proof (ulp_mono _ _ K); unfold b64_abs_le in *;
    repeat split; try (intro Hz; rewrite Hz, Rabs_R0 in *; lra); lra.
Qed.

Lemma priest_keys4 :
  forall e f g1 g2 g3 g4,
    priest_chain e -> priest_chain f -> (length e + length f = 4)%nat ->
    sort_by_abs (e ++ f) = [g1; g2; g3; g4] -> keys4 g1 g2 g3 g4.
Proof.
  intros e f g1 g2 g3 g4 He Hf Hlen Hs.
  pose proof (sort4_ord _ _ _ _ _ Hs) as Hord.
  assert (Hp : Permutation (e ++ f) [g1; g2; g3; g4])
    by (rewrite <- Hs; apply sort_by_abs_perm).
  destruct (Nat.le_ge_cases (length f) (length e)) as [Hle | Hge].
  - exact (keys_of_perm e f _ _ _ _ He Hf Hlen Hle Hp Hord).
  - apply (keys_of_perm f e _ _ _ _ Hf He); [ lia | lia | | exact Hord ].
    eapply Permutation_trans; [ apply Permutation_app_comm | exact Hp ].
Qed.

(* --------------------------------------------------------------------------
   Layered lists.  Each component is a multiple of a power of two that
   bounds everything after it.  Without its zeros such a list is strictly
   decreasing and nonoverlapping, so its blocks are all singles.
   -------------------------------------------------------------------------- *)

Definition below (c : Z) (y : binary64) : Prop := Rabs (b2r y) < bpow radix2 c.

Fixpoint layered (l : list binary64) : Prop :=
  match l with
  | [] => True
  | x :: rest =>
      (exists c, pow2_multiple c (b2r x) /\ Forall (below c) rest) /\ layered rest
  end.

Lemma Forall_filter_sub :
  forall (P : binary64 -> Prop) (q : binary64 -> bool) l,
    Forall P l -> Forall P (filter q l).
Proof.
  intros P q l H. apply Forall_forall. intros y Hy.
  apply filter_In in Hy. destruct Hy as [Hy _].
  rewrite Forall_forall in H. exact (H y Hy).
Qed.

Lemma layered_filter :
  forall q l, layered l -> layered (filter q l).
Proof.
  intros q. induction l as [| x l IH]; intro H; [ exact I | ].
  destruct H as [[c [Hm Hb]] Hl]. cbn [filter].
  destruct (q x); [ | exact (IH Hl) ].
  split; [ exists c; split; [ exact Hm | apply Forall_filter_sub, Hb ] | exact (IH Hl) ].
Qed.

Lemma layered_desc :
  forall l, layered l -> Forall b64_nz l -> strict_desc l /\ nonoverlapping_chain l.
Proof.
  induction l as [| x l IH]; intros Hl Hnz; [ split; exact I | ].
  destruct Hl as [[c [[n Hn] Hb]] Hl].
  inversion Hnz as [| ? ? [_ Hx0] Hnz']; subst.
  destruct (IH Hl Hnz') as [Hd Hc].
  destruct l as [| y l']; [ split; exact I | ].
  inversion Hb as [| ? ? Hy _]; subst. unfold below in Hy.
  pose proof (scaled_nonzero_ge _ n c Hn Hx0).
  split; [ split; [ lra | exact Hd ] | ].
  split; [ exact (nonov_scaled _ _ n c Hn Hy) | exact Hc ].
Qed.

Lemma drop_zeros_nz :
  forall l, Forall b64_fin l -> Forall b64_nz (drop_zeros l).
Proof.
  intros l H. apply Forall_forall. intros y Hy.
  unfold drop_zeros in Hy. apply filter_In in Hy. destruct Hy as [Hy Hz].
  rewrite Forall_forall in H. apply b64_nz_of_not_zero; [ exact (H y Hy) | ].
  destruct (b64_is_zero y); [ discriminate | reflexivity ].
Qed.

Lemma expand_singles : forall l, flat_map cblock_expand (map CSingle l) = l.
Proof. induction l as [| x l IH]; [ reflexivity | cbn; rewrite IH; reflexivity ]. Qed.

Lemma reduce_singles : forall l, flat_map cblock_reduce (map CSingle l) = l.
Proof. induction l as [| x l IH]; [ reflexivity | cbn; rewrite IH; reflexivity ]. Qed.

Lemma keys_singles : forall l, strict_desc l -> keys_decreasing (map CSingle l).
Proof.
  induction l as [| x [| y l] IH]; intro H; [ exact I | exact (conj I I) | ].
  destruct H as [Hlt Hd]. split; [ exact Hlt | exact (IH Hd) ].
Qed.

(* The shape, all singles, for a list whose nonzero part is layered. *)
Lemma singles_shape_of_layered :
  forall l, Forall b64_fin l -> layered (drop_zeros l) ->
    exists bs, drop_zeros l = flat_map cblock_expand bs /\ carry_shape bs
               /\ Forall is_single bs.
Proof.
  intros l Hf Hl.
  pose proof (drop_zeros_nz l Hf) as Hnz.
  destruct (layered_desc _ Hl Hnz) as [Hd Hc].
  exists (map CSingle (drop_zeros l)).
  split; [ symmetry; apply expand_singles | ].
  split; [ split; [ | split ] | ].
  - apply Forall_map. exact Hnz.
  - apply keys_singles, Hd.
  - rewrite reduce_singles. exact Hc.
  - apply Forall_map, Forall_forall. intros; exact I.
Qed.

(* A TwoSum head pair (a, b), both multiples of 2^c, over a layered rest
   below 2^c. *)
Lemma head_pair_layered :
  forall (a b : binary64) rest (c : Z),
    b64_fin a -> b64_fin b ->
    strict_succ_b64 a b ->
    pow2_multiple c (b2r a) -> pow2_multiple c (b2r b) ->
    Forall (below c) rest -> layered rest ->
    layered (drop_zeros (a :: b :: rest)).
Proof.
  intros a b rest c Ha Hb Hab Ma [nb Hnb] Hr Hl.
  unfold strict_succ_b64 in Hab.
  assert (Hlf : layered (drop_zeros rest)) by (apply layered_filter, Hl).
  assert (Hrf : Forall (below c) (drop_zeros rest)) by (apply Forall_filter_sub, Hr).
  destruct (b64_fin_zero_or_nz a Ha) as [[Hza Ha0] | [Hza [_ Ha0]]];
  destruct (b64_fin_zero_or_nz b Hb) as [[Hzb Hb0] | [Hzb [_ Hb0]]];
  unfold drop_zeros in *; cbn [filter]; rewrite Hza, Hzb; cbn [negb].
  - exact Hlf.
  - (* a = 0 forces b = 0 *)
    exfalso. apply Hb0. apply binary64_below_emin_is_zero. rewrite Ha0 in Hab.
    change (ulp radix2 (SpecFloat.fexp prec emax) 0) with (b64_ulp 0) in Hab.
    rewrite b64_ulp_FLT_0 in Hab.
    pose proof (bpow_gt_0 radix2 (3 - emax - prec)). lra.
  - split; [ exists c; split; assumption | exact Hlf ].
  - (* a is a multiple of 2^(cexp a); b and the rest are below it *)
    assert (Hge : bpow radix2 c <= Rabs (b2r b)) by (apply (scaled_nonzero_ge _ nb c Hnb Hb0)).
    rewrite ulp_neq_0 in Hab by exact Ha0.
    set (ca := cexp radix2 b64_fexp (b2r a)) in Hab.
    pose proof (bpow_gt_0 radix2 ca).
    split; [ | split; [ exists c; split; [ exists nb; exact Hnb | exact Hrf ] | exact Hlf ] ].
    exists ca. split; [ apply b64_pow2_multiple_cexp | ].
    constructor; [ unfold below; lra | ].
    eapply Forall_impl; [ | exact Hrf ]. unfold below. intros y Hy. lra.
Qed.

(* --------------------------------------------------------------------------
   The rounding error near the top component.
   -------------------------------------------------------------------------- *)

Lemma fexp_succ_le :
  forall k, (b64_fexp k < k)%Z -> (b64_fexp (k + 1) <= k)%Z.
Proof. intros k H. unfold SpecFloat.fexp in *. unfold prec in *. lia. Qed.

(* Two summands below ulp(g) round below 2 ulp(g). *)
Lemma rn_sum_lt_two_ulp :
  forall (g x y : binary64),
    b2r g <> 0 ->
    Rabs (b2r x) < ulp radix2 b64_fexp (b2r g) ->
    Rabs (b2r y) < ulp radix2 b64_fexp (b2r g) ->
    Rabs (round radix2 b64_fexp (BinarySingleNaN.round_mode mode_b64) (b2r x + b2r y))
      < 2 * ulp radix2 b64_fexp (b2r g).
Proof.
  intros g x y Hg0 Hx Hy.
  rewrite ulp_neq_0 in * by exact Hg0.
  set (e := cexp radix2 b64_fexp (b2r g)) in *.
  assert (He : (b64_fexp e <= e)%Z).
  { unfold e, cexp. unfold SpecFloat.fexp. unfold prec. lia. }
  assert (Fe : generic_format radix2 b64_fexp (bpow radix2 e))
    by (apply generic_format_bpow; unfold SpecFloat.fexp in *; unfold prec in *; lia).
  assert (Fe1 : generic_format radix2 b64_fexp (bpow radix2 (e + 1)))
    by (apply generic_format_bpow; unfold SpecFloat.fexp in *; unfold prec in *; lia).
  (* each summand is at most pred(2^e) = 2^e - 2^(fexp e) *)
  assert (Px : Rabs (b2r x) <= bpow radix2 e - bpow radix2 (b64_fexp e)).
  { rewrite <- pred_bpow.
    exact (pred_ge_gt radix2 b64_fexp _ _
             (generic_format_abs _ _ _ (Binary.generic_format_B2R prec emax x)) Fe Hx). }
  assert (Py : Rabs (b2r y) <= bpow radix2 e - bpow radix2 (b64_fexp e)).
  { rewrite <- pred_bpow.
    exact (pred_ge_gt radix2 b64_fexp _ _
             (generic_format_abs _ _ _ (Binary.generic_format_B2R prec emax y)) Fe Hy). }
  (* and 2 pred(2^e) <= pred(2^(e+1)), a format number below 2^(e+1) *)
  assert (Hf1 : bpow radix2 (b64_fexp (e + 1)) <= 2 * bpow radix2 (b64_fexp e)).
  { change 2 with (bpow radix2 1). rewrite <- bpow_plus. apply bpow_le.
    unfold SpecFloat.fexp. unfold prec. lia. }
  assert (H2 : bpow radix2 (e + 1) = 2 * bpow radix2 e)
    by (rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
  assert (Hle : Rabs (b2r x + b2r y) <= pred radix2 b64_fexp (bpow radix2 (e + 1))).
  { rewrite pred_bpow. pose proof (Rabs_triang (b2r x) (b2r y)). lra. }
  pose proof (abs_round_le_generic radix2 b64_fexp
                (BinarySingleNaN.round_mode mode_b64) _ _
                (generic_format_pred radix2 b64_fexp _ Fe1) Hle) as Hr.
  rewrite pred_bpow in Hr.
  pose proof (bpow_gt_0 radix2 (b64_fexp (e + 1))). lra.
Qed.

(* x below g in magnitude, y below 2 ulp(g): the error of RN(x + y) is
   below ulp(g). *)
Lemma rn_err_lt_ulp_top :
  forall (g : binary64) (x y : R),
    b2r g <> 0 -> Rabs x <= Rabs (b2r g) ->
    Rabs y < 2 * ulp radix2 b64_fexp (b2r g) ->
    Rabs (round radix2 b64_fexp (BinarySingleNaN.round_mode mode_b64) (x + y) - (x + y))
      < ulp radix2 b64_fexp (b2r g).
Proof.
  intros g x y Hg0 Hx Hy.
  change (BinarySingleNaN.round_mode mode_b64) with (Znearest (fun z => negb (Z.even z))).
  rewrite ulp_neq_0 in * by exact Hg0.
  set (M := mag radix2 (b2r g)).
  assert (Hce : cexp radix2 b64_fexp (b2r g) = b64_fexp M) by reflexivity.
  rewrite Hce in *.
  set (u := bpow radix2 (b64_fexp M)) in *.
  assert (Hu : 0 < u) by apply bpow_gt_0.
  pose proof (mag_generic_gt radix2 b64_fexp (b2r g) Hg0 (Binary.generic_format_B2R prec emax g))
    as Hgt. rewrite Hce in Hgt. fold M in Hgt.
  assert (FB : generic_format radix2 b64_fexp (bpow radix2 M))
    by (apply generic_format_bpow, fexp_succ_le, Hgt).
  (* |g| <= 2^M - u *)
  assert (Hg : Rabs (b2r g) <= bpow radix2 M - u).
  { unfold u. rewrite <- pred_bpow.
    exact (pred_ge_gt radix2 b64_fexp _ _
             (generic_format_abs _ _ _ (Binary.generic_format_B2R prec emax g)) FB
             (bpow_mag_gt radix2 (b2r g))). }
  set (z := x + y).
  assert (Hz : Rabs z < bpow radix2 M + u)
    by (unfold z; pose proof (Rabs_triang x y); lra).
  destruct (Rlt_or_le (Rabs z) (bpow radix2 M)) as [Hlo | Hhi].
  - (* below 2^M: half an ulp of z, and ulp(z) <= u *)
    destruct (Req_dec z 0) as [Hz0 | Hz0].
    + rewrite Hz0, round_0 by apply valid_rnd_N. rewrite Rminus_0_r, Rabs_R0. exact Hu.
    + pose proof (error_le_half_ulp radix2 b64_fexp (fun z => negb (Z.even z)) z) as He.
      rewrite ulp_neq_0 in He by exact Hz0.
      assert (Hc : (cexp radix2 b64_fexp z <= b64_fexp M)%Z)
        by exact (cexp_le_bpow radix2 b64_fexp z M Hz0 Hlo).
      assert (bpow radix2 (cexp radix2 b64_fexp z) <= u) by (apply bpow_le, Hc).
      lra.
  - (* from 2^M up: at most the distance to +-2^M *)
    destruct (round_N_pt radix2 b64_fexp (fun z => negb (Z.even z)) z) as [_ Hmin].
    destruct (Rle_or_lt 0 z) as [Hzp | Hzn].
    + specialize (Hmin _ FB).
      rewrite Rabs_pos_eq in Hhi, Hz by exact Hzp.
      assert (Hd : Rabs (bpow radix2 M - z) < u)
        by (rewrite Rabs_minus_sym, Rabs_pos_eq by lra; lra).
      lra.
    + specialize (Hmin _ (generic_format_opp _ _ _ FB)).
      rewrite Rabs_left in Hhi, Hz by exact Hzn.
      assert (Hd : Rabs (- bpow radix2 M - z) < u)
        by (rewrite Rabs_pos_eq by lra; lra).
      lra.
Qed.

(* --------------------------------------------------------------------------
   Three chained TwoSums, given the keys.  No Priest hypothesis here, and
   no full ordering either: only |g3| <= |g4| and the two keys (`keys4`).
   The ordering of g1, g2 among themselves and below g3 is not used, which
   leaves a later rung less to establish before reusing it.
   -------------------------------------------------------------------------- *)

Definition fes4 (g1 g2 g3 g4 : binary64) : list binary64 :=
  let '(hs, q) := b64_grow_expansion_aux g1 [g2; g3; g4] in q :: rev hs.

(* |h| <= ulp(Q)/2 puts h below 2^(cexp Q), also when Q = 0 (then h = 0). *)
Lemma half_ulp_below :
  forall (Q h : binary64),
    Rabs (b2r h) <= ulp radix2 b64_fexp (b2r Q) / 2 ->
    Rabs (b2r h) < bpow radix2 (cexp radix2 b64_fexp (b2r Q)).
Proof.
  intros Q h H.
  destruct (Req_dec (b2r Q) 0) as [HQ0 | HQ0].
  - assert (Hh0 : b2r h = 0).
    { apply binary64_below_emin_is_zero. rewrite HQ0 in H.
      change (ulp radix2 (SpecFloat.fexp prec emax) 0) with (b64_ulp 0) in H.
      rewrite b64_ulp_FLT_0 in H.
      pose proof (bpow_gt_0 radix2 (3 - emax - prec)). lra. }
    rewrite Hh0, Rabs_R0. apply bpow_gt_0.
  - rewrite ulp_neq_0 in H by exact HQ0.
    pose proof (bpow_gt_0 radix2 (cexp radix2 b64_fexp (b2r Q))). lra.
Qed.

Lemma fes4_shape_of_keys :
  forall g1 g2 g3 g4 : binary64,
    b64_fin g1 -> b64_fin g2 -> b64_fin g3 -> b64_fin g4 ->
    cascade_safe g1 [g2; g3; g4] ->
    b64_abs_le g3 g4 -> keys4 g1 g2 g3 g4 ->
    exists bs, drop_zeros (fes4 g1 g2 g3 g4) = flat_map cblock_expand bs
               /\ carry_shape bs /\ Forall is_single bs.
Proof.
  intros g1 g2 g3 g4 F1 F2 F3 F4 Hsafe H34 (Hg30 & Hg40 & K1 & K2).
  cbn [cascade_safe] in Hsafe. destruct Hsafe as [S12 [S3 [S4 _]]].
  change (fst (b64_TwoSum g2 g1)) with (b64_plus g2 g1) in S3, S4.
  unfold fes4. cbn [b64_grow_expansion_aux].
  (* first TwoSum: (Q2, h2) = TwoSum(g2, g1) *)
  pose proof S12 as (A1 & A2 & A3 & A4 & A5 & A6).
  pose proof (b64_TwoSum_correct g2 g1 A1 A2 A3 A4 A5 A6) as Hex2.
  pose proof (b64_TwoSum_nonoverlap g2 g1 A1 A2 A3 A4 A5 A6) as Hno2.
  destruct (b64_plus_correct g2 g1 A1) as [RQ2 FQ2].
  destruct (b64_plus_correct _ _ A6) as [_ Fh2].
  destruct (b64_TwoSum g2 g1) as [Q2 h2] eqn:E2.
  cbv iota beta in Hex2, Hno2.
  unfold b64_TwoSum in E2. injection E2 as EQ2 Eh2.
  rewrite EQ2 in RQ2, FQ2, S3, S4. rewrite Eh2 in Fh2.
  change (fst (b64_TwoSum g3 Q2)) with (b64_plus g3 Q2) in S4.
  (* second TwoSum: (Q3, h3) = TwoSum(g3, Q2) *)
  pose proof S3 as (B1 & B2 & B3 & B4 & B5 & B6).
  pose proof (b64_TwoSum_correct g3 Q2 B1 B2 B3 B4 B5 B6) as Hex3.
  pose proof (b64_TwoSum_nonoverlap g3 Q2 B1 B2 B3 B4 B5 B6) as Hno3.
  destruct (b64_plus_correct g3 Q2 B1) as [RQ3 FQ3].
  destruct (b64_plus_correct _ _ B6) as [_ Fh3].
  destruct (b64_TwoSum g3 Q2) as [Q3 h3] eqn:E3.
  cbv iota beta in Hex3, Hno3.
  unfold b64_TwoSum in E3. injection E3 as EQ3 Eh3.
  rewrite EQ3 in RQ3, FQ3, S4. rewrite Eh3 in Fh3.
  (* third TwoSum: (Q4, h4) = TwoSum(g4, Q3) *)
  pose proof S4 as (C1 & C2 & C3 & C4 & C5 & C6).
  pose proof (b64_TwoSum_correct g4 Q3 C1 C2 C3 C4 C5 C6) as Hex4.
  pose proof (b64_TwoSum_nonoverlap g4 Q3 C1 C2 C3 C4 C5 C6) as Hno4.
  destruct (b64_plus_correct g4 Q3 C1) as [RQ4 FQ4].
  destruct (b64_plus_correct _ _ C6) as [_ Fh4].
  destruct (b64_TwoSum g4 Q3) as [Q4 h4] eqn:E4.
  cbv iota beta in Hex4, Hno4.
  unfold b64_TwoSum in E4. injection E4 as EQ4 Eh4.
  rewrite EQ4 in RQ4, FQ4. rewrite Eh4 in Fh4.
  cbn [rev app].
  unfold strict_succ_b64 in Hno2, Hno3.
  (* layer 2: c2 = min(cexp g3, cexp Q2), as on rung 2 *)
  set (c2 := Z.min (cexp radix2 b64_fexp (b2r g3)) (cexp radix2 b64_fexp (b2r Q2))).
  assert (Mg3 : pow2_multiple c2 (b2r g3))
    by (apply (pow2_multiple_le _ _ _ (Z.le_min_l _ _)), b64_pow2_multiple_cexp).
  assert (MQ2 : pow2_multiple c2 (b2r Q2))
    by (apply (pow2_multiple_le _ _ _ (Z.le_min_r _ _)), b64_pow2_multiple_cexp).
  assert (MQ3 : pow2_multiple c2 (b2r Q3))
    by (rewrite RQ3; apply round_pow2_multiple, pow2_multiple_plus; assumption).
  assert (Mh3 : pow2_multiple c2 (b2r h3)).
  { replace (b2r h3) with ((b2r g3 + b2r Q2) - b2r Q3) by lra.
    apply pow2_multiple_minus; [ apply pow2_multiple_plus | ]; assumption. }
  assert (Hh2g1 : Rabs (b2r h2) <= Rabs (b2r g1)).
  { replace (b2r h2)
      with (- (round radix2 b64_fexp (BinarySingleNaN.round_mode mode_b64) (b2r g2 + b2r g1)
               - (b2r g2 + b2r g1)))
      by (rewrite <- RQ2; lra).
    rewrite Rabs_Ropp. apply round_N_err_le_operand, Binary.generic_format_B2R. }
  assert (Hh2Q2 := half_ulp_below Q2 h2 Hno2).
  rewrite ulp_neq_0 in K1 by exact Hg30.
  rewrite ulp_neq_0 in K2 by exact Hg40.
  assert (Hh2c2 : Rabs (b2r h2) < bpow radix2 c2).
  { unfold c2. destruct (Z.min_spec (cexp radix2 b64_fexp (b2r g3))
                                    (cexp radix2 b64_fexp (b2r Q2))) as [[_ Hm] | [_ Hm]];
      rewrite Hm; lra. }
  (* layer 1: c1 = min(cexp g4, L3), L3 = max(c2, cexp Q3) *)
  set (L3 := Z.max c2 (cexp radix2 b64_fexp (b2r Q3))).
  assert (MQ3L : pow2_multiple L3 (b2r Q3)).
  { unfold L3. destruct (Z.max_spec c2 (cexp radix2 b64_fexp (b2r Q3))) as [[_ Hm] | [_ Hm]];
      rewrite Hm; [ apply b64_pow2_multiple_cexp | exact MQ3 ]. }
  set (c1 := Z.min (cexp radix2 b64_fexp (b2r g4)) L3).
  assert (Mg4 : pow2_multiple c1 (b2r g4))
    by (apply (pow2_multiple_le _ _ _ (Z.le_min_l _ _)), b64_pow2_multiple_cexp).
  assert (MQ3c1 : pow2_multiple c1 (b2r Q3))
    by (apply (pow2_multiple_le _ _ _ (Z.le_min_r _ _)), MQ3L).
  assert (MQ4 : pow2_multiple c1 (b2r Q4))
    by (rewrite RQ4; apply round_pow2_multiple, pow2_multiple_plus; assumption).
  assert (Mh4 : pow2_multiple c1 (b2r h4)).
  { replace (b2r h4) with ((b2r g4 + b2r Q3) - b2r Q4) by lra.
    apply pow2_multiple_minus; [ apply pow2_multiple_plus | ]; assumption. }
  (* h3 below 2^c1: below ulp(Q3), and below ulp(g4) by `rn_err_lt_ulp_top` *)
  assert (HQ2 : Rabs (b2r Q2) < 2 * ulp radix2 b64_fexp (b2r g4)).
  { rewrite RQ2. apply rn_sum_lt_two_ulp; [ exact Hg40 | | ];
      rewrite ulp_neq_0 by exact Hg40; [ exact K2 | ].
    pose proof (ulp_mono _ _ H34) as U34.
    rewrite ulp_neq_0 in U34 by exact Hg30. rewrite ulp_neq_0 in U34 by exact Hg40. lra. }
  assert (Hh3g4 : Rabs (b2r h3) < bpow radix2 (cexp radix2 b64_fexp (b2r g4))).
  { replace (b2r h3)
      with (- (round radix2 b64_fexp (BinarySingleNaN.round_mode mode_b64) (b2r g3 + b2r Q2)
               - (b2r g3 + b2r Q2)))
      by (rewrite <- RQ3; lra).
    rewrite Rabs_Ropp, <- ulp_neq_0 by exact Hg40.
    apply rn_err_lt_ulp_top; [ exact Hg40 | exact H34 | exact HQ2 ]. }
  assert (Hh3Q3 := half_ulp_below Q3 h3 Hno3).
  assert (Hh3c1 : below c1 h3).
  { unfold below, c1, L3.
    destruct (Z.min_spec (cexp radix2 b64_fexp (b2r g4))
                         (Z.max c2 (cexp radix2 b64_fexp (b2r Q3)))) as [[_ Hm] | [_ Hm]];
      rewrite Hm; [ exact Hh3g4 | ].
    apply Rlt_le_trans with (1 := Hh3Q3). apply bpow_le, Z.le_max_r. }
  assert (Hh2c1 : below c1 h2).
  { pose proof (ulp_mono _ _ H34) as U34.
    rewrite ulp_neq_0 in U34 by exact Hg30. rewrite ulp_neq_0 in U34 by exact Hg40.
    unfold below, c1, L3.
    destruct (Z.min_spec (cexp radix2 b64_fexp (b2r g4))
                         (Z.max c2 (cexp radix2 b64_fexp (b2r Q3)))) as [[_ Hm] | [_ Hm]];
      rewrite Hm; [ lra | ].
    apply Rlt_le_trans with (1 := Hh2c2). apply bpow_le, Z.le_max_l. }
  (* the output is layered *)
  apply singles_shape_of_layered.
  { repeat (apply Forall_cons; [ assumption | ]). apply Forall_nil. }
  apply (head_pair_layered Q4 h4 [h3; h2] c1 FQ4 Fh4 Hno4 MQ4 Mh4).
  - repeat (apply Forall_cons; [ assumption | ]). apply Forall_nil.
  - split; [ exists c2; split; [ exact Mh3 | ] | ].
    + apply Forall_cons; [ exact Hh2c2 | apply Forall_nil ].
    + split; [ exists (cexp radix2 b64_fexp (b2r h2));
               split; [ apply b64_pow2_multiple_cexp | apply Forall_nil ] | exact I ].
Qed.

(* --------------------------------------------------------------------------
   RUNG 3.
   -------------------------------------------------------------------------- *)

Lemma fes_rung3_singles :
  forall e f : list binary64,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    (length e + length f = 4)%nat ->
    exists bs, drop_zeros (fast_expansion_sum e f) = flat_map cblock_expand bs
               /\ carry_shape bs /\ Forall is_single bs.
Proof.
  intros e f He Hf Hef Hff Hov Hlen.
  pose proof (fes_cascade_safe e f Hef Hff Hov) as Hsafe.
  assert (Hfin : Forall b64_fin (sort_by_abs (e ++ f)))
    by (apply sort_by_abs_Forall, Forall_app; split; assumption).
  assert (Hl4 : length (sort_by_abs (e ++ f)) = 4%nat)
    by (rewrite sort_by_abs_length, length_app; exact Hlen).
  destruct (sort_by_abs (e ++ f)) as [| g1 [| g2 [| g3 [| g4 [| g5 rest]]]]] eqn:Hs;
    cbn [length] in Hl4; try lia.
  pose proof (priest_keys4 e f g1 g2 g3 g4 He Hf Hlen Hs) as Hkeys.
  pose proof (sort4_ord _ _ _ _ _ Hs) as (_ & _ & H34).
  inversion Hfin as [| ? ? F1 Hfin2]; subst.
  inversion Hfin2 as [| ? ? F2 Hfin3]; subst.
  inversion Hfin3 as [| ? ? F3 Hfin4]; subst.
  inversion Hfin4 as [| ? ? F4 _]; subst.
  unfold fast_expansion_sum. rewrite Hs.
  exact (fes4_shape_of_keys g1 g2 g3 g4 F1 F2 F3 F4 Hsafe H34 Hkeys).
Qed.

(* The shape for the exhibited decomposition (what the target consumes). *)
Theorem fes_carry_bridge_rung3 :
  forall e f : list binary64,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    (length e + length f = 4)%nat ->
    exists bs, drop_zeros (fast_expansion_sum e f) = flat_map cblock_expand bs
               /\ carry_shape bs.
Proof.
  intros e f He Hf Hef Hff Hov Hlen.
  destruct (fes_rung3_singles e f He Hf Hef Hff Hov Hlen) as [bs [Hl [Hs _]]].
  exists bs. split; assumption.
Qed.

(* Bridge part (a) at total length 4. *)
Theorem fes_carry_pattern_rung3 : fes_priest_carry_pattern_n 4.
Proof.
  intros e f He Hf Hef Hff Hov Hlen.
  destruct (fes_rung3_singles e f He Hf Hef Hff Hov Hlen) as [bs [Hl [[Hok [Hdec _]] _]]].
  exists bs. split; [ exact Hl | split; assumption ].
Qed.

(* Bridge part (b) at total length 4, for EVERY decomposition. *)
Theorem fes_reduction_nonoverlap_rung3 : fes_priest_reduction_nonoverlap_n 4.
Proof.
  intros e f He Hf Hef Hff Hov Hlen bs Hl _.
  destruct (fes_rung3_singles e f He Hf Hef Hff Hov Hlen)
    as [bs0 [Hl0 [[Hok0 [Hdec0 Hno0]] Hsg0]]].
  assert (Hdesc : strict_desc (flat_map cblock_expand bs)).
  { rewrite <- Hl, Hl0. apply singles_strict_desc; assumption. }
  rewrite (desc_all_singles bs Hdesc), <- Hl, Hl0, <- (singles_reduce bs0 Hsg0).
  exact Hno0.
Qed.

(* The target on rung 3, and on all of rungs 1-3 together. *)
Corollary carry_clean_priest_target_rung3 :
  forall e f : list binary64,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    (length e + length f <= 4)%nat ->
    nonoverlapping_chain (carry_clean (fast_expansion_sum e f)).
Proof.
  intros e f He Hf Hef Hff Hov Hlen.
  destruct (Nat.eq_dec (length e + length f) 4) as [H4 | H4].
  - destruct (fes_carry_bridge_rung3 e f He Hf Hef Hff Hov H4) as [bs [Hl Hs]].
    apply (carry_clean_nonoverlap_of_shape _ bs Hl Hs).
  - apply carry_clean_priest_target_rung2; [ assumption .. | lia ].
Qed.

Print Assumptions ord4_two.
Print Assumptions priest_keys4.
Print Assumptions layered_desc.
Print Assumptions head_pair_layered.
Print Assumptions rn_sum_lt_two_ulp.
Print Assumptions rn_err_lt_ulp_top.
Print Assumptions fes4_shape_of_keys.
Print Assumptions fes_carry_pattern_rung3.
Print Assumptions fes_reduction_nonoverlap_rung3.
Print Assumptions carry_clean_priest_target_rung3.
