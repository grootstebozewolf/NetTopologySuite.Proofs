(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_CarryCleanSign
   ----------------------------------------------------------------------------
   carry_clean (fast_expansion_sum e f) on Priest input is sign-ready: it is
   a nonoverlapping chain (carry_clean_priest_target_proved), its components
   are nonzero with strictly decreasing magnitudes, and it sums exactly to
   expansion_R e + expansion_R f.  Hence its leading component gives the sign
   of the exact sum (B64_NonoverlapSign.nonoverlapping_chain_sign_correct).

   WHY THE ORDER IS PROVED HERE.  nonoverlapping_chain alone does not fix
   the sign (QEX [-4; 1; 8], B64_NonoverlapSign.v).  The order is not a new
   assumption: fes_shape_all (B64_CarryCleanTarget.v) already gives the block
   decomposition with strictly decreasing keys (keys_decreasing), and
   carry_clean_priest_core gives carry_clean's output as the block reduction
   (anti pairs deleted, twins doubled exactly).  Each surviving block reduces
   to ONE component whose magnitude is its key, so the output is strictly
   decreasing.

   ALSO DISCHARGED: fast_expansion_sum_safe follows from the same overflow
   margin abs_sum e + abs_sum f <= 2^(emax-5) (fes_cascade_safe: the cascade
   safety is the same Fixpoint up to b64_TwoSum_fst), so the exact-sum
   statement needs no separate safety hypothesis.

   topic: binary64
   claimId: carry-clean-sign
   witness: carry_clean_fes_priest_sign_correct

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human-reviewed (2026-11-10, J. Bloemscheer, PR #1017 @ 16a1b47).
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra List.
From Flocq Require Import IEEE754.Binary Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_lib B64_Pff_bridge
     B64_Expansion B64_FastExpansionSum B64_FastExpansionSum_Shewchuk
     B64_Overlap_Hierarchy B64_CarryCleanAlgo B64_CarryCleanCore
     B64_CarryCleanTarget B64_NonoverlapSign.

Import ListNotations.
Local Open Scope R_scope.
Local Abbreviation b2r := (Binary.B2R prec emax).

(* --------------------------------------------------------------------------
   fast_expansion_sum_safe from the overflow margin.
   -------------------------------------------------------------------------- *)

Lemma cascade_safe_grow_safe :
  forall es q, cascade_safe q es -> b64_grow_expansion_aux_safe q es.
Proof.
  induction es as [| x es IH]; intros q H; [ exact I | ].
  destruct H as [H1 H2]. split; [ exact H1 | ].
  rewrite <- b64_TwoSum_fst. exact (IH _ H2).
Qed.

Theorem fes_safe_of_overflow :
  forall e f : list binary64,
    Forall b64_fin e -> Forall b64_fin f ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    fast_expansion_sum_safe e f.
Proof.
  intros e f Fe Ff Hov.
  pose proof (fes_cascade_safe e f Fe Ff Hov) as C.
  unfold fast_expansion_sum_safe.
  destruct (sort_by_abs (e ++ f)) as [| x xs]; [ exact I | ].
  exact (cascade_safe_grow_safe xs x C).
Qed.

(* --------------------------------------------------------------------------
   The block reduction is in strictly decreasing magnitude order.
   -------------------------------------------------------------------------- *)

(* keys_decreasing is transitive along the list. *)
Lemma keys_decreasing_all :
  forall bs b, keys_decreasing (b :: bs) ->
    forall b', In b' bs -> block_key b' < block_key b.
Proof.
  induction bs as [| c bs IH]; intros b Hd b' Hin; [ destruct Hin | ].
  cbn [keys_decreasing] in Hd. destruct Hd as [Hcb Hd].
  destruct Hin as [<- | Hin]; [ exact Hcb | ].
  pose proof (IH c Hd b' Hin). lra.
Qed.

(* Every component of the reduction has the magnitude of its block's key. *)
Lemma reduce_in_key :
  forall bs y, Forall block_ok bs -> In y (flat_map cblock_reduce bs) ->
    exists b, In b bs /\ Rabs (b2r y) = block_key b /\ b2r y <> 0.
Proof.
  induction bs as [| b bs IH]; intros y Hok Hin; [ destruct Hin | ].
  inversion Hok as [| ? ? Hb Hbs]; subst.
  cbn [flat_map] in Hin. apply in_app_or in Hin as [Hin | Hin].
  - exists b. split; [ left; reflexivity | ].
    destruct b as [u | x | x]; cbn [cblock_reduce block_key block_ok] in Hin, Hb |- *.
    + destruct Hin as [<- | []]. split; [ reflexivity | exact (proj2 Hb) ].
    + destruct Hin as [<- | []]. destruct Hb as [[Hxf Hx0] Hov].
      destruct (double_exact x Hxf Hov) as [HdR _]. rewrite HdR.
      split; [ rewrite Rabs_mult, (Rabs_pos_eq 2) by lra; reflexivity | ].
      intro H. apply Hx0. lra.
    + destruct Hin.
  - destruct (IH y Hbs Hin) as (b' & Hb' & Hk & Hy). exists b'.
    split; [ right; exact Hb' | split; assumption ].
Qed.

Lemma mag_desc_cons_le :
  forall v l, mag_desc l -> (forall w, In w l -> Rabs (b2r w) <= Rabs (b2r v)) ->
    mag_desc (v :: l).
Proof.
  intros v [| w l] Hl Hle; [ exact I | ].
  split; [ apply Hle; left; reflexivity | exact Hl ].
Qed.

Theorem reduce_mag_desc :
  forall bs, Forall block_ok bs -> keys_decreasing bs ->
    mag_desc (flat_map cblock_reduce bs).
Proof.
  induction bs as [| b bs IH]; intros Hok Hd; [ exact I | ].
  inversion Hok as [| ? ? Hb Hbs]; subst.
  pose proof (IH Hbs (proj2 Hd)) as Hrest.
  pose proof (keys_decreasing_all bs b Hd) as Hall.
  cbn [flat_map].
  destruct b as [u | x | x]; cbn [cblock_reduce app]; [ | | exact Hrest ].
  - apply mag_desc_cons_le; [ exact Hrest | ].
    intros w Hw. destruct (reduce_in_key bs w Hbs Hw) as (b' & Hb' & Hk & _).
    pose proof (Hall b' Hb') as Hlt. cbn [block_key] in Hlt. lra.
  - apply mag_desc_cons_le; [ exact Hrest | ].
    destruct Hb as [[Hxf Hx0] Hov].
    destruct (double_exact x Hxf Hov) as [HdR _].
    intros w Hw. destruct (reduce_in_key bs w Hbs Hw) as (b' & Hb' & Hk & _).
    pose proof (Hall b' Hb') as Hlt. cbn [block_key] in Hlt.
    rewrite HdR, Rabs_mult, (Rabs_pos_eq 2) by lra. lra.
Qed.

Lemma reduce_nonzero :
  forall bs, Forall block_ok bs ->
    Forall (fun y => b2r y <> 0) (flat_map cblock_reduce bs).
Proof.
  intros bs Hok. apply Forall_forall. intros y Hy.
  destruct (reduce_in_key bs y Hok Hy) as (_ & _ & _ & H). exact H.
Qed.

(* --------------------------------------------------------------------------
   carry_clean (fast_expansion_sum e f) on Priest input: sign-ready.
   -------------------------------------------------------------------------- *)

Theorem carry_clean_fes_priest_ordered :
  forall e f : list binary64,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    let c := carry_clean (fast_expansion_sum e f) in
    nonoverlapping_chain c /\ mag_desc c
    /\ Forall (fun y => b2r y <> 0) c
    /\ expansion_R c = expansion_R e + expansion_R f.
Proof.
  intros e f Pe Pf Fe Ff Hov c.
  destruct (fes_shape_all e f Pe Pf Fe Ff Hov) as (bs & Hb & (Ok & Dec & No) & _).
  destruct (carry_clean_priest_core (fast_expansion_sum e f) bs Hb (conj Ok Dec))
    as (Hcc & Hsum & _).
  unfold c. rewrite Hsum, (fast_expansion_sum_correct e f (fes_safe_of_overflow e f Fe Ff Hov)).
  rewrite Hcc.
  split; [ exact No | split; [ exact (reduce_mag_desc bs Ok Dec) | ] ].
  split; [ exact (reduce_nonzero bs Ok) | reflexivity ].
Qed.

(* HEADLINE: the leading component of carry_clean's output decides the sign
   of e + f.  No Stage D hypothesis; Priest input and the overflow margin. *)
Theorem carry_clean_fes_priest_sign_correct :
  forall e f : list binary64,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    match sign_of_expansion (carry_clean (fast_expansion_sum e f)) with
    | ExpPos  => 0 < expansion_R e + expansion_R f
    | ExpNeg  => expansion_R e + expansion_R f < 0
    | ExpZero => expansion_R e + expansion_R f = 0
    end.
Proof.
  intros e f Pe Pf Fe Ff Hov.
  destruct (carry_clean_fes_priest_ordered e f Pe Pf Fe Ff Hov) as (No & Md & _ & Hs).
  pose proof (nonoverlapping_chain_sign_correct _ No Md) as H.
  rewrite Hs in H. exact H.
Qed.

(* --------------------------------------------------------------------------
   Assumption audit.
   -------------------------------------------------------------------------- *)

Print Assumptions fes_safe_of_overflow.
Print Assumptions reduce_mag_desc.
Print Assumptions carry_clean_fes_priest_ordered.
Print Assumptions carry_clean_fes_priest_sign_correct.
