(* CascadeInvariant.v -- the cascade invariant on `bstate`: a three-state
   machine over the ascending-sorted merge of two Priest chains.  Evidence
   probe; needs CascadeTailBound compiled first with
   -Q docs/h1-vacuity NTS.Proofs.Probes (scripts/hunt_probe_smoke.sh).

     N  ordinary : bstate, every block key < ulp(g_next)            [bstate_step]
     T  tie      : top error h = s*2^c = s*ulp(g_next), Q = s*2^M  [bstate_tie]
     P  pending twin : Q = h, newest error 0, |h| = 2^c,
                   4*2^c < ulp(g_next)                              [bstate_twin]

   PROVED (Qed, corpus axioms)
     cinv_final_shape, cinv_init, cinv_N_step (N -> N given |h| < ulp(g2)).
     N_step_reachable / N_step_actual: on the actual cascade of two Priest
       chains, N -> N or N -> T (strict vs equal look-ahead, from
       CascadeTailBound).  N_to_T_entry: the T-entry contract holds; the
       bstate_tie bound 2^M - 2*2^c <= |g_next| has one ulp of slack.
     cinv_T_step / T_step_reachable: T -> N (anti pair or single outcome of
       bstate_tie) or T -> P (pending twin), on the actual cascade; the
       look-ahead for the following input comes from |g_j| = 2^M - 2^c and
       the Priest key |g_j| < ulp(g_(j+2)), so 2^M <= ulp(g3) and, at p = 53,
       4*2^c < ulp(g3) (the p = 2 pending-twin equality does not arise here).
     cascade_step_obligation_false: the step obligation as stated (over
       ARBITRARY (Q, E, rest)) is FALSE -- Q = 1, g = 2^54, next 2^-100.

   VACUOUS  cascade_aligned_shape is Qed but conditional on
     cascade_step_obligation, which is refuted.  Not citable.  A usable form
     must quantify over reachable states (as N_step_reachable does).

   P -> N (QED): cinv_P_step / P_step_reachable / P_last_step /
     pending_twin_settles.  A pending twin settles in exactly ONE step: with
     |h| = 2^c < ulp(g)/4 the TwoSum(g, h) is exact, Q' = g, and bstate_twin
     files (h, 0, h) as CTwin h below g.  No look-ahead beyond what
     T_step_reachable already proves is needed; cinv_P was not strengthened.

   GLOBAL INDUCTION (QED): cascade_stage_invariant -- at every stage k the
     machine state cinv (acc k) (rev (firstn k hs)) (skipn (S k) s) holds
     (N/T/P steps chained, last-input forms at the end) -- and
     cascade_reachable_shape: for any Priest-valid input pair and any length,
     drop_zeros (cascade_out x0 [] xs) is the aligned carry shape.  Only the
     pure index bookkeeping (acc_final, rev_firstn_S, skipn_nth_cons) is new.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude
*)
From Stdlib Require Import Reals ZArith Lia Lra List Permutation.
From Flocq Require Import IEEE754.Binary Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_lib B64_Pff_bridge
     B64_Expansion B64_FastExpansionSum B64_Overlap_Hierarchy B64_CarryCleanAlgo
     B64_CarryCleanCore B64_CarryCleanLadder B64_CarryCleanOneBit B64_FastExpansionSum_Shewchuk
     B64_CarryCleanRung4 B64_Priest_FES_counterexample.
From NTS.Proofs.Probes Require CascadeTailBound.
Import ListNotations.
Local Open Scope R_scope.
Local Abbreviation b2r := (Binary.B2R prec emax).

(* Full output after running the remaining inputs from state (Q, E);
   E holds the errors so far, newest first. *)
Definition cascade_out (Q : binary64) (E rest : list binary64) : list binary64 :=
  let '(hs, q) := b64_grow_expansion_aux Q rest in q :: (rev hs ++ E).

Lemma cascade_out_step :
  forall Q E g rest,
    cascade_out Q E (g :: rest)
    = cascade_out (fst (b64_TwoSum g Q)) (snd (b64_TwoSum g Q) :: E) rest.
Proof.
  intros Q E g rest. unfold cascade_out. cbn [b64_grow_expansion_aux].
  destruct (b64_TwoSum g Q) as [Qn h]. cbn [fst snd].
  destruct (b64_grow_expansion_aux Qn rest) as [hs q]. cbn [rev].
  rewrite <- app_assoc. reflexivity.
Qed.

(* ---- the three states ------------------------------------------------- *)

(* N: ordinary.  The look-ahead is the keys conjunct. *)
Definition cinv_N (Q : binary64) (E rest : list binary64) : Prop :=
  exists L bs, bstate Q E L bs /\
    match rest with
    | nil => True
    | g :: _ => b64_fin g /\ b2r g <> 0 /\ b64_TwoSum_safe g Q
                /\ Forall (key_below (cexp radix2 b64_fexp (b2r g))) bs
    end.

(* T: a tie is next -- exactly the hypotheses of `bstate_tie`. *)
Definition cinv_T (Q : binary64) (E rest : list binary64) : Prop :=
  exists g rest', rest = g :: rest' /\
  exists (h : binary64) (E0 : list binary64) (bs0 : list cblock) (L : Z) (s : R),
    E = h :: E0 /\ bstate Q E L (push h bs0) /\
    b64_fin g /\ b64_TwoSum_safe g Q /\ (s = 1 \/ s = -1) /\
    let c := cexp radix2 b64_fexp (b2r g) in
    let M := mag radix2 (b2r g) in
    b2r g <> 0 /\ (2 <= M - c)%Z /\ b64_fexp (M + 1) = (c + 1)%Z /\
    b2r Q = s * bpow radix2 M /\ b2r h = s * bpow radix2 c /\
    bpow radix2 M - 2 * bpow radix2 c <= Rabs (b2r g) /\
    b64_fin h /\ Forall b64_fin E0 /\ drop_zeros E0 = flat_map cblock_expand bs0 /\
    carry_shape bs0 /\ pairs_aligned bs0 /\ Forall (key_below c) bs0.

(* P: a pending twin -- the hypotheses of `bstate_twin` / `twin_top_shape`;
   the look-ahead 4*2^c < ulp(g) is only required when an input remains
   (the model needs "<=" at p = 2: see the writeup). *)
Definition cinv_P (Q : binary64) (E rest : list binary64) : Prop :=
  exists (z h : binary64) (E0 : list binary64) (bs0 : list cblock) (c : Z),
    E = z :: h :: E0 /\ Q = h /\ b64_fin z /\ b64_fin h /\ Forall b64_fin E0 /\
    b2r z = 0 /\ Rabs (b2r h) = bpow radix2 c /\
    2 * bpow radix2 c < bpow radix2 emax /\
    drop_zeros E0 = flat_map cblock_expand bs0 /\
    carry_shape bs0 /\ pairs_aligned bs0 /\ Forall (key_below c) bs0 /\
    match rest with
    | nil => True
    | g :: _ => b64_fin g /\ b2r g <> 0 /\ b64_TwoSum_safe g Q /\
                bpow radix2 c < ulp radix2 b64_fexp (b2r g) / 4
    end.

Definition cinv (Q : binary64) (E rest : list binary64) : Prop :=
  cinv_N Q E rest \/ cinv_T Q E rest \/ cinv_P Q E rest.

(* ---- readout: the invariant at the end is the aligned carry shape ----- *)
Lemma cinv_final_shape :
  forall Q E,
    cinv Q E [] ->
    exists bs, drop_zeros (Q :: E) = flat_map cblock_expand bs
               /\ carry_shape bs /\ pairs_aligned bs.
Proof.
  intros Q E [(L & bs & H & _) | [(g & r & Hr & _) | (z & h & E0 & bs0 & c & HE & HQ & Fz & Fh & FE0 & Hz & Hh & Hov & DE & Sh & Al & Kb & _)]].
  - exact (bstate_shape Q E L bs H).
  - discriminate Hr.
  - subst E Q. exact (twin_top_shape h z h E0 bs0 c Fz Fh Hz eq_refl Hh Hov DE Sh Al Kb).
Qed.

(* ---- the OPEN obligation: one TwoSum preserves the machine ------------ *)
Definition cascade_step_obligation : Prop :=
  forall Q E g rest, cinv Q E (g :: rest) ->
    cinv (fst (b64_TwoSum g Q)) (snd (b64_TwoSum g Q) :: E) rest.

(* ---- length is irrelevant: induction over the remaining inputs -------- *)
Theorem cascade_aligned_shape :
  cascade_step_obligation ->
  forall rest Q E, cinv Q E rest ->
    exists bs, drop_zeros (cascade_out Q E rest) = flat_map cblock_expand bs
               /\ carry_shape bs /\ pairs_aligned bs.
Proof.
  intros Ob rest. induction rest as [| g rest IH]; intros Q E H.
  - unfold cascade_out. cbn [b64_grow_expansion_aux rev app]. exact (cinv_final_shape Q E H).
  - rewrite cascade_out_step. apply IH. apply Ob. exact H.
Qed.

(* ---- QEX: cascade_step_obligation is FALSE as stated -----------------
   It quantifies over arbitrary (Q, E, rest), but cinv only looks one input
   ahead.  Q = 1, g = 2^54, next input g3 = 2^-100: the N state holds before
   the step (E = []), and after TwoSum(2^54, 1) = (2^54, 1) the error 1 is
   far above ulp(2^-100), so neither N, T (2^54 is not +-2^mag(g3)) nor P
   (needs two errors) holds.  So cascade_aligned_shape is VACUOUS as a
   headline: its hypothesis is refutable.  A usable obligation must be
   restated over reachable states (cf. N_step_reachable below). *)

Definition qx_one : binary64 := Binary.B754_finite prec emax false 4503599627370496 (-52) eq_refl.
Definition qx_g : binary64 := Binary.B754_finite prec emax false 4503599627370496 2 eq_refl.
Definition qx_g3 : binary64 := Binary.B754_finite prec emax false 4503599627370496 (-152) eq_refl.

Lemma qx_step : [fst (b64_TwoSum qx_g qx_one); snd (b64_TwoSum qx_g qx_one)] = [qx_g; qx_one].
Proof. apply map_B2FF_inj. vm_compute. reflexivity. Qed.

Lemma qx_vals : b2r qx_one = 1 /\ b2r qx_g = bpow radix2 54 /\ b2r qx_g3 = bpow radix2 (-100).
Proof.
  unfold qx_one, qx_g, qx_g3. rewrite !B2R_fin. cbn [cond_Zopp].
  change 4503599627370496 with (bpow radix2 52). rewrite <- !bpow_plus. split; [ reflexivity | split; reflexivity ].
Qed.

Lemma flat_single : forall bs (x : binary64), flat_map cblock_expand bs = [x] ->
  exists bs', bs = CSingle x :: bs'.
Proof.
  intros [| [u | y | y] bs'] x H; cbn in H; try discriminate.
  - injection H as -> _. exists bs'. reflexivity.
Qed.

Theorem cascade_step_obligation_false : ~ cascade_step_obligation.
Proof.
  intro Ob. destruct qx_vals as (V1 & Vg & V3).
  assert (Fone : b64_fin qx_one) by reflexivity. assert (Fg : b64_fin qx_g) by reflexivity.
  assert (F3 : b64_fin qx_g3) by reflexivity.
  assert (Hsm : forall k, (k <= 54)%Z -> bpow radix2 k <= bpow radix2 (emax - 4)) by (intros k Hk; apply bpow_le; unfold emax; lia).
  assert (S : b64_TwoSum_safe qx_g qx_one).
  { apply b64_TwoSum_safe_bound; try assumption.
    - rewrite Vg, Rabs_pos_eq by apply bpow_ge_0. apply Hsm. lia.
    - rewrite V1, Rabs_R1. replace 1 with (bpow radix2 0) by reflexivity. apply Hsm. lia. }
  assert (Pre : cinv qx_one [] (qx_g :: [qx_g3])).
  { left. exists (cexp radix2 b64_fexp (b2r qx_one)), []. split; [ apply bstate_init, Fone | ].
    split; [ exact Fg | ]. split; [ rewrite Vg; apply Rgt_not_eq, bpow_gt_0 | ]. split; [ exact S | constructor ]. }
  pose proof (Ob _ _ _ _ Pre) as Post.
  assert (SQ : fst (b64_TwoSum qx_g qx_one) = qx_g) by exact (f_equal (fun l => nth 0 l qx_g) qx_step).
  assert (Sh : snd (b64_TwoSum qx_g qx_one) = qx_one) by exact (f_equal (fun l => nth 1 l qx_g) qx_step).
  rewrite SQ, Sh in Post.
  assert (Hm3 : mag radix2 (b2r qx_g3) = (-99)%Z :> Z).
  { apply mag_unique. rewrite V3, Rabs_pos_eq by apply bpow_ge_0. split; apply bpow_le || apply bpow_lt; lia. }
  assert (Hc3 : (cexp radix2 b64_fexp (b2r qx_g3) <= 0)%Z).
  { unfold cexp. rewrite Hm3. unfold SpecFloat.fexp, SpecFloat.emin, prec, emax. cbn. lia. }
  destruct Post as [N | [T | P]].
  - destruct N as (L & bs & (_ & _ & _ & DE & _ & _ & _) & _ & _ & _ & K).
    rewrite drop_zeros_cons_nz in DE by (apply b64_is_zero_false; [ exact Fone | rewrite V1; lra ]).
    cbn [drop_zeros filter] in DE. destruct (flat_single bs qx_one (eq_sym DE)) as [bs' ->].
    inversion K as [| ? ? Kb _]. unfold key_below in Kb. cbn [block_key] in Kb. rewrite V1, Rabs_R1 in Kb.
    pose proof (bpow_le radix2 _ 0 Hc3) as Hb. change (bpow radix2 0) with 1 in Hb. lra.
  - destruct T as (g & rest' & Hr & h & E0 & bs0 & L & s & HE & _ & _ & _ & Hs & T).
    injection Hr as <- _. cbv zeta in T. destruct T as (_ & _ & _ & HQ & _).
    rewrite Vg, Hm3 in HQ. pose proof (bpow_lt radix2 (-99) 54 ltac:(lia)) as Hlt.
    pose proof (bpow_gt_0 radix2 (-99)). destruct Hs as [-> | ->]; lra.
  - destruct P as (z & h & E0 & bs0 & c & HE & _). injection HE as _ HE. discriminate.
Qed.

(* The initial state: the first sorted input is the accumulator. *)
Lemma cinv_init :
  forall g rest, b64_fin g ->
    (match rest with nil => True
     | g2 :: _ => b2r g2 <> 0 /\ b64_fin g2 /\ b64_TwoSum_safe g2 g end) ->
    cinv_N g [] rest.
Proof.
  intros g rest Fg Hr. exists (cexp radix2 b64_fexp (b2r g)), []. split.
  - exact (bstate_init g Fg).
  - destruct rest as [| g2 r]; [ exact I | ]. cbn in Hr; destruct Hr as (H0 & Fg2 & S2).
    refine (conj Fg2 (conj H0 (conj S2 _))). constructor.
Qed.

(* ---- RUNG: the N -> N step, structural half PROVED --------------------
   One TwoSum from an N state, next input g2 with |g| <= |g2| (sortedness).
   Everything in N for g2 follows from `bstate_step` and monotonicity of ulp,
   EXCEPT the one arithmetic fact kept as a hypothesis:
       LOOKAHEAD_h :  |h| < ulp(g2)   (the new error, below the next input's ulp)
   That is what remains of the obligation on this branch: it needs
   |Q'| to be at most a small multiple of |g2| (Priest keys), not structure. *)
Lemma cinv_N_step :
  forall Q E g g2 rest,
    cinv_N Q E (g :: g2 :: rest) ->
    Rabs (b2r g) <= Rabs (b2r g2) ->
    b64_fin g2 -> b2r g2 <> 0 ->
    b64_TwoSum_safe g2 (fst (b64_TwoSum g Q)) ->
    Rabs (b2r (snd (b64_TwoSum g Q))) < ulp radix2 b64_fexp (b2r g2) ->
    cinv_N (fst (b64_TwoSum g Q)) (snd (b64_TwoSum g Q) :: E) (g2 :: rest).
Proof.
  intros Q E g g2 rest (L & bs & H & Fg & Hg0 & S & Kg) Hle Fg2 Hg20 S2 Hlook.
  destruct (bstate_step Q E L bs g H Fg S Kg) as [St _]. cbv zeta in St.
  exists (Z.max (Z.min (cexp radix2 b64_fexp (b2r g)) L)
                (cexp radix2 b64_fexp (b2r (fst (b64_TwoSum g Q))))),
         (push (snd (b64_TwoSum g Q)) bs).
  refine (conj St (conj Fg2 (conj Hg20 (conj S2 _)))).
  assert (Hu : ulp radix2 b64_fexp (b2r g2) = bpow radix2 (cexp radix2 b64_fexp (b2r g2)))
    by (apply ulp_neq_0, Hg20).
  assert (Hu1 : ulp radix2 b64_fexp (b2r g) = bpow radix2 (cexp radix2 b64_fexp (b2r g)))
    by (apply ulp_neq_0, Hg0).
  pose proof (ulp_le radix2 b64_fexp (b2r g) (b2r g2) Hle) as Hmono.
  apply key_below_push.
  - rewrite <- Hu. exact Hlook.
  - eapply Forall_impl; [ | exact Kg ]. unfold key_below. intros b Hb.
    apply Rlt_le_trans with (1 := Hb). rewrite <- Hu1, <- Hu. exact Hmono.
Qed.


(* ---- RUNG: N -> T entry ----------------------------------------------
   The machine half: an N state plus the tie facts for the next state
   give cinv_T.  Then the reachable version: on the actual cascade of two
   Priest chains, equality in the closed look-ahead supplies those facts
   (CascadeTailBound.b64_equality_entry), so N -> T entry is PROVED; the
   lower bound 2^M - 2*2^c <= |g_next| inherited from bstate_tie holds,
   in fact with |g| = 2^M - 2^c <= |g_next|. *)

Lemma cexp64_mono : forall x y, b2r x <> 0 -> Rabs (b2r x) <= Rabs (b2r y) ->
  (cexp radix2 b64_fexp (b2r x) <= cexp radix2 b64_fexp (b2r y))%Z.
Proof.
  intros x y Hx Hxy. assert (Hm : (mag radix2 (b2r x) <= mag radix2 (b2r y))%Z) by (apply mag_le_abs; assumption).
  unfold cexp, SpecFloat.fexp, SpecFloat.emin. change IntDef.Z.max with Z.max. lia.
Qed.

Lemma cinv_N_to_T :
  forall Q E g g2 rest (sg : R),
    cinv_N Q E (g :: g2 :: rest) ->
    Rabs (b2r g) <= Rabs (b2r g2) -> b64_fin g2 -> b2r g2 <> 0 ->
    b64_TwoSum_safe g2 (fst (b64_TwoSum g Q)) -> (sg = 1 \/ sg = -1) ->
    let M := mag radix2 (b2r g2) in
    let c := cexp radix2 b64_fexp (b2r g2) in
    b2r (fst (b64_TwoSum g Q)) = sg * bpow radix2 M ->
    b2r (snd (b64_TwoSum g Q)) = sg * bpow radix2 c ->
    (2 <= M - c)%Z -> b64_fexp (M + 1) = (c + 1)%Z ->
    bpow radix2 M - 2 * bpow radix2 c <= Rabs (b2r g2) ->
    cinv_T (fst (b64_TwoSum g Q)) (snd (b64_TwoSum g Q) :: E) (g2 :: rest).
Proof.
  intros Q E g g2 rest sg (L & bs & H & Fg & Hg0 & S & Kg) Hle Fg2 Hg20 S2 Hsg M c HQ Hh HMc Hf Hgl.
  destruct (bstate_step Q E L bs g H Fg S Kg) as [St _]. cbv zeta in St.
  pose proof H as (FQ & FE & MQ & DE & Sh & Al & Kb).
  destruct (ts_facts g Q S) as (_ & Fh & _ & _ & _ & _).
  exists g2, rest. split; [ reflexivity | ].
  exists (snd (b64_TwoSum g Q)), E, bs,
    (Z.max (Z.min (cexp radix2 b64_fexp (b2r g)) L) (cexp radix2 b64_fexp (b2r (fst (b64_TwoSum g Q))))), sg.
  split; [ reflexivity | ]. split; [ exact St | ]. split; [ exact Fg2 | ]. split; [ exact S2 | ].
  split; [ exact Hsg | ]. cbv zeta. fold M c.
  refine (conj Hg20 (conj HMc (conj Hf (conj HQ (conj Hh (conj Hgl (conj Fh (conj FE (conj DE (conj Sh (conj Al _))))))))))).
  apply (key_below_mono (cexp radix2 b64_fexp (b2r g))); [ apply cexp64_mono; assumption | exact Kg ].
Qed.

(* On the actual cascade (q, gj, g2 are the real accumulator and inputs; E
   and rest are universally quantified, so they cover the real error prefix
   and remaining inputs -- see N_step_actual): N state + equality => T. *)
Theorem N_to_T_entry :
  forall e f x0 xs,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    Forall (fun x => b2r x <> 0) (e ++ f) ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    sort_by_abs (e ++ f) = x0 :: xs ->
    forall j E rest, (1 <= j)%nat -> (j < length xs)%nat ->
    let d := Binary.B754_zero prec emax false in
    let gj := nth j (x0 :: xs) d in
    let g2 := nth (S j) (x0 :: xs) d in
    let q := CascadeTailBound.acc x0 xs (j - 1) in
    cinv_N q E (gj :: g2 :: rest) ->
    Rabs (b2r (snd (b64_TwoSum gj q))) = ulp radix2 b64_fexp (b2r g2) ->
    cinv_T (fst (b64_TwoSum gj q)) (snd (b64_TwoSum gj q) :: E) (g2 :: rest).
Proof.
  intros e f x0 xs Pe Pf Fe Ff Nz Hov Hs j E rest Hj1 Hj2 d gj g2 q HN Heq.
  destruct (CascadeTailBound.b64_equality_entry e f x0 xs Pe Pf Fe Ff Nz Hov Hs j Hj1 Hj2 Heq)
    as (sg & Hsg & HQ & Hh & HMc & Hf & _ & Hle & Hgl & _).
  assert (Hperm : Permutation (e ++ f) (x0 :: xs)) by (rewrite <- Hs; apply sort_by_abs_perm).
  assert (Fs : Forall b64_fin (x0 :: xs)) by (rewrite <- Hs; apply sort_by_abs_Forall, Forall_app; split; assumption).
  assert (In2 : In g2 (x0 :: xs)) by (apply nth_In; simpl; lia).
  assert (Fg2 : b64_fin g2) by (rewrite Forall_forall in Fs; apply Fs, In2).
  assert (Hg20 : b2r g2 <> 0).
  { rewrite Forall_forall in Nz. apply Nz. apply (Permutation_in _ (Permutation_sym Hperm)), In2. }
  assert (S2 : b64_TwoSum_safe g2 (fst (b64_TwoSum gj q))).
  { pose proof (fes_cascade_safe e f Fe Ff Hov) as C. rewrite Hs in C.
    pose proof (CascadeTailBound.safe_nth xs x0 j C Hj2) as Sj.
    destruct j as [| j']; [ lia | ]. unfold g2, gj, q. simpl Nat.sub. rewrite Nat.sub_0_r. exact Sj. }
  exact (cinv_N_to_T q E gj g2 rest sg HN Hle Fg2 Hg20 S2 Hsg HQ Hh HMc Hf Hgl).
Qed.

(* The N branch on reachable states: N -> N (strict look-ahead) or N -> T
   (equality).  This discharges the N branch of the step for the actual
   cascade; T -> {N, P, anti} and P -> N remain. *)
Theorem N_step_reachable :
  forall e f x0 xs,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    Forall (fun x => b2r x <> 0) (e ++ f) ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    sort_by_abs (e ++ f) = x0 :: xs ->
    forall j E rest, (1 <= j)%nat -> (j < length xs)%nat ->
    let d := Binary.B754_zero prec emax false in
    let gj := nth j (x0 :: xs) d in
    let g2 := nth (S j) (x0 :: xs) d in
    let q := CascadeTailBound.acc x0 xs (j - 1) in
    cinv_N q E (gj :: g2 :: rest) ->
    cinv_N (fst (b64_TwoSum gj q)) (snd (b64_TwoSum gj q) :: E) (g2 :: rest)
    \/ cinv_T (fst (b64_TwoSum gj q)) (snd (b64_TwoSum gj q) :: E) (g2 :: rest).
Proof.
  intros e f x0 xs Pe Pf Fe Ff Nz Hov Hs j E rest Hj1 Hj2 d gj g2 q HN.
  assert (Hperm : Permutation (e ++ f) (x0 :: xs)) by (rewrite <- Hs; apply sort_by_abs_perm).
  assert (Fs : Forall b64_fin (x0 :: xs)) by (rewrite <- Hs; apply sort_by_abs_Forall, Forall_app; split; assumption).
  assert (In2 : In g2 (x0 :: xs)) by (apply nth_In; simpl; lia).
  assert (Fg2 : b64_fin g2) by (rewrite Forall_forall in Fs; apply Fs, In2).
  assert (Hg20 : b2r g2 <> 0).
  { rewrite Forall_forall in Nz. apply Nz. apply (Permutation_in _ (Permutation_sym Hperm)), In2. }
  pose proof (fes_cascade_safe e f Fe Ff Hov) as C. rewrite Hs in C.
  assert (S2 : b64_TwoSum_safe g2 (fst (b64_TwoSum gj q))).
  { pose proof (CascadeTailBound.safe_nth xs x0 j C Hj2) as Sj.
    destruct j as [| j']; [ lia | ]. unfold g2, gj, q. simpl Nat.sub. rewrite Nat.sub_0_r. exact Sj. }
  assert (Hle : Rabs (b2r gj) <= Rabs (b2r g2)).
  { apply (CascadeTailBound.sorted_g (x0 :: xs)); [ rewrite <- Hs; apply sort_by_abs_sorted | simpl; lia ]. }
  assert (Hlook : Rabs (b2r (snd (b64_TwoSum gj q))) <= ulp radix2 b64_fexp (b2r g2)).
  { pose proof (CascadeTailBound.b64_closed_lookahead e f x0 xs Pe Pf Fe Ff Nz Hov Hs j Hj1 Hj2) as L.
    rewrite CascadeTailBound.nth_hs in L by lia.
    destruct j as [| j']; [ lia | ]. unfold gj, q, g2. simpl Nat.sub in *. rewrite Nat.sub_0_r in *. exact L. }
  destruct (Rlt_or_le (Rabs (b2r (snd (b64_TwoSum gj q)))) (ulp radix2 b64_fexp (b2r g2))) as [Lt | Ge].
  - left. exact (cinv_N_step q E gj g2 rest HN Hle Fg2 Hg20 S2 Lt).
  - right. assert (Heq : Rabs (b2r (snd (b64_TwoSum gj q))) = ulp radix2 b64_fexp (b2r g2)) by lra.
    exact (N_to_T_entry e f x0 xs Pe Pf Fe Ff Nz Hov Hs j E rest Hj1 Hj2 HN Heq).
Qed.

(* The same with E and rest fixed to the actual cascade: the error prefix
   h_(j-1), ..., h_1 (newest first) and the inputs after g2. *)
Corollary N_step_actual :
  forall e f x0 xs,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    Forall (fun x => b2r x <> 0) (e ++ f) ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    sort_by_abs (e ++ f) = x0 :: xs ->
    forall j, (1 <= j)%nat -> (j < length xs)%nat ->
    let d := Binary.B754_zero prec emax false in
    let gj := nth j (x0 :: xs) d in
    let g2 := nth (S j) (x0 :: xs) d in
    let q := CascadeTailBound.acc x0 xs (j - 1) in
    let E := rev (firstn (j - 1) (fst (b64_grow_expansion_aux x0 xs))) in
    let rest := skipn (S (S j)) (x0 :: xs) in
    cinv_N q E (gj :: g2 :: rest) ->
    cinv_N (fst (b64_TwoSum gj q)) (snd (b64_TwoSum gj q) :: E) (g2 :: rest)
    \/ cinv_T (fst (b64_TwoSum gj q)) (snd (b64_TwoSum gj q) :: E) (g2 :: rest).
Proof.
  intros e f x0 xs Pe Pf Fe Ff Nz Hov Hs j Hj1 Hj2 d gj g2 q E rest.
  exact (N_step_reachable e f x0 xs Pe Pf Fe Ff Nz Hov Hs j E rest Hj1 Hj2).
Qed.

(* ---- RUNG: T -> {N, P} -------------------------------------------------
   From a T state, bstate_tie's three outcomes land in the machine:
   anti pair -> N, single -> N, pending twin -> P.  The look-ahead for the
   following input g3 is a hypothesis of the machine half (cinv_T_step) and
   is PROVED on the actual cascade (T_step_reachable), from the entry fact
   |g_j| = 2^M - 2^c and the Priest key |g_j| < ulp(g_(j+2)). *)

Lemma cinv_T_step :
  forall Q E g2 rest,
    cinv_T Q E (g2 :: rest) ->
    let M := mag radix2 (b2r g2) in
    let c := cexp radix2 b64_fexp (b2r g2) in
    let Q' := fst (b64_TwoSum g2 Q) in
    let h' := snd (b64_TwoSum g2 Q) in
    2 * bpow radix2 c < bpow radix2 emax ->
    match rest with
    | nil => True
    | g3 :: _ => b64_fin g3 /\ b2r g3 <> 0 /\ b64_TwoSum_safe g3 Q'
                 /\ bpow radix2 M <= ulp radix2 b64_fexp (b2r g3) /\ (c + 2 < M)%Z
    end ->
    cinv_N Q' (h' :: E) rest \/ cinv_P Q' (h' :: E) rest.
Proof.
  intros Q E g2 rest HT M c Q' h' Hov Hlook.
  destruct HT as (g & rest' & Hr & h & E0 & bs0 & L & s & HE & St & Fg & S & Hs & T).
  injection Hr as <- <-. cbv zeta in T.
  destruct T as (Hg0 & HMc & Hf & HQ & Hh & Hgl & Fh & FE & DE & Sh & Al & Kb).
  fold M c in HMc, Hf, HQ, Hh, Hgl, Kb.
  pose proof (bstate_tie g2 Q h E0 bs0 s Fg S Hs Hg0 HMc Hf HQ Hh Hgl Fh FE DE Sh Al Kb) as TS.
  cbv zeta in TS. fold Q' h' in TS. subst E.
  (* keys below 2^M stay below ulp(g3) *)
  assert (Lift : forall bs L', (L' <= M)%Z -> Forall (key_below L') bs ->
            match rest with nil => True | g3 :: _ => Forall (key_below (cexp radix2 b64_fexp (b2r g3))) bs end).
  { intros bs L' HL K. destruct rest as [| g3 r]; [ exact I | ].
    destruct Hlook as (_ & N3 & _ & HM3 & _). rewrite ulp_neq_0 in HM3 by exact N3.
    apply le_bpow in HM3. apply (key_below_mono L'); [ lia | exact K ]. }
  destruct TS as [Anti | [(Hz & HQ') | Single]].
  - left. exists M, (CAnti h' :: bs0). split; [ exact Anti | ].
    pose proof (Lift _ M (Z.le_refl M) (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Anti))))))) as K.
    destruct rest as [| g3 r]; [ exact I | ].
    destruct Hlook as (F3 & N3 & S3 & _ & _). exact (conj F3 (conj N3 (conj S3 K))).
  - right. destruct (ts_facts g2 Q S) as (_ & Fh' & _ & _ & _ & _). fold Q' h' in Fh'.
    exists h', h, E0, bs0, c. split; [ reflexivity | ]. split; [ exact HQ' | ].
    split; [ exact Fh' | ]. split; [ exact Fh | ]. split; [ exact FE | ]. split; [ exact Hz | ].
    split.
    { rewrite Hh, Rabs_mult. pose proof (bpow_gt_0 radix2 c).
      destruct Hs as [-> | ->]; [ rewrite Rabs_R1 | rewrite (Rabs_left (-1)) by lra ];
      rewrite Rabs_pos_eq by lra; ring. }
    split; [ exact Hov | ]. split; [ exact DE | ]. split; [ exact Sh | ]. split; [ exact Al | ].
    split; [ exact Kb | ].
    destruct rest as [| g3 r]; [ exact I | ].
    destruct Hlook as (F3 & N3 & S3 & HM3 & Hc2). split; [ exact F3 | ]. split; [ exact N3 | ].
    split; [ exact S3 | ].
    assert (H4 : 4 * bpow radix2 c = bpow radix2 (c + 2))
      by (rewrite bpow_plus; change (bpow radix2 2) with 4; ring).
    assert (bpow radix2 (c + 2) < bpow radix2 M) by (apply bpow_lt; lia). lra.
  - left. exists (c + 1)%Z, (CSingle h :: bs0). split; [ exact Single | ].
    pose proof (Lift _ (c + 1)%Z ltac:(lia) (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Single))))))) as K.
    destruct rest as [| g3 r]; [ exact I | ].
    destruct Hlook as (F3 & N3 & S3 & _ & _). exact (conj F3 (conj N3 (conj S3 K))).
Qed.

(* On the actual cascade: the T state entered at step j (equality in the
   look-ahead) steps to N or P, with the real remaining inputs. *)
Theorem T_step_reachable :
  forall e f x0 xs,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    Forall (fun x => b2r x <> 0) (e ++ f) ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    sort_by_abs (e ++ f) = x0 :: xs ->
    forall j E0, (1 <= j)%nat -> (j < length xs)%nat ->
    let d := Binary.B754_zero prec emax false in
    let gj := nth j (x0 :: xs) d in
    let g2 := nth (S j) (x0 :: xs) d in
    let q := CascadeTailBound.acc x0 xs (j - 1) in
    let Q := fst (b64_TwoSum gj q) in
    let h := snd (b64_TwoSum gj q) in
    let rest := skipn (S (S j)) (x0 :: xs) in
    Rabs (b2r h) = ulp radix2 b64_fexp (b2r g2) ->
    cinv_T Q (h :: E0) (g2 :: rest) ->
    cinv_N (fst (b64_TwoSum g2 Q)) (snd (b64_TwoSum g2 Q) :: h :: E0) rest
    \/ cinv_P (fst (b64_TwoSum g2 Q)) (snd (b64_TwoSum g2 Q) :: h :: E0) rest.
Proof.
  intros e f x0 xs Pe Pf Fe Ff Nz Hov Hs j E0 Hj1 Hj2 d gj g2 q Q h rest Heq HT.
  destruct (CascadeTailBound.b64_equality_entry e f x0 xs Pe Pf Fe Ff Nz Hov Hs j Hj1 Hj2 Heq)
    as (sg & _ & _ & _ & HMc & _ & Hgj & _ & _ & Hc).
  set (M := (mag radix2 (b2r g2) : Z)). set (c := cexp radix2 b64_fexp (b2r g2)).
  assert (Hc' : c = (M - prec)%Z) by exact Hc.
  assert (Hgj' : Rabs (b2r gj) = bpow radix2 M - bpow radix2 c) by exact Hgj.
  clear Hc Hgj HMc.
  assert (Fs : Forall b64_fin (x0 :: xs)) by (rewrite <- Hs; apply sort_by_abs_Forall, Forall_app; split; assumption).
  assert (Hperm : Permutation (e ++ f) (x0 :: xs)) by (rewrite <- Hs; apply sort_by_abs_perm).
  assert (HMe : (M <= emax)%Z).
  { assert (Hg20 : b2r g2 <> 0).
    { rewrite Forall_forall in Nz. apply Nz. apply (Permutation_in _ (Permutation_sym Hperm)). apply nth_In. simpl. lia. }
    apply mag_le_bpow; [ exact Hg20 | apply Binary.abs_B2R_lt_emax ]. }
  assert (Hov2 : 2 * bpow radix2 c < bpow radix2 emax).
  { assert (E2 : 2 * bpow radix2 c = bpow radix2 (c + 1)) by (rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
    rewrite E2. apply bpow_lt. unfold prec in Hc'. lia. }
  apply (cinv_T_step Q (h :: E0) g2 rest HT Hov2).
  unfold rest. destruct (Nat.lt_ge_cases (S j) (length xs)) as [Lt | Ge].
  - (* g3 exists *)
    assert (Hsk : skipn (S (S j)) (x0 :: xs) = nth (S (S j)) (x0 :: xs) d :: skipn (S (S (S j))) (x0 :: xs)).
    { cbn [skipn]. clear -Lt. revert xs Lt. induction j as [| j' IH]; intros [| y ys] Lt; simpl in Lt |- *; try lia.
      - destruct ys as [| z zs]; simpl in Lt |- *; [ lia | reflexivity ].
      - apply IH. lia. }
    rewrite Hsk. set (g3 := nth (S (S j)) (x0 :: xs) d).
    assert (In3 : In g3 (x0 :: xs)) by (apply nth_In; simpl; lia).
    split; [ rewrite Forall_forall in Fs; apply Fs, In3 | ].
    assert (N3 : b2r g3 <> 0).
    { rewrite Forall_forall in Nz. apply Nz. apply (Permutation_in _ (Permutation_sym Hperm)), In3. }
    split; [ exact N3 | ].
    split.
    { pose proof (fes_cascade_safe e f Fe Ff Hov) as C. rewrite Hs in C.
      pose proof (CascadeTailBound.safe_nth xs x0 (S j) C Lt) as Sj.
      destruct j as [| j']; [ lia | ]. unfold g3, Q, gj, q. simpl Nat.sub. rewrite Nat.sub_0_r. exact Sj. }
    split; [ | unfold prec in Hc'; lia ].
    (* 2^M <= ulp(g3): ulp(g3) > |g_j| = 2^M - 2^c > 2^(M-1) *)
    pose proof (CascadeTailBound.b64_keys e f x0 xs Pe Pf Fe Ff Nz Hs j ltac:(lia)) as K.
    replace (j + 2)%nat with (S (S j)) in K by lia.
    assert (K' : Rabs (b2r gj) < ulp radix2 b64_fexp (b2r g3)) by exact K. rewrite Hgj' in K'. clear K. rewrite ulp_neq_0 in K' |- * by exact N3.
    assert (Hhalf : bpow radix2 (M - 1) < bpow radix2 M - bpow radix2 c).
    { assert (bpow radix2 c <= bpow radix2 (M - 2)) by (apply bpow_le; unfold prec in Hc'; lia).
      assert (D1 : bpow radix2 (M - 1) = 2 * bpow radix2 (M - 2))
        by (replace (M - 1)%Z with ((M - 2) + 1)%Z by ring; rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
      assert (D2 : bpow radix2 M = 2 * bpow radix2 (M - 1))
        by (replace M with ((M - 1) + 1)%Z at 1 by ring; rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
      pose proof (bpow_gt_0 radix2 (M - 2)). lra. }
    apply bpow_le. assert (Hlt : bpow radix2 (M - 1) < bpow radix2 (cexp radix2 b64_fexp (b2r g3))) by lra.
    apply lt_bpow in Hlt. lia.
  - (* no g3 *)
    rewrite skipn_all2 by (simpl; lia). exact I.
Qed.

(* ---- RUNG 9a: P -> N -- a pending twin settles in ONE step ------------------
   Question: can a Priest-valid pending twin stay pending indefinitely?
   ANSWER: NO.  cinv_P holds Q = h with |h| = 2^c and the look-ahead
   4*2^c < ulp(g) for the next input g.  Then |h| < ulp(g)/4 < half the
   spacing on either side of g, so TwoSum(g, h) = (g, h) EXACTLY: g absorbs the
   old accumulator, and h reappears as the new error.  The pending carry is
   discharged by that single TwoSum -- bstate_twin turns (h, 0, h) into the
   twin block CTwin h below g.  The consumed resource is the accumulator
   itself: after the step Q' = g, which is no longer a tiny carry, so there
   is nothing left to sustain a pending twin.  The settling time is exactly 1.

   The machine half below needs from the following input g2 only what N needs
   (finite, nonzero, TwoSum-safe) plus sortedness |g| <= |g2|, which lifts
   the twin key 2*2^c < ulp(g) <= ulp(g2).  No strengthening of cinv_P was
   needed: the look-ahead conjunct is exactly what T_step_reachable proves. *)
Lemma cinv_P_step :
  forall Q E g rest,
    cinv_P Q E (g :: rest) ->
    match rest with
    | nil => True
    | g2 :: _ => Rabs (b2r g) <= Rabs (b2r g2) /\ b64_fin g2 /\ b2r g2 <> 0
                 /\ b64_TwoSum_safe g2 (fst (b64_TwoSum g Q))
    end ->
    cinv_N (fst (b64_TwoSum g Q)) (snd (b64_TwoSum g Q) :: E) rest.
Proof.
  intros Q E g rest HP Hnext.
  destruct HP as (z & h & E0 & bs0 & c & HE & HQ & Fz & Fh & FE0 & Hz & Hh & Hov & DE & Sh & Al & Kb & Fg & Hg0 & S & Hsmall).
  subst E Q.
  pose proof (bstate_twin g h z h E0 bs0 c Fg Hg0 S Fz Fh FE0 Hz eq_refl Hh Hsmall Hov DE Sh Al Kb) as B.
  cbv zeta in B.
  exists (cexp radix2 b64_fexp (b2r g)), (CTwin h :: bs0). split; [ exact B | ].
  destruct rest as [| g2 rest']; [ exact I | ].
  destruct Hnext as (Hle & Fg2 & Hg20 & S2).
  refine (conj Fg2 (conj Hg20 (conj S2 _))).
  assert (Hu : ulp radix2 b64_fexp (b2r g2) = bpow radix2 (cexp radix2 b64_fexp (b2r g2)))
    by (apply ulp_neq_0, Hg20).
  assert (Hu1 : ulp radix2 b64_fexp (b2r g) = bpow radix2 (cexp radix2 b64_fexp (b2r g)))
    by (apply ulp_neq_0, Hg0).
  pose proof (ulp_le radix2 b64_fexp (b2r g) (b2r g2) Hle) as Hmono.
  pose proof (bpow_gt_0 radix2 c) as Hc0.
  constructor.
  - unfold key_below. cbn [block_key]. rewrite <- Hu, Hh. lra.
  - eapply Forall_impl; [ | exact Kb ]. unfold key_below. intros b Hb. rewrite <- Hu. lra.
Qed.

(* On the actual cascade: a pending twin at accumulator acc(j-1) with inputs
   g_j, g_(j+1) steps to N.  Same ingredients as N_step_reachable. *)
Theorem P_step_reachable :
  forall e f x0 xs,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    Forall (fun x => b2r x <> 0) (e ++ f) ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    sort_by_abs (e ++ f) = x0 :: xs ->
    forall j E rest, (1 <= j)%nat -> (j < length xs)%nat ->
    let d := Binary.B754_zero prec emax false in
    let gj := nth j (x0 :: xs) d in
    let g2 := nth (S j) (x0 :: xs) d in
    let q := CascadeTailBound.acc x0 xs (j - 1) in
    cinv_P q E (gj :: g2 :: rest) ->
    cinv_N (fst (b64_TwoSum gj q)) (snd (b64_TwoSum gj q) :: E) (g2 :: rest).
Proof.
  intros e f x0 xs Pe Pf Fe Ff Nz Hov Hs j E rest Hj1 Hj2 d gj g2 q HP.
  assert (Hperm : Permutation (e ++ f) (x0 :: xs)) by (rewrite <- Hs; apply sort_by_abs_perm).
  assert (Fs : Forall b64_fin (x0 :: xs)) by (rewrite <- Hs; apply sort_by_abs_Forall, Forall_app; split; assumption).
  assert (In2 : In g2 (x0 :: xs)) by (apply nth_In; simpl; lia).
  assert (Fg2 : b64_fin g2) by (rewrite Forall_forall in Fs; apply Fs, In2).
  assert (Hg20 : b2r g2 <> 0).
  { rewrite Forall_forall in Nz. apply Nz. apply (Permutation_in _ (Permutation_sym Hperm)), In2. }
  pose proof (fes_cascade_safe e f Fe Ff Hov) as C. rewrite Hs in C.
  assert (S2 : b64_TwoSum_safe g2 (fst (b64_TwoSum gj q))).
  { pose proof (CascadeTailBound.safe_nth xs x0 j C Hj2) as Sj.
    destruct j as [| j']; [ lia | ]. unfold g2, gj, q. simpl Nat.sub. rewrite Nat.sub_0_r. exact Sj. }
  assert (Hle : Rabs (b2r gj) <= Rabs (b2r g2)).
  { apply (CascadeTailBound.sorted_g (x0 :: xs)); [ rewrite <- Hs; apply sort_by_abs_sorted | simpl; lia ]. }
  exact (cinv_P_step q E gj (g2 :: rest) HP (conj Hle (conj Fg2 (conj Hg20 S2)))).
Qed.

(* No next input: a pending twin at the last step also lands in N (and so in
   the final aligned shape, via cinv_final_shape). *)
Corollary P_last_step :
  forall Q E g,
    cinv_P Q E [g] -> cinv_N (fst (b64_TwoSum g Q)) (snd (b64_TwoSum g Q) :: E) [].
Proof. intros Q E g HP. exact (cinv_P_step Q E g [] HP I). Qed.

(* Machine-level classification: from P, ONE step is N.  So P is never
   followed by P, and a pending twin never propagates. *)
Corollary pending_twin_settles :
  forall Q E g rest,
    cinv_P Q E (g :: rest) ->
    match rest with
    | nil => True
    | g2 :: _ => Rabs (b2r g) <= Rabs (b2r g2) /\ b64_fin g2 /\ b2r g2 <> 0
                 /\ b64_TwoSum_safe g2 (fst (b64_TwoSum g Q))
    end ->
    exists L bs, bstate (fst (b64_TwoSum g Q)) (snd (b64_TwoSum g Q) :: E) L bs.
Proof.
  intros Q E g rest HP Hn. destruct (cinv_P_step Q E g rest HP Hn) as (L & bs & H & _).
  exists L, bs. exact H.
Qed.

(* ---- RUNG 9b: the global induction ------------------------------------
   Everything below is bookkeeping: each stage k (k TwoSums done) carries
   cinv (acc k) (rev (firstn k hs)) (skipn (S k) s), s = x0 :: xs, hs the
   errors of b64_grow_expansion_aux.  The step is N_step_reachable /
   T_step_reachable / P_step_reachable (or their last-input forms); no new
   arithmetic.  Conclusion: the FULL output of the actual recurrence on any
   Priest-valid input pair has the aligned carry shape, for any length. *)

Definition cascade_hyps (e f : list binary64) (x0 : binary64) (xs : list binary64) : Prop :=
  priest_chain e /\ priest_chain f /\ Forall b64_fin e /\ Forall b64_fin f /\
  Forall (fun x => b2r x <> 0) (e ++ f) /\
  abs_sum e + abs_sum f <= bpow radix2 (emax - 5) /\
  sort_by_abs (e ++ f) = x0 :: xs.

Local Definition dz : binary64 := Binary.B754_zero prec emax false.

Lemma cinv_N_last :
  forall Q E g, cinv_N Q E [g] -> cinv_N (fst (b64_TwoSum g Q)) (snd (b64_TwoSum g Q) :: E) [].
Proof.
  intros Q E g (L & bs & H & Fg & Hg0 & S & Kg).
  destruct (bstate_step Q E L bs g H Fg S Kg) as [St _].
  exact (ex_intro _ _ (ex_intro _ _ (conj St I))).
Qed.

Lemma acc_final : forall xs q, snd (b64_grow_expansion_aux q xs) = CascadeTailBound.acc q xs (length xs).
Proof.
  induction xs as [| x xs IH]; intro q; [ reflexivity | ].
  cbn [b64_grow_expansion_aux length]. destruct (b64_TwoSum x q) as [qn h0] eqn:E.
  destruct (b64_grow_expansion_aux qn xs) as [hs qf] eqn:E2. cbn [snd].
  rewrite CascadeTailBound.acc_shift, E. cbn [fst]. specialize (IH qn). rewrite E2 in IH. exact IH.
Qed.

Lemma rev_firstn_S : forall (l : list binary64) k, (k < length l)%nat ->
  rev (firstn (S k) l) = nth k l dz :: rev (firstn k l).
Proof.
  induction l as [| a l IH]; intros k Hk; [ simpl in Hk; lia | ].
  destruct k as [| k]; [ reflexivity | ].
  assert (Hk' : (k < length l)%nat) by (simpl in Hk; lia).
  change (firstn (S (S k)) (a :: l)) with (a :: firstn (S k) l).
  change (firstn (S k) (a :: l)) with (a :: firstn k l).
  change (nth (S k) (a :: l) dz) with (nth k l dz).
  cbn [rev]. rewrite (IH k Hk'). reflexivity.
Qed.

Lemma skipn_nth_cons : forall (l : list binary64) n, (n < length l)%nat ->
  skipn n l = nth n l dz :: skipn (S n) l.
Proof.
  induction l as [| a l IH]; intros n Hn; [ simpl in Hn; lia | ].
  destruct n as [| n]; [ reflexivity | ]. cbn [skipn nth]. apply IH. simpl in Hn; lia.
Qed.

Theorem cascade_stage_invariant :
  forall e f x0 xs, cascade_hyps e f x0 xs ->
  forall k, (k <= length xs)%nat ->
    cinv (CascadeTailBound.acc x0 xs k) (rev (firstn k (fst (b64_grow_expansion_aux x0 xs))))
         (skipn (S k) (x0 :: xs)).
Proof.
  intros e f x0 xs HH. pose proof HH as (Pe & Pf & Fe & Ff & Nz & Hov & Hs).
  assert (Hperm : Permutation (e ++ f) (x0 :: xs)) by (rewrite <- Hs; apply sort_by_abs_perm).
  assert (Fs : Forall b64_fin (x0 :: xs)) by (rewrite <- Hs; apply sort_by_abs_Forall, Forall_app; split; assumption).
  assert (C : cascade_safe x0 xs) by (pose proof (fes_cascade_safe e f Fe Ff Hov) as C0; rewrite Hs in C0; exact C0).
  induction k as [| k IH]; intro Hk.
  - (* stage 0 *)
    left. cbn [CascadeTailBound.acc firstn rev skipn].
    apply cinv_init; [ rewrite Forall_forall in Fs; apply Fs; left; reflexivity | ].
    destruct xs as [| g2 r]; [ exact I | ].
    destruct C as [S1 _]. split; [ | split; [ | exact S1 ] ].
    + rewrite Forall_forall in Nz. apply Nz. apply (Permutation_in _ (Permutation_sym Hperm)). right; left; reflexivity.
    + rewrite Forall_forall in Fs; apply Fs; right; left; reflexivity.
  - specialize (IH ltac:(lia)).
    set (hs := fst (b64_grow_expansion_aux x0 xs)) in *.
    assert (Hlen : length hs = length xs) by apply CascadeTailBound.grow_len.
    assert (HE : rev (firstn (S k) hs) = snd (b64_TwoSum (nth (S k) (x0 :: xs) dz) (CascadeTailBound.acc x0 xs k))
                                         :: rev (firstn k hs)).
    { rewrite rev_firstn_S by lia. unfold hs. rewrite CascadeTailBound.nth_hs by lia. reflexivity. }
    rewrite HE. 
    assert (HQ : CascadeTailBound.acc x0 xs (S k) = fst (b64_TwoSum (nth (S k) (x0 :: xs) dz) (CascadeTailBound.acc x0 xs k))) by reflexivity.
    rewrite HQ.
    assert (Hlt : (S k < length (x0 :: xs))%nat) by (simpl; lia).
    rewrite (skipn_nth_cons (x0 :: xs) (S k) Hlt) in IH.
    set (gj := nth (S k) (x0 :: xs) dz) in *.
    set (q := CascadeTailBound.acc x0 xs k) in *.
    set (E := rev (firstn k hs)) in *.
    destruct IH as [HN | [HT | HP]].
    + (* N *)
      destruct (Nat.lt_ge_cases (S k) (length xs)) as [Lg2 | Nog2].
      * assert (Hlt2 : (S (S k) < length (x0 :: xs))%nat) by (simpl; lia).
        rewrite (skipn_nth_cons (x0 :: xs) (S (S k)) Hlt2) in HN |- *.
        pose proof (N_step_reachable e f x0 xs Pe Pf Fe Ff Nz Hov Hs (S k) E (skipn (S (S (S k))) (x0 :: xs)) ltac:(lia) Lg2) as R0.
        cbv zeta in R0. replace (S k - 1)%nat with k in R0 by lia.
        destruct (R0 HN) as [R | R]; [ left | right; left ]; exact R.
      * assert (Hnil : skipn (S (S k)) (x0 :: xs) = []) by (apply skipn_all2; simpl; lia).
        rewrite Hnil in HN |- *. left. exact (cinv_N_last _ _ _ HN).
    + (* T *)
      destruct k as [| k'].
      { destruct HT as (g & r & Hr & h & E0 & bs0 & L & sg & HE0 & _). unfold E in HE0. cbn in HE0. discriminate. }
      pose proof HT as HT0.
      destruct HT as (g & r & Hr & h & E0 & bs0 & L & sg & HE0 & St & Fg & S0 & Hsg & T).
      injection Hr as Hg Hr'.
      cbv zeta in T. destruct T as (Hg0 & HMc & Hf & HQh & Hh & _).
      assert (HEeq : E = nth k' hs dz :: rev (firstn k' hs)) by (unfold E; apply rev_firstn_S; lia).
      rewrite HEeq in HE0. injection HE0 as Hh1 Hh2.
      assert (Hnh : snd (b64_TwoSum (nth (S k') (x0 :: xs) dz) (CascadeTailBound.acc x0 xs k')) = h)
        by (rewrite <- Hh1; unfold hs; rewrite CascadeTailBound.nth_hs by lia; reflexivity).
      assert (Heq : Rabs (b2r (snd (b64_TwoSum (nth (S k') (x0 :: xs) dz) (CascadeTailBound.acc x0 xs k'))))
                    = ulp radix2 b64_fexp (b2r (nth (S (S k')) (x0 :: xs) dz))).
      { rewrite Hnh. change (nth (S (S k')) (x0 :: xs) dz) with gj. rewrite Hg, ulp_neq_0 by exact Hg0.
        rewrite Hh, Rabs_mult. pose proof (bpow_gt_0 radix2 (cexp radix2 b64_fexp (b2r g))).
        destruct Hsg as [-> | ->]; [ rewrite Rabs_R1 | rewrite (Rabs_left (-1)) by lra ];
          rewrite Rabs_pos_eq by lra; ring. }
      pose proof (T_step_reachable e f x0 xs Pe Pf Fe Ff Nz Hov Hs (S k') (rev (firstn k' hs)) ltac:(lia) Hk) as R0.
      cbv zeta in R0. replace (S k' - 1)%nat with k' in R0 by lia.
      rewrite HEeq, Hh1, <- Hnh in HT0. rewrite HEeq, Hh1, <- Hnh.
      destruct (R0 Heq HT0) as [R | R]; [ left | right; right ]; exact R.
    + (* P *)
      destruct (Nat.lt_ge_cases (S k) (length xs)) as [Lg2 | Nog2].
      * assert (Hlt2 : (S (S k) < length (x0 :: xs))%nat) by (simpl; lia).
        rewrite (skipn_nth_cons (x0 :: xs) (S (S k)) Hlt2) in HP |- *.
        pose proof (P_step_reachable e f x0 xs Pe Pf Fe Ff Nz Hov Hs (S k) E (skipn (S (S (S k))) (x0 :: xs)) ltac:(lia) Lg2) as R0.
        cbv zeta in R0. replace (S k - 1)%nat with k in R0 by lia.
        left. exact (R0 HP).
      * assert (Hnil : skipn (S (S k)) (x0 :: xs) = []) by (apply skipn_all2; simpl; lia).
        rewrite Hnil in HP |- *. left. exact (P_last_step _ _ _ HP).
Qed.

(* RUNG 9b, QED: the full output of the actual recurrence has the aligned
   carry shape -- arbitrary length, no hypothesis beyond Priest validity. *)
Theorem cascade_reachable_shape :
  forall e f x0 xs, cascade_hyps e f x0 xs ->
    exists bs, drop_zeros (cascade_out x0 [] xs) = flat_map cblock_expand bs
               /\ carry_shape bs /\ pairs_aligned bs.
Proof.
  intros e f x0 xs HH.
  pose proof (cascade_stage_invariant e f x0 xs HH (length xs) (Nat.le_refl _)) as I.
  rewrite skipn_all2 in I by (simpl; lia).
  destruct (cinv_final_shape _ _ I) as (bs & H1 & H2 & H3). exists bs.
  split; [ | split; assumption ].
  rewrite <- H1. unfold cascade_out.
  destruct (b64_grow_expansion_aux x0 xs) as [hs q] eqn:Eg.
  pose proof (acc_final xs x0) as Hq. rewrite Eg in Hq. cbn [snd] in Hq. rewrite <- Hq.
  assert (Hl : length hs = length xs) by (pose proof (CascadeTailBound.grow_len xs x0) as L; rewrite Eg in L; exact L).
  cbn [fst]. rewrite <- Hl, firstn_all, app_nil_r. reflexivity.
Qed.

Print Assumptions cascade_reachable_shape.
Print Assumptions cinv_P_step.
Print Assumptions P_step_reachable.
Print Assumptions T_step_reachable.
Print Assumptions N_step_reachable.
Print Assumptions N_to_T_entry.
Print Assumptions cascade_step_obligation_false.
Print Assumptions cinv_N_step.
Print Assumptions cascade_aligned_shape.
