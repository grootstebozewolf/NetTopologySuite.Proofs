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
     cascade_step_obligation_false: the step obligation as stated (over
       ARBITRARY (Q, E, rest)) is FALSE -- Q = 1, g = 2^54, next 2^-100.

   VACUOUS  cascade_aligned_shape is Qed but conditional on
     cascade_step_obligation, which is refuted.  Not citable.  A usable form
     must quantify over reachable states (as N_step_reachable does).

   OPEN  T -> {N, P, anti}, P -> N, and the p = 2 pending-twin equality
     (model only: 4*2^c = ulp(g_next) is reached at p = 2).

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
    as (sg & Hsg & HQ & Hh & HMc & Hf & _ & Hle & Hgl).
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

Print Assumptions N_step_reachable.
Print Assumptions N_to_T_entry.
Print Assumptions cascade_step_obligation_false.
Print Assumptions cinv_N_step.
Print Assumptions cascade_aligned_shape.
