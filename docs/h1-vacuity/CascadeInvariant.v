(* CascadeInvariant.v -- the arbitrary-length cascade invariant on `bstate`.

   The cascade is  (Q', h) := TwoSum(g, Q)  over the ascending-sorted merge
   g_1 <= g_2 <= ... of two Priest chains.  `bstate Q E L bs` (OneBit) is
   length-free but each step lemma needs a LOOK-AHEAD fact about the NEXT
   input g.  The invariant is a three-state machine:

     N  ordinary : bstate, every block key < ulp(g_next)            [bstate_step]
     T  tie      : the top error h = s*2^c = s*ulp(g_next) and Q = s*2^M,
                   the TwoSum will land on a midpoint               [bstate_tie]
     P  pending twin : Q = h, newest error 0, |h| = 2^c,
                   4*2^c <= ulp(g_next)                             [bstate_twin]

   STATUS: compiles against the built corpus (Rocq 9.2; axioms: Reals +
   classic + funext, as the corpus); needs CascadeTailBound compiled first
   with -Q docs/h1-vacuity NTS.Proofs.Probes (scripts/hunt_probe_smoke.sh).
   N -> T ENTRY PROVED (N_to_T_entry, on the actual cascade of two Priest
   chains).  N -> N needs only the strict look-ahead (cinv_N_step).
   Definitions + the induction that makes length irrelevant are
   proved below (Qed, no new axioms beyond the corpus's).  The single OPEN
   obligation is `cascade_step_obligation`: that one TwoSum preserves the
   machine, i.e. that the LOOK-AHEAD conjuncts hold for the next input.
   It is stated as a Definition, never assumed as an Axiom.  Model evidence
   (docs/attacks/2026-11-08-cascade-invariant.md): no violation found. *)
From Stdlib Require Import Reals ZArith Lia Lra List Permutation.
From Flocq Require Import IEEE754.Binary Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_lib B64_Pff_bridge
     B64_Expansion B64_FastExpansionSum B64_Overlap_Hierarchy B64_CarryCleanAlgo
     B64_CarryCleanCore B64_CarryCleanLadder B64_CarryCleanOneBit B64_FastExpansionSum_Shewchuk.
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

(* On the actual cascade: N state + look-ahead equality => T state. *)
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

Print Assumptions N_to_T_entry.
Print Assumptions cinv_N_step.
Print Assumptions cascade_aligned_shape.
