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

   STATUS: NOT YET COMPILE-CHECKED when first committed (dependency build
   pending); treat every Qed below as a claim until the smoke job passes.
   Definitions + the induction that makes length irrelevant are
   proved below (Qed, no new axioms beyond the corpus's).  The single OPEN
   obligation is `cascade_step_obligation`: that one TwoSum preserves the
   machine, i.e. that the LOOK-AHEAD conjuncts hold for the next input.
   It is stated as a Definition, never assumed as an Axiom.  Model evidence
   (docs/attacks/2026-11-08-cascade-invariant.md): no violation found. *)
From Stdlib Require Import Reals ZArith Lia Lra List.
From Flocq Require Import IEEE754.Binary Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_lib B64_Pff_bridge
     B64_Expansion B64_FastExpansionSum B64_Overlap_Hierarchy B64_CarryCleanAlgo
     B64_CarryCleanCore B64_CarryCleanLadder B64_CarryCleanOneBit.
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
  - destruct rest as [| g2 r]; [ exact I | ]. destruct Hr as (H0 & F2 & S2).
    repeat split; try assumption. constructor.
Qed.

Print Assumptions cascade_aligned_shape.
