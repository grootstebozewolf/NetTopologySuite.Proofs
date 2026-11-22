(* AlpogeTransportSizes.v -- NACK hunt on the two highest-risk QEX calls
   left by the TopShape slice:

     theoremS_transport_link_zero
       LinkSPos.lean:131 (Formalism.L2.SG.ThmSOwn).  Counting constants
       c30 are read at Fm.cOut (hc30, line 141).  The row witness is
       ⟨(sel Fm hc).1, …⟩ (lines 155-157), an ∃ xR inside the member.
       closed_of_th (ThmSOwn.lean:435) takes those two zero functions as
       family-constant side conditions (0 ≤ CGam, 0 ≤ sC', 0 ≤ sCl).
       The lambda does not turn them into an x-tail.
     sizesRec_at
       LinkIRROfJoinEx.lean.  The rpow comparisons used by SizesRec.
       The exponent 9/2 + 10 ε + ε/100 ≤ 5 needs ε < 1/52.
       256 ≤ x^4 needs x ≥ 4.

   The old rpower hypothesis quantified over every function and is
   false.  sizesRec_exponents_r now uses Stdlib Rle_Rpower's statement,
   kept as a hypothesis because its proof needs Classical_Prop.classic.
   link_of_eval follows theoremS_link_of_evaluation (LinkSPos.lean:97).

   Mirror CocoSgt/riemann-hypothesis-lean @ 7cbf7a0, read from source.
   Within docs/axiom-allowlist.txt.  No Admitted.  Not a proof of RH.
   Verdict on the external development: PASS-STATIC / PENDING.

   Evidence for docs/attacks/2026-11-22-alpoge-transport-sizesrec.md.
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human-reviewed by Jeroen Bloemscheer (2026-11-22).
     Assisted-by: Cursor Grok 4.7
*)
From Stdlib Require Import Reals Lra Lia.
Local Open Scope R_scope.

(* ===================================================================== *)
(* sizesRec_at: which exponent comparisons need ε < 1/52, and which do   *)
(* not.  LinkIRROfJoinEx.lean, the rpow_le_rpow_of_exponent_le steps.     *)
(* ===================================================================== *)

(* 9/2 + 10 ε + ε/100 ≤ 5  iff  ε ≤ 50/1001.  1/52 < 50/1001. *)
Theorem sizes_exp_upper : forall eps,
  eps < 1 / 52 -> 9 / 2 + 10 * eps + eps / 100 <= 5.
Proof. intros eps H. lra. Qed.

(* The upper bound is load-bearing.  At ε = 1 the exponent is 14.51 > 5. *)
Theorem sizes_exp_upper_needs_eps :
  ~ (9 / 2 + 10 * 1 + 1 / 100 <= 5).
Proof. lra. Qed.

(* 4 ≤ 9/2 + 10 ε − ε/100 for every ε ≥ 0.  The 1/52 cap is not used. *)
Theorem sizes_exp_lower_4 : forall eps,
  0 <= eps -> 4 <= 9 / 2 + 10 * eps - eps / 100.
Proof. intros eps H. lra. Qed.

(* 2 ≤ 2 + 8 ε − ε/100 for every ε ≥ 0. *)
Theorem sizes_exp_lower_2 : forall eps,
  0 <= eps -> 2 <= 2 + 8 * eps - eps / 100.
Proof. intros eps H. lra. Qed.

(* 256 ≤ x^4 once x ≥ 4, the hx4p step (4^4 = 256). *)
Theorem sizes_pow4_256 : forall x : R, 4 <= x -> 256 <= x * x * x * x.
Proof.
  intros x Hx.
  assert (H2 : 16 <= x * x).
  { replace 16 with (4 * 4) by ring.
    apply Rmult_le_compat; lra. }
  replace 256 with (16 * 16) by ring.
  replace (x * x * x * x) with ((x * x) * (x * x)) by ring.
  apply Rmult_le_compat; lra.
Qed.

(* x = 2 fails the same bound: 2^4 = 16 < 256.  The x ≥ 4 hypothesis
   of sizesRec_at is load-bearing. *)
Theorem sizes_pow4_needs_x : ~ (256 <= 2 * 2 * 2 * 2).
Proof. lra. Qed.

(* 2 * x^5 ≤ x^6 once x ≥ 2, hence once x ≥ 4 (hx65). *)
Theorem sizes_two_x5 : forall x : R, 4 <= x -> 2 * (x * x * x * x * x) <= x * x * x * x * x * x.
Proof.
  intros x Hx.
  replace (x * x * x * x * x * x) with (x * (x * x * x * x * x)) by ring.
  assert (Hx0 : 0 <= x) by lra.
  assert (H5 : 0 <= x * x * x * x * x).
  { apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos|]|]|]; exact Hx0. }
  apply Rmult_le_compat_r; [exact H5|lra].
Qed.

(* LinkIRROfJoinEx.lean hεq: ez/6 ≤ ez/5 − ez/100 once ez ≥ 0
   (ez = eps/J with J ≥ 1). *)
Theorem sizes_ez_sixth : forall ez,
  0 <= ez -> ez / 6 <= ez / 5 - ez / 100.
Proof. intros ez H. lra. Qed.

(* At ez = −1 the same comparison fails.  The sign of ez is load-bearing. *)
Theorem sizes_ez_sixth_needs_nonneg :
  ~ ((-1) / 6 <= (-1) / 5 - (-1) / 100).
Proof. lra. Qed.

(* The previous hypothesis quantified over every rp : R -> R -> R.
   That statement is false: rp _ e := -e sends 0 <= 1 to 0 <= -1. *)
Theorem rpower_mono_not_for_every_fn :
  ~ (forall (rp : R -> R -> R) (x e1 e2 : R),
       1 <= x -> e1 <= e2 -> rp x e1 <= rp x e2).
Proof.
  intro H.
  set (rp := fun (_ e : R) => - e).
  assert (Hle : rp 1 0 <= rp 1 1) by (apply (H rp 1 0 1); lra).
  unfold rp in Hle. lra.
Qed.

Section SizesMono.
(* [Stdlib] Rle_Rpower, read for one function rp.
   The identifier Rpower is not written here: its definition depends on
   Classical_Prop.classic, which is off the allowlist.  The guard 1 <= x
   is the one Rle_Rpower uses.  It is not claimed for every rp. *)
Variable rp : R -> R -> R.
Hypothesis rpower_mono : forall (x e1 e2 : R),
  1 <= x -> e1 <= e2 -> rp x e1 <= rp x e2.

Theorem sizesRec_exponents_r : forall (x eps Cs : R),
  1 <= x -> 4 <= x -> 0 <= eps -> eps < 1 / 52 -> 6 <= Cs ->
  rp x (9 / 2 + 10 * eps + eps / 100) <= rp x 5 /\
  rp x 5 <= rp x Cs /\
  rp x 6 <= rp x Cs /\
  rp x 4 <= rp x (9 / 2 + 10 * eps - eps / 100) /\
  rp x 2 <= rp x (2 + 8 * eps - eps / 100).
Proof.
  intros x eps Cs Hx1 Hx4 He0 He HeCs.
  assert (H5 : 9 / 2 + 10 * eps + eps / 100 <= 5) by (apply sizes_exp_upper; exact He).
  assert (H4 : 4 <= 9 / 2 + 10 * eps - eps / 100) by (apply sizes_exp_lower_4; exact He0).
  assert (H2 : 2 <= 2 + 8 * eps - eps / 100) by (apply sizes_exp_lower_2; exact He0).
  assert (H6 : 6 <= Cs) by exact HeCs.
  assert (H56 : 5 <= Cs) by lra.
  split; [|split; [|split; [|split]]].
  - apply rpower_mono; [exact Hx1|exact H5].
  - apply rpower_mono; [exact Hx1|exact H56].
  - apply rpower_mono; [exact Hx1|exact H6].
  - apply rpower_mono; [exact Hx1|exact H4].
  - apply rpower_mono; [exact Hx1|exact H2].
Qed.
End SizesMono.

(* ===================================================================== *)
(* theoremS_transport_link_zero: the quantifier order                     *)
(* LinkSPos.lean, hRows := ⟨(sel Fm hc).1, fun x hx0 hx i => …⟩          *)
(* and hc30 read at that Fm, not before the member is chosen.            *)
(* ===================================================================== *)

(* xR is the member's own selection threshold.  The index i is the
   Lean `i : Fm.Ix x` of RowsTieP (LinkSPos.lean:156-157). *)
Theorem rows_threshold_inside : forall (sel1 x1 : R) (Ix : R -> Type)
  (P : forall x, Ix x -> Prop),
  (forall (x : R) (i : Ix x), sel1 <= x -> x1 < x -> P x i) ->
  exists xR, xR = sel1 /\ forall (x : R) (i : Ix x), xR <= x -> x1 < x -> P x i.
Proof.
  intros sel1 x1 Ix P H. exists sel1. split; [reflexivity|].
  intros x i Hx H1. apply H; assumption.
Qed.

(* c30 Fm.cOut is applied at Fm.  LinkSPos.lean hc30, used as (hc30 Fm). *)
Theorem counting_constants_at_member : forall (Fam : Type) (C A Cg : Fam -> R),
  (forall Fm, 0 <= C Fm /\ 2 * Cg Fm <= A Fm) ->
  forall Fm, 0 <= C Fm /\ 2 * Cg Fm <= A Fm.
Proof. intros Fam C A Cg H Fm. exact (H Fm). Qed.

Section Transport.
Variable Fam : Type.
Variable InC : Fam -> Prop.
Variable sel1 x1 sCl : Fam -> R.
Variable Ix : Fam -> R -> Type.
Variable RowsAut : Type.
(* LinkSPos.lean:97-102.  TuSize is not a premise of this lemma. *)
Variable LinkS : R -> Fam -> Prop.
Variable RowsTieP : forall (Fm : Fam) (x : R), Ix Fm x -> RowsAut -> Prop.
Variable Cg cb Cu cT CT cC cA c7 cb7 : Fam -> R.
Variable n0 : Fam -> nat.
Variable C0 : R.
(* StandingHypothesesWithConstants, ThmSOwn, CountAllPointsClass. *)
Variable Standing ThmSOwn CountAll : Fam -> Prop.
Hypothesis C0_ge1 : 1 <= C0.
(* [inventory] hc30, read at the member *)
Hypothesis hc30 : forall Fm, InC Fm -> 0 <= cC Fm /\ 2 * Cg Fm <= cA Fm.
Hypothesis sCl_ge2 : forall Fm, InC Fm -> 2 <= sCl Fm.
Hypothesis sCl_twiceC : forall Fm, InC Fm -> 2 * cC Fm <= sCl Fm.
Hypothesis standing_of : forall Fm, InC Fm -> Standing Fm.
Hypothesis thmOwn_of : forall Fm, InC Fm -> ThmSOwn Fm.
Hypothesis countAll_of : forall Fm, InC Fm -> CountAll Fm.
(* [inventory] theoremS_link_of_evaluation, premise for premise.
   hR is ∃ xR, ∀ x ≥ xR, x1 < x → ∀ i, ∃ X : RowsAut, RowsTieP. *)
Hypothesis link_of_eval : forall Fm, InC Fm ->
  1 <= C0 -> 0 <= cC Fm -> 2 * Cg Fm <= cA Fm ->
  2 <= sCl Fm -> 2 * cC Fm <= sCl Fm ->
  Standing Fm ->
  (exists xR, forall (x : R) (i : Ix Fm x),
     xR <= x -> x1 Fm < x -> exists X : RowsAut, RowsTieP Fm x i X) ->
  ThmSOwn Fm -> CountAll Fm ->
  LinkS C0 Fm.

Theorem transport_link_zero_r : forall Fm, InC Fm ->
  (forall (x : R) (i : Ix Fm x), sel1 Fm <= x -> x1 Fm < x ->
     exists X : RowsAut, RowsTieP Fm x i X) ->
  LinkS C0 Fm.
Proof.
  intros Fm HC Hrows.
  destruct (hc30 Fm HC) as [Hc0 HcA].
  assert (Hpack : exists xR : R, forall (x : R) (i : Ix Fm x),
      xR <= x -> x1 Fm < x -> exists X : RowsAut, RowsTieP Fm x i X).
  { exists (sel1 Fm). intros x i Hx Hlt. exact (Hrows x i Hx Hlt). }
  apply link_of_eval; [exact HC|exact C0_ge1|exact Hc0|exact HcA|
    apply sCl_ge2; exact HC|apply sCl_twiceC; exact HC|
    apply standing_of; exact HC|exact Hpack|
    apply thmOwn_of; exact HC|apply countAll_of; exact HC].
Qed.
End Transport.

(* The swapped order — one xR for every member — does not follow.
   Two thresholds, 0 and 3: xR = 0 serves the first and misses the second
   at x = 1; there is still a uniform xR (namely 3) for a finite set.
   An infinite unbounded family is the real obstruction; stating it here
   would call the archimedean axiom, which is not on the allowlist.
   The finite illustration is the control that a threshold chosen for one
   member need not serve another. *)
Theorem threshold_of_one_misses_another :
  let sel1 := 0 in let sel2 := 3 in
  (forall x : R, sel1 <= x -> x <= x) /\
  ~ (forall x : R, sel1 <= x -> sel2 <= x).
Proof.
  simpl. split; [intros; lra|].
  intro H. specialize (H 1). lra.
Qed.

Print Assumptions sizes_exp_upper.
Print Assumptions sizes_exp_upper_needs_eps.
Print Assumptions sizes_pow4_256.
Print Assumptions sizes_pow4_needs_x.
Print Assumptions sizes_two_x5.
Print Assumptions sizes_ez_sixth.
Print Assumptions sizes_ez_sixth_needs_nonneg.
Print Assumptions sizes_exp_lower_4.
Print Assumptions sizes_exp_lower_2.
Print Assumptions rpower_mono_not_for_every_fn.
Print Assumptions sizesRec_exponents_r.
Print Assumptions counting_constants_at_member.
Print Assumptions rows_threshold_inside.
Print Assumptions transport_link_zero_r.
Print Assumptions threshold_of_one_misses_another.
