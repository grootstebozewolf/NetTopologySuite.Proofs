(* ============================================================================
   NetTopologySuite.Proofs.ClothoidDegenerate
   ----------------------------------------------------------------------------
   The degenerate straight-chord regime of the clothoid chord-length residual
   -- the one EXACT sub-regime, and a non-vacuity witness for the conditional
   interface of theories/ClothoidResidual.v.  Route (A) of
   docs/clothoid-open-questions-triage.md.

   Context.  ClothoidResidual.v proves monotone-branch uniqueness of the
   residual f(L) = L^2 * (P(L)^2 + Q(L)^2) - d^2 CONDITIONALLY: f, f', kappa
   are Section Variables and the analytic facts (H_deriv, H_fprime_pos,
   H_mvt) are named hypotheses, externally witnessed in the companion
   clothoid-halley-coq corpus (Coquelicot).  In the degenerate regime
   k0 = k1 = 0 the turning angle psi vanishes identically, so the
   Fresnel-like integrals collapse on the nose:

       P(L) = \int_0^1 cos 0 dtau = 1,     Q(L) = \int_0^1 sin 0 dtau = 0,

   and the residual is the bare polynomial

       f_deg(L) = L^2 - d^2,

   with derivative f_deg'(L) = 2L.  No transcendental function survives, so
   this regime admits what the general regime cannot (see the triage doc's
   Q2 analysis): EXACT statements with no approximation, no rounding, and no
   appeal to the mean value theorem's classical proof -- the MVT witness for
   a quadratic is constructively c = (a+b)/2.

   This file delivers two things:

   1. The exact-root headline for the degenerate regime: L = d is the unique
      positive root of f_deg (degenerate_root_exact,
      degenerate_unique_positive_root) -- proved directly, no interface.

   2. NON-VACUITY of ClothoidResidual.v's conditional interface: all three
      Section hypotheses are discharged concretely for f_deg with kappa = 0
      (degenerate_H_deriv, degenerate_H_fprime_pos, degenerate_H_mvt -- the
      last WITHOUT Classical_Prop.classic, by exhibiting the midpoint), and
      the Section-closed theorems are instantiated end-to-end
      (degenerate_unique_root_via_interface).  The conditional headline is
      therefore inhabited: its hypotheses are not mutually unsatisfiable.
      Cf. the corpus's RED non-vacuity idiom (GeneralTriangleParityRED.v).

   Queued (NOT this file): the binary64 mirror -- for integer-valued d the
   root L = d is exactly representable and the residual evaluation is exact
   in the 2^26 window, mirroring the `_small_int` headline pattern of
   theories-flocq/Orient_b64_exact.v.  See the triage doc, route (A).

   NTS mapping: the straight-chord fast path of a clothoid G^1 Hermite
   solver (clothoid-halley-coq, public EUPL-1.2 repro), consumed through the
   RelateClothoid.v chord carrier on the NetTopologySuite.Curve side.

   No Admitted, no Axiom (except the classical real axioms inherited from the
   corpus's Real.v).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Psatz.
From Stdlib Require Import Ranalysis1.   (* derivable_pt_lim *)
From NTS.Proofs Require Import Real.
From NTS.Proofs Require Import ClothoidResidual.

Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* The degenerate residual and its derivative.                                *)
(* -------------------------------------------------------------------------- *)

Definition degenerate_residual (d : R) (L : R) : R := L * L - d * d.

Definition degenerate_residual' (d : R) (L : R) : R := 2 * L.

(* -------------------------------------------------------------------------- *)
(* Part 1 -- the exact-root headline, proved directly.                        *)
(* -------------------------------------------------------------------------- *)

(* The chord length d itself is a root: f_deg(d) = d^2 - d^2 = 0.  On the
   nose -- no approximation enters at any point. *)
Lemma degenerate_root_exact :
  forall d : R, degenerate_residual d d = 0.
Proof.
  intro d. unfold degenerate_residual. ring.
Qed.

(* Strict monotonicity on L > 0, directly (no MVT): L1^2 < L2^2. *)
Lemma degenerate_strictly_increasing :
  forall d L1 L2 : R,
    0 < L1 -> L1 < L2 ->
    degenerate_residual d L1 < degenerate_residual d L2.
Proof.
  intros d L1 L2 HL1 HL12. unfold degenerate_residual. nra.
Qed.

(* The unique positive root is L = d (for a positive chord).  This is the
   exact answer the Halley iteration would converge to: in the degenerate
   regime the solver's fixpoint is available in closed form. *)
Theorem degenerate_unique_positive_root :
  forall d L : R,
    0 < d -> 0 < L ->
    degenerate_residual d L = 0 ->
    L = d.
Proof.
  intros d L Hd HL Hroot. unfold degenerate_residual in Hroot. nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Part 2 -- discharging the ClothoidResidual.v interface concretely.         *)
(*                                                                            *)
(* kappa = 0: the branch precondition |kappa * L| <= pi is trivially true     *)
(* everywhere, so the degenerate regime lies entirely on the monotone branch. *)
(* -------------------------------------------------------------------------- *)

(* H_deriv, concretely: the derivative of L*L - d*d at L is 2*L.  Assembled
   from Stdlib's derivability algebra (id * id, minus a constant). *)
Lemma degenerate_H_deriv :
  forall d L : R,
    derivable_pt_lim (degenerate_residual d) L (degenerate_residual' d L).
Proof.
  intros d L.
  unfold degenerate_residual, degenerate_residual'.
  replace (2 * L) with (1 * L + L * 1 - 0) by ring.
  apply (derivable_pt_lim_minus (fun x => x * x) (fun _ => d * d)).
  - apply (derivable_pt_lim_mult (fun x => x) (fun x => x)).
    + apply derivable_pt_lim_id.
    + apply derivable_pt_lim_id.
  - apply derivable_pt_lim_const.
Qed.

(* H_fprime_pos, concretely (with kappa = 0): 2L > 0 for L > 0. *)
Lemma degenerate_H_fprime_pos :
  forall d L : R,
    0 < L -> Rabs (0 * L) <= PI ->
    0 < degenerate_residual' d L.
Proof.
  intros d L HL _. unfold degenerate_residual'. lra.
Qed.

(* The branch precondition itself is trivial at kappa = 0 -- every L > 0 is
   on the monotone branch, so the interface's guard never bites here. *)
Lemma degenerate_branch_trivial :
  forall L : R, Rabs (0 * L) <= PI.
Proof.
  intro L.
  rewrite Rmult_0_l, Rabs_R0.
  pose proof PI_RGT_0. lra.
Qed.

(* H_mvt, concretely -- and CONSTRUCTIVELY.  For the quadratic residual the
   mean value witness on [a, b] is the midpoint c = (a+b)/2:

       f b - f a = b^2 - a^2 = (a+b)(b-a) = (2 * (a+b)/2) * (b - a).

   Stdlib's MVT_cor2 would pull Classical_Prop.classic (see the
   ClothoidResidual.v header); exhibiting the midpoint keeps this file on
   the corpus's three-axiom allowlist. *)
Lemma degenerate_H_mvt :
  forall d a b : R,
    a < b ->
    (forall c : R, a <= c <= b ->
       derivable_pt_lim (degenerate_residual d) c (degenerate_residual' d c)) ->
    exists c : R,
      degenerate_residual d b - degenerate_residual d a
        = degenerate_residual' d c * (b - a)
      /\ a < c < b.
Proof.
  intros d a b Hab _.
  exists ((a + b) / 2).
  split.
  - unfold degenerate_residual, degenerate_residual'. field.
  - lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* The non-vacuity payoff: the Section-closed conditional theorems of         *)
(* ClothoidResidual.v, instantiated end-to-end with the degenerate residual.  *)
(* Every hypothesis of the conditional headline is discharged by a Qed lemma  *)
(* above -- the interface is inhabited, hence not mutually unsatisfiable.     *)
(* -------------------------------------------------------------------------- *)

Theorem degenerate_strictly_increasing_via_interface :
  forall d L1 L2 : R,
    0 < L1 -> L1 < L2 ->
    Rabs (0 * L2) <= PI ->
    degenerate_residual d L1 < degenerate_residual d L2.
Proof.
  intros d.
  apply (clothoid_residual_strictly_increasing
           (degenerate_residual d) (degenerate_residual' d) 0
           (degenerate_H_deriv d)
           (degenerate_H_fprime_pos d)
           (degenerate_H_mvt d)).
Qed.

Theorem degenerate_unique_root_via_interface :
  forall d L1 L2 : R,
    0 < L1 -> 0 < L2 ->
    degenerate_residual d L1 = 0 ->
    degenerate_residual d L2 = 0 ->
    L1 = L2.
Proof.
  intros d L1 L2 HL1 HL2 Hf1 Hf2.
  apply (clothoid_residual_unique_root
           (degenerate_residual d) (degenerate_residual' d) 0
           (degenerate_H_deriv d)
           (degenerate_H_fprime_pos d)
           (degenerate_H_mvt d)
           L1 L2 HL1 HL2
           (degenerate_branch_trivial L1)
           (degenerate_branch_trivial L2)
           Hf1 Hf2).
Qed.

(* Consistency: the interface route and the direct route agree on the
   closed-form answer. *)
Corollary degenerate_root_is_chord_length :
  forall d L : R,
    0 < d -> 0 < L ->
    degenerate_residual d L = 0 ->
    L = d.
Proof.
  intros d L Hd HL Hroot.
  apply (degenerate_unique_root_via_interface d L d HL Hd Hroot
           (degenerate_root_exact d)).
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Everything above must show a SUBSET of the three             *)
(* classical-reals axioms (docs/axiom-allowlist.txt).  In particular          *)
(* degenerate_H_mvt and the two _via_interface theorems must NOT show         *)
(* Classical_Prop.classic: the MVT witness is exhibited, not deduced.         *)
(* -------------------------------------------------------------------------- *)

Print Assumptions degenerate_root_exact.
Print Assumptions degenerate_unique_positive_root.
Print Assumptions degenerate_H_deriv.
Print Assumptions degenerate_H_mvt.
Print Assumptions degenerate_strictly_increasing_via_interface.
Print Assumptions degenerate_unique_root_via_interface.
Print Assumptions degenerate_root_is_chord_length.
