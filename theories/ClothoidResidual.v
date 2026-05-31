(* ============================================================================
   NetTopologySuite.Proofs.ClothoidResidual
   ----------------------------------------------------------------------------
   Strict monotonicity of the clothoid chord-length residual on the monotone
   turning branch -- a Qed-closed CONDITIONAL theorem.

   Context.  The companion (proprietary, source-available) corpus
   `clothoid-halley-coq` (Bertolazzi-Frego G^1 Hermite interpolation,
   Halley-on-L) studies the chord-length residual

       f(L) = L^2 * (P(L)^2 + Q(L)^2) - d^2,

   where, with  psi(tau) = k0 * tau + (k1 - k0) * tau^2 / 2,
       P(L) = \int_0^1 cos(L * psi(tau)) dtau,
       Q(L) = \int_0^1 sin(L * psi(tau)) dtau,
   and d is the chord length.  Its `coq/Clothoid_L.v` proves (Qed, Coquelicot,
   no Admitted) the derivative identities, in particular
       f'(L) = 2 L (P^2 + Q^2) + 2 L^2 (Q R - P T).

   This file states -- in the clean Stdlib lane of NetTopologySuite.Proofs --
   the monotonicity result the Halley/Newton solver depends on for
   well-posedness, as a CONDITIONAL theorem.  The hard analytic content (that
   f' is the derivative of f, and that f' is positive on the monotone branch
   |kappa * L| <= pi) enters as named Section hypotheses -- never as an
   `Admitted` theorem, an `Axiom`, or a `Parameter`.  The companion
   `Clothoid_L.v` is the dischargeable witness for those hypotheses; only the
   STATEMENT crosses the licence
   boundary, and that statement is authored here, BSD-3-Clause from birth (see
   the CROSS-CORPUS BSD-3-CLAUSE BRIDGE clause cited in theories/Azimuth.v).

   This realises the "next concrete Azimuth.v target" named in the
   cross-corpus bridge block of theories/Azimuth.v: the monotone-branch
   precondition |kappa_i * L| <= pi connected to f'(L) > 0 via a
   continuous-turning monotonicity argument.  See docs/audit-phase4-curves.md
   section 6.1 for the bidirectional-bridge status.

   Structural idiom.  Mirrors `hobby_theorem_4_1_conditional`
   (theories-flocq/HobbyTheorem_b64.v) and `overlay_ng_correct_conditional`
   (theories-flocq/OverlayCorrectness.v): the hard lemma is a discharged
   premise, not an Admitted.  The Section-Variable form is used (as in
   OverlayCorrectness) because f, f', kappa, and the two derivative
   hypotheses form a single interface shared by the headline theorem and its
   unique-root corollary; on `End` every theorem becomes universally
   quantified over them.  A Section-bound Variable / Hypothesis is not an
   `Axiom`, a `Parameter`, or an `admit` -- `Print Assumptions` on the closed
   theorems shows only the three classical-reals axioms (see the audit footer).

   The argument itself is ordinary real analysis: Stdlib's mean value theorem
   (`MVT_cor2`) turns a positive derivative on the branch into a positive
   secant slope, hence strict monotonicity, hence at most one root (the
   solver's well-posedness).  No transcendental angle is materialised --
   consistent with Azimuth.v's "sign + ratio only" stance; the branch
   precondition is stated directly with Stdlib `Rabs` / `PI`.

   Pin: clothoid-halley-coq coq/Clothoid_L.v  f'(L)  (companion witness for
        H_deriv and H_fprime_pos; relicensing collapses these hypotheses into
        real lemmas).  Cf. Azimuth.v `turn_sign_eq_cross` per the named
        cross-corpus bridge block.

   No Admitted, no Axiom (except the classical real axioms inherited from the
   corpus's Real.v).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.8)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Ranalysis1.
From Stdlib Require Import MVT.
From NTS.Proofs Require Import Real.
(* Azimuth.v names this file as its downstream cross-corpus target and the
   scholarly bridge (turn_sign_eq_cross, sin_half_turn_sq, miter_ratio_le_iff).
   The monotonicity proof below is self-contained Stdlib analysis; the import
   anchors the dependency direction (ClothoidResidual depends on Azimuth). *)
From NTS.Proofs Require Import Azimuth.

Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* The conditional interface.                                                 *)
(*                                                                            *)
(* `f` is the chord-length residual; `f'` its first derivative; `kappa` the   *)
(* curvature parameter whose product with L bounds the monotone branch.  The  *)
(* two derivative facts are supplied by the consumer (witnessed Qed in the    *)
(* companion clothoid-halley-coq/coq/Clothoid_L.v).                           *)
(* -------------------------------------------------------------------------- *)

Section ClothoidResidualMonotone.

Variable f  : R -> R.
Variable f' : R -> R.
Variable kappa : R.

(* H_deriv: f' is the derivative of f everywhere.  Discharged in
   clothoid-halley-coq via auto_derive + Derive composition, Qed.
   Pin: Clothoid_L.v f'(L). *)
Hypothesis H_deriv : forall L : R, derivable_pt_lim f L (f' L).

(* H_fprime_pos: on the monotone branch |kappa * L| <= pi (and L > 0), the
   derivative is strictly positive.  This is the analytic content the paper
   attributes to a continuous-turning argument; stated here, witnessed in the
   companion corpus.  Pin: Clothoid_L.v f'(L) > 0 on the monotone branch. *)
Hypothesis H_fprime_pos :
  forall L : R, 0 < L -> Rabs (kappa * L) <= PI -> 0 < f' L.

(* -------------------------------------------------------------------------- *)
(* Helper: the branch precondition propagates inward.  If |kappa * L2| <= pi  *)
(* and 0 < c <= L2, then |kappa * c| <= pi.  (|kappa| * c <= |kappa| * L2.)    *)
(* -------------------------------------------------------------------------- *)

Lemma branch_monotone_inward :
  forall c L2 : R,
    0 <= c -> c <= L2 ->
    Rabs (kappa * L2) <= PI ->
    Rabs (kappa * c) <= PI.
Proof.
  intros c L2 Hc0 HcL2 Hbranch.
  rewrite Rabs_mult in *.
  rewrite (Rabs_pos_eq c) by exact Hc0.
  rewrite (Rabs_pos_eq L2) in Hbranch by lra.
  apply Rle_trans with (Rabs kappa * L2); [ | exact Hbranch ].
  apply Rmult_le_compat_l; [ apply Rabs_pos | exact HcL2 ].
Qed.

(* -------------------------------------------------------------------------- *)
(* The Qed-closed headline: strict monotonicity of f on the monotone branch.  *)
(* Pure mean-value-theorem argument relative to the two hypotheses.           *)
(* -------------------------------------------------------------------------- *)

Theorem clothoid_residual_strictly_increasing :
  forall L1 L2 : R,
    0 < L1 ->
    L1 < L2 ->
    Rabs (kappa * L2) <= PI ->
    f L1 < f L2.
Proof.
  intros L1 L2 HL1 HL12 Hbranch.
  (* Mean value theorem: some c in (L1, L2) with the secant = f' c. *)
  destruct (MVT_cor2 f f' L1 L2 HL12 (fun c _ => H_deriv c)) as [c [Hfc Hcin]].
  (* c is interior and positive. *)
  assert (Hc0 : 0 < c) by lra.
  (* The branch holds at c (c <= L2), so the derivative is positive there. *)
  assert (Hcb : Rabs (kappa * c) <= PI).
  { apply (branch_monotone_inward c L2); [ lra | lra | exact Hbranch ]. }
  pose proof (H_fprime_pos c Hc0 Hcb) as Hpos.
  (* Positive slope times positive width = positive rise. *)
  assert (Hrise : 0 < f' c * (L2 - L1)) by (apply Rmult_pos_pos; lra).
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* The corollary the solver actually consumes: at most one root on the        *)
(* branch.  Strict monotonicity => injectivity => the Halley/Newton iteration *)
(* converges to a uniquely-determined L (existence is the IVT side, supplied  *)
(* by the solver's bracketing; uniqueness is exactly this).                   *)
(* -------------------------------------------------------------------------- *)

Corollary clothoid_residual_unique_root :
  forall L1 L2 : R,
    0 < L1 -> 0 < L2 ->
    Rabs (kappa * L1) <= PI ->
    Rabs (kappa * L2) <= PI ->
    f L1 = 0 -> f L2 = 0 ->
    L1 = L2.
Proof.
  intros L1 L2 HL1 HL2 Hb1 Hb2 Hf1 Hf2.
  destruct (Rtotal_order L1 L2) as [Hlt | [Heq | Hgt]].
  - (* L1 < L2: monotonicity forces f L1 < f L2, contradicting f L1 = f L2 = 0. *)
    pose proof (clothoid_residual_strictly_increasing L1 L2 HL1 Hlt Hb2). lra.
  - exact Heq.
  - (* L2 < L1: symmetric. *)
    pose proof (clothoid_residual_strictly_increasing L2 L1 HL2 Hgt Hb1). lra.
Qed.

End ClothoidResidualMonotone.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  On the Section-closed (universally quantified) theorems, the  *)
(* assumptions must be a SUBSET of docs/axiom-allowlist.txt: the three         *)
(* classical-reals axioms only.  f, f', kappa, H_deriv, H_fprime_pos are       *)
(* Section-generalised quantifiers in the theorem TYPE, NOT axioms -- they do  *)
(* not appear here.  If `Print Assumptions` shows an Axiom or Parameter, the   *)
(* file is wrong.                                                             *)
(* -------------------------------------------------------------------------- *)

Print Assumptions clothoid_residual_strictly_increasing.
Print Assumptions clothoid_residual_unique_root.
