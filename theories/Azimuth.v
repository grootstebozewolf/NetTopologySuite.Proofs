(* ============================================================================
   NetTopologySuite.Proofs.Azimuth
   ----------------------------------------------------------------------------
   Turning-angle decisions for buffer joins, offset curves, and snap-rounding
   direction compatibility -- expressed without a transcendental angle.

   The motivation.  NTS `BufferParameters` chooses miter / bevel / round joins
   based on (a) the sign of the turn at each polyline vertex (left / right /
   collinear) and (b) the magnitude of the half-turn (via the miter-ratio
   cap `1 / sin(theta/2) <= miter_limit`).  Both decisions are sign-and-
   ratio decisions, not angle-of-rotation decisions -- so we do not need to
   materialise `atan2 (vcross u v) (vdot u v)` as a first-class Coq term.
   Stdlib `Reals` does not even ship `atan2`; defining it here would force
   a quadrant case-split that buys no operational information for the
   `BufferParameters` join logic.

   Instead this file exposes two primitives on `Vec`:

     - `turn_sign u v := vcross u v`          -- signed area of the
                                                  parallelogram spanned by
                                                  u and v.  Decides
                                                  left-turn (positive),
                                                  right-turn (negative),
                                                  or collinear (zero).
     - `sin_half_turn u v`                    -- |sin(theta / 2)| where
                                                  theta is the unsigned
                                                  angle between u and v.
                                                  Always in [0, 1].
                                                  Its reciprocal is the
                                                  miter-length multiplier
                                                  in `BufferParameters`.

   The C# host (NetTopologySuite.Curve / BufferParameters) computes the
   actual numeric angle via `Math.Atan2 (vcross, vdot)` for golden-vector
   tests and for visualisation; this file verifies only the operational
   decisions it derives.

   PROOF STATUS
   ============
   - `turn_sign_antisym`                : turn_sign u v = - turn_sign v u.
   - `turn_sign_zero_iff_parallel`      : turn_sign u v = 0 <-> parallel u v.
   - `turn_sign_eq_cross`               : on three points P0, P1, P2,
                                          the Vec-side turn sign of the
                                          consecutive edge vectors equals
                                          the Point-side `cross` from
                                          `Orientation.v`.  Bridge to NTS
                                          `Orientation.Index` decisions.
   - `vdot_abs_le_vmag_mult`            : Cauchy-Schwarz in unsquared form.
   - `vdot_le_vmag_mult`,
     `vdot_ge_neg_vmag_mult`            : the two directional bounds derived
                                          from the absolute-value form.
   - `sin_half_turn_nonneg`             : 0 <= sin_half_turn u v.
   - `sin_half_turn_sq`                 : (sin_half_turn u v) ^ 2
                                          = (1 - vdot u v / (vmag u * vmag v))
                                            / 2
                                          on non-zero u, v.
   - `miter_ratio_le_iff`               : on non-zero u, v and miter_limit > 0,
                                          1 <= miter_limit * sin_half_turn u v
                                          <-> sin_half_turn u v >= / miter_limit.
                                          The operational form of the
                                          BufferParameters miter cap, with
                                          no division by zero in either
                                          direction.

   Two further nice-to-have lemmas (`sin_half_turn_le_one`,
   `sin_half_turn_zero_aligned`) are documented as deferred at the foot
   of the file.  They are true but their closing `lra` call does not
   fire in this Rocq 9.1.1 context; they are NOT load-bearing for the
   NTS BufferParameters decisions (sign + miter cap).

   What is *not* proved (intentionally):

     - No `atan2` definition or `(-pi, pi]` range bound.  See header for
       the motivation; this is the "Sign + ratio only" path.
     - No `R`-valued `signed_turn_angle`.  The C# host computes
       `Math.Atan2 (vcross, vdot)` for display; Coq verifies the
       decisions derived from it.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From NTS.Proofs Require Import Distance.
From NTS.Proofs Require Import Orientation.
From NTS.Proofs Require Import Vec.
From NTS.Proofs Require Import Direction.

Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Bridge: Point-difference as a Vec.  Records have distinct field names so   *)
(* no implicit coercion is possible -- this helper makes the lift explicit.   *)
(* -------------------------------------------------------------------------- *)

Definition point_diff (P Q : Point) : Vec :=
  mkVec (px P - px Q) (py P - py Q).

(* -------------------------------------------------------------------------- *)
(* Turn sign.  Signed area of the parallelogram spanned by u and v.           *)
(* NTS convention: positive = CCW = left turn.                                *)
(* -------------------------------------------------------------------------- *)

Definition turn_sign (u v : Vec) : R := vcross u v.

Lemma turn_sign_antisym :
  forall u v, turn_sign u v = - turn_sign v u.
Proof. intros u v. unfold turn_sign. apply vcross_antisym. Qed.

Lemma turn_sign_zero_iff_parallel :
  forall u v, turn_sign u v = 0 <-> parallel u v.
Proof.
  intros u v. unfold turn_sign.
  symmetry. apply parallel_iff_vcross_zero.
Qed.

(* -------------------------------------------------------------------------- *)
(* Sign-agreement bridge to NTS Orientation.Index.  Given three points        *)
(* P0, P1, P2 with consecutive edge vectors u = P1 - P0 and v = P2 - P1,     *)
(* the Vec-side turn sign equals the Point-side `cross P0 P1 P2`.             *)
(* (The "(P2 - P0).y" pieces in `cross` cancel with the "(P2 - P1).x" pieces *)
(* in `vcross` -- it really is the same polynomial in the six coordinates.)  *)
(* -------------------------------------------------------------------------- *)

Lemma turn_sign_eq_cross :
  forall P0 P1 P2 : Point,
    turn_sign (point_diff P1 P0) (point_diff P2 P1) = cross P0 P1 P2.
Proof.
  intros P0 P1 P2.
  unfold turn_sign, vcross, point_diff, cross. simpl. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Magnitude (unsquared).  Vec.v exposes `vmag_sq` only; the half-angle      *)
(* formula's denominator wants the unsquared form.  Defined here as a       *)
(* convenience helper.                                                        *)
(* -------------------------------------------------------------------------- *)

Definition vmag (v : Vec) : R := sqrt (vmag_sq v).

Lemma vmag_nonneg : forall v, 0 <= vmag v.
Proof. intros v. unfold vmag. apply sqrt_pos. Qed.

Lemma vmag_pos_iff_nonzero :
  forall v, 0 < vmag v <-> v <> vzero.
Proof.
  intros v. unfold vmag. split.
  - intros Hpos Heq. subst.
    rewrite (proj2 (vmag_sq_zero_iff vzero) (eq_refl _)) in Hpos.
    rewrite sqrt_0 in Hpos. lra.
  - intros Hne.
    assert (Hsq : 0 < vmag_sq v).
    { destruct (Rle_lt_or_eq_dec 0 (vmag_sq v) (vmag_sq_nonneg v)) as [Hlt | Heq].
      - exact Hlt.
      - symmetry in Heq. apply vmag_sq_zero_iff in Heq. contradiction. }
    apply sqrt_lt_R0. exact Hsq.
Qed.

Lemma vmag_mult_nonneg : forall u v, 0 <= vmag u * vmag v.
Proof.
  intros u v.
  apply Rmult_le_pos; apply vmag_nonneg.
Qed.

Lemma vmag_mult_pos :
  forall u v, u <> vzero -> v <> vzero -> 0 < vmag u * vmag v.
Proof.
  intros u v Hu Hv.
  apply Rmult_lt_0_compat.
  - apply vmag_pos_iff_nonzero. exact Hu.
  - apply vmag_pos_iff_nonzero. exact Hv.
Qed.

(* Cauchy-Schwarz in unsquared form: |vdot| <= vmag u * vmag v. *)
Lemma vdot_abs_le_vmag_mult :
  forall u v, Rabs (vdot u v) <= vmag u * vmag v.
Proof.
  intros u v.
  pose proof (cauchy_schwarz_sq u v) as HCS.
  pose proof (vmag_nonneg u) as Hu.
  pose proof (vmag_nonneg v) as Hv.
  apply Rsqr_incr_0;
    [ | apply Rabs_pos | apply Rmult_le_pos; assumption ].
  (* Main goal: (Rabs (vdot u v))² <= (vmag u * vmag v)² *)
  rewrite <- Rsqr_abs.
  unfold Rsqr.
  replace ((vmag u * vmag v) * (vmag u * vmag v))
    with (vmag u * vmag u * (vmag v * vmag v)) by ring.
  unfold vmag.
  rewrite sqrt_def by apply vmag_sq_nonneg.
  rewrite sqrt_def by apply vmag_sq_nonneg.
  exact HCS.
Qed.

(* Directional Cauchy-Schwarz bounds: avoid the abs-le-iff dance in       *)
(* downstream proofs by exposing the upper and lower bounds directly.    *)
Lemma vdot_le_vmag_mult :
  forall u v, vdot u v <= vmag u * vmag v.
Proof.
  intros u v.
  pose proof (vdot_abs_le_vmag_mult u v) as Habs.
  pose proof (Rle_abs (vdot u v)) as Hle.
  lra.
Qed.

Lemma vdot_ge_neg_vmag_mult :
  forall u v, - (vmag u * vmag v) <= vdot u v.
Proof.
  intros u v.
  pose proof (vdot_abs_le_vmag_mult u v) as Habs.
  pose proof (Rle_abs (- vdot u v)) as Hle.
  rewrite Rabs_Ropp in Hle.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Half-turn sine.  |sin(theta/2)| via the half-angle identity                *)
(*    sin^2(theta/2) = (1 - cos theta) / 2                                    *)
(* with cos theta = vdot u v / (vmag u * vmag v).                             *)
(*                                                                            *)
(* Defined unconditionally; on a zero vector the denominator becomes 0,      *)
(* Coq's Rdiv_0_r gives 0, and the formula collapses to sqrt(1/2).  Lemmas  *)
(* below that depend on a meaningful cos-theta carry an explicit non-zero    *)
(* hypothesis on both inputs.                                                *)
(* -------------------------------------------------------------------------- *)

Definition sin_half_turn (u v : Vec) : R :=
  sqrt ((1 - vdot u v / (vmag u * vmag v)) / 2).

Lemma sin_half_turn_nonneg :
  forall u v, 0 <= sin_half_turn u v.
Proof. intros u v. unfold sin_half_turn. apply sqrt_pos. Qed.

(* Algebraic identity for the squared half-turn sine on non-zero inputs.    *)
(* Useful as a rewriting target when downstream callers want to square     *)
(* the operational miter test out of the sqrt.                              *)
Lemma sin_half_turn_sq :
  forall u v,
    u <> vzero -> v <> vzero ->
    (sin_half_turn u v) ^ 2
      = (1 - vdot u v / (vmag u * vmag v)) / 2.
Proof.
  intros u v Hu Hv.
  pose proof (vmag_mult_pos u v Hu Hv) as Hpos.
  pose proof (vdot_le_vmag_mult u v) as Hhi.
  assert (Hnn : 0 <= (1 - vdot u v / (vmag u * vmag v)) / 2).
  { apply (Rmult_le_compat_r (/ (vmag u * vmag v))) in Hhi;
      [| left; apply Rinv_0_lt_compat; exact Hpos ].
    rewrite Rinv_r in Hhi by lra.
    unfold Rdiv. lra. }
  unfold sin_half_turn.
  replace ((sqrt ((1 - vdot u v / (vmag u * vmag v)) / 2)) ^ 2)
    with (sqrt ((1 - vdot u v / (vmag u * vmag v)) / 2)
        * sqrt ((1 - vdot u v / (vmag u * vmag v)) / 2)) by ring.
  apply sqrt_def. exact Hnn.
Qed.

(* Two further "nice to have" lemmas would round out the API:                *)
(*                                                                            *)
(*   sin_half_turn_le_one       : forall u v, sin_half_turn u v <= 1.        *)
(*   sin_half_turn_zero_aligned : on non-zero inputs,                        *)
(*                                  sin_half_turn u v = 0                   *)
(*                                  -> parallel u v /\ 0 < vdot u v.        *)
(*                                                                            *)
(* Both are true but require chained Cauchy-Schwarz inverse manipulation     *)
(* whose closing `lra` call presently doesn't fire in this Rocq 9.1.1        *)
(* context (lra reproduces fine in isolation; the in-proof context is        *)
(* introducing something the witness search can't handle).  Deferred --     *)
(* they are not load-bearing for the NTS BufferParameters decisions          *)
(* (sign + miter cap), which compose only the lemmas below.                  *)

(* -------------------------------------------------------------------------- *)
(* Miter-ratio cap.  The operational form of the BufferParameters miter     *)
(* test, biconditional in `sin_half_turn`, with no division by zero in      *)
(* either direction.                                                          *)
(* -------------------------------------------------------------------------- *)

Lemma miter_ratio_le_iff :
  forall u v miter_limit,
    u <> vzero -> v <> vzero ->
    0 < miter_limit ->
    (1 <= miter_limit * sin_half_turn u v
       <-> / miter_limit <= sin_half_turn u v).
Proof.
  intros u v L Hu Hv HL.
  split.
  - intros H.
    (* 1 <= L * s   ->  / L <= s.  Multiply both sides by / L > 0. *)
    apply (Rmult_le_reg_l L); [ exact HL | ].
    rewrite Rinv_r by lra.
    exact H.
  - intros H.
    (* / L <= s   ->  1 <= L * s.  Multiply both sides by L > 0.   *)
    apply (Rmult_le_compat_l L) in H; [ | lra ].
    rewrite Rinv_r in H by lra.
    exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* Cross-corpus bridge to clothoid-halley-coq (v1.0.3, retitled                *)
(* "A Verified-Azimuth, Zero-Friction Halley Solver for the Chord-Length      *)
(* Parameter L in Clothoid G^1 Hermite Interpolation").                       *)
(*                                                                            *)
(* The companion proprietary corpus at                                         *)
(*   https://github.com/grootstebozewolf/clothoid-halley-coq                 *)
(* now cites three lemmas from this file -- `turn_sign_eq_cross`,            *)
(* `sin_half_turn_sq`, `miter_ratio_le_iff` -- as scholarly references in    *)
(* its Section 7 ("Cross-Corpus Bridge to NetTopologySuite").  The bridge    *)
(* is documented as a *zero-friction call-site substitution*: production    *)
(* pipelines that already use NetTopologySuite get the verified-azimuth     *)
(* semantics without any porting effort.                                      *)
(*                                                                            *)
(* Licence note.  The clothoid-halley-coq paper is proprietary               *)
(* (LicenseRef-Merkator-Proprietary-NoAITraining) but its LICENSE explicitly *)
(* preserves the BSD-3-Clause status of this file: the CROSS-CORPUS          *)
(* BSD-3-CLAUSE BRIDGE clause states that "the theorem statements, function *)
(* signatures, and other identifying excerpts of the Sibling Corpus that    *)
(* the paper reproduces ... remain governed by the BSD-3-Clause licence of  *)
(* the Sibling Corpus."  See docs/audit-phase4-curves.md \S 6.1 for the     *)
(* full bidirectional-bridge status.                                          *)
(*                                                                            *)
(* Sibling-corpus target -- LANDED.  The clothoid paper's monotone-branch     *)
(* precondition `|kappa_i * L| <= pi` is connected to `f'(L) > 0` via a       *)
(* continuous-turning monotonicity argument that "lives naturally in          *)
(* Azimuth.v" (paper's wording, Section 7).  That result is now stated and    *)
(* Qed-closed CONDITIONALLY in theories/ClothoidResidual.v                    *)
(* (`clothoid_residual_strictly_increasing` + the unique-root corollary):     *)
(* the derivative identities enter as named Section hypotheses (H_deriv,      *)
(* H_fprime_pos), witnessed Qed in clothoid-halley-coq/coq/Clothoid_L.v;      *)
(* only the BSD-3-Clause statement lives here.  Consistent with this file's   *)
(* "sign + ratio only" stance, the branch is stated directly via Stdlib       *)
(* `Rabs` / `PI` rather than a materialised turning angle.  Collapsing the    *)
(* hypotheses into real lemmas (porting the witness across the licence        *)
(* boundary) is the follow-up if the relicensing decision is taken.          *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                              *)
(* -------------------------------------------------------------------------- *)

Print Assumptions turn_sign_antisym.
Print Assumptions turn_sign_zero_iff_parallel.
Print Assumptions turn_sign_eq_cross.
Print Assumptions vmag_nonneg.
Print Assumptions vmag_pos_iff_nonzero.
Print Assumptions vdot_abs_le_vmag_mult.
Print Assumptions vdot_le_vmag_mult.
Print Assumptions vdot_ge_neg_vmag_mult.
Print Assumptions sin_half_turn_nonneg.
Print Assumptions sin_half_turn_sq.
Print Assumptions miter_ratio_le_iff.
