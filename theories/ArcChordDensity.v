(* ============================================================================
   NetTopologySuite.Proofs.ArcChordDensity
   ----------------------------------------------------------------------------
   Route (B) of docs/clothoid-open-questions-triage.md: the sagitta-density
   bound -- "n chords achieve eps" -- the provable face of the Q3
   performance-vs-fidelity trade-off, over the ArcChordApprox.v foundations.

   Mathematical core.  For a valid arc with radius r and half-chord l,
   ArcChordApprox.v's Pythagorean identity pins the sagitta exactly:
   s = r - sqrt(r^2 - l^2).  Multiplying by the conjugate gives

       s * (r + sqrt(r^2 - l^2)) = l^2            (conjugate identity)

   and since the conjugate factor is at least r,

       s * r <= l^2                               (division-free bound)

   so s <= l^2 / r.  Under an n-fold chord refinement on the SAME circle
   each sub-chord's half-length budget is L/n, hence each sub-sagitta is
   bounded by L^2 / (n^2 r): the quadratic density law.  The headline
   `n_chords_achieve_eps` states the count form: any n with
   n^2 * (r * eps) >= L^2 (i.e. n >= L / sqrt(r*eps)) achieves per-chord
   sagitta <= eps.

   Scope honesty.  The statements are per-sub-chord and take the
   refinement interface as hypotheses (each sub-chord lies on the same
   circle, with half-chord budget L/n): the corpus's CircularArc record
   carries no arc parametrisation, so the trigonometric construction of
   the subdivision itself (equal-angle splitting, sin/cos manipulation,
   deferred in ArcChordApprox.v section 6c) is NOT built here.  What is
   proven is the quantitative bound every such subdivision inherits.

   NTS mapping: the chord-count-vs-tolerance law behind curve
   linearisation (NetTopologySuite.Curve / jts-curved consumers;
   cf. PostGIS ST_CurveToLine's segments-per-quadrant knob).  Q3 of the
   clothoid triage records throughput as out of corpus scope; this file
   is the part that IS a theorem.

   No Admitted, no Axiom, no Parameter (allowlist axioms only).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import Psatz.

From NTS.Proofs Require Import Distance.
From NTS.Proofs Require Import CurveGeometry.
From NTS.Proofs Require Import ArcChordApprox.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The conjugate identity: s * (r + sqrt(r^2 - l^2)) = l^2.               *)
(*                                                                            *)
(* Pure algebra over ArcChordApprox.v: under valid_arc the Rmax 0 in          *)
(* sagitta_sq_inner does not trigger (arc_radius_sq_ge_chord_half_length_sq), *)
(* and both sqrt squares collapse via sqrt_sqrt.                              *)
(* -------------------------------------------------------------------------- *)

Lemma sagitta_conjugate_identity :
  forall a : CircularArc,
    valid_arc a ->
    sagitta a * (arc_radius a + sqrt (sagitta_sq_inner a))
      = chord_half_length_sq a.
Proof.
  intros a Hva.
  unfold sagitta.
  rewrite <- arc_radius_eq_sqrt.
  set (q := sqrt (sagitta_sq_inner a)).
  replace ((arc_radius a - q) * (arc_radius a + q))
    with (arc_radius a * arc_radius a - q * q) by ring.
  assert (Hq2 : q * q = sagitta_sq_inner a).
  { unfold q. apply sqrt_sqrt. apply sagitta_sq_inner_nonneg. }
  assert (Hr2 : arc_radius a * arc_radius a = arc_radius_sq a).
  { rewrite arc_radius_eq_sqrt. apply sqrt_sqrt. apply arc_radius_sq_nonneg. }
  rewrite Hq2, Hr2.
  unfold sagitta_sq_inner.
  rewrite Rmax_right.
  - lra.
  - pose proof (arc_radius_sq_ge_chord_half_length_sq a Hva). lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Division-free linear bound: s * r <= l^2.                              *)
(*                                                                            *)
(* The conjugate factor r + sqrt(...) dominates r, and s >= 0; no             *)
(* positivity of r is needed at this stage.                                   *)
(* -------------------------------------------------------------------------- *)

Lemma sagitta_mul_radius_le :
  forall a : CircularArc,
    valid_arc a ->
    sagitta a * arc_radius a <= chord_half_length_sq a.
Proof.
  intros a Hva.
  pose proof (sagitta_conjugate_identity a Hva) as Hc.
  pose proof (sagitta_nonneg a) as Hs.
  pose proof (sqrt_pos (sagitta_sq_inner a)) as Hq.
  nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The eps-budget form: l^2 <= r * eps  =>  s <= eps.                     *)
(* -------------------------------------------------------------------------- *)

Lemma sagitta_le_of_chord_sq_budget :
  forall (a : CircularArc) (eps : R),
    valid_arc a ->
    0 < arc_radius a ->
    chord_half_length_sq a <= arc_radius a * eps ->
    sagitta a <= eps.
Proof.
  intros a eps Hva Hr Hbudget.
  pose proof (sagitta_mul_radius_le a Hva) as Hm.
  apply Rmult_le_reg_r with (r := arc_radius a); [exact Hr | nra].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Quadratic decay: half-chord budget L/n gives sagitta <= l2/(n^2 r).    *)
(*                                                                            *)
(* Stated on the squared budget l2 (no sqrt in the interface): if a           *)
(* sub-chord's squared half-length is within l2/n^2, its sagitta is within    *)
(* l2/(n^2 r) -- subdividing twice as finely buys a 4x tighter tolerance.     *)
(* -------------------------------------------------------------------------- *)

Lemma sagitta_le_quadratic_decay :
  forall (a : CircularArc) (l2 : R) (n : nat),
    valid_arc a ->
    0 < arc_radius a ->
    (1 <= n)%nat ->
    chord_half_length_sq a <= l2 / (INR n * INR n) ->
    sagitta a <= l2 / (INR n * INR n * arc_radius a).
Proof.
  intros a l2 n Hva Hr Hn Hchord.
  assert (Hn0 : 0 < INR n) by (apply lt_0_INR; lia).
  apply sagitta_le_of_chord_sq_budget; [exact Hva | exact Hr | ].
  replace (arc_radius a * (l2 / (INR n * INR n * arc_radius a)))
    with (l2 / (INR n * INR n)).
  - exact Hchord.
  - field. split; apply Rgt_not_eq; nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Headline: n chords achieve eps.                                        *)
(*                                                                            *)
(* Count form, squared interface: with total half-chord budget Lhalf split    *)
(* n ways (each sub-chord's squared half-length <= Lhalf^2/n^2), any n with   *)
(*                                                                            *)
(*     n^2 * (r * eps) >= Lhalf^2      (i.e.  n >= Lhalf / sqrt(r * eps))     *)
(*                                                                            *)
(* brings every sub-chord's sagitta within eps.  This is the chord-count      *)
(* law a lineariser consumes: the required n grows as 1/sqrt(eps), so each    *)
(* extra digit of tolerance costs ~3.2x the chords, not 10x.                  *)
(* -------------------------------------------------------------------------- *)

Theorem n_chords_achieve_eps :
  forall (a : CircularArc) (Lhalf eps : R) (n : nat),
    valid_arc a ->
    0 < arc_radius a ->
    (1 <= n)%nat ->
    chord_half_length_sq a <= (Lhalf * Lhalf) / (INR n * INR n) ->
    Lhalf * Lhalf <= INR n * INR n * (arc_radius a * eps) ->
    sagitta a <= eps.
Proof.
  intros a Lhalf eps n Hva Hr Hn Hchord Hcount.
  assert (Hn0 : 0 < INR n) by (apply lt_0_INR; lia).
  apply sagitta_le_of_chord_sq_budget; [exact Hva | exact Hr | ].
  apply Rle_trans with (Lhalf * Lhalf / (INR n * INR n)); [exact Hchord | ].
  apply Rmult_le_reg_l with (r := INR n * INR n); [nra | ].
  replace (INR n * INR n * (Lhalf * Lhalf / (INR n * INR n)))
    with (Lhalf * Lhalf).
  - nra.
  - field. apply Rgt_not_eq. nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure R algebra over ArcChordApprox.v; allowlist only.        *)
(* -------------------------------------------------------------------------- *)

Print Assumptions sagitta_conjugate_identity.
Print Assumptions sagitta_mul_radius_le.
Print Assumptions sagitta_le_of_chord_sq_budget.
Print Assumptions sagitta_le_quadratic_decay.
Print Assumptions n_chords_achieve_eps.
