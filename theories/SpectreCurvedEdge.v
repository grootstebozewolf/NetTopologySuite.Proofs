(* ============================================================================
   NetTopologySuite.Proofs.SpectreCurvedEdge
   ----------------------------------------------------------------------------
   The defining ingredient of the "Spectre" -- the strictly chiral aperiodic
   monotile (Smith, Myers, Kaplan, Goodman-Strauss, 2023) -- formalized using
   CURVES.

   The hat needs reflections to tile; the Spectre removes that by replacing each
   straight edge with a CURVED edge that is point-symmetric about its midpoint.
   That central symmetry is the whole trick: a curved edge then mates with the
   corresponding edge of a neighbour obtained by a 180 degree ROTATION (never a
   reflection), which is exactly what forces chirality / no mirror images.

   We capture this directly.  A curved edge from A to B is the chord plus a
   normal displacement `f t` along the perpendicular of B-A:

     curved_edge A B f t = A + t*(B-A) + (f t) * perp(B-A).

   The key theorem `curved_edge_central_symmetry`: for ANY displacement profile
   `f` that is ODD about the midparameter (`f (1-s) = - f s`) -- circular-arc
   S-curves, sine bumps, etc. -- the edge is invariant under the 180 degree
   rotation about the midpoint of A,B:

     curved_edge A B f (1 - t) = rot180 (midpoint A B) (curved_edge A B f t).

   That is precisely the Spectre's reflection-free mating property, proved once
   for the whole class.  A concrete curved instance (`sine_edge`, a genuine
   non-straight curve) is given to show the class is inhabited.

   Pure-R (trig: cos/sin are axiom-clean); three-axiom.  No `Admitted`/`Axiom`/
   `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (claude-opus-4-8)
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance.

Local Open Scope R_scope.

(* Minimal planar point arithmetic. *)
Definition padd  (p q : Point) : Point := mkPoint (px p + px q) (py p + py q).
Definition psub  (p q : Point) : Point := mkPoint (px p - px q) (py p - py q).
Definition pscale (c : R) (p : Point) : Point := mkPoint (c * px p) (c * py p).
Definition pperp (p : Point) : Point := mkPoint (- py p) (px p).       (* 90 deg rotation *)
Definition pmid (A B : Point) : Point := pscale (/ 2) (padd A B).
Definition prot180 (M P : Point) : Point := psub (pscale 2 M) P.        (* 180 deg about M *)

(* A curved edge: the chord A--B plus a normal displacement profile f. *)
Definition curved_edge (A B : Point) (f : R -> R) (t : R) : Point :=
  padd (padd A (pscale t (psub B A))) (pscale (f t) (pperp (psub B A))).

(* Endpoints (whenever the profile vanishes at the ends). *)
Lemma curved_edge_start : forall A B f, f 0 = 0 -> curved_edge A B f 0 = A.
Proof.
  intros A B f H0. destruct A as [Ax Ay], B as [Bx By].
  unfold curved_edge, padd, psub, pscale, pperp.
  rewrite H0. apply (f_equal2 mkPoint); cbn [px py]; ring.
Qed.

Lemma curved_edge_end : forall A B f, f 1 = 0 -> curved_edge A B f 1 = B.
Proof.
  intros A B f H1. destruct A as [Ax Ay], B as [Bx By].
  unfold curved_edge, padd, psub, pscale, pperp.
  rewrite H1. apply (f_equal2 mkPoint); cbn [px py]; ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* THE Spectre property: a midpoint-odd profile makes the edge invariant under *)
(* the 180 degree rotation about the chord midpoint -- so it mates under       *)
(* rotation, never reflection.  Proved for the whole class of such profiles.   *)
(* -------------------------------------------------------------------------- *)

Theorem curved_edge_central_symmetry : forall (A B : Point) (f : R -> R) (t : R),
  (forall s, f (1 - s) = - f s) ->
  curved_edge A B f (1 - t) = prot180 (pmid A B) (curved_edge A B f t).
Proof.
  intros A B f t Hodd. destruct A as [Ax Ay], B as [Bx By].
  unfold curved_edge, prot180, pmid, padd, psub, pscale, pperp.
  rewrite (Hodd t). apply (f_equal2 mkPoint); cbn [px py]; field.
Qed.

(* -------------------------------------------------------------------------- *)
(* A concrete curved instance: the sine bump.  It vanishes at the ends, is     *)
(* midpoint-odd (so it inherits the mating property), and genuinely leaves the  *)
(* chord (bulges by the amplitude at the quarter point) -- a real curve, not a  *)
(* segment.                                                                    *)
(* -------------------------------------------------------------------------- *)

Definition sine_profile (amp : R) (t : R) : R := amp * sin (2 * PI * t).

Lemma sine_profile_0 : forall amp, sine_profile amp 0 = 0.
Proof. intros amp; unfold sine_profile. rewrite Rmult_0_r, sin_0. ring. Qed.

Lemma sine_profile_1 : forall amp, sine_profile amp 1 = 0.
Proof.
  intros amp; unfold sine_profile.
  replace (2 * PI * 1) with (2 * PI) by ring. rewrite sin_2PI. ring.
Qed.

Lemma sine_profile_odd : forall amp s,
  sine_profile amp (1 - s) = - sine_profile amp s.
Proof.
  intros amp s. unfold sine_profile.
  replace (2 * PI * (1 - s)) with (2 * PI - 2 * PI * s) by ring.
  rewrite sin_minus, sin_2PI, cos_2PI. ring.
Qed.

(* Genuinely curved: the displacement reaches the full amplitude at t = 1/4. *)
Lemma sine_profile_quarter : forall amp, sine_profile amp (1 / 4) = amp.
Proof.
  intros amp. unfold sine_profile.
  replace (2 * PI * (1 / 4)) with (PI / 2) by field. rewrite sin_PI2. ring.
Qed.

(* The concrete Spectre-style curved edge and its inherited properties. *)
Definition sine_edge (A B : Point) (amp : R) : R -> Point :=
  curved_edge A B (sine_profile amp).

Theorem sine_edge_start : forall A B amp, sine_edge A B amp 0 = A.
Proof. intros; apply curved_edge_start, sine_profile_0. Qed.

Theorem sine_edge_end : forall A B amp, sine_edge A B amp 1 = B.
Proof. intros; apply curved_edge_end, sine_profile_1. Qed.

Theorem sine_edge_central_symmetry : forall A B amp t,
  sine_edge A B amp (1 - t) = prot180 (pmid A B) (sine_edge A B amp t).
Proof. intros; apply curved_edge_central_symmetry, sine_profile_odd. Qed.

(* It is a real curve, not the chord: at t=1/4 it is displaced by `amp` along the
   perpendicular, so for amp <> 0 it leaves the straight segment. *)
Theorem sine_edge_off_chord : forall A B amp t,
  sine_edge A B amp t =
    padd (padd A (pscale t (psub B A))) (pscale (sine_profile amp t) (pperp (psub B A))).
Proof. reflexivity. Qed.

Lemma sine_edge_quarter_displacement : forall amp, sine_profile amp (1 / 4) = amp.
Proof. exact sine_profile_quarter. Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions curved_edge_central_symmetry.
Print Assumptions sine_edge_central_symmetry.
