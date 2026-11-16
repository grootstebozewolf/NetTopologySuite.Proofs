(* ============================================================================
   NetTopologySuite.Proofs.SheetHenEllipseEgg
   ----------------------------------------------------------------------------
   EllipticEgg payload for host MkEllipse (claimId 0007-ellipse-first-cook).
   NTS has no elliptic arc type; this is the SQL/MM-style EllipticalCurve
   egg of ADR-0007, not a mirror of a JTS class.
   γ(t) = O + R(φ)·(a·cos(θ₀ + t·Δθ), b·sin(θ₀ + t·Δθ)).
   θ is the eccentric anomaly, not the polar angle and not arc length.
   The parameterisation is OUR choice. Angles and axes are egg data.
   Endpoints are derived: ell_start := γ(0), ell_end := γ(1).
   ell_eval is total: a = b is a circle; a = 0 or b = 0 collapses to
   an axis segment traced back and forth; Δθ = 0 is constant; Δθ < 0
   is clockwise in the egg frame. on_ell is the parameterized arc.
   ell_split is a sub-window of the same placement and axes.
   Not SidecarEllipticEgg and not RelateEllipticArc.EllipticArcChord
   (endpoint chord). Not EllipseLength / EllipseSpeedIntegral.
   3-axiom host. No Admitted, no stub declaration.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance.
Local Open Scope R_scope.

Record EllipticEgg : Type := mkEllipticEgg {
  ell_o : Point;
  ell_a : R;
  ell_b : R;
  ell_phi : R;
  ell_theta0 : R;
  ell_sweep : R
}.

(* Egg-frame coordinates before the rotation by φ. *)
Definition ell_u (e : EllipticEgg) (t : R) : R :=
  ell_a e * cos (ell_theta0 e + t * ell_sweep e).
Definition ell_v (e : EllipticEgg) (t : R) : R :=
  ell_b e * sin (ell_theta0 e + t * ell_sweep e).

Definition ell_eval (e : EllipticEgg) (t : R) : Point :=
  mkPoint (px (ell_o e) + cos (ell_phi e) * ell_u e t
                        - sin (ell_phi e) * ell_v e t)
          (py (ell_o e) + sin (ell_phi e) * ell_u e t
                        + cos (ell_phi e) * ell_v e t).

Definition ell_start (e : EllipticEgg) : Point := ell_eval e 0.
Definition ell_end (e : EllipticEgg) : Point := ell_eval e 1.

Definition on_ell (e : EllipticEgg) (t : R) (p : Point) : Prop :=
  0 <= t <= 1 /\ p = ell_eval e t.

Definition ell_split (e : EllipticEgg) (t : R) : EllipticEgg * EllipticEgg :=
  (mkEllipticEgg (ell_o e) (ell_a e) (ell_b e) (ell_phi e)
     (ell_theta0 e) (t * ell_sweep e),
   mkEllipticEgg (ell_o e) (ell_a e) (ell_b e) (ell_phi e)
     (ell_theta0 e + t * ell_sweep e) ((1 - t) * ell_sweep e)).

Lemma ell_eval_at_0 : forall e, ell_eval e 0 = ell_start e.
Proof. reflexivity. Qed.

Lemma ell_eval_at_1 : forall e, ell_eval e 1 = ell_end e.
Proof. reflexivity. Qed.

Lemma ell_split_eval_left :
  forall e t u,
    ell_eval (fst (ell_split e t)) u = ell_eval e (t * u).
Proof.
  intros e t u.
  unfold ell_eval, ell_u, ell_v, ell_split.
  cbn [fst ell_o ell_a ell_b ell_phi ell_theta0 ell_sweep].
  replace (ell_theta0 e + u * (t * ell_sweep e))
    with (ell_theta0 e + (t * u) * ell_sweep e) by ring.
  reflexivity.
Qed.

Lemma ell_split_eval_right :
  forall e t u,
    ell_eval (snd (ell_split e t)) u =
    ell_eval e (t + (1 - t) * u).
Proof.
  intros e t u.
  unfold ell_eval, ell_u, ell_v, ell_split.
  cbn [snd ell_o ell_a ell_b ell_phi ell_theta0 ell_sweep].
  replace (ell_theta0 e + t * ell_sweep e + u * ((1 - t) * ell_sweep e))
    with (ell_theta0 e + (t + (1 - t) * u) * ell_sweep e) by ring.
  reflexivity.
Qed.

Lemma ell_split_join :
  forall e t,
    ell_eval (fst (ell_split e t)) 1 = ell_eval e t /\
    ell_eval (snd (ell_split e t)) 0 = ell_eval e t.
Proof.
  intros e t.
  rewrite ell_split_eval_left, ell_split_eval_right.
  split; apply f_equal; ring.
Qed.

Lemma ell_split_ends :
  forall e t,
    ell_eval (fst (ell_split e t)) 0 = ell_eval e 0 /\
    ell_eval (snd (ell_split e t)) 1 = ell_eval e 1.
Proof.
  intros e t.
  rewrite ell_split_eval_left, ell_split_eval_right.
  split; apply f_equal; ring.
Qed.

(* Every point of the egg lies on the full ellipse: in the egg frame
   (u, v) the implicit equation b²u² + a²v² = a²b² holds. Stated
   without division so a = 0 / b = 0 need no side condition. *)
Lemma ell_frame_implicit :
  forall e t,
    ell_b e * ell_b e * (ell_u e t * ell_u e t)
    + ell_a e * ell_a e * (ell_v e t * ell_v e t)
    = ell_a e * ell_a e * (ell_b e * ell_b e).
Proof.
  intros e t. unfold ell_u, ell_v.
  set (th := ell_theta0 e + t * ell_sweep e).
  pose proof (sin2_cos2 th) as H. unfold Rsqr in H.
  replace (ell_b e * ell_b e * (ell_a e * cos th * (ell_a e * cos th))
           + ell_a e * ell_a e * (ell_b e * sin th * (ell_b e * sin th)))
    with (ell_a e * ell_a e * (ell_b e * ell_b e)
          * (sin th * sin th + cos th * cos th)) by ring.
  rewrite H. ring.
Qed.

(* a = b = r is the host circular egg's point set at rotation 0. *)
Lemma ell_circle_eval :
  forall o r th0 sw t,
    ell_eval (mkEllipticEgg o r r 0 th0 sw) t =
    mkPoint (px o + r * cos (th0 + t * sw))
            (py o + r * sin (th0 + t * sw)).
Proof.
  intros o r th0 sw t.
  unfold ell_eval, ell_u, ell_v.
  cbn [ell_o ell_a ell_b ell_phi ell_theta0 ell_sweep].
  rewrite cos_0, sin_0.
  apply (f_equal2 mkPoint); ring.
Qed.

Print Assumptions ell_eval_at_0.
Print Assumptions ell_eval_at_1.
Print Assumptions ell_split_eval_left.
Print Assumptions ell_split_eval_right.
Print Assumptions ell_split_join.
Print Assumptions ell_split_ends.
Print Assumptions ell_frame_implicit.
Print Assumptions ell_circle_eval.
