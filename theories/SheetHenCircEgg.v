(* ============================================================================
   NetTopologySuite.Proofs.SheetHenCircEgg
   ----------------------------------------------------------------------------
   CircularEgg payload for host MkCirc (claimId 0007-gamma-mkcirc).
   γ(t) = O + r·(cos(θ₀ + t·Δθ), sin(θ₀ + t·Δθ)). Angles are egg data.
   Not sidecar CircEgg. 3-axiom. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance.
Local Open Scope R_scope.

Record CircularEgg : Type := mkCircularEgg {
  circ_o : Point;
  circ_r : R;
  circ_theta0 : R;
  circ_sweep : R
}.

Definition circ_eval (c : CircularEgg) (t : R) : Point :=
  mkPoint (px (circ_o c) + circ_r c * cos (circ_theta0 c + t * circ_sweep c))
          (py (circ_o c) + circ_r c * sin (circ_theta0 c + t * circ_sweep c)).

Definition on_circ (c : CircularEgg) (t : R) (p : Point) : Prop :=
  0 <= t <= 1 /\ p = circ_eval c t.

Definition circ_split (c : CircularEgg) (t : R) : CircularEgg * CircularEgg :=
  (mkCircularEgg (circ_o c) (circ_r c) (circ_theta0 c) (t * circ_sweep c),
   mkCircularEgg (circ_o c) (circ_r c)
     (circ_theta0 c + t * circ_sweep c) ((1 - t) * circ_sweep c)).
