(* ============================================================================
   NetTopologySuite.Proofs.BufferBridgeRound
   ----------------------------------------------------------------------------
   Seam map: docs/buffer-noder-pipeline.md §6 (the H_bridge residual; the exact
   round-arc case that closes both directions / the corner trichotomy).
   The "Goldilocks" closing of H_bridge at a corner: the round (exact-arc)
   join sits EXACTLY on the corner's d-circle, so the idealised round buffer
   neither undershoots (chord) nor overshoots (miter) the d-neighbourhood --
   both the soundness and completeness directions close there.

   This completes the corner trichotomy proved across the buffer-bridge files:

       chord midpoint      d^2 / 2   (< d^2)   undershoot  -- BufferBridgeComplete
       round arc           d^2       (= d^2)   exact       -- HERE
       miter apex          2 d^2     (> d^2)   overshoot   -- BufferBridgeSound

   Every point of the round-join arc is `V + d * u` for a unit direction `u`
   in the corner's sweep; `round_arc_dist_sq_on_circle` shows each lies at
   squared distance exactly `d^2` from the vertex.  Hence the round buffer's
   corner boundary is the radius-d circular arc itself -- precisely why
   `point_set (extract) = buffer_spec` holds exactly for the idealised round
   buffer, the case `BufferBridge.v`'s decomposition isolates.

   Bridgeheaded on the closed `BufferOffset.dist_sq_translate` and the
   concrete `miter_apex_dist_sq_90` / `chord_midpoint_dist_sq_90`.  Pure-R;
   three-axiom footprint.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Real Vec Distance Direction HotPixel
                               BufferOffset BufferMiter BufferBevel
                               BufferBridgeSound BufferBridgeComplete.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The round-join arc point and its on-circle property.                   *)
(* -------------------------------------------------------------------------- *)

(* A point of the round join: the corner vertex offset by d along a unit
   direction u in the swept arc. *)
Definition round_arc_point (V : Point) (u : Vec) (d : R) : Point :=
  pt_translate V (d * vx u) (d * vy u).

(* Every round-arc point lies at squared distance exactly d^2 from the
   corner -- on the radius-d circle. *)
Lemma round_arc_dist_sq_on_circle :
  forall (V : Point) (u : Vec) (d : R),
    vmag_sq u = 1 -> dist_sq V (round_arc_point V u d) = d * d.
Proof.
  intros V u d Hu. unfold round_arc_point. rewrite dist_sq_translate.
  replace ((d * vx u) * (d * vx u) + (d * vy u) * (d * vy u))
    with (d * d * vmag_sq u) by (unfold vmag_sq, vdot; ring).
  rewrite Hu. ring.
Qed.

(* In Euclidean distance: exactly d (for d >= 0). *)
Lemma round_arc_dist :
  forall (V : Point) (u : Vec) (d : R),
    0 <= d -> vmag_sq u = 1 -> dist V (round_arc_point V u d) = d.
Proof.
  intros V u d Hd Hu. unfold dist.
  rewrite (round_arc_dist_sq_on_circle V u d Hu).
  replace (d * d) with (Rsqr d) by (unfold Rsqr; ring).
  rewrite sqrt_Rsqr_abs, Rabs_right by lra. reflexivity.
Qed.

(* The round join is SOUND at the corner (within d) -- and reaches d, so the
   corner of the d-neighbourhood is on its boundary (completeness there). *)
Lemma round_arc_within_d :
  forall (V : Point) (u : Vec) (d : R),
    0 <= d -> vmag_sq u = 1 -> dist V (round_arc_point V u d) <= d.
Proof.
  intros V u d Hd Hu. rewrite (round_arc_dist V u d Hd Hu). lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The corner trichotomy capstone.                                        *)
(* -------------------------------------------------------------------------- *)

(* For the unit right-angle corner, the chord midpoint (d^2/2) is strictly
   inside, the round arc (d^2) is exactly on, and the miter apex (2 d^2) is
   strictly outside the corner's d-circle.  Only the round (exact-arc) join
   matches the d-neighbourhood. *)
Theorem buffer_corner_trichotomy :
  forall (u : Vec) (d : R),
    0 < d -> vmag_sq u = 1 ->
    dist_sq (mkPoint 0 0)
            (segment_point (bevel_point (mkPoint 0 0) (mkVec 1 0) d)
                           (bevel_point (mkPoint 0 0) (mkVec 0 1) d) (1 / 2))
      < dist_sq (mkPoint 0 0) (round_arc_point (mkPoint 0 0) u d)
    /\ dist_sq (mkPoint 0 0) (round_arc_point (mkPoint 0 0) u d) = d * d
    /\ dist_sq (mkPoint 0 0) (round_arc_point (mkPoint 0 0) u d)
      < dist_sq (mkPoint 0 0)
                (miter_apex (mkPoint 0 0) (mkVec 1 0) (mkVec 0 1) d).
Proof.
  intros u d Hd Hu.
  rewrite (round_arc_dist_sq_on_circle (mkPoint 0 0) u d Hu).
  rewrite (chord_midpoint_dist_sq_90 d).
  rewrite (miter_apex_dist_sq_90 d).
  repeat split; nra.
Qed.

Print Assumptions round_arc_dist_sq_on_circle.
Print Assumptions buffer_corner_trichotomy.
