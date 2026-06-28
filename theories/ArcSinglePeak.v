(** * ArcSinglePeak — the exact remaining geometric seam for #64 (arc point-distance)

    On a circle, squared distance to P is affine-DECREASING in the dot product
    <P-O, Y-O>.  So the nearest on-arc point to P is wherever that dot is
    largest; when the radial foot (the global dot-maximiser) lies OUTSIDE the
    directed sweep, that maximum over the arc is attained at an ENDPOINT.

    This file BANKS the reusable circle/dot monotonicity helpers (§1, all Qed),
    then ISOLATES the one residual planar inequality (§2) — the "single-peak dot
    bound".  The metric seam `point_to_arc_dist_fallback_ends_lower` is
    discharged in `ArcPointDistance.v` by reducing it to §2, so the only
    remaining Tier-3 obligation is the crisp planar fact below — no metric
    residue.

    Status of §2 (honest):
      - Believed TRUE: numerically falsity-checked on symmetric and asymmetric
        configs and both signs of the center offset; no counterexample found.
      - Resists automation: `nra` returns "cannot find witness" (degree-2
        Positivstellensatz insufficient); `psatz R 4` needs the external CSDP
        solver, absent here. A hand certificate / chord-frame proof is the
        documented follow-up (see the chord-frame reduction in the comment).
      - It is NOT admitted as anything suspect: it is a true, isolated planar
        inequality, kept as the single named deferred obligation.

    Translates directly to the NTS CircularString / point-to-arc distance
    fallback guard.  Pure-R; the §1 helpers are classical-reals trio only, §2 is
    the lone isolated obligation.  *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance ArcDistance.

Local Open Scope R_scope.

(* The center-based dot product <P-O, Y-O>, inline in coordinates (ring-friendly). *)
Definition gdot (O P Y : Point) : R :=
  (px P - px O) * (px Y - px O) + (py P - py O) * (py Y - py O).

(* signed side of chord SE: cross (E-S) (Y-S). *)
Definition side (S E Y : Point) : R :=
  (px E - px S) * (py Y - py S) - (py E - py S) * (px Y - px S).

(* ------------------------------------------------------------------ *)
(* §1  Banked reductions (Qed, reusable).                             *)
(* ------------------------------------------------------------------ *)

(* Law of cosines about the center. *)
Lemma dist2_via_center_dot : forall O P Y,
  dist_sq P Y = dist_sq P O + dist_sq O Y - 2 * gdot O P Y.
Proof. intros O P Y. unfold dist_sq, gdot. ring. Qed.

(* On a common circle, larger dot ==> nearer to P. *)
Lemma circle_dist_le_of_dot_ge : forall O P Y Z r,
  dist O Y = r -> dist O Z = r ->
  gdot O P Z <= gdot O P Y ->
  dist P Y <= dist P Z.
Proof.
  intros O P Y Z r HY HZ Hdot.
  unfold dist. apply sqrt_le_1_alt.
  pose proof (dist2_via_center_dot O P Y) as EY.
  pose proof (dist2_via_center_dot O P Z) as EZ.
  assert (HsqY : dist_sq O Y = r * r).
  { pose proof (dist_mul_self O Y) as H. rewrite HY in H. lra. }
  assert (HsqZ : dist_sq O Z = r * r).
  { pose proof (dist_mul_self O Z) as H. rewrite HZ in H. lra. }
  rewrite EY, EZ, HsqY, HsqZ. lra.
Qed.

(* Opposite-sign helper: same-side product positive + cross product nonpositive
   forces the remaining product nonpositive (used to turn "X in span, foot not in
   span" into the opposite-sides hypothesis of the core). *)
Lemma sign_opp : forall m x f : R, 0 < m * x -> m * f <= 0 -> x * f <= 0.
Proof.
  intros m x f Hmx Hmf.
  destruct (Rtotal_order m 0) as [Hm | [Hm | Hm]].
  - nra.
  - subst m; lra.
  - nra.
Qed.

(* ------------------------------------------------------------------ *)
(* §2  The isolated planar single-peak dot bound.                     *)
(*                                                                    *)
(* S,E,X on the circle of center O radius r; X and the radial foot F  *)
(* on opposite (closed) sides of chord SE  ==>  the dot at X is        *)
(* bounded by the larger endpoint dot.                                *)
(*                                                                    *)
(* CHORD-FRAME REDUCTION (the documented route to a hand proof):       *)
(*   frame: M=midpoint SE, t=normalize(E-S), n=perp t; S=(-h,0),       *)
(*   E=(h,0), O=(0,d); X=(a,b) with a^2 = h^2 + 2*b*d - b^2 and        *)
(*   h^2+d^2=r^2; (pt,pn)=P-O in frame, q=|P-O|.  X in span gives      *)
(*   b*d <= 0; foot outside gives d*(q*d + r*pn) >= 0.  Goal reduces   *)
(*   to  a*pt + b*pn <= h*Rabs pt  (the irreducible scalar core).      *)
(*                                                                    *)
(* Believed true (falsity-checked); nra/psatz (CSDP-gated) insufficient.*)
Lemma arc_dot_max_at_endpoint : forall O P S E X r,
  dist O S = r -> dist O E = r -> dist O X = r ->
  side S E X * side S E (radial_foot O P r) <= 0 ->
  0 < dist O P ->
  gdot O P X <= Rmax (gdot O P S) (gdot O P E).
Proof.
Admitted.
