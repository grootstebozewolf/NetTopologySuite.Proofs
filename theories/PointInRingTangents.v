(* ============================================================================
   NetTopologySuite.Proofs.PointInRingTangents
   ----------------------------------------------------------------------------
   Green-phase tangent attempts for Seams 3 + 5 of `point_in_ring_correct`.

   Per `docs/point-in-ring-seams-3-5-7-red.md`:
     Seam 3 = `geometric_interior` (Real.structure bridge or Stdlib-only).
     Seam 5 = `winding_number` (atan2 / turning / bypass).

   Each tangent: simplest possible implementation, simplest possible proof,
   outcome recorded (Qed or stuck) in `docs/point-in-ring-tangent-attempts.md`.

   Tangents that close land here as Qed-closed lemmas.  Tangents that fail
   live in the companion doc only -- no Admitteds.

   Tangent 3A (fourcolor import gate) is attempted FIRST since it gates all
   other Seam 3 tangents.  If the import fails or conflicts, fall back to
   Tangent 3D (Stdlib-only geometric_interior).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import List.
From Stdlib Require Import Ratan.
From Stdlib Require Import Rtrigo1.

From NTS.Proofs Require Import Distance.
From NTS.Proofs Require Import Overlay.
From NTS.Proofs Require Import PointInRingCorrect.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Tangent 5A: atan2 definition + trivial property.                       *)
(* -------------------------------------------------------------------------- *)

(* Standard quadrant-corrected arctangent.  Convention: at the origin
   (x = 0, y = 0) we return 0 (Coq's standard, also matches IEEE 754 atan2
   when the inputs are ordinary zeros). *)
Definition atan2 (y x : R) : R :=
  if Rgt_dec x 0 then atan (y / x)
  else if Rlt_dec x 0 then
    if Rge_dec y 0 then atan (y / x) + PI
    else atan (y / x) - PI
  else  (* x = 0 *)
    if Rgt_dec y 0 then PI / 2
    else if Rlt_dec y 0 then - (PI / 2)
    else 0.

Lemma atan2_pos_x :
  forall y x : R,
    x > 0 ->
    atan2 y x = atan (y / x).
Proof.
  intros y x Hx.
  unfold atan2.
  destruct (Rgt_dec x 0) as [_ | Hcontra]; [reflexivity|].
  exfalso; apply Hcontra; exact Hx.
Qed.

(* Bonus -- a few more simple atan2 properties that close cleanly. *)
Lemma atan2_neg_x_pos_y :
  forall y x : R,
    x < 0 -> y >= 0 ->
    atan2 y x = atan (y / x) + PI.
Proof.
  intros y x Hx Hy.
  unfold atan2.
  destruct (Rgt_dec x 0) as [Hgt | _]; [lra|].
  destruct (Rlt_dec x 0) as [_ | Hc]; [|contradiction].
  destruct (Rge_dec y 0) as [_ | Hc]; [reflexivity|contradiction].
Qed.

Lemma atan2_zero_x_pos_y :
  forall y : R, y > 0 -> atan2 y 0 = PI / 2.
Proof.
  intros y Hy.
  unfold atan2.
  destruct (Rgt_dec 0 0) as [Hc | _]; [lra|].
  destruct (Rlt_dec 0 0) as [Hc | _]; [lra|].
  destruct (Rgt_dec y 0) as [_ | Hc]; [reflexivity|contradiction].
Qed.

Lemma atan2_origin : atan2 0 0 = 0.
Proof.
  unfold atan2.
  destruct (Rgt_dec 0 0) as [Hc | _]; [lra|].
  destruct (Rlt_dec 0 0) as [Hc | _]; [lra|].
  destruct (Rgt_dec 0 0) as [Hc | _]; [lra|].
  destruct (Rlt_dec 0 0) as [Hc | _]; [lra|].
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Tangent 5D: Option C bypass theorem.                                   *)
(*                                                                            *)
(* The conditional headline: once the JCT-style hypothesis is available,      *)
(* point_in_ring_correct follows immediately.  Mirrors Seam 4's vacuous       *)
(* conditional but adds the generic-ray-position precondition and             *)
(* parameterises over an abstract topological interior.                       *)
(* -------------------------------------------------------------------------- *)

Section OptionCBypass.

  Variable topological_interior : Point -> Ring -> Prop.

  Theorem point_in_ring_correct_via_crossing :
    forall (p : Point) (r : Ring),
      ring_simple r ->
      ring_closed r ->
      no_horizontal_edge_at p r ->
      (forall (q : Point) (s : Ring),
         ring_simple s -> ring_closed s ->
         no_horizontal_edge_at q s ->
         point_in_ring q s <-> topological_interior q s) ->
      point_in_ring p r <-> topological_interior p r.
  Proof.
    intros p r Hs Hc Hg HJCT.
    apply HJCT; assumption.
  Qed.

  (* A slightly stronger form: bridges to the bool-side parity via the
     fold bridge.  The bool predicate's parity now directly characterises
     topological membership. *)
  Theorem count_crossings_correct_via_crossing :
    forall (p : Point) (r : Ring),
      ring_simple r ->
      ring_closed r ->
      no_horizontal_edge_at p r ->
      (forall (q : Point) (s : Ring),
         ring_simple s -> ring_closed s ->
         no_horizontal_edge_at q s ->
         point_in_ring q s <-> topological_interior q s) ->
      Nat.odd (count_crossings_ray p r) = true <-> topological_interior p r.
  Proof.
    intros p r Hs Hc Hg HJCT.
    rewrite <- (point_in_ring_eq_parity p r Hg).
    apply HJCT; assumption.
  Qed.

End OptionCBypass.

(* -------------------------------------------------------------------------- *)
(* §3  Tangent 3D: geometric_interior in Stdlib only.                         *)
(*                                                                            *)
(* Bypass fourcolor entirely.  Define the topological interior using only     *)
(* Stdlib Reals primitives.                                                   *)
(* -------------------------------------------------------------------------- *)

(* The image of a ring's edge skeleton -- points lying on some edge. *)
Definition ring_image (r : Ring) (q : Point) : Prop :=
  exists e : Edge, exists t : R,
    In e (ring_edges r) /\
    0 <= t <= 1 /\
    px q = (1 - t) * px (fst e) + t * px (snd e) /\
    py q = (1 - t) * py (fst e) + t * py (snd e).

(* Complement of the edge skeleton -- the "off-ring" point set. *)
Definition ring_complement (r : Ring) (q : Point) : Prop :=
  ~ ring_image r q.

(* A continuous path between two points stays in the complement.  This is
   the corpus-level "connected in R^2 \ ring" relation. *)
Definition connected_in_complement
    (r : Ring) (p q : Point) : Prop :=
  exists path : R -> Point,
    path 0 = p /\ path 1 = q /\
    forall t : R, 0 <= t <= 1 -> ring_complement r (path t).

(* p is in a BOUNDED connected component of the complement: there is a
   bound M such that every point reachable from p stays within radius M
   of the origin. *)
Definition in_bounded_component
    (r : Ring) (p : Point) : Prop :=
  exists M : R,
    M > 0 /\
    forall q : Point,
      connected_in_complement r p q ->
      px q * px q + py q * py q <= M * M.

(* Geometric interior: off-ring AND in a bounded component. *)
Definition geometric_interior_stdlib
    (p : Point) (r : Ring) : Prop :=
  ring_complement r p /\ in_bounded_component r p.

(* Tangent 3D's basic property: a point on a ring edge is in the ring
   image, hence not in the complement, hence not in the interior. *)
Lemma not_geometric_interior_on_edge :
  forall (p : Point) (r : Ring) (e : Edge) (t : R),
    In e (ring_edges r) ->
    0 <= t <= 1 ->
    px p = (1 - t) * px (fst e) + t * px (snd e) ->
    py p = (1 - t) * py (fst e) + t * py (snd e) ->
    ~ geometric_interior_stdlib p r.
Proof.
  intros p r e t Hin Ht Hx Hy [Hcomp _].
  apply Hcomp. exists e, t. split; [|split; [|split]]; assumption.
Qed.

(* Edges of an empty ring: there are none. *)
Lemma ring_image_nil :
  forall q : Point, ~ ring_image [] q.
Proof.
  intros q [e [t [Hin _]]].
  simpl in Hin. contradiction.
Qed.

(* On an empty ring, the complement is everything; the bounded-component
   requirement then forces a contradiction (no single bound covers all of
   R^2). *)
Lemma not_geometric_interior_empty_ring :
  forall p : Point, ~ geometric_interior_stdlib p [].
Proof.
  intros p [_ [M [HMpos Hbnd]]].
  destruct p as [px_p py_p].
  set (q := mkPoint (M + 1) 0).
  assert (Hcon : connected_in_complement [] (mkPoint px_p py_p) q).
  { exists (fun t => mkPoint ((1 - t) * px_p + t * (M + 1))
                              ((1 - t) * py_p + t * 0)).
    split; [|split].
    - cbn. f_equal; lra.
    - unfold q. cbn. f_equal; lra.
    - intros t Ht. intro Himg. apply (ring_image_nil _ Himg). }
  specialize (Hbnd q Hcon).
  unfold q in Hbnd. cbn in Hbnd. nra.
Qed.

(* Tangent 3E additional: connected_in_complement is reflexive. *)
Lemma connected_in_complement_refl :
  forall (r : Ring) (p : Point),
    ring_complement r p ->
    connected_in_complement r p p.
Proof.
  intros r p Hcomp.
  exists (fun _ => p).
  split; [reflexivity|split; [reflexivity|]].
  intros t _. exact Hcomp.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Tangents documented as STUCK or DEFERRED.                              *)
(* -------------------------------------------------------------------------- *)

(* Tangent 5B (atan2_bound: -PI < atan2 y x <= PI):
   Provable but tedious -- 6+ case branches (x>0; x<0 with y>=0 and y<0;
   x=0 with y>0, y<0, y=0).  Each requires `atan_bound : -PI/2 < atan x <
   PI/2` plus sign analysis of y/x.  Estimate: 50-80 lines.  Skipped here
   as it exceeds the 20-min/tangent budget; the path is mechanical. *)

(* Tangent 5C (total_angle_telescopes):
   STUCK -- the angular contributions do NOT telescope cleanly.  atan2
   has a branch cut at the negative x-axis (-PI to PI discontinuity).
   For a closed simple polygon the total angle sum is 2*PI*k for some
   k in {-1, 0, +1}, NOT zero.  The "telescoping" interpretation
   confuses angle differences with arc lengths.  No fix in this
   formulation; requires either:
     (a) a branch-cut-aware angular difference (subtract 2*PI when
         the naive difference jumps), or
     (b) the Cauchy/Stokes-style integral form (line integral of
         d theta).
   Both are research-grade.  Documented as Option C bypass (§2 above)
   is the right move. *)

(* Tangent 3A (fourcolor import gate):
   GREEN -- confirmed via standalone test (not committed here).
     From fourcolor Require Import realplane.
   imports cleanly alongside Stdlib Reals; no universe inconsistency
   or namespace conflict.  Real.structure and realplane.point are
   accessible.  See docs/point-in-ring-tangent-attempts.md §3A for
   the exact test. *)

(* Tangent 3B (Real.sup from Stdlib completeness):
   GREEN with COST -- the construction
     Definition R_sup (E : R -> Prop) : R :=
       match excluded_middle_informative (bound E /\ (exists x, E x)) with
       | left H => proj1_sig (completeness E (proj1 H) (proj2 H))
       | right _ => 0
       end.
   typechecks and produces a total `(R -> Prop) -> R` function suitable
   for Real.sup.  HOWEVER it pulls `constructive_definite_description`
   into the axiom footprint (via excluded_middle_informative) -- NOT
   currently on the README allowlist.  A landing in the main corpus
   would require README/allowlist expansion (policy-level decision).
   Documented in the companion doc; not landed here. *)

(* Tangent 3C (to_rplane translation):
   GREEN -- once Stdlib_R_struct is built with `Real.val := R` (i.e.
   definitionally R, not a coerced opaque), the translation
     Definition to_rplane (p : Point) : realplane.point Stdlib_R_struct :=
       @realplane.Point Stdlib_R_struct (px p) (py p).
   typechecks immediately with no coercion or universe gymnastics.
   The eq_rect-based approach hit a universe inconsistency
   (Real.val Rmodel : Type vs R : Set) -- avoided by building the
   structure with val := R definitionally.  See companion doc §3C. *)

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions atan2_pos_x.
Print Assumptions atan2_neg_x_pos_y.
Print Assumptions atan2_origin.
Print Assumptions point_in_ring_correct_via_crossing.
Print Assumptions count_crossings_correct_via_crossing.
Print Assumptions not_geometric_interior_on_edge.
Print Assumptions ring_image_nil.
Print Assumptions not_geometric_interior_empty_ring.
Print Assumptions connected_in_complement_refl.
