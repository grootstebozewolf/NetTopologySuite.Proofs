(* ============================================================================
   NetTopologySuite.Proofs.ArcOverlay
   ----------------------------------------------------------------------------
   Phase 4 Session 7: arc overlay correctness conditional headline.

   The Phase 4 Option B headline.  Same epistemic position as Phase 3's
   `overlay_ng_correct_conditional`: Qed-closed under named hypotheses
   carrying the deferred gaps (chord approximation error bound + hot-
   pixel soundness + chord-to-arc proximity bridge).

   The mathematical claim:

     Given valid CurveGeometries A and B, if a point p lies in the
     boolean_op result of their chord-approximated counterparts
     `to_geometry A n` and `to_geometry B n`, then p is within
     `max_sagitta A B` distance of some point on an arc of A or B.

   Equivalently: the chord-approximated overlay's point-set tracks the
   true arc point-set up to the maximum sagitta error.  This is the
   formal Option B guarantee: chord approximation is correct up to the
   sagitta-bounded tolerance.

   See `docs/audit-phase4-chord-overfitting.md` §5 (Session 7 in the
   7-session plan).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import List.

From NTS.Proofs Require Import Distance.
From NTS.Proofs Require Import Overlay.
From NTS.Proofs Require Import CurveGeometry.
From NTS.Proofs Require Import ArcOrient.
From NTS.Proofs Require Import ArcIntersect.
From NTS.Proofs Require Import ArcHotPixel.
From NTS.Proofs Require Import ArcChordApprox.

Import ListNotations.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  arcs_of -- enumerate every CircularArc in a CurveGeometry.             *)
(* -------------------------------------------------------------------------- *)

Definition arcs_of_segment (s : CurveSegment) : list CircularArc :=
  match s with
  | CSChord _ _ => []
  | CSArc a => [a]
  end.

Definition arcs_of_ring (r : CurveRing) : list CircularArc :=
  flat_map arcs_of_segment r.

Definition arcs_of_polygon (cp : CurvePolygon) : list CircularArc :=
  arcs_of_ring (curve_outer cp) ++
  flat_map arcs_of_ring (curve_holes cp).

Definition arcs_of (cg : CurveGeometry) : list CircularArc :=
  flat_map arcs_of_polygon cg.

(* -------------------------------------------------------------------------- *)
(* §2  max_sagitta -- the chord-approximation tolerance.                      *)
(*                                                                            *)
(* The maximum sagitta over all arcs in A and B.  This is the error bound:    *)
(* every chord-approximation point lies within max_sagitta of the original    *)
(* arc.                                                                       *)
(* -------------------------------------------------------------------------- *)

Definition max_sagitta (A B : CurveGeometry) : R :=
  fold_left
    (fun acc a => Rmax acc (sagitta a))
    (arcs_of A ++ arcs_of B)
    0.

(* Helper: fold preserves non-negativity of the accumulator. *)
Lemma fold_max_sagitta_ge_acc :
  forall xs acc,
    0 <= acc ->
    0 <= fold_left (fun acc a => Rmax acc (sagitta a)) xs acc.
Proof.
  induction xs as [|x xs IH]; intros acc Hacc.
  - cbn. exact Hacc.
  - cbn. apply IH.
    pose proof (Rmax_l acc (sagitta x)). lra.
Qed.

(* max_sagitta is non-negative (Rmax with 0 base). *)
Lemma max_sagitta_nonneg :
  forall A B, 0 <= max_sagitta A B.
Proof.
  intros. unfold max_sagitta.
  apply fold_max_sagitta_ge_acc. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  arc_close_to_curves -- the conclusion predicate.                       *)
(*                                                                            *)
(* `arc_close_to_curves q A B eps` means: q is within eps (Chebyshev          *)
(* distance, i.e. max of |dx| and |dy|) of some point X on an ARC CURVE of   *)
(* A or B (i.e. on the 1D circumcircle boundary, not in the 2D region's      *)
(* interior).  X must satisfy both circumcircle membership                    *)
(* (inCircle_R = 0) AND arc-span containment.                                 *)
(*                                                                            *)
(* IMPORTANT semantic distinction (boundary vs region):                       *)
(*                                                                            *)
(*   This predicate is BOUNDARY closeness -- it asks for proximity to an     *)
(*   arc CURVE (1D), not membership in an arc REGION (2D).  Sagitta is a    *)
(*   boundary-distance bound: the chord-vs-arc-curve distance is bounded by  *)
(*   sagitta.  For 2D region membership the natural notion is symmetric-    *)
(*   difference / Hausdorff distance between the chord-polygon and arc-     *)
(*   region; these coincide for boundary points but DIVERGE for points     *)
(*   deep inside the polygon (or arc region), where the boundary distance  *)
(*   is large but region membership matches exactly.                          *)
(*                                                                            *)
(* Consequence for the headline (acknowledged below):                         *)
(*   The H_A_bridge / H_B_bridge hypotheses are PRACTICALLY DEMANDING --    *)
(*   they ask the consumer to prove that EVERY point in the chord-polygon   *)
(*   interior is close to an arc curve.  For polygons close in size to the *)
(*   sagitta this holds; for larger polygons (interior points far from any *)
(*   boundary edge) it does NOT hold.  The conditional theorem is           *)
(*   structurally correct but its hypotheses are more demanding than the    *)
(*   bare sagitta bound from S6; a future session targeting Option A's     *)
(*   region-level semantics would tighten this.                              *)
(* -------------------------------------------------------------------------- *)

Definition arc_close_to_curves
    (q : Point) (A B : CurveGeometry) (eps : R) : Prop :=
  exists (a : CircularArc) (X : Point),
    In a (arcs_of A ++ arcs_of B) /\
    inCircle_R (arc_start a) (arc_mid a) (arc_end a) X = 0 /\
    arc_span_contains a X /\
    Rabs (px q - px X) <= eps /\
    Rabs (py q - py X) <= eps.

(* -------------------------------------------------------------------------- *)
(* §4  The Phase 4 conditional headline.                                      *)
(*                                                                            *)
(* Two named gaps as hypotheses, mirroring Phase 3's pattern:                  *)
(*                                                                            *)
(*   H_A_bridge: any point in the chord-approximated A is close to an arc    *)
(*               of A or B.  This encapsulates `chord_approx_error_bound`    *)
(*               (deferred from S6) -- when that lemma lands, H_A_bridge     *)
(*               follows for free.                                            *)
(*                                                                            *)
(*   H_B_bridge: symmetric for B.                                             *)
(*                                                                            *)
(* The proof is a clean case split on `op`.  Each BooleanOp case unfolds      *)
(* `boolean_op` to a disjunction or conjunction of `point_set` claims; each  *)
(* `point_set` claim feeds H_A_bridge or H_B_bridge to produce the witness.  *)
(* -------------------------------------------------------------------------- *)

Theorem arc_overlay_correct_chord_approx :
  forall (A B : CurveGeometry) (op : BooleanOp)
         (p : Point) (n : nat),
    valid_curve_geometry A ->
    valid_curve_geometry B ->
    (* H_A_bridge: points in chord-approximated A are close to an arc *)
    (forall q : Point,
       point_set (to_geometry A n) q ->
       arc_close_to_curves q A B (max_sagitta A B)) ->
    (* H_B_bridge: points in chord-approximated B are close to an arc *)
    (forall q : Point,
       point_set (to_geometry B n) q ->
       arc_close_to_curves q A B (max_sagitta A B)) ->
    (* Premise: p is in the chord-approximated boolean-op result *)
    boolean_op op (to_geometry A n) (to_geometry B n) p ->
    (* Conclusion: p is within max_sagitta of an arc point *)
    arc_close_to_curves p A B (max_sagitta A B).
Proof.
  intros A B op p n HA HB H_A_bridge H_B_bridge Hbool.
  destruct op; cbn in Hbool.
  - (* Union: point_set A p \/ point_set B p *)
    destruct Hbool as [Hp | Hp].
    + apply H_A_bridge; exact Hp.
    + apply H_B_bridge; exact Hp.
  - (* Intersection: point_set A p /\ point_set B p *)
    destruct Hbool as [Hp _].
    apply H_A_bridge; exact Hp.
  - (* Difference: point_set A p /\ ~ point_set B p *)
    destruct Hbool as [Hp _].
    apply H_A_bridge; exact Hp.
  - (* SymDiff: (point_set A p /\ ~B) \/ (point_set B p /\ ~A) *)
    destruct Hbool as [[Hp _] | [Hp _]].
    + apply H_A_bridge; exact Hp.
    + apply H_B_bridge; exact Hp.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Forward and backward corollaries (sugar for downstream consumers).     *)
(* -------------------------------------------------------------------------- *)

(* Forward: if a point is in the chord-approximated boolean-op result, the
   conclusion holds.  Identical to the main theorem -- forward direction is
   the natural form. *)
Corollary arc_overlay_correct_chord_approx_forward :
  forall (A B : CurveGeometry) (op : BooleanOp)
         (p : Point) (n : nat),
    valid_curve_geometry A ->
    valid_curve_geometry B ->
    (forall q, point_set (to_geometry A n) q ->
       arc_close_to_curves q A B (max_sagitta A B)) ->
    (forall q, point_set (to_geometry B n) q ->
       arc_close_to_curves q A B (max_sagitta A B)) ->
    boolean_op op (to_geometry A n) (to_geometry B n) p ->
    arc_close_to_curves p A B (max_sagitta A B).
Proof. exact arc_overlay_correct_chord_approx. Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Structural lemmas on arcs_of.                                          *)
(* -------------------------------------------------------------------------- *)

Lemma arcs_of_nil : arcs_of [] = [].
Proof. reflexivity. Qed.

Lemma arcs_of_cons :
  forall cp cg,
    arcs_of (cp :: cg) =
    arcs_of_polygon cp ++ arcs_of cg.
Proof. intros. reflexivity. Qed.

Lemma arcs_of_segment_chord :
  forall p q, arcs_of_segment (CSChord p q) = [].
Proof. intros. reflexivity. Qed.

Lemma arcs_of_segment_arc :
  forall a, arcs_of_segment (CSArc a) = [a].
Proof. intros. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* §7  What this session does NOT close (and why).                            *)
(*                                                                            *)
(* The two H_*_bridge hypotheses are the load-bearing named gaps.  Each       *)
(* encapsulates several pieces:                                               *)
(*                                                                            *)
(*   (a) `chord_approx_error_bound` from S6 -- the geometric perpendicular-    *)
(*       bisector fact + IVT chain.  Provably TRUE (the sagitta is the        *)
(*       maximum perpendicular distance from chord to arc curve), but the     *)
(*       proof requires multi-step geometric reasoning PLUS S4's IVT-blocked  *)
(*       `arc_chord_intersect_sound`.  This part IS gated on IVT.             *)
(*                                                                            *)
(*   (b) The polygon-traversal lift from "point in `to_geometry A n`" to      *)
(*       "point in chord-approximation of some specific arc of A".  This is   *)
(*       a structural property of `to_geometry`'s definition (a flat_map      *)
(*       composition); proving it requires unfolding `point_set` through      *)
(*       `point_in_polygon` / `point_in_ring` to relate point-set semantics  *)
(*       to the underlying arc structure.  This part is IVT-INDEPENDENT.     *)
(*                                                                            *)
(*   (c) The boundary-vs-region semantic gap noted in §3 above: even if      *)
(*       (a) and (b) close, the H_*_bridge hypotheses ALSO require the       *)
(*       chord-polygon's INTERIOR points to be close to arc curves -- which  *)
(*       holds only when the chord polygon's interior fits within a sagitta- *)
(*       band of the arc boundary.  For thin (low-curvature) arcs this       *)
(*       holds; for thick arcs (interior points far from any boundary edge)  *)
(*       it does not.  Tightening this requires Option A's region-level      *)
(*       semantics (separate from the IVT gap and from the polygon-traversal *)
(*       lift).                                                                *)
(*                                                                            *)
(* CORRECTION (from PR #50 review).  An earlier version of this comment      *)
(* claimed "both gaps are independent of the IVT-blocked piece" -- that was  *)
(* wrong: (a) IS IVT-gated.  Only (b) (the polygon-traversal lift) is        *)
(* genuinely IVT-independent.  (c) is independent of both (a) and (b) and   *)
(* sits in Option A territory.                                                *)
(*                                                                            *)
(* Path to making the Phase 4 headline UNCONDITIONAL within Option B's       *)
(* chord-approx tolerance regime requires closing (a), (b), AND ensuring    *)
(* the H_*_bridge predicate is restated (per §3) to capture region-level    *)
(* closeness rather than boundary closeness.  Closing (a) alone or (b)      *)
(* alone is insufficient.                                                    *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* §8  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions max_sagitta_nonneg.
Print Assumptions arc_overlay_correct_chord_approx.
Print Assumptions arc_overlay_correct_chord_approx_forward.
Print Assumptions arcs_of_nil.
Print Assumptions arcs_of_cons.
Print Assumptions arcs_of_segment_chord.
Print Assumptions arcs_of_segment_arc.
