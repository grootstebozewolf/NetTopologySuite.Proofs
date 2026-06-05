(* ============================================================================
   NetTopologySuite.Proofs.ConvexField
   ----------------------------------------------------------------------------
   The convex specialisation of the IVT separation engine: the separating
   field as the minimum over a list of half-plane inward slacks.

   The rectangle (box_min, four slabs) and the right triangle (tri_min, two
   slabs + the affine hypotenuse distance) both instantiate the same shape: a
   `Rmin` over affine "inward distance to an edge line" functions.  This module
   captures that pattern once, for an arbitrary list of half-planes, giving:

     conv_min hps pt  := Rmin over [ hp_slack hp pt | hp <- hps ]   (>0 inside)

   with
     - `conv_min_pos_iff`         : >0  <->  every slack is >0 (strict interior
                                    of the half-plane intersection);
     - `continuity_pt_conv_min_path` : continuity along any continuous path
                                    (each slack is affine);
     - `convex_separation`        : the engine wrapper -- a `conv_min` field that
                                    is nonzero off the ring skeleton, positive at
                                    p, with bounded positive region, forces
                                    `in_bounded_component_cont r p`.

   A convex polygon then discharges its bounded-component obligation by giving
   its edge half-planes plus the (shape-specific) facts that the field's zero set
   lies on the ring skeleton and its positive region is bounded.  No new axioms.

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (claude-opus-4-8)
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From Stdlib Require Import Ranalysis.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam.
From NTS.Proofs Require Import RectangleSeparation SeparationField.
Import ListNotations.

Local Open Scope R_scope.

(* A half-plane (a, b, c) is { (x,y) | a*x + b*y <= c }; its inward slack is
   c - (a*x + b*y), strictly positive on the open side. *)
Definition hp_slack (hp : R * R * R) (pt : Point) : R :=
  let '(a, b, c) := hp in c - (a * px pt + b * py pt).

(* The convex field: min of the slacks, with a positive sentinel for the empty
   intersection (the whole plane). *)
Fixpoint conv_min (hps : list (R * R * R)) (pt : Point) : R :=
  match hps with
  | [] => 1
  | hp :: rest => Rmin (hp_slack hp pt) (conv_min rest pt)
  end.

(* Positivity = strictly inside every half-plane. *)
Lemma conv_min_pos_iff : forall hps pt,
  0 < conv_min hps pt <-> Forall (fun hp => 0 < hp_slack hp pt) hps.
Proof.
  induction hps as [| hp rest IH]; intros pt; simpl.
  - split; [ intros _; constructor | intros _; lra ].
  - rewrite Rmin_pos_iff, IH. split.
    + intros [Ha Hf]; constructor; assumption.
    + intros HF; inversion HF; subst; split; assumption.
Qed.

(* Each slack is affine, hence continuous along any continuous path. *)
Lemma continuity_pt_hp_slack_path : forall hp (g : R -> Point) t,
  continuity_pt (fun s => px (g s)) t ->
  continuity_pt (fun s => py (g s)) t ->
  continuity_pt (fun s => hp_slack hp (g s)) t.
Proof.
  intros [[a b] c] g t Hu Hv. unfold hp_slack; cbn [fst snd].
  apply continuity_pt_minus.
  - apply continuity_pt_const; intros ? ?; reflexivity.
  - apply continuity_pt_plus; apply continuity_pt_scal; assumption.
Qed.

Lemma continuity_pt_conv_min_path : forall hps (g : R -> Point) t,
  continuity_pt (fun s => px (g s)) t ->
  continuity_pt (fun s => py (g s)) t ->
  continuity_pt (fun s => conv_min hps (g s)) t.
Proof.
  induction hps as [| hp rest IH]; intros g t Hu Hv; simpl.
  - apply continuity_pt_const; intros ? ?; reflexivity.
  - apply continuity_pt_Rmin;
      [ apply continuity_pt_hp_slack_path; assumption | apply IH; assumption ].
Qed.

(* -------------------------------------------------------------------------- *)
(* The convex separation wrapper.                                              *)
(* -------------------------------------------------------------------------- *)

Theorem convex_separation :
  forall (r : Ring) (hps : list (R * R * R)) (p : Point) (M : R),
    (forall pt, ring_complement r pt -> conv_min hps pt <> 0) ->
    0 < conv_min hps p ->
    0 < M ->
    (forall pt, 0 < conv_min hps pt -> px pt * px pt + py pt * py pt <= M * M) ->
    in_bounded_component_cont r p.
Proof.
  intros r hps p M Hnz Hp HM Hbound.
  apply (separation_via_field r (conv_min hps) p M); try assumption.
  intros g Hcx Hcy t. apply continuity_pt_conv_min_path; [ apply Hcx | apply Hcy ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions conv_min_pos_iff.
Print Assumptions convex_separation.
