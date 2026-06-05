(* ============================================================================
   NetTopologySuite.Proofs.Convex
   ----------------------------------------------------------------------------
   Convex combinations, the convex-set predicate, and a few worked examples
   (half-planes, the whole plane, intersections).

   Underpins later results about convex hulls, polygon-in-polygon
   containment, and the geometric correctness of buffer offsets at convex
   corners.  At this stage we prove the foundational closure properties;
   the hull algorithm itself is downstream.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From NTS.Proofs Require Import Distance Orientation Segment.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* The convex combination of two points with parameter t.                     *)
(* -------------------------------------------------------------------------- *)

Definition convex_combination (P Q : Point) (t : R) : Point :=
  mkPoint ((1 - t) * px P + t * px Q) ((1 - t) * py P + t * py Q).

Lemma convex_combination_at_0 : forall P Q,
  convex_combination P Q 0 = P.
Proof.
  intros P Q. unfold convex_combination. destruct P. simpl. f_equal; ring.
Qed.

Lemma convex_combination_at_1 : forall P Q,
  convex_combination P Q 1 = Q.
Proof.
  intros P Q. unfold convex_combination. destruct Q. simpl. f_equal; ring.
Qed.

Lemma convex_combination_self : forall P t,
  convex_combination P P t = P.
Proof.
  intros P t. unfold convex_combination. destruct P. simpl. f_equal; ring.
Qed.

Lemma convex_combination_symmetric : forall P Q t,
  convex_combination P Q t = convex_combination Q P (1 - t).
Proof.
  intros P Q t. unfold convex_combination. simpl. f_equal; ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Relation to `between` from Segment.v: a point is on the closed segment    *)
(* iff it is a convex combination of the endpoints with parameter in [0,1].  *)
(* -------------------------------------------------------------------------- *)

Lemma between_iff_convex_combo : forall P Q R,
  between P Q R <->
  exists t, 0 <= t <= 1 /\ R = convex_combination P Q t.
Proof.
  intros P Q R. split.
  - intros [t [Ht0 [Ht1 [Hx Hy]]]]. exists t. split; [lra |].
    unfold convex_combination. destruct R. simpl in *. f_equal; assumption.
  - intros [t [[Ht0 Ht1] Heq]].
    exists t. split; [lra | split; [lra |]].
    rewrite Heq. unfold convex_combination. simpl. split; ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* A set (predicate over Point) is convex if it is closed under convex       *)
(* combinations of any two of its members.                                    *)
(* -------------------------------------------------------------------------- *)

Definition is_convex (S : Point -> Prop) : Prop :=
  forall P Q t,
    S P -> S Q -> 0 <= t -> t <= 1 ->
    S (convex_combination P Q t).

(* -------------------------------------------------------------------------- *)
(* The entire plane is trivially convex.                                      *)
(* -------------------------------------------------------------------------- *)

Lemma whole_plane_is_convex : is_convex (fun _ => True).
Proof. unfold is_convex. intros. trivial. Qed.

(* -------------------------------------------------------------------------- *)
(* Intersection of two convex sets is convex.                                 *)
(* -------------------------------------------------------------------------- *)

Lemma intersection_is_convex : forall S1 S2,
  is_convex S1 -> is_convex S2 ->
  is_convex (fun P => S1 P /\ S2 P).
Proof.
  intros S1 S2 H1 H2. unfold is_convex.
  intros P Q t [HP1 HP2] [HQ1 HQ2] Ht0 Ht1.
  split.
  - apply H1; assumption.
  - apply H2; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* A half-plane defined by a linear inequality is convex.  This is the       *)
(* worked example that, intersected with itself n times, gives any convex   *)
(* polygon's interior+boundary.                                              *)
(* -------------------------------------------------------------------------- *)

Definition half_plane (a b c : R) (p : Point) : Prop :=
  a * px p + b * py p <= c.

Lemma half_plane_is_convex : forall a b c,
  is_convex (half_plane a b c).
Proof.
  intros a b c. unfold is_convex, half_plane, convex_combination.
  intros P Q t HP HQ Ht0 Ht1. simpl.
  (* a*((1-t)*px P + t*px Q) + b*((1-t)*py P + t*py Q) <= c *)
  (* = (1-t) * (a*px P + b*py P) + t * (a*px Q + b*py Q) <= c *)
  (* The convex combination of two values each <= c is itself <= c. *)
  nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* The closed half-plane on the "other side" is also convex (the dual).      *)
(* -------------------------------------------------------------------------- *)

Definition half_plane_ge (a b c : R) (p : Point) : Prop :=
  a * px p + b * py p >= c.

Lemma half_plane_ge_is_convex : forall a b c,
  is_convex (half_plane_ge a b c).
Proof.
  intros a b c. unfold is_convex, half_plane_ge, convex_combination.
  intros P Q t HP HQ Ht0 Ht1. simpl. nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Empty set and singleton.                                                   *)
(* -------------------------------------------------------------------------- *)

Lemma empty_set_is_convex : is_convex (fun _ => False).
Proof. unfold is_convex. intros. contradiction. Qed.

Lemma singleton_is_convex : forall P,
  is_convex (fun X => X = P).
Proof.
  intros P. unfold is_convex.
  intros Q R t HQ HR Ht0 Ht1. subst.
  unfold convex_combination. destruct P. simpl. f_equal; ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Convex combination is symmetric/affine.                                    *)
(* -------------------------------------------------------------------------- *)

Lemma convex_combination_swap_endpoints : forall P Q t,
  convex_combination P Q t = convex_combination Q P (1 - t).
Proof. apply convex_combination_symmetric. Qed.

Lemma convex_combination_t_zero : forall P Q,
  convex_combination P Q 0 = P.
Proof. apply convex_combination_at_0. Qed.

Lemma convex_combination_t_one : forall P Q,
  convex_combination P Q 1 = Q.
Proof. apply convex_combination_at_1. Qed.

Lemma convex_combination_x_formula : forall P Q t,
  px (convex_combination P Q t) = (1 - t) * px P + t * px Q.
Proof. intros. unfold convex_combination. reflexivity. Qed.

Lemma convex_combination_y_formula : forall P Q t,
  py (convex_combination P Q t) = (1 - t) * py P + t * py Q.
Proof. intros. unfold convex_combination. reflexivity. Qed.

Lemma convex_combination_translate : forall P Q t dx dy,
  convex_combination (mkPoint (px P + dx) (py P + dy))
                     (mkPoint (px Q + dx) (py Q + dy)) t
  = mkPoint (px (convex_combination P Q t) + dx)
            (py (convex_combination P Q t) + dy).
Proof.
  intros. unfold convex_combination. simpl. f_equal; ring.
Qed.

Lemma convex_combination_scale : forall P Q t c,
  convex_combination (mkPoint (c * px P) (c * py P))
                     (mkPoint (c * px Q) (c * py Q)) t
  = mkPoint (c * px (convex_combination P Q t))
            (c * py (convex_combination P Q t)).
Proof.
  intros. unfold convex_combination. simpl. f_equal; ring.
Qed.

Lemma convex_combo_collinear : forall P Q t,
  cross P Q (convex_combination P Q t) = 0.
Proof.
  intros P Q t. unfold cross, convex_combination. simpl. ring.
Qed.

Lemma between_implies_convex_combo : forall P Q R,
  between P Q R -> exists t, 0 <= t <= 1 /\ R = convex_combination P Q t.
Proof. intros P Q R H. apply between_iff_convex_combo. exact H. Qed.

Lemma convex_combo_implies_between : forall P Q t,
  0 <= t -> t <= 1 -> between P Q (convex_combination P Q t).
Proof.
  intros P Q t Ht0 Ht1. apply between_iff_convex_combo.
  exists t. split; [lra | reflexivity].
Qed.

Lemma is_convex_universe : is_convex (fun _ => True).
Proof. apply whole_plane_is_convex. Qed.

(* -------------------------------------------------------------------------- *)
(* Closed segments are convex sets.                                           *)
(* -------------------------------------------------------------------------- *)

Lemma closed_segment_is_convex : forall A B,
  is_convex (between A B).
Proof.
  intros A B. unfold is_convex.
  intros P Q t [tp [Htp0 [Htp1 [HPx HPy]]]] [tq [Htq0 [Htq1 [HQx HQy]]]] Ht0 Ht1.
  exists ((1 - t) * tp + t * tq).
  split; [nra |].
  split; [nra |].
  unfold convex_combination in *. simpl in *.
  split.
  - rewrite HPx, HQx. ring.
  - rewrite HPy, HQy. ring.
Qed.

Lemma half_plane_at_origin : half_plane 0 0 0 (mkPoint 0 0).
Proof. unfold half_plane. simpl. lra. Qed.

Lemma half_plane_contains_origin_iff : forall a b c,
  half_plane a b c (mkPoint 0 0) <-> 0 <= c.
Proof.
  intros. unfold half_plane. simpl. split; intros; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions half_plane_is_convex.
Print Assumptions intersection_is_convex.
