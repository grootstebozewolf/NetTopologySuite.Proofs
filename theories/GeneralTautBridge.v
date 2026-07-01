(* ============================================================================
   NetTopologySuite.Proofs.GeneralTautBridge
   ----------------------------------------------------------------------------
   THE GENERAL RING-CLASS BRIDGE: extending the taut polygonal Jordan seam
   (`JCTEscapeDescentHolds.parity_seam_offring_taut`) from the single concrete
   instance discharged so far (`TriangleTautBridge.tri_ring_taut`, a bespoke
   `nsatz` argument tied to the triangle's three edges) to ARBITRARY simple
   rings.

   `TriangleTautBridge.v` flagged the exact obstruction under "HONEST
   OBSTRUCTION": `ring_simple` forbids PROPER crossings but not T-junctions (a
   foreign vertex sitting in another edge's relative interior), while
   `ring_taut` forbids both -- so no general bridge from `ring_simple` alone
   was available, only per-shape ad-hoc arguments.

   This file supplies the missing noding predicate and closes the gap
   completely and generically:

     `ring_no_vertex_on_foreign_edge_interior` : no endpoint of a distinct edge
       lies in another edge's OPEN interior (the precise T-junction ban).

     `ring_taut_of_simple_and_no_foreign_vertex` :
       ring_simple r -> ring_no_vertex_on_foreign_edge_interior r -> ring_taut r.

       Proof shape: `ring_taut`'s defining coincidence, for e <> f, splits on
       where the coincidence parameter t (along e) lands.  t in {0,1} closes
       the goal immediately (that IS the conclusion).  t strictly interior and
       s in {0,1} is exactly a foreign vertex of f sitting in e's interior --
       excluded by the new predicate.  t and s both strictly interior is
       exactly `segments_intersect_properly` -- excluded by `ring_simple`.
       No other case exists (t is decided against 0/1 by `Req_dec_T` on reals,
       not classical choice, so the corpus's axiom footprint is unchanged).

     `parity_seam_offring_of_simple` : the capstone.  Any ring that is
       `ring_simple`, T-junction-free, vertex-distinct (`ring_core_nodup`) and
       has no horizontal edge (`no_horizontal_edges`) satisfies the corrected
       off-ring H1 biconditional `parity_characterises_interior_cont_offring`
       -- UNCONDITIONALLY, with no per-shape combinatorial argument.  This is
       the literal generalization the rectangle/triangle/diamond families were
       each discharged by bespoke means: one theorem now covers every simple
       polygon (convex or NOT) satisfying the natural generic-position guards.

   DEMONSTRATION OF GENERALITY (§3): the rectangle, triangle and diamond
   families discharged so far are all CONVEX.  To show this bridge is a
   genuine generalization and not just a repackaging of the triangle argument,
   §3 instantiates it on a concrete NON-CONVEX simple quadrilateral (a "dart" /
   arrowhead with one reflex vertex) that no prior file in the corpus covers.

   Pure-R; classical-reals trio only (no new axioms; `Req_dec_T` is a
   constructive decision procedure already used pervasively in the corpus).
   No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List.
From NTS.Proofs Require Import Distance Overlay.
From NTS.Proofs Require Import JordanCurveSeam PointInRingCorrect PointInRingTangents.
From NTS.Proofs Require Import JCTTautClearance JCTRingCycle JCTHugStep.
From NTS.Proofs Require Import JCT_OnEdgeCounterexample JCTEscapeDescentHolds.
Import ListNotations.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §0  Decidable equality on Point/Edge from `Req_dec_T` (no new axioms: this  *)
(* is the same real-number trichotomy decision already used throughout the    *)
(* corpus, e.g. RelateNG's `point_eqb`).                                      *)
(* -------------------------------------------------------------------------- *)

Lemma point_eq_dec_r : forall p q : Point, {p = q} + {p <> q}.
Proof.
  intros p q.
  destruct (Req_dec_T (px p) (px q)) as [Hx | Hx].
  - destruct (Req_dec_T (py p) (py q)) as [Hy | Hy].
    + left. destruct p as [px0 py0]; destruct q as [px1 py1].
      cbn in Hx, Hy. subst. reflexivity.
    + right. intro H. apply Hy. rewrite H. reflexivity.
  - right. intro H. apply Hx. rewrite H. reflexivity.
Qed.

Lemma edge_eq_dec_r : forall e f : Edge, {e = f} + {e <> f}.
Proof.
  intros [p1 p2] [q1 q2].
  destruct (point_eq_dec_r p1 q1) as [-> | Hne1].
  - destruct (point_eq_dec_r p2 q2) as [-> | Hne2].
    + left; reflexivity.
    + right; congruence.
  - right; congruence.
Qed.

(* -------------------------------------------------------------------------- *)
(* §1  The missing noding predicate: no T-junctions.                          *)
(* -------------------------------------------------------------------------- *)

(* No endpoint of a distinct edge f lies in the OPEN interior of e.  Together
   with `ring_simple` (no proper interior-interior crossings) this is exactly
   the classical "simple polygon" noding condition. *)
Definition ring_no_vertex_on_foreign_edge_interior (r : Ring) : Prop :=
  forall e f : Edge,
    In e (ring_edges r) -> In f (ring_edges r) -> e <> f ->
    (~ exists t : R, 0 < t < 1 /\
         px (fst f) = (1 - t) * px (fst e) + t * px (snd e) /\
         py (fst f) = (1 - t) * py (fst e) + t * py (snd e))
    /\
    (~ exists t : R, 0 < t < 1 /\
         px (snd f) = (1 - t) * px (fst e) + t * px (snd e) /\
         py (snd f) = (1 - t) * py (fst e) + t * py (snd e)).

(* -------------------------------------------------------------------------- *)
(* §2  THE BRIDGE: ring_simple + no-T-junctions => ring_taut.                  *)
(* -------------------------------------------------------------------------- *)

Lemma ring_taut_of_simple_and_no_foreign_vertex : forall r : Ring,
  ring_simple r ->
  ring_no_vertex_on_foreign_edge_interior r ->
  ring_taut r.
Proof.
  intros r Hsimple Hnov e f He Hf t s Ht Hs Hx Hy.
  destruct (Req_dec_T t 0) as [Ht0 | Ht0'].
  - left; left; exact Ht0.
  - destruct (Req_dec_T t 1) as [Ht1 | Ht1'].
    + left; right; exact Ht1.
    + assert (Htint : 0 < t < 1) by lra.
      destruct (edge_eq_dec_r e f) as [Hef | Hef].
      * right. subst f. split; reflexivity.
      * exfalso.
        destruct (Req_dec_T s 0) as [Hs0 | Hs0'].
        -- subst s.
           assert (Hx' : px (fst f) = (1 - t) * px (fst e) + t * px (snd e)) by lra.
           assert (Hy' : py (fst f) = (1 - t) * py (fst e) + t * py (snd e)) by lra.
           destruct (Hnov e f He Hf Hef) as [Hnov1 _].
           apply Hnov1. exists t. auto.
        -- destruct (Req_dec_T s 1) as [Hs1 | Hs1'].
           ++ subst s.
              assert (Hx' : px (snd f) = (1 - t) * px (fst e) + t * px (snd e)) by lra.
              assert (Hy' : py (snd f) = (1 - t) * py (fst e) + t * py (snd e)) by lra.
              destruct (Hnov e f He Hf Hef) as [_ Hnov2].
              apply Hnov2. exists t. auto.
           ++ assert (Hsint : 0 < s < 1) by lra.
              apply (Hsimple e f He Hf Hef).
              exists t, s.
              split; [ exact Htint | split; [ exact Hsint | split; [ exact Hx | exact Hy ] ] ].
Qed.

(* -------------------------------------------------------------------------- *)
(* CAPSTONE: the fully general polygonal Jordan seam.  ANY simple ring         *)
(* (convex or not) satisfying the natural noding + generic-position guards    *)
(* discharges the corrected off-ring H1 biconditional -- no per-shape          *)
(* combinatorial argument needed.                                            *)
(* -------------------------------------------------------------------------- *)

Theorem parity_seam_offring_of_simple : forall (r : Ring) (p : Point),
  ring_simple r ->
  ring_no_vertex_on_foreign_edge_interior r ->
  ring_core_nodup r ->
  no_horizontal_edges r ->
  parity_characterises_interior_cont_offring p r.
Proof.
  intros r p Hsimple Hnov Hnd Hnoh.
  apply parity_seam_offring_taut.
  - exact (ring_taut_of_simple_and_no_foreign_vertex r Hsimple Hnov).
  - exact Hnd.
  - exact Hnoh.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  DEMONSTRATION: a NON-CONVEX simple polygon, beyond rectangle/triangle/  *)
(* diamond (all convex).  The "dart" / arrowhead quadrilateral                *)
(*                                                                            *)
(*        B=(2,1)                                                            *)
(*         /|                                                                *)
(*        / |                                                                *)
(*   A---+  | C=(1,0) is a REFLEX vertex (pulled toward A): the notch.       *)
(* (0,0) \  |                                                                *)
(*        \ |                                                                *)
(*        D=(2,-1)                                                           *)
(*                                                                            *)
(* ring = A,B,C,D,A.  C sits INSIDE the triangle A-B-D, making the polygon    *)
(* concave at C -- no convexity, no CCW/signed-area machinery anywhere in     *)
(* this section, only the four ring-class predicates.                        *)
(* -------------------------------------------------------------------------- *)

Definition dart_A : Point := mkPoint 0 0.
Definition dart_B : Point := mkPoint 2 1.
Definition dart_C : Point := mkPoint 1 0.
Definition dart_D : Point := mkPoint 2 (-1).

Definition dart_ring : Ring := [dart_A; dart_B; dart_C; dart_D; dart_A].

Lemma dart_ring_edges :
  ring_edges dart_ring =
    (dart_A, dart_B) :: (dart_B, dart_C) :: (dart_C, dart_D) :: (dart_D, dart_A) :: nil.
Proof. reflexivity. Qed.

Lemma dart_ring_closed : ring_closed dart_ring.
Proof. exists dart_A, [dart_B; dart_C; dart_D]. reflexivity. Qed.

Lemma dart_min_points : ring_has_minimum_points dart_ring.
Proof. unfold ring_has_minimum_points, dart_ring. simpl. lia. Qed.

Lemma dart_core_nodup : ring_core_nodup dart_ring.
Proof.
  exists dart_A, [dart_B; dart_C; dart_D]. split; [ reflexivity | ].
  unfold dart_A, dart_B, dart_C, dart_D.
  constructor.
  - intro Hin. simpl in Hin.
    destruct Hin as [H | [H | [H | []]]]; injection H; intros; lra.
  - constructor.
    + intro Hin. simpl in Hin.
      destruct Hin as [H | [H | []]]; injection H; intros; lra.
    + constructor.
      * intro Hin. simpl in Hin.
        destruct Hin as [H | []]; injection H; intros; lra.
      * constructor; [ intro Hin; exact Hin | constructor ].
Qed.

Lemma dart_no_horizontal_edges : no_horizontal_edges dart_ring.
Proof.
  intros g Hg. rewrite dart_ring_edges in Hg. simpl in Hg.
  destruct Hg as [H | [H | [H | [H | []]]]]; subst g;
    unfold dart_A, dart_B, dart_C, dart_D; cbn [fst snd py]; lra.
Qed.

(* No proper crossings: the two pairs of non-adjacent edges (AB/CD and BC/DA)
   never meet at simultaneously-interior parameters. *)
Lemma dart_ring_simple : ring_simple dart_ring.
Proof.
  intros e1 e2 H1 H2 Hne Hcross.
  rewrite dart_ring_edges in H1, H2. simpl in H1, H2.
  destruct Hcross as [t [s [[Ht0 Ht1] [[Hs0 Hs1] [Hx Hy]]]]].
  destruct H1 as [E1 | [E1 | [E1 | [E1 | []]]]];
  destruct H2 as [E2 | [E2 | [E2 | [E2 | []]]]];
    subst e1 e2; unfold dart_A, dart_B, dart_C, dart_D in Hx, Hy;
    cbn [fst snd px py] in Hx, Hy, Hne;
    try (exfalso; apply Hne; reflexivity);
    nra.
Qed.

(* No T-junctions: no vertex of the dart lies in the open interior of a
   non-incident edge. *)
Lemma dart_no_foreign_vertex : ring_no_vertex_on_foreign_edge_interior dart_ring.
Proof.
  intros e f He Hf Hef.
  rewrite dart_ring_edges in He, Hf. simpl in He, Hf.
  unfold dart_A, dart_B, dart_C, dart_D in *.
  destruct He as [He | [He | [He | [He | []]]]];
  destruct Hf as [Hf | [Hf | [Hf | [Hf | []]]]];
    subst e f; cbn [fst snd px py];
    split; intros [t [[Ht0 Ht1] [Hx Hy]]];
    try (apply Hef; reflexivity);
    nra.
Qed.

(* THE CAPSTONE, instantiated on a genuinely non-convex simple polygon: the
   corrected off-ring H1 biconditional holds for the dart at every off-ring,
   ray-generic, horizontal-free-height point -- exactly the same guard set as
   the triangle instance, now realized on a concave shape. *)
Theorem dart_parity_seam_offring : forall p : Point,
  ring_complement dart_ring p ->
  no_horizontal_edge_at p dart_ring ->
  ray_avoids_vertices p dart_ring ->
  (geometric_interior_cont p dart_ring <-> point_in_ring p dart_ring).
Proof.
  intros p Hcompl Hnoh Hrav.
  apply (parity_seam_offring_of_simple dart_ring p
           dart_ring_simple dart_no_foreign_vertex dart_core_nodup
           dart_no_horizontal_edges).
  - exact dart_ring_simple.
  - exact dart_ring_closed.
  - exact dart_min_points.
  - exact Hcompl.
  - exact Hnoh.
  - exact Hrav.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions ring_taut_of_simple_and_no_foreign_vertex.
Print Assumptions parity_seam_offring_of_simple.
Print Assumptions dart_ring_simple.
Print Assumptions dart_no_foreign_vertex.
Print Assumptions dart_parity_seam_offring.
