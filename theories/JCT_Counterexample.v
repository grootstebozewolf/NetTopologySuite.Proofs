(* ============================================================================
   NetTopologySuite.Proofs.JCT_Counterexample
   ----------------------------------------------------------------------------
   Why `ring_simple` is NOT enough for the polygonal Jordan Curve Theorem:
   the self-touching "bowtie" (figure-8) counterexample.

   `JordanCurveSeam.v` carries the honest, continuity-bearing hypothesis
   `JCT_two_components_cont r`, guarded by THREE structural premises:
   `ring_simple r`, `ring_closed r`, `ring_has_minimum_points r`.  The
   eventual goal of the seam is to discharge that hypothesis for genuine
   simple polygons.

   This file shows that the THREE premises as currently stated are NOT
   sufficient: there is a closed ring with >= 4 vertices that is
   `ring_simple` -- yet violates the two-component conclusion.  Hence
   `forall r, JCT_two_components_cont r` is FALSE as stated; the premise
   set must be strengthened (to genuine curve injectivity / no self-touch),
   not merely to "no proper crossing".

   The witness is the figure-8 made of two triangles that meet ONLY at the
   shared origin vertex:

       Triangle R (right):  (0,0) -> (1,1)  -> (1,-1)  -> (0,0)
       Triangle L (left):   (0,0) -> (-1,1) -> (-1,-1) -> (0,0)

   The subtlety -- and the whole point -- is that `ring_simple` (Overlay.v)
   forbids only PROPER crossings (interior-interior, with parameters
   strictly inside (0,1)).  The two triangles meet only at the origin, which
   is an ENDPOINT of every edge incident to it, so NO pair of edges crosses
   properly.  The bowtie is therefore `ring_simple` (proved below,
   `bowtie_ring_simple`).  But the origin is a degree-4 vertex
   (`bowtie_origin_degree_four`): a non-manifold "pinch" that a genuine
   simple closed curve never has.  The complement splits into THREE pieces --
   left lobe, right lobe, unbounded exterior -- not two.

   WHAT IS PROVED HERE (all Qed-closed, no `Admitted`/`Axiom`/`Parameter`):

     - `bowtie_ring_closed`, `bowtie_min_points`, `bowtie_ring_simple`:
       the bowtie passes EVERY structural premise of `JCT_two_components_cont`.
     - `bowtie_origin_degree_four`: four distinct edges meet at the origin --
       the topological signature of a self-touch (degree 2 is mandatory for a
       simple closed curve).
     - `bowtie_parity_*`: the ray-casting predicate `point_in_ring` marks
       BOTH bounded lobes as interior and the far point as exterior -- exactly
       the misclassification a naive parity test makes on a non-simple curve.
     - `bowtie_refutes_two_components_modulo_separation` (RED): assuming the
       three (geometrically true, thesis-scale) component-separation facts --
       the left lobe, right lobe and exterior are pairwise unreachable by a
       CONTINUOUS complement path -- the bowtie's three premises hold yet
       `JCT_two_components_cont bowtie` is contradictory.  A two-set partition
       cannot cover three mutually disconnected components.
     - `bowtie_excluded_by_rescoped_JCT` (GREEN, §7): the precise fix.  Adding
       the OGC vertex-distinctness premise `ring_vertices_distinct` (which the
       bowtie violates, `bowtie_violates_vertex_distinctness`) re-scopes the
       hypothesis so the witness is correctly excluded.
     - `rescoping_resolves_the_bowtie`: RED and GREEN in one statement -- the
       bowtie refutes the old hypothesis but satisfies the re-scoped one, the
       single added premise being the whole difference.

   The separation facts are taken as explicit hypotheses, NOT proved and NOT
   axiomatised -- mirroring exactly how `JordanCurveSeam.v` treats
   `JCT_two_components_cont` itself (the trapped-interior half of the JCT is
   the genuine thesis-scale gap).  The contribution of this file is the
   REDUCTION: it isolates the false statement and pins the blame on the
   `ring_simple`-only premise set.

   See docs/jct-bowtie-counterexample.md for the prose writeup and the
   premise-strengthening recommendation.

   Pure-R; no atan / Flocq / `Classical_Prop.classic`.  No `Admitted`,
   no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import List.

From NTS.Proofs Require Import Distance.
From NTS.Proofs Require Import Overlay.
From NTS.Proofs Require Import PointInRingTangents.
From NTS.Proofs Require Import JordanCurveSeam.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The figure-8 bowtie and three test points.                             *)
(* -------------------------------------------------------------------------- *)

(* Two triangles sharing ONLY the origin vertex.  As a vertex list the
   origin is visited three times (positions 0, 3, 6): the closing vertex,
   plus the pinch where the two triangles meet. *)
Definition bowtie : Ring :=
  mkPoint 0 0
    :: mkPoint 1 1     :: mkPoint 1 (-1)
    :: mkPoint 0 0
    :: mkPoint (-1) 1  :: mkPoint (-1) (-1)
    :: mkPoint 0 0 :: nil.

(* Centroid-ish interior points of each lobe, on the x-axis. *)
Definition p_right    : Point := mkPoint (1/2) 0.    (* inside triangle R *)
Definition p_left     : Point := mkPoint (-1/2) 0.   (* inside triangle L *)
Definition p_exterior : Point := mkPoint 10 0.       (* unbounded exterior *)

(* The six edges, made explicit once so every downstream proof shares the
   same normal form. *)
Lemma bowtie_ring_edges :
  ring_edges bowtie =
       (mkPoint 0 0,      mkPoint 1 1)
    :: (mkPoint 1 1,      mkPoint 1 (-1))
    :: (mkPoint 1 (-1),   mkPoint 0 0)
    :: (mkPoint 0 0,      mkPoint (-1) 1)
    :: (mkPoint (-1) 1,   mkPoint (-1) (-1))
    :: (mkPoint (-1) (-1),mkPoint 0 0)
    :: nil.
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The bowtie passes every STRUCTURAL premise of JCT_two_components_cont. *)
(* -------------------------------------------------------------------------- *)

Lemma bowtie_ring_closed : ring_closed bowtie.
Proof.
  exists (mkPoint 0 0),
    [ mkPoint 1 1; mkPoint 1 (-1); mkPoint 0 0;
      mkPoint (-1) 1; mkPoint (-1) (-1) ].
  reflexivity.
Qed.

Lemma bowtie_min_points : ring_has_minimum_points bowtie.
Proof. unfold ring_has_minimum_points, bowtie. simpl. lia. Qed.

(* The crux: `ring_simple` forbids only PROPER (interior-interior) crossings.
   The two triangles meet only at the origin, which is an ENDPOINT of every
   incident edge, so no two distinct edges cross properly.  All 30 distinct
   ordered pairs reduce to an inconsistency under 0 < t < 1, 0 < s < 1. *)
Lemma bowtie_ring_simple : ring_simple bowtie.
Proof.
  intros e1 e2 H1 H2 Hne Hcross.
  rewrite bowtie_ring_edges in H1, H2.
  simpl in H1, H2.
  destruct Hcross as [t [s [[Ht0 Ht1] [[Hs0 Hs1] [Hx Hy]]]]].
  destruct H1 as [E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]];
  destruct H2 as [E2|[E2|[E2|[E2|[E2|[E2|[]]]]]]];
    subst e1 e2; simpl in Hx, Hy, Hne;
    try (exfalso; apply Hne; reflexivity);
    nra.
Qed.

(* The three premises bundled, for the headline. *)
Lemma bowtie_satisfies_all_structural_premises :
  ring_simple bowtie /\ ring_closed bowtie /\ ring_has_minimum_points bowtie.
Proof.
  split; [apply bowtie_ring_simple | split;
    [apply bowtie_ring_closed | apply bowtie_min_points]].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  ... yet it is NOT a simple closed curve: the origin has degree 4.      *)
(* -------------------------------------------------------------------------- *)

(* Four distinct edges of the ring are incident to the origin.  A genuine
   simple closed curve has every vertex of degree exactly 2; degree 4 is the
   self-touch that `ring_simple` (no-proper-crossing) fails to exclude. *)
Lemma bowtie_origin_degree_four :
  In (mkPoint 1 (-1),    mkPoint 0 0)   (ring_edges bowtie) /\
  In (mkPoint 0 0,       mkPoint 1 1)   (ring_edges bowtie) /\
  In (mkPoint (-1) (-1), mkPoint 0 0)   (ring_edges bowtie) /\
  In (mkPoint 0 0,       mkPoint (-1) 1)(ring_edges bowtie).
Proof.
  rewrite bowtie_ring_edges. simpl. tauto.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The three test points are off the ring.                                *)
(* -------------------------------------------------------------------------- *)

Lemma bowtie_off_right : ring_complement bowtie p_right.
Proof.
  unfold ring_complement, ring_image, p_right.
  intros [e [t [Hin [[Ht0 Ht1] [Hx Hy]]]]].
  rewrite bowtie_ring_edges in Hin. simpl in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]];
    subst e; simpl in Hx, Hy; lra.
Qed.

Lemma bowtie_off_left : ring_complement bowtie p_left.
Proof.
  unfold ring_complement, ring_image, p_left.
  intros [e [t [Hin [[Ht0 Ht1] [Hx Hy]]]]].
  rewrite bowtie_ring_edges in Hin. simpl in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]];
    subst e; simpl in Hx, Hy; lra.
Qed.

Lemma bowtie_off_exterior : ring_complement bowtie p_exterior.
Proof.
  unfold ring_complement, ring_image, p_exterior.
  intros [e [t [Hin [[Ht0 Ht1] [Hx Hy]]]]].
  rewrite bowtie_ring_edges in Hin. simpl in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]];
    subst e; simpl in Hx, Hy; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Ray-casting parity marks BOTH lobes interior, the far point exterior.  *)
(*                                                                            *)
(* Only the two vertical edges (x = 1 and x = -1) straddle the y = 0 ray; the *)
(* four origin-incident edges merely touch y = 0 at an endpoint and so are    *)
(* not counted.  For a lobe point the single right-hand vertical edge is      *)
(* crossed (odd -> "inside"); for the far point neither is (even ->           *)
(* "outside").  This is precisely the misclassification a naive parity test   *)
(* makes on a self-touching curve.                                            *)
(* -------------------------------------------------------------------------- *)

(* A non-crossing edge: either the y-straddle fails, or the x-intercept is
   not strictly to the right.  Both kill the crossing predicate. *)
Ltac no_cross :=
  let H := fresh "H" in
  intro H; unfold edge_crosses_ray in H; simpl in H;
  destruct H as [ [[? ?] ?] | [[? ?] ?] ]; lra.

(* A crossing edge: the downward vertical edge straddles y = 0 and its
   x-intercept sits strictly right of the (lobe) test point. *)
Ltac yes_cross :=
  unfold edge_crosses_ray; simpl; right; repeat split; lra.

Lemma bowtie_parity_right : point_in_ring p_right bowtie.
Proof.
  unfold point_in_ring, p_right. rewrite bowtie_ring_edges.
  apply rpo_skip;  [ no_cross | ].   (* (0,0)->(1,1)       *)
  apply rpo_cross; [ yes_cross | ].  (* (1,1)->(1,-1)  HIT *)
  apply rpe_skip;  [ no_cross | ].   (* (1,-1)->(0,0)      *)
  apply rpe_skip;  [ no_cross | ].   (* (0,0)->(-1,1)      *)
  apply rpe_skip;  [ no_cross | ].   (* (-1,1)->(-1,-1)    *)
  apply rpe_skip;  [ no_cross | ].   (* (-1,-1)->(0,0)     *)
  apply rpe_nil.
Qed.

Lemma bowtie_parity_left : point_in_ring p_left bowtie.
Proof.
  unfold point_in_ring, p_left. rewrite bowtie_ring_edges.
  apply rpo_skip;  [ no_cross | ].   (* (0,0)->(1,1)       *)
  apply rpo_cross; [ yes_cross | ].  (* (1,1)->(1,-1)  HIT *)
  apply rpe_skip;  [ no_cross | ].   (* (1,-1)->(0,0)      *)
  apply rpe_skip;  [ no_cross | ].   (* (0,0)->(-1,1)      *)
  apply rpe_skip;  [ no_cross | ].   (* (-1,1)->(-1,-1)    *)
  apply rpe_skip;  [ no_cross | ].   (* (-1,-1)->(0,0)     *)
  apply rpe_nil.
Qed.

(* Even-excludes-odd for the mutually-inductive ray parity, proved locally
   (the corpus has no such lemma).  Structural induction on the edge list;
   each step inverts both derivations and either contradicts the per-edge
   crossing classifier or recurses on the tail. *)
Lemma ray_parity_even_not_odd :
  forall (p : Point) (es : list Edge),
    ray_parity_even p es -> ~ ray_parity_odd p es.
Proof.
  intros p es; induction es as [|e es' IH]; intros Heven Hodd.
  - inversion Hodd.
  - inversion Heven; subst; inversion Hodd; subst;
      try (eapply IH; eassumption);
      try contradiction.
Qed.

Lemma bowtie_parity_exterior : ~ point_in_ring p_exterior bowtie.
Proof.
  unfold point_in_ring, p_exterior. rewrite bowtie_ring_edges.
  apply ray_parity_even_not_odd.
  apply rpe_skip; [ no_cross | ].   (* (0,0)->(1,1)    *)
  apply rpe_skip; [ no_cross | ].   (* (1,1)->(1,-1)   *)
  apply rpe_skip; [ no_cross | ].   (* (1,-1)->(0,0)   *)
  apply rpe_skip; [ no_cross | ].   (* (0,0)->(-1,1)   *)
  apply rpe_skip; [ no_cross | ].   (* (-1,1)->(-1,-1) *)
  apply rpe_skip; [ no_cross | ].   (* (-1,-1)->(0,0)  *)
  apply rpe_nil.
Qed.

(* The parity misclassification, bundled. *)
Lemma bowtie_parity_marks_both_lobes_interior :
  point_in_ring p_left bowtie /\
  point_in_ring p_right bowtie /\
  ~ point_in_ring p_exterior bowtie.
Proof.
  split; [apply bowtie_parity_left | split;
    [apply bowtie_parity_right | apply bowtie_parity_exterior]].
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  The refutation: the bowtie's premises hold, yet two-components fails.   *)
(*                                                                            *)
(* The complement of the figure-8 has THREE connected components -- the left  *)
(* lobe, the right lobe, and the unbounded exterior -- so no two of           *)
(* {p_left, p_right, p_exterior} share a component.  Those pairwise           *)
(* separation facts are the trapped-interior (thesis-scale) half of the JCT;  *)
(* they are taken here as explicit hypotheses, NOT proved -- exactly as        *)
(* `JCT_two_components_cont` itself is a named, unproved `Prop` in             *)
(* `JordanCurveSeam.v`.  Given them, the conclusion is contradictory: any       *)
(* JCT partition has only TWO classes (interior / exterior), each connected by *)
(* continuous complement paths, so by pigeonhole two of the three             *)
(* representatives land in one class -- forcing a continuous complement path   *)
(* between two separated components.                                          *)
(* -------------------------------------------------------------------------- *)

Theorem bowtie_refutes_two_components_modulo_separation :
  ~ connected_in_complement_cont bowtie p_left  p_right    ->
  ~ connected_in_complement_cont bowtie p_left  p_exterior ->
  ~ connected_in_complement_cont bowtie p_right p_exterior ->
  ~ JCT_two_components_cont bowtie.
Proof.
  intros Hlr Hle Hre HJCT.
  destruct (HJCT bowtie_ring_simple bowtie_ring_closed bowtie_min_points)
    as [ip [ep [Hpart [Hicon [Hecon _]]]]].
  destruct (Hpart p_left     bowtie_off_left)     as [HclL _].
  destruct (Hpart p_right    bowtie_off_right)    as [HclR _].
  destruct (Hpart p_exterior bowtie_off_exterior) as [HclE _].
  destruct HclL as [iL|eL];
  destruct HclR as [iR|eR];
  destruct HclE as [iE|eE].
  - apply Hlr. apply Hicon; assumption.   (* in in in : left ~ right     *)
  - apply Hlr. apply Hicon; assumption.   (* in in ex : left ~ right     *)
  - apply Hle. apply Hicon; assumption.   (* in ex in : left ~ exterior  *)
  - apply Hre. apply Hecon; assumption.   (* in ex ex : right ~ exterior *)
  - apply Hre. apply Hicon; assumption.   (* ex in in : right ~ exterior *)
  - apply Hle. apply Hecon; assumption.   (* ex in ex : left ~ exterior  *)
  - apply Hlr. apply Hecon; assumption.   (* ex ex in : left ~ right     *)
  - apply Hlr. apply Hecon; assumption.   (* ex ex ex : left ~ right     *)
Qed.

(* CONSEQUENCE (informal, recorded here as the take-away).  Because
   `bowtie_satisfies_all_structural_premises` holds while
   `bowtie_refutes_two_components_modulo_separation` shows the conclusion
   fails, the universally-quantified goal `forall r, JCT_two_components_cont r`
   is unprovable under the current premise set: `ring_simple` (no proper
   crossing) does not capture "simple closed curve".  The seam must add a
   curve-injectivity / no-self-touch premise (equivalently: every vertex of
   degree 2), which the bowtie's degree-4 origin violates.  §7 turns this
   take-away into theorems. *)

(* -------------------------------------------------------------------------- *)
(* §7  GREEN: the re-scoped hypothesis excludes the bowtie.                    *)
(*                                                                            *)
(* RED (§2-§6): `ring_simple` + `ring_closed` + `ring_has_minimum_points` is   *)
(* too weak -- the bowtie passes all three yet refutes two-components.  The    *)
(* fix is the OTHER half of the OGC "simple ring" condition that `ring_simple` *)
(* omits: VERTEX DISTINCTNESS (no repeated vertex apart from the closing one), *)
(* i.e. the curve is injective and every vertex has degree 2.  Here we make    *)
(* that premise precise, prove the bowtie violates it, and prove the re-scoped *)
(* hypothesis is therefore NOT refuted by the bowtie -- closing the loop the   *)
(* RED opened.                                                                 *)
(* -------------------------------------------------------------------------- *)

(* The missing premise `ring_vertices_distinct r := NoDup (removelast r)` -- the
   genuine vertices (closing vertex dropped) are pairwise distinct -- now lives
   upstream in Overlay.v (it is a ring-validity condition, used by the
   re-scoped seam in JordanCurveSeam.v). *)

(* The bowtie violates it: the origin is revisited (it is `removelast`'s head
   and also its 4th element) -- precisely the degree-4 pinch of §3. *)
Lemma bowtie_violates_vertex_distinctness :
  ~ ring_vertices_distinct bowtie.
Proof.
  unfold ring_vertices_distinct, bowtie. simpl.
  intro H. apply NoDup_cons_iff in H. destruct H as [Hnin _].
  apply Hnin. right. right. left. reflexivity.
Qed.

(* The re-scoped JCT hypothesis `JCT_two_components_cont_simple` (the body of
   `JCT_two_components_cont` additionally guarded by `ring_vertices_distinct`)
   now lives upstream in JordanCurveSeam.v, where the headline
   `jct_cont_interior_is_geometric` is stated against it. *)

(* GREEN.  Under the re-scoped hypothesis the bowtie is NO LONGER a
   counterexample: the obligation at the bowtie is dischargeable because the
   added vertex-distinctness premise is unsatisfiable for it.  Contrast
   `bowtie_refutes_two_components_modulo_separation` (RED), where the same ring
   against the unstrengthened `JCT_two_components_cont` was contradictory.
   Strengthening the premise -- and nothing else -- is exactly the fix. *)
Theorem bowtie_excluded_by_rescoped_JCT :
  JCT_two_components_cont_simple bowtie.
Proof.
  intros _ _ _ Hnodup.
  exfalso. apply bowtie_violates_vertex_distinctness. exact Hnodup.
Qed.

(* The RGR loop closed, in one statement: the bowtie REFUTES the old hypothesis
   (modulo the thesis-scale separation facts) but SATISFIES the re-scoped one.
   The single premise `ring_vertices_distinct` is the whole difference. *)
Theorem rescoping_resolves_the_bowtie :
  (~ connected_in_complement_cont bowtie p_left  p_right    ->
   ~ connected_in_complement_cont bowtie p_left  p_exterior ->
   ~ connected_in_complement_cont bowtie p_right p_exterior ->
   ~ JCT_two_components_cont bowtie)                              (* RED   *)
  /\ JCT_two_components_cont_simple bowtie.                       (* GREEN *)
Proof.
  split.
  - exact bowtie_refutes_two_components_modulo_separation.
  - exact bowtie_excluded_by_rescoped_JCT.
Qed.

