(* ============================================================================
   NetTopologySuite.Proofs.JCT_VertexGrazingCounterexample
   ----------------------------------------------------------------------------
   Why `no_horizontal_edge_at` is NOT enough to make ray-parity a faithful
   interior test: the vertex-grazing (degenerate-ray) counterexample.

   `JCT.v` carries the named remaining seam

       parity_characterises_interior_cont p r :=
         ring_simple r -> ring_closed r -> ring_has_minimum_points r ->
         no_horizontal_edge_at p r ->
         (geometric_interior_cont p r <-> point_in_ring p r).

   The intent is that this holds for every off-ring point of a valid simple
   polygon, so that the headline `point_in_ring_correct_jct_cont` discharges.
   This file shows the FOUR guards above are insufficient: there is a genuinely
   simple convex polygon (a diamond) and two off-ring points A, B such that the
   seam CANNOT hold at both -- so it is not universally true as stated.

   The witness is a convex DIAMOND with vertices (0,1),(1,0),(0,-1),(-1,0) and:

       A = (0, 1/2)   -- ray at height 1/2 crosses one edge (parity ODD)
       B = (0, 0)     -- ray at height 0 GRAZES the vertex (1,0): the strict
                         y-straddle in `edge_crosses_ray` counts NEITHER of the
                         two edges meeting at (1,0), so parity is EVEN.

   Both A and B satisfy all four guards (in particular `no_horizontal_edge_at`
   holds -- the diamond has NO horizontal edge -- yet it fails to exclude B).
   A and B lie in the SAME connected component of the complement (joined by the
   vertical segment x = 0), and `geometric_interior_cont` is a component
   invariant (JCT.v).  So if the seam held at both, the invariant
   `geometric_interior_cont` would have to agree with the NON-invariant
   `point_in_ring` on A and B -- impossible, since the parities differ.

   WHAT IS PROVED HERE (all Qed-closed, no `Admitted`/`Axiom`/`Parameter`):

     - `diamond_ring_simple`, `diamond_ring_closed`, `diamond_min_points`,
       `diamond_no_horizontal`: the diamond is a valid simple polygon and both
       test points pass `no_horizontal_edge_at`.
     - `diamond_point_in_ring_A` / `diamond_not_point_in_ring_B`: ray-parity is
       ODD at A but EVEN at B (the vertex graze).
     - `diamond_segment_off_ring`: A and B are joined by a CONTINUOUS complement
       path (so they share a component).
     - `geometric_interior_cont_invariant`: the continuous interior is a
       component invariant (assembled from JCT.v's bounded-component invariance).
     - `diamond_refutes_parity_seam` (RED): the seam cannot hold at both A and
       B; hence `parity_characterises_interior_cont` is not universally true for
       a valid simple polygon -- the four guards are insufficient.
     - `ray_avoids_vertices` + `diamond_excluded_by_strict_parity_seam` (GREEN):
       the precise fix.  Adding "no ring vertex lies on the rightward ray"
       (which B violates, `diamond_B_ray_hits_vertex`, but A satisfies) re-scopes
       the seam so the witness is excluded.  `no_horizontal_edge_at` alone does
       NOT exclude B (`diamond_guard_insufficient`).

   This is the continuous, vertex-grazing analogue of the bowtie scope finding
   (theories/JCT_Counterexample.v / docs/jct-bowtie-counterexample.md): there
   the missing premise was vertex DISTINCTNESS; here it is the generic-position
   guard that the rightward ray miss every vertex.

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
From NTS.Proofs Require Import PointInRingCorrect.
From NTS.Proofs Require Import JordanCurveSeam.
From NTS.Proofs Require Import JCT.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The diamond and two on-axis test points.                               *)
(* -------------------------------------------------------------------------- *)

Definition diamond : Ring :=
  mkPoint 0 1 :: mkPoint 1 0 :: mkPoint 0 (-1) :: mkPoint (-1) 0 :: mkPoint 0 1 :: nil.

Definition A : Point := mkPoint 0 (1/2).   (* ray crosses one edge: parity ODD  *)
Definition B : Point := mkPoint 0 0.       (* ray grazes vertex (1,0): parity EVEN *)

Lemma diamond_ring_edges :
  ring_edges diamond =
       (mkPoint 0 1,    mkPoint 1 0)
    :: (mkPoint 1 0,    mkPoint 0 (-1))
    :: (mkPoint 0 (-1), mkPoint (-1) 0)
    :: (mkPoint (-1) 0, mkPoint 0 1)
    :: nil.
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The diamond is a valid simple polygon; both points pass the guards.     *)
(* -------------------------------------------------------------------------- *)

Lemma diamond_ring_closed : ring_closed diamond.
Proof.
  exists (mkPoint 0 1), [ mkPoint 1 0; mkPoint 0 (-1); mkPoint (-1) 0 ].
  reflexivity.
Qed.

Lemma diamond_min_points : ring_has_minimum_points diamond.
Proof. unfold ring_has_minimum_points, diamond. simpl. lia. Qed.

(* No two distinct edges cross properly (the diamond is convex). *)
Lemma diamond_ring_simple : ring_simple diamond.
Proof.
  intros e1 e2 H1 H2 Hne Hcross.
  rewrite diamond_ring_edges in H1, H2.
  simpl in H1, H2.
  destruct Hcross as [t [s [[Ht0 Ht1] [[Hs0 Hs1] [Hx Hy]]]]].
  destruct H1 as [E1|[E1|[E1|[E1|[]]]]];
  destruct H2 as [E2|[E2|[E2|[E2|[]]]]];
    subst e1 e2; simpl in Hx, Hy, Hne;
    try (exfalso; apply Hne; reflexivity);
    nra.
Qed.

(* The diamond has NO horizontal edge, so `no_horizontal_edge_at` holds at every
   point -- including the pathological B.  This is the guard that fails to
   exclude the witness. *)
Lemma diamond_no_horizontal : forall p, no_horizontal_edge_at p diamond.
Proof.
  intro p. unfold no_horizontal_edge_at. rewrite diamond_ring_edges.
  repeat constructor; simpl; intro Heq; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Ray-parity: ODD at A, EVEN at B (the vertex graze).                     *)
(* -------------------------------------------------------------------------- *)

Ltac no_cross :=
  let H := fresh "H" in
  intro H; unfold edge_crosses_ray in H; simpl in H;
  destruct H as [ [[? ?] ?] | [[? ?] ?] ]; lra.

Ltac yes_cross :=
  unfold edge_crosses_ray; simpl; right; repeat split; lra.

(* Even-excludes-odd for the mutually-inductive ray parity (proved locally;
   the corpus has no exported lemma). *)
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

(* A = (0,1/2): the ray at height 1/2 crosses edge (0,1)->(1,0) once. *)
Lemma diamond_point_in_ring_A : point_in_ring A diamond.
Proof.
  unfold point_in_ring, A. rewrite diamond_ring_edges.
  apply rpo_cross; [ yes_cross | ].   (* (0,1)->(1,0)   crosses at x=1/2 *)
  apply rpe_skip;  [ no_cross | ].    (* (1,0)->(0,-1)  no straddle      *)
  apply rpe_skip;  [ no_cross | ].    (* (0,-1)->(-1,0) no straddle      *)
  apply rpe_skip;  [ no_cross | ].    (* (-1,0)->(0,1)  x-intercept left *)
  apply rpe_nil.
Qed.

(* B = (0,0): the ray at height 0 grazes vertex (1,0); the strict y-straddle
   counts NEITHER incident edge, and no other edge straddles 0 either -- so the
   parity is even and B is (wrongly) classified outside. *)
Lemma diamond_not_point_in_ring_B : ~ point_in_ring B diamond.
Proof.
  unfold point_in_ring, B. rewrite diamond_ring_edges.
  apply ray_parity_even_not_odd.
  apply rpe_skip; [ no_cross | ].   (* (0,1)->(1,0)   endpoint at y=0  *)
  apply rpe_skip; [ no_cross | ].   (* (1,0)->(0,-1)  endpoint at y=0  *)
  apply rpe_skip; [ no_cross | ].   (* (0,-1)->(-1,0) endpoint at y=0  *)
  apply rpe_skip; [ no_cross | ].   (* (-1,0)->(0,1)  endpoint at y=0  *)
  apply rpe_nil.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  A and B share a connected component of the complement.                  *)
(* -------------------------------------------------------------------------- *)

(* The vertical segment x = 0 from B = (0,0) up to A = (0,1/2) is a continuous
   path that never meets the ring (the ring meets x = 0 only at the apex
   vertices (0,1) and (0,-1), both outside [0,1/2]). *)
Lemma diamond_segment_off_ring : connected_in_complement_cont diamond B A.
Proof.
  unfold connected_in_complement_cont.
  exists (fun t => mkPoint ((1 - t) * 0 + t * 0) ((1 - t) * 0 + t * (1/2))).
  split; [ apply straight_path_continuous | ].
  split; [ unfold B; cbn; f_equal; lra | ].
  split; [ unfold A; cbn; f_equal; lra | ].
  intros t [Ht0 Ht1] Himg.
  unfold ring_image in Himg.
  destruct Himg as [e [u [Hin [[Hu0 Hu1] [Hx Hy]]]]].
  rewrite diamond_ring_edges in Hin. simpl in Hin.
  destruct Hin as [E|[E|[E|[E|[]]]]]; subst e; simpl in Hx, Hy; nra.
Qed.

(* `geometric_interior_cont` is a component invariant: off-ring is preserved at
   both endpoints, and boundedness is invariant (JCT.v). *)
Lemma geometric_interior_cont_invariant : forall r a b,
  connected_in_complement_cont r a b ->
  (geometric_interior_cont a r <-> geometric_interior_cont b r).
Proof.
  intros r a b Hab. unfold geometric_interior_cont. split.
  - intros [_ Hbnd]. split.
    + exact (connected_in_complement_cont_right r a b Hab).
    + exact (proj1 (in_bounded_component_cont_iff r a b Hab) Hbnd).
  - intros [_ Hbnd]. split.
    + exact (connected_in_complement_cont_left r a b Hab).
    + exact (proj2 (in_bounded_component_cont_iff r a b Hab) Hbnd).
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  RED: the seam cannot hold at both A and B.                              *)
(* -------------------------------------------------------------------------- *)

(* If `parity_characterises_interior_cont` held at both A and B (both satisfy
   all four guards), then:
     - A is parity-odd, so geometric_interior_cont A;
     - by component invariance (A ~ B), geometric_interior_cont B;
     - so by the seam at B, point_in_ring B -- contradicting the vertex graze.
   Hence at least one of these well-formed instances is FALSE: the seam is not
   universally true for a valid simple polygon under the four guards alone. *)
Theorem diamond_refutes_parity_seam :
  ~ (parity_characterises_interior_cont A diamond /\
     parity_characterises_interior_cont B diamond).
Proof.
  intros [HA HB].
  specialize (HA diamond_ring_simple diamond_ring_closed diamond_min_points
                 (diamond_no_horizontal A)).
  specialize (HB diamond_ring_simple diamond_ring_closed diamond_min_points
                 (diamond_no_horizontal B)).
  assert (HgA : geometric_interior_cont A diamond)
    by (apply HA; exact diamond_point_in_ring_A).
  assert (HgB : geometric_interior_cont B diamond)
    by (exact (proj2 (geometric_interior_cont_invariant diamond B A
                        diamond_segment_off_ring) HgA)).
  apply diamond_not_point_in_ring_B. exact (proj1 HB HgB).
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  GREEN: the generic-position guard excludes the witness.                 *)
(* -------------------------------------------------------------------------- *)

(* The missing premise: no ring vertex lies ON the closed rightward ray from p
   (same height, at or to the right).  This is the generic-position condition
   the crossing-number algorithm needs; `no_horizontal_edge_at` is the weaker,
   insufficient cousin. *)
Definition ray_avoids_vertices (p : Point) (r : Ring) : Prop :=
  forall v : Point, In v r -> ~ (py v = py p /\ px p <= px v).

(* B violates it: vertex (1,0) sits on B's rightward ray (same height 0, to the
   right).  This is exactly the graze that broke the parity count. *)
Lemma diamond_B_ray_hits_vertex : ~ ray_avoids_vertices B diamond.
Proof.
  unfold ray_avoids_vertices, B, diamond. intro H.
  apply (H (mkPoint 1 0)).
  - simpl. right. left. reflexivity.
  - simpl. split; lra.
Qed.

(* A satisfies it: no diamond vertex has height 1/2. *)
Lemma diamond_A_ray_avoids_vertices : ray_avoids_vertices A diamond.
Proof.
  unfold ray_avoids_vertices, A, diamond.
  intros v Hin [Hy _]. simpl in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; subst v; simpl in Hy; lra.
Qed.

(* `no_horizontal_edge_at` alone does NOT exclude the bad point B: it holds at B
   while the generic-position guard fails. *)
Lemma diamond_guard_insufficient :
  no_horizontal_edge_at B diamond /\ ~ ray_avoids_vertices B diamond.
Proof.
  split; [ apply diamond_no_horizontal | apply diamond_B_ray_hits_vertex ].
Qed.

(* The re-scoped seam: same body, additionally guarded by `ray_avoids_vertices`. *)
Definition parity_characterises_interior_cont_strict (p : Point) (r : Ring) : Prop :=
  ring_simple r -> ring_closed r -> ring_has_minimum_points r ->
  no_horizontal_edge_at p r ->
  ray_avoids_vertices p r ->
  (geometric_interior_cont p r <-> point_in_ring p r).

(* GREEN.  Under the re-scoped seam the witness B is excluded: the obligation is
   dischargeable because the added generic-position premise is unsatisfiable for
   B.  Contrast `diamond_refutes_parity_seam` (RED), where B against the
   un-strengthened seam was part of a contradiction.  Adding the vertex-
   avoidance guard -- and nothing else -- is the fix. *)
Theorem diamond_excluded_by_strict_parity_seam :
  parity_characterises_interior_cont_strict B diamond.
Proof.
  intros _ _ _ _ Hray. exfalso. apply diamond_B_ray_hits_vertex. exact Hray.
Qed.

(* RED and GREEN in one statement: the seam fails to hold at both A and B, but
   the generic-position-strengthened seam excludes the offending B; the single
   added premise `ray_avoids_vertices` is the whole difference. *)
Theorem strict_seam_resolves_the_diamond :
  (~ (parity_characterises_interior_cont A diamond /\
      parity_characterises_interior_cont B diamond))          (* RED   *)
  /\ parity_characterises_interior_cont_strict B diamond.     (* GREEN *)
Proof.
  split.
  - exact diamond_refutes_parity_seam.
  - exact diamond_excluded_by_strict_parity_seam.
Qed.
