(* ============================================================================
   NetTopologySuite.Proofs.JCT
   ----------------------------------------------------------------------------
   The continuous-component SPINE of the polygonal Jordan-Curve seam.

   `theories/JordanCurveSeam.v` (#81/#82) settled two things about the seam of
   `point_in_ring_correct`:

     - the corpus's interior predicate `geometric_interior_stdlib` is
       *identically false* (`geometric_interior_stdlib_vacuous`), because the
       complement-connectivity relation it rests on carries no continuity
       obligation; and
     - the corrected, continuity-carrying definitions
       (`connected_in_complement_cont`, `in_bounded_component_cont`,
       `geometric_interior_cont`, the genuine `JCT_two_components_cont` Prop)
       make the relation non-degenerate (`far_points_connected_cont`).

   This file builds the proof STRUCTURE on top of those corrected definitions.
   The headline finding sharpens the proposed structure in the issue:

       The lemma the sketch graded "the genuine topological content"
       (`no_path_from_interior_to_exterior`: an interior point cannot reach a
       non-interior point through the complement) is NOT thesis-scale.  Once
       "interior" is *defined* as "in a bounded complement component", that
       lemma is a one-line corollary of COMPONENT INVARIANCE -- which we prove
       here, fully Qed, for the continuous relation.

   What is therefore FREE (this file, all Qed, axiom-clean):

     §1  `connected_in_complement_cont` is an equivalence relation on the
         complement.  The only real work is `continuity_glue` (gluing two
         continuous functions that agree at a point) -- needed because the
         transitivity path concatenates two continuous paths at their join.
     §2  `in_bounded_component_cont` is a COMPONENT INVARIANT (constant on a
         connectivity class), exactly as in the discontinuous `BoundedComponent.v`.
     §3  `no_path_from_interior_to_exterior` and `interior_component_bounded`:
         the interior is trapped relative to the exterior -- for free.
     §4  The exterior is genuinely inhabited and connected, and every point far
         enough past the bounding box is NOT interior
         (`far_point_not_interior`) -- the honest, continuous analogue of the
         vacuity witness, now using a real straight-line path.

   What REMAINS the genuine seam (NOT proved; stated as a named Prop, §5):

       That ray-crossing parity CHARACTERISES the continuous geometric interior
       (`parity_characterises_interior_cont`).  Both directions are real
       topology -- "an odd-parity off-ring point is trapped" (no continuous
       escape to infinity) and "a bounded-component point has odd parity"
       (a winding/counting argument).  This is the load-bearing half of the
       polygonal JCT, identical in weight to `JCT_two_components_cont`.  §5
       wires it into a *non-vacuous* continuous headline
       `point_in_ring_correct_jct_cont`, the honest replacement for
       `point_in_ring_correct_jct` (which is Qed-closed only over the vacuous
       `geometric_interior_stdlib`).

   NOTE (relation to the corpus `JCT_two_components_cont` Prop).  As of #82 that
   Prop carries an explicit inter-component SEPARATION clause -- interior and
   exterior points are never complement-connected -- and
   `JordanCurveSeam.jct_cont_interior_is_geometric` uses it to place every
   interior point into `geometric_interior_cont`.  §3's
   `no_path_from_interior_to_exterior` is the gap-free Qed COUNTERPART for the
   `geometric_interior_cont` definition itself: there separation is not assumed
   but PROVED, because boundedness is baked into the interior predicate and the
   rest is component invariance (§2).  The two agree; neither proves the JCT.

   Pure-R; no atan / Flocq.  No `Admitted` / `Axiom` / `Parameter`.  The
   axiom footprint is the corpus-standard classical-reals pair plus
   `functional_extensionality` (already in the corpus footprint).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import List.
From Stdlib Require Import Ranalysis.
From Stdlib Require Import FunctionalExtensionality.

From NTS.Proofs Require Import Distance.
From NTS.Proofs Require Import Overlay.
From NTS.Proofs Require Import PointInRingCorrect.
From NTS.Proofs Require Import PointInRingTangents.
From NTS.Proofs Require Import JordanCurveSeam.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §0  Gluing continuity.                                                      *)
(*                                                                            *)
(* Two functions continuous on all of R, agreeing at a, glue into a function *)
(* continuous on all of R.  This is the one genuine analysis obligation the   *)
(* continuous relation adds over the discontinuous `BoundedComponent.v`: the  *)
(* transitivity path concatenates two continuous paths at their meeting point.*)
(* -------------------------------------------------------------------------- *)

Lemma continuity_glue :
  forall (f g : R -> R) (a : R),
    continuity f -> continuity g -> f a = g a ->
    continuity (fun x => if Rle_dec x a then f x else g x).
Proof.
  intros f g a Hf Hg Hfa x0.
  unfold continuity_pt, continue_in, limit1_in, limit_in.
  intros eps Heps.
  destruct (Rtotal_order x0 a) as [Hlt | [Heq | Hgt]].
  - (* x0 < a : the glued function agrees with f on a neighbourhood of x0. *)
    specialize (Hf x0).
    unfold continuity_pt, continue_in, limit1_in, limit_in in Hf.
    destruct (Hf eps Heps) as [alp [Halp Hclose]].
    exists (Rmin alp (a - x0)). split.
    + apply Rmin_glb_lt; lra.
    + intros x [[_ Hne] Hd].
      assert (Hda : Rlimit.dist R_met x x0 < alp)
        by (eapply Rlt_le_trans; [exact Hd | apply Rmin_l]).
      assert (Hdb : Rlimit.dist R_met x x0 < a - x0)
        by (eapply Rlt_le_trans; [exact Hd | apply Rmin_r]).
      assert (Hxa : x < a).
      { assert (HH : Rabs (x - x0) < a - x0) by exact Hdb.
        apply Rabs_def2 in HH. lra. }
      destruct (Rle_dec x a) as [_ | Hc]; [| lra].
      destruct (Rle_dec x0 a) as [_ | Hc]; [| lra].
      apply Hclose. split; [split; [exact I | exact Hne] | exact Hda].
  - (* x0 = a : both branches matter; they meet because f a = g a. *)
    subst x0.
    specialize (Hf a); specialize (Hg a).
    unfold continuity_pt, continue_in, limit1_in, limit_in in Hf, Hg.
    destruct (Hf eps Heps) as [alpf [Halpf Hcf]].
    destruct (Hg eps Heps) as [alpg [Halpg Hcg]].
    exists (Rmin alpf alpg). split.
    + apply Rmin_glb_lt; lra.
    + intros x [[_ Hne] Hd].
      assert (Hdf : Rlimit.dist R_met x a < alpf)
        by (eapply Rlt_le_trans; [exact Hd | apply Rmin_l]).
      assert (Hdg : Rlimit.dist R_met x a < alpg)
        by (eapply Rlt_le_trans; [exact Hd | apply Rmin_r]).
      destruct (Rle_dec a a) as [_ | Hc]; [| lra].
      destruct (Rle_dec x a) as [_ | _].
      * apply Hcf. split; [split; [exact I | exact Hne] | exact Hdf].
      * rewrite Hfa. apply Hcg. split; [split; [exact I | exact Hne] | exact Hdg].
  - (* x0 > a : the glued function agrees with g on a neighbourhood of x0. *)
    specialize (Hg x0).
    unfold continuity_pt, continue_in, limit1_in, limit_in in Hg.
    destruct (Hg eps Heps) as [alp [Halp Hclose]].
    exists (Rmin alp (x0 - a)). split.
    + apply Rmin_glb_lt; lra.
    + intros x [[_ Hne] Hd].
      assert (Hda : Rlimit.dist R_met x x0 < alp)
        by (eapply Rlt_le_trans; [exact Hd | apply Rmin_l]).
      assert (Hdb : Rlimit.dist R_met x x0 < x0 - a)
        by (eapply Rlt_le_trans; [exact Hd | apply Rmin_r]).
      assert (Hxa : x > a).
      { assert (HH : Rabs (x - x0) < x0 - a) by exact Hdb.
        apply Rabs_def2 in HH. lra. }
      destruct (Rle_dec x a) as [Hc | _]; [lra |].
      destruct (Rle_dec x0 a) as [Hc | _]; [lra |].
      apply Hclose. split; [split; [exact I | exact Hne] | exact Hda].
Qed.

(* -------------------------------------------------------------------------- *)
(* §1  connected_in_complement_cont is an equivalence relation.               *)
(*                                                                            *)
(* Mirrors BoundedComponent.v's equivalence proofs for the discontinuous      *)
(* relation -- but each path-builder now carries a continuity obligation:     *)
(* the constant path (refl), the time-reversal t |-> 1 - t (sym), and the     *)
(* midpoint concatenation (trans, via continuity_glue).                       *)
(* -------------------------------------------------------------------------- *)

(* Reflexive on complement points (constant path). *)
Lemma connected_in_complement_cont_refl : forall r p,
  ring_complement r p -> connected_in_complement_cont r p p.
Proof.
  intros r p Hp. exists (fun _ => p).
  split; [| split; [reflexivity | split; [reflexivity |]]].
  - split; apply continuity_const; intros x y; reflexivity.
  - intros t _. exact Hp.
Qed.

(* Time-reversal preserves continuity: h o (1 - .) is continuous. *)
Lemma continuity_reverse : forall h : R -> R,
  continuity h -> continuity (fun t => h (1 - t)).
Proof.
  intros h Hh.
  replace (fun t => h (1 - t)) with (comp h (fun t => 1 - t)) by reflexivity.
  apply continuity_comp; [ reg | exact Hh ].
Qed.

(* Symmetric (reverse the parametrisation t |-> 1 - t). *)
Lemma connected_in_complement_cont_sym : forall r p q,
  connected_in_complement_cont r p q -> connected_in_complement_cont r q p.
Proof.
  intros r p q [path [[Hcx Hcy] [H0 [H1 Hc]]]].
  exists (fun t => path (1 - t)).
  split; [| split; [| split]].
  - split.
    + apply (continuity_reverse (fun t => px (path t))); exact Hcx.
    + apply (continuity_reverse (fun t => py (path t))); exact Hcy.
  - replace (1 - 0) with 1 by lra. exact H1.
  - replace (1 - 1) with 0 by lra. exact H0.
  - intros t Ht. apply Hc. lra.
Qed.

(* Transitive (concatenate at the midpoint, glued by continuity_glue). *)
Lemma connected_in_complement_cont_trans : forall r p q s,
  connected_in_complement_cont r p q ->
  connected_in_complement_cont r q s ->
  connected_in_complement_cont r p s.
Proof.
  intros r p q s [p1 [[H1cx H1cy] [H10 [H11 Hc1]]]]
                 [p2 [[H2cx H2cy] [H20 [H21 Hc2]]]].
  (* The two half-paths concatenate; continuity holds for any coordinate
     projection because they meet at q (p1 1 = q = p2 0). *)
  assert (Hcat : forall proj : Point -> R,
    continuity (fun t => proj (p1 t)) ->
    continuity (fun t => proj (p2 t)) ->
    continuity (fun t => proj (if Rle_dec t (1/2) then p1 (2*t) else p2 (2*t-1)))).
  { intros proj Hpj1 Hpj2.
    replace (fun t => proj (if Rle_dec t (1/2) then p1 (2*t) else p2 (2*t-1)))
       with (fun t => if Rle_dec t (1/2) then proj (p1 (2*t)) else proj (p2 (2*t-1))).
    2:{ apply functional_extensionality. intro t.
        destruct (Rle_dec t (1/2)); reflexivity. }
    apply continuity_glue.
    - replace (fun t => proj (p1 (2*t)))
         with (comp (fun u => proj (p1 u)) (fun t => 2*t)) by reflexivity.
      apply continuity_comp; [ reg | exact Hpj1 ].
    - replace (fun t => proj (p2 (2*t-1)))
         with (comp (fun u => proj (p2 u)) (fun t => 2*t-1)) by reflexivity.
      apply continuity_comp; [ reg | exact Hpj2 ].
    - cbn beta.
      replace (2 * (1/2) - 1) with 0 by lra.
      replace (2 * (1/2)) with 1 by lra.
      rewrite H11, H20. reflexivity. }
  exists (fun t => if Rle_dec t (1/2) then p1 (2*t) else p2 (2*t-1)).
  split; [| split; [| split]].
  - split; [ apply (Hcat px H1cx H2cx) | apply (Hcat py H1cy H2cy) ].
  - destruct (Rle_dec 0 (1/2)) as [_ | Hn]; [| lra].
    replace (2 * 0) with 0 by lra. exact H10.
  - destruct (Rle_dec 1 (1/2)) as [Hle | _]; [lra |].
    replace (2 * 1 - 1) with 1 by lra. exact H21.
  - intros t Ht. destruct (Rle_dec t (1/2)) as [Hle | Hgt].
    + apply Hc1. lra.
    + apply Hc2. lra.
Qed.

(* The left endpoint of any complement path is in the complement. *)
Lemma connected_in_complement_cont_left : forall r p q,
  connected_in_complement_cont r p q -> ring_complement r p.
Proof.
  intros r p q [path [_ [H0 [_ Hc]]]]. rewrite <- H0. apply Hc. lra.
Qed.

(* ...and so is the right endpoint (by symmetry). *)
Lemma connected_in_complement_cont_right : forall r p q,
  connected_in_complement_cont r p q -> ring_complement r q.
Proof.
  intros r p q H. apply connected_in_complement_cont_left with (q := p).
  apply connected_in_complement_cont_sym. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  in_bounded_component_cont is a component invariant.                     *)
(*                                                                            *)
(* The continuous analogue of BoundedComponent.v §2: boundedness is constant  *)
(* on a connectivity class (same radius works, by transitivity).              *)
(* -------------------------------------------------------------------------- *)

Lemma in_bounded_component_cont_invariant : forall r p q,
  connected_in_complement_cont r p q ->
  in_bounded_component_cont r p ->
  in_bounded_component_cont r q.
Proof.
  intros r p q Hpq [M [HM Hbound]].
  exists M. split; [exact HM |].
  intros s Hqs. apply Hbound.
  apply (connected_in_complement_cont_trans r p q s Hpq Hqs).
Qed.

Theorem in_bounded_component_cont_iff : forall r p q,
  connected_in_complement_cont r p q ->
  (in_bounded_component_cont r p <-> in_bounded_component_cont r q).
Proof.
  intros r p q Hpq. split.
  - apply in_bounded_component_cont_invariant; exact Hpq.
  - apply in_bounded_component_cont_invariant.
    apply connected_in_complement_cont_sym; exact Hpq.
Qed.

(* Refutation tool: unbounded reachability rules out a bounded component. *)
Theorem not_in_bounded_component_cont_intro : forall r p,
  (forall M, M > 0 ->
     exists q, connected_in_complement_cont r p q /\
               px q * px q + py q * py q > M * M) ->
  ~ in_bounded_component_cont r p.
Proof.
  intros r p Hunb [M [HM Hbound]].
  destruct (Hunb M HM) as [q [Hpq Hbig]].
  specialize (Hbound q Hpq). lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The interior is trapped relative to the exterior -- for FREE.          *)
(*                                                                            *)
(* This is the lemma the issue sketch graded thesis-scale (the genuine        *)
(* topological content).  With interior DEFINED as in-a-bounded-component      *)
(* (`geometric_interior_cont`), it is a direct                                 *)
(* corollary of component invariance (§2): a continuous complement path from  *)
(* an interior point to q forces q into the same (bounded) component, hence q  *)
(* is itself interior.  No new geometry, no JCT.                              *)
(* -------------------------------------------------------------------------- *)

Theorem no_path_from_interior_to_exterior : forall r p q,
  geometric_interior_cont p r ->
  ~ geometric_interior_cont q r ->
  ~ connected_in_complement_cont r p q.
Proof.
  intros r p q [Hcp Hbp] Hnq Hpath.
  apply Hnq. split.
  - apply connected_in_complement_cont_right with (p := p). exact Hpath.
  - apply (in_bounded_component_cont_invariant r p q Hpath Hbp).
Qed.

(* The interior component is bounded (immediate from the definition: this is
   the honest content of "interior_component_bounded" in the sketch). *)
Lemma interior_component_bounded : forall r p,
  geometric_interior_cont p r ->
  exists M, M > 0 /\
    forall q, connected_in_complement_cont r p q ->
              px q * px q + py q * py q <= M * M.
Proof. intros r p [_ Hb]. exact Hb. Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The exterior is genuinely inhabited and connected.                     *)
(*                                                                            *)
(* The honest, continuous analogue of `geometric_interior_stdlib_vacuous`:    *)
(* a point far enough past the ring's bounding box is NOT interior, because   *)
(* a genuine straight-line (continuous) ray to the right escapes any radius.  *)
(* Unlike the vacuity theorem, this does NOT claim the interior is empty --   *)
(* only that far-right points are exterior.                                   *)
(* -------------------------------------------------------------------------- *)

Lemma far_point_not_interior : forall (r : Ring) (x0 : R),
  x0 > edges_maxX (ring_edges r) ->
  ~ geometric_interior_cont (mkPoint x0 0) r.
Proof.
  intros r x0 Hx0 [_ [M [HM Hbnd]]].
  set (B := edges_maxX (ring_edges r)).
  set (X := Rmax (B + 1) (M + 1)).
  assert (HXB : X > B)
    by (apply Rlt_le_trans with (B + 1); [lra | apply Rmax_l]).
  assert (HXM : X > M)
    by (apply Rlt_le_trans with (M + 1); [lra | apply Rmax_r]).
  assert (Hcon : connected_in_complement_cont r (mkPoint x0 0) (mkPoint X 0)).
  { apply far_points_connected_cont; [exact Hx0 | exact HXB]. }
  specialize (Hbnd (mkPoint X 0) Hcon). simpl in Hbnd. nra.
Qed.

(* Two far-right points are both exterior and joined by a continuous complement
   path: the exterior component is non-degenerate where the old relation was
   vacuous. *)
Corollary exterior_inhabited_and_connected : forall (r : Ring) (x0 x1 : R),
  x0 > edges_maxX (ring_edges r) ->
  x1 > edges_maxX (ring_edges r) ->
  ~ geometric_interior_cont (mkPoint x0 0) r /\
  ~ geometric_interior_cont (mkPoint x1 0) r /\
  connected_in_complement_cont r (mkPoint x0 0) (mkPoint x1 0).
Proof.
  intros r x0 x1 H0 H1. repeat split.
  - apply far_point_not_interior; exact H0.
  - apply far_point_not_interior; exact H1.
  - apply far_points_connected_cont; [exact H0 | exact H1].
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  The genuine remaining seam, isolated -- and a NON-VACUOUS headline.     *)
(*                                                                            *)
(* Everything above is free.  The load-bearing topological fact that is NOT   *)
(* free is that ray-crossing parity characterises the (continuous) geometric  *)
(* interior.  We state it as a named Prop -- never axiomatised, never         *)
(* Admitted -- exactly as `JCT_two_components_cont` is stated in              *)
(* JordanCurveSeam.v.  It bundles the two thesis-scale directions:            *)
(*                                                                            *)
(*   (->)  a bounded-component (interior) point has odd ray-parity            *)
(*         (a winding / counting argument);                                   *)
(*   (<-)  an odd-parity off-ring point is TRAPPED in a bounded component     *)
(*         (no continuous escape to infinity -- the load-bearing half of the  *)
(*         polygonal JCT, the same gap `far_point_not_interior` only settles  *)
(*         for the far-field).                                                 *)
(* -------------------------------------------------------------------------- *)

(* `point_in_ring p r` (Overlay.v) is exactly `ray_parity_odd p (ring_edges r)`
   -- the horizontal-ray crossing-parity test.  It is the SAME ray-parity
   primitive the buffer depth-labelling uses to decide enclosure
   (`BufferDepth.v`, `ray_parity_odd p (edges_of (kept_edges G))`); so this seam
   is precisely "ray-casting decides interior", shared across point-in-ring and
   depth labelling. *)
Definition parity_characterises_interior_cont (p : Point) (r : Ring) : Prop :=
  ring_simple r -> ring_closed r -> ring_has_minimum_points r ->
  no_horizontal_edge_at p r ->
  (geometric_interior_cont p r <-> point_in_ring p r).

(* SCOPE CAVEAT (see theories/JCT_VertexGrazingCounterexample.v +
   docs/jct-vertex-grazing-counterexample.md).  The four guards above are NOT
   sufficient: `no_horizontal_edge_at` does not stop the rightward ray from
   GRAZING a vertex.  For the convex diamond, the centre B = (0,0) passes all
   four guards yet ray-parity counts neither edge meeting the grazed vertex
   (1,0) -- so `point_in_ring` disagrees with the (component-invariant)
   `geometric_interior_cont` there (`diamond_refutes_parity_seam`).  The fix is
   the generic-position guard `ray_avoids_vertices p r` (no ring vertex lies on
   the rightward ray), giving `parity_characterises_interior_cont_strict`
   (ibid.).  Any eventual discharge of this seam should carry that guard. *)

(* CONCRETE INSTANCE (theories/RectangleJCT.v).  This seam is discharged for
   AXIS-ALIGNED RECTANGLES as far as analysis allows: `point_in_ring_rect_iff`
   proves the ray-parity equivalence directly by finite evaluation over the four
   edges, and -- because a strict-interior height satisfies y0<py<y1, coinciding
   with no vertex (all vertices sit at y0 or y1) -- the grazing caveat above does
   NOT bite there.  The separation is then proved UNCONDITIONALLY for strict-
   interior points (`RectangleSeparation.v : rect_parity_characterises_interior`)
   via a 1-D IVT on a scalar box field, so the rectangle is a fully Qed-closed
   instance of this seam -- no residual hypothesis. *)

(* SECOND CONCRETE INSTANCE (theories/RightTriangleJCT.v +
   RightTriangleSeparation.v).  The same recipe -- ray-parity computation +
   a min-of-inward-signed-distances field + the IVT separation engine
   (SeparationField.separation_via_field) -- discharges the seam for the
   axis-aligned RIGHT TRIANGLE, the first family with a SLOPED edge (the
   hypotenuse, handled affinely via `s_hyp`).  `right_triangle_parity_
   characterises_interior` is again fully Qed-closed for strict-interior points,
   showing the technique is not tied to axis-aligned edges. *)

(* The re-scoped seam, carrying BOTH generic-position guards: it adds
   `ray_avoids_vertices p r` (PointInRingCorrect.v) to the four premises of
   `parity_characterises_interior_cont`.  Together `no_horizontal_edge_at`
   (necessary: JCT_HorizontalEdgeCounterexample.v) and `ray_avoids_vertices`
   (additionally required: JCT_VertexGrazingCounterexample.v) form the minimal
   generic-position guard set under which ray-parity can characterise the
   continuous interior.  The headline below is stated against THIS strengthened
   seam; the un-strengthened `parity_characterises_interior_cont` is kept only
   as the (counterexample-refuted) naive form.  Still a thesis-scale `Prop`:
   not proved, not axiomatised. *)
Definition parity_characterises_interior_cont_strict (p : Point) (r : Ring) : Prop :=
  ring_simple r -> ring_closed r -> ring_has_minimum_points r ->
  no_horizontal_edge_at p r ->
  ray_avoids_vertices p r ->
  (geometric_interior_cont p r <-> point_in_ring p r).

(* The non-vacuous continuous replacement for `point_in_ring_correct_jct`.
   Unlike that headline -- Qed-closed only over the identically-false
   `geometric_interior_stdlib` -- this one concludes over
   `geometric_interior_cont`, which §4 shows is genuinely inhabitable, under a
   single named seam Prop.  Trivial composition; the value is that the seam is
   now stated over a non-degenerate interior predicate AND carries the
   generic-position guards (`no_horizontal_edge_at`, `ray_avoids_vertices`) that
   the degenerate-case counterexamples show are necessary. *)
Theorem point_in_ring_correct_jct_cont :
  forall (p : Point) (r : Ring),
    ring_simple r ->
    ring_closed r ->
    ring_has_minimum_points r ->
    no_horizontal_edge_at p r ->
    ray_avoids_vertices p r ->
    parity_characterises_interior_cont_strict p r ->
    point_in_ring p r <-> geometric_interior_cont p r.
Proof.
  intros p r Hs Hc Hm Hnh Hrav Hjct.
  split; intro H; apply (Hjct Hs Hc Hm Hnh Hrav); exact H.
Qed.
