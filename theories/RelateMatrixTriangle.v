(* ============================================================================
   NetTopologySuite.Proofs.RelateMatrixTriangle
   ----------------------------------------------------------------------------
   Triangle analogue of RelateMatrixRect.v (S7 style).

   Defines TrianglePairRegime + triangle_pair_fill (regime → witness matrix)
   and classify_triangle_pair.

   Witnesses reuse the aa_* shapes from RelateAreaArea.v for now
   (touch has same BB=1 / EE=2 shape).

   The five classifier predicates are real geometry (#522 / #567): stated
   against the SPECIFIED interior of ADR-0003 -- strict `0 < gtri` for
   interior facts, closed `0 <= gtri` for closure facts.  The four
   gtri-shaped predicates get pairwise exclusivity and per-regime witnesses
   at the end of the file (`TPR_TouchEdge` keeps its frozen shared-edge
   vocabulary and is deliberately outside that exclusivity block).
   Ray parity never appears here; it enters only via the sanctioned
   ADR-0003 bridge (RelateNGTouchCells).  The five names are not a
   partition of all triangle pairs:    a partial-edge kiss that is neither
   a full shared edge nor a single shared vertex used to satisfy none of
   them.     Leftover `Ⅰ` adds `TPR_TouchPartialEdge` (fill stays
   `im_unsupported` until a fill is named). Leftover `Ⅲ` adds
   `TPR_TouchOnesided` (same fill honesty). Leftover `Ⅱ` adds
   `TPR_TouchObtuse` (same fill honesty). Leftover `Ⅴ` adds
   `TPR_MixedCone` (same fill honesty). Leftover `Ⅵ` adds
   `TPR_SameCone` (same fill honesty). Completeness is an unnamed
   lens pair (not leftover `Ⅶ`).

   Honest scoping: triangles only (convex, no holes). Full pointset
   satisfaction and noding bridge in RelateNG.

   WITNESS topic: relate · claimId: 522-a · witness: 522-a-regime-exclusive
   macro: relate
   lane: proofs
   issue: #567 / #522
   ADR-0004: not a remint.  522-a is the existing #567 ticket id.

   No `Admitted`, no `Axiom`, no `Parameter`.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import DE9IM Distance RelateAreaArea Orientation Real.
From NTS.Proofs Require Import GeneralTriangleSeparation.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Regime enum + matrix fill (parallel to RectPairRegime).                   *)
(* -------------------------------------------------------------------------- *)

Inductive TrianglePairRegime : Type :=
| TPR_Disjoint
| TPR_Overlap
| TPR_Contains
| TPR_TouchEdge
| TPR_TouchVertex   (* vertex contact; matrix shape can be adjusted later *)
| TPR_TouchPartialEdge (* leftover Ⅰ: mutual vertex-in-open-edge; fill is the token *)
| TPR_TouchOnesided (* leftover Ⅲ∨Ⅳ: one-sided vertex-in-open-edge; fill is the token *)
| TPR_TouchObtuse   (* leftover Ⅱ: closed-cone vertex kiss; fill is the token *)
| TPR_MixedCone     (* leftover Ⅴ: opposite-sign cone at a shared vertex; fill is the token *)
| TPR_SameCone      (* leftover Ⅵ: same-sign cone spill at a shared vertex; fill is the token *)
| TPR_Unsupported.  (* the classifier declined -- NOT a geometric verdict *)

Definition triangle_pair_fill (r : TrianglePairRegime) : IntersectionMatrix :=
  match r with
  | TPR_Disjoint    => aa_matrix_disjoint
  | TPR_Overlap     => aa_matrix_partial_overlap
  | TPR_Contains    => aa_matrix_contains
  | TPR_TouchEdge   => aa_matrix_touch_vertical  (* BB=1, EE=2 *)
  | TPR_TouchVertex => aa_matrix_touch_vertical  (* same for starter; point contact may be dim 0 *)
  | TPR_TouchPartialEdge => im_unsupported       (* leftover Ⅰ: classified, fill not named *)
  | TPR_TouchOnesided => im_unsupported          (* leftover Ⅲ∨Ⅳ: classified, fill not named *)
  | TPR_TouchObtuse => im_unsupported            (* leftover Ⅱ: classified, fill not named *)
  | TPR_MixedCone => im_unsupported              (* leftover Ⅴ: classified, fill not named *)
  | TPR_SameCone => im_unsupported               (* leftover Ⅵ: classified, fill not named *)
  | TPR_Unsupported => im_unsupported            (* decline; see DE9IM.im_unsupported *)
  end.

Lemma triangle_pair_fill_disjoint_eq :
  triangle_pair_fill TPR_Disjoint = aa_matrix_disjoint.
Proof. reflexivity. Qed.

Lemma triangle_pair_fill_overlap_eq :
  triangle_pair_fill TPR_Overlap = aa_matrix_partial_overlap.
Proof. reflexivity. Qed.

Lemma triangle_pair_fill_contains_eq :
  triangle_pair_fill TPR_Contains = aa_matrix_contains.
Proof. reflexivity. Qed.

Lemma triangle_pair_fill_touch_edge_eq :
  triangle_pair_fill TPR_TouchEdge = aa_matrix_touch_vertical.
Proof. reflexivity. Qed.

Lemma triangle_pair_fill_touch_vertex_eq :
  triangle_pair_fill TPR_TouchVertex = aa_matrix_touch_vertical.
Proof. reflexivity. Qed.

Lemma triangle_pair_fill_touch_partial_eq :
  triangle_pair_fill TPR_TouchPartialEdge = im_unsupported.
Proof. reflexivity. Qed.

Lemma triangle_pair_fill_touch_onesided_eq :
  triangle_pair_fill TPR_TouchOnesided = im_unsupported.
Proof. reflexivity. Qed.

Lemma triangle_pair_fill_touch_obtuse_eq :
  triangle_pair_fill TPR_TouchObtuse = im_unsupported.
Proof. reflexivity. Qed.

Lemma triangle_pair_fill_touch_mixed_eq :
  triangle_pair_fill TPR_MixedCone = im_unsupported.
Proof. reflexivity. Qed.

Lemma triangle_pair_fill_touch_samecone_eq :
  triangle_pair_fill TPR_SameCone = im_unsupported.
Proof. reflexivity. Qed.

Lemma triangle_pair_fill_unsupported_eq :
  triangle_pair_fill TPR_Unsupported = im_unsupported.
Proof. reflexivity. Qed.

(* The point of the new regime: declining is not the same answer as
   "disjoint".  A classifier that cannot place a pair must not fill the
   disjointness matrix for it. *)
Lemma triangle_pair_fill_unsupported_not_disjoint :
  ~ im_disjoint (triangle_pair_fill TPR_Unsupported).
Proof.
  rewrite triangle_pair_fill_unsupported_eq. exact im_unsupported_not_disjoint.
Qed.

(* -------------------------------------------------------------------------- *)
(* Point-in-triangle vocabulary (ADR-0003 signs over `gtri`).                 *)
(*                                                                            *)
(* `gtri` (GeneralTriangleSeparation) is the min of the three inward edge     *)
(* slacks: > 0 strictly inside, = 0 exactly on the edge skeleton, < 0         *)
(* outside -- MEANINGFUL FOR CCW INPUT (0 < gdbl), hence the explicit CCW     *)
(* guards on the closure-shaped predicates below.  Names are `in_tri_*` to    *)
(* stay clear of the coordinate-style `tri_interior` in RelateNGTouchCells.   *)
(* -------------------------------------------------------------------------- *)

Definition tri_ccw (a1 a2 a3 : Point) : Prop :=
  0 < gdbl (px a1) (py a1) (px a2) (py a2) (px a3) (py a3).

Definition in_tri_interior (a1 a2 a3 pt : Point) : Prop :=
  0 < gtri (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) pt.

Definition in_tri_closure (a1 a2 a3 pt : Point) : Prop :=
  0 <= gtri (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) pt.

Definition in_tri_exterior (a1 a2 a3 pt : Point) : Prop :=
  gtri (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) pt < 0.

Definition is_vertex_of (v a1 a2 a3 : Point) : Prop :=
  v = a1 \/ v = a2 \/ v = a3.

Lemma in_tri_interior_closure : forall a1 a2 a3 pt,
  in_tri_interior a1 a2 a3 pt -> in_tri_closure a1 a2 a3 pt.
Proof. unfold in_tri_interior, in_tri_closure; intros; lra. Qed.

Lemma in_tri_exterior_not_closure : forall a1 a2 a3 pt,
  in_tri_exterior a1 a2 a3 pt -> ~ in_tri_closure a1 a2 a3 pt.
Proof. unfold in_tri_exterior, in_tri_closure; intros; lra. Qed.

(* Closed analogue of GeneralTriangleSeparation.Rmin_pos_iff / gtri_pos_iff. *)
Lemma Rmin_nonneg_iff : forall a b, 0 <= Rmin a b <-> 0 <= a /\ 0 <= b.
Proof.
  intros a b; split.
  - intros H; split.
    + exact (Rle_trans _ _ _ H (Rmin_l_le a b)).
    + exact (Rle_trans _ _ _ H (Rmin_r_le a b)).
  - intros [Ha Hb]; apply Rmin_glb; assumption.
Qed.

Lemma gtri_nonneg_iff : forall ax ay bx by_ cx cy pt,
  0 <= gtri ax ay bx by_ cx cy pt <->
  (0 <= gsA ax ay bx by_ pt /\ 0 <= gsB bx by_ cx cy pt /\ 0 <= gsC ax ay cx cy pt).
Proof. intros; unfold gtri; rewrite !Rmin_nonneg_iff; tauto. Qed.

(* `gtri` is bounded by each individual edge slack (min of the three). *)
Lemma gtri_le_gsA : forall ax ay bx by_ cx cy pt,
  gtri ax ay bx by_ cx cy pt <= gsA ax ay bx by_ pt.
Proof.
  intros; unfold gtri.
  exact (Rle_trans _ _ _ (Rmin_l_le _ _) (Rmin_l_le _ _)).
Qed.

Lemma gtri_le_gsB : forall ax ay bx by_ cx cy pt,
  gtri ax ay bx by_ cx cy pt <= gsB bx by_ cx cy pt.
Proof.
  intros; unfold gtri.
  exact (Rle_trans _ _ _ (Rmin_l_le _ _) (Rmin_r_le _ _)).
Qed.

Lemma gtri_le_gsC : forall ax ay bx by_ cx cy pt,
  gtri ax ay bx by_ cx cy pt <= gsC ax ay cx cy pt.
Proof. intros; unfold gtri; exact (Rmin_r_le _ _). Qed.

(* An interior point forces CCW: the three positive slacks sum to gdbl. *)
Lemma in_tri_interior_ccw : forall a1 a2 a3 pt,
  in_tri_interior a1 a2 a3 pt -> tri_ccw a1 a2 a3.
Proof.
  intros a1 a2 a3 pt H. unfold in_tri_interior in H. unfold tri_ccw.
  apply gtri_pos_iff in H. destruct H as [HA [HB HC]].
  pose proof (g_sum (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) pt). lra.
Qed.

(* Each edge slack vanishes at its own two endpoints, so no vertex is a
   specified-interior point of its own triangle. *)
Lemma vertex_not_in_tri_interior : forall a1 a2 a3 v,
  is_vertex_of v a1 a2 a3 -> ~ in_tri_interior a1 a2 a3 v.
Proof.
  intros a1 a2 a3 v Hv H. unfold in_tri_interior in H.
  apply gtri_pos_iff in H. destruct H as [HA [HB HC]].
  destruct Hv as [-> | [-> | ->]].
  - assert (E : gsA (px a1) (py a1) (px a2) (py a2) a1 = 0) by (unfold gsA; ring).
    lra.
  - assert (E : gsA (px a1) (py a1) (px a2) (py a2) a2 = 0) by (unfold gsA; ring).
    lra.
  - assert (E : gsB (px a2) (py a2) (px a3) (py a3) a3 = 0) by (unfold gsB; ring).
    lra.
Qed.

(* Under the CCW guard every vertex lies in its own triangle's closure: two
   edge slacks vanish there and the third equals gdbl. *)
Lemma vertex_in_tri_closure : forall a1 a2 a3 v,
  tri_ccw a1 a2 a3 -> is_vertex_of v a1 a2 a3 -> in_tri_closure a1 a2 a3 v.
Proof.
  intros a1 a2 a3 v Hccw Hv. unfold tri_ccw in Hccw. unfold in_tri_closure.
  apply gtri_nonneg_iff.
  destruct Hv as [-> | [-> | ->]].
  - assert (EA : gsA (px a1) (py a1) (px a2) (py a2) a1 = 0) by (unfold gsA; ring).
    assert (EB : gsB (px a2) (py a2) (px a3) (py a3) a1
                 = gdbl (px a1) (py a1) (px a2) (py a2) (px a3) (py a3))
      by (unfold gsB, gdbl; ring).
    assert (EC : gsC (px a1) (py a1) (px a3) (py a3) a1 = 0) by (unfold gsC; ring).
    lra.
  - assert (EA : gsA (px a1) (py a1) (px a2) (py a2) a2 = 0) by (unfold gsA; ring).
    assert (EB : gsB (px a2) (py a2) (px a3) (py a3) a2 = 0) by (unfold gsB; ring).
    assert (EC : gsC (px a1) (py a1) (px a3) (py a3) a2
                 = gdbl (px a1) (py a1) (px a2) (py a2) (px a3) (py a3))
      by (unfold gsC, gdbl; ring).
    lra.
  - assert (EA : gsA (px a1) (py a1) (px a2) (py a2) a3
                 = gdbl (px a1) (py a1) (px a2) (py a2) (px a3) (py a3))
      by (unfold gsA, gdbl; ring).
    assert (EB : gsB (px a2) (py a2) (px a3) (py a3) a3 = 0) by (unfold gsB; ring).
    assert (EC : gsC (px a1) (py a1) (px a3) (py a3) a3 = 0) by (unfold gsC; ring).
    lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Classifier (geometry predicates).                                          *)
(* -------------------------------------------------------------------------- *)

(* Shared-edge touch vocabulary (frozen: do not disturb -- RelateNGTouch's
   anchors are stated over these). *)
Definition shares_edge (p1 p2 q1 q2 : Point) : Prop :=
  (p1 = q1 /\ p2 = q2) \/ (p1 = q2 /\ p2 = q1).

Definition opposite_sides (p1 p2 p q : Point) : Prop :=
  let s1 := cross p1 p2 p in
  let s2 := cross p1 p2 q in
  s1 * s2 < 0.

Definition triangles_touch_on_shared_edge (a1 a2 a3 b1 b2 b3 : Point) : Prop :=
  (shares_edge a1 a2 b1 b2 /\ opposite_sides a1 a2 a3 b3) \/
  (shares_edge a1 a2 b2 b3 /\ opposite_sides a1 a2 a3 b1) \/
  (shares_edge a1 a2 b3 b1 /\ opposite_sides a1 a2 a3 b2) \/
  (shares_edge a2 a3 b1 b2 /\ opposite_sides a2 a3 a1 b3) \/
  (shares_edge a2 a3 b2 b3 /\ opposite_sides a2 a3 a1 b1) \/
  (shares_edge a2 a3 b3 b1 /\ opposite_sides a2 a3 a1 b2) \/
  (shares_edge a3 a1 b1 b2 /\ opposite_sides a3 a1 a2 b3) \/
  (shares_edge a3 a1 b2 b3 /\ opposite_sides a3 a1 a2 b1) \/
  (shares_edge a3 a1 b3 b1 /\ opposite_sides a3 a1 a2 b2).

(* The four regime predicates, for real (#567; formerly `Prop := True` with
   machine-checked vacuity witnesses -- those witnesses return, flipped into
   their negations, at the end of this file).

   Conventions:
   - "closed region" of a CCW triangle is `{ pt | 0 <= gtri pt }`, its
     specified interior is `{ pt | 0 < gtri pt }` (ADR-0003).
   - Predicates whose content lives in the CLOSED region carry explicit CCW
     guards: for CW input `{ 0 <= gtri }` is empty and a guard-free
     definition would hold of garbage.  `triangles_partial_overlap` needs no
     guard -- a common specified-interior point already forces both
     orientations (`in_tri_interior_ccw`).
   - `triangle_a_contains_b` is CLOSED containment (admits equal triangles
     and boundary contact), with BOTH triangles guarded CCW.  NB the strict
     vertex detector `contains_b` (RelateNGCore) guards only A's
     orientation, so it does not by itself entail this predicate -- a
     CW-listed B passes the detector and fails the B-side guard here.
     The detector -> predicate bridge (barycentric / convexity lift,
     adding B's CCW hypothesis) is RelateNGContainsBridge
     (`contains_b_ccw_implies_closed_containment`), still #522 / 522-a.
   - The five names are not a partition of all pairs.  A partial-edge
     kiss that is not a full shared edge and not a single vertex
     satisfies none of them; the decline path (`TPR_Unsupported`)
     already exists. *)

Definition triangles_separated (a1 a2 a3 b1 b2 b3 : Point) : Prop :=
  tri_ccw a1 a2 a3 /\ tri_ccw b1 b2 b3 /\
  forall pt, ~ (in_tri_closure a1 a2 a3 pt /\ in_tri_closure b1 b2 b3 pt).

Definition triangles_partial_overlap (a1 a2 a3 b1 b2 b3 : Point) : Prop :=
  (exists pt, in_tri_interior a1 a2 a3 pt /\ in_tri_interior b1 b2 b3 pt) /\
  (exists pt, in_tri_interior a1 a2 a3 pt /\ in_tri_exterior b1 b2 b3 pt) /\
  (exists pt, in_tri_interior b1 b2 b3 pt /\ in_tri_exterior a1 a2 a3 pt).

Definition triangle_a_contains_b (a1 a2 a3 b1 b2 b3 : Point) : Prop :=
  tri_ccw a1 a2 a3 /\ tri_ccw b1 b2 b3 /\
  forall pt, in_tri_closure b1 b2 b3 pt -> in_tri_closure a1 a2 a3 pt.

Definition triangles_touch_on_edge (a1 a2 a3 b1 b2 b3 : Point) : Prop :=
  triangles_touch_on_shared_edge a1 a2 a3 b1 b2 b3.

Definition triangles_touch_at_vertex (a1 a2 a3 b1 b2 b3 : Point) : Prop :=
  tri_ccw a1 a2 a3 /\ tri_ccw b1 b2 b3 /\
  exists v, is_vertex_of v a1 a2 a3 /\ is_vertex_of v b1 b2 b3 /\
    forall pt, in_tri_closure a1 a2 a3 pt -> in_tri_closure b1 b2 b3 pt ->
      pt = v.

Definition classify_triangle_pair (a1 a2 a3 b1 b2 b3 : Point)
    (r : TrianglePairRegime) : Prop :=
  match r with
  | TPR_Disjoint    => triangles_separated a1 a2 a3 b1 b2 b3
  | TPR_Overlap     => triangles_partial_overlap a1 a2 a3 b1 b2 b3
  | TPR_Contains    => triangle_a_contains_b a1 a2 a3 b1 b2 b3
  | TPR_TouchEdge   => triangles_touch_on_edge a1 a2 a3 b1 b2 b3
  | TPR_TouchVertex => triangles_touch_at_vertex a1 a2 a3 b1 b2 b3
  (* Leftover Ⅰ: #567 placeholder returning. [True] is not a
     denotation. Do not prove [classify_triangle_pair] facts about
     this constructor. Fill stays [im_unsupported]. A later letter
     needs a real predicate, or this arm stays off
     [classify_triangle_pair]. Do not remint to a Touches fill —
     the compiled pair is sliver overlap (II nonempty). *)
  | TPR_TouchPartialEdge => True
  (* Leftover Ⅲ: same honesty as leftover Ⅰ. [True] is not a
     denotation. Do not prove [classify_triangle_pair] facts about
     this constructor. Fill stays [im_unsupported]. Not CONTEXT
     Bar 1. Exterior-side stem; II empty; do not remint to a
     Touches fill until the owner names a matrix. *)
  | TPR_TouchOnesided => True
  (* Leftover Ⅱ: same honesty as leftover Ⅰ. [True] is not a
     denotation. Do not prove [classify_triangle_pair] facts about
     this constructor. Fill stays [im_unsupported]. Not CONTEXT
     Bar 1. Closed-cone vertex kiss; do not remint to
     [aa_matrix_touch_vertical] — that pin is #572 / leftover
     `TPR_TouchVertex`. Do not remint [cone_separates_b]. *)
  | TPR_TouchObtuse => True
  (* Leftover Ⅴ: same honesty as leftover Ⅰ. [True] is not a
     denotation. Do not prove [classify_triangle_pair] facts about
     this constructor. Fill stays [im_unsupported]. Not CONTEXT
     Bar 1. Opposite-sign cone at a shared vertex; do not remint
     [cone_separates_b] / [touch_obtuse_vertex_b]. *)
  | TPR_MixedCone => True
  (* Leftover Ⅵ: same honesty as leftover Ⅰ. [True] is not a
     denotation. Do not prove [classify_triangle_pair] facts about
     this constructor. Fill stays [im_unsupported]. Not CONTEXT
     Bar 1. Same-sign cone spill at a shared vertex; interiors
     may meet. Do not remint [cone_separates_b] /
     [mixed_cone_vertex_b] / [overlap_b]. Do not emit
     [2FFF1FFF2]. *)
  | TPR_SameCone => True
  (* `TPR_Unsupported` names no configuration -- it records that the
     classifier made no claim.  `True` is the correct denotation of "no
     claim"; unlike the five arms above it is not a geometric predicate. *)
  | TPR_Unsupported => True
  end.

(* -------------------------------------------------------------------------- *)
(* Pairwise exclusivity.                                                      *)
(*                                                                            *)
(* All six pairs among {separated, overlap, contains, touch-at-vertex} are    *)
(* mutually exclusive.  That block is not a partition of all pairs: a         *)
(* partial-edge kiss can miss every named arm and still decline.              *)
(* `TPR_TouchEdge` is deliberately absent: its predicate is the frozen        *)
(* shared-edge vocabulary (RelateNGTouch anchors) and its exclusivity         *)
(* against the gtri-shaped predicates is not a cheap consequence of the       *)
(* definitions.  #567 / 522-a DoD does not include that exclusivity; the      *)
(* leftover is carved (witness 522-a-touch-edge-carve).  If minted later,     *)
(* use leftover letter 522-n — do not remint the frozen anchors.              *)
(* -------------------------------------------------------------------------- *)

Theorem separated_not_overlap : forall a1 a2 a3 b1 b2 b3,
  triangles_separated a1 a2 a3 b1 b2 b3 ->
  ~ triangles_partial_overlap a1 a2 a3 b1 b2 b3.
Proof.
  intros a1 a2 a3 b1 b2 b3 (_ & _ & Hsep) ([pt [HiA HiB]] & _ & _).
  exact (Hsep pt (conj (in_tri_interior_closure _ _ _ _ HiA)
                       (in_tri_interior_closure _ _ _ _ HiB))).
Qed.

Theorem contains_not_overlap : forall a1 a2 a3 b1 b2 b3,
  triangle_a_contains_b a1 a2 a3 b1 b2 b3 ->
  ~ triangles_partial_overlap a1 a2 a3 b1 b2 b3.
Proof.
  intros a1 a2 a3 b1 b2 b3 (_ & _ & Hsub) (_ & _ & [pt [HiB HeA]]).
  apply (in_tri_exterior_not_closure a1 a2 a3 pt HeA).
  apply Hsub. apply in_tri_interior_closure. exact HiB.
Qed.

Theorem contains_not_separated : forall a1 a2 a3 b1 b2 b3,
  triangle_a_contains_b a1 a2 a3 b1 b2 b3 ->
  ~ triangles_separated a1 a2 a3 b1 b2 b3.
Proof.
  intros a1 a2 a3 b1 b2 b3 (_ & HccwB & Hsub) (_ & _ & Hsep).
  assert (Hb1 : in_tri_closure b1 b2 b3 b1)
    by (apply vertex_in_tri_closure; [ exact HccwB | left; reflexivity ]).
  exact (Hsep b1 (conj (Hsub b1 Hb1) Hb1)).
Qed.

Theorem touch_vertex_not_separated : forall a1 a2 a3 b1 b2 b3,
  triangles_touch_at_vertex a1 a2 a3 b1 b2 b3 ->
  ~ triangles_separated a1 a2 a3 b1 b2 b3.
Proof.
  intros a1 a2 a3 b1 b2 b3 (HccwA & HccwB & [v (HvA & HvB & _)]) (_ & _ & Hsep).
  exact (Hsep v (conj (vertex_in_tri_closure _ _ _ _ HccwA HvA)
                      (vertex_in_tri_closure _ _ _ _ HccwB HvB))).
Qed.

Theorem touch_vertex_not_overlap : forall a1 a2 a3 b1 b2 b3,
  triangles_touch_at_vertex a1 a2 a3 b1 b2 b3 ->
  ~ triangles_partial_overlap a1 a2 a3 b1 b2 b3.
Proof.
  intros a1 a2 a3 b1 b2 b3 (_ & _ & [v (HvA & _ & Huniq)]) ([pt [HiA HiB]] & _ & _).
  assert (Hpt : pt = v)
    by (apply Huniq; apply in_tri_interior_closure; assumption).
  subst pt.
  exact (vertex_not_in_tri_interior a1 a2 a3 v HvA HiA).
Qed.

Theorem touch_vertex_not_contains : forall a1 a2 a3 b1 b2 b3,
  triangles_touch_at_vertex a1 a2 a3 b1 b2 b3 ->
  ~ triangle_a_contains_b a1 a2 a3 b1 b2 b3.
Proof.
  intros a1 a2 a3 b1 b2 b3 (_ & HccwB & [v (_ & _ & Huniq)]) (_ & _ & Hsub).
  (* Contained closure meets A's closure everywhere, so B's closure collapses
     to the single point v -- flattening B against its CCW guard. *)
  assert (Hb1c : in_tri_closure b1 b2 b3 b1)
    by (apply vertex_in_tri_closure; [ exact HccwB | left; reflexivity ]).
  assert (Hb2c : in_tri_closure b1 b2 b3 b2)
    by (apply vertex_in_tri_closure; [ exact HccwB | right; left; reflexivity ]).
  assert (Hb1 : b1 = v) by (apply Huniq; [ apply Hsub; exact Hb1c | exact Hb1c ]).
  assert (Hb2 : b2 = v) by (apply Huniq; [ apply Hsub; exact Hb2c | exact Hb2c ]).
  subst b1 b2. unfold tri_ccw in HccwB.
  assert (E : gdbl (px v) (py v) (px v) (py v) (px b3) (py b3) = 0)
    by (unfold gdbl; ring).
  lra.
Qed.

(* WITNESS topic: relate · claimId: 522-a · witness: 522-a-regime-exclusive *)
(* WITNESS {"claimId":"522-a","topic":"relate","lemma":"regime_predicates_pairwise_exclusive","title":"Triangle regime predicates are real geometry and pairwise exclusive","file":"theories/RelateMatrixTriangle.v"} *)

Theorem regime_predicates_pairwise_exclusive : forall a1 a2 a3 b1 b2 b3,
  (triangles_separated a1 a2 a3 b1 b2 b3 ->
     ~ triangles_partial_overlap a1 a2 a3 b1 b2 b3) /\
  (triangle_a_contains_b a1 a2 a3 b1 b2 b3 ->
     ~ triangles_partial_overlap a1 a2 a3 b1 b2 b3) /\
  (triangle_a_contains_b a1 a2 a3 b1 b2 b3 ->
     ~ triangles_separated a1 a2 a3 b1 b2 b3) /\
  (triangles_touch_at_vertex a1 a2 a3 b1 b2 b3 ->
     ~ triangles_separated a1 a2 a3 b1 b2 b3) /\
  (triangles_touch_at_vertex a1 a2 a3 b1 b2 b3 ->
     ~ triangles_partial_overlap a1 a2 a3 b1 b2 b3) /\
  (triangles_touch_at_vertex a1 a2 a3 b1 b2 b3 ->
     ~ triangle_a_contains_b a1 a2 a3 b1 b2 b3).
Proof.
  intros a1 a2 a3 b1 b2 b3.
  repeat split.
  - apply separated_not_overlap.
  - apply contains_not_overlap.
  - apply contains_not_separated.
  - apply touch_vertex_not_separated.
  - apply touch_vertex_not_overlap.
  - apply touch_vertex_not_contains.
Qed.

(* -------------------------------------------------------------------------- *)
(* Vacuity witnesses, FLIPPED (honesty, #567).                                *)
(*                                                                            *)
(* The four arms used to be `True`; the vacuity witnesses proved that any six *)
(* points satisfied them.  Each witness now returns as its own negation, on   *)
(* the #530 dispatch pair (RelateNGCore.relate_triangle_dispatch_ex): two     *)
(* genuinely separated CCW triangles.  The dual failure mode -- a predicate   *)
(* that is `False` in disguise -- is ruled out by the satisfiability          *)
(* witnesses that follow.                                                     *)
(* -------------------------------------------------------------------------- *)

(* The #530 dispatch pair provably satisfies the new `triangles_separated`:
   A's closed region forces px <= 1, B's forces px >= 2. *)
Lemma dispatch_pair_separated :
  triangles_separated (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
                      (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1).
Proof.
  split; [ | split ].
  - unfold tri_ccw, gdbl; cbn [px py]; lra.
  - unfold tri_ccw, gdbl; cbn [px py]; lra.
  - intros pt [HA HB].
    unfold in_tri_closure in HA, HB.
    apply gtri_nonneg_iff in HA; apply gtri_nonneg_iff in HB.
    destruct HA as [HA1 [HA2 HA3]]; destruct HB as [HB1 [HB2 HB3]].
    unfold gsA, gsB, gsC in *; cbn [px py] in *; lra.
Qed.

(* Was `classify_disjoint_vacuous` (any six points): the disjoint arm now
   FAILS where it must -- e.g. on the unit triangle against itself. *)
Theorem classify_disjoint_fails_of_a_shared_pair :
  ~ classify_triangle_pair (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
                           (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
                           TPR_Disjoint.
Proof.
  intros (HccwA & _ & Hsep).
  assert (Hv : in_tri_closure (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
                              (mkPoint 0 0))
    by (apply vertex_in_tri_closure; [ exact HccwA | left; reflexivity ]).
  exact (Hsep (mkPoint 0 0) (conj Hv Hv)).
Qed.

(* Was `classify_overlap_vacuous` / `classify_overlap_holds_of_a_separated_pair`
   (the sharpest vacuity witness): the overlap arm held of a provably
   separated pair.  Now it provably fails on one. *)
Theorem classify_overlap_fails_of_a_separated_pair :
  ~ classify_triangle_pair (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
                           (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1)
                           TPR_Overlap.
Proof.
  exact (separated_not_overlap _ _ _ _ _ _ dispatch_pair_separated).
Qed.

(* The ORIGINAL sharpest-witness pair, (9,9)(10,9)(9,10): the pre-#567
   witness showed the overlap arm holding of exactly this separated pair,
   so its negation is proven on exactly this pair too -- the flip is
   literal, not just in spirit. *)
Lemma original_pair_separated :
  triangles_separated (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
                      (mkPoint 9 9) (mkPoint 10 9) (mkPoint 9 10).
Proof.
  split; [ | split ].
  - unfold tri_ccw, gdbl; cbn [px py]; lra.
  - unfold tri_ccw, gdbl; cbn [px py]; lra.
  - intros pt [HA HB].
    unfold in_tri_closure in HA, HB.
    apply gtri_nonneg_iff in HA; apply gtri_nonneg_iff in HB.
    destruct HA as [HA1 [HA2 HA3]]; destruct HB as [HB1 [HB2 HB3]].
    unfold gsA, gsB, gsC in *; cbn [px py] in *; lra.
Qed.

Theorem classify_overlap_fails_of_the_original_pair :
  ~ classify_triangle_pair (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
                           (mkPoint 9 9) (mkPoint 10 9) (mkPoint 9 10)
                           TPR_Overlap.
Proof.
  exact (separated_not_overlap _ _ _ _ _ _ original_pair_separated).
Qed.

(* Was `classify_contains_vacuous`. *)
Theorem classify_contains_fails_of_a_separated_pair :
  ~ classify_triangle_pair (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
                           (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1)
                           TPR_Contains.
Proof.
  intros Hcont.
  exact (contains_not_separated _ _ _ _ _ _ Hcont dispatch_pair_separated).
Qed.

(* Was `classify_touch_vertex_vacuous`. *)
Theorem classify_touch_vertex_fails_of_a_separated_pair :
  ~ classify_triangle_pair (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
                           (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1)
                           TPR_TouchVertex.
Proof.
  intros Htv.
  exact (touch_vertex_not_separated _ _ _ _ _ _ Htv dispatch_pair_separated).
Qed.

(* And positively: the dispatch pair satisfies exactly the regime it is in. *)
Theorem classify_disjoint_holds_of_the_dispatch_pair :
  classify_triangle_pair (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
                         (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1)
                         TPR_Disjoint.
Proof. exact dispatch_pair_separated. Qed.

(* -------------------------------------------------------------------------- *)
(* Satisfiability witnesses.                                                  *)
(*                                                                            *)
(* Each new predicate holds of a concrete pair, so none is `False` in         *)
(* disguise -- the dual of the old vacuity.  Together with the flipped        *)
(* witnesses above, every strict/closed sign in the definitions is pinned.    *)
(*                                                                            *)
(* Mutation replay (in-tree, #567; not an ADR-0004 mint).  Flip exactly one   *)
(* comparison below, rebuild this file, then restore the sign.  Each flip     *)
(* loses Qed on a named lemma here:                                           *)
(*   1. `in_tri_interior`: `0 < gtri` → `0 <= gtri`                           *)
(*      pin: `vertex_not_in_tri_interior`                                     *)
(*   2. `in_tri_closure`: `0 <= gtri` → `0 < gtri`                            *)
(*      pin: `vertex_in_tri_closure`                                          *)
(*   3. `in_tri_exterior`: `gtri < 0` → `gtri <= 0`                           *)
(*      pin: `in_tri_exterior_not_closure`                                    *)
(*   4. `triangle_a_contains_b`: A's `in_tri_closure` → `in_tri_interior`     *)
(*      pin: `contains_is_closed_containment`                                 *)
(*   5. `triangles_touch_at_vertex`: `pt = v` uniqueness over closures;       *)
(*      flip either closure test to interior and the closed-meet pin moves.   *)
(*      pin: `touch_vertex_pair_touches` (closed meet at the shared vertex)   *)
(* -------------------------------------------------------------------------- *)

(* Unit triangle vs its translate by (1/4, 1/4): common interior point,
   and each has interior points strictly outside the other. *)
Lemma overlap_pair_overlaps :
  triangles_partial_overlap
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint (1/4) (1/4)) (mkPoint (5/4) (1/4)) (mkPoint (1/4) (5/4)).
Proof.
  split; [ | split ].
  - exists (mkPoint (3/8) (3/8)).
    split; unfold in_tri_interior; apply gtri_pos_iff;
      unfold gsA, gsB, gsC; cbn [px py]; repeat split; lra.
  - exists (mkPoint (1/8) (1/8)).
    split.
    + unfold in_tri_interior; apply gtri_pos_iff;
        unfold gsA, gsB, gsC; cbn [px py]; repeat split; lra.
    + unfold in_tri_exterior.
      eapply Rle_lt_trans; [ apply gtri_le_gsC | ].
      unfold gsC; cbn [px py]; lra.
  - exists (mkPoint (3/4) (1/2)).
    split.
    + unfold in_tri_interior; apply gtri_pos_iff;
        unfold gsA, gsB, gsC; cbn [px py]; repeat split; lra.
    + unfold in_tri_exterior.
      eapply Rle_lt_trans; [ apply gtri_le_gsB | ].
      unfold gsB; cbn [px py]; lra.
Qed.

(* Closed containment of a strictly interior triangle. *)
Lemma contains_pair_contains :
  triangle_a_contains_b
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint (1/4) (1/4)) (mkPoint (1/2) (1/4)) (mkPoint (1/4) (1/2)).
Proof.
  split; [ | split ].
  - unfold tri_ccw, gdbl; cbn [px py]; lra.
  - unfold tri_ccw, gdbl; cbn [px py]; lra.
  - intros pt HB. unfold in_tri_closure in *.
    apply gtri_nonneg_iff in HB. apply gtri_nonneg_iff.
    destruct HB as [H1 [H2 H3]].
    unfold gsA, gsB, gsC in *; cbn [px py] in *.
    repeat split; lra.
Qed.

(* Closed containment admits equal triangles -- the regression that pins the
   CLOSED conclusion (a strict-conclusion mutation breaks exactly here). *)
Lemma contains_is_closed_containment :
  triangle_a_contains_b
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1).
Proof.
  split; [ | split ].
  - unfold tri_ccw, gdbl; cbn [px py]; lra.
  - unfold tri_ccw, gdbl; cbn [px py]; lra.
  - intros pt H; exact H.
Qed.

(* Unit triangle vs its reflection through the origin: the closed regions
   meet exactly at the shared vertex (0,0). *)
Lemma touch_vertex_pair_touches :
  triangles_touch_at_vertex
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint 0 0) (mkPoint (-1) 0) (mkPoint 0 (-1)).
Proof.
  split; [ | split ].
  - unfold tri_ccw, gdbl; cbn [px py]; lra.
  - unfold tri_ccw, gdbl; cbn [px py]; lra.
  - exists (mkPoint 0 0).
    split; [ left; reflexivity | split; [ left; reflexivity | ] ].
    intros pt HA HB. destruct pt as [x y].
    unfold in_tri_closure in HA, HB.
    apply gtri_nonneg_iff in HA; apply gtri_nonneg_iff in HB.
    destruct HA as [HA1 [HA2 HA3]]; destruct HB as [HB1 [HB2 HB3]].
    unfold gsA, gsB, gsC in *; cbn [px py] in *.
    f_equal; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions regime_predicates_pairwise_exclusive.
Print Assumptions dispatch_pair_separated.
Print Assumptions overlap_pair_overlaps.
Print Assumptions contains_pair_contains.
Print Assumptions touch_vertex_pair_touches.
