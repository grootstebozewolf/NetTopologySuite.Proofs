(* ============================================================================
   NetTopologySuite.Proofs.ClothoidShearLawStmt
   ----------------------------------------------------------------------------
   STATEMENTS ONLY (no Lemma / Theorem / Proof here).  The statement half of
   claimId `cloth-linear-law-iff-similarity`; the proof half is
   ClothoidShearLaw.v, which must prove exactly `claim`, `supporting` and
   `witness` below.  The code of this file (comments excluded) is pinned by
   sha256 in docs/claim-statements.json and checked by
   scripts/check_claim_statements.py.

   Objects.  The host clothoid in arc length s (ClothoidTraversal:
   cloth_arc, unit tangent cloth_arc_v, its derivative cloth_arc_a) read
   through a linear placement M (ClothoidPlacement: placed o M).  The
   placed tangent is M v and its derivative M a (cloth_placed_curvature
   computes both), so the placed signed curvature is
   signed_curv (M v) (M a) and the placed speed is |M v|.

   "Curvature linear in placed arc length on (s1, s2)" is stated without
   an integral: some sg with sg' = |M v| on (s1, s2) (any placed
   arc-length function; it is fixed up to a constant, absorbed in a) has
   kappa_P = a + b * sg there.

   A placement is conformal when M^T M = lam^2 I: columns of equal length
   and orthogonal.  With det M <> 0 this is exactly a similarity, a
   rotation or a reflection times lam > 0 (ClothoidPlacement lin_sim /
   lin_refl).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending
   (review.status in docs/claim-statements.json).
   ========================================================================== *)

From Stdlib Require Import Reals Ranalysis1.
From NTS.Proofs Require Import Distance SignedCurvature SheetHenClothoidCore
  ClothoidTraversal ClothoidPlacement.

Local Open Scope R_scope.

Definition placed_curv (c : ClothoidEgg) (M : Lin2) (s : R) : R :=
  signed_curv (lin_ap M (cloth_arc_v c s)) (lin_ap M (cloth_arc_a c s)).

Definition placed_speed (c : ClothoidEgg) (M : Lin2) (s : R) : R :=
  sqrt (curv_speed2 (lin_ap M (cloth_arc_v c s))).

Definition lin_conformal (M : Lin2) : Prop :=
  l11 M * l11 M + l21 M * l21 M = l12 M * l12 M + l22 M * l22 M /\
  l11 M * l12 M + l21 M * l22 M = 0.

Definition linear_law_on (c : ClothoidEgg) (M : Lin2) (s1 s2 : R) : Prop :=
  exists (sg : R -> R) (a b : R),
    forall s, s1 < s < s2 ->
      derivable_pt_lim sg s (placed_speed c M s) /\
      placed_curv c M s = a + b * sg s.

(* main: on any window of positive length, the placed curvature of a
   non-degenerate placed clothoid is linear in placed arc length if and only
   if the placement is a similarity. *)
Definition claim : Prop :=
  forall c M s1 s2,
    cloth_A c <> 0 -> cloth_h2 c <> 0 -> cloth_d c <> 0 ->
    lin_det M <> 0 -> s1 < s2 ->
    (linear_law_on c M s1 s2 <-> lin_conformal M).

(* supporting: the converse is pointwise rigid.  A unit vector v and a
   placement with M v . M J v = 0 and |M J v| = |M v| (J the quarter turn)
   already force M conformal; this is the step the proof ends on. *)
Definition supporting : Prop :=
  forall M x y, x * x + y * y = 1 ->
    (l11 M * x + l12 M * y) * (- l11 M * y + l12 M * x)
      + (l21 M * x + l22 M * y) * (- l21 M * y + l22 M * x) = 0 ->
    curv_speed2 (lin_ap M (mkPoint (- y) x)) = curv_speed2 (lin_ap M (mkPoint x y)) ->
    lin_conformal M.

(* witness: the GEOS #1566 sheared placement (u, v) = ((2, 0), (1/2, 1)) has
   no window, however short, on which its curvature is linear in placed arc
   length; the old geos_shear_curvature_not_affine was the window (0, 11) in
   host arc length only. *)
Definition witness : Prop :=
  forall s1 s2, s1 < s2 -> ~ linear_law_on geos_shear_egg geos_shear s1 s2.
