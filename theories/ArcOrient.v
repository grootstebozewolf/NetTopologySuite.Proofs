(* ============================================================================
   NetTopologySuite.Proofs.ArcOrient
   ----------------------------------------------------------------------------
   Phase 4 Session 3: arc orientation predicate.

   Two related tools, both R-side:

     1. `cross_R_pt` -- 2D cross product (parallel of `cross_R_BP` from
        Orient_b64_sound.v but on Stdlib `Point` rather than `BPoint`).
        The Phase 0 chord-orientation primitive lifted to Stdlib R.

     2. `inCircle_R` -- 4-point lifted determinant (the standard Shewchuk
        1997 / Guibas-Stolfi convention).  Sign indicates whether the
        4th point is inside, on, or outside the circumscribed circle of
        the first three.  This is the load-bearing tool for arc-arc
        intersection (S4) where we need to compare a query point's
        relation to an arc's circle.

   Arc orientation built on top of these:

     - `arc_side_chord` -- which side of the chord `(arc_start, arc_end)`
       a point lies on.  This is the orientation primitive we actually use
       for `arc_orient` because `arc_mid` is on the circumscribed circle
       (it's one of the three defining points!), so `inCircle_R` would
       trivially classify `arc_mid` as on-circle rather than interior.

     - `arc_interior_side` -- predicate form: `P` on the same side of the
       chord as `arc_mid`.  This IS the arc's interior region.

     - `arc_orient` -- computable trichotomy
       (ArcInterior / ArcExterior / ArcOnChord).

   Sign-convention design decision (recorded for posterity): for the
   "which side of an arc" question, the chord cross product is the right
   primitive.  The 3x3 / 4x4 lifted determinant is for "inside which
   circle" -- different question, S4's job.  Both definitions land here
   to keep the arc-orientation machinery in one file.

   See `docs/audit-phase4-chord-overfitting.md` §3 (GENERALIZE on
   `cross_R_BP` / NEW PROOF on `b64_orient_arc_*`).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.

From NTS.Proofs Require Import Distance.
From NTS.Proofs Require Import CurveGeometry.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Cross product on Stdlib Point.                                         *)
(*                                                                            *)
(* Direct lift of Orient_b64_sound.v:148's `cross_R_BP` to Stdlib `Point`     *)
(* (no Flocq B2R wrapping).  Same sign convention: positive iff (P0, P1, Q)   *)
(* is counter-clockwise.                                                      *)
(* -------------------------------------------------------------------------- *)

Definition cross_R_pt (P0 P1 Q : Point) : R :=
  (px P1 - px P0) * (py Q - py P0)
  - (px Q - px P0) * (py P1 - py P0).

(* -------------------------------------------------------------------------- *)
(* §2  inCircle_R: 4-point lifted determinant.                                *)
(*                                                                            *)
(* Shewchuk 1997 §3 (Eq. 21) / Guibas-Stolfi convention:                      *)
(*                                                                            *)
(*   inCircle_R A B C P =                                                     *)
(*     det of                                                                  *)
(*       | Ax-Px    Ay-Py    (Ax-Px)^2 + (Ay-Py)^2 |                          *)
(*       | Bx-Px    By-Py    (Bx-Px)^2 + (By-Py)^2 |                          *)
(*       | Cx-Px    Cy-Py    (Cx-Px)^2 + (Cy-Py)^2 |                          *)
(*                                                                            *)
(* Positive iff (A,B,C) is CCW AND P is inside the circumscribed circle.     *)
(* For CW (A,B,C), the sign flips; consumers compose with a CCW-orientation   *)
(* test if they need the absolute "inside circle" answer.                    *)
(*                                                                            *)
(* Cofactor expansion along the first column gives the explicit formula      *)
(* below.  This is structurally NEW PROOF per the audit doc; no               *)
(* Stdlib/Flocq analog exists.                                                *)
(* -------------------------------------------------------------------------- *)

Definition inCircle_R (A B C P : Point) : R :=
  let ax := px A - px P in
  let ay := py A - py P in
  let bx := px B - px P in
  let by_ := py B - py P in
  let cx := px C - px P in
  let cy := py C - py P in
  let na := ax * ax + ay * ay in
  let nb := bx * bx + by_ * by_ in
  let nc := cx * cx + cy * cy in
  ax * (by_ * nc - cy * nb)
  - ay * (bx * nc - cx * nb)
  + na * (bx * cy - cx * by_).

(* -------------------------------------------------------------------------- *)
(* §3  Arc orientation (chord-based).                                         *)
(*                                                                            *)
(* `arc_side_chord a P` = `cross_R_pt (arc_start a) (arc_end a) P`.  Sign     *)
(* indicates which side of the open chord (arc_start, arc_end) the point P    *)
(* lies on.                                                                   *)
(*                                                                            *)
(* `arc_interior_side a P` = "P is on the same side as arc_mid".  This is     *)
(* the interior side of the arc (the bulge side).                             *)
(*                                                                            *)
(* `arc_orient a P` is the computable trichotomy.                             *)
(* -------------------------------------------------------------------------- *)

Definition arc_side_chord (a : CircularArc) (P : Point) : R :=
  cross_R_pt (arc_start a) (arc_end a) P.

Definition arc_interior_side (a : CircularArc) (P : Point) : Prop :=
  0 < arc_side_chord a (arc_mid a) * arc_side_chord a P.

Inductive ArcSide : Type :=
  | ArcInterior
  | ArcExterior
  | ArcOnChord.

Definition arc_orient (a : CircularArc) (P : Point) : ArcSide :=
  let s_mid := arc_side_chord a (arc_mid a) in
  let s_P := arc_side_chord a P in
  let prod := s_mid * s_P in
  if Rgt_dec prod 0 then ArcInterior
  else if Rlt_dec prod 0 then ArcExterior
  else ArcOnChord.

(* -------------------------------------------------------------------------- *)
(* §4  Soundness lemmas.                                                      *)
(* -------------------------------------------------------------------------- *)

(* cross_R_pt is antisymmetric in its first two arguments. *)
Lemma cross_R_pt_antisymm :
  forall P0 P1 Q : Point,
    cross_R_pt P0 P1 Q = - cross_R_pt P1 P0 Q.
Proof. intros. unfold cross_R_pt. ring. Qed.

(* arc_side_chord on arc_mid equals the negation of valid_arc's expression
   (which uses (mid - start) cross (end - start) -- arc_side_chord uses
   the opposite ordering (end - start) cross (mid - start)). *)
Lemma arc_side_chord_mid_eq_neg_valid :
  forall a : CircularArc,
    arc_side_chord a (arc_mid a)
    = - ((px (arc_mid a) - px (arc_start a))
         * (py (arc_end a) - py (arc_start a))
       - (py (arc_mid a) - py (arc_start a))
         * (px (arc_end a) - px (arc_start a))).
Proof. intros. unfold arc_side_chord, cross_R_pt. ring. Qed.

(* Under valid_arc, arc_side_chord at arc_mid is non-zero. *)
Lemma arc_side_chord_mid_nonzero :
  forall a : CircularArc,
    valid_arc a -> arc_side_chord a (arc_mid a) <> 0.
Proof.
  intros a Hva Hzero.
  apply Hva.
  unfold valid_arc.
  rewrite arc_side_chord_mid_eq_neg_valid in Hzero.
  lra.
Qed.

(* arc_mid is on the interior side of its own arc -- the key sanity check. *)
Theorem arc_interior_side_mid :
  forall a : CircularArc,
    valid_arc a -> arc_interior_side a (arc_mid a).
Proof.
  intros a Hva.
  unfold arc_interior_side.
  pose proof (arc_side_chord_mid_nonzero a Hva) as Hnz.
  set (s := arc_side_chord a (arc_mid a)) in *.
  (* Goal: 0 < s * s.  Follows from s <> 0 via Rsqr_pos / nra. *)
  nra.
Qed.

(* arc_orient at arc_mid evaluates to ArcInterior. *)
Theorem arc_orient_mid :
  forall a : CircularArc,
    valid_arc a -> arc_orient a (arc_mid a) = ArcInterior.
Proof.
  intros a Hva.
  unfold arc_orient.
  pose proof (arc_interior_side_mid a Hva) as Hint.
  unfold arc_interior_side in Hint.
  destruct (Rgt_dec (arc_side_chord a (arc_mid a) *
                     arc_side_chord a (arc_mid a)) 0) as [_|Hcontra].
  - reflexivity.
  - exfalso. apply Hcontra. exact Hint.
Qed.

(* inCircle_R at one of its defining points is zero (two equal rows in
   the determinant after lifting). *)
Lemma inCircle_R_at_C : forall A B C : Point, inCircle_R A B C C = 0.
Proof. intros. unfold inCircle_R. cbn. ring. Qed.

Lemma inCircle_R_at_B : forall A B C : Point, inCircle_R A B C B = 0.
Proof. intros. unfold inCircle_R. cbn. ring. Qed.

Lemma inCircle_R_at_A : forall A B C : Point, inCircle_R A B C A = 0.
Proof. intros. unfold inCircle_R. cbn. ring. Qed.

(* Diagnostic corollary explaining why arc_orient cannot use inCircle_R:
   at arc_mid (one of the three defining points), inCircle_R is zero. *)
Corollary inCircle_R_arc_mid_zero :
  forall a : CircularArc,
    inCircle_R (arc_start a) (arc_end a) (arc_mid a) (arc_mid a) = 0.
Proof. intros. apply inCircle_R_at_C. Qed.

(* -------------------------------------------------------------------------- *)
(* inCircle_R algebraic sign family.                                          *)
(*                                                                            *)
(* `inCircle_R A B C P` is the 3x3 determinant of the lifted rows             *)
(* [ax ay na; bx by nb; cx cy nc] (coordinates relative to P, lifted by the   *)
(* squared norm).  So it obeys the determinant symmetries: swapping two of    *)
(* A,B,C swaps two rows and flips the sign; a cyclic permutation is an even   *)
(* permutation and preserves it; and the predicate is translation-invariant   *)
(* (it depends only on the offsets from P).  These are the Delaunay           *)
(* sign-convention foundations -- the inCircle analogue of Phase 0's          *)
(* cross_antisymmetric / cross_cyclic / cross_translation_invariant.          *)
(* -------------------------------------------------------------------------- *)

Lemma inCircle_R_swap_AB : forall A B C P : Point,
  inCircle_R B A C P = - inCircle_R A B C P.
Proof. intros. unfold inCircle_R. ring. Qed.

Lemma inCircle_R_swap_BC : forall A B C P : Point,
  inCircle_R A C B P = - inCircle_R A B C P.
Proof. intros. unfold inCircle_R. ring. Qed.

Lemma inCircle_R_swap_AC : forall A B C P : Point,
  inCircle_R C B A P = - inCircle_R A B C P.
Proof. intros. unfold inCircle_R. ring. Qed.

Lemma inCircle_R_cyclic : forall A B C P : Point,
  inCircle_R B C A P = inCircle_R A B C P.
Proof. intros. unfold inCircle_R. ring. Qed.

(* Translation invariance: shifting all four points by the same vector leaves *)
(* the predicate unchanged (the defining offsets from P are preserved).       *)
Lemma inCircle_R_translation_invariant : forall (A B C P : Point) (vx vy : R),
  inCircle_R (mkPoint (px A + vx) (py A + vy))
             (mkPoint (px B + vx) (py B + vy))
             (mkPoint (px C + vx) (py C + vy))
             (mkPoint (px P + vx) (py P + vy))
  = inCircle_R A B C P.
Proof. intros. unfold inCircle_R. cbn. ring. Qed.

(* Scaling homogeneity: inCircle_R is degree 4 (two linear offset factors x   *)
(* two squared-norm factors), so a uniform scale by `s` multiplies it by      *)
(* s^4.  With translation invariance above and the (deferred) rotation case,  *)
(* this makes the *sign* a similarity invariant -- the geometric basis of the *)
(* Delaunay / incircle test.                                                   *)
Lemma inCircle_R_scaling : forall (A B C P : Point) (s : R),
  inCircle_R (mkPoint (s * px A) (s * py A)) (mkPoint (s * px B) (s * py B))
             (mkPoint (s * px C) (s * py C)) (mkPoint (s * px P) (s * py P))
  = (s * s * s * s) * inCircle_R A B C P.
Proof. intros. unfold inCircle_R. cbn. ring. Qed.

(* Positive uniform scaling preserves the incircle sign (s^4 > 0). *)
Lemma inCircle_R_scale_pos_iff_pos : forall (A B C P : Point) (s : R),
  0 < s ->
  (0 < inCircle_R (mkPoint (s * px A) (s * py A)) (mkPoint (s * px B) (s * py B))
                  (mkPoint (s * px C) (s * py C)) (mkPoint (s * px P) (s * py P))
   <-> 0 < inCircle_R A B C P).
Proof.
  intros A B C P s Hs.
  rewrite (inCircle_R_scaling A B C P s).
  assert (Hpos : 0 < s * s * s * s) by (repeat apply Rmult_lt_0_compat; exact Hs).
  split; intro H.
  - apply (Rmult_lt_reg_l (s * s * s * s)); [exact Hpos|].
    rewrite Rmult_0_r. exact H.
  - apply Rmult_lt_0_compat; [exact Hpos | exact H].
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  arc_coord_safe -- R-side precondition for exact 3x3 determinant.       *)
(*                                                                            *)
(* Magnitude bound on coordinates suitable for the inCircle_R arithmetic.    *)
(* The 4-point lifted determinant has degree-4 products (two lifted          *)
(* coordinates each ~2^50 multiplied with two unlifted ~2^25 = 2^150);       *)
(* for binary64 exact arithmetic the inputs need to be much smaller.  The    *)
(* 2^25 bound here matches Phase 0's `coord_int_safe` (HotPixel_b64.v) for   *)
(* the 2x2 chord cross product; S4 will tighten or split this for the 3x3    *)
(* case when actually computing in binary64.                                  *)
(*                                                                            *)
(* This is the R-SIDE bound (Stdlib Reals); the binary64 mirror lives in    *)
(* the Flocq layer with its own integer-witness predicate.                   *)
(* -------------------------------------------------------------------------- *)

Definition arc_coord_safe (p : Point) : Prop :=
  Rabs (px p) < 33554432 /\ Rabs (py p) < 33554432.
(* 33554432 = 2^25. *)

(* Trivial structural lemma: arc_coord_safe is a conjunction predicate. *)
Lemma arc_coord_safe_px :
  forall p : Point,
    arc_coord_safe p -> Rabs (px p) < 33554432.
Proof. intros p [Hx _]. exact Hx. Qed.

Lemma arc_coord_safe_py :
  forall p : Point,
    arc_coord_safe p -> Rabs (py p) < 33554432.
Proof. intros p [_ Hy]. exact Hy. Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions cross_R_pt_antisymm.
Print Assumptions arc_side_chord_mid_eq_neg_valid.
Print Assumptions arc_side_chord_mid_nonzero.
Print Assumptions arc_interior_side_mid.
Print Assumptions arc_orient_mid.
Print Assumptions inCircle_R_at_C.
Print Assumptions inCircle_R_at_B.
Print Assumptions inCircle_R_at_A.
Print Assumptions inCircle_R_arc_mid_zero.
Print Assumptions inCircle_R_swap_AB.
Print Assumptions inCircle_R_swap_BC.
Print Assumptions inCircle_R_swap_AC.
Print Assumptions inCircle_R_cyclic.
Print Assumptions inCircle_R_translation_invariant.
Print Assumptions arc_coord_safe_px.
Print Assumptions arc_coord_safe_py.
