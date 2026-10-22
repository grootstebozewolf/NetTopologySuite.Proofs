(* ============================================================================
   NetTopologySuite.Proofs.ArcSimilarityStmt
   ----------------------------------------------------------------------------
   STATEMENTS ONLY (no Lemma / Theorem / Proof here).  The statement half of
   the statement/proof split for the arc-similarity claim (claimId
   `arc-sim-image`); the proof half is ArcSimilarityImage.v, which must prove
   exactly `claim`, `supporting` and `witness` below.  The code of this
   file (comments excluded) is pinned by sha256 in docs/claim-statements.json
   and checked by scripts/check_claim_statements.py, so a refactor cannot
   silently weaken a cited statement.

   Pattern inspired by the Comparator statement/solution split and
   formalization.yaml v0.4 (openai/math@1581d4cb, ideas only; nothing from
   that catalogue is cited as proved here).

   Objects: the repo's own SQL/MM three-point arc `CurveGeometry.CircularArc`
   (with `valid_arc`, `arc_center`, `arc_radius`) and the algebraic arc
   membership `CurveRingSimple.on_arc` (on the circumcircle and in the sweep).
   A similarity is z |-> (a + b i) z + t (sim_refl = false) or
   z |-> (a + b i) conj(z) + t (sim_refl = true), with a = sim_a, b = sim_b,
   t = sim_tx + sim_ty i, a + b i <> 0, and scale sqrt (a^2 + b^2)
   (sim_k2 = a^2 + b^2).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending
   (review.status in docs/claim-statements.json).
   ========================================================================== *)

From Stdlib Require Import Reals QArith Qreals.
From NTS.Proofs Require Import Distance CurveGeometry CurveRingSimple.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Similarities of the plane and the control-point image of an arc.       *)
(* -------------------------------------------------------------------------- *)

Record Sim2 : Type := mkSim2 {
  sim_a : R; sim_b : R; sim_tx : R; sim_ty : R; sim_refl : bool }.

Definition sim_apply (m : Sim2) (p : Point) : Point :=
  if sim_refl m
  then mkPoint (sim_a m * px p + sim_b m * py p + sim_tx m)
               (sim_b m * px p - sim_a m * py p + sim_ty m)
  else mkPoint (sim_a m * px p - sim_b m * py p + sim_tx m)
               (sim_b m * px p + sim_a m * py p + sim_ty m).

Definition sim_k2 (m : Sim2) : R := sim_a m * sim_a m + sim_b m * sim_b m.

(* What GEOSGeom_transformXY-style code does to an arc: move the three
   control points independently. *)
Definition map_arc (f : Point -> Point) (a : CircularArc) : CircularArc :=
  mkCircularArc (f (arc_start a)) (f (arc_mid a)) (f (arc_end a)).

(* -------------------------------------------------------------------------- *)
(* §2  Rational affine maps and the similarity test an adapter would run.     *)
(*     x' = m11 x + m12 y + tx,  y' = m21 x + m22 y + ty.                      *)
(* -------------------------------------------------------------------------- *)

Record QAff : Type := mkQAff {
  qm11 : Q; qm12 : Q; qm21 : Q; qm22 : Q; qtx : Q; qty : Q }.

Definition qaff_R (m : QAff) (p : Point) : Point :=
  mkPoint (Q2R (qm11 m) * px p + Q2R (qm12 m) * py p + Q2R (qtx m))
          (Q2R (qm21 m) * px p + Q2R (qm22 m) * py p + Q2R (qty m)).

Definition is_similarity_q (m : QAff) : Prop :=
  (((qm11 m == qm22 m) /\ (qm12 m == - qm21 m))
   \/ ((qm11 m == - qm22 m) /\ (qm12 m == qm21 m)))%Q
  /\ ~ (qm11 m * qm11 m + qm21 m * qm21 m == 0)%Q.

(* -------------------------------------------------------------------------- *)
(* §3  The statements.                                                        *)
(* -------------------------------------------------------------------------- *)

Definition sim_dist_sq_stmt : Prop :=
  forall m p q,
    dist_sq (sim_apply m p) (sim_apply m q) = sim_k2 m * dist_sq p q.

Definition sim_valid_arc_stmt : Prop :=
  forall m a, sim_k2 m <> 0 -> valid_arc a ->
    valid_arc (map_arc (sim_apply m) a).

Definition sim_arc_center_stmt : Prop :=
  forall m a, sim_k2 m <> 0 -> valid_arc a ->
    arc_center (map_arc (sim_apply m) a) = sim_apply m (arc_center a).

Definition sim_arc_radius_stmt : Prop :=
  forall m a, sim_k2 m <> 0 -> valid_arc a ->
    arc_radius (map_arc (sim_apply m) a) = sqrt (sim_k2 m) * arc_radius a.

Definition sim_on_arc_stmt : Prop :=
  forall m a X, sim_k2 m <> 0 ->
    (on_arc a X <-> on_arc (map_arc (sim_apply m) a) (sim_apply m X)).

(* main: a similarity maps the arc through three control points onto the arc
   through their images (centre, radius and membership all transported). *)
Definition claim : Prop :=
  sim_dist_sq_stmt /\ sim_valid_arc_stmt /\ sim_arc_center_stmt
  /\ sim_arc_radius_stmt /\ sim_on_arc_stmt.

(* supporting: a rational affine map that passes `is_similarity_q` is exact on
   arcs when applied to the three control points. *)
Definition supporting : Prop :=
  forall m, is_similarity_q m ->
    forall a X, on_arc a X <-> on_arc (map_arc (qaff_R m) a) (qaff_R m X).

(* witness: some rational affine map that fails `is_similarity_q` is NOT exact
   on the control points of some valid arc (one sample, not a converse). *)
Definition witness : Prop :=
  exists m a X, ~ is_similarity_q m /\ valid_arc a /\ on_arc a X /\
    ~ on_arc (map_arc (qaff_R m) a) (qaff_R m X).
