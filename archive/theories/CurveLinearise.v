(* ============================================================================
   NetTopologySuite.Proofs.CurveLinearise
   ----------------------------------------------------------------------------
   Structural faithfulness of the SQL/MM curve -> Phase-3 linearisation bridge
   (`CurveGeometry.to_geometry` / `chord_approx_ring`), for full
   CIRCULARSTRING and COMPOUNDCURVE support.

   `CurveRing := list CurveSegment` (CurveGeometry.v) models a SQL/MM
   COMPOUNDCURVE -- a chain of `CSChord` (line) and `CSArc` (circular)
   segments; the all-arc case is a CIRCULARSTRING.  `chord_approx_ring`
   flattens it to a Phase-3 `Ring`, and `to_geometry` packages a whole
   `CurveGeometry` as a Phase-3 `Geometry`.

   Nothing yet proves this bridge produces WELL-FORMED Phase-3 rings.  This
   file closes the combinatorial heart of that: a valid (adjacent + closed)
   curve ring -- circular OR compound, uniformly -- linearises to a
   `ring_closed` Phase-3 ring (`chord_approx_ring_closed`), and hence every
   outer ring and hole of `to_geometry cg n` is closed for a valid `cg`
   (`to_geometry_outer_ring_closed`, `to_geometry_hole_ring_closed`).  This is
   the `ring_closed` conjunct of `valid_polygon` for the linearised curve
   geometry -- the curve analogue of RingExtract's `face_walk_closed`, and the
   structural prerequisite for plugging linearised curves into the
   `extract_rings_valid` / overlay machinery.

   Pure-R; only list + curve structure (no atan / Flocq / analytics).
   Three-axiom footprint.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals List.
From NTS.Proofs Require Import Distance Overlay CurveGeometry.
Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §0  Small list helpers about `last`.                                       *)
(* -------------------------------------------------------------------------- *)

Lemma last_cons_nonnil :
  forall {A : Type} (a : A) (l : list A) (d : A),
    l <> [] -> last (a :: l) d = last l d.
Proof. intros A a l d Hl. destruct l; [ contradiction | reflexivity ]. Qed.

Lemma last_default_irrel :
  forall {A : Type} (l : list A) (d1 d2 : A),
    l <> [] -> last l d1 = last l d2.
Proof.
  intros A l. induction l as [|a l IH]; intros d1 d2 H.
  - contradiction.
  - destruct l as [|b l'].
    + reflexivity.
    + rewrite !last_cons_nonnil by discriminate. apply IH. discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* §1  Per-segment shape: chord_approx_segment = start :: (M ++ [end]).       *)
(* -------------------------------------------------------------------------- *)

(* Each segment's chord approximation begins at the segment start and ends at
   the segment end (CSChord: [p;q]; CSArc: [start;mid;end]). *)
Lemma chord_approx_segment_shape :
  forall (s : CurveSegment) (n : nat),
    exists M, chord_approx_segment s n
              = curve_segment_start s :: (M ++ [curve_segment_end s]).
Proof.
  intros [p q | a] n.
  - exists []. reflexivity.
  - exists [arc_mid a]. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Whole-ring shape: chord_approx_ring = start_1 :: (M ++ [end_last]).    *)
(* -------------------------------------------------------------------------- *)

Lemma chord_approx_ring_shape :
  forall (rest : list CurveSegment) (s : CurveSegment) (n : nat),
    exists M, chord_approx_ring (s :: rest) n
              = curve_segment_start s
                :: (M ++ [curve_segment_end (List.last (s :: rest) s)]).
Proof.
  induction rest as [|s2 rest IH]; intros s n.
  - destruct (chord_approx_segment_shape s n) as [Ms HMs].
    exists Ms.
    change (chord_approx_ring [s] n)
      with (chord_approx_segment s n ++ chord_approx_ring [] n).
    simpl (chord_approx_ring [] n). rewrite app_nil_r, HMs. reflexivity.
  - destruct (chord_approx_segment_shape s n) as [Ms HMs].
    destruct (IH s2 n) as [M' HM'].
    exists (Ms ++ curve_segment_end s :: curve_segment_start s2 :: M').
    change (chord_approx_ring (s :: s2 :: rest) n)
      with (chord_approx_segment s n ++ chord_approx_ring (s2 :: rest) n).
    rewrite HMs, HM'.
    replace (curve_segment_end (List.last (s :: s2 :: rest) s))
       with (curve_segment_end (List.last (s2 :: rest) s2)).
    2:{ f_equal. rewrite (last_cons_nonnil s (s2 :: rest) s) by discriminate.
        apply last_default_irrel. discriminate. }
    rewrite <- app_comm_cons. f_equal.
    rewrite <- !app_assoc. cbn [app]. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Closure of the linearised ring (circularstring OR compoundcurve).      *)
(* -------------------------------------------------------------------------- *)

(* A closed curve ring -- all arcs (CIRCULARSTRING) or mixed (COMPOUNDCURVE),
   handled uniformly -- linearises to a `ring_closed` Phase-3 ring. *)
Theorem chord_approx_ring_closed :
  forall (r : CurveRing) (n : nat),
    curve_ring_closed r -> ring_closed (chord_approx_ring r n).
Proof.
  intros [|s rest] n Hcl.
  - simpl in Hcl. contradiction.
  - unfold curve_ring_closed in Hcl.
    destruct (chord_approx_ring_shape rest s n) as [M HM].
    unfold ring_closed. exists (curve_segment_start s), M.
    rewrite HM, Hcl. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Lifting to to_geometry: outer rings and holes are closed.              *)
(* -------------------------------------------------------------------------- *)

(* For a valid curve geometry, every linearised outer ring is closed. *)
Theorem to_geometry_outer_ring_closed :
  forall (cg : CurveGeometry) (n : nat) (cp : CurvePolygon),
    valid_curve_geometry cg -> In cp cg ->
    ring_closed (chord_approx_ring (curve_outer cp) n).
Proof.
  intros cg n cp Hcg Hin.
  unfold valid_curve_geometry in Hcg.
  rewrite Forall_forall in Hcg.
  destruct (Hcg cp Hin) as [[_ [_ Hclosed]] _].
  apply chord_approx_ring_closed. exact Hclosed.
Qed.

(* ... and every linearised hole ring is closed. *)
Theorem to_geometry_hole_ring_closed :
  forall (cg : CurveGeometry) (n : nat) (cp : CurvePolygon) (h : CurveRing),
    valid_curve_geometry cg -> In cp cg -> In h (curve_holes cp) ->
    ring_closed (chord_approx_ring h n).
Proof.
  intros cg n cp h Hcg Hin Hinh.
  unfold valid_curve_geometry in Hcg.
  rewrite Forall_forall in Hcg.
  destruct (Hcg cp Hin) as [_ Hholes].
  rewrite Forall_forall in Hholes.
  destruct (Hholes h Hinh) as [_ [_ Hclosed]].
  apply chord_approx_ring_closed. exact Hclosed.
Qed.

Print Assumptions chord_approx_ring_closed.
Print Assumptions to_geometry_outer_ring_closed.
