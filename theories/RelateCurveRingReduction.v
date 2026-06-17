(* ============================================================================
   NetTopologySuite.Proofs.RelateCurveRingReduction
   ----------------------------------------------------------------------------
   Issue #67 (curve→matrix soundness): the GENERAL arc/compound-ring reduction.

   The per-shape results (`point_in_ring_chord_rect_iff`,
   `RelateCurveArcSegment.point_in_ring_arc_seg_iff`,
   `RelateCurveVesica.point_in_ring_vesica_iff`) each strip the degenerate
   `(v, v)` join edges of one linearised curve ring by hand.  This file proves
   the reduction ONCE, for an arbitrary adjacent CurveRing — chord-only,
   all-arc (CIRCULARSTRING), or mixed (COMPOUNDCURVE), uniformly.

   `inscribed_ring r n` keeps each segment's chord approximation but DROPS the
   trailing endpoint of every non-final segment (the one adjacency duplicates as
   the next segment's start).  The headline

     point_in_ring_chord_approx_eq_inscribed :
       curve_ring_adjacent r ->
       (point_in_ring p (chord_approx_ring r n)
          <-> point_in_ring p (inscribed_ring r n))

   says the linearised ring and the inscribed control polygon have the SAME
   point-in-ring.  Proof: a prefix-generalised induction on the segment list,
   discharging exactly one `RayParityDegenerate.point_in_ring_dup_at` per join.
   The geometry-level corollary `point_in_simple_curve_geometry_iff_inscribed`
   transports it through the `to_geometry` point-set bridge for a single
   no-holes curve polygon — the general form of the S12b transport the rectangle,
   lens, and vesica each did by hand.

   All `Qed`; the reduction is at the standard classical-reals footprint (only
   `point_in_ring` decidability), no new `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Setoid.
From NTS.Proofs Require Import Distance Overlay CurveGeometry CurveLinearise
  RayParityDegenerate.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The inscribed control polygon of a curve ring.                          *)
(*                                                                            *)
(* Final segment: keep its whole chord approximation (its end is the ring's    *)
(* closing vertex).  Every earlier segment: drop its trailing end (adjacency   *)
(* repeats it as the next segment's start).                                     *)
(* -------------------------------------------------------------------------- *)

Fixpoint inscribed_ring (r : CurveRing) (n : nat) : Ring :=
  match r with
  | [] => []
  | s :: rest =>
      match rest with
      | [] => chord_approx_segment s n
      | _ :: _ => removelast (chord_approx_segment s n) ++ inscribed_ring rest n
      end
  end.

(* Each segment's chord approximation is its `removelast` plus its end point. *)
Lemma chord_approx_segment_removelast :
  forall s n,
    chord_approx_segment s n
    = removelast (chord_approx_segment s n) ++ [curve_segment_end s].
Proof.
  intros s n. destruct (chord_approx_segment_shape s n) as [M HM].
  rewrite HM.
  replace (curve_segment_start s :: (M ++ [curve_segment_end s]))
     with ((curve_segment_start s :: M) ++ [curve_segment_end s]) by reflexivity.
  rewrite removelast_last. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The prefix-generalised reduction (the induction).                       *)
(*                                                                            *)
(* Generalising over an arbitrary leading `P` lets the inductive step swap a   *)
(* suffix: peel the first segment, strip its join duplicate with the second    *)
(* via `point_in_ring_dup_at`, then apply the IH to the tail with the enlarged *)
(* prefix `P ++ removelast (chord_approx_segment s1 n)`.                        *)
(* -------------------------------------------------------------------------- *)

Lemma point_in_ring_chord_approx_inscribed_prefix :
  forall (r : CurveRing) (n : nat) (p : Point) (P : Ring),
    curve_ring_adjacent r ->
    (point_in_ring p (P ++ chord_approx_ring r n)
     <-> point_in_ring p (P ++ inscribed_ring r n)).
Proof.
  induction r as [| s1 rest IH]; intros n p P Hadj.
  - (* empty ring *)
    simpl. reflexivity.
  - destruct rest as [| s2 rest'].
    + (* single segment: chord_approx_ring [s1] = chord_approx_segment s1 = inscribed *)
      replace (chord_approx_ring [s1] n) with (chord_approx_segment s1 n)
        by (simpl; rewrite app_nil_r; reflexivity).
      reflexivity.
    + (* >= 2 segments: peel s1, strip its join with s2, recurse on s2::rest' *)
      destruct Hadj as [Hend Hadj'].
      destruct (chord_approx_ring_shape rest' s2 n) as [M2 HM2].
      set (TL := M2 ++ [curve_segment_end (List.last (s2 :: rest') s2)]) in HM2.
      (* the linearised ring, rewritten into a leading-prefix + adjacent-dup form *)
      assert (Eq1 : P ++ chord_approx_ring (s1 :: s2 :: rest') n
                  = (P ++ removelast (chord_approx_segment s1 n))
                    ++ curve_segment_end s1 :: curve_segment_end s1 :: TL).
      { change (chord_approx_ring (s1 :: s2 :: rest') n)
          with (chord_approx_segment s1 n ++ chord_approx_ring (s2 :: rest') n).
        rewrite (chord_approx_segment_removelast s1 n) at 1.
        rewrite HM2, <- Hend.
        rewrite <- !app_assoc. cbn [app]. reflexivity. }
      rewrite Eq1.
      (* strip the single (end s1, end s1) join edge *)
      rewrite (point_in_ring_dup_at p
                 (P ++ removelast (chord_approx_segment s1 n))
                 (curve_segment_end s1) TL).
      (* re-fold end s1 :: TL into chord_approx_ring (s2 :: rest') n *)
      assert (Eq3 : (P ++ removelast (chord_approx_segment s1 n))
                       ++ curve_segment_end s1 :: TL
                  = (P ++ removelast (chord_approx_segment s1 n))
                       ++ chord_approx_ring (s2 :: rest') n).
      { rewrite HM2, Hend. reflexivity. }
      rewrite Eq3.
      (* unfold the inscribed ring of s1::s2::rest' on the RHS *)
      assert (Eq4 : P ++ inscribed_ring (s1 :: s2 :: rest') n
                  = (P ++ removelast (chord_approx_segment s1 n))
                       ++ inscribed_ring (s2 :: rest') n).
      { cbn [inscribed_ring]. rewrite app_assoc. reflexivity. }
      rewrite Eq4.
      (* IH on the tail with the enlarged prefix *)
      exact (IH n p (P ++ removelast (chord_approx_segment s1 n)) Hadj').
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The headline reduction (closed/adjacent ring, empty prefix).            *)
(* -------------------------------------------------------------------------- *)

Theorem point_in_ring_chord_approx_eq_inscribed :
  forall (r : CurveRing) (n : nat) (p : Point),
    curve_ring_adjacent r ->
    (point_in_ring p (chord_approx_ring r n)
     <-> point_in_ring p (inscribed_ring r n)).
Proof.
  intros r n p Hadj.
  exact (point_in_ring_chord_approx_inscribed_prefix r n p [] Hadj).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Geometry-level transport for a single no-holes curve polygon.           *)
(* -------------------------------------------------------------------------- *)

Definition simple_curve_geometry (r : CurveRing) : CurveGeometry :=
  [ {| curve_outer := r; curve_holes := [] |} ].

Theorem point_in_simple_curve_geometry_iff_inscribed :
  forall (r : CurveRing) (n : nat) (p : Point),
    curve_ring_adjacent r ->
    (point_set (to_geometry (simple_curve_geometry r) n) p
     <-> point_in_ring p (inscribed_ring r n)).
Proof.
  intros r n p Hadj.
  unfold point_set, to_geometry, simple_curve_geometry.
  cbn [map curve_outer curve_holes].
  split.
  - intros [poly [Hin Hpip]]. cbn [In] in Hin.
    destruct Hin as [Heq | Hfalse]; [ subst poly | contradiction ].
    unfold point_in_polygon in Hpip. cbn [outer_ring hole_rings] in Hpip.
    destruct Hpip as [Hring _].
    apply (proj1 (point_in_ring_chord_approx_eq_inscribed r n p Hadj)). exact Hring.
  - intro H.
    exists (mkPolygon (chord_approx_ring r n) []).
    cbn [In]. split; [ left; reflexivity | ].
    unfold point_in_polygon. cbn [outer_ring hole_rings]. split.
    + apply (proj2 (point_in_ring_chord_approx_eq_inscribed r n p Hadj)). exact H.
    + intros h Hin. destruct Hin.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  The inscribed control polygon is itself a closed Phase-3 ring.           *)
(*                                                                            *)
(* `chord_approx_ring` carries a duplicated vertex at every join; the inscribed *)
(* control polygon is the DEDUPLICATED boundary.  For a closed adjacent curve   *)
(* ring it is again a `ring_closed` Phase-3 ring — a cleaner first-class ring   *)
(* than the linearisation, the form for plugging linearised curves into the     *)
(* overlay / extract_rings machinery.  Same shape/closed argument as            *)
(* `CurveLinearise.chord_approx_ring_shape` / `chord_approx_ring_closed`.       *)
(* -------------------------------------------------------------------------- *)

Lemma inscribed_ring_shape :
  forall (rest : list CurveSegment) (s : CurveSegment) (n : nat),
    exists M, inscribed_ring (s :: rest) n
              = curve_segment_start s
                :: (M ++ [curve_segment_end (List.last (s :: rest) s)]).
Proof.
  induction rest as [| s2 rest IH]; intros s n.
  - (* single segment: inscribed_ring [s] n = chord_approx_segment s n *)
    destruct (chord_approx_segment_shape s n) as [Ms HMs].
    exists Ms.
    replace (inscribed_ring [s] n) with (chord_approx_segment s n) by reflexivity.
    replace (curve_segment_end (List.last [s] s)) with (curve_segment_end s)
      by reflexivity.
    exact HMs.
  - (* >= 2 segments: removelast(cas s) ++ inscribed (s2::rest) *)
    destruct (chord_approx_segment_shape s n) as [Ms HMs].
    destruct (IH s2 n) as [M' HM'].
    assert (Hrl : removelast (chord_approx_segment s n) = curve_segment_start s :: Ms).
    { rewrite HMs.
      replace (curve_segment_start s :: (Ms ++ [curve_segment_end s]))
        with ((curve_segment_start s :: Ms) ++ [curve_segment_end s]) by reflexivity.
      rewrite removelast_last. reflexivity. }
    exists (Ms ++ curve_segment_start s2 :: M').
    change (inscribed_ring (s :: s2 :: rest) n)
      with (removelast (chord_approx_segment s n) ++ inscribed_ring (s2 :: rest) n).
    rewrite Hrl, HM'.
    replace (curve_segment_end (List.last (s :: s2 :: rest) s))
       with (curve_segment_end (List.last (s2 :: rest) s2)).
    2:{ f_equal. rewrite (last_cons_nonnil s (s2 :: rest) s) by discriminate.
        apply last_default_irrel. discriminate. }
    rewrite <- app_comm_cons. f_equal.
    rewrite <- !app_assoc. cbn [app]. reflexivity.
Qed.

Theorem inscribed_ring_closed :
  forall (r : CurveRing) (n : nat),
    curve_ring_closed r -> ring_closed (inscribed_ring r n).
Proof.
  intros [| s rest] n Hcl.
  - simpl in Hcl. contradiction.
  - unfold curve_ring_closed in Hcl.
    destruct (inscribed_ring_shape rest s n) as [M HM].
    unfold ring_closed. exists (curve_segment_start s), M.
    rewrite HM, Hcl. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  With-holes transport: a full curve polygon (outer + holes).             *)
(*                                                                            *)
(* `to_geometry` maps `chord_approx_ring` over the outer ring AND every hole,  *)
(* so a curve polygon's point-set membership is: in the inscribed outer ring    *)
(* and outside every inscribed hole ring.  This lifts the no-holes transport    *)
(* (§4) to the full SQL/MM CurvePolygon, the first curve->matrix membership      *)
(* result that admits holes.                                                    *)
(* -------------------------------------------------------------------------- *)

Definition curve_polygon_adjacent (cp : CurvePolygon) : Prop :=
  curve_ring_adjacent (curve_outer cp)
  /\ Forall curve_ring_adjacent (curve_holes cp).

(* The hole quantifier transports pointwise: outside every linearised hole iff
   outside every inscribed hole. *)
Lemma point_outside_holes_iff_inscribed :
  forall (holes : list CurveRing) (n : nat) (p : Point),
    Forall curve_ring_adjacent holes ->
    ((forall h, In h (map (fun h0 => chord_approx_ring h0 n) holes)
                -> ~ point_in_ring p h)
     <-> (forall h0, In h0 holes -> ~ point_in_ring p (inscribed_ring h0 n))).
Proof.
  intros holes n p Hadj. rewrite Forall_forall in Hadj. split.
  - intros H h0 Hin0 Hpir_ins.
    apply (H (chord_approx_ring h0 n)
             (in_map (fun h0 => chord_approx_ring h0 n) holes h0 Hin0)).
    apply (proj2 (point_in_ring_chord_approx_eq_inscribed h0 n p (Hadj h0 Hin0))).
    exact Hpir_ins.
  - intros H h Hin Hpir_ch.
    apply in_map_iff in Hin. destruct Hin as [h0 [Heq Hin0]]. subst h.
    apply (H h0 Hin0).
    apply (proj1 (point_in_ring_chord_approx_eq_inscribed h0 n p (Hadj h0 Hin0))).
    exact Hpir_ch.
Qed.

Theorem point_in_curve_polygon_geometry_iff_inscribed :
  forall (cp : CurvePolygon) (n : nat) (p : Point),
    curve_polygon_adjacent cp ->
    (point_set (to_geometry [cp] n) p
     <-> point_in_ring p (inscribed_ring (curve_outer cp) n)
         /\ (forall h0, In h0 (curve_holes cp)
                        -> ~ point_in_ring p (inscribed_ring h0 n))).
Proof.
  intros cp n p [Houter Hholes].
  unfold point_set, to_geometry. cbn [map].
  split.
  - intros [poly [Hin Hpip]]. cbn [In] in Hin.
    destruct Hin as [Heq | Hf]; [ subst poly | contradiction ].
    unfold point_in_polygon in Hpip. cbn [outer_ring hole_rings] in Hpip.
    destruct Hpip as [Hout Hin_holes]. split.
    + apply (proj1 (point_in_ring_chord_approx_eq_inscribed
                      (curve_outer cp) n p Houter)). exact Hout.
    + apply (proj1 (point_outside_holes_iff_inscribed
                      (curve_holes cp) n p Hholes)). exact Hin_holes.
  - intros [Hout Hin_holes].
    exists (mkPolygon (chord_approx_ring (curve_outer cp) n)
                      (map (fun h => chord_approx_ring h n) (curve_holes cp))).
    cbn [In]. split; [ left; reflexivity | ].
    unfold point_in_polygon. cbn [outer_ring hole_rings]. split.
    + apply (proj2 (point_in_ring_chord_approx_eq_inscribed
                      (curve_outer cp) n p Houter)). exact Hout.
    + apply (proj2 (point_outside_holes_iff_inscribed
                      (curve_holes cp) n p Hholes)). exact Hin_holes.
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions point_in_ring_chord_approx_eq_inscribed.
Print Assumptions point_in_simple_curve_geometry_iff_inscribed.
Print Assumptions inscribed_ring_closed.
Print Assumptions point_in_curve_polygon_geometry_iff_inscribed.
