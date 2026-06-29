(* ============================================================================
   NetTopologySuite.Proofs.ClothoidBufferAssembly
   ----------------------------------------------------------------------------
   GLOBAL CLOTHOID OFFSET ASSEMBLY SOUNDNESS (adjacency level, whole ring).

   PR #304 (ClothoidOffsetContact.clothoid_clothoid_offset_contact_sound) proved
   the PAIRWISE fact: two consecutive G1-joined clothoid offset osculating arcs
   meet ONLY at their shared join.  This file LIFTS that local result to a whole
   closed clothoid arc-ring: every consecutive offset-arc pair -- the interior
   pairs AND the wrap-around (last -> first) pair -- meets only at its join, and
   the offset ring is itself a valid curve ring.

   The headline `clothoid_buffer_assembly_sound` packages three facts about the
   offset of a valid, G1-consistent, curvature-bounded, distinct-adjacent-radii
   clothoid arc-ring:
     (1) valid_curve_ring (curve_ring_offset r d)   -- reuses clothoid_ring_offset_valid
     (2) ring_adjacent_offset_clean r d             -- interior joins all clean (NEW)
     (3) ring_closing_offset_clean  r d             -- the wrap join clean        (NEW)

   The new content is the structural induction lifting the pairwise theorem over
   the ring, mirroring CurveRingOffset.curve_ring_offset_adjacent (interior) and
   curve_ring_offset_closed (the last/first wrap via last_map / last_in).

   Scope (honest): adjacency-level global assembly -- every join (interior and
   closing) is a single clean contact.  Full NON-adjacent ring simplicity
   (CurveRingSimple.curve_ring_simple: non-consecutive segments meet NOWHERE)
   needs a global Jordan/winding argument the corpus does not have; it remains
   the noder's job (raw offset is not simple -- RingSimple.bowtie) and is NOT
   claimed here.  This is parameter-interval arc chains, not full Fresnel
   materialisation.

   Pure-R; classical-reals trio only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
Import ListNotations.
From NTS.Proofs Require Import CurveGeometry CurveRingOffset ArcOffsetThreePoint
  ArcOrient ClothoidOffsetContact ClothoidBufferBridge.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Per-pair cleanliness predicate.                                        *)
(*                                                                            *)
(* For an arc-arc pair, the conclusion of clothoid_clothoid_offset_contact_   *)
(* sound verbatim (stated on arc_offset_arc, so the theorem `exact`s with no  *)
(* rewriting); any pair involving a chord is vacuously clean.                 *)
(* -------------------------------------------------------------------------- *)
Definition pair_offset_clean (s1 s2 : CurveSegment) (d : R) : Prop :=
  match s1, s2 with
  | CSArc a1, CSArc a2 =>
      forall X,
        inCircle_R (arc_start (arc_offset_arc a1 d)) (arc_mid (arc_offset_arc a1 d))
                   (arc_end (arc_offset_arc a1 d)) X = 0 ->
        inCircle_R (arc_start (arc_offset_arc a2 d)) (arc_mid (arc_offset_arc a2 d))
                   (arc_end (arc_offset_arc a2 d)) X = 0 ->
        X = arc_end (arc_offset_arc a1 d)
  | _, _ => True
  end.

(* The pairwise theorem, repackaged on the per-pair predicate. *)
Lemma pair_offset_clean_arcs : forall a1 a2 d,
  valid_arc a1 -> valid_arc a2 ->
  arc_end a1 = arc_start a2 ->
  join_normals_consistent a1 a2 ->
  arc_radius a1 <> arc_radius a2 ->
  - arc_radius a1 < d -> - arc_radius a2 < d ->
  pair_offset_clean (CSArc a1) (CSArc a2) d.
Proof.
  intros a1 a2 d Hv1 Hv2 HP Hn Hrne Hd1 Hd2.
  exact (clothoid_clothoid_offset_contact_sound a1 a2 d Hv1 Hv2 HP Hn Hrne Hd1 Hd2).
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Ring-level cleanliness: interior fixpoint + closing-wrap definition,   *)
(* mirroring ring_joins_normals_consistent / ring_closing_join_normals_*.     *)
(* -------------------------------------------------------------------------- *)
Fixpoint ring_adjacent_offset_clean (r : CurveRing) (d : R) : Prop :=
  match r with
  | [] => True
  | s1 :: rest =>
      match rest with
      | [] => True
      | s2 :: _ => pair_offset_clean s1 s2 d /\ ring_adjacent_offset_clean rest d
      end
  end.

Definition ring_closing_offset_clean (r : CurveRing) (d : R) : Prop :=
  match r with
  | [] => True
  | s :: _ => pair_offset_clean (last r s) s d
  end.

(* -------------------------------------------------------------------------- *)
(* §3  Distinct consecutive radii (the generic clothoid hypothesis): the      *)
(* curvature strictly varies along a spiral, so adjacent osculating radii      *)
(* differ.  Required by clothoid_clothoid_offset_contact_sound (r1 <> r2).    *)
(* -------------------------------------------------------------------------- *)
Fixpoint ring_consecutive_radii_distinct (r : CurveRing) : Prop :=
  match r with
  | [] => True
  | s1 :: rest =>
      match rest with
      | [] => True
      | s2 :: _ =>
          match s1, s2 with
          | CSArc a1, CSArc a2 => arc_radius a1 <> arc_radius a2
          | _, _ => True
          end /\ ring_consecutive_radii_distinct rest
      end
  end.

Definition ring_closing_radii_distinct (r : CurveRing) : Prop :=
  match r with
  | [] => True
  | s :: _ =>
      match last r s, s with
      | CSArc a1, CSArc a2 => arc_radius a1 <> arc_radius a2
      | _, _ => True
      end
  end.

(* -------------------------------------------------------------------------- *)
(* §4  Normal-field equality -> join_normals_consistent (the existing iff,    *)
(* backward direction).                                                       *)
(* -------------------------------------------------------------------------- *)
Lemma norm_eq_join_consistent : forall a1 a2,
  arc_end a1 = arc_start a2 ->
  segment_norm_end (CSArc a1) = segment_norm_start (CSArc a2) ->
  join_normals_consistent a1 a2.
Proof.
  intros a1 a2 HP HN.
  exact (proj2 (join_normals_consistent_norm_iff a1 a2 HP) HN).
Qed.

(* All-arcs predicate (False on chords lets a chord branch close by `destruct`). *)
Definition ring_all_arcs (r : CurveRing) : Prop :=
  Forall (fun s => match s with CSChord _ _ => False | CSArc _ => True end) r.

Definition ring_radius_lb (r : CurveRing) (rmin : R) : Prop :=
  Forall (fun s => match s with
                   | CSChord _ _ => True
                   | CSArc a => rmin <= arc_radius a
                   end) r.

(* -------------------------------------------------------------------------- *)
(* §5  Interior lifting: every consecutive offset-arc pair is clean.          *)
(* Structural induction copying CurveRingOffset.curve_ring_offset_adjacent.   *)
(* -------------------------------------------------------------------------- *)
Lemma ring_adjacent_offset_clean_intro : forall r k0 k1 d,
  0 < k0 -> 0 < k1 ->
  ring_all_arcs r ->
  curve_ring_arcs_valid r ->
  curve_ring_adjacent r ->
  ring_joins_normals_consistent r ->
  ring_radius_lb r (1 / Rmax k0 k1) ->
  ring_consecutive_radii_distinct r ->
  - (1 / Rmax k0 k1) < d ->
  ring_adjacent_offset_clean r d.
Proof.
  intros r k0 k1 d Hk0 Hk1.
  assert (Hrmin : 0 < 1 / Rmax k0 k1)
    by (apply Rdiv_lt_0_compat; [ lra | pose proof (Rmax_l k0 k1); lra ]).
  induction r as [| s1 rest IH]; intros Harcs Hav Hadj HG1 Hlb Hdist Hd.
  - exact I.
  - destruct rest as [| s2 rest'].
    + exact I.
    + destruct Hadj  as [Hj   Hadj' ].
      destruct HG1   as [Hn   HG1'  ].
      destruct Hdist as [Hrad Hdist'].
      split.
      * (* head pair clean *)
        destruct s1 as [p1 q1 | a1]; [ destruct (Forall_inv Harcs) | ].
        destruct s2 as [p2 q2 | a2];
          [ destruct (Forall_inv (Forall_inv_tail Harcs)) | ].
        cbn [curve_segment_end curve_segment_start] in Hj.
        assert (Hv1 : valid_arc a1) by exact (Forall_inv Hav).
        assert (Hv2 : valid_arc a2) by exact (Forall_inv (Forall_inv_tail Hav)).
        assert (Hjn : join_normals_consistent a1 a2)
          by (apply norm_eq_join_consistent; [ exact Hj | exact Hn ]).
        assert (Hr1 : 1 / Rmax k0 k1 <= arc_radius a1) by exact (Forall_inv Hlb).
        assert (Hr2 : 1 / Rmax k0 k1 <= arc_radius a2)
          by exact (Forall_inv (Forall_inv_tail Hlb)).
        apply pair_offset_clean_arcs; try assumption; lra.
      * (* recurse on rest = s2 :: rest' *)
        apply IH;
          [ exact (Forall_inv_tail Harcs)
          | exact (Forall_inv_tail Hav)
          | exact Hadj'
          | exact HG1'
          | exact (Forall_inv_tail Hlb)
          | exact Hdist'
          | exact Hd ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Closing-wrap lifting: the (last, first) offset-arc pair is clean.      *)
(* Non-inductive, copying CurveRingOffset.curve_ring_offset_closed.           *)
(* -------------------------------------------------------------------------- *)
Lemma ring_closing_offset_clean_intro : forall r k0 k1 d,
  0 < k0 -> 0 < k1 ->
  ring_all_arcs r ->
  curve_ring_arcs_valid r ->
  curve_ring_closed r ->
  ring_closing_join_normals_consistent r ->
  ring_radius_lb r (1 / Rmax k0 k1) ->
  ring_closing_radii_distinct r ->
  - (1 / Rmax k0 k1) < d ->
  ring_closing_offset_clean r d.
Proof.
  intros r k0 k1 d Hk0 Hk1.
  assert (Hrmin : 0 < 1 / Rmax k0 k1)
    by (apply Rdiv_lt_0_compat; [ lra | pose proof (Rmax_l k0 k1); lra ]).
  destruct r as [| s rest]; intros Harcs Hav Hcl HG1c Hlb Hdist Hd.
  - exact I.
  - cbn [ring_closing_offset_clean] in *.
    cbn [curve_ring_closed] in Hcl.
    cbn [ring_closing_join_normals_consistent] in HG1c.
    cbn [ring_closing_radii_distinct] in Hdist.
    (* facts about the last segment, via In + Forall_forall *)
    assert (Hin : In (last (s :: rest) s) (s :: rest))
      by (apply last_in; discriminate).
    pose proof (proj1 (Forall_forall _ _) Harcs _ Hin) as Hla.
    pose proof (proj1 (Forall_forall _ _) Hav  _ Hin) as Hvl.
    pose proof (proj1 (Forall_forall _ _) Hlb  _ Hin) as Hrl.
    destruct (last (s :: rest) s) as [pl ql | a1] eqn:Hlast;
      [ destruct Hla | ].
    destruct s as [ps qs | a2]; [ destruct (Forall_inv Harcs) | ].
    cbn [curve_segment_end curve_segment_start] in Hcl.
    assert (Hv2 : valid_arc a2) by exact (Forall_inv Hav).
    assert (Hr2 : 1 / Rmax k0 k1 <= arc_radius a2) by exact (Forall_inv Hlb).
    assert (Hjn : join_normals_consistent a1 a2)
      by (apply norm_eq_join_consistent; [ exact Hcl | exact HG1c ]).
    apply pair_offset_clean_arcs; try assumption; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  Headline: the offset of a clothoid arc-ring is a VALID ring whose every *)
(* join -- interior and closing -- is a single clean contact.                 *)
(* -------------------------------------------------------------------------- *)
Theorem clothoid_buffer_assembly_sound : forall (r : CurveRing) (k0 k1 d : R),
  0 < k0 -> 0 < k1 ->
  ring_all_arcs r ->
  valid_curve_ring r ->
  ring_joins_normals_consistent r ->
  ring_closing_join_normals_consistent r ->
  ring_radius_lb r (1 / Rmax k0 k1) ->
  ring_consecutive_radii_distinct r ->
  ring_closing_radii_distinct r ->
  - (1 / Rmax k0 k1) < d ->
  valid_curve_ring (curve_ring_offset r d) /\
  ring_adjacent_offset_clean r d /\
  ring_closing_offset_clean r d.
Proof.
  intros r k0 k1 d Hk0 Hk1 Harcs Hvalid HG1 HG1c Hlb Hdist Hcdist Hd.
  destruct Hvalid as [Hav [Hadj Hclosed]].
  split; [ | split ].
  - apply (clothoid_ring_offset_valid r k0 k1 d); try assumption.
    split; [ exact Hav | split; [ exact Hadj | exact Hclosed ] ].
  - apply (ring_adjacent_offset_clean_intro r k0 k1 d); assumption.
  - apply (ring_closing_offset_clean_intro r k0 k1 d); assumption.
Qed.

Print Assumptions pair_offset_clean_arcs.
Print Assumptions norm_eq_join_consistent.
Print Assumptions ring_adjacent_offset_clean_intro.
Print Assumptions ring_closing_offset_clean_intro.
Print Assumptions clothoid_buffer_assembly_sound.
