(* ============================================================================
   NetTopologySuite.Proofs.RelateNGJordanUncond
   ----------------------------------------------------------------------------
   ADR-0007 letter (claimId 0007-relateng-jordan-uncond): unconditional
   curve-ring Jordan. QEX expected.

   Intended QED (not constructed):
     forall r, curve_ring r -> jordan_true_region r
   with no taut / no-horizontal / vertex-distinct side conditions, 3-axiom
   host, forcing relateng_kind = RNG_JordanUncond (or inhabiting the park
   ctor for real). That constructor is UncondCurveHeight.

   WHAT IS ALREADY TRUE.  Taut simple polygonal rings with a vertex-free
   height have a closed true-region
   (RelateNGJordanTrueRegion.v : relateng_jordan_true_region_taut;
   pull/issue 791).  That is not forall curve ring.  Do not remint it as
   uncond.  Do not weaken jordan_true_region_taut's guards
   (ray_avoids_vertices / exists_real_avoiding stay).

   WHY QEX.  Blocked by vertex grazing (JCT_VertexGrazingCounterexample.v:
   diamond B = (0,0) grazes (1,0); closed point_in_ring reads EVEN),
   horizontal chords on a valid curve ring, arc members on a valid curve
   ring, and a missing generic height on an arbitrary curve ring.
   UncondCurveHeight stays uninhabited.  RNG_JordanUncond is not flipped.
   Letter status is not RelateNGJordanDischarged.  Issue 509 (V-CP
   CurvePolygon true-region) stays open — this letter is not that stop.

   Not: first_cook_scope, LeftoverBagTermArm, Karney, half-open remint,
   atan2 / classic.  ADR-0007 stays Accepted.

   WITNESS topic: relate · claimId: 0007-relateng-jordan-uncond
   witness: 0007-relateng-jordan-uncond · board: ADR-0007
   3-axiom host lane (Stdlib Reals). No Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import
  RelateNGFace
  RelateNGJordanTrueRegion
  JCT_VertexGrazingCounterexample
  JordanRingKit
  CurveGeometry.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  curve_ring is a valid CurveRing.  The uncond true-region constructor   *)
(*     UncondCurveHeight is missing — do not remint the taut polygonal Prop.  *)
(* -------------------------------------------------------------------------- *)

Definition curve_ring (r : CurveRing) : Prop := valid_curve_ring r.

Inductive UncondCurveJordanPark : Type :=
| UncondCurveHeight.

Definition uncond_curve_height_inhabits (c : UncondCurveJordanPark) : Prop :=
  match c with
  | UncondCurveHeight => False
  end.

Lemma uncond_curve_height_missing :
  ~ uncond_curve_height_inhabits UncondCurveHeight.
Proof.
  intro H. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  #791 is taut, not uncond.  Park and letter stay.                       *)
(* -------------------------------------------------------------------------- *)

Lemma taut_polygonal_is_not_uncond :
  jordan_true_region_taut /\
  relateng_kind <> RNG_JordanUncond.
Proof.
  split; [ exact relateng_jordan_true_region_taut | ].
  exact relateng_not_jordan_uncond.
Qed.

Lemma letter_not_jordan_discharged :
  relateng_letter_status <> RelateNGJordanDischarged.
Proof.
  discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Blockers: vertex grazing, horizontal chord, arc member.                *)
(* -------------------------------------------------------------------------- *)

Lemma diamond_blocks_unguarded_height :
  no_horizontal_edge_at B diamond /\
  ~ ray_avoids_vertices B diamond /\
  ~ point_in_ring B diamond.
Proof.
  destruct diamond_guard_insufficient as [Hnh Hray].
  exact (conj Hnh (conj Hray diamond_not_point_in_ring_B)).
Qed.

Definition locked_rect : CurveRing :=
  [ CSChord (mkPoint 0 0) (mkPoint 1 0)
  ; CSChord (mkPoint 1 0) (mkPoint 1 1)
  ; CSChord (mkPoint 1 1) (mkPoint 0 1)
  ; CSChord (mkPoint 0 1) (mkPoint 0 0) ].

Lemma locked_rect_is_curve_ring : curve_ring locked_rect.
Proof.
  unfold curve_ring, valid_curve_ring, locked_rect.
  split; [ unfold curve_ring_arcs_valid; repeat constructor; auto | ].
  split.
  - unfold curve_ring_adjacent, curve_segment_end, curve_segment_start.
    repeat split; reflexivity.
  - unfold curve_ring_closed, curve_segment_end, curve_segment_start.
    reflexivity.
Qed.

Lemma locked_rect_has_horizontal_chord :
  exists s e : Point,
    In (CSChord s e) locked_rect /\ py s = py e.
Proof.
  exists (mkPoint 0 0), (mkPoint 1 0).
  split; [ unfold locked_rect; left; reflexivity | reflexivity ].
Qed.

Definition locked_arc : CircularArc :=
  mkCircularArc (mkPoint 1 0) (mkPoint 0 1) (mkPoint (-1) 0).

Lemma locked_arc_valid : valid_arc locked_arc.
Proof.
  unfold valid_arc, locked_arc; cbn [arc_start arc_mid arc_end px py].
  lra.
Qed.

Definition locked_lens : CurveRing :=
  [ CSArc locked_arc ; CSChord (mkPoint (-1) 0) (mkPoint 1 0) ].

Lemma locked_lens_is_curve_ring : curve_ring locked_lens.
Proof.
  unfold curve_ring, valid_curve_ring, locked_lens.
  split.
  - unfold curve_ring_arcs_valid. repeat constructor. exact locked_arc_valid.
  - split.
    + unfold curve_ring_adjacent, curve_segment_end, curve_segment_start,
        locked_arc.
      split; reflexivity.
    + unfold curve_ring_closed, curve_segment_end, curve_segment_start,
        locked_arc.
      reflexivity.
Qed.

Lemma locked_lens_has_arc_member :
  exists a : CircularArc, In (CSArc a) locked_lens.
Proof.
  exists locked_arc. unfold locked_lens. left. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Ticket stop.                                                           *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-relateng-jordan-uncond","topic":"relate","lemma":"ticket_0007_relateng_jordan_uncond_qed_or_qex","title":"unconditional curve Jordan: forall curve_ring, a closed true-region with no taut / no-horizontal / vertex-distinct guards and relateng_kind = RNG_JordanUncond (QED) or UncondCurveHeight stays a named missing constructor, the #791 taut polygonal inhabitant stays taut, RNG_JordanUncond stays a park, and vertex grazing / horizontal chords / arc members block a generic curve-ring height (QEX); discharged QEX","file":"theories/RelateNGJordanUncond.v","witness":"0007-relateng-jordan-uncond","board":"ADR-0007"} *)
Theorem ticket_0007_relateng_jordan_uncond_qed_or_qex :
  (relateng_kind = RNG_JordanUncond /\
   uncond_curve_height_inhabits UncondCurveHeight)
  \/
  (relateng_kind <> RNG_JordanUncond /\
   ~ uncond_curve_height_inhabits UncondCurveHeight /\
   relateng_letter_status <> RelateNGJordanDischarged /\
   jordan_true_region_taut /\
   no_horizontal_edge_at B diamond /\
   ~ ray_avoids_vertices B diamond /\
   ~ point_in_ring B diamond /\
   curve_ring locked_rect /\
   (exists s e : Point, In (CSChord s e) locked_rect /\ py s = py e) /\
   curve_ring locked_lens /\
   (exists a : CircularArc, In (CSArc a) locked_lens)).
Proof.
  right.
  split; [ exact relateng_not_jordan_uncond | ].
  split; [ exact uncond_curve_height_missing | ].
  split; [ exact letter_not_jordan_discharged | ].
  split; [ exact relateng_jordan_true_region_taut | ].
  destruct diamond_blocks_unguarded_height as [Hnh [Hray Hpir]].
  split; [ exact Hnh | ].
  split; [ exact Hray | ].
  split; [ exact Hpir | ].
  split; [ exact locked_rect_is_curve_ring | ].
  split; [ exact locked_rect_has_horizontal_chord | ].
  split; [ exact locked_lens_is_curve_ring | ].
  exact locked_lens_has_arc_member.
Qed.

Print Assumptions uncond_curve_height_missing.
Print Assumptions taut_polygonal_is_not_uncond.
Print Assumptions diamond_blocks_unguarded_height.
Print Assumptions locked_rect_is_curve_ring.
Print Assumptions locked_lens_is_curve_ring.
Print Assumptions ticket_0007_relateng_jordan_uncond_qed_or_qex.
