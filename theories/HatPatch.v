(* ============================================================================
   NetTopologySuite.Proofs.HatPatch
   ----------------------------------------------------------------------------
   A finite multi-hat patch as a valid, internally non-crossing geometry.

   The hat aperiodic tiling is EXACT in R: every finite patch of hats is a list
   of simple, pairwise non-crossing polygons at every scale -- there is no
   "ring_simple brink".  (The only soundness diameter is the binary64
   coordinate window; see docs/hat-soundness.md.)  This file witnesses that
   with a concrete two-hat patch, placed by translation (no substitution /
   inflation machinery is needed or claimed).

   Reusable content:
     - `translate_ring` and the translation-invariance of `segments_intersect_properly`,
       `ring_edges`, `ring_simple`, `ring_closed`, `ring_has_minimum_points`;
     - `x_separated_no_cross`: rings in disjoint x-bands cannot properly cross.

   Headlines:
     - `hat_patch_all_valid`   : both hats are `valid_polygon`;
     - `hat_patch_non_crossing`: the union of their edges is `pairwise_no_proper_cross`.

   Pure-R; three-axiom.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List.
From NTS.Proofs Require Import Distance Overlay RingSimple RingExtract
                               FacePolygonHoles HatMonotile HatValidPolygon.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Translation of points / rings, and its invariants.                      *)
(* -------------------------------------------------------------------------- *)

Definition tpt (dx dy : R) (p : Point) : Point := mkPoint (px p + dx) (py p + dy).
Definition translate_ring (dx dy : R) (r : Ring) : Ring := map (tpt dx dy) r.

Lemma sip_translate :
  forall dx dy P0 P1 Q0 Q1,
    segments_intersect_properly (tpt dx dy P0) (tpt dx dy P1)
                                (tpt dx dy Q0) (tpt dx dy Q1) ->
    segments_intersect_properly P0 P1 Q0 Q1.
Proof.
  intros dx dy P0 P1 Q0 Q1 (t & s & Ht & Hs & Hx & Hy).
  exists t, s. unfold tpt in *; cbn [px py] in *.
  repeat split; try lra.
Qed.

Lemma ring_edges_translate :
  forall dx dy r,
    ring_edges (translate_ring dx dy r) =
      map (fun e => (tpt dx dy (fst e), tpt dx dy (snd e))) (ring_edges r).
Proof.
  intros dx dy r. induction r as [| a r' IH].
  - reflexivity.
  - destruct r' as [| b l].
    + reflexivity.
    + change (translate_ring dx dy (a :: b :: l))
        with (tpt dx dy a :: tpt dx dy b :: map (tpt dx dy) l).
      rewrite (ring_edges_cons2 (tpt dx dy a) (tpt dx dy b) (map (tpt dx dy) l)).
      rewrite (ring_edges_cons2 a b l).
      cbn [map fst snd].
      f_equal.
      change (tpt dx dy b :: map (tpt dx dy) l) with (translate_ring dx dy (b :: l)).
      exact IH.
Qed.

Lemma ring_simple_translate :
  forall dx dy r, ring_simple r -> ring_simple (translate_ring dx dy r).
Proof.
  intros dx dy r Hr e1 e2 H1 H2 Hne Hsip.
  rewrite ring_edges_translate in H1, H2.
  apply in_map_iff in H1. destruct H1 as [f1 [Hf1 Hin1]].
  apply in_map_iff in H2. destruct H2 as [f2 [Hf2 Hin2]].
  apply (Hr f1 f2 Hin1 Hin2).
  - intro Heq. apply Hne. subst f1. rewrite <- Hf1, <- Hf2. f_equal; exact Heq.
  - subst e1 e2. cbn [fst snd] in Hsip.
    apply (sip_translate dx dy). exact Hsip.
Qed.

Lemma ring_closed_translate :
  forall dx dy r, ring_closed r -> ring_closed (translate_ring dx dy r).
Proof.
  intros dx dy r [p [ps Hr]]. exists (tpt dx dy p), (map (tpt dx dy) ps).
  unfold translate_ring. rewrite Hr. cbn [map]. rewrite map_app. reflexivity.
Qed.

Lemma ring_min_points_translate :
  forall dx dy r, ring_has_minimum_points r ->
    ring_has_minimum_points (translate_ring dx dy r).
Proof.
  intros dx dy r H. unfold ring_has_minimum_points, translate_ring in *.
  rewrite length_map. exact H.
Qed.

Lemma valid_polygon_translate_no_holes :
  forall dx dy r,
    ring_closed r -> ring_simple r -> ring_has_minimum_points r ->
    valid_polygon (mkPolygon (translate_ring dx dy r) []).
Proof.
  intros dx dy r Hc Hs Hm. apply polygon_valid_of_rings.
  - apply ring_closed_translate; exact Hc.
  - apply ring_simple_translate; exact Hs.
  - apply ring_min_points_translate; exact Hm.
  - intros h [].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Rings in disjoint x-bands cannot properly cross.                        *)
(* -------------------------------------------------------------------------- *)

Definition ring_x_le (a : R) (r : Ring) : Prop := forall p, In p r -> px p <= a.
Definition ring_x_ge (b : R) (r : Ring) : Prop := forall p, In p r -> b <= px p.

(* Endpoints of an edge of `r` are members of `r`. *)
Lemma ring_edge_endpoints_in :
  forall r e, In e (ring_edges r) -> In (fst e) r /\ In (snd e) r.
Proof.
  intros r. induction r as [| a r' IH]; intros e He; [ destruct He | ].
  destruct r' as [| b l]; [ destruct He | ].
  rewrite (ring_edges_cons2 a b l) in He. destruct He as [<- | He].
  - cbn [fst snd]. split; [ left; reflexivity | right; left; reflexivity ].
  - destruct (IH e He) as [Hf Hs]. split; right; assumption.
Qed.

Theorem x_separated_no_cross :
  forall (a b : R) (r1 r2 : Ring),
    ring_x_le a r1 -> ring_x_ge b r2 -> a < b ->
    forall e1 e2, In e1 (ring_edges r1) -> In e2 (ring_edges r2) ->
      ~ segments_intersect_properly (fst e1) (snd e1) (fst e2) (snd e2).
Proof.
  intros a b r1 r2 Hle Hge Hab e1 e2 H1 H2 (t & s & Ht & Hs & Hx & Hy).
  destruct (ring_edge_endpoints_in r1 e1 H1) as [Hf1 Hs1].
  destruct (ring_edge_endpoints_in r2 e2 H2) as [Hf2 Hs2].
  pose proof (Hle _ Hf1). pose proof (Hle _ Hs1).
  pose proof (Hge _ Hf2). pose proof (Hge _ Hs2).
  (* crossing x is <= a on the left, >= b on the right: a < b is contradicted *)
  nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The two-hat patch.                                                      *)
(* -------------------------------------------------------------------------- *)

Definition hat2 : Ring := translate_ring 20 0 hat_ring.

Definition hat_patch : list Polygon :=
  [ mkPolygon hat_ring [] ; mkPolygon hat2 [] ].

(* hat1 lives in x <= 8 (max vertex px = 7.5 at hexPt 7 1). *)
Lemma hat_ring_x_le_8 : ring_x_le 8 hat_ring.
Proof.
  intros p Hp. unfold hat_ring in Hp. cbn [In] in Hp.
  repeat (destruct Hp as [<- | Hp]; [ unfold hexPt; cbn [px]; lra | ]).
  destruct Hp.
Qed.

(* hat2 = hat1 shifted +20 in x, so it lives in x >= 19 (min vertex px = 19.5). *)
Lemma hat2_x_ge_19 : ring_x_ge 19 hat2.
Proof.
  intros p Hp. unfold hat2, translate_ring, hat_ring in Hp.
  cbn [map In] in Hp.
  repeat (destruct Hp as [<- | Hp]; [ unfold tpt, hexPt; cbn [px]; lra | ]).
  destruct Hp.
Qed.

Theorem hat_patch_all_valid : Forall valid_polygon hat_patch.
Proof.
  unfold hat_patch.
  apply Forall_cons; [ exact valid_polygon_hat | ].
  apply Forall_cons; [ | apply Forall_nil ].
  apply valid_polygon_translate_no_holes;
    [ apply hat_ring_closed | apply hat_ring_simple | apply hat_ring_min_points ].
Qed.

Theorem hat_patch_non_crossing :
  pairwise_no_proper_cross (ring_edges hat_ring ++ ring_edges hat2).
Proof.
  assert (Hs2 : ring_simple hat2)
    by (apply ring_simple_translate, hat_ring_simple).
  intros e1 e2 H1 H2 Hne.
  apply in_app_or in H1. apply in_app_or in H2.
  destruct H1 as [H1 | H1]; destruct H2 as [H2 | H2].
  - exact (hat_ring_simple e1 e2 H1 H2 Hne).
  - apply (x_separated_no_cross 8 19 hat_ring hat2
             hat_ring_x_le_8 hat2_x_ge_19 ltac:(lra) e1 e2 H1 H2).
  - intro Hsip.
    apply (x_separated_no_cross 8 19 hat_ring hat2
             hat_ring_x_le_8 hat2_x_ge_19 ltac:(lra) e2 e1 H2 H1).
    (* swap argument order of the crossing *)
    destruct Hsip as (t & s & Ht & Hs & Hx & Hy). exists s, t.
    repeat split; lra.
  - exact (Hs2 e1 e2 H1 H2 Hne).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions ring_simple_translate.
Print Assumptions x_separated_no_cross.
Print Assumptions hat_patch_all_valid.
Print Assumptions hat_patch_non_crossing.
