(* ============================================================================
   NetTopologySuite.Proofs.JCTMirrorKit
   ----------------------------------------------------------------------------
   ESCAPE DESCENT, rung 5b: THE MIRROR KIT.  The boundary-hugging walk that
   closes the descent needs corridor moves in all four orientations: west
   AND east of a wall, under bottoms AND over tops.  Rather than hand-write
   three mirrored copies of the corridor/corner kits (rungs 2-5a), this
   rung transports the whole complement geometry through the two coordinate
   reflections:

     xmir (x, y) := (-x, y)   -- swaps east/west,
     ymir (x, y) := (x, -y)   -- swaps over/under.

   Transported invariants (each both ways, via involution):
     - the edge list:        ring_edges (map m r) = mapped edges;
     - the skeleton:         ring_image / ring_complement;
     - tautness:             ring_taut;
     - closedness:           ring_closed;
     - connectivity:         connected_in_complement_cont (paths compose
                             with the reflection; Stdlib continuity_opp);
     - boundedness:          in_bounded_component_cont (the norm
                             px^2 + py^2 is reflection-invariant);
     - the ray guard (ymir): ray_avoids_vertices -- the eastward ray is
                             horizontal, so the y-flip preserves it exactly;
     - the crossing data (ymir): under the guard every half-open crossing
       is a strict straddle (`ho_cross_strict_of_guard`), and strictness is
       y-symmetric, so `edge_crosses_ray_ho`, `ho_count` and the parity
       transport across the y-flip exactly (`ho_count_ymir`).

   The x-flip reverses the ray (eastward becomes westward), so counts are
   NOT x-transported -- the walk uses xmir only for freedom/connectivity
   (east-side corridors = west-side corridors of the mirror) and recomputes
   counts at the endpoints in original coordinates.

   With this kit, every west/under theorem of rungs 2-5a applies verbatim
   to `map xmir r` / `map ymir r`, and the conclusions pull back along
   `connected_xmir_rev` / `connected_ymir_rev`.  Rung 5c assembles the
   four-orientation walk.

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Arith Lia.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam.
From NTS.Proofs Require Import PointInRingCorrect JCT JCT_OnEdgeCounterexample.
From NTS.Proofs Require Import ConvexOffringSeam JCTParityTransport.
From NTS.Proofs Require Import JCTHalfOpenParity JCTGenericStability JCTLevelJump.
From NTS.Proofs Require Import JCTTrappedHalf JCTSeamAssembly JCTEscapeDescent.
From NTS.Proofs Require Import JCTEastApproach JCTCorridor JCTWalkKit JCTWalkStep.
From NTS.Proofs Require Import JCTTautClearance JCTWallClear JCTCornerSector.
From NTS.Proofs Require Import JCTCornerClear.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §0  The two reflections and their involutions.
   --------------------------------------------------------------------------- *)

Definition xmir (p : Point) : Point := mkPoint (- px p) (py p).
Definition ymir (p : Point) : Point := mkPoint (px p) (- py p).

Lemma xmir_invol : forall p : Point, xmir (xmir p) = p.
Proof.
  intros [x y]. unfold xmir. cbn [px py]. f_equal. ring.
Qed.

Lemma ymir_invol : forall p : Point, ymir (ymir p) = p.
Proof.
  intros [x y]. unfold ymir. cbn [px py]. f_equal. ring.
Qed.

Lemma map_xmir_invol : forall (r : Ring), map xmir (map xmir r) = r.
Proof.
  induction r as [| a r IH]; [ reflexivity | ].
  cbn [map]. rewrite xmir_invol, IH. reflexivity.
Qed.

Lemma map_ymir_invol : forall (r : Ring), map ymir (map ymir r) = r.
Proof.
  induction r as [| a r IH]; [ reflexivity | ].
  cbn [map]. rewrite ymir_invol, IH. reflexivity.
Qed.

(* ---------------------------------------------------------------------------
   §1  The edge list of a mapped ring.
   --------------------------------------------------------------------------- *)

Lemma ring_edges_map : forall (m : Point -> Point) (r : Ring),
  ring_edges (map m r)
    = map (fun e => (m (fst e), m (snd e))) (ring_edges r).
Proof.
  intros m. induction r as [| a r IH]; [ reflexivity | ].
  destruct r as [| b r']; [ reflexivity | ].
  cbn [map ring_edges] in *. f_equal. exact IH.
Qed.

Lemma ring_closed_map : forall (m : Point -> Point) (r : Ring),
  ring_closed r -> ring_closed (map m r).
Proof.
  intros m r [p [ps He]]. subst r.
  exists (m p), (map m ps).
  cbn [map]. rewrite map_app. reflexivity.
Qed.

(* ---------------------------------------------------------------------------
   §2  Skeleton transport.
   --------------------------------------------------------------------------- *)

Lemma ring_image_xmir : forall (r : Ring) (q : Point),
  ring_image (map xmir r) (xmir q) <-> ring_image r q.
Proof.
  intros r q. unfold ring_image. split.
  - intros [e [t [Hin [Ht [Hx Hy]]]]].
    rewrite ring_edges_map in Hin.
    apply in_map_iff in Hin. destruct Hin as [e' [He Hin']].
    subst e. cbn [fst snd] in Hx, Hy.
    unfold xmir in Hx, Hy; cbn [px py] in Hx, Hy.
    exists e', t.
    split; [ exact Hin' | ]. split; [ exact Ht | ]. split; nra.
  - intros [e [t [Hin [Ht [Hx Hy]]]]].
    exists (xmir (fst e), xmir (snd e)), t.
    split.
    { rewrite ring_edges_map.
      change (xmir (fst e), xmir (snd e))
        with ((fun e0 => (xmir (fst e0), xmir (snd e0))) e).
      apply in_map. exact Hin. }
    split; [ exact Ht | ].
    cbn [fst snd]. unfold xmir; cbn [px py]. split; nra.
Qed.

Lemma ring_image_ymir : forall (r : Ring) (q : Point),
  ring_image (map ymir r) (ymir q) <-> ring_image r q.
Proof.
  intros r q. unfold ring_image. split.
  - intros [e [t [Hin [Ht [Hx Hy]]]]].
    rewrite ring_edges_map in Hin.
    apply in_map_iff in Hin. destruct Hin as [e' [He Hin']].
    subst e. cbn [fst snd] in Hx, Hy.
    unfold ymir in Hx, Hy; cbn [px py] in Hx, Hy.
    exists e', t.
    split; [ exact Hin' | ]. split; [ exact Ht | ]. split; nra.
  - intros [e [t [Hin [Ht [Hx Hy]]]]].
    exists (ymir (fst e), ymir (snd e)), t.
    split.
    { rewrite ring_edges_map.
      change (ymir (fst e), ymir (snd e))
        with ((fun e0 => (ymir (fst e0), ymir (snd e0))) e).
      apply in_map. exact Hin. }
    split; [ exact Ht | ].
    cbn [fst snd]. unfold ymir; cbn [px py]. split; nra.
Qed.

Lemma ring_complement_xmir : forall (r : Ring) (q : Point),
  ring_complement (map xmir r) (xmir q) <-> ring_complement r q.
Proof.
  intros r q. unfold ring_complement.
  split; intros H C; apply H; apply (ring_image_xmir r q); exact C.
Qed.

Lemma ring_complement_ymir : forall (r : Ring) (q : Point),
  ring_complement (map ymir r) (ymir q) <-> ring_complement r q.
Proof.
  intros r q. unfold ring_complement.
  split; intros H C; apply H; apply (ring_image_ymir r q); exact C.
Qed.

(* ---------------------------------------------------------------------------
   §3  Tautness transport.
   --------------------------------------------------------------------------- *)

Lemma ring_taut_xmir : forall (r : Ring),
  ring_taut r -> ring_taut (map xmir r).
Proof.
  intros r Htaut e f Hin1 Hin2 t s Ht Hs Hx Hy.
  rewrite ring_edges_map in Hin1, Hin2.
  apply in_map_iff in Hin1. destruct Hin1 as [e' [He Hin1']].
  apply in_map_iff in Hin2. destruct Hin2 as [f' [Hf Hin2']].
  subst e f. cbn [fst snd] in *.
  unfold xmir in Hx, Hy; cbn [px py] in Hx, Hy.
  assert (Hx' : (1 - t) * px (fst e') + t * px (snd e')
                  = (1 - s) * px (fst f') + s * px (snd f')) by nra.
  assert (Hy' : (1 - t) * py (fst e') + t * py (snd e')
                  = (1 - s) * py (fst f') + s * py (snd f')) by nra.
  destruct (Htaut e' f' Hin1' Hin2' t s Ht Hs Hx' Hy') as [He | [H1 H2]].
  - left. exact He.
  - right. rewrite H1, H2. split; reflexivity.
Qed.

Lemma ring_taut_ymir : forall (r : Ring),
  ring_taut r -> ring_taut (map ymir r).
Proof.
  intros r Htaut e f Hin1 Hin2 t s Ht Hs Hx Hy.
  rewrite ring_edges_map in Hin1, Hin2.
  apply in_map_iff in Hin1. destruct Hin1 as [e' [He Hin1']].
  apply in_map_iff in Hin2. destruct Hin2 as [f' [Hf Hin2']].
  subst e f. cbn [fst snd] in *.
  unfold ymir in Hx, Hy; cbn [px py] in Hx, Hy.
  assert (Hx' : (1 - t) * px (fst e') + t * px (snd e')
                  = (1 - s) * px (fst f') + s * px (snd f')) by nra.
  assert (Hy' : (1 - t) * py (fst e') + t * py (snd e')
                  = (1 - s) * py (fst f') + s * py (snd f')) by nra.
  destruct (Htaut e' f' Hin1' Hin2' t s Ht Hs Hx' Hy') as [He | [H1 H2]].
  - left. exact He.
  - right. rewrite H1, H2. split; reflexivity.
Qed.

(* ---------------------------------------------------------------------------
   §4  Connectivity and boundedness transport.
   --------------------------------------------------------------------------- *)

Lemma path_continuous_xmir : forall (path : R -> Point),
  path_continuous path -> path_continuous (fun t => xmir (path t)).
Proof.
  intros path [Hx Hy]. split.
  - exact (continuity_opp _ Hx).
  - exact Hy.
Qed.

Lemma path_continuous_ymir : forall (path : R -> Point),
  path_continuous path -> path_continuous (fun t => ymir (path t)).
Proof.
  intros path [Hx Hy]. split.
  - exact Hx.
  - exact (continuity_opp _ Hy).
Qed.

Lemma connected_xmir : forall (r : Ring) (p q : Point),
  connected_in_complement_cont r p q ->
  connected_in_complement_cont (map xmir r) (xmir p) (xmir q).
Proof.
  intros r p q [path [Hc [H0 [H1 Havoid]]]].
  exists (fun t => xmir (path t)).
  split; [ exact (path_continuous_xmir path Hc) | ].
  split; [ rewrite H0; reflexivity | ].
  split; [ rewrite H1; reflexivity | ].
  intros t Ht.
  apply (ring_complement_xmir r (path t)). exact (Havoid t Ht).
Qed.

Lemma connected_ymir : forall (r : Ring) (p q : Point),
  connected_in_complement_cont r p q ->
  connected_in_complement_cont (map ymir r) (ymir p) (ymir q).
Proof.
  intros r p q [path [Hc [H0 [H1 Havoid]]]].
  exists (fun t => ymir (path t)).
  split; [ exact (path_continuous_ymir path Hc) | ].
  split; [ rewrite H0; reflexivity | ].
  split; [ rewrite H1; reflexivity | ].
  intros t Ht.
  apply (ring_complement_ymir r (path t)). exact (Havoid t Ht).
Qed.

Lemma connected_xmir_rev : forall (r : Ring) (p q : Point),
  connected_in_complement_cont (map xmir r) (xmir p) (xmir q) ->
  connected_in_complement_cont r p q.
Proof.
  intros r p q H.
  pose proof (connected_xmir (map xmir r) (xmir p) (xmir q) H) as H'.
  rewrite map_xmir_invol, !xmir_invol in H'. exact H'.
Qed.

Lemma connected_ymir_rev : forall (r : Ring) (p q : Point),
  connected_in_complement_cont (map ymir r) (ymir p) (ymir q) ->
  connected_in_complement_cont r p q.
Proof.
  intros r p q H.
  pose proof (connected_ymir (map ymir r) (ymir p) (ymir q) H) as H'.
  rewrite map_ymir_invol, !ymir_invol in H'. exact H'.
Qed.

Lemma in_bounded_xmir_rev : forall (r : Ring) (p : Point),
  in_bounded_component_cont (map xmir r) (xmir p) ->
  in_bounded_component_cont r p.
Proof.
  intros r p [M [HM Hb]]. exists M. split; [ exact HM | ].
  intros q Hconn.
  pose proof (Hb (xmir q) (connected_xmir r p q Hconn)) as Hq.
  unfold xmir in Hq; cbn [px py] in Hq. nra.
Qed.

Lemma in_bounded_ymir_rev : forall (r : Ring) (p : Point),
  in_bounded_component_cont (map ymir r) (ymir p) ->
  in_bounded_component_cont r p.
Proof.
  intros r p [M [HM Hb]]. exists M. split; [ exact HM | ].
  intros q Hconn.
  pose proof (Hb (ymir q) (connected_ymir r p q Hconn)) as Hq.
  unfold ymir in Hq; cbn [px py] in Hq. nra.
Qed.

Lemma in_bounded_xmir : forall (r : Ring) (p : Point),
  in_bounded_component_cont r p ->
  in_bounded_component_cont (map xmir r) (xmir p).
Proof.
  intros r p H.
  apply (in_bounded_xmir_rev (map xmir r) (xmir p)).
  rewrite map_xmir_invol, xmir_invol. exact H.
Qed.

Lemma in_bounded_ymir : forall (r : Ring) (p : Point),
  in_bounded_component_cont r p ->
  in_bounded_component_cont (map ymir r) (ymir p).
Proof.
  intros r p H.
  apply (in_bounded_ymir_rev (map ymir r) (ymir p)).
  rewrite map_ymir_invol, ymir_invol. exact H.
Qed.

(* ---------------------------------------------------------------------------
   §5  The ray guard across the y-flip (the ray is horizontal).
   --------------------------------------------------------------------------- *)

Lemma guard_ymir : forall (r : Ring) (p : Point),
  ray_avoids_vertices p r ->
  ray_avoids_vertices (ymir p) (map ymir r).
Proof.
  intros r p Hg v Hin [Hy Hx].
  apply in_map_iff in Hin. destruct Hin as [v' [Hv Hin']].
  subst v. unfold ymir in Hy, Hx; cbn [px py] in Hy, Hx.
  apply (Hg v' Hin'). split; lra.
Qed.

Lemma guard_ymir_rev : forall (r : Ring) (p : Point),
  ray_avoids_vertices (ymir p) (map ymir r) ->
  ray_avoids_vertices p r.
Proof.
  intros r p Hg v Hin [Hy Hx].
  apply (Hg (ymir v)).
  - apply in_map. exact Hin.
  - unfold ymir; cbn [px py]. split; lra.
Qed.

(* ---------------------------------------------------------------------------
   §6  Crossing data across the y-flip: under the guard, the half-open
       convention is a strict straddle, and strictness is y-symmetric.
   --------------------------------------------------------------------------- *)

Lemma ho_cross_ymir : forall (r : Ring) (p : Point) (a b : Point),
  ray_avoids_vertices p r ->
  In (a, b) (ring_edges r) ->
  (edge_crosses_ray_ho (ymir p) (ymir a, ymir b)
     <-> edge_crosses_ray_ho p (a, b)).
Proof.
  intros r p a b Hg Hin.
  assert (Hin' : In (ymir a, ymir b) (ring_edges (map ymir r))).
  { rewrite ring_edges_map.
    change (ymir a, ymir b)
      with ((fun e => (ymir (fst e), ymir (snd e))) (a, b)).
    apply in_map. exact Hin. }
  split.
  - intro Hc.
    pose proof (ho_cross_strict_of_guard (map ymir r) (ymir p)
                  (ymir a) (ymir b) (guard_ymir r p Hg) Hin' Hc) as Hstrict.
    unfold ymir in Hstrict; cbn [px py] in Hstrict.
    unfold edge_crosses_ray_ho in Hc |- *.
    unfold ymir in Hc; cbn [px py] in Hc.
    destruct Hstrict as [Hs | Hs].
    + (* py b < py p < py a : the original SECOND disjunct *)
      right. split; [ lra | ].
      destruct Hc as [[Hb Hx] | [Hb Hx]]; [ | lra ].
      replace (px b + (px a - px b) * (py p - py b) / (py a - py b))
        with (px a + (px b - px a) * (- py p - - py a) / (- py b - - py a))
        by (field; lra).
      exact Hx.
    + (* py a < py p < py b : the original FIRST disjunct *)
      left. split; [ lra | ].
      destruct Hc as [[Hb Hx] | [Hb Hx]]; [ lra | ].
      replace (px a + (px b - px a) * (py p - py a) / (py b - py a))
        with (px b + (px a - px b) * (- py p - - py b) / (- py a - - py b))
        by (field; lra).
      exact Hx.
  - intro Hc.
    pose proof (ho_cross_strict_of_guard r p a b Hg Hin Hc) as Hstrict.
    unfold edge_crosses_ray_ho in Hc |- *.
    unfold ymir; cbn [px py].
    destruct Hstrict as [Hs | Hs].
    + (* py a < py p < py b : the mirrored SECOND disjunct *)
      right. split; [ lra | ].
      destruct Hc as [[Hb Hx] | [Hb Hx]]; [ | lra ].
      replace (px b + (px a - px b) * (- py p - - py b) / (- py a - - py b))
        with (px a + (px b - px a) * (py p - py a) / (py b - py a))
        by (field; lra).
      exact Hx.
    + (* py b < py p < py a : the mirrored FIRST disjunct *)
      left. split; [ lra | ].
      destruct Hc as [[Hb Hx] | [Hb Hx]]; [ lra | ].
      replace (px a + (px b - px a) * (- py p - - py a) / (- py b - - py a))
        with (px b + (px a - px b) * (py p - py b) / (py a - py b))
        by (field; lra).
      exact Hx.
Qed.

Lemma ho_count_ymir : forall (r : Ring) (p : Point),
  ray_avoids_vertices p r ->
  ho_count (ymir p) (ring_edges (map ymir r)) = ho_count p (ring_edges r).
Proof.
  intros r p Hg.
  rewrite ring_edges_map.
  assert (Hsub : forall l, (forall e, In e l -> In e (ring_edges r)) ->
    ho_count (ymir p) (map (fun e => (ymir (fst e), ymir (snd e))) l)
      = ho_count p l).
  { induction l as [| e l' IH]; intros Hsubl; [ reflexivity | ].
    cbn [map ho_count].
    rewrite IH; [ | intros e' He'; apply Hsubl; right; exact He' ].
    destruct e as [a b]; cbn [fst snd].
    pose proof (ho_cross_ymir r p a b Hg
                  (Hsubl (a, b) (or_introl eq_refl))) as Hiff.
    destruct (edge_crosses_ray_ho_dec (ymir p) (ymir a, ymir b)) as [H1 | H1];
    destruct (edge_crosses_ray_ho_dec p (a, b)) as [H2 | H2];
      [ reflexivity
      | exfalso; exact (H2 (proj1 Hiff H1))
      | exfalso; exact (H1 (proj2 Hiff H2))
      | reflexivity ]. }
  apply Hsub. intros e He. exact He.
Qed.

Lemma ho_parity_even_ymir : forall (r : Ring) (p : Point),
  ray_avoids_vertices p r ->
  (ho_parity_even (ymir p) (ring_edges (map ymir r))
     <-> ho_parity_even p (ring_edges r)).
Proof.
  intros r p Hg.
  destruct (ho_count_parity (ymir p) (ring_edges (map ymir r))) as [HE1 _].
  destruct (ho_count_parity p (ring_edges r)) as [HE2 _].
  rewrite <- HE1, <- HE2.
  rewrite (ho_count_ymir r p Hg).
  split; intro H; exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions ring_taut_xmir.
Print Assumptions connected_xmir_rev.
Print Assumptions in_bounded_ymir_rev.
Print Assumptions ho_count_ymir.
