(* ============================================================================
   NetTopologySuite.Proofs.JCTParityTransport
   ----------------------------------------------------------------------------
   H1 PROPER, part 1: the topological transport engine for the general simple
   polygon, and the reduction of H1's hard "trapped" half to ONE isolated
   analytic kernel.

   The seam's load-bearing half is "an odd-parity off-ring point is trapped"
   (no continuous escape to infinity).  The classical proof transports a
   parity-like invariant along the escape path: the invariant is locally
   constant on the complement, differs between the start (odd) and the far
   field (even), and a continuous path cannot change a locally-constant
   decidable value -- contradiction.  This file builds that machinery in full
   generality and Qed-closes everything EXCEPT the kernel:

     §1  Decidability: `edge_crosses_ray_dec`, `ray_parity_dec` (every edge
         list is decidably odd-or-even), `ray_parity_excl` (never both),
         `point_in_ring_dec`.
     §2  `invariant_transport_along_path` : a pointwise-DECIDABLE predicate
         that is locally stable along a path is constant along it.  Pure
         completeness-of-R (lub) argument; the decidability replaces the
         classical choice the textbook proof hides, so the corpus's 3-axiom
         budget is preserved.
     §3  `invariant_traps` / `odd_parity_trapped_of_invariant` : ANY ring,
         ANY point.  Given an invariant Q that is (i) decidable, (ii) locally
         constant along complement paths, (iii) false beyond some radius, and
         (iv) agreeing with `point_in_ring` at p -- an odd-parity p is in a
         bounded complement component.  This is H1's trapped half, reduced.
     §4  Non-vacuity: the rectangle instantiates the reduction.  Q := the
         box-field sign (`0 < box_min`); local constancy is the sign
         stability of a continuous field that is nonzero on the complement
         (`pos_stable_along` / `neg_stable_along`), far-falsity is the box
         bound.  `rect_trapped_via_invariant` re-derives the rectangle's
         trapping through the generic engine.

   THE KERNEL THAT REMAINS (the genuine H1 content, stated honestly): exhibit
   such a Q for an arbitrary simple ring.  The intended Q is the HALF-OPEN
   ray parity (count an edge when `vy <= h < wy` or `wy <= h < vy`): the
   STRICT parity of `point_in_ring` is NOT locally constant on the
   complement -- a far-west point's strict count jumps by one when its height
   crosses a pass-through vertex (one neighbour above, one below), because
   both incident edges stop counting while exactly one alternation remains
   elsewhere.  The half-open convention re-counts exactly one of the two
   incident edges and is the classical locally-constant invariant; under the
   ray guards it agrees with the strict parity pointwise.  Constructing it
   and proving (ii) is the y-monotone vertex-pairing argument -- the isolated
   remaining work.

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From Stdlib Require Import Ranalysis.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam.
From NTS.Proofs Require Import PointInRingCorrect JCT JCT_OnEdgeCounterexample.
From NTS.Proofs Require Import RectangleJCT RectangleSeparation RectangleOffringSeam.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §1  Decidability of the crossing-number parity.
   --------------------------------------------------------------------------- *)

Lemma edge_crosses_ray_dec : forall (p : Point) (e : Edge),
  {edge_crosses_ray p e} + {~ edge_crosses_ray p e}.
Proof.
  intros p [a b]. unfold edge_crosses_ray.
  assert (D1 : {py a < py p < py b /\
                px p < px a + (px b - px a) * (py p - py a) / (py b - py a)}
             + {~ (py a < py p < py b /\
                px p < px a + (px b - px a) * (py p - py a) / (py b - py a))}).
  { destruct (Rlt_dec (py a) (py p)) as [H1 | H1];
      [ destruct (Rlt_dec (py p) (py b)) as [H2 | H2];
        [ destruct (Rlt_dec (px p)
            (px a + (px b - px a) * (py p - py a) / (py b - py a))) as [H3 | H3];
          [ left; tauto | right; intros [_ Hc]; exact (H3 Hc) ]
        | right; intros [[_ Hc] _]; exact (H2 Hc) ]
      | right; intros [[Hc _] _]; exact (H1 Hc) ]. }
  assert (D2 : {py b < py p < py a /\
                px p < px b + (px a - px b) * (py p - py b) / (py a - py b)}
             + {~ (py b < py p < py a /\
                px p < px b + (px a - px b) * (py p - py b) / (py a - py b))}).
  { destruct (Rlt_dec (py b) (py p)) as [H1 | H1];
      [ destruct (Rlt_dec (py p) (py a)) as [H2 | H2];
        [ destruct (Rlt_dec (px p)
            (px b + (px a - px b) * (py p - py b) / (py a - py b))) as [H3 | H3];
          [ left; tauto | right; intros [_ Hc]; exact (H3 Hc) ]
        | right; intros [[_ Hc] _]; exact (H2 Hc) ]
      | right; intros [[Hc _] _]; exact (H1 Hc) ]. }
  destruct D1 as [Hy | Hn1]; [ left; left; exact Hy | ].
  destruct D2 as [Hy | Hn2]; [ left; right; exact Hy | ].
  right; intros [Hc | Hc]; [ exact (Hn1 Hc) | exact (Hn2 Hc) ].
Qed.

(* Every edge list is decidably odd-or-even... *)
Lemma ray_parity_dec : forall (p : Point) (es : list Edge),
  {ray_parity_odd p es} + {ray_parity_even p es}.
Proof.
  intros p; induction es as [| e es' IH].
  - right; constructor.
  - destruct (edge_crosses_ray_dec p e) as [Hc | Hn]; destruct IH as [Ho | He].
    + right; apply rpe_cross; assumption.
    + left; apply rpo_cross; assumption.
    + left; apply rpo_skip; assumption.
    + right; apply rpe_skip; assumption.
Qed.

(* ... and never both. *)
Lemma ray_parity_excl : forall (p : Point) (es : list Edge),
  ray_parity_odd p es -> ray_parity_even p es -> False.
Proof.
  intros p; induction es as [| e es' IH]; intros Ho He.
  - inversion Ho.
  - inversion Ho as [? ? Hc1 Ht1 | ? ? Hn1 Ht1]; subst;
    inversion He as [| ? ? Hc2 Ht2 | ? ? Hn2 Ht2]; subst.
    + exact (IH Ht2 Ht1).
    + exact (Hn2 Hc1).
    + exact (Hn1 Hc2).
    + exact (IH Ht1 Ht2).
Qed.

Theorem point_in_ring_dec : forall (p : Point) (r : Ring),
  {point_in_ring p r} + {~ point_in_ring p r}.
Proof.
  intros p r. unfold point_in_ring.
  destruct (ray_parity_dec p (ring_edges r)) as [Ho | He].
  - left; exact Ho.
  - right; intro Ho; exact (ray_parity_excl p _ Ho He).
Qed.

(* ---------------------------------------------------------------------------
   §2  The transport engine: a decidable, locally-stable predicate is
       constant along a path.  Completeness-of-R; no new axioms.
   --------------------------------------------------------------------------- *)

Theorem invariant_transport_along_path :
  forall (Q : Point -> Prop) (g : R -> Point),
    (forall pt : Point, {Q pt} + {~ Q pt}) ->
    (forall t, 0 <= t <= 1 ->
       exists d, 0 < d /\
         forall s, 0 <= s <= 1 -> Rabs (s - t) < d -> (Q (g s) <-> Q (g t))) ->
    (Q (g 0) <-> Q (g 1)).
Proof.
  intros Q g Qdec Hstab.
  set (E := fun t : R => 0 <= t <= 1 /\ (Q (g t) <-> Q (g 0))).
  assert (HE0 : E 0) by (split; [ lra | tauto ]).
  assert (Hbnd : bound E) by (exists 1; intros t [Ht _]; lra).
  destruct (completeness E Hbnd (ex_intro _ 0 HE0)) as [m [Hub Hleast]].
  assert (Hm0 : 0 <= m) by (apply Hub; exact HE0).
  assert (Hm1 : m <= 1) by (apply Hleast; intros t [Ht _]; lra).
  destruct (Hstab m (conj Hm0 Hm1)) as [d [Hd Hball]].
  (* Step 1: Q (g m) <-> Q (g 0).  The goal is decidable; in the two "bad"
     cases every E-element is forced below m - d/2, contradicting leastness. *)
  assert (Hgm : Q (g m) <-> Q (g 0)).
  { assert (Hupb : (Q (g m) <-> Q (g 0)) \/ is_upper_bound E (m - d / 2)).
    { destruct (Qdec (g m)) as [Hq | Hq]; destruct (Qdec (g 0)) as [H0 | H0];
        try (left; tauto);
        right; intros t [Htr Hiff];
        destruct (Rle_or_lt t (m - d / 2)) as [Hle | Hgt]; try exact Hle;
        exfalso;
        assert (Hlem : t <= m) by (apply Hub; split; assumption);
        assert (Htm : Rabs (t - m) < d)
          by (unfold Rabs; destruct (Rcase_abs (t - m)); lra);
        pose proof (Hball t Htr Htm) as Hiff2; tauto. }
    destruct Hupb as [Hgood | Hupb]; [ exact Hgood | exfalso ].
    pose proof (Hleast _ Hupb). lra. }
  (* Step 2: the supremum is 1 -- otherwise the ball extends E past m. *)
  destruct (Rlt_le_dec m 1) as [Hlt | Hge].
  - exfalso.
    set (s := Rmin 1 (m + d / 2)).
    assert (Hs01 : 0 <= s <= 1).
    { unfold s; split; [ apply Rmin_glb; lra | apply Rmin_l ]. }
    assert (Hsm : Rabs (s - m) < d).
    { unfold s, Rmin; destruct (Rle_dec 1 (m + d / 2));
        unfold Rabs; destruct (Rcase_abs _); lra. }
    pose proof (Hball s Hs01 Hsm) as Hiff.
    assert (HsE : E s) by (split; [ exact Hs01 | tauto ]).
    pose proof (Hub s HsE) as Hsub.
    unfold s, Rmin in Hsub; destruct (Rle_dec 1 (m + d / 2)); lra.
  - assert (Hm : m = 1) by lra.
    rewrite Hm in Hgm. tauto.
Qed.

(* ---------------------------------------------------------------------------
   §3  The reduction: H1's "trapped" half, for ANY ring, from an invariant.
   --------------------------------------------------------------------------- *)

(* What a family (or, for H1 proper, the half-open parity construction) must
   supply: local constancy along complement paths, and far-falsity. *)
Definition parity_invariant_for (r : Ring) (Q : Point -> Prop) : Prop :=
  (forall g : R -> Point,
     path_continuous g ->
     (forall t, 0 <= t <= 1 -> ring_complement r (g t)) ->
     forall t, 0 <= t <= 1 ->
       exists d, 0 < d /\
         forall s, 0 <= s <= 1 -> Rabs (s - t) < d -> (Q (g s) <-> Q (g t)))
  /\ (exists Mq, 0 < Mq /\
        forall q, Mq < px q * px q + py q * py q -> ~ Q q).

Theorem invariant_traps :
  forall (r : Ring) (p : Point) (Q : Point -> Prop),
    (forall pt : Point, {Q pt} + {~ Q pt}) ->
    parity_invariant_for r Q ->
    Q p ->
    in_bounded_component_cont r p.
Proof.
  intros r p Q Qdec [Hloc [Mq [HMq Hfar]]] Hq.
  exists (Mq + 1). split; [ lra | ].
  intros q [g [Hgc [Hg0 [Hg1 Hcompl]]]].
  pose proof (invariant_transport_along_path Q g Qdec
                (Hloc g Hgc Hcompl)) as Hiff.
  rewrite Hg0, Hg1 in Hiff.
  assert (Hqq : Q q) by tauto.
  destruct (Rle_or_lt (px q * px q + py q * py q) Mq) as [Hle | Hgt].
  - nra.
  - exfalso. exact (Hfar q Hgt Hqq).
Qed.

(* The seam-shaped corollary: an odd-parity point agreeing with the invariant
   is trapped.  H1's hard half now IS "construct Q" (the half-open parity). *)
Theorem odd_parity_trapped_of_invariant :
  forall (r : Ring) (p : Point) (Q : Point -> Prop),
    (forall pt : Point, {Q pt} + {~ Q pt}) ->
    parity_invariant_for r Q ->
    (Q p <-> point_in_ring p r) ->
    point_in_ring p r ->
    in_bounded_component_cont r p.
Proof.
  intros r p Q Qdec Hinv Hagree Hpir.
  apply (invariant_traps r p Q Qdec Hinv). tauto.
Qed.

(* ---------------------------------------------------------------------------
   §4  Non-vacuity: the rectangle instantiates the reduction.
   --------------------------------------------------------------------------- *)

(* Sign stability of a continuous real function at a point. *)
Lemma pos_stable_at : forall (F : R -> R) (t : R),
  continuity_pt F t -> 0 < F t ->
  exists d, 0 < d /\ forall s, Rabs (s - t) < d -> 0 < F s.
Proof.
  intros F t Hc HF.
  destruct (Hc (F t) HF) as [d [Hd Hball]].
  exists d. split; [ lra | ].
  intros s Hs.
  destruct (Req_dec t s) as [Heq | Hne]; [ rewrite <- Heq; exact HF | ].
  assert (Hdist : R_dist (F s) (F t) < F t).
  { apply Hball. split.
    - split; [ exact I | exact Hne ].
    - simpl. unfold R_dist. exact Hs. }
  unfold R_dist, Rabs in Hdist. destruct (Rcase_abs (F s - F t)); lra.
Qed.

Lemma neg_stable_at : forall (F : R -> R) (t : R),
  continuity_pt F t -> F t < 0 ->
  exists d, 0 < d /\ forall s, Rabs (s - t) < d -> F s < 0.
Proof.
  intros F t Hc HF.
  destruct (Hc (- F t) ltac:(lra)) as [d [Hd Hball]].
  exists d. split; [ lra | ].
  intros s Hs.
  destruct (Req_dec t s) as [Heq | Hne]; [ rewrite <- Heq; exact HF | ].
  assert (Hdist : R_dist (F s) (F t) < - F t).
  { apply Hball. split.
    - split; [ exact I | exact Hne ].
    - simpl. unfold R_dist. exact Hs. }
  unfold R_dist, Rabs in Hdist. destruct (Rcase_abs (F s - F t)); lra.
Qed.

(* The rectangle's invariant: the box-field sign. *)
Theorem rect_parity_invariant : forall x0 y0 x1 y1,
  x0 < x1 -> y0 < y1 ->
  parity_invariant_for (rect_ring x0 y0 x1 y1)
    (fun q => 0 < box_min x0 y0 x1 y1 q).
Proof.
  intros x0 y0 x1 y1 Hx01 Hy01. split.
  - (* local constancy: the field is continuous along the path and nonzero on
       the complement, so its sign is stable *)
    intros g [Hgx Hgy] Hcompl t Ht.
    assert (Hc : continuity_pt (fun s => box_min x0 y0 x1 y1 (g s)) t)
      by (apply continuity_pt_box_min_path; [ apply Hgx | apply Hgy ]).
    destruct (Rtotal_order 0 (box_min x0 y0 x1 y1 (g t))) as [Hpos | [Hz | Hneg]].
    + destruct (pos_stable_at _ t Hc Hpos) as [d [Hd Hball]].
      exists d. split; [ exact Hd | ].
      intros s Hs01 Hst. pose proof (Hball s Hst). split; intros _; lra.
    + exfalso.
      exact (box_min_nonzero_off_skeleton x0 y0 x1 y1 (g t) Hx01 Hy01
               (Hcompl t Ht) (eq_sym Hz)).
    + destruct (neg_stable_at _ t Hc Hneg) as [d [Hd Hball]].
      exists d. split; [ exact Hd | ].
      intros s Hs01 Hst. pose proof (Hball s Hst).
      split; intros Habs; lra.
  - (* far-falsity: a positive field confines the point to the box *)
    set (Mq := x0 * x0 + x1 * x1 + y0 * y0 + y1 * y1 + 1).
    exists Mq. split; [ unfold Mq; nra | ].
    intros q Hfar Hpos.
    apply box_min_pos_iff in Hpos.
    pose proof (sq_le_max_endpoints (px q) x0 x1 ltac:(lra)) as Hxm.
    pose proof (sq_le_max_endpoints (py q) y0 y1 ltac:(lra)) as Hym.
    assert (Hx : Rmax (x0 * x0) (x1 * x1) <= x0 * x0 + x1 * x1)
      by (apply Rmax_lub; nra).
    assert (Hy : Rmax (y0 * y0) (y1 * y1) <= y0 * y0 + y1 * y1)
      by (apply Rmax_lub; nra).
    unfold Mq in Hfar. lra.
Qed.

(* The rectangle's trapping, re-derived through the generic engine. *)
Theorem rect_trapped_via_invariant : forall x0 y0 x1 y1 p,
  x0 < x1 -> y0 < y1 ->
  0 < box_min x0 y0 x1 y1 p ->
  in_bounded_component_cont (rect_ring x0 y0 x1 y1) p.
Proof.
  intros x0 y0 x1 y1 p Hx01 Hy01 Hp.
  apply (invariant_traps _ _ (fun q => 0 < box_min x0 y0 x1 y1 q)).
  - intro pt. destruct (Rlt_dec 0 (box_min x0 y0 x1 y1 pt)); [ left | right ]; auto.
  - apply rect_parity_invariant; assumption.
  - exact Hp.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions point_in_ring_dec.
Print Assumptions invariant_transport_along_path.
Print Assumptions invariant_traps.
Print Assumptions odd_parity_trapped_of_invariant.
Print Assumptions rect_trapped_via_invariant.
