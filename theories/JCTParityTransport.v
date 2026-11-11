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
         that is locally stable along a path is constant along it.  Bisection
         on a nested-interval limit (NestedIntervals), not the Stdlib lub:
         the decidability drives the halving, and no sig_not_dec.
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

   Pure-R; sig_forall_dec + functional_extensionality_dep (no sig_not_dec).
   No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From Stdlib Require Import Ranalysis.
From NTS.Proofs Require Import JordanRingKit NestedIntervals.
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
       constant along a path.  Nested intervals; no sig_not_dec.
   --------------------------------------------------------------------------- *)

(* Bisection, not a supremum: Stdlib `completeness` pulls sig_not_dec, the
   nested-interval limit (NestedIntervals) does not.  While Q(g t) <-> Q(g 0)
   holds at a and fails at b, halve [a,b] keeping that shape; the common
   point c of the intervals has a stability ball containing both ends of a
   short enough interval, so the two ends agree -- contradiction. *)
Lemma inv_pow2_le_inv_IPR : forall p : positive,
  / 2 ^ Pos.to_nat p <= / IPR p.
Proof.
  intro p.
  assert (HN : forall k, INR k <= 2 ^ k).
  { induction k as [| k IH]; cbn [pow]; [ cbn; lra | ].
    rewrite S_INR. assert (1 <= 2 ^ k) by (apply pow_R1_Rle; lra). lra. }
  assert (HI : IPR p = INR (Pos.to_nat p)) by (rewrite INR_IPR; reflexivity).
  assert (Hpos : 0 < IPR p) by exact (IZR_lt 0 (Z.pos p) (Pos2Z.is_pos p)).
  pose proof (HN (Pos.to_nat p)). apply Rinv_le_contravar; lra.
Qed.

Section Bisect.

Variable P : R -> Prop.
Hypothesis Pdec : forall t, {P t} + {~ P t}.

Fixpoint bisect (n : nat) : R * R :=
  match n with
  | O => (0, 1)
  | S k => let ab := bisect k in
           let m := (fst ab + snd ab) / 2 in
           if Pdec m then (m, snd ab) else (fst ab, m)
  end.

Lemma bisect_step : forall n,
  let a := fst (bisect n) in let b := snd (bisect n) in
  a <= b ->
  a <= fst (bisect (S n)) /\ snd (bisect (S n)) <= b /\
  snd (bisect (S n)) - fst (bisect (S n)) = (b - a) / 2.
Proof.
  intros n a b Hab. cbn [bisect]. fold a b.
  destruct (Pdec ((a + b) / 2)); cbn [fst snd]; repeat split; lra.
Qed.

Lemma bisect_props : forall n,
  0 <= fst (bisect n) /\ fst (bisect n) <= fst (bisect (S n)) /\
  snd (bisect (S n)) <= snd (bisect n) /\ snd (bisect n) <= 1 /\
  snd (bisect n) - fst (bisect n) = / 2 ^ n.
Proof.
  assert (W : forall n, 0 <= fst (bisect n) /\ snd (bisect n) <= 1 /\
            snd (bisect n) - fst (bisect n) = / 2 ^ n).
  { induction n as [| k (H0 & H1 & H2)]; [ cbn; repeat split; lra | ].
    assert (Hp : 0 < / 2 ^ k) by (apply Rinv_0_lt_compat, pow_lt; lra).
    destruct (bisect_step k ltac:(lra)) as (S1 & S2 & S3).
    cbn [pow]. rewrite Rinv_mult. repeat split; lra. }
  intro n. destruct (W n) as (H0 & H1 & H2).
  assert (Hp : 0 < / 2 ^ n) by (apply Rinv_0_lt_compat, pow_lt; lra).
  destruct (bisect_step n ltac:(lra)) as (S1 & S2 & S3).
  repeat split; lra.
Qed.

Lemma bisect_ends : P 0 -> ~ P 1 -> forall n,
  P (fst (bisect n)) /\ ~ P (snd (bisect n)).
Proof.
  intros H0 H1. induction n as [| k IH]; cbn [bisect fst snd]; [ tauto | ].
  destruct (Pdec ((fst (bisect k) + snd (bisect k)) / 2)); cbn [fst snd]; tauto.
Qed.

Lemma bisect_point : { c : R | forall n,
  fst (bisect n) <= c <= snd (bisect n) }.
Proof.
  apply nested_intervals_limit.
  - intro n. apply (bisect_props n).
  - intro n. apply (bisect_props n).
  - intro n. destruct (bisect_props n) as (_ & _ & _ & _ & E).
    pose proof (pow_lt 2 n ltac:(lra)) as Hp.
    assert (0 < / 2 ^ n) by (apply Rinv_0_lt_compat; exact Hp). lra.
  - intros e He. destruct (inv_pos_lt e He) as [p Hp].
    exists (Pos.to_nat p).
    destruct (bisect_props (Pos.to_nat p)) as (_ & _ & _ & _ & ->).
    apply (Rle_lt_trans _ (/ IPR p)); [ | exact Hp ].
    apply inv_pow2_le_inv_IPR.
Qed.

End Bisect.

Theorem invariant_transport_along_path :
  forall (Q : Point -> Prop) (g : R -> Point),
    (forall pt : Point, {Q pt} + {~ Q pt}) ->
    (forall t, 0 <= t <= 1 ->
       exists d, 0 < d /\
         forall s, 0 <= s <= 1 -> Rabs (s - t) < d -> (Q (g s) <-> Q (g t))) ->
    (Q (g 0) <-> Q (g 1)).
Proof.
  intros Q g Qdec Hstab.
  set (P := fun t : R => Q (g t) <-> Q (g 0)).
  assert (Pdec : forall t, {P t} + {~ P t}).
  { intro t. unfold P.
    destruct (Qdec (g t)), (Qdec (g 0)); [ left | right | right | left ]; tauto. }
  destruct (Pdec 1) as [H1 | H1]; [ unfold P in H1; tauto | exfalso ].
  assert (H0 : P 0) by (unfold P; tauto).
  destruct (bisect_point P Pdec) as [c Hc].
  pose proof (Hc O) as Hc0. cbn [bisect fst snd] in Hc0.
  destruct (Hstab c Hc0) as [d [Hd Hball]].
  destruct (inv_pos_lt d Hd) as [p Hp].
  set (n := Pos.to_nat p).
  destruct (bisect_props P Pdec n) as (Ha0 & _ & _ & Hb1 & Ew).
  destruct (bisect_ends P Pdec H0 H1 n) as [Pa Pb].
  pose proof (Hc n) as [Hac Hcb].
  pose proof (inv_pow2_le_inv_IPR p) as Hw. fold n in Hw.
  set (a := fst (bisect P Pdec n)) in *. set (b := snd (bisect P Pdec n)) in *.
  assert (Ha : Q (g a) <-> Q (g c)).
  { apply Hball; [ lra | ].
    unfold Rabs; destruct (Rcase_abs (a - c)); lra. }
  assert (Hb : Q (g b) <-> Q (g c)).
  { apply Hball; [ lra | ].
    unfold Rabs; destruct (Rcase_abs (b - c)); lra. }
  unfold P in Pa, Pb. tauto.
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
