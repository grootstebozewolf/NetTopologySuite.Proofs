(* ==========================================================================
   EdgeCrossParity.v

   Phase B step 3a of the H_bridge geometric/JCT route (Rung 3b-iv).

   Single-edge parity flip: if two points `p1`, `p2` agree on the half-open
   ray-crossing status of every edge of a list EXCEPT one distinguished edge
   `d` (which exactly one of them crosses), then their half-open ray parities
   over the whole list are OPPOSITE.  This is the purely combinatorial heart of
   the "two points straddling a single ring edge have opposite point-in-ring
   parity" step: it isolates the contribution of `d` from all other edges.

   Proved through the nat crossing count `ho_count` (JCTEscapeDescent.v) and its
   parity bridge `ho_count_parity`: equal per-edge crossings give equal partial
   counts, the single straddled edge shifts the total count by exactly one, so
   the two parities differ.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Arith Lia.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents
                               PointInRingCorrect JCTHalfOpenParity
                               JCTGenericStability JCTEscapeDescent.

Import ListNotations.
Local Open Scope R_scope.

(* Two naturals summing to an odd number have opposite parity. *)
Lemma odd_even_of_sum_odd : forall a b n : nat,
  (a + b = 2 * n + 1)%nat -> (Nat.Odd a <-> Nat.Even b).
Proof.
  intros a b n H. split.
  - intros [i Hi]. exists (n - i)%nat. lia.
  - intros [j Hj]. exists (n - j)%nat. lia.
Qed.

(* `ho_count` is additive over list concatenation. *)
Lemma ho_count_app : forall p l1 l2,
  ho_count p (l1 ++ l2) = (ho_count p l1 + ho_count p l2)%nat.
Proof.
  intros p l1 l2. induction l1 as [| e l1 IH]; cbn [ho_count app]; [ reflexivity | ].
  rewrite IH. lia.
Qed.

(* If two points cross every edge of a list identically, their counts agree. *)
Lemma ho_count_agree : forall p1 p2 l,
  (forall e, In e l -> (edge_crosses_ray_ho p1 e <-> edge_crosses_ray_ho p2 e)) ->
  ho_count p1 l = ho_count p2 l.
Proof.
  intros p1 p2 l H. induction l as [| e l IH]; [ reflexivity | ].
  cbn [ho_count].
  assert (Heq : (if edge_crosses_ray_ho_dec p1 e then 1 else 0)%nat
              = (if edge_crosses_ray_ho_dec p2 e then 1 else 0)%nat).
  { destruct (edge_crosses_ray_ho_dec p1 e) as [c1 | n1];
    destruct (edge_crosses_ray_ho_dec p2 e) as [c2 | n2]; try reflexivity.
    - exfalso. apply n2. apply (H e (or_introl eq_refl)). exact c1.
    - exfalso. apply n1. apply (H e (or_introl eq_refl)). exact c2. }
  rewrite Heq, IH; [ reflexivity | ].
  intros e' Hin. apply H. right. exact Hin.
Qed.

(* Step 3a, count form: agree off `d`, opposite on `d`  ==>  opposite parity. *)
Lemma ho_parity_flip_split : forall p1 p2 pre suf d,
  (forall e, In e (pre ++ suf) ->
     (edge_crosses_ray_ho p1 e <-> edge_crosses_ray_ho p2 e)) ->
  (edge_crosses_ray_ho p1 d <-> ~ edge_crosses_ray_ho p2 d) ->
  (ho_parity_odd p1 (pre ++ d :: suf) <-> ho_parity_even p2 (pre ++ d :: suf)).
Proof.
  intros p1 p2 pre suf d Hagree Hopp.
  set (es := pre ++ d :: suf).
  (* decompose both counts *)
  assert (Hc1 : ho_count p1 es
    = (ho_count p1 pre + ((if edge_crosses_ray_ho_dec p1 d then 1 else 0)
                          + ho_count p1 suf))%nat).
  { unfold es. rewrite ho_count_app. cbn [ho_count]. reflexivity. }
  assert (Hc2 : ho_count p2 es
    = (ho_count p2 pre + ((if edge_crosses_ray_ho_dec p2 d then 1 else 0)
                          + ho_count p2 suf))%nat).
  { unfold es. rewrite ho_count_app. cbn [ho_count]. reflexivity. }
  assert (Hpre : ho_count p1 pre = ho_count p2 pre).
  { apply ho_count_agree. intros e He. apply Hagree, in_or_app. left. exact He. }
  assert (Hsuf : ho_count p1 suf = ho_count p2 suf).
  { apply ho_count_agree. intros e He. apply Hagree, in_or_app. right. exact He. }
  (* the straddled edge shifts the count by exactly one *)
  assert (Hd : ((if edge_crosses_ray_ho_dec p1 d then 1 else 0)
              + (if edge_crosses_ray_ho_dec p2 d then 1 else 0))%nat = 1%nat).
  { destruct (edge_crosses_ray_ho_dec p1 d) as [c1 | n1];
    destruct (edge_crosses_ray_ho_dec p2 d) as [c2 | n2].
    - exfalso. exact (proj1 Hopp c1 c2).
    - reflexivity.
    - reflexivity.
    - exfalso. apply n1. apply (proj2 Hopp). exact n2. }
  (* hence the two total counts sum to an odd number *)
  assert (Hsum : (ho_count p1 es + ho_count p2 es
                  = 2 * (ho_count p2 pre + ho_count p2 suf) + 1)%nat).
  { rewrite Hc1, Hc2, Hpre, Hsuf. lia. }
  (* convert count parity to inductive parity *)
  destruct (ho_count_parity p1 es) as [_ Ho1].
  destruct (ho_count_parity p2 es) as [He2 _].
  rewrite <- Ho1, <- He2.
  apply (odd_even_of_sum_odd _ _ _ Hsum).
Qed.

(* Step 3a, ring form: a single straddled ring edge flips point-in-ring parity
   (under the standard ray-avoids-vertices guards bridging `ho` and strict). *)
Lemma point_in_ring_flip_one_edge : forall p1 p2 r pre suf d,
  ring_edges r = pre ++ d :: suf ->
  ray_avoids_vertices p1 r ->
  ray_avoids_vertices p2 r ->
  (forall e, In e (pre ++ suf) ->
     (edge_crosses_ray_ho p1 e <-> edge_crosses_ray_ho p2 e)) ->
  (edge_crosses_ray_ho p1 d <-> ~ edge_crosses_ray_ho p2 d) ->
  (point_in_ring p1 r <-> ~ point_in_ring p2 r).
Proof.
  intros p1 p2 r pre suf d Hsplit Hav1 Hav2 Hagree Hopp.
  pose proof (ho_parity_flip_split p1 p2 pre suf d Hagree Hopp) as Hflip.
  rewrite <- Hsplit in Hflip.
  (* Hflip : ho_parity_odd p1 (ring_edges r) <-> ho_parity_even p2 (ring_edges r) *)
  rewrite <- (point_in_ring_ho_agrees p1 r Hav1).
  rewrite <- (point_in_ring_ho_agrees p2 r Hav2).
  unfold point_in_ring_ho.
  split.
  - intros Hp1 Hp2. exact (ho_parity_excl p2 (ring_edges r) Hp2 (proj1 Hflip Hp1)).
  - intros Hp1.
    destruct (ho_parity_dec p1 (ring_edges r)) as [Ho | He]; [ exact Ho | ].
    exfalso. apply Hp1.
    destruct (ho_parity_dec p2 (ring_edges r)) as [Ho2 | He2]; [ exact Ho2 | ].
    (* p1 even and p2 even: but flip says p2-even -> p1-odd, contradiction *)
    exfalso. apply proj2 in Hflip.
    exact (ho_parity_excl p1 (ring_edges r) (Hflip He2) He).
Qed.

(* ==========================================================================
   Phase B step 3b (arithmetic core): straddle-crossing of one edge.

   For a non-horizontal edge `(a,b)` and an interior ray height `my`, let `X`
   be the exact abscissa where the edge meets the height-`my` ray (the zero of
   the affine crossing form).  Then a point just LEFT of `X` (at `X - eps`)
   crosses the edge and a point just RIGHT (`X + eps`) does not.  This is the
   per-edge half of "two straddle points have opposite parity": combined with
   `point_in_ring_flip_one_edge` (all OTHER edges agreeing), it flips parity.
   ========================================================================== *)

(* Ascending edge (py a < py b). *)
Lemma cross_ho_straddle_zero_asc : forall (a b : Point) (my X eps : R),
  py a < py b ->
  py a <= my < py b ->
  (py b - py a) * (px a - X) + (px b - px a) * (my - py a) = 0 ->
  0 < eps ->
  edge_crosses_ray_ho (mkPoint (X - eps) my) (a, b) /\
  ~ edge_crosses_ray_ho (mkPoint (X + eps) my) (a, b).
Proof.
  intros a b my X eps Hab Hrange Hzero Heps. split.
  - apply (ho_asc_iff a b (mkPoint (X - eps) my) Hab).
    cbn [px py]. split; [ exact Hrange | ]. nra.
  - intro Hc. apply (ho_asc_iff a b (mkPoint (X + eps) my) Hab) in Hc.
    cbn [px py] in Hc. destruct Hc as [_ HP]. nra.
Qed.

(* Descending edge (py b < py a). *)
Lemma cross_ho_straddle_zero_desc : forall (a b : Point) (my X eps : R),
  py b < py a ->
  py b <= my < py a ->
  (py a - py b) * (px b - X) + (px a - px b) * (my - py b) = 0 ->
  0 < eps ->
  edge_crosses_ray_ho (mkPoint (X - eps) my) (a, b) /\
  ~ edge_crosses_ray_ho (mkPoint (X + eps) my) (a, b).
Proof.
  intros a b my X eps Hab Hrange Hzero Heps. split.
  - apply (ho_desc_iff a b (mkPoint (X - eps) my) Hab).
    cbn [px py]. split; [ exact Hrange | ]. nra.
  - intro Hc. apply (ho_desc_iff a b (mkPoint (X + eps) my) Hab) in Hc.
    cbn [px py] in Hc. destruct Hc as [_ HP]. nra.
Qed.
