(* ============================================================================
   NetTopologySuite.Proofs.PolarTriangleProduct
   ----------------------------------------------------------------------------
   claimId `polar-tri-27-4`.  Planar Mahler for triangles (classical: Mahler
   1939; the general planar bound is NOT claimed here).  For a triangle T with
   area2 T > 0 and an interior point z with barycentric weights l1, l2, l3 > 0
   (l1 + l2 + l3 = 1), let T* be the triangle of the poles of T's edge lines
   with respect to z (`polar_vertex`: the point v with v.(a - z) = 1 and
   v.(b - z) = 1).  Classically T* is the polar body of T - z; that duality is
   not proved here, so the names say pole triangle, not polar body.
     triangle_polar_product         area T * area T* = 1 / (4 l1 l2 l3)
     triangle_polar_product_ge      27/4 <= area T * area T*
     triangle_polar_product_eq_iff  equality iff z is the centroid
   Q twin `q_polar_product` computes every pole vertex and both shoelaces and
   agrees with the R product (`q_polar_product_R`); the fixtures evaluate it
   (27/4 at the centroid, 8 off it), nothing is pinned.

   Consumer today: none (a possible ConvexHull property-test oracle).  Idea
   from openai/math@1581d4cb gem 087; nothing from that catalogue is cited as
   proved.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
   ========================================================================== *)

From Stdlib Require Import Reals Lra Psatz QArith Qreals.
From NTS.Proofs Require Import Distance Orientation Triangle.
Local Open Scope R_scope.

Definition bary (t : Triangle) (l1 l2 l3 : R) : Point :=
  mkPoint (l1 * px (tA t) + l2 * px (tB t) + l3 * px (tC t))
          (l1 * py (tA t) + l2 * py (tB t) + l3 * py (tC t)).

Definition polar_vertex (z a b : Point) : Point :=
  let ax := px a - px z in let ay := py a - py z in
  let bx := px b - px z in let by_ := py b - py z in
  let d := ax * by_ - ay * bx in
  mkPoint ((by_ - ay) / d) ((ax - bx) / d).

(* The triangle of the edge-line poles of t with respect to z. *)
Definition polar_triangle (t : Triangle) (z : Point) : Triangle :=
  mkTriangle (polar_vertex z (tA t) (tB t)) (polar_vertex z (tB t) (tC t))
             (polar_vertex z (tC t) (tA t)).

(* Area of t times area of its pole triangle (area = area2 / 2). *)
Definition polar_product (t : Triangle) (z : Point) : R :=
  (area2 t / 2) * (area2 (polar_triangle t z) / 2).

Theorem triangle_polar_product : forall t l1 l2 l3,
  0 < area2 t -> 0 < l1 -> 0 < l2 -> 0 < l3 -> l1 + l2 + l3 = 1 ->
  polar_product t (bary t l1 l2 l3) = / (4 * (l1 * l2 * l3)).
Proof.
  intros [[ax ay] [bx by_] [cx cy]] l1 l2 l3 Ha H1 H2 H3 Hs.
  unfold polar_product, polar_triangle, polar_vertex, bary, area2, cross in *.
  cbn [tA tB tC px py] in *. cbv zeta.
  set (D := (bx - ax) * (cy - ay) - (cx - ax) * (by_ - ay)) in *.
  replace l3 with (1 - l1 - l2) in * by lra.
  assert (E1 : (ax - (l1 * ax + l2 * bx + (1 - l1 - l2) * cx)) * (by_ - (l1 * ay + l2 * by_ + (1 - l1 - l2) * cy))
             - (ay - (l1 * ay + l2 * by_ + (1 - l1 - l2) * cy)) * (bx - (l1 * ax + l2 * bx + (1 - l1 - l2) * cx))
             = (1 - l1 - l2) * D) by (unfold D; ring).
  assert (E2 : (bx - (l1 * ax + l2 * bx + (1 - l1 - l2) * cx)) * (cy - (l1 * ay + l2 * by_ + (1 - l1 - l2) * cy))
             - (by_ - (l1 * ay + l2 * by_ + (1 - l1 - l2) * cy)) * (cx - (l1 * ax + l2 * bx + (1 - l1 - l2) * cx))
             = l1 * D) by (unfold D; ring).
  assert (E3 : (cx - (l1 * ax + l2 * bx + (1 - l1 - l2) * cx)) * (ay - (l1 * ay + l2 * by_ + (1 - l1 - l2) * cy))
             - (cy - (l1 * ay + l2 * by_ + (1 - l1 - l2) * cy)) * (ax - (l1 * ax + l2 * bx + (1 - l1 - l2) * cx))
             = l2 * D) by (unfold D; ring).
  rewrite E1, E2, E3. unfold D in *.
  field. repeat split; try lra.
Qed.

Lemma cube_minus_27_sos : forall x y z,
  (x + y + z) ^ 3 - 27 * (x * y * z)
  = (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) / 2
    + 3 * (x * (y - z) ^ 2 + y * (z - x) ^ 2 + z * (x - y) ^ 2).
Proof. intros. field. Qed.

Lemma bary_weights_product_le : forall x y z,
  0 < x -> 0 < y -> 0 < z -> x + y + z = 1 -> 27 * (x * y * z) <= 1.
Proof.
  intros x y z Hx Hy Hz Hs.
  pose proof (cube_minus_27_sos x y z) as E. rewrite Hs in E.
  pose proof (pow2_ge_0 (x - y)). pose proof (pow2_ge_0 (y - z)).
  pose proof (pow2_ge_0 (z - x)).
  pose proof (Rmult_le_pos x ((y - z) ^ 2) ltac:(lra) ltac:(assumption)).
  pose proof (Rmult_le_pos y ((z - x) ^ 2) ltac:(lra) ltac:(assumption)).
  pose proof (Rmult_le_pos z ((x - y) ^ 2) ltac:(lra) ltac:(assumption)).
  replace (1 ^ 3) with 1 in E by ring. lra.
Qed.

Lemma bary_weights_product_eq_iff : forall x y z,
  0 < x -> 0 < y -> 0 < z -> x + y + z = 1 ->
  (27 * (x * y * z) = 1 <-> x = 1 / 3 /\ y = 1 / 3).
Proof.
  intros x y z Hx Hy Hz Hs. split.
  - intro He.
    pose proof (cube_minus_27_sos x y z) as E. rewrite Hs, He in E.
    pose proof (pow2_ge_0 (x - y)). pose proof (pow2_ge_0 (y - z)).
    pose proof (pow2_ge_0 (z - x)).
    pose proof (Rmult_le_pos x ((y - z) ^ 2) ltac:(lra) ltac:(assumption)).
    pose proof (Rmult_le_pos y ((z - x) ^ 2) ltac:(lra) ltac:(assumption)).
    pose proof (Rmult_le_pos z ((x - y) ^ 2) ltac:(lra) ltac:(assumption)).
    assert (Hxy : (x - y) ^ 2 = 0) by (replace (1 ^ 3) with 1 in E by ring; lra).
    assert (Hyz : (y - z) ^ 2 = 0) by (replace (1 ^ 3) with 1 in E by ring; lra).
    assert (x = y) by nra. assert (y = z) by nra. lra.
  - intros [-> ->]. replace z with (1 / 3) by lra. field.
Qed.

Theorem triangle_polar_product_ge : forall t l1 l2 l3,
  0 < area2 t -> 0 < l1 -> 0 < l2 -> 0 < l3 -> l1 + l2 + l3 = 1 ->
  27 / 4 <= polar_product t (bary t l1 l2 l3).
Proof.
  intros t l1 l2 l3 Ha H1 H2 H3 Hs.
  rewrite (triangle_polar_product t l1 l2 l3 Ha H1 H2 H3 Hs).
  pose proof (bary_weights_product_le l1 l2 l3 H1 H2 H3 Hs) as Hle.
  assert (Hp : 0 < l1 * l2 * l3) by (apply Rmult_lt_0_compat; [nra | exact H3]).
  apply (Rmult_le_reg_l (4 * (l1 * l2 * l3))); [lra|].
  rewrite Rinv_r by lra. lra.
Qed.

Theorem triangle_polar_product_eq_iff : forall t l1 l2 l3,
  0 < area2 t -> 0 < l1 -> 0 < l2 -> 0 < l3 -> l1 + l2 + l3 = 1 ->
  (polar_product t (bary t l1 l2 l3) = 27 / 4 <-> l1 = 1 / 3 /\ l2 = 1 / 3).
Proof.
  intros t l1 l2 l3 Ha H1 H2 H3 Hs.
  rewrite (triangle_polar_product t l1 l2 l3 Ha H1 H2 H3 Hs).
  rewrite <- (bary_weights_product_eq_iff l1 l2 l3 H1 H2 H3 Hs).
  assert (Hp : 0 < l1 * l2 * l3) by (apply Rmult_lt_0_compat; [nra | exact H3]).
  split; intro H.
  - apply (f_equal Rinv) in H. rewrite Rinv_inv in H.
    replace (/ (27 / 4)) with (4 / 27) in H by field. lra.
  - replace (4 * (l1 * l2 * l3)) with (4 / 27) by lra. field.
Qed.

(* -------------------------------------------------------------------------- *)
(* Q twin: every vertex, both shoelaces and the product are computed.          *)
(* -------------------------------------------------------------------------- *)

Local Open Scope Q_scope.

Definition qcross2 (p0 p1 q : Q * Q) : Q :=
  (fst p1 - fst p0) * (snd q - snd p0) - (fst q - fst p0) * (snd p1 - snd p0).

Definition q_polar_d (z a b : Q * Q) : Q :=
  (fst a - fst z) * (snd b - snd z) - (snd a - snd z) * (fst b - fst z).

Definition q_polar_vertex (z a b : Q * Q) : Q * Q :=
  (((snd b - snd z) - (snd a - snd z)) / q_polar_d z a b,
   ((fst a - fst z) - (fst b - fst z)) / q_polar_d z a b).

Definition q_polar_product (A B C z : Q * Q) : Q :=
  (qcross2 A B C / 2)
  * (qcross2 (q_polar_vertex z A B) (q_polar_vertex z B C) (q_polar_vertex z C A) / 2).

Local Close Scope Q_scope.

Definition qpair_R (p : Q * Q) : Point := mkPoint (Q2R (fst p)) (Q2R (snd p)).

Lemma Q2R_two : Q2R 2 = 2.
Proof. unfold Q2R. simpl. field. Qed.

Lemma q_polar_vertex_R : forall z a b, ~ (q_polar_d z a b == 0)%Q ->
  qpair_R (q_polar_vertex z a b) = polar_vertex (qpair_R z) (qpair_R a) (qpair_R b).
Proof.
  intros z a b Hd. unfold q_polar_vertex, polar_vertex, qpair_R. cbn [fst snd px py].
  rewrite !Q2R_div by exact Hd. unfold q_polar_d.
  rewrite !Q2R_minus, !Q2R_mult, !Q2R_minus. reflexivity.
Qed.

Lemma q_polar_product_R : forall A B C z,
  ~ (q_polar_d z A B == 0)%Q -> ~ (q_polar_d z B C == 0)%Q -> ~ (q_polar_d z C A == 0)%Q ->
  Q2R (q_polar_product A B C z)
  = polar_product (mkTriangle (qpair_R A) (qpair_R B) (qpair_R C)) (qpair_R z).
Proof.
  intros A B C z H1 H2 H3. unfold q_polar_product, polar_product, polar_triangle.
  cbn [tA tB tC]. rewrite <- !q_polar_vertex_R by assumption.
  assert (H20 : ~ (2 == 0)%Q) by discriminate.
  rewrite Q2R_mult, !Q2R_div by exact H20. rewrite Q2R_two.
  unfold area2, qcross2, cross, qpair_R. cbn [tA tB tC px py fst snd].
  rewrite !Q2R_minus, !Q2R_mult, !Q2R_minus. reflexivity.
Qed.

(* Right triangle (0,0),(1,0),(0,1): 27/4 at the centroid, 8 at weights (1/2,1/4,1/4). *)
Lemma right_tri_centroid_fixtures :
  (q_polar_product (0, 0) (1, 0) (0, 1) (1 # 3, 1 # 3) == 27 # 4)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma right_tri_offcentre_fixtures :
  (q_polar_product (0, 0) (1, 0) (0, 1) (1 # 4, 1 # 4) == 8)%Q.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions triangle_polar_product.
Print Assumptions cube_minus_27_sos.
Print Assumptions bary_weights_product_le.
Print Assumptions bary_weights_product_eq_iff.
Print Assumptions triangle_polar_product_ge.
Print Assumptions triangle_polar_product_eq_iff.
Print Assumptions Q2R_two.
Print Assumptions q_polar_vertex_R.
Print Assumptions q_polar_product_R.
Print Assumptions right_tri_centroid_fixtures.
Print Assumptions right_tri_offcentre_fixtures.
