(* ============================================================================
   NetTopologySuite.Proofs.PerronStage
   ----------------------------------------------------------------------------
   Finite, polygonal Perron-tree stages — Phase A of the Besicovitch–Kakeya
   plan (docs/besicovitch-kakeya-plan.md).

   PHILOSOPHY (do not overclaim).  We do NOT prove the Kakeya conjecture, that
   the limit set has Lebesgue measure zero, or anything measure-theoretic.
   Those need machinery the corpus does not have yet (Lebesgue outer measure,
   countable intersections) and are deferred to Phase D.  What we build here is
   a concrete, FINITE, POLYGONAL object that is fully compatible with the
   existing `Ring` / `Overlay` / orientation machinery:

     `perron_stage n : list Ring`

   the n-th stage of the construction's elementary figure — the apex-fan over a
   unit base subdivided into `2^n` equal pieces.  Stage `n` is a finite
   collection of `2^n` triangles (each a closed `Ring`), whose union is the
   master triangle.  This is the figure the Perron-tree area-reduction *starts
   from*; the area-reducing translations (the actual "tree") and the area -> 0
   analysis belong to Phase D and are NOT done here.

   What IS proved at each finite stage `n`:
     - exactly `2^n` triangles (`perron_stage_length`);
     - every triangle is a closed `Ring` with the minimum vertex count, so the
       DCEL / ray-parity machinery applies (`perron_stage_rings_valid`);
     - every triangle is non-degenerate (`perron_tri_nondegenerate`), with
       signed area `1 / 2^n` (`perron_tri_area`);
     - DIRECTION COVERAGE: the `2^n` triangles carry `2^n` pairwise
       NON-PARALLEL directions (`perron_stage_directions_distinct`), the honest
       finite-stage analogue of "segments in many directions";
     - the whole stage sits in the closed unit square (`perron_stage_in_unit_square`);
     - a Phase-D hook: those directions are invariant under the sliding
       translations the area-reduction uses (`perron_dir_translation_invariant`).

   Pure-R; three-axiom footprint.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List.
From NTS.Proofs Require Import Distance Orientation Overlay.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The elementary figure.                                                 *)
(*                                                                            *)
(* The master triangle has apex (1/2, 1) over the unit base [0,1] x {0}.      *)
(* Stage `n` subdivides the base into `2^n` equal pieces; sub-triangle `k`    *)
(* is (apex, B_k, B_{k+1}) where B_k = (k / 2^n, 0).                          *)
(* -------------------------------------------------------------------------- *)

(* The fixed apex, above the midpoint of the unit base. *)
Definition apex : Point := mkPoint (1 / 2) 1.

(* The k-th of N+1 equally spaced points along the unit base [0,1] x {0}. *)
Definition base_pt (N k : nat) : Point := mkPoint (INR k / INR N) 0.

(* A triangle, packaged as a closed ring [A; B; C; A]. *)
Definition tri_ring (A B C : Point) : Ring := A :: B :: C :: A :: nil.

(* Number of sub-triangles at stage n: 2^n. *)
Definition stage_count (n : nat) : nat := (2 ^ n)%nat.

(* The k-th sub-triangle of stage n (intended for k in 0 .. 2^n - 1). *)
Definition perron_tri (n k : nat) : Ring :=
  tri_ring apex (base_pt (stage_count n) k) (base_pt (stage_count n) (S k)).

(* Stage n: the finite collection of all 2^n sub-triangles, as `list Ring`. *)
Definition perron_stage (n : nat) : list Ring :=
  map (perron_tri n) (seq 0 (stage_count n)).

(* -------------------------------------------------------------------------- *)
(* §2  Counting facts.                                                        *)
(* -------------------------------------------------------------------------- *)

Lemma stage_count_pos : forall n, (0 < stage_count n)%nat.
Proof. intros n. unfold stage_count. induction n; simpl; lia. Qed.

Lemma INR_stage_count_neq : forall n, INR (stage_count n) <> 0.
Proof.
  intros n. apply not_0_INR. pose proof (stage_count_pos n). lia.
Qed.

(* Stage n is exactly 2^n triangles. *)
Lemma perron_stage_length : forall n,
  length (perron_stage n) = (2 ^ n)%nat.
Proof.
  intros n. unfold perron_stage, stage_count.
  rewrite length_map, length_seq. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Structural invariants (Ring closure, minimum vertices, edge count).    *)
(* These are exactly the hypotheses the DCEL / ray-parity machinery needs.    *)
(* -------------------------------------------------------------------------- *)

Lemma perron_tri_closed : forall n k, ring_closed (perron_tri n k).
Proof.
  intros n k. unfold ring_closed.
  exists apex,
    (base_pt (stage_count n) k :: base_pt (stage_count n) (S k) :: nil).
  unfold perron_tri, tri_ring. reflexivity.
Qed.

Lemma perron_tri_min_points : forall n k,
  ring_has_minimum_points (perron_tri n k).
Proof.
  intros n k. unfold ring_has_minimum_points, perron_tri, tri_ring.
  simpl. lia.
Qed.

(* Each triangle has exactly three edges. *)
Lemma perron_tri_edges_count : forall n k,
  length (ring_edges (perron_tri n k)) = 3%nat.
Proof.
  intros n k. unfold perron_tri, tri_ring.
  cbn [ring_edges length]. reflexivity.
Qed.

(* Every ring of the stage is closed and has the minimum vertex count, so it is
   a legitimate input to `point_in_ring`, `ring_edges`, and the overlay DCEL. *)
Theorem perron_stage_rings_valid : forall n r,
  In r (perron_stage n) ->
  ring_closed r /\ ring_has_minimum_points r.
Proof.
  intros n r Hr. unfold perron_stage in Hr.
  apply in_map_iff in Hr. destruct Hr as [k [Hk _]]. subst r.
  split; [ apply perron_tri_closed | apply perron_tri_min_points ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Orientation: signed area and non-degeneracy.                           *)
(*                                                                            *)
(* `cross apex B_k B_j` is the signed area of (apex, B_k, B_j); since the      *)
(* base points are collinear it equals (j - k) / 2^n, which also equals the    *)
(* 2D cross product of the two apex-rays (B_k - apex) and (B_j - apex).        *)
(* -------------------------------------------------------------------------- *)

Lemma base_cross_value : forall N j k, INR N <> 0 ->
  cross apex (base_pt N k) (base_pt N j) = (INR j - INR k) / INR N.
Proof.
  intros N j k HN. unfold cross, apex, base_pt; cbn [px py]. field; exact HN.
Qed.

(* Signed area of sub-triangle k is 1 / 2^n: positive, so the triangle is
   genuinely two-dimensional (and consistently oriented across the stage). *)
Lemma perron_tri_area : forall n k,
  cross apex (base_pt (stage_count n) k) (base_pt (stage_count n) (S k))
  = 1 / INR (stage_count n).
Proof.
  intros n k.
  rewrite base_cross_value by apply INR_stage_count_neq.
  rewrite S_INR.
  replace (INR k + 1 - INR k) with 1 by ring.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Direction coverage — the headline finite-stage Kakeya property.        *)
(*                                                                            *)
(* For distinct indices the two apex-rays are NON-PARALLEL (their cross        *)
(* product is non-zero).  Hence the 2^n sub-triangles of stage n carry 2^n     *)
(* pairwise-distinct directions: the honest, finite, polygonal analogue of     *)
(* "contains segments pointing in 2^n directions".                            *)
(* -------------------------------------------------------------------------- *)

Lemma base_dir_distinct : forall N j k,
  (0 < N)%nat -> j <> k ->
  cross apex (base_pt N k) (base_pt N j) <> 0.
Proof.
  intros N j k HN Hjk.
  assert (HN0 : INR N <> 0) by (apply not_0_INR; lia).
  rewrite base_cross_value by exact HN0.
  unfold Rdiv. intro H. apply Rmult_integral in H. destruct H as [H | H].
  - apply Hjk. apply INR_eq. lra.
  - exact (Rinv_neq_0_compat (INR N) HN0 H).
Qed.

(* Non-degeneracy of every sub-triangle: the cevian to its left base point and
   to its right base point are non-parallel. *)
Lemma perron_tri_nondegenerate : forall n k,
  cross apex (base_pt (stage_count n) k) (base_pt (stage_count n) (S k)) <> 0.
Proof.
  intros n k. apply base_dir_distinct; [ apply stage_count_pos | lia ].
Qed.

(* The headline: distinct triangles of a stage point in non-parallel
   directions.  Quantified over all distinct indices, so the 2^n triangles of
   stage n exhibit 2^n pairwise-distinct directions. *)
Theorem perron_stage_directions_distinct : forall n j k,
  j <> k ->
  cross apex (base_pt (stage_count n) k) (base_pt (stage_count n) j) <> 0.
Proof.
  intros n j k Hjk.
  apply base_dir_distinct; [ apply stage_count_pos | exact Hjk ].
Qed.

(* The base points themselves are distinct (injectivity of `base_pt` in the
   index), confirming the 2^n directions are realised by 2^n distinct rays. *)
Lemma base_pt_inj : forall N k j, (0 < N)%nat ->
  base_pt N k = base_pt N j -> k = j.
Proof.
  intros N k j HN Heq.
  assert (HN0 : INR N <> 0) by (apply not_0_INR; lia).
  assert (Hx : INR k / INR N = INR j / INR N).
  { apply (f_equal px) in Heq. unfold base_pt in Heq. cbn [px] in Heq. exact Heq. }
  apply INR_eq.
  apply (Rmult_eq_reg_r (/ INR N)).
  - unfold Rdiv in Hx. exact Hx.
  - apply Rinv_neq_0_compat; exact HN0.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Boundedness — the stage lies in the closed unit square.                *)
(* -------------------------------------------------------------------------- *)

Lemma quotient_in_01 : forall N k, (k <= N)%nat -> (0 < N)%nat ->
  0 <= INR k / INR N <= 1.
Proof.
  intros N k Hkn HN.
  pose proof (pos_INR k) as Hk.
  pose proof (lt_0_INR N HN) as HN'.
  pose proof (le_INR k N Hkn) as Hle.
  pose proof (Rinv_0_lt_compat (INR N) HN') as Hinv.
  unfold Rdiv. split.
  - apply Rmult_le_pos; lra.
  - rewrite <- (Rinv_r (INR N)) by lra.
    apply Rmult_le_compat_r; lra.
Qed.

Theorem perron_stage_in_unit_square : forall n r v,
  In r (perron_stage n) -> In v r ->
  0 <= px v <= 1 /\ 0 <= py v <= 1.
Proof.
  intros n r v Hr Hv.
  unfold perron_stage in Hr.
  apply in_map_iff in Hr. destruct Hr as [k [Hk Hin]].
  apply in_seq in Hin. destruct Hin as [_ Hklt].
  subst r. unfold perron_tri, tri_ring in Hv. cbn [In] in Hv.
  destruct Hv as [Hv | [Hv | [Hv | [Hv | []]]]]; subst v.
  - unfold apex; cbn [px py]; lra.
  - unfold base_pt; cbn [px py]. split.
    + apply quotient_in_01; [ lia | apply stage_count_pos ].
    + lra.
  - unfold base_pt; cbn [px py]. split.
    + apply quotient_in_01; [ lia | apply stage_count_pos ].
    + lra.
  - unfold apex; cbn [px py]; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  Phase-D hook: the sliding translations preserve direction.             *)
(*                                                                            *)
(* The Perron-tree area reduction slides each sub-triangle rigidly along the   *)
(* base line.  Translation leaves the apex-ray cross product unchanged, so the *)
(* direction set is invariant under the (future) area-reducing moves — the     *)
(* exact reason the directions survive while the area shrinks.  Immediate from *)
(* `Orientation.cross_translation_invariant`.                                  *)
(* -------------------------------------------------------------------------- *)

Lemma perron_dir_translation_invariant : forall n j k dx dy,
  cross (translate apex dx dy)
        (translate (base_pt (stage_count n) k) dx dy)
        (translate (base_pt (stage_count n) j) dx dy)
  = cross apex (base_pt (stage_count n) k) (base_pt (stage_count n) j).
Proof.
  intros. apply cross_translation_invariant.
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions perron_stage_length.
Print Assumptions perron_stage_rings_valid.
Print Assumptions perron_stage_directions_distinct.
Print Assumptions perron_stage_in_unit_square.
