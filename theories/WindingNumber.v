(* ============================================================================
   NetTopologySuite.Proofs.WindingNumber
   ----------------------------------------------------------------------------
   A WINDING NUMBER VERIFICATION MECHANISM (atan2-free, Z-valued).

   PointInRingCorrect.v §5 deferred a winding number, assuming it needs atan2 /
   Coquelicot (not installed).  That is avoidable: the standard practical winding
   number is the SIGNED ray-crossing count (Sunday's algorithm) -- a directed ring
   edge crossing the rightward ray from p contributes +1 if it crosses UPWARD and
   -1 if DOWNWARD; the sum is the winding number.  It needs only the orientation
   already implicit in segment_crosses_ray (no transcendentals), is Z-valued by
   construction, and -- because +1 and -1 are both odd -- its PARITY equals the
   parity of the unsigned crossing count.  Hence it reflects the corpus's existing
   ray-casting membership test exactly:

     winding_decides_membership : no_horizontal_edge_at p r ->
       (Z.odd (winding_number p r) = true  <->  point_in_ring p r)

   i.e. a verified winding-number decision procedure for point-in-ring.

   Honest scope: the VERIFIED property is that winding parity decides membership
   (equivalent to point_in_ring).  The full {-1,0,+1} characterisation for SIMPLE
   polygons (winding +/-1 inside, 0 outside) is the global simple-polygon geometry
   and remains the deferred next rung -- NOT claimed here, and NOT admitted.

   Pure-R + Z parity; classical-reals trio only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra ZArith List Bool.
Import ListNotations.
From NTS.Proofs Require Import Distance Overlay PointInRingCorrect.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Signed per-edge contribution and the winding number.                   *)
(*                                                                            *)
(* When segment_crosses_ray fires it is via a strict y-straddle: either       *)
(* py A < py p < py B (UPWARD, +1) or py B < py p < py A (DOWNWARD, -1).  The  *)
(* sign is therefore `Rlt_b (py A) (py B)`.  Non-crossing edges contribute 0.  *)
(* -------------------------------------------------------------------------- *)
Definition edge_winding (p : Point) (e : Edge) : Z :=
  let '(A, B) := e in
  if segment_crosses_ray p A B
  then (if Rlt_b (py A) (py B) then 1 else -1)%Z
  else 0%Z.

Definition winding_number (p : Point) (r : Ring) : Z :=
  fold_left (fun acc e => (acc + edge_winding p e)%Z) (ring_edges r) 0%Z.

(* Each edge contributes exactly one of {0, +1, -1} -- useful for extraction and
   for any sign/bound reasoning over the winding sum. *)
Lemma edge_winding_triple : forall (p : Point) (e : Edge),
  edge_winding p e = 0%Z \/ edge_winding p e = 1%Z \/ edge_winding p e = (-1)%Z.
Proof.
  intros p [A B]. unfold edge_winding.
  destruct (segment_crosses_ray p A B); [ destruct (Rlt_b (py A) (py B)) | ]; auto.
Qed.

(* The computable verification mechanism: winding parity. *)
Definition winding_in_ring_b (p : Point) (r : Ring) : bool :=
  Z.odd (winding_number p r).

(* -------------------------------------------------------------------------- *)
(* §2  Parity bridge: signed winding count and unsigned crossing count agree   *)
(* mod 2 (each crossing edge flips both parities; non-crossing edges flip      *)
(* neither).  Proved by induction over the edge list with BOTH accumulators    *)
(* generalised, mirroring count_crossings_ray's fold.                          *)
(* -------------------------------------------------------------------------- *)
Lemma winding_crossing_parity_aux : forall (p : Point) (es : list Edge) (zacc : Z) (nacc : nat),
  Z.odd zacc = Nat.odd nacc ->
  Z.odd (fold_left (fun acc e => (acc + edge_winding p e)%Z) es zacc)
  = Nat.odd (fold_left
      (fun acc e => let '(A, B) := e in
                    if segment_crosses_ray p A B then S acc else acc) es nacc).
Proof.
  intros p es. induction es as [| e es' IH]; intros zacc nacc Hpar.
  - cbn [fold_left]. exact Hpar.
  - cbn [fold_left]. destruct e as [A B]. apply IH.
    unfold edge_winding. destruct (segment_crosses_ray p A B) eqn:Hc.
    + (* crossing edge: +/-1 on the Z side, S on the nat side *)
      rewrite Nat.odd_succ.
      destruct (Rlt_b (py A) (py B));
        rewrite Z.odd_add, Hpar;
        [ replace (Z.odd 1) with true by reflexivity
        | replace (Z.odd (-1)) with true by reflexivity ];
        rewrite xorb_true_r, Nat.negb_odd; reflexivity.
    + (* non-crossing edge: +0 on the Z side, accumulator unchanged on the nat side *)
      rewrite Z.add_0_r. exact Hpar.
Qed.

Lemma winding_parity_eq_crossing_parity : forall (p : Point) (r : Ring),
  Z.odd (winding_number p r) = Nat.odd (count_crossings_ray p r).
Proof.
  intros p r. unfold winding_number, count_crossings_ray.
  apply winding_crossing_parity_aux. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Verification mechanism: winding parity decides point-in-ring.          *)
(* -------------------------------------------------------------------------- *)
Theorem winding_decides_membership : forall (p : Point) (r : Ring),
  no_horizontal_edge_at p r ->
  (winding_in_ring_b p r = true <-> point_in_ring p r).
Proof.
  intros p r Hnh. unfold winding_in_ring_b.
  rewrite winding_parity_eq_crossing_parity.
  symmetry. apply point_in_ring_eq_parity. exact Hnh.
Qed.

Print Assumptions edge_winding_triple.
Print Assumptions winding_parity_eq_crossing_parity.
Print Assumptions winding_decides_membership.
