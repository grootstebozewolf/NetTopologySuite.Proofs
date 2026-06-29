(* ============================================================================
   NetTopologySuite.Proofs.HalfOpenEscape
   ----------------------------------------------------------------------------
   Half-open migration, rung 2: the ESCAPE half made guard-free by perturbation,
   yielding the full guard-free interior biconditional over half-open parity.

   The guard `ray_avoids_vertices` in the escape walk is a walk artifact, not a
   truth condition.  Using `RingComplementOpen.ring_complement_open` (the
   boundary complement is open), a non-generic even-parity complement point is
   perturbed to a nearby GENERIC complement point in the same component; the
   guarded escape applies there and component-invariance transports it back.

   §1 supplies the analytic pigeonhole `exists_real_avoiding`: any open interval
   contains a real avoiding a given finite list (the vertex heights).

   Pure-R; classical-reals trio only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Lia Arith FinFun.
Import ListNotations.

Local Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(* §1  Analytic pigeonhole: avoid a finite list within an interval.   *)
(* ------------------------------------------------------------------ *)

(* n+1 distinct candidates in (c, c + eps): c + eps/(k+2), k = 0..n. *)
Definition avoid_cand (c eps : R) (k : nat) : R := c + eps / (INR k + 2).

Lemma avoid_cand_inj : forall c eps, eps <> 0 -> Injective (avoid_cand c eps).
Proof.
  intros c eps Heps i j H. unfold avoid_cand in H.
  apply Rplus_eq_reg_l in H.       (* H : eps / (INR i + 2) = eps / (INR j + 2) *)
  assert (Hi : INR i + 2 <> 0) by (pose proof (pos_INR i); lra).
  assert (Hj : INR j + 2 <> 0) by (pose proof (pos_INR j); lra).
  unfold Rdiv in H.
  assert (Hinv : / (INR i + 2) = / (INR j + 2)).
  { apply (Rmult_eq_reg_l eps); [ exact H | exact Heps ]. }
  apply (f_equal Rinv) in Hinv. rewrite !Rinv_inv in Hinv.
  apply INR_eq. lra.
Qed.

Lemma avoid_cand_in_ball : forall c eps k, 0 < eps -> Rabs (avoid_cand c eps k - c) < eps.
Proof.
  intros c eps k Heps. unfold avoid_cand.
  assert (Hpos : 0 < INR k + 2) by (pose proof (pos_INR k); lra).
  assert (Hposv : 0 < eps / (INR k + 2)) by (apply Rdiv_lt_0_compat; lra).
  assert (Hval : eps / (INR k + 2) < eps).
  { apply (Rmult_lt_reg_r (INR k + 2)); [ exact Hpos | ].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
    replace (eps * (INR k + 2)) with (eps * INR k + 2 * eps) by ring.
    assert (0 <= eps * INR k) by (apply Rmult_le_pos; [ lra | apply pos_INR ]).
    lra. }
  replace (c + eps / (INR k + 2) - c) with (eps / (INR k + 2)) by ring.
  apply Rabs_def1; lra.
Qed.

Theorem exists_real_avoiding : forall (L : list R) (c eps : R),
  0 < eps -> exists y, Rabs (y - c) < eps /\ ~ In y L.
Proof.
  intros L c eps Heps.
  set (cl := map (avoid_cand c eps) (seq 0 (S (length L)))).
  destruct (Exists_dec (fun y => ~ In y L) cl
              (fun y => match in_dec Req_EM_T y L with
                        | left h => right (fun n => n h)
                        | right h => left h
                        end)) as [Hex | Hnex].
  - apply Exists_exists in Hex. destruct Hex as [y [Hin Hni]].
    exists y. split; [ | exact Hni ].
    unfold cl in Hin. apply in_map_iff in Hin. destruct Hin as [k [Hk _]].
    rewrite <- Hk. apply avoid_cand_in_ball; exact Heps.
  - exfalso.
    (* not-exists-avoiding -> all candidates are in L -> incl cl L -> length clash *)
    assert (Hincl : incl cl L).
    { intros y Hy. destruct (in_dec Req_EM_T y L) as [h | h]; [ exact h | ].
      exfalso. apply Hnex. apply Exists_exists. exists y; auto. }
    assert (Hnd : NoDup cl).
    { unfold cl. apply Injective_map_NoDup; [ | apply seq_NoDup ].
      apply avoid_cand_inj. lra. }
    pose proof (NoDup_incl_length Hnd Hincl) as Hlen.
    unfold cl in Hlen. rewrite length_map, length_seq in Hlen. lia.
Qed.

Print Assumptions exists_real_avoiding.
