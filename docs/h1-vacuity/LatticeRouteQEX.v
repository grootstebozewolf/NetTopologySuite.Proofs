(* LatticeRouteQEX.v -- the lattice route to the two-ulp tail bound fails.

   Route proposed: with U = ulp(g_k), d = 2^L, rho = Q_{k-1} - g_{k-1}
   = S_{k-2} - H_{k-1}: if |S_{k-2}| < 2U, |H_{k-1}| < d, rho in dZ and d | 2U,
   then |rho| < 2U + d forces |rho| <= 2U.  The lemma is sound; the facts are
   not available together.  Priest-valid binary64 witness, M = 2^53 - 1:

       e = [2; 2^-59]      f = [M 2^-60]
       sorted: 2^-59, M 2^-60, 2
       TwoSum(M 2^-60, 2^-59): exact (2^53 + 1) 2^-60, a tie, rounds to the
       even 2^-7; error h_1 = 2^-60.
       k = 2:  rho = Q_1 - g_1 = 2^-7 - M 2^-60 = 2^-60,  H_1 = h_1 = 2^-60.

   NO power of two d has both |H_1| < d and rho in dZ (d <= 2^-60 fails the
   first, d >= 2^-59 the second) -- whatever d | 2U says.  The bound itself
   holds here (|rho| = 2^-60 <= 2 ulp(2) = 2^-50).  For bstate's own scale
   (keys < 2^L, Q multiple of 2^L forces d in [2^-59, 2^-7]) the fact that
   fails is rho in dZ, because g_1 = M 2^-60 is not on the d-lattice. 
   Attribution: an internal proof route (PR #1012), not a published one; this
   header is the only record of it.  The statement drops two of the route's
   premises (|S_(k-2)| < 2U, d | 2U), which strengthens the refutation, and
   carries the rung-4 hypotheses (overflow margin, nonzero components).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human-reviewed (2026-11-10, J. Bloemscheer, on main @ 4eb6c4b6):
     rung 2, on the reading that the route above is the one attempted.
     Assisted-by: Claude
*)
From Stdlib Require Import Reals ZArith Lia Lra List.
From Flocq Require Import IEEE754.Binary Core Ulp.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib B64_Pff_bridge
     B64_Expansion B64_FastExpansionSum B64_FastExpansionSum_Shewchuk
     B64_Shewchuk_Thm13_counterexample B64_Overlap_Hierarchy
     B64_Priest_FES_counterexample DivRoundPow2_b64
     B64_CarryCleanAlgo B64_CarryCleanCore.
Import ListNotations.
Local Open Scope R_scope.
Local Abbreviation b2r := (Binary.B2R prec emax).

Definition la : binary64 := Binary.B754_finite prec emax false 4503599627370496 (-111) eq_refl. (* 2^-59 *)
Definition lb : binary64 := bM_scaled (-60) eq_refl.                                        (* M 2^-60 *)
Definition lc : binary64 := Binary.B754_finite prec emax false 4503599627370496 (-51) eq_refl.  (* 2 *)
Definition le_ : list binary64 := [lc; la].
Definition lf : list binary64 := [lb].

Definition lQ1 : binary64 := Binary.B754_finite prec emax false 4503599627370496 (-59) eq_refl.  (* 2^-7 *)
Definition lh1 : binary64 := Binary.B754_finite prec emax false 4503599627370496 (-112) eq_refl. (* 2^-60 *)

Lemma l_priest : priest_chain le_ /\ priest_chain lf.
Proof. unfold le_, lf, la, lc. simpl. repeat split; apply priest_fin; zdec. Qed.

Lemma l_finite : Forall b64_fin le_ /\ Forall b64_fin lf.
Proof. unfold le_, lf, la, lb, lc, bM_scaled. split; repeat constructor. Qed.

Lemma l_sort : sort_by_abs (le_ ++ lf) = [la; lb; lc].
Proof.
  assert (Hab : Rabs (b2r la) < Rabs (b2r lb)).
  { unfold la, lb, bM_scaled, mant_M. rewrite !abs_B2R_fin. apply scaled_lt'; zdec. }
  assert (Hbc : Rabs (b2r lb) < Rabs (b2r lc)).
  { unfold lb, lc, bM_scaled, mant_M. rewrite !abs_B2R_fin. apply scaled_lt'; zdec. }
  unfold le_, lf. cbn [app sort_by_abs].
  repeat first [ rewrite insert_by_abs_nil
               | rewrite insert_by_abs_le by lra
               | rewrite insert_by_abs_gt by lra ].
  reflexivity.
Qed.

(* Inside the rung-4 hypothesis set: the overflow margin and nonzero
   components (f is a singleton chain, so priest_chain alone does not give
   the latter). *)
Lemma l_small : abs_sum le_ + abs_sum lf <= bpow radix2 (emax - 5).
Proof.
  assert (Hb : forall s m k H, (k <= 2)%Z -> (Z.pos m < Zpower radix2 (2 - k))%Z ->
             Rabs (b2r (Binary.B754_finite prec emax s m k H)) < bpow radix2 2).
  { intros s m k H Hk Hm. rewrite B2R_fin.
    apply abs_scaled_lt_bpow; [ exact Hk | destruct s; cbn [cond_Zopp]; lia ]. }
  assert (A : Rabs (b2r lc) < bpow radix2 2)
    by (unfold lc; apply Hb; [ lia | vm_compute; reflexivity ]).
  assert (B : Rabs (b2r la) < bpow radix2 2)
    by (unfold la; apply Hb; [ lia | vm_compute; reflexivity ]).
  assert (C : Rabs (b2r lb) < bpow radix2 2)
    by (unfold lb, bM_scaled, mant_M; apply Hb; [ lia | vm_compute; reflexivity ]).
  assert (H16 : 16 <= bpow radix2 (emax - 5))
    by (change 16 with (bpow radix2 4); apply bpow_le; unfold emax; lia).
  unfold le_, lf. cbn [abs_sum]. change (bpow radix2 2) with 4 in A, B, C. lra.
Qed.

Lemma l_nonzero : Forall (fun x => b2r x <> 0) (le_ ++ lf).
Proof.
  unfold le_, lf, la, lb, lc, bM_scaled. cbn [app].
  repeat (apply Forall_cons; [ apply B2R_fin_nonzero | ]). apply Forall_nil.
Qed.

(* The first cascade step is TwoSum(g_1, g_0) = TwoSum(lb, la). *)
Lemma l_step : [fst (b64_TwoSum lb la); snd (b64_TwoSum lb la)] = [lQ1; lh1].
Proof. apply map_B2FF_inj. vm_compute. reflexivity. Qed.

Lemma l_step_first :
  b64_grow_expansion_aux la [lb; lc]
  = (snd (b64_TwoSum lb la) :: fst (b64_grow_expansion_aux (fst (b64_TwoSum lb la)) [lc]),
     snd (b64_grow_expansion_aux (fst (b64_TwoSum lb la)) [lc])).
Proof.
  cbn [b64_grow_expansion_aux]. destruct (b64_TwoSum lb la) as [q h]. cbn [fst snd].
  destruct (b64_TwoSum lc q) as [q2 h2]. reflexivity.
Qed.

Lemma l_vals : b2r lQ1 - b2r lb = bpow radix2 (-60) /\ b2r lh1 = bpow radix2 (-60).
Proof.
  assert (E59 : bpow radix2 (-59) = 2 * bpow radix2 (-60))
    by (replace (-59)%Z with (1 + -60)%Z by reflexivity; rewrite bpow_plus; reflexivity).
  assert (E112 : IZR 4503599627370496 * bpow radix2 (-112) = bpow radix2 (-60)).
  { change 4503599627370496 with (bpow radix2 52) at 1. rewrite <- bpow_plus. reflexivity. }
  assert (E59' : IZR 4503599627370496 * bpow radix2 (-59) = 2 * IZR 4503599627370496 * bpow radix2 (-60))
    by (rewrite E59; ring).
  unfold lQ1, lb, lh1, bM_scaled, mant_M. rewrite !B2R_fin. cbn [cond_Zopp].
  split; [ | exact E112 ].
  rewrite E59'. pose proof (bpow_gt_0 radix2 (-60)).
  replace (2 * IZR 4503599627370496 * bpow radix2 (-60) - IZR 9007199254740991 * bpow radix2 (-60))
    with ((2 * IZR 4503599627370496 - IZR 9007199254740991) * bpow radix2 (-60)) by ring.
  replace (2 * IZR 4503599627370496 - IZR 9007199254740991) with 1
    by (rewrite <- mult_IZR, <- minus_IZR; reflexivity).
  ring.
Qed.

(* No lattice scale fits rho and H_1 = h_1 at once. *)
Lemma no_common_scale :
  forall x : R, 0 < x ->
    ~ (exists L : Z, Rabs x < bpow radix2 L /\ exists n : Z, x = IZR n * bpow radix2 L).
Proof.
  intros x Hx [L [HL [n Hn]]]. rewrite Rabs_pos_eq in HL by lra.
  pose proof (bpow_gt_0 radix2 L) as HB.
  destruct (Z_lt_le_dec 0 n) as [Hn0 | Hn0].
  - assert (H1 : (1 <= n)%Z) by lia. apply IZR_le in H1. nra.
  - apply IZR_le in Hn0. nra.
Qed.

Lemma ulp_lc : ulp radix2 b64_fexp (b2r lc) = bpow radix2 (-51).
Proof.
  assert (Hq : b2r lc = 2).
  { unfold lc. rewrite B2R_fin. cbn [cond_Zopp].
    change 4503599627370496 with (bpow radix2 52) at 1. rewrite <- bpow_plus. reflexivity. }
  assert (H0 : b2r lc <> 0) by (rewrite Hq; lra).
  rewrite (ulp_neq_0 _ _ _ H0).
  assert (Hm : mag radix2 (b2r lc) = 2%Z :> Z).
  { apply mag_unique. rewrite Hq, Rabs_pos_eq by lra. change (bpow radix2 (2 - 1)) with 2.
    change (bpow radix2 2) with 4. lra. }
  unfold cexp. rewrite Hm. unfold b64_fexp, SpecFloat.fexp, SpecFloat.emin, prec, emax. reflexivity.
Qed.

Theorem lattice_route_false :
  exists e f g0 g1 g2,
    priest_chain e /\ priest_chain f /\ Forall b64_fin e /\ Forall b64_fin f /\
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) /\
    Forall (fun x => b2r x <> 0) (e ++ f) /\
    sort_by_abs (e ++ f) = [g0; g1; g2] /\
    let Q1 := fst (b64_TwoSum g1 g0) in
    let h1 := snd (b64_TwoSum g1 g0) in
    (* rho = Q_1 - g_1 and H_1 = h_1 admit no common lattice scale *)
    ~ (exists L : Z, Rabs (b2r h1) < bpow radix2 L /\
         exists n : Z, b2r Q1 - b2r g1 = IZR n * bpow radix2 L)
    (* while the bound itself holds *)
    /\ Rabs (b2r Q1 - b2r g1) <= 2 * ulp radix2 b64_fexp (b2r g2).
Proof.
  destruct l_priest as [Pe Pf]. destruct l_finite as [Fe Ff].
  exists le_, lf, la, lb, lc.
  refine (conj Pe (conj Pf (conj Fe (conj Ff (conj l_small (conj l_nonzero (conj l_sort _))))))).
  cbv zeta.
  assert (SQ : fst (b64_TwoSum lb la) = lQ1) by exact (f_equal (fun l => nth 0 l lQ1) l_step).
  assert (Sh : snd (b64_TwoSum lb la) = lh1) by exact (f_equal (fun l => nth 1 l lQ1) l_step).
  rewrite SQ, Sh.
  destruct l_vals as [Vr Vh]. rewrite Vr, Vh. split.
  - intros [L [HL Hn]]. apply (no_common_scale (bpow radix2 (-60)) (bpow_gt_0 _ _)).
    exists L. split; [ exact HL | exact Hn ].
  - rewrite ulp_lc, Rabs_pos_eq by (left; apply bpow_gt_0).
    pose proof (bpow_le radix2 (-60) (-51) ltac:(lia)). pose proof (bpow_gt_0 radix2 (-51)). lra.
Qed.

Print Assumptions l_small.
Print Assumptions l_nonzero.
Print Assumptions lattice_route_false.
