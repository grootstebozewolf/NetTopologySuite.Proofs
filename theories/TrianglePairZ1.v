(* NetTopologySuite.Proofs.TrianglePairZ1
   Z1 leaves of the separating-edge follow-up: successor, predecessor,
   both-positive, and the cU = 0 leaf.
   Deferred: sat_iff. For two positive triangles, open interiors are
   disjoint iff some_outer. The easy direction is
   TrianglePairClip.some_outer_disjoint. The hard direction is not
   proved (cQ = 0, the Z2 orbit, boundary mixture). Not Admitted.
   topic: relate
   claimId: tri-de9im-a
   witness: none
   3-axiom host. No Jordan.
   AI-drafted (Cursor Grok 4.7), human-reviewed.
   License: BSD-3-Clause *)

From Stdlib Require Import Reals Lra Lia List.
Import ListNotations.
From NTS.Proofs Require Import Distance Orientation Convex Centroid
  ConvexClip TrianglePairCommon.
From NTS.Proofs Require Export TrianglePairSepCap.
Local Open Scope R_scope.

Lemma tri_open_rot : forall A B C X,
  tri_open A B C X -> tri_open B C A X.
Proof.
  intros A B C X [Hab [Hbc Hca]]. repeat split; assumption.
Qed.

Lemma tri_open_rot2 : forall A B C X,
  tri_open A B C X -> tri_open C A B X.
Proof.
  intros A B C X [Hab [Hbc Hca]]. repeat split; assumption.
Qed.

Lemma outer3_rot : forall p q a b c,
  outer3 p q a b c -> outer3 p q b c a.
Proof.
  intros p q a b c [H1 [H2 H3]]. repeat split; assumption.
Qed.

Lemma outer3_rot2 : forall p q a b c,
  outer3 p q a b c -> outer3 p q c a b.
Proof.
  intros p q a b c [H1 [H2 H3]]. repeat split; assumption.
Qed.

Lemma some_outer_swap : forall A B C P Q U,
  some_outer P Q U A B C -> some_outer A B C P Q U.
Proof.
  intros A B C P Q U [H|[H|[H|[H|[H|H]]]]].
  - do 3 right. left. exact H.
  - do 4 right. left. exact H.
  - do 5 right. exact H.
  - left. exact H.
  - right. left. exact H.
  - do 2 right. left. exact H.
Qed.

Lemma meet_swap : forall A B C P Q U,
  (exists X, tri_open P Q U X /\ tri_open A B C X) ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U [X [Hs Ht]]. exists X. split; assumption.
Qed.

Lemma meet_rot_T : forall A B C P Q U,
  (exists X, tri_open B C A X /\ tri_open P Q U X) ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U [X [Ht Hs]].
  exists X. split; [| exact Hs].
  destruct Ht as [Hbc [Hca Hab]]. repeat split; assumption.
Qed.

Lemma meet_rot_S : forall A B C P Q U,
  (exists X, tri_open A B C X /\ tri_open Q U P X) ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U [X [Ht Hs]].
  exists X. split; [exact Ht |].
  destruct Hs as [Hqu [Hup Hpq]]. repeat split; assumption.
Qed.

(* P sits in the exterior corner at A, Q at B, U at C. Vertex A of ABC
   is then strictly inside triangle PQU. *)
Lemma surround_open_A : forall A B C P Q U,
  0 < cross A B C ->
  0 < cross B C P -> cross C A P < 0 -> cross A B P < 0 ->
  cross B C Q < 0 -> 0 < cross C A Q -> cross A B Q < 0 ->
  cross B C U < 0 -> cross C A U < 0 -> 0 < cross A B U ->
  tri_open P Q U A.
Proof.
  intros A B C P Q U Hd HaP HbP HcP HaQ HbQ HcQ HaU HbU HcU.
  repeat split.
  - apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite sep_nb_A. replace (0 * cross A B C) with 0 by ring.
    assert (H1 : 0 < (- cross A B P) * cross C A Q).
    { apply Rmult_lt_0_compat; lra. }
    assert (Hnq : 0 < - cross A B Q) by lra.
    assert (Hnp : 0 < - cross C A P) by lra.
    assert (H2 : 0 < (- cross A B Q) * (- cross C A P)).
    { apply Rmult_lt_0_compat; assumption. }
    replace ((- cross A B Q) * (- cross C A P))
      with (cross A B Q * cross C A P) in H2 by ring.
    assert (Hsum : 0 < (- cross A B P) * cross C A Q
                      + cross A B Q * cross C A P).
    { apply Rplus_lt_0_compat; assumption. }
    replace (- (cross A B P * cross C A Q - cross A B Q * cross C A P))
      with ((- cross A B P) * cross C A Q + cross A B Q * cross C A P)
      by ring.
    exact Hsum.
  - apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite qua_bb. replace (0 * cross A B C) with 0 by ring.
    assert (Eb := cross_sum3 A B C Q).
    assert (Eu := cross_sum3 A B C U).
    set (ap := - cross B C Q).
    set (cq := - cross A B Q).
    set (au := - cross B C U).
    set (bu := - cross C A U).
    assert (Hap : 0 < ap) by (unfold ap; lra).
    assert (Hcq : 0 < cq) by (unfold cq; lra).
    assert (Hau : 0 < au) by (unfold au; lra).
    assert (Hbu : 0 < bu) by (unfold bu; lra).
    assert (EbQ : cross C A Q = cross A B C + ap + cq).
    { unfold ap, cq.
      replace (cross A B C - cross B C Q - cross A B Q)
        with (cross A B C + - cross B C Q + - cross A B Q) by ring.
      assert (Esum : cross A B Q + cross B C Q + cross C A Q = cross A B C)
        by exact Eb.
      lra. }
    assert (EcU : cross A B U = cross A B C + au + bu).
    { unfold au, bu.
      assert (Esum : cross A B U + cross B C U + cross C A U = cross A B C)
        by exact Eu.
      lra. }
    rewrite EbQ, EcU.
    assert (Hdd : 0 < cross A B C * cross A B C).
    { apply Rmult_lt_0_compat; assumption. }
    assert (H1 : 0 < cross A B C * au) by (apply Rmult_lt_0_compat; assumption).
    assert (H2 : 0 < cross A B C * bu) by (apply Rmult_lt_0_compat; assumption).
    assert (H3 : 0 < cross A B C * ap) by (apply Rmult_lt_0_compat; assumption).
    assert (H4 : 0 < cross A B C * cq) by (apply Rmult_lt_0_compat; assumption).
    assert (H5 : 0 < ap * au) by (apply Rmult_lt_0_compat; assumption).
    assert (H6 : 0 < ap * bu) by (apply Rmult_lt_0_compat; assumption).
    assert (H7 : 0 < cq * au) by (apply Rmult_lt_0_compat; assumption).
    assert (S01 : 0 < cross A B C * cross A B C + cross A B C * au).
    { apply Rplus_lt_0_compat; assumption. }
    assert (S02 : 0 < cross A B C * cross A B C + cross A B C * au
                    + cross A B C * bu).
    { apply Rplus_lt_0_compat; [exact S01 | exact H2]. }
    assert (S03 : 0 < cross A B C * cross A B C + cross A B C * au
                    + cross A B C * bu + cross A B C * ap).
    { apply Rplus_lt_0_compat; [exact S02 | exact H3]. }
    assert (S04 : 0 < cross A B C * cross A B C + cross A B C * au
                    + cross A B C * bu + cross A B C * ap
                    + cross A B C * cq).
    { apply Rplus_lt_0_compat; [exact S03 | exact H4]. }
    assert (S05 : 0 < cross A B C * cross A B C + cross A B C * au
                    + cross A B C * bu + cross A B C * ap
                    + cross A B C * cq + ap * au).
    { apply Rplus_lt_0_compat; [exact S04 | exact H5]. }
    assert (S06 : 0 < cross A B C * cross A B C + cross A B C * au
                    + cross A B C * bu + cross A B C * ap
                    + cross A B C * cq + ap * au + ap * bu).
    { apply Rplus_lt_0_compat; [exact S05 | exact H6]. }
    assert (S07 : 0 < cross A B C * cross A B C + cross A B C * au
                    + cross A B C * bu + cross A B C * ap
                    + cross A B C * cq + ap * au + ap * bu + cq * au).
    { apply Rplus_lt_0_compat; [exact S06 | exact H7]. }
    assert (HeqS : (cross A B C + ap + cq) * (cross A B C + au + bu)
                   - cross A B Q * cross C A U
                 = cross A B C * cross A B C
                   + cross A B C * au + cross A B C * bu
                   + cross A B C * ap + cross A B C * cq
                   + ap * au + ap * bu + cq * au).
    { unfold ap, cq, au, bu. ring. }
    rewrite <- HeqS in S07. exact S07.
  - apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite cross_up_A. replace (0 * cross A B C) with 0 by ring.
    assert (H1 : 0 < cross A B P * cross C A U).
    { assert (Hn1 : 0 < - cross A B P) by lra.
      assert (Hn2 : 0 < - cross C A U) by lra.
      assert (Hp : 0 < (- cross A B P) * (- cross C A U)).
      { apply Rmult_lt_0_compat; assumption. }
      replace ((- cross A B P) * (- cross C A U))
        with (cross A B P * cross C A U) in Hp by ring.
      exact Hp. }
    assert (H2 : 0 < cross A B U * (- cross C A P)).
    { apply Rmult_lt_0_compat; [exact HcU | lra]. }
    assert (Hsum : 0 < cross A B P * cross C A U
                      + cross A B U * (- cross C A P)).
    { apply Rplus_lt_0_compat; assumption. }
    replace (cross A B P * cross C A U - cross A B U * cross C A P)
      with (cross A B P * cross C A U + cross A B U * (- cross C A P))
      by ring.
    exact Hsum.
Qed.

(* A strict spike has exactly one positive slack. skA sits in the
   exterior corner at A, and likewise for skB and skC. *)
Definition skA (A B C X : Point) : Prop :=
  0 < cross B C X /\ cross C A X < 0 /\ cross A B X < 0.
Definition skB (A B C X : Point) : Prop :=
  cross B C X < 0 /\ 0 < cross C A X /\ cross A B X < 0.
Definition skC (A B C X : Point) : Prop :=
  cross B C X < 0 /\ cross C A X < 0 /\ 0 < cross A B X.

Lemma skB_rot : forall A B C X, skB A B C X -> skA B C A X.
Proof. intros A B C X [Ha [Hb Hc]]. repeat split; assumption. Qed.

Lemma skC_rot : forall A B C X, skC A B C X -> skB B C A X.
Proof. intros A B C X [Ha [Hb Hc]]. repeat split; assumption. Qed.

Lemma skA_rot : forall A B C X, skA A B C X -> skC B C A X.
Proof. intros A B C X [Ha [Hb Hc]]. repeat split; assumption. Qed.

Lemma spikes_ccw : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  skA A B C P -> skB A B C Q -> skC A B C U ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu.
  destruct Hp as [HaP [HbP HcP]].
  destruct Hq as [HaQ [HbQ HcQ]].
  destruct Hu as [HaU [HbU HcU]].
  assert (Hopen : tri_open P Q U A).
  { apply (surround_open_A A B C P Q U); assumption. }
  destruct (meet_vertex P Q U A B C A Hs Hd (or_introl eq_refl) Hopen)
    as [X [HsX HtX]].
  exists X. split; assumption.
Qed.

Lemma spikes_ccw_rot : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  skB A B C P -> skC A B C Q -> skA A B C U ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu.
  apply meet_rot_T.
  apply spikes_ccw.
  - replace (cross B C A) with (cross A B C) by apply cross_cycle. exact Hd.
  - exact Hs.
  - apply skB_rot. exact Hp.
  - apply skC_rot. exact Hq.
  - apply skA_rot. exact Hu.
Qed.

Lemma spikes_ccw_rot2 : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  skC A B C P -> skA A B C Q -> skB A B C U ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu.
  apply meet_rot_T.
  apply spikes_ccw_rot.
  - replace (cross B C A) with (cross A B C) by apply cross_cycle. exact Hd.
  - exact Hs.
  - apply skC_rot. exact Hp.
  - apply skA_rot. exact Hq.
  - apply skB_rot. exact Hu.
Qed.

Lemma spikes_cw_false : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  skA A B C P -> skC A B C Q -> skB A B C U -> False.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu.
  destruct Hp as [HaP [HbP HcP]].
  destruct Hq as [HaQ [HbQ HcQ]].
  destruct Hu as [HaU [HbU HcU]].
  assert (Hopen : tri_open P U Q A).
  { apply (surround_open_A A B C P U Q); assumption. }
  destruct Hopen as [Hpu [Huq Hqp]].
  assert (Hpq : cross P Q A < 0).
  { assert (E := cross_swap_first_two Q P A). lra. }
  assert (Hqu : cross Q U A < 0).
  { assert (E := cross_swap_first_two U Q A). lra. }
  assert (Hup : cross U P A < 0).
  { assert (E := cross_swap_first_two P U A). lra. }
  assert (Esum := cross_sum3 P Q U A). lra.
Qed.

Lemma spikes_cw_rot_false : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  skB A B C P -> skA A B C Q -> skC A B C U -> False.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu.
  apply (spikes_cw_false B C A P Q U).
  - replace (cross B C A) with (cross A B C) by apply cross_cycle. exact Hd.
  - exact Hs.
  - apply skB_rot. exact Hp.
  - apply skA_rot. exact Hq.
  - apply skC_rot. exact Hu.
Qed.

Lemma spikes_cw_rot2_false : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  skC A B C P -> skB A B C Q -> skA A B C U -> False.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu.
  apply (spikes_cw_false C A B P Q U).
  - replace (cross C A B) with (cross A B C) by apply cross_cycle2. exact Hd.
  - exact Hs.
  - apply (skB_rot B C A). apply skC_rot. exact Hp.
  - apply (skA_rot B C A). apply skB_rot. exact Hq.
  - apply (skC_rot B C A). apply skA_rot. exact Hu.
Qed.

Local Ltac le_c :=
  match goal with
  | H : skA ?A ?B ?C ?X |- cross ?A ?B ?X <= 0 =>
      destruct H as [? [? Hc]]; apply Rlt_le; exact Hc
  | H : skB ?A ?B ?C ?X |- cross ?A ?B ?X <= 0 =>
      destruct H as [? [? Hc]]; apply Rlt_le; exact Hc
  end.

Local Ltac le_a :=
  match goal with
  | H : skB ?A ?B ?C ?X |- cross ?B ?C ?X <= 0 =>
      destruct H as [Ha [? ?]]; apply Rlt_le; exact Ha
  | H : skC ?A ?B ?C ?X |- cross ?B ?C ?X <= 0 =>
      destruct H as [Ha [? ?]]; apply Rlt_le; exact Ha
  end.

Local Ltac le_b :=
  match goal with
  | H : skA ?A ?B ?C ?X |- cross ?C ?A ?X <= 0 =>
      destruct H as [? [Hb ?]]; apply Rlt_le; exact Hb
  | H : skC ?A ?B ?C ?X |- cross ?C ?A ?X <= 0 =>
      destruct H as [? [Hb ?]]; apply Rlt_le; exact Hb
  end.

Local Ltac out_c :=
  left; apply some_outer_ab; unfold outer3; repeat split; le_c.
Local Ltac out_a :=
  left; unfold some_outer; right; left; unfold outer3; repeat split; le_a.
Local Ltac out_b :=
  left; unfold some_outer; do 2 right; left; unfold outer3; repeat split; le_b.

Lemma spikes_cert : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  (skA A B C P \/ skB A B C P \/ skC A B C P) ->
  (skA A B C Q \/ skB A B C Q \/ skC A B C Q) ->
  (skA A B C U \/ skB A B C U \/ skC A B C U) ->
  some_outer A B C P Q U \/
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hp Hq Hu.
  destruct Hp as [Pa|[Pb|Pc]]; destruct Hq as [Qa|[Qb|Qc]];
  destruct Hu as [Ua|[Ub|Uc]].
  - out_c. (* AAA *)
  - out_c. (* AAB *)
  - out_b. (* AAC *)
  - out_c. (* ABA *)
  - out_c. (* ABB *)
  - apply or_intror. apply (spikes_ccw A B C P Q U); assumption. (* ABC *)
  - out_b. (* ACA *)
  - exfalso. apply (spikes_cw_false A B C P Q U); assumption. (* ACB *)
  - out_b. (* ACC *)
  - out_c. (* BAA *)
  - out_c. (* BAB *)
  - exfalso. apply (spikes_cw_rot_false A B C P Q U); assumption. (* BAC *)
  - out_c. (* BBA *)
  - out_c. (* BBB *)
  - out_a. (* BBC *)
  - apply or_intror. apply (spikes_ccw_rot A B C P Q U); assumption. (* BCA *)
  - out_a. (* BCB *)
  - out_a. (* BCC *)
  - out_b. (* CAA *)
  - apply or_intror. apply (spikes_ccw_rot2 A B C P Q U); assumption. (* CAB *)
  - out_b. (* CAC *)
  - exfalso. apply (spikes_cw_rot2_false A B C P Q U); assumption. (* CBA *)
  - out_a. (* CBB *)
  - out_a. (* CBC *)
  - out_b. (* CCA *)
  - out_a. (* CCB *)
  - out_a. (* CCC *)
Qed.

Lemma qu_gap_b : forall A B C Q U,
  0 < cross A B C ->
  cross Q U B - cross Q U A = cross A B Q - cross A B U.
Proof.
  intros A B C Q U Hd.
  assert (E := qu_b_gap A B C Q U).
  apply Rmult_eq_reg_l with (r := cross A B C).
  - replace (cross A B C * (cross Q U B - cross Q U A))
      with ((cross Q U B - cross Q U A) * cross A B C) by ring.
    exact E.
  - apply not_eq_sym. apply Rlt_not_eq. exact Hd.
Qed.

Lemma qu_gap_c : forall A B C Q U,
  0 < cross A B C ->
  cross Q U C - cross Q U A = cross C A U - cross C A Q.
Proof.
  intros A B C Q U Hd.
  assert (E := qu_c_gap A B C Q U).
  apply Rmult_eq_reg_l with (r := cross A B C).
  - replace (cross A B C * (cross Q U C - cross Q U A))
      with ((cross Q U C - cross Q U A) * cross A B C) by ring.
    exact E.
  - apply not_eq_sym. apply Rlt_not_eq. exact Hd.
Qed.

(* P lies on line AB, strictly beyond A: c = 0, b < 0, a > 0. *)
Lemma z1_pqA : forall A B C P Q,
  cross A B P = 0 ->
  cross P Q A * cross A B C = cross A B Q * cross C A P.
Proof.
  intros A B C P Q Hc.
  assert (E := sep_nb_A A B C P Q). rewrite Hc in E. ring_simplify in E. exact E.
Qed.

Lemma z1_pqB : forall A B C P Q,
  cross A B P = 0 ->
  cross P Q B * cross A B C = - cross A B Q * cross B C P.
Proof.
  intros A B C P Q Hc.
  assert (E := cross_pq_B_na A B C P Q). rewrite Hc in E. ring_simplify in E. exact E.
Qed.

Lemma z1_upA : forall A B C P U,
  cross A B P = 0 ->
  cross U P A * cross A B C = - cross A B U * cross C A P.
Proof.
  intros A B C P U Hc.
  assert (E := cross_up_A A B C P U). rewrite Hc in E. ring_simplify in E. exact E.
Qed.

Lemma z1_upB : forall A B C P U,
  cross A B P = 0 ->
  cross U P B * cross A B C = cross A B U * cross B C P.
Proof.
  intros A B C P U Hc.
  assert (E := cross_up_B A B C P U). rewrite Hc in E. ring_simplify in E. exact E.
Qed.

Lemma wedge_cab : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  cross C A P * cross C A Q < 0 ->
  cross P Q C * cross P Q A < 0 ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hca Hpq.
  assert (Hm : exists X, tri_open C A B X /\ tri_open P Q U X).
  { apply wedge_edges; try assumption.
    replace (cross C A B) with (cross A B C) by apply cross_cycle2. exact Hd. }
  destruct Hm as [X [Ht HsX]].
  exists X. split; [| exact HsX].
  apply tri_open_rot. exact Ht.
Qed.

Lemma wedge_bca : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  cross B C P * cross B C Q < 0 ->
  cross P Q B * cross P Q C < 0 ->
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs Hbc Hpq.
  assert (Hm : exists X, tri_open B C A X /\ tri_open P Q U X).
  { apply wedge_edges; try assumption.
    replace (cross B C A) with (cross A B C) by apply cross_cycle. exact Hd. }
  destruct Hm as [X [Ht HsX]].
  exists X. split; [| exact HsX].
  destruct Ht as [H1 [H2 H3]]. repeat split; assumption.
Qed.

Lemma z1_succ : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  cross A B P = 0 -> cross C A P < 0 -> 0 < cross B C P ->
  0 < cross A B Q -> cross A B U < 0 ->
  some_outer A B C P Q U \/
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs HcP HbP HaP Hq Hu.
  assert (HPQA : cross P Q A < 0).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite (z1_pqA A B C P Q HcP).
    replace (0 * cross A B C) with 0 by ring.
    apply prod_pos_neg; assumption. }
  assert (HPQB : cross P Q B < 0).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite (z1_pqB A B C P Q HcP).
    replace (0 * cross A B C) with 0 by ring.
    apply prod_neg; [lra | exact HaP]. }
  destruct (Rlt_dec 0 (cross C A U)) as [HbU|HbU].
  - assert (HUPA : cross U P A < 0).
    { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
      rewrite (z1_upA A B C P U HcP).
      replace (0 * cross A B C) with 0 by ring.
      apply prod_pos_neg; [lra | exact HbP]. }
    assert (HUPB : cross U P B < 0).
    { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
      rewrite (z1_upB A B C P U HcP).
      replace (0 * cross A B C) with 0 by ring.
      apply prod_neg; assumption. }
    assert (HUPC : cross U P C < 0).
    { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
      assert (E := cross_up_C A B C P U).
      assert (Ea := cross_sum3 A B C P). rewrite HcP in Ea.
      assert (Eu := cross_sum3 A B C U).
      replace (0 * cross A B C) with 0 by ring.
      (* UPC * Δ = Δ * (bP - bU) - cU * bP *)
      assert (Hrew : cross U P C * cross A B C =
          cross A B C * (cross C A P - cross C A U)
          - cross A B U * cross C A P).
      { rewrite E.
        replace (cross B C U) with
          (cross A B C - cross C A U - cross A B U) by lra.
        replace (cross B C P) with
          (cross A B C - cross C A P) by lra.
        ring. }
      rewrite Hrew.
      assert (H1 : cross A B C * (cross C A P - cross C A U) < 0).
      { apply prod_pos_neg; [exact Hd | lra]. }
      assert (H2 : - cross A B U * cross C A P < 0).
      { apply prod_pos_neg; [lra | exact HbP]. }
      replace (cross A B C * (cross C A P - cross C A U)
                 - cross A B U * cross C A P)
        with (cross A B C * (cross C A P - cross C A U)
              + (- cross A B U * cross C A P)) by ring.
      replace 0 with (0 + 0) by ring.
      apply Rplus_lt_compat; assumption. }
    left. apply some_outer_up. repeat split; apply Rlt_le; assumption.
  - apply Rnot_lt_le in HbU.
    destruct (Rlt_dec 0 (cross P Q C)) as [HC|HC].
    + destruct (Rlt_dec 0 (cross C A Q)) as [HbQ|HbQ].
      * right. apply wedge_cab; try assumption.
        -- apply prod_neg; assumption.
        -- assert (Hprod : cross P Q A * cross P Q C < 0).
           { apply prod_neg; [exact HPQA | exact HC]. }
           replace (cross P Q C * cross P Q A)
             with (cross P Q A * cross P Q C) by ring.
           exact Hprod.
      * apply Rnot_lt_le in HbQ.
        left. unfold some_outer. right. right. left.
        repeat split; [apply Rlt_le; exact HbP | exact HbQ | exact HbU].
    + apply Rnot_lt_le in HC.
      left. apply some_outer_pq. repeat split; [apply Rlt_le; exact HPQA |
        apply Rlt_le; exact HPQB | exact HC].
Qed.

Lemma face_pos : forall sM sV u,
  0 <= sM -> 0 <= sV -> 0 < u -> u < 1 ->
  (sM = 0 -> 0 < sV) ->
  0 < (1 - u) * sM + u * sV.
Proof.
  intros sM sV u Hm Hv Hu Hu1 Hlift.
  destruct (Rle_lt_or_eq_dec 0 sM Hm) as [Hgt|Heq].
  - apply Rplus_lt_le_0_compat; [apply Rmult_lt_0_compat; lra | apply Rmult_le_pos; lra].
  - apply slack_mix_pos; [rewrite <- Heq; lra | apply Hlift; symmetry; exact Heq | exact Hu | lra].
Qed.

Lemma nudge_meet : forall A B C D E F M V,
  0 < cross A B C ->
  tri_open A B C M ->
  0 <= cross D E M -> 0 <= cross E F M -> 0 <= cross F D M ->
  0 <= cross D E V -> 0 <= cross E F V -> 0 <= cross F D V ->
  (cross D E M = 0 -> 0 < cross D E V) ->
  (cross E F M = 0 -> 0 < cross E F V) ->
  (cross F D M = 0 -> 0 < cross F D V) ->
  exists X, tri_open A B C X /\ tri_open D E F X.
Proof.
  intros A B C D E F M V Hd HM HdeM HefM HfdM HdeV HefV HfdV Lde Lef Lfd.
  destruct HM as [HmAB [HmBC HmCA]].
  set (rooms :=
    [ seg_room (cross A B M) (cross A B V);
      seg_room (cross B C M) (cross B C V);
      seg_room (cross C A M) (cross C A V) ]).
  set (t := rmin_list rooms).
  assert (Ht : 0 < t).
  { unfold t, rooms. apply rmin_list_pos. intros s Hin. simpl in Hin.
    destruct Hin as [<-|[<-|[<-|[]]]]; apply seg_room_pos; assumption. }
  set (u := t / 2).
  assert (Hu : 0 < u) by (unfold u; lra).
  assert (Hu1 : u < 1).
  { assert (Hh := rmin_list_half rooms). unfold u, t in *. lra. }
  assert (HuAB : u < seg_room (cross A B M) (cross A B V)).
  { apply Rlt_le_trans with (r2 := t); [unfold u; lra | unfold t].
    apply rmin_list_le. unfold rooms. simpl. left. reflexivity. }
  assert (HuBC : u < seg_room (cross B C M) (cross B C V)).
  { apply Rlt_le_trans with (r2 := t); [unfold u; lra | unfold t].
    apply rmin_list_le. unfold rooms. simpl. right. left. reflexivity. }
  assert (HuCA : u < seg_room (cross C A M) (cross C A V)).
  { apply Rlt_le_trans with (r2 := t); [unfold u; lra | unfold t].
    apply rmin_list_le. unfold rooms. simpl. right. right. left. reflexivity. }
  set (X := convex_combination M V u). exists X. split.
  - repeat split; unfold X; rewrite cross_combo.
    + apply slack_pos_room; [exact HmAB | apply Rlt_le; exact Hu | exact HuAB].
    + apply slack_pos_room; [exact HmBC | apply Rlt_le; exact Hu | exact HuBC].
    + apply slack_pos_room; [exact HmCA | apply Rlt_le; exact Hu | exact HuCA].
  - repeat split; unfold X; rewrite cross_combo.
    + apply face_pos; assumption.
    + apply face_pos; assumption.
    + apply face_pos; assumption.
Qed.

Lemma z1_pred : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  cross A B P = 0 -> cross C A P < 0 -> 0 < cross B C P ->
  cross A B Q < 0 -> 0 < cross A B U ->
  some_outer A B C P Q U \/
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs HcP HbP HaP Hq Hu.
  assert (HPQA : 0 < cross P Q A).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite (z1_pqA A B C P Q HcP). replace (0 * cross A B C) with 0 by ring.
    replace (cross A B Q * cross C A P)
      with ((- cross A B Q) * (- cross C A P)) by ring.
    apply Rmult_lt_0_compat; lra. }
  assert (HUPA : 0 < cross U P A).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite (z1_upA A B C P U HcP). replace (0 * cross A B C) with 0 by ring.
    replace (- cross A B U * cross C A P)
      with (cross A B U * (- cross C A P)) by ring.
    apply Rmult_lt_0_compat; lra. }
  destruct (Rlt_dec 0 (cross Q U A)) as [HQA|HQA].
  - right.
    destruct (meet_vertex P Q U A B C A Hs Hd (or_introl eq_refl)
                (conj HPQA (conj HQA HUPA))) as [X [HsX HtX]].
    exists X. split; assumption.
  - apply Rnot_lt_le in HQA.
    assert (HQUB : cross Q U B < 0).
    { assert (E := qu_gap_b A B C Q U Hd). lra. }
    destruct (Rlt_dec 0 (cross Q U C)) as [HQC|HQC].
    + assert (HbQ : cross C A Q < 0).
      { destruct (Rle_dec 0 (cross C A Q)) as [Hge|Hlt];
          [| apply Rnot_le_lt; exact Hlt].
        assert (Hgc := qu_gap_c A B C Q U Hd). exfalso.
        destruct (Rlt_dec (cross C A U) 0) as [Hun|Hup].
        - assert (E := Hgc). assert (HQ : cross Q U C < 0) by lra.
          apply (Rlt_asym 0 (cross Q U C) HQC HQ).
        - apply Rnot_lt_le in Hup.
          assert (Eneg : cross Q U A * cross A B C =
              cross C A Q * cross A B U + (- cross A B Q) * cross C A U).
          { rewrite (qua_bb A B C Q U). ring. }
          assert (Hle : cross Q U A * cross A B C <= 0).
          { apply Rle_trans with (r2 := 0 * cross A B C).
            - apply Rmult_le_compat_r; [apply Rlt_le; exact Hd | exact HQA].
            - replace (0 * cross A B C) with 0 by ring. apply Rle_refl. }
          destruct (Rle_lt_or_eq_dec 0 (cross C A Q) Hge) as [Hqb|Hqe].
          + assert (Hpos : 0 < cross C A Q * cross A B U
                             + (- cross A B Q) * cross C A U).
            { apply Rplus_lt_le_0_compat.
              - apply Rmult_lt_0_compat; [exact Hqb | exact Hu].
              - apply Rmult_le_pos; lra. }
            apply (Rle_not_lt 0 _ Hle). rewrite Eneg. exact Hpos.
          + destruct (Rle_lt_or_eq_dec 0 (cross C A U) Hup) as [Hub|Hue].
            * assert (Hpos : 0 < cross C A Q * cross A B U
                               + (- cross A B Q) * cross C A U).
              { rewrite <- Hqe.
                replace (0 * cross A B U + (- cross A B Q) * cross C A U)
                  with ((- cross A B Q) * cross C A U) by ring.
                apply Rmult_lt_0_compat; lra. }
              apply (Rle_not_lt 0 _ Hle). rewrite Eneg. exact Hpos.
            * assert (Hz : cross Q U A = 0).
              { apply Rmult_eq_reg_l with (r := cross A B C).
                - replace (cross A B C * cross Q U A)
                    with (cross Q U A * cross A B C) by ring.
                  rewrite Eneg. rewrite <- Hqe. rewrite <- Hue. ring.
                - apply not_eq_sym. apply Rlt_not_eq. exact Hd. }
              assert (Hc0 : cross Q U C = 0).
              { assert (E := Hgc). rewrite Hz in E. rewrite <- Hqe in E.
                rewrite <- Hue in E. lra. }
              apply (Rlt_not_eq 0 (cross Q U C) HQC). symmetry. exact Hc0. }
      destruct (Rlt_dec 0 (cross C A U)) as [HbU|HbU].
      * right.
        destruct (Rle_lt_or_eq_dec _ _ HQA) as [Hqa|Hqe].
        -- assert (Hm : exists X, tri_open A B C X /\ tri_open Q U P X).
           { apply wedge_cab; try assumption.
             - replace (cross Q U P) with (cross P Q U)
                 by (rewrite cross_cycle; reflexivity). exact Hs.
             - apply prod_neg; assumption.
             - apply prod_pos_neg; [exact HQC | exact Hqa]. }
           destruct Hm as [X [Ht HsX]]. exists X. split;
             [exact Ht | apply tri_open_rot; apply tri_open_rot; exact HsX].
        -- assert (HaQ : 0 < cross B C Q).
           { assert (E := cross_sum3 A B C Q). lra. }
           destruct (Rlt_dec 0 (cross B C U)) as [HaU|HaU].
           ++ destruct (meet_vertex A B C P Q U U Hd Hs
                         (or_intror (or_intror (or_introl eq_refl)))
                         (conj Hu (conj HaU HbU))) as [X [Ht HsX]].
              exists X. split; assumption.
           ++ apply Rnot_lt_le in HaU.
              destruct (Rle_lt_or_eq_dec _ _ HaU) as [HaUn|HaU0].
              ** assert (Hm : exists X, tri_open B C A X /\ tri_open Q U P X).
                 { apply wedge_edges.
                   - replace (cross B C A) with (cross A B C)
                       by apply cross_cycle. exact Hd.
                   - replace (cross Q U P) with (cross P Q U)
                       by (rewrite cross_cycle; reflexivity). exact Hs.
                   - apply prod_pos_neg; [exact HaQ | exact HaUn].
                   - apply prod_neg; [exact HQUB | exact HQC]. }
                 destruct Hm as [X [Ht HsX]]. exists X. split.
                 --- destruct Ht as [H1 [H2 H3]]. repeat split; assumption.
                 --- destruct HsX as [H1 [H2 H3]]. repeat split; assumption.
              ** set (Mpt := convex_combination A U (1 / 2)).
                 assert (HMopen : tri_open A B C Mpt).
                 { repeat split; unfold Mpt; rewrite cross_combo.
                   - rewrite (cross_third_eq_first A B). lra.
                   - rewrite HaU0. rewrite <- (cross_cycle A B C). lra.
                   - rewrite (cross_third_eq_second C A). lra. }
                 assert (HpqM : 0 < cross P Q Mpt).
                 { unfold Mpt. rewrite cross_combo. lra. }
                 assert (HupM : 0 < cross U P Mpt).
                 { unfold Mpt. rewrite cross_combo.
                   rewrite (cross_third_eq_first U P). lra. }
                 assert (HquM : cross Q U Mpt = 0).
                 { unfold Mpt. rewrite cross_combo. rewrite Hqe.
                   rewrite (cross_third_eq_second Q U). ring. }
                 assert (HquP : 0 < cross Q U P).
                 { replace (cross Q U P) with (cross P Q U)
                     by (rewrite cross_cycle; reflexivity). exact Hs. }
                 apply (nudge_meet A B C P Q U Mpt P Hd HMopen).
                 --- apply Rlt_le. exact HpqM.
                 --- rewrite HquM. apply Rle_refl.
                 --- apply Rlt_le. exact HupM.
                 --- rewrite (cross_third_eq_first P Q). apply Rle_refl.
                 --- apply Rlt_le. exact HquP.
                 --- rewrite (cross_third_eq_second U P). apply Rle_refl.
                 --- intros Hz. exfalso. apply (Rlt_not_eq 0 _ HpqM).
                     symmetry. exact Hz.
                 --- intros _. exact HquP.
                 --- intros Hz. exfalso. apply (Rlt_not_eq 0 _ HupM).
                     symmetry. exact Hz.
      * apply Rnot_lt_le in HbU.
        left. unfold some_outer. right. right. left. repeat split.
        -- apply Rlt_le. exact HbP.
        -- apply Rlt_le. exact HbQ.
        -- exact HbU.
    + apply Rnot_lt_le in HQC.
      left. apply some_outer_qu. repeat split; [exact HQA | apply Rlt_le; exact HQUB | exact HQC].
Qed.

Lemma some_outer_rot_T : forall A B C P Q U,
  some_outer B C A P Q U -> some_outer A B C P Q U.
Proof.
  intros A B C P Q U [H|[H|[H|[H|[H|H]]]]].
  - right. left. exact H.
  - do 2 right. left. exact H.
  - left. exact H.
  - apply some_outer_pq. apply outer3_rot. apply outer3_rot. exact H.
  - apply some_outer_qu. apply outer3_rot. apply outer3_rot. exact H.
  - apply some_outer_up. apply outer3_rot. apply outer3_rot. exact H.
Qed.

Lemma some_outer_rot2_T : forall A B C P Q U,
  some_outer C A B P Q U -> some_outer A B C P Q U.
Proof.
  intros A B C P Q U H.
  apply (some_outer_rot_T A B C).
  apply (some_outer_rot_T B C A). exact H.
Qed.

Lemma some_outer_rot_S : forall A B C P Q U,
  some_outer A B C Q U P -> some_outer A B C P Q U.
Proof.
  intros A B C P Q U [H|[H|[H|[H|[H|H]]]]].
  - left. apply outer3_rot. apply outer3_rot. exact H.
  - right. left. apply outer3_rot. apply outer3_rot. exact H.
  - do 2 right. left. apply outer3_rot. apply outer3_rot. exact H.
  - apply some_outer_qu. exact H.
  - apply some_outer_up. exact H.
  - apply some_outer_pq. exact H.
Qed.

(* P on line AB. The signed area of PQU splits across the QU slacks at A and B. *)
Lemma z1_area : forall A B C P Q U,
  0 < cross A B C ->
  cross A B P = 0 ->
  cross P Q U * cross A B C =
    cross B C P * cross Q U A + cross C A P * cross Q U B.
Proof.
  intros A B C P Q U Hd HcP.
  assert (E := s_qua_id A B C P Q U).
  rewrite HcP in E. ring_simplify in E.
  assert (G := qu_gap_b A B C Q U Hd).
  assert (Sa := cross_sum3 A B C P). rewrite HcP in Sa.
  assert (E1 : cross P Q U * cross A B C =
      cross A B C * cross Q U A
      + cross C A P * (cross Q U B - cross Q U A)).
  { rewrite E. rewrite G. ring. }
  replace (cross B C P) with (cross A B C - cross C A P) by lra.
  rewrite E1. ring.
Qed.

Lemma z1_nonpos : forall A B C P Q U,
  cross A B P = 0 ->
  cross A B Q <= 0 ->
  cross A B U <= 0 ->
  some_outer A B C P Q U.
Proof.
  intros A B C P Q U HcP Hq Hu.
  apply some_outer_ab. repeat split; [rewrite HcP; apply Rle_refl | exact Hq | exact Hu].
Qed.

(* P beyond A on line AB, and both Q and U strictly on C's side of AB. *)
Lemma z1_pos : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  cross A B P = 0 -> cross C A P < 0 -> 0 < cross B C P ->
  0 < cross A B Q -> 0 < cross A B U ->
  some_outer A B C P Q U \/
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs HcP HbP HaP Hq Hu.
  assert (HPQA : cross P Q A < 0).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite (z1_pqA A B C P Q HcP).
    replace (0 * cross A B C) with 0 by ring.
    apply prod_pos_neg; assumption. }
  assert (HPQB : cross P Q B < 0).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite (z1_pqB A B C P Q HcP).
    replace (0 * cross A B C) with 0 by ring.
    apply prod_neg; [lra | exact HaP]. }
  destruct (Rlt_dec 0 (cross P Q C)) as [HPC|HPC].
  - destruct (Rlt_dec 0 (cross C A Q)) as [HbQ|HbQ].
    + right. apply wedge_cab; try assumption.
      * apply prod_neg; assumption.
      * apply prod_pos_neg; [exact HPC | exact HPQA].
    + apply Rnot_lt_le in HbQ.
      destruct (Rlt_dec (cross B C Q) 0) as [HaQn|HaQ].
      * right. apply wedge_bca; try assumption.
        -- apply prod_pos_neg; [exact HaP | exact HaQn].
        -- apply prod_neg; [exact HPQB | exact HPC].
      * apply Rnot_lt_le in HaQ.
        destruct (Rlt_dec 0 (cross C A U)) as [HbU|HbU].
        -- assert (HQA : cross Q U A < 0).
           { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
             rewrite (qua_bb A B C Q U).
             replace (0 * cross A B C) with 0 by ring.
             assert (Hle : cross C A Q * cross A B U <= 0).
             { assert (Hc : cross C A Q * cross A B U <= 0 * cross A B U).
               { apply Rmult_le_compat_r; [apply Rlt_le; exact Hu | exact HbQ]. }
               replace (0 * cross A B U) with 0 in Hc by ring. exact Hc. }
             assert (Hneg : - (cross A B Q * cross C A U) < 0).
             { assert (Hp : 0 < cross A B Q * cross C A U).
               { apply Rmult_lt_0_compat; assumption. }
               lra. }
             assert (Hsum : cross C A Q * cross A B U
                            - cross A B Q * cross C A U < 0) by lra.
             exact Hsum. }
           assert (HQUB : cross Q U B < 0).
           { assert (E := z1_area A B C P Q U Hd HcP).
             assert (Hap : cross B C P * cross Q U A < 0).
             { apply prod_pos_neg; [exact HaP | exact HQA]. }
             assert (Hbp : 0 < cross C A P * cross Q U B).
             { assert (Hsd : 0 < cross P Q U * cross A B C).
               { apply Rmult_lt_0_compat; assumption. }
               assert (Hdiff : 0 < cross P Q U * cross A B C
                                 - cross B C P * cross Q U A) by lra.
               replace (cross P Q U * cross A B C - cross B C P * cross Q U A)
                 with (cross C A P * cross Q U B) in Hdiff by (rewrite E; ring).
               exact Hdiff. }
             destruct (Rle_dec 0 (cross Q U B)) as [Hge|Hlt].
             - exfalso.
               assert (Hle : cross C A P * cross Q U B <= cross C A P * 0).
               { apply Rmult_le_compat_neg_l; lra. }
               replace (cross C A P * 0) with 0 in Hle by ring.
               apply (Rle_not_lt 0 _ Hle). exact Hbp.
             - apply Rnot_le_lt. exact Hlt. }
           destruct (Rlt_dec 0 (cross Q U C)) as [HQC|HQC].
           ++ destruct (Rle_lt_or_eq_dec _ _ HbQ) as [HbQn|HbQ0].
              ** right.
                 assert (Hm : exists X, tri_open C A B X /\ tri_open Q U P X).
                 { apply wedge_edges.
                   - replace (cross C A B) with (cross A B C) by apply cross_cycle2.
                     exact Hd.
                   - replace (cross Q U P) with (cross P Q U)
                       by (rewrite cross_cycle; reflexivity). exact Hs.
                   - apply prod_neg; assumption.
                   - apply prod_pos_neg; [exact HQC | exact HQA]. }
                 destruct Hm as [X [Ht HsX]]. exists X. split.
                 --- apply tri_open_rot. exact Ht.
                 --- apply tri_open_rot. apply tri_open_rot. exact HsX.
              ** assert (HaQpos : 0 < cross B C Q).
                 { destruct (Rle_lt_or_eq_dec 0 (cross B C Q) HaQ) as [Hgt|Heq].
                   - exact Hgt.
                   - exfalso.
                     assert (HcQd : cross A B Q = cross A B C).
                     { assert (Es := cross_sum3 A B C Q). lra. }
                     assert (Ebb := qua_bb A B C Q U).
                     rewrite HbQ0 in Ebb. rewrite HcQd in Ebb.
                     assert (Hqa : cross Q U A = - cross C A U).
                     { apply Rmult_eq_reg_l with (r := cross A B C).
                       - replace (cross A B C * cross Q U A)
                           with (cross Q U A * cross A B C) by ring.
                         rewrite Ebb. ring.
                       - apply not_eq_sym. apply Rlt_not_eq. exact Hd. }
                     assert (Hz : cross Q U C = 0).
                     { assert (Egc := qu_gap_c A B C Q U Hd).
                       rewrite Hqa in Egc. rewrite HbQ0 in Egc. lra. }
                     apply (Rlt_not_eq 0 (cross Q U C) HQC). symmetry. exact Hz. }
                 right.
                 set (room := seg_room (cross B C Q) (cross B C U)).
                 assert (Hroom : 0 < room).
                 { unfold room. apply seg_room_pos. exact HaQpos. }
                 set (t := Rmin (room / 2) (1 / 2)).
                 assert (Ht0 : 0 < t).
                 { unfold t. apply Rmin_pos; lra. }
                 assert (Ht1 : t < 1).
                 { assert (Hle : t <= 1 / 2) by (unfold t; apply Rmin_r). lra. }
                 assert (Htroom : t < room).
                 { assert (Hle : t <= room / 2) by (unfold t; apply Rmin_l).
                   apply Rle_lt_trans with (r2 := room / 2); [exact Hle | lra]. }
                 set (Mpt := convex_combination Q U t).
                 assert (HcM : 0 < cross A B Mpt).
                 { unfold Mpt. rewrite cross_combo.
                   assert (H1 : 0 < (1 - t) * cross A B Q).
                   { apply Rmult_lt_0_compat; lra. }
                   assert (H2 : 0 < t * cross A B U).
                   { apply Rmult_lt_0_compat; assumption. }
                   lra. }
                 assert (HbM : 0 < cross C A Mpt).
                 { unfold Mpt. rewrite cross_combo. rewrite HbQ0.
                   replace ((1 - t) * 0 + t * cross C A U)
                     with (t * cross C A U) by ring.
                   apply Rmult_lt_0_compat; assumption. }
                 assert (HaM : 0 < cross B C Mpt).
                 { unfold Mpt. rewrite cross_combo.
                   apply slack_pos_room; [exact HaQpos | apply Rlt_le; exact Ht0 |
                     exact Htroom]. }
                 assert (HpqM : 0 < cross P Q Mpt).
                 { unfold Mpt. rewrite cross_combo.
                   rewrite (cross_third_eq_second P Q).
                   replace ((1 - t) * 0 + t * cross P Q U)
                     with (t * cross P Q U) by ring.
                   apply Rmult_lt_0_compat; assumption. }
                 assert (HupM : 0 < cross U P Mpt).
                 { unfold Mpt. rewrite cross_combo.
                   rewrite (cross_third_eq_first U P).
                   replace (cross U P Q) with (cross P Q U)
                     by (rewrite <- cross_cycle; reflexivity).
                   replace ((1 - t) * cross P Q U + t * 0)
                     with ((1 - t) * cross P Q U) by ring.
                   apply Rmult_lt_0_compat; lra. }
                 assert (HquM : cross Q U Mpt = 0).
                 { unfold Mpt. rewrite cross_combo.
                   rewrite (cross_third_eq_first Q U).
                   rewrite (cross_third_eq_second Q U). ring. }
                 assert (HquP : 0 < cross Q U P).
                 { replace (cross Q U P) with (cross P Q U)
                     by (rewrite cross_cycle; reflexivity). exact Hs. }
                 apply (nudge_meet A B C P Q U Mpt P Hd).
                 --- repeat split; assumption.
                 --- apply Rlt_le. exact HpqM.
                 --- rewrite HquM. apply Rle_refl.
                 --- apply Rlt_le. exact HupM.
                 --- rewrite (cross_third_eq_first P Q). apply Rle_refl.
                 --- apply Rlt_le. exact HquP.
                 --- rewrite (cross_third_eq_second U P). apply Rle_refl.
                 --- intros Hz. exfalso.
                     apply (Rlt_not_eq 0 _ HpqM). symmetry. exact Hz.
                 --- intros _. exact HquP.
                 --- intros Hz. exfalso.
                     apply (Rlt_not_eq 0 _ HupM). symmetry. exact Hz.
           ++ apply Rnot_lt_le in HQC.
              left. apply some_outer_qu. repeat split;
                [apply Rlt_le; exact HQA | apply Rlt_le; exact HQUB | exact HQC].
        -- apply Rnot_lt_le in HbU.
           left. unfold some_outer. do 2 right. left. repeat split.
           ++ apply Rlt_le. exact HbP.
           ++ exact HbQ.
           ++ exact HbU.
  - apply Rnot_lt_le in HPC.
    left. apply some_outer_pq. repeat split;
      [apply Rlt_le; exact HPQA | apply Rlt_le; exact HPQB | exact HPC].
Qed.

(* U lies on line AB as well, on the same side of A as P, and Q is strictly
   on C's side. The far vertex U is then strictly outside edge CA. *)
Lemma z1_cu0 : forall A B C P Q U,
  0 < cross A B C -> 0 < cross P Q U ->
  cross A B P = 0 -> cross C A P < 0 -> 0 < cross B C P ->
  0 < cross A B Q -> cross A B U = 0 ->
  some_outer A B C P Q U \/
  exists X, tri_open A B C X /\ tri_open P Q U X.
Proof.
  intros A B C P Q U Hd Hs HcP HbP HaP Hq HcU.
  assert (HPQA : cross P Q A < 0).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite (z1_pqA A B C P Q HcP).
    replace (0 * cross A B C) with 0 by ring.
    apply prod_pos_neg; assumption. }
  assert (HPQB : cross P Q B < 0).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    rewrite (z1_pqB A B C P Q HcP).
    replace (0 * cross A B C) with 0 by ring.
    apply prod_neg; [lra | exact HaP]. }
  assert (Hsd : cross P Q U * cross A B C =
      cross A B C * cross Q U A + cross C A P * cross A B Q).
  { assert (E := z1_area A B C P Q U Hd HcP).
    assert (G := qu_gap_b A B C Q U Hd). rewrite HcU in G.
    assert (Sa := cross_sum3 A B C P). rewrite HcP in Sa.
    rewrite E. replace (cross Q U B) with (cross Q U A + cross A B Q) by lra.
    replace (cross B C P) with (cross A B C - cross C A P) by lra. ring. }
  assert (HQA : 0 < cross Q U A).
  { apply Rmult_lt_reg_r with (r := cross A B C); [exact Hd |].
    replace (0 * cross A B C) with 0 by ring.
    assert (Hpos : 0 < cross P Q U * cross A B C
                     - cross C A P * cross A B Q).
    { assert (Hs0 : 0 < cross P Q U * cross A B C).
      { apply Rmult_lt_0_compat; assumption. }
      assert (Hn : cross C A P * cross A B Q < 0) by (apply prod_neg; assumption).
      lra. }
    replace (cross Q U A * cross A B C)
      with (cross P Q U * cross A B C - cross C A P * cross A B Q)
      by (rewrite Hsd; ring).
    exact Hpos. }
  assert (HbU : cross C A U < 0).
  {     assert (E0 : cross Q U A * cross A B C =
        - cross A B Q * cross C A U).
    { assert (E := qua_bb A B C Q U). rewrite HcU in E. ring_simplify in E.
      exact E. }
    assert (Hlt : cross A B Q * cross C A U < 0).
    { assert (Hp : 0 < cross Q U A * cross A B C).
      { apply Rmult_lt_0_compat; assumption. }
      rewrite E0 in Hp. lra. }
    destruct (Rle_dec 0 (cross C A U)) as [Hge|HltU].
    - exfalso.
      assert (Hge0 : 0 <= cross A B Q * cross C A U).
      { apply Rmult_le_pos; [apply Rlt_le; exact Hq | exact Hge]. }
      apply (Rle_not_lt (cross A B Q * cross C A U) 0 Hge0). exact Hlt.
    - apply Rnot_le_lt. exact HltU. }
  assert (HaU : 0 < cross B C U).
  { assert (E := cross_sum3 A B C U). rewrite HcU in E. lra. }
  destruct (Rlt_dec 0 (cross C A Q)) as [HbQ|HbQ].
  - destruct (Rlt_dec 0 (cross P Q C)) as [HPC|HPC].
    + destruct (Rlt_dec (cross B C Q) 0) as [HaQn|HaQ].
      * right. apply wedge_bca; try assumption.
        -- apply prod_pos_neg; [exact HaP | exact HaQn].
        -- apply prod_neg; [exact HPQB | exact HPC].
      * apply Rnot_lt_le in HaQ.
        destruct (Rle_lt_or_eq_dec 0 (cross B C Q) HaQ) as [HaQgt|HaQ0].
        -- right.
           destruct (meet_vertex A B C P Q U Q Hd Hs
                      (or_intror (or_introl eq_refl))
                      (conj Hq (conj HaQgt HbQ))) as [X [Ht HsX]].
           exists X. split; assumption.
        -- right.
           set (room := seg_room (cross C A Q) (cross C A U)).
           assert (Hroom : 0 < room).
           { unfold room. apply seg_room_pos. exact HbQ. }
           set (t := Rmin (room / 2) (1 / 2)).
           assert (Ht0 : 0 < t).
           { unfold t. apply Rmin_pos; lra. }
           assert (Ht1 : t < 1).
           { assert (Hle : t <= 1 / 2) by (unfold t; apply Rmin_r). lra. }
           assert (Htroom : t < room).
           { assert (Hle : t <= room / 2) by (unfold t; apply Rmin_l).
             apply Rle_lt_trans with (r2 := room / 2); [exact Hle | lra]. }
           set (Mpt := convex_combination Q U t).
           assert (HcM : 0 < cross A B Mpt).
           { unfold Mpt. rewrite cross_combo. rewrite HcU.
             replace ((1 - t) * cross A B Q + t * 0)
               with ((1 - t) * cross A B Q) by ring.
             apply Rmult_lt_0_compat; lra. }
           assert (HaM : 0 < cross B C Mpt).
           { unfold Mpt. rewrite cross_combo. rewrite <- HaQ0.
             replace ((1 - t) * 0 + t * cross B C U)
               with (t * cross B C U) by ring.
             apply Rmult_lt_0_compat; assumption. }
           assert (HbM : 0 < cross C A Mpt).
           { unfold Mpt. rewrite cross_combo.
             apply slack_pos_room; [exact HbQ | apply Rlt_le; exact Ht0 |
               exact Htroom]. }
           assert (HpqM : 0 < cross P Q Mpt).
           { unfold Mpt. rewrite cross_combo.
             rewrite (cross_third_eq_second P Q).
             replace ((1 - t) * 0 + t * cross P Q U)
               with (t * cross P Q U) by ring.
             apply Rmult_lt_0_compat; assumption. }
           assert (HupM : 0 < cross U P Mpt).
           { unfold Mpt. rewrite cross_combo.
             rewrite (cross_third_eq_first U P).
             replace (cross U P Q) with (cross P Q U)
               by (rewrite <- cross_cycle; reflexivity).
             replace ((1 - t) * cross P Q U + t * 0)
               with ((1 - t) * cross P Q U) by ring.
             apply Rmult_lt_0_compat; lra. }
           assert (HquM : cross Q U Mpt = 0).
           { unfold Mpt. rewrite cross_combo.
             rewrite (cross_third_eq_first Q U).
             rewrite (cross_third_eq_second Q U). ring. }
           assert (HquP : 0 < cross Q U P).
           { replace (cross Q U P) with (cross P Q U)
               by (rewrite cross_cycle; reflexivity). exact Hs. }
           apply (nudge_meet A B C P Q U Mpt P Hd).
           --- repeat split; assumption.
           --- apply Rlt_le. exact HpqM.
           --- rewrite HquM. apply Rle_refl.
           --- apply Rlt_le. exact HupM.
           --- rewrite (cross_third_eq_first P Q). apply Rle_refl.
           --- apply Rlt_le. exact HquP.
           --- rewrite (cross_third_eq_second U P). apply Rle_refl.
           --- intros Hz. exfalso.
               apply (Rlt_not_eq 0 _ HpqM). symmetry. exact Hz.
           --- intros _. exact HquP.
           --- intros Hz. exfalso.
               apply (Rlt_not_eq 0 _ HupM). symmetry. exact Hz.
    + apply Rnot_lt_le in HPC.
      left. apply some_outer_pq. repeat split;
        [apply Rlt_le; exact HPQA | apply Rlt_le; exact HPQB | exact HPC].
  - apply Rnot_lt_le in HbQ.
    left. unfold some_outer. do 2 right. left. repeat split.
    + apply Rlt_le. exact HbP.
    + exact HbQ.
    + apply Rlt_le. exact HbU.
Qed.

(* Assumptions: sig_not_dec, sig_forall_dec, functional_extensionality_dep. *)
Print Assumptions tri_open_rot.
Print Assumptions tri_open_rot2.
Print Assumptions outer3_rot.
Print Assumptions outer3_rot2.
Print Assumptions some_outer_swap.
Print Assumptions meet_swap.
Print Assumptions meet_rot_T.
Print Assumptions meet_rot_S.
Print Assumptions surround_open_A.
Print Assumptions skB_rot.
Print Assumptions skC_rot.
Print Assumptions skA_rot.
Print Assumptions spikes_ccw.
Print Assumptions spikes_ccw_rot.
Print Assumptions spikes_ccw_rot2.
Print Assumptions spikes_cw_false.
Print Assumptions spikes_cw_rot_false.
Print Assumptions spikes_cw_rot2_false.
Print Assumptions spikes_cert.
Print Assumptions qu_gap_b.
Print Assumptions qu_gap_c.
Print Assumptions z1_pqA.
Print Assumptions z1_pqB.
Print Assumptions z1_upA.
Print Assumptions z1_upB.
Print Assumptions wedge_cab.
Print Assumptions wedge_bca.
Print Assumptions z1_succ.
Print Assumptions face_pos.
Print Assumptions nudge_meet.
Print Assumptions z1_pred.
Print Assumptions some_outer_rot_T.
Print Assumptions some_outer_rot2_T.
Print Assumptions some_outer_rot_S.
Print Assumptions z1_area.
Print Assumptions z1_nonpos.
Print Assumptions z1_pos.
Print Assumptions z1_cu0.
