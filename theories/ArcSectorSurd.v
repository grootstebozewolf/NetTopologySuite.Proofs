(* ============================================================================
   NetTopologySuite.Proofs.ArcSectorSurd
   ----------------------------------------------------------------------------
   Inventory row T4b: exact arc-sector membership for COMPUTED intersection
   points.  Segment/circle, circle/circle and ray/circle intersections are
   algebraic of degree 2 over the exact input data:

       P = U + sqrt D * V,      U, V in Q^2,  D in Q,  D >= 0

   (segment: U the exact foot of the centre, V the segment direction,
   D = h^2 / l^2; circles: U the exact radical foot, V the perpendicular of
   the centre line, D = h^2 / d^2; ray: U = (ox, py), V = (1, 0)).  The T4a
   sector predicate (ArcSectorExact.asx_sector) only asks, of query-dependent
   quantities, whether they are >= 0, = 0 or > 0, and every such quantity is
   LINEAR in P, so it is a + b sqrt D with a, b in Q.  Its sign is decidable
   exactly:
     qs_pos D a b    a + b sqrt D > 0   (same signs, or compare a^2 with b^2 D)
     qs_zero D a b   a + b sqrt D = 0
     qs_nonneg D a b
   so the decision needs no rounding and no atan2 (the T4a differential
   showed an exact test on the ROUNDED point loses exact shared-vertex
   hits; on the algebraic point it cannot).

     asxs_sector_correct   asxs_sector D ... U V = true  <->
                           asx_sector O A B C (U + sqrt D * V)    (D >= 0)
     qs_*_ok               the three sign tests against the real value
   With ArcSectorExact.asx_sector_on_circle_iff this is arc_span_contains for
   the intersection points (they lie on the circle by construction).
   claimId: t4b-sector-surd.  witness: asxs_sector_correct.
   3-axiom host.  No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra QArith Qreals.
From NTS.Proofs Require Import Distance CurveGeometry ArcSectorExact.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Exact signs in Q(sqrt D).                                              *)
(* -------------------------------------------------------------------------- *)

Definition qs_val (D a b : Q) : R := Q2R a + Q2R b * sqrt (Q2R D).

Definition qs_pos (D a b : Q) : bool :=
  if Qle_bool 0 a then
    if Qle_bool 0 b then negb (Qeq_bool a 0) || (negb (Qeq_bool b 0) && negb (Qeq_bool D 0))
    else negb (Qle_bool (a * a) (b * b * D))
  else if Qle_bool b 0 then false
  else negb (Qle_bool (b * b * D) (a * a)).

Definition qs_zero (D a b : Q) : bool :=
  if Qeq_bool b 0 then Qeq_bool a 0
  else Qle_bool (a * b) 0 && Qeq_bool (a * a) (b * b * D).

Definition qs_nonneg (D a b : Q) : bool := qs_pos D a b || qs_zero D a b.

Lemma qs_Qle_false : forall x y, Qle_bool x y = false -> Q2R y < Q2R x.
Proof.
  intros x y H. apply asx_negb_Qle_R. rewrite H. reflexivity.
Qed.

Lemma qs_Qeq_false : forall x y, Qeq_bool x y = false -> Q2R x <> Q2R y.
Proof.
  intros x y H E. apply asx_Qeq_bool_R in E. congruence.
Qed.

Lemma qs_sq_lt : forall u v, 0 <= u -> 0 <= v -> (u < v <-> u * u < v * v).
Proof. intros u v Hu Hv. split; intro H; nra. Qed.

Lemma qs_pos_ok : forall D a b, 0 <= Q2R D ->
  qs_pos D a b = true <-> 0 < qs_val D a b.
Proof.
  intros D a b HD. unfold qs_pos, qs_val.
  set (s := sqrt (Q2R D)).
  assert (Hs : 0 <= s) by apply sqrt_pos.
  assert (Hss : s * s = Q2R D) by (apply sqrt_sqrt; exact HD).
  pose proof asx_Q2R_0 as Z.
  assert (Ds : Q2R D = 0 <-> s = 0).
  { split; intro H; [unfold s; rewrite H; apply sqrt_0 | nra]. }
  destruct (Qle_bool 0 a) eqn:Ha.
  - apply asx_Qle_bool_R in Ha. rewrite Z in Ha.
    destruct (Qle_bool 0 b) eqn:Hb.
    + apply asx_Qle_bool_R in Hb. rewrite Z in Hb.
      destruct (Qeq_bool a 0) eqn:Ea; destruct (Qeq_bool b 0) eqn:Eb;
        destruct (Qeq_bool D 0) eqn:ED; cbn;
        repeat match goal with
               | H : Qeq_bool _ _ = true |- _ => apply asx_Qeq_bool_R in H; rewrite Z in H
               | H : Qeq_bool _ _ = false |- _ => apply qs_Qeq_false in H; rewrite Z in H
               end;
        try (split; [discriminate|]; intro; exfalso; nra);
        try (split; [intros _|reflexivity]).
      all: try (assert (0 < Q2R a) by lra; nra).
      all: assert (0 < s) by (destruct (Req_dec s 0) as [E|E]; [apply Ds in E; contradiction | lra]);
           assert (0 < Q2R b) by lra; nra.
    + apply qs_Qle_false in Hb. rewrite Z in Hb.
      rewrite asx_negb_Qle_R, !Q2R_mult.
      assert (Bs : 0 <= - (Q2R b * s)) by nra.
      split; intro H.
      * assert (- (Q2R b * s) < Q2R a) by (apply (proj2 (qs_sq_lt _ _ Bs Ha)); nra). lra.
      * assert (- (Q2R b * s) < Q2R a) by lra.
        apply (proj1 (qs_sq_lt _ _ Bs Ha)) in H0. nra.
  - apply qs_Qle_false in Ha. rewrite Z in Ha.
    destruct (Qle_bool b 0) eqn:Hb.
    + apply asx_Qle_bool_R in Hb. rewrite Z in Hb.
      split; [discriminate|]. intro H. exfalso. nra.
    + apply qs_Qle_false in Hb. rewrite Z in Hb.
      rewrite asx_negb_Qle_R, !Q2R_mult.
      assert (Bs : 0 <= Q2R b * s) by nra.
      assert (Am : 0 <= - Q2R a) by lra.
      split; intro H.
      * assert (- Q2R a < Q2R b * s) by (apply (proj2 (qs_sq_lt _ _ Am Bs)); nra). lra.
      * assert (- Q2R a < Q2R b * s) by lra.
        apply (proj1 (qs_sq_lt _ _ Am Bs)) in H0. nra.
Qed.

Lemma qs_zero_ok : forall D a b, 0 <= Q2R D ->
  qs_zero D a b = true <-> qs_val D a b = 0.
Proof.
  intros D a b HD. unfold qs_zero, qs_val.
  set (s := sqrt (Q2R D)).
  assert (Hs : 0 <= s) by apply sqrt_pos.
  assert (Hss : s * s = Q2R D) by (apply sqrt_sqrt; exact HD).
  pose proof asx_Q2R_0 as Z.
  destruct (Qeq_bool b 0) eqn:Eb.
  - apply asx_Qeq_bool_R in Eb. rewrite Z in Eb. rewrite Eb, asx_Qeq_bool_R, Z.
    split; intro H; lra.
  - apply qs_Qeq_false in Eb. rewrite Z in Eb.
    rewrite Bool.andb_true_iff, asx_Qle_bool_R, asx_Qeq_bool_R, !Q2R_mult, Z.
    split.
    + intros [H1 H2].
      assert (P : (Q2R a + Q2R b * s) * (Q2R a - Q2R b * s) = 0).
      { replace ((Q2R a + Q2R b * s) * (Q2R a - Q2R b * s))
          with (Q2R a * Q2R a - Q2R b * Q2R b * (s * s)) by ring.
        rewrite Hss. lra. }
      apply Rmult_integral in P as [P|P]; [exact P|].
      assert (Ea : Q2R a = Q2R b * s) by lra.
      assert (Q2R b * Q2R b * s <= 0) by (rewrite Ea in H1; nra).
      assert (0 < Q2R b * Q2R b) by (destruct (Rlt_le_dec 0 (Q2R b)); nra).
      assert (s = 0) by nra.
      rewrite Ea. subst s. nra.
    + intro H. assert (Ea : Q2R a = - (Q2R b * s)) by lra.
      split; [rewrite Ea; nra | rewrite Ea, <- Hss; ring].
Qed.

Lemma qs_nonneg_ok : forall D a b, 0 <= Q2R D ->
  qs_nonneg D a b = true <-> 0 <= qs_val D a b.
Proof.
  intros D a b HD. unfold qs_nonneg. rewrite Bool.orb_true_iff, qs_pos_ok, qs_zero_ok by exact HD.
  split; [intros [H|H]; lra | intro H; destruct (Rle_lt_or_eq_dec _ _ H); [left; lra | right; lra]].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The T4a sector predicate on a point of Q(sqrt D)^2.                    *)
(* -------------------------------------------------------------------------- *)

(* A query offset q = (qx0 + qx1 sqrt D, qy0 + qy1 sqrt D) against fixed u. *)
Definition asxs_cross_uq (ux uy qx0 qx1 qy0 qy1 : Q) : Q * Q :=
  ((ux * qy0 - uy * qx0)%Q, (ux * qy1 - uy * qx1)%Q).
Definition asxs_cross_qu (qx0 qx1 qy0 qy1 ux uy : Q) : Q * Q :=
  ((qx0 * uy - qy0 * ux)%Q, (qx1 * uy - qy1 * ux)%Q).
Definition asxs_dot_uq (ux uy qx0 qx1 qy0 qy1 : Q) : Q * Q :=
  ((ux * qx0 + uy * qy0)%Q, (ux * qx1 + uy * qy1)%Q).

Definition asxs_cone_vals (D s : Q) (x y : Q * Q) (d : Q) (e : Q * Q) : bool :=
  if Qlt_le_dec 0 s then qs_nonneg D (fst x) (snd x) && qs_nonneg D (fst y) (snd y)
  else if Qlt_le_dec s 0 then qs_nonneg D (fst x) (snd x) || qs_nonneg D (fst y) (snd y)
  else if Qlt_le_dec d 0 then qs_nonneg D (fst x) (snd x)
  else qs_zero D (fst x) (snd x) && qs_pos D (fst e) (snd e).

Definition asxs_cone (D ax ay cx cy qx0 qx1 qy0 qy1 : Q) : bool :=
  asxs_cone_vals D (asxq_cross ax ay cx cy) (asxs_cross_uq ax ay qx0 qx1 qy0 qy1)
    (asxs_cross_qu qx0 qx1 qy0 qy1 cx cy) (asxq_dot ax ay cx cy)
    (asxs_dot_uq ax ay qx0 qx1 qy0 qy1).

Definition asxs_same_dir (D ux uy qx0 qx1 qy0 qy1 : Q) : bool :=
  let c := asxs_cross_uq ux uy qx0 qx1 qy0 qy1 in
  let d := asxs_dot_uq ux uy qx0 qx1 qy0 qy1 in
  qs_zero D (fst c) (snd c) && qs_pos D (fst d) (snd d).

(* Centre O, arc A -> B -> C, query point U + sqrt D * V. *)
Definition asxs_sector (D ox oy ax ay bx by_ cx cy ux uy vx vy : Q) : bool :=
  let ax' := (ax - ox)%Q in let ay' := (ay - oy)%Q in
  let bx' := (bx - ox)%Q in let by' := (by_ - oy)%Q in
  let cx' := (cx - ox)%Q in let cy' := (cy - oy)%Q in
  let qx0 := (ux - ox)%Q in let qy0 := (uy - oy)%Q in
  if asxq_same_dir ax' ay' cx' cy' then
    (if asxq_same_dir ax' ay' bx' by' then asxs_same_dir D ax' ay' qx0 vx qy0 vy else true)
  else if asxq_cone ax' ay' cx' cy' bx' by' then asxs_cone D ax' ay' cx' cy' qx0 vx qy0 vy
  else asxs_cone D cx' cy' ax' ay' qx0 vx qy0 vy.

(* the real offsets of the query point *)
Definition asxs_qR (D q0 q1 : Q) : R := Q2R q0 + Q2R q1 * sqrt (Q2R D).

Lemma asxs_cross_uq_val : forall D ux uy qx0 qx1 qy0 qy1,
  let c := asxs_cross_uq ux uy qx0 qx1 qy0 qy1 in
  qs_val D (fst c) (snd c)
  = asx_cross (Q2R ux) (Q2R uy) (asxs_qR D qx0 qx1) (asxs_qR D qy0 qy1).
Proof.
  intros. unfold c, asxs_cross_uq, qs_val, asxs_qR, asx_cross. cbn [fst snd].
  rewrite !Q2R_minus, !Q2R_mult. ring.
Qed.

Lemma asxs_cross_qu_val : forall D qx0 qx1 qy0 qy1 ux uy,
  let c := asxs_cross_qu qx0 qx1 qy0 qy1 ux uy in
  qs_val D (fst c) (snd c)
  = asx_cross (asxs_qR D qx0 qx1) (asxs_qR D qy0 qy1) (Q2R ux) (Q2R uy).
Proof.
  intros. unfold c, asxs_cross_qu, qs_val, asxs_qR, asx_cross. cbn [fst snd].
  rewrite !Q2R_minus, !Q2R_mult. ring.
Qed.

Lemma asxs_dot_uq_val : forall D ux uy qx0 qx1 qy0 qy1,
  let c := asxs_dot_uq ux uy qx0 qx1 qy0 qy1 in
  qs_val D (fst c) (snd c)
  = asx_dot (Q2R ux) (Q2R uy) (asxs_qR D qx0 qx1) (asxs_qR D qy0 qy1).
Proof.
  intros. unfold c, asxs_dot_uq, qs_val, asxs_qR, asx_dot. cbn [fst snd].
  rewrite !Q2R_plus, !Q2R_mult. ring.
Qed.

Lemma asxs_cone_vals_correct : forall D s x y d e, 0 <= Q2R D ->
  asxs_cone_vals D s x y d e = true
  <-> asx_cone_vals (Q2R s) (qs_val D (fst x) (snd x)) (qs_val D (fst y) (snd y))
        (Q2R d) (qs_val D (fst e) (snd e)).
Proof.
  intros D s x y d e HD. unfold asxs_cone_vals, asx_cone_vals.
  pose proof asx_Q2R_0 as Z.
  set (X := qs_val D (fst x) (snd x)). set (Y := qs_val D (fst y) (snd y)).
  set (E := qs_val D (fst e) (snd e)).
  destruct (Qlt_le_dec 0 s) as [Hs|Hs].
  - apply asx_Qlt_R in Hs. rewrite Z in Hs.
    rewrite Bool.andb_true_iff, !qs_nonneg_ok by exact HD. fold X Y.
    split; [intros [H1 H2]; left; repeat split; assumption|].
    intros [[_ [H1 H2]]|[[H _]|[[H _]|[H _]]]]; [split; assumption|lra|lra|lra].
  - apply asx_Qle_R in Hs. rewrite Z in Hs.
    destruct (Qlt_le_dec s 0) as [Hs'|Hs'].
    + apply asx_Qlt_R in Hs'. rewrite Z in Hs'.
      rewrite Bool.orb_true_iff, !qs_nonneg_ok by exact HD. fold X Y.
      split; [intros H; right; left; split; assumption|].
      intros [[H _]|[[_ H]|[[H _]|[H _]]]]; [lra|exact H|lra|lra].
    + apply asx_Qle_R in Hs'. rewrite Z in Hs'.
      assert (Es : Q2R s = 0) by lra.
      destruct (Qlt_le_dec d 0) as [Hd|Hd].
      * apply asx_Qlt_R in Hd. rewrite Z in Hd.
        rewrite qs_nonneg_ok by exact HD. fold X.
        split; [intro H; right; right; left; repeat split; assumption|].
        intros [[H _]|[[H _]|[[_ [_ H]]|[_ [H _]]]]]; [lra|lra|exact H|lra].
      * apply asx_Qle_R in Hd. rewrite Z in Hd.
        rewrite Bool.andb_true_iff, qs_zero_ok, qs_pos_ok by exact HD. fold X E.
        split; [intros [H1 H2]; right; right; right; repeat split; assumption|].
        intros [[H _]|[[H _]|[[_ [H _]]|[_ [_ [H1 H2]]]]]];
          [lra|lra|lra|split; assumption].
Qed.

Lemma asxs_cone_correct : forall D ax ay cx cy qx0 qx1 qy0 qy1, 0 <= Q2R D ->
  asxs_cone D ax ay cx cy qx0 qx1 qy0 qy1 = true
  <-> asx_cone (Q2R ax) (Q2R ay) (Q2R cx) (Q2R cy) (asxs_qR D qx0 qx1) (asxs_qR D qy0 qy1).
Proof.
  intros D ax ay cx cy qx0 qx1 qy0 qy1 HD. unfold asxs_cone, asx_cone.
  rewrite asxs_cone_vals_correct by exact HD.
  rewrite asxs_cross_uq_val, asxs_cross_qu_val, asxs_dot_uq_val, asx_Q2R_cross, asx_Q2R_dot.
  reflexivity.
Qed.

Lemma asxs_same_dir_correct : forall D ux uy qx0 qx1 qy0 qy1, 0 <= Q2R D ->
  asxs_same_dir D ux uy qx0 qx1 qy0 qy1 = true
  <-> asx_same_dir (Q2R ux) (Q2R uy) (asxs_qR D qx0 qx1) (asxs_qR D qy0 qy1).
Proof.
  intros D ux uy qx0 qx1 qy0 qy1 HD. unfold asxs_same_dir, asx_same_dir. cbv zeta.
  rewrite Bool.andb_true_iff, qs_zero_ok, qs_pos_ok by exact HD.
  rewrite asxs_cross_uq_val, asxs_dot_uq_val. reflexivity.
Qed.

(* WITNESS {"claimId":"t4b-sector-surd","topic":"curves","lemma":"asxs_sector_correct","title":"Exact arc-sector membership of an algebraic point U + sqrt D V (U, V in Q^2, D >= 0): the extractable asxs_sector is the R predicate asx_sector on that point (signs in Q(sqrt D), no atan2, no rounding)","file":"theories/ArcSectorSurd.v","witness":"asxs_sector_correct","board":"ADR-0006"} *)
Theorem asxs_sector_correct : forall D ox oy ax ay bx by_ cx cy ux uy vx vy,
  0 <= Q2R D ->
  asxs_sector D ox oy ax ay bx by_ cx cy ux uy vx vy = true
  <-> asx_sector (mkPoint (Q2R ox) (Q2R oy)) (mkPoint (Q2R ax) (Q2R ay))
        (mkPoint (Q2R bx) (Q2R by_)) (mkPoint (Q2R cx) (Q2R cy))
        (mkPoint (Q2R ux + Q2R vx * sqrt (Q2R D)) (Q2R uy + Q2R vy * sqrt (Q2R D))).
Proof.
  intros D ox oy ax ay bx by_ cx cy ux uy vx vy HD.
  unfold asxs_sector, asx_sector. cbv zeta. cbn [px py].
  assert (QX : Q2R ux + Q2R vx * sqrt (Q2R D) - Q2R ox = asxs_qR D (ux - ox) vx)
    by (unfold asxs_qR; rewrite Q2R_minus; ring).
  assert (QY : Q2R uy + Q2R vy * sqrt (Q2R D) - Q2R oy = asxs_qR D (uy - oy) vy)
    by (unfold asxs_qR; rewrite Q2R_minus; ring).
  rewrite QX, QY. rewrite <- !Q2R_minus.
  pose proof (asxq_same_dir_correct (ax - ox) (ay - oy) (cx - ox) (cy - oy)) as SAC.
  pose proof (asxq_same_dir_correct (ax - ox) (ay - oy) (bx - ox) (by_ - oy)) as SAB.
  pose proof (asxs_same_dir_correct D (ax - ox) (ay - oy) (ux - ox) vx (uy - oy) vy HD) as SAX.
  pose proof (asxq_cone_correct (ax - ox) (ay - oy) (cx - ox) (cy - oy)
                (bx - ox) (by_ - oy)) as CB.
  pose proof (asxs_cone_correct D (ax - ox) (ay - oy) (cx - ox) (cy - oy)
                (ux - ox) vx (uy - oy) vy HD) as CX.
  pose proof (asxs_cone_correct D (cx - ox) (cy - oy) (ax - ox) (ay - oy)
                (ux - ox) vx (uy - oy) vy HD) as CX'.
  pose proof (asx_bool_iff _ _ SAC) as SAC'.
  pose proof (asx_bool_iff _ _ SAB) as SAB'.
  pose proof (asx_bool_iff _ _ CB) as CB'.
  destruct (asxq_same_dir (ax - ox) (ay - oy) (cx - ox) (cy - oy));
  destruct (asxq_same_dir (ax - ox) (ay - oy) (bx - ox) (by_ - oy));
  destruct (asxq_cone (ax - ox) (ay - oy) (cx - ox) (cy - oy) (bx - ox) (by_ - oy));
  rewrite ?SAX, ?CX, ?CX';
  destruct SAC as [SAC1 SAC2]; destruct SAB as [SAB1 SAB2]; destruct CB as [CB1 CB2];
  destruct SAC' as [SAC3 SAC4]; destruct SAB' as [SAB3 SAB4];
  destruct CB' as [CB3 CB4];
  first
    [ specialize (SAC1 eq_refl) | specialize (SAC3 eq_refl) ];
  first
    [ specialize (SAB1 eq_refl) | specialize (SAB3 eq_refl) ];
  first
    [ specialize (CB1 eq_refl) | specialize (CB3 eq_refl) ];
  tauto.
Qed.

Print Assumptions qs_pos_ok.
Print Assumptions qs_zero_ok.
Print Assumptions qs_nonneg_ok.
Print Assumptions asxs_sector_correct.
