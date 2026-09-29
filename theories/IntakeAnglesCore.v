(* ============================================================================
   NetTopologySuite.Proofs.IntakeAnglesCore
   ----------------------------------------------------------------------------
   Definitions for claimId 0007-intake-angles. The letter theorems
   stay in IntakeAngles.v. WKT compute is egg_of_points: circumcenter,
   pole chart, principal theta0, chart sweep. ISO CIRCLE
   (try_circle_eggs) reuses that theta0 (angle of A). The full-turn
   egg stays circle_of_egg (sweep ±2*PI). The bag is two half-span
   eggs (sweep ±PI) and ends [A; antipode], not a src=dst chicken.

   3-axiom host. No Admitted / Axiom / Parameter.
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Field List.
From NTS.Proofs Require Import Distance Segment SheetHenCook CircleChart Atan2 AtanIvt
  CurveGeometry ArcChordApprox.
Import ListNotations.
Local Open Scope R_scope.
Local Open Scope list_scope.

(* -------------------------------------------------------------------------- *)
(* Fail-closed construction result. Mapped to IntakeDecline in the walker.    *)
(* -------------------------------------------------------------------------- *)

Inductive AngleFail : Type :=
| AF_Empty
| AF_BadCount
| AF_Duplicate
| AF_Collinear
| AF_Degenerate
| AF_SpanMismatch
| AF_CsClosedDegenerate.

Definition AngleResult (A : Type) : Type := (A + AngleFail)%type.

(* -------------------------------------------------------------------------- *)
(* Unique circumcircle of a control triple. Same formula as CurveGeometry.    *)
(* -------------------------------------------------------------------------- *)

Definition circ_denom (a b c : Point) : R :=
  2 * (px a * (py b - py c) + px b * (py c - py a) + px c * (py a - py b)).

Definition circumcenter_of (a b c : Point) : Point :=
  let ax := px a in let ay := py a in
  let bx := px b in let by_ := py b in
  let cx := px c in let cy := py c in
  let d := circ_denom a b c in
  let na := ax * ax + ay * ay in
  let nb := bx * bx + by_ * by_ in
  let nc := cx * cx + cy * cy in
  let ux := (na * (by_ - cy) + nb * (cy - ay) + nc * (ay - by_)) / d in
  let uy := (na * (cx - bx) + nb * (ax - cx) + nc * (bx - ax)) / d in
  mkPoint ux uy.

(* One wrap lands in (-π, π] on (-2π, 2π). atan2's cut is +π, so -π maps to π. *)
Definition principal (a : R) : R :=
  if Rle_dec a (- PI) then a + 2 * PI
  else if Rlt_dec PI a then a - 2 * PI
  else a.

(* WKT compute: pole opposite the mid control, then atan2 of the pole frame
   plus the half-angle chart. Δθ is the chart sweep, not ±2π. *)
Definition egg_of_points (a m b : Point) : CircularEgg :=
  let o := circumcenter_of a m b in
  let r := dist o a in
  let q := pole_point o m (midpoint a b) in
  let ux := px o - px q in
  let uy := py o - py q in
  let za := zeta_of_pt o q a in
  let zb := zeta_of_pt o q b in
  mkCircularEgg o r
    (principal (atan2 uy ux + 2 * atan3 za))
    (2 * (atan3 zb - atan3 za)).

(* Req_dec is Prop (`or`) in Rocq 9.2 and cannot inhabit AngleResult.
   Req_EM_T is the Type-level sumbool; 3-axiom classical reals. *)
Definition try_triple (a b c : Point) : AngleResult CircularEgg :=
  if Req_EM_T (dist_sq a b) 0 then inr AF_Duplicate
  else if Req_EM_T (dist_sq b c) 0 then inr AF_Duplicate
  else if Req_EM_T (dist_sq a c) 0 then inr AF_Duplicate
  else
    let d := circ_denom a b c in
    if Req_EM_T d 0 then inr AF_Collinear
    else
      let o := circumcenter_of a b c in
      let r := dist o a in
      if Req_EM_T r 0 then inr AF_Degenerate
      else inl (egg_of_points a b c).

(* Recurse on the matched tail `rest2` (the list starting at the
   junction). Rebuilding `c :: rest` is not a decreasing argument. *)
Fixpoint go_arcs (pts : list Point) {struct pts}
  : AngleResult (list CircularEgg * list Point) :=
  match pts with
  | [] => inr AF_BadCount
  | a :: rest1 =>
      match rest1 with
      | [] => inr AF_BadCount
      | b :: rest2 =>
          match rest2 with
          | [] => inr AF_BadCount
          | c :: rest =>
              match try_triple a b c with
              | inr f => inr f
              | inl e =>
                  match rest with
                  | [] => inl ([e], [a; c])
                  | _ :: _ =>
                      match go_arcs rest2 with
                      | inr f => inr f
                      | inl (es, ends) => inl (e :: es, a :: ends)
                      end
                  end
              end
          end
      end
  end.

(* CIRCULARSTRING(A,B,A) is the GEOS/PostGIS full-circle spelling.
   ISO does not say that. First = last on a 3-control string Declines
   before the duplicate check. A longer closed string is not this case. *)
Definition try_cs_eggs (pts : list Point)
  : AngleResult (list CircularEgg * list Point) :=
  match pts with
  | [] => inr AF_Empty
  | a :: b :: c :: [] =>
      if Req_EM_T (dist_sq a c) 0 then inr AF_CsClosedDegenerate
      else go_arcs pts
  | _ :: _ => go_arcs pts
  end.

(* θ₀ is the chart angle of A (same egg_of_points as try_triple).
   circle_of_egg is the full turn, sweep ±2π. The bag does not store
   that egg: two hens at distinct points, A and γ(1/2), and two
   MkCirc of sweep ±π (θ₀, then θ₀±π). piece_wf / bag_step do not
   state that a chicken with ck_src = ck_dst is well-formed, so the
   bag is not a self-loop. *)
Definition full_sweep (a b c : Point) : R :=
  if Rle_dec 0 (orient_pts a b c) then 2 * PI else - (2 * PI).

Definition half_sweep (a b c : Point) : R :=
  if Rle_dec 0 (orient_pts a b c) then PI else - PI.

Definition circle_of_egg (e : CircularEgg) (a b c : Point) : CircularEgg :=
  mkCircularEgg (circ_o e) (circ_r e) (circ_theta0 e) (full_sweep a b c).

Definition circle_half_fst (e : CircularEgg) (a b c : Point) : CircularEgg :=
  mkCircularEgg (circ_o e) (circ_r e) (circ_theta0 e) (half_sweep a b c).

Definition circle_half_snd (e : CircularEgg) (a b c : Point) : CircularEgg :=
  mkCircularEgg (circ_o e) (circ_r e)
    (circ_theta0 e + half_sweep a b c) (half_sweep a b c).

Definition circle_antipode (e : CircularEgg) (a b c : Point) : Point :=
  circ_eval (circle_of_egg e a b c) (1 / 2).

Definition try_circle_eggs (pts : list Point)
  : AngleResult (list CircularEgg * list Point) :=
  match pts with
  | [] => inr AF_Empty
  | [a; b; c] =>
      match try_triple a b c with
      | inr f => inr f
      | inl e =>
          inl ([circle_half_fst e a b c; circle_half_snd e a b c],
               [a; circle_antipode e a b c])
      end
  | _ => inr AF_BadCount
  end.

(* Cycle 0→1, 1→0. circ_chickens would mint a third hen. *)
Definition circle_cycle (e1 e2 : CircularEgg) : list Chicken :=
  [mkChicken 0%nat 1%nat (MkCirc e1); mkChicken 1%nat 0%nat (MkCirc e2)].

Fixpoint circ_chickens (es : list CircularEgg) (h0 : nat) : list Chicken :=
  match es with
  | [] => []
  | e :: rest =>
      mkChicken h0 (S h0) (MkCirc e) :: circ_chickens rest (S h0)
  end.

(* -------------------------------------------------------------------------- *)
(* Fixture: prior unknown_cs_cst points (0,0), (2,0), (3,1).                  *)
(* -------------------------------------------------------------------------- *)

Definition ang_a : Point := mkPoint 0 0.
Definition ang_b : Point := mkPoint 2 0.
Definition ang_c : Point := mkPoint 3 1.

Definition ang_egg : CircularEgg := egg_of_points ang_a ang_b ang_c.

Lemma sqrt_pos_neq_0 : forall x, 0 < x -> sqrt x <> 0.
Proof.
  intros x Hx Hz.
  pose proof (sqrt_lt_R0 x Hx) as Hp.
  lra.
Qed.

Lemma ang_denom : circ_denom ang_a ang_b ang_c = 4.
Proof.
  unfold circ_denom, ang_a, ang_b, ang_c. cbn. ring.
Qed.

Lemma ang_center : circumcenter_of ang_a ang_b ang_c = mkPoint 1 2.
Proof.
  unfold circumcenter_of. rewrite ang_denom.
  unfold ang_a, ang_b, ang_c. cbn.
  apply (f_equal2 mkPoint); field; lra.
Qed.

Lemma ang_dab_nz : dist_sq ang_a ang_b <> 0.
Proof.
  unfold dist_sq, ang_a, ang_b. cbn. lra.
Qed.

Lemma ang_dbc_nz : dist_sq ang_b ang_c <> 0.
Proof.
  unfold dist_sq, ang_b, ang_c. cbn. lra.
Qed.

Lemma ang_dac_nz : dist_sq ang_a ang_c <> 0.
Proof.
  unfold dist_sq, ang_a, ang_c. cbn. lra.
Qed.

Lemma ang_r_nz : dist (circumcenter_of ang_a ang_b ang_c) ang_a <> 0.
Proof.
  rewrite ang_center. unfold dist, dist_sq, ang_a. cbn.
  apply sqrt_pos_neq_0. lra.
Qed.

Lemma ang_r_sqrt5 :
  dist (circumcenter_of ang_a ang_b ang_c) ang_a = sqrt 5.
Proof.
  rewrite ang_center. unfold dist, dist_sq, ang_a. cbn.
  f_equal. ring.
Qed.

Lemma ang_triple_egg : try_triple ang_a ang_b ang_c = inl ang_egg.
Proof.
  unfold try_triple.
  destruct (Req_EM_T (dist_sq ang_a ang_b) 0) as [Hab|Hab];
    [exfalso; exact (ang_dab_nz Hab)|].
  destruct (Req_EM_T (dist_sq ang_b ang_c) 0) as [Hbc|Hbc];
    [exfalso; exact (ang_dbc_nz Hbc)|].
  destruct (Req_EM_T (dist_sq ang_a ang_c) 0) as [Hac|Hac];
    [exfalso; exact (ang_dac_nz Hac)|].
  destruct (Req_EM_T (circ_denom ang_a ang_b ang_c) 0) as [Hd|Hd];
    [exfalso; rewrite ang_denom in Hd; lra|].
  destruct (Req_EM_T (dist (circumcenter_of ang_a ang_b ang_c) ang_a) 0)
    as [Hr|Hr];
    [exfalso; exact (ang_r_nz Hr)|].
  unfold ang_egg. reflexivity.
Qed.

Lemma ang_cs_ok :
  try_cs_eggs [ang_a; ang_b; ang_c] = inl ([ang_egg], [ang_a; ang_c]).
Proof.
  unfold try_cs_eggs.
  destruct (Req_EM_T (dist_sq ang_a ang_c) 0) as [Hac|Hac].
  - exfalso. exact (ang_dac_nz Hac).
  - unfold go_arcs. rewrite ang_triple_egg. reflexivity.
Qed.

Lemma ang_egg_center : circ_o ang_egg = mkPoint 1 2.
Proof.
  unfold ang_egg, egg_of_points. exact ang_center.
Qed.

Lemma ang_egg_radius : circ_r ang_egg = sqrt 5.
Proof.
  unfold ang_egg, egg_of_points. exact ang_r_sqrt5.
Qed.

Lemma try_triple_ok : forall a b c,
  dist_sq a b <> 0 ->
  dist_sq b c <> 0 ->
  dist_sq a c <> 0 ->
  circ_denom a b c <> 0 ->
  dist (circumcenter_of a b c) a <> 0 ->
  try_triple a b c = inl (egg_of_points a b c).
Proof.
  intros a b c Hab Hbc Hac Hd Hr.
  unfold try_triple.
  destruct (Req_EM_T (dist_sq a b) 0) as [E|E]; [contradiction|].
  destruct (Req_EM_T (dist_sq b c) 0) as [E2|E2]; [contradiction|].
  destruct (Req_EM_T (dist_sq a c) 0) as [E3|E3]; [contradiction|].
  destruct (Req_EM_T (circ_denom a b c) 0) as [E4|E4]; [contradiction|].
  destruct (Req_EM_T (dist (circumcenter_of a b c) a) 0) as [E5|E5];
    [contradiction|].
  reflexivity.
Qed.

Lemma try_circle_halves : forall a b c,
  dist_sq a b <> 0 ->
  dist_sq b c <> 0 ->
  dist_sq a c <> 0 ->
  circ_denom a b c <> 0 ->
  dist (circumcenter_of a b c) a <> 0 ->
  try_circle_eggs [a; b; c] =
    inl ([circle_half_fst (egg_of_points a b c) a b c;
          circle_half_snd (egg_of_points a b c) a b c],
         [a; circle_antipode (egg_of_points a b c) a b c]).
Proof.
  intros a b c Hab Hbc Hac Hd Hr.
  unfold try_circle_eggs.
  rewrite (try_triple_ok a b c Hab Hbc Hac Hd Hr).
  reflexivity.
Qed.

Lemma ang_circle_ok :
  try_circle_eggs [ang_a; ang_b; ang_c] =
    inl ([circle_half_fst ang_egg ang_a ang_b ang_c;
          circle_half_snd ang_egg ang_a ang_b ang_c],
         [ang_a; circle_antipode ang_egg ang_a ang_b ang_c]).
Proof.
  assert (Hd : circ_denom ang_a ang_b ang_c <> 0).
  { rewrite ang_denom. lra. }
  unfold ang_egg.
  rewrite (try_circle_halves ang_a ang_b ang_c
            ang_dab_nz ang_dbc_nz ang_dac_nz Hd ang_r_nz).
  reflexivity.
Qed.

Lemma try_cs_closed_degenerate :
  forall a b, try_cs_eggs [a; b; a] = inr AF_CsClosedDegenerate.
Proof.
  intros a b. unfold try_cs_eggs.
  destruct (Req_EM_T (dist_sq a a) 0) as [_|H].
  - reflexivity.
  - exfalso. apply H. unfold dist_sq. cbn. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Fail-closed named reasons.                                                 *)
(* -------------------------------------------------------------------------- *)

Lemma try_cs_empty : try_cs_eggs [] = inr AF_Empty.
Proof.
  reflexivity.
Qed.

Lemma try_cs_singleton :
  try_cs_eggs [ang_a] = inr AF_BadCount.
Proof.
  reflexivity.
Qed.

Lemma try_cs_pair :
  try_cs_eggs [ang_a; ang_b] = inr AF_BadCount.
Proof.
  reflexivity.
Qed.

Lemma try_cs_even_four :
  try_cs_eggs [ang_a; ang_b; ang_c; ang_a] = inr AF_BadCount.
Proof.
  unfold try_cs_eggs, go_arcs.
  rewrite ang_triple_egg.
  reflexivity.
Qed.

Lemma try_triple_dup_ab :
  forall a b c, dist_sq a b = 0 -> try_triple a b c = inr AF_Duplicate.
Proof.
  intros a b c H.
  unfold try_triple.
  destruct (Req_EM_T (dist_sq a b) 0) as [H'|H']; [reflexivity|].
  exfalso. apply H'. exact H.
Qed.

Lemma try_triple_collinear :
  forall a b c,
    dist_sq a b <> 0 ->
    dist_sq b c <> 0 ->
    dist_sq a c <> 0 ->
    circ_denom a b c = 0 ->
    try_triple a b c = inr AF_Collinear.
Proof.
  intros a b c Hab Hbc Hac Hd.
  unfold try_triple.
  destruct (Req_EM_T (dist_sq a b) 0) as [H1|H1]; [exfalso; apply Hab; exact H1|].
  destruct (Req_EM_T (dist_sq b c) 0) as [H2|H2]; [exfalso; apply Hbc; exact H2|].
  destruct (Req_EM_T (dist_sq a c) 0) as [H3|H3]; [exfalso; apply Hac; exact H3|].
  destruct (Req_EM_T (circ_denom a b c) 0) as [H4|H4]; [reflexivity|].
  exfalso. apply H4. exact Hd.
Qed.

Definition col_a : Point := mkPoint 0 0.
Definition col_b : Point := mkPoint 1 0.
Definition col_c : Point := mkPoint 2 0.

Lemma col_denom : circ_denom col_a col_b col_c = 0.
Proof.
  unfold circ_denom, col_a, col_b, col_c. cbn. ring.
Qed.

Lemma col_dab_nz : dist_sq col_a col_b <> 0.
Proof.
  unfold dist_sq, col_a, col_b. cbn. lra.
Qed.

Lemma col_dbc_nz : dist_sq col_b col_c <> 0.
Proof.
  unfold dist_sq, col_b, col_c. cbn. lra.
Qed.

Lemma col_dac_nz : dist_sq col_a col_c <> 0.
Proof.
  unfold dist_sq, col_a, col_c. cbn. lra.
Qed.

Lemma col_triple_collinear :
  try_triple col_a col_b col_c = inr AF_Collinear.
Proof.
  apply try_triple_collinear.
  - exact col_dab_nz.
  - exact col_dbc_nz.
  - exact col_dac_nz.
  - exact col_denom.
Qed.

Lemma col_cs_collinear :
  try_cs_eggs [col_a; col_b; col_c] = inr AF_Collinear.
Proof.
  unfold try_cs_eggs.
  destruct (Req_EM_T (dist_sq col_a col_c) 0) as [Hac|Hac].
  - exfalso. exact (col_dac_nz Hac).
  - unfold go_arcs. rewrite col_triple_collinear. reflexivity.
Qed.

Definition dup_a : Point := mkPoint 0 0.
Definition dup_b : Point := mkPoint 0 0.
Definition dup_c : Point := mkPoint 1 1.

Lemma dup_ab : dist_sq dup_a dup_b = 0.
Proof.
  unfold dist_sq, dup_a, dup_b. cbn. ring.
Qed.

Lemma dup_triple :
  try_triple dup_a dup_b dup_c = inr AF_Duplicate.
Proof.
  apply try_triple_dup_ab. exact dup_ab.
Qed.

Lemma dup_ac_nz : dist_sq dup_a dup_c <> 0.
Proof.
  unfold dist_sq, dup_a, dup_c. cbn. lra.
Qed.

Lemma dup_cs :
  try_cs_eggs [dup_a; dup_b; dup_c] = inr AF_Duplicate.
Proof.
  unfold try_cs_eggs.
  destruct (Req_EM_T (dist_sq dup_a dup_c) 0) as [Hac|Hac].
  - exfalso. exact (dup_ac_nz Hac).
  - unfold go_arcs. rewrite dup_triple. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Chickens are MkCirc. Never a silent MkChord.                               *)
(* -------------------------------------------------------------------------- *)

Lemma circ_chickens_mkcirc :
  forall es h0 c,
    In c (circ_chickens es h0) ->
    exists e, ck_egg c = MkCirc e.
Proof.
  intros es. induction es as [|e rest IH]; intros h0 c Hin.
  - simpl in Hin. contradiction.
  - simpl in Hin. destruct Hin as [Hhd|Htl].
    + subst c. exists e. reflexivity.
    + apply (IH (S h0) c Htl).
Qed.

Lemma circ_chickens_not_chord :
  forall es h0 c,
    In c (circ_chickens es h0) ->
    egg_class (ck_egg c) <> EggChord.
Proof.
  intros es h0 c Hin.
  destruct (circ_chickens_mkcirc es h0 c Hin) as [e He].
  rewrite He. discriminate.
Qed.

Lemma ang_chickens_mkcirc :
  circ_chickens [ang_egg] 0%nat =
    [mkChicken 0%nat 1%nat (MkCirc ang_egg)].
Proof.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Chart arithmetic. θ₀ is the principal value of atan2(u) + 2·atan3(ζA).    *)
(* Δθ = 2·(atan3 ζB − atan3 ζA) on the pole-opposite-M chart.                 *)
(* -------------------------------------------------------------------------- *)

Lemma cos_two_pi : cos (2 * PI) = 1.
Proof.
  replace (2 * PI) with (PI + PI) by ring.
  rewrite cos_plus, cos_PI, sin_PI. ring.
Qed.

Lemma sin_two_pi : sin (2 * PI) = 0.
Proof.
  replace (2 * PI) with (PI + PI) by ring.
  rewrite sin_plus, cos_PI, sin_PI. ring.
Qed.

Lemma cos_shift_2pi : forall a, cos (a + 2 * PI) = cos a.
Proof.
  intro a. rewrite cos_plus, cos_two_pi, sin_two_pi. ring.
Qed.

Lemma sin_shift_2pi : forall a, sin (a + 2 * PI) = sin a.
Proof.
  intro a. rewrite sin_plus, cos_two_pi, sin_two_pi. ring.
Qed.

Lemma cos_shift_m2pi : forall a, cos (a - 2 * PI) = cos a.
Proof.
  intro a.
  replace (a - 2 * PI) with (a + - (2 * PI)) by ring.
  rewrite cos_plus, cos_neg, sin_neg, cos_two_pi, sin_two_pi. ring.
Qed.

Lemma sin_shift_m2pi : forall a, sin (a - 2 * PI) = sin a.
Proof.
  intro a.
  replace (a - 2 * PI) with (a + - (2 * PI)) by ring.
  rewrite sin_plus, cos_neg, sin_neg, cos_two_pi, sin_two_pi. ring.
Qed.

Lemma principal_range : forall a,
  - (2 * PI) < a < 2 * PI ->
  - PI < principal a <= PI.
Proof.
  intros a Ha. unfold principal.
  destruct (Rle_dec a (- PI)) as [Hle|Hgt].
  - pose proof PI_RGT_0. split; lra.
  - destruct (Rlt_dec PI a) as [Hlt|Hge].
    + pose proof PI_RGT_0. split; lra.
    + pose proof PI_RGT_0. split; lra.
Qed.

Lemma principal_cos : forall a,
  - (2 * PI) < a < 2 * PI ->
  cos (principal a) = cos a.
Proof.
  intros a Ha. unfold principal.
  destruct (Rle_dec a (- PI)) as [Hle|Hgt].
  - apply cos_shift_2pi.
  - destruct (Rlt_dec PI a) as [Hlt|Hge].
    + apply cos_shift_m2pi.
    + reflexivity.
Qed.

Lemma principal_sin : forall a,
  - (2 * PI) < a < 2 * PI ->
  sin (principal a) = sin a.
Proof.
  intros a Ha. unfold principal.
  destruct (Rle_dec a (- PI)) as [Hle|Hgt].
  - apply sin_shift_2pi.
  - destruct (Rlt_dec PI a) as [Hlt|Hge].
    + apply sin_shift_m2pi.
    + reflexivity.
Qed.

Lemma atan3_strict : forall x y, x < y -> atan3 x < atan3 y.
Proof.
  intros x y Hab.
  destruct (Rle_lt_or_eq_dec _ _ (atan3_le x y (Rlt_le _ _ Hab))) as [H|H].
  - exact H.
  - exfalso.
    destruct (atan3_spec x) as [Bx Sx]. destruct (atan3_spec y) as [By Sy].
    assert (Hc : 0 < cos (atan3 x)) by (apply cos_gt_0; lra).
    rewrite H in Sx, Hc.
    assert (x * cos (atan3 y) = y * cos (atan3 y)) by lra.
    assert (x = y).
    { apply (Rmult_eq_reg_r (cos (atan3 y))); [exact H0 | lra]. }
    lra.
Qed.

Lemma atan3_inj : forall x y, atan3 x = atan3 y -> x = y.
Proof.
  intros x y E.
  destruct (Rtotal_order x y) as [Hlt|[Heq|Hgt]].
  - exfalso. pose proof (atan3_strict x y Hlt). lra.
  - exact Heq.
  - exfalso. pose proof (atan3_strict y x Hgt). lra.
Qed.

Lemma angle_eq_of_trig : forall a b,
  cos a = cos b ->
  sin a = sin b ->
  - (2 * PI) < a - b < 2 * PI ->
  a = b.
Proof.
  intros a b Hc Hs Hb.
  assert (Hcd : cos (a - b) = 1).
  { rewrite cos_minus, Hc, Hs.
    pose proof (sin2_cos2 b) as E. unfold Rsqr in E. nra. }
  assert (He : a - b = 0).
  { apply cos_eq_1_two_pi; assumption. }
  lra.
Qed.

Lemma circ_denom_orient : forall a m b,
  circ_denom a m b = 2 * orient_pts a m b.
Proof.
  intros a m b. unfold circ_denom, orient_pts, orient3, crs. cbn. ring.
Qed.

Lemma orient_swap_end_mid : forall a m b,
  orient_pts a b m = - orient_pts a m b.
Proof.
  intros. unfold orient_pts, orient3, crs. ring.
Qed.

Lemma dist_sq_neq_ne : forall p q, dist_sq p q <> 0 -> p <> q.
Proof.
  intros p q H E. apply H. subst q. unfold dist_sq. ring.
Qed.

Lemma dist_pos_of_neq : forall p q, dist p q <> 0 -> 0 < dist p q.
Proof.
  intros p q H.
  unfold dist in *.
  destruct (Req_dec (dist_sq p q) 0) as [E|N].
  - exfalso. apply H. rewrite E. apply sqrt_0.
  - apply sqrt_lt_R0.
    pose proof (Rle_0_sqr (px p - px q)) as Hx.
    pose proof (Rle_0_sqr (py p - py q)) as Hy.
    unfold dist_sq, Rsqr in *. lra.
Qed.

Lemma points_of_valid_denom : forall a m b,
  circ_denom a m b <> 0 ->
  valid_arc (mkCircularArc a m b).
Proof.
  intros a m b Hd.
  unfold valid_arc. cbn.
  intros Hc. apply Hd.
  rewrite circ_denom_orient.
  unfold orient_pts, orient3, crs. cbn.
  nra.
Qed.

Lemma circum_is_arc_center : forall a m b,
  circumcenter_of a m b = arc_center (mkCircularArc a m b).
Proof.
  intros a m b. unfold circumcenter_of, arc_center, circ_denom. cbn. reflexivity.
Qed.

Lemma circum_equidistant : forall a m b,
  circ_denom a m b <> 0 ->
  dist_sq (circumcenter_of a m b) m = dist_sq (circumcenter_of a m b) a /\
  dist_sq (circumcenter_of a m b) b = dist_sq (circumcenter_of a m b) a.
Proof.
  intros a m b Hd.
  set (arc := mkCircularArc a m b).
  assert (Hv : valid_arc arc) by (apply points_of_valid_denom; exact Hd).
  destruct (arc_center_equidistant arc Hv) as [Hm He].
  assert (E : circumcenter_of a m b = arc_center arc).
  { unfold arc. apply circum_is_arc_center. }
  rewrite <- E in Hm, He.
  unfold arc in Hm, He.
  cbn [arc_start arc_mid arc_end] in Hm, He.
  split; symmetry; assumption.
Qed.

Lemma center_unique : forall a m b U,
  circ_denom a m b <> 0 ->
  dist_sq U a = dist_sq U m ->
  dist_sq U a = dist_sq U b ->
  U = circumcenter_of a m b.
Proof.
  intros a m b U Hd H1 H2.
  set (arc := mkCircularArc a m b).
  assert (HU : U = arc_center arc).
  { unfold arc. unfold dist_sq in H1, H2. unfold arc_center.
    cbn [arc_start arc_mid arc_end px py].
    set (ax := px a) in *. set (ay := py a) in *.
    set (bx := px m) in *. set (by_ := py m) in *.
    set (cx := px b) in *. set (cy := py b) in *.
    set (ux := px U) in *. set (uy := py U) in *.
    set (na := ax * ax + ay * ay).
    set (nb := bx * bx + by_ * by_).
    set (nc := cx * cx + cy * cy).
    set (dd := 2 * (ax * (by_ - cy) + bx * (cy - ay) + cx * (ay - by_))) in *.
    assert (Hdd : dd <> 0) by (unfold dd, circ_denom in *; exact Hd).
    assert (L1 : 2 * (bx - ax) * ux + 2 * (by_ - ay) * uy = nb - na)
      by (unfold na, nb; nra).
    assert (L2 : 2 * (cx - ax) * ux + 2 * (cy - ay) * uy = nc - na)
      by (unfold na, nc; nra).
    assert (K1x : (2 * (bx - ax) * ux + 2 * (by_ - ay) * uy) * (cy - ay)
                  = (nb - na) * (cy - ay)) by (rewrite L1; reflexivity).
    assert (K2x : (2 * (cx - ax) * ux + 2 * (cy - ay) * uy) * (by_ - ay)
                  = (nc - na) * (by_ - ay)) by (rewrite L2; reflexivity).
    assert (K1y : (2 * (bx - ax) * ux + 2 * (by_ - ay) * uy) * (cx - ax)
                  = (nb - na) * (cx - ax)) by (rewrite L1; reflexivity).
    assert (K2y : (2 * (cx - ax) * ux + 2 * (cy - ay) * uy) * (bx - ax)
                  = (nc - na) * (bx - ax)) by (rewrite L2; reflexivity).
    apply Point_eq_of_coords; simpl.
    - fold ux. field_simplify_eq; [| exact Hdd].
      unfold dd, na, nb, nc in *. nra.
    - fold uy. field_simplify_eq; [| exact Hdd].
      unfold dd, na, nb, nc in *. nra. }
  rewrite HU. unfold arc. apply circum_is_arc_center.
Qed.

(* Axiom audit. Headlines are the classical-reals trio. *)
Print Assumptions sqrt_pos_neq_0.
Print Assumptions ang_denom.
Print Assumptions ang_center.
Print Assumptions ang_dab_nz.
Print Assumptions ang_dbc_nz.
Print Assumptions ang_dac_nz.
Print Assumptions ang_r_nz.
Print Assumptions ang_r_sqrt5.
Print Assumptions ang_triple_egg.
Print Assumptions ang_cs_ok.
Print Assumptions ang_egg_center.
Print Assumptions ang_egg_radius.
Print Assumptions try_triple_ok.
Print Assumptions try_circle_halves.
Print Assumptions ang_circle_ok.
Print Assumptions try_cs_closed_degenerate.
Print Assumptions try_cs_empty.
Print Assumptions try_cs_singleton.
Print Assumptions try_cs_pair.
Print Assumptions try_cs_even_four.
Print Assumptions try_triple_dup_ab.
Print Assumptions try_triple_collinear.
Print Assumptions col_denom.
Print Assumptions col_dab_nz.
Print Assumptions col_dbc_nz.
Print Assumptions col_dac_nz.
Print Assumptions col_triple_collinear.
Print Assumptions col_cs_collinear.
Print Assumptions dup_ab.
Print Assumptions dup_triple.
Print Assumptions dup_ac_nz.
Print Assumptions dup_cs.
Print Assumptions circ_chickens_mkcirc.
Print Assumptions circ_chickens_not_chord.
Print Assumptions ang_chickens_mkcirc.
Print Assumptions cos_two_pi.
Print Assumptions sin_two_pi.
Print Assumptions cos_shift_2pi.
Print Assumptions sin_shift_2pi.
Print Assumptions cos_shift_m2pi.
Print Assumptions sin_shift_m2pi.
Print Assumptions principal_range.
Print Assumptions principal_cos.
Print Assumptions principal_sin.
Print Assumptions atan3_strict.
Print Assumptions atan3_inj.
Print Assumptions angle_eq_of_trig.
Print Assumptions circ_denom_orient.
Print Assumptions orient_swap_end_mid.
Print Assumptions dist_sq_neq_ne.
Print Assumptions dist_pos_of_neq.
Print Assumptions points_of_valid_denom.
Print Assumptions circum_is_arc_center.
Print Assumptions circum_equidistant.
Print Assumptions center_unique.
