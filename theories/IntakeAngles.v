(* ============================================================================
   NetTopologySuite.Proofs.IntakeAngles
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: intake angles-from-points
   (claimId 0007-intake-angles). Needle AFTER first-slice walker
   (#725 / claimId 0007-intake-walker). Not a CircGamma remint.

   Host constructs CircularEgg (O, r, θ₀, Δθ) from well-formed WKT
   circular control points. Three non-collinear distinct points
   determine a unique circumcircle (algebraic O, r). Angle fields
   are inhabited from that geometry without importing Stdlib atan
   / Atan2.v (Ratan proofs are Category C / classic; that would
   contaminate first-slice Print Assumptions on the shared
   intake_map). θ₀ is the sheet e₁ ray (0). Δθ is the oriented
   full span ±2π (sign = sign of the three-point area). Host γ
   stays the atan2-free interpolant on CircularEgg data
   (CircularCookMkCirc.v). Sidecar Parks Γ is not reminted.

   Fail closed: empty / bad count / duplicate control / collinear
   / zero-radius. No silent chord demote. Demote is later
   cook/view. IntakeMkClothoid stays QEX (parks stop).

   Mapper consumers live in IntakeWalker.v. This module is the
   thin construction sibling.

   WITNESS topic: core · claimId: 0007-intake-angles
   witness: 0007-intake-angles
   board: ADR-0007
   3-axiom host. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance SheetHenCook.
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
| AF_Degenerate.

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

Definition sweep_from_denom (d : R) : R :=
  if Rlt_dec 0 d then 2 * PI else - (2 * PI).

Definition try_triple (a b c : Point) : AngleResult CircularEgg :=
  if Req_dec (dist_sq a b) 0 then inr AF_Duplicate
  else if Req_dec (dist_sq b c) 0 then inr AF_Duplicate
  else if Req_dec (dist_sq a c) 0 then inr AF_Duplicate
  else
    let d := circ_denom a b c in
    if Req_dec d 0 then inr AF_Collinear
    else
      let o := circumcenter_of a b c in
      let r := dist o a in
      if Req_dec r 0 then inr AF_Degenerate
      else inl (mkCircularEgg o r 0 (sweep_from_denom d)).

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

Definition try_cs_eggs (pts : list Point)
  : AngleResult (list CircularEgg * list Point) :=
  match pts with
  | [] => inr AF_Empty
  | _ :: _ => go_arcs pts
  end.

Definition try_circle_eggs (pts : list Point)
  : AngleResult (list CircularEgg * list Point) :=
  match pts with
  | [] => inr AF_Empty
  | [a; b; c] =>
      match try_triple a b c with
      | inr f => inr f
      | inl e =>
          inl ([mkCircularEgg (circ_o e) (circ_r e) (circ_theta0 e) (2 * PI)],
               [a; c])
      end
  | _ => inr AF_BadCount
  end.

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

Definition ang_egg : CircularEgg :=
  mkCircularEgg (mkPoint 1 2) (sqrt 5) 0 (2 * PI).

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
  destruct (Req_dec (dist_sq ang_a ang_b) 0) as [Hab|Hab];
    [exfalso; exact (ang_dab_nz Hab)|].
  destruct (Req_dec (dist_sq ang_b ang_c) 0) as [Hbc|Hbc];
    [exfalso; exact (ang_dbc_nz Hbc)|].
  destruct (Req_dec (dist_sq ang_a ang_c) 0) as [Hac|Hac];
    [exfalso; exact (ang_dac_nz Hac)|].
  destruct (Req_dec (circ_denom ang_a ang_b ang_c) 0) as [Hd|Hd];
    [exfalso; rewrite ang_denom in Hd; lra|].
  destruct (Req_dec (dist (circumcenter_of ang_a ang_b ang_c) ang_a) 0)
    as [Hr|Hr];
    [exfalso; exact (ang_r_nz Hr)|].
  unfold sweep_from_denom, ang_egg.
  rewrite ang_r_sqrt5.
  destruct (Rlt_dec 0 (circ_denom ang_a ang_b ang_c)) as [Hs|Hs].
  - reflexivity.
  - exfalso. rewrite ang_denom in Hs. lra.
Qed.

Lemma ang_cs_ok :
  try_cs_eggs [ang_a; ang_b; ang_c] = inl ([ang_egg], [ang_a; ang_c]).
Proof.
  unfold try_cs_eggs, go_arcs.
  rewrite ang_triple_egg.
  reflexivity.
Qed.

Lemma ang_circle_ok :
  try_circle_eggs [ang_a; ang_b; ang_c] = inl ([ang_egg], [ang_a; ang_c]).
Proof.
  unfold try_circle_eggs.
  rewrite ang_triple_egg.
  reflexivity.
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
  destruct (Req_dec (dist_sq a b) 0) as [H'|H']; [reflexivity|].
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
  destruct (Req_dec (dist_sq a b) 0) as [H1|H1]; [exfalso; apply Hab; exact H1|].
  destruct (Req_dec (dist_sq b c) 0) as [H2|H2]; [exfalso; apply Hbc; exact H2|].
  destruct (Req_dec (dist_sq a c) 0) as [H3|H3]; [exfalso; apply Hac; exact H3|].
  destruct (Req_dec (circ_denom a b c) 0) as [H4|H4]; [reflexivity|].
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
  unfold try_cs_eggs, go_arcs.
  rewrite col_triple_collinear.
  reflexivity.
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

Lemma dup_cs :
  try_cs_eggs [dup_a; dup_b; dup_c] = inr AF_Duplicate.
Proof.
  unfold try_cs_eggs, go_arcs.
  rewrite dup_triple.
  reflexivity.
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

Lemma intake_angles_ctor_shape :
  exists e, try_triple ang_a ang_b ang_c = inl e /\
            circ_o e = mkPoint 1 2 /\
            circ_r e = sqrt 5 /\
            circ_theta0 e = 0 /\
            circ_sweep e = 2 * PI.
Proof.
  exists ang_egg.
  split; [exact ang_triple_egg|].
  unfold ang_egg. repeat split; reflexivity.
Qed.

Print Assumptions ang_triple_egg.
Print Assumptions ang_cs_ok.
Print Assumptions col_cs_collinear.
Print Assumptions dup_cs.
Print Assumptions circ_chickens_mkcirc.
Print Assumptions circ_chickens_not_chord.
Print Assumptions intake_angles_ctor_shape.
