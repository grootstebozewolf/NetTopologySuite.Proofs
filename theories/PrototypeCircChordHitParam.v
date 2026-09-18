(* ============================================================================
   PROTOTYPE — throwaway. Not host cook. Not a remint of I_ok / try_cook_hit.
   ----------------------------------------------------------------------------
   Wayfinder ticket: Arc parameter on a host Hit without atan2
   Map: Wayfinder: 𝒤 factory — circ×chord first cook
   Branch: prototype/circ-chord-hit-param

   Question this file answers by being something to react to:
     How does a host Hit I_ok (MkCirc c) (MkChord s) (IHit p ti tj)
     carry the arc parameter ti in the 3-axiom lane, and what must
     try_cook_hit *compute*?

   Three candidate statement shapes live below. Only Candidate C is
   inhabited on a locked fixture (the one that matches circ×circ).
   Candidates A and B are written as types you can reject, not land.

   Does not touch SheetHenCook.v (module-split ceiling).
   Does not expand first_cook_scope (letter after Accept).
   3-axiom on the inhabited lemmas. No Admitted / Axiom / Parameter.
   ========================================================================== *)

From Stdlib Require Import Reals Lra Rtrigo_facts.
From NTS.Proofs Require Import Distance SheetHenCook.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Locked fixture: quarter-circle × its diameter-ish chord, one interior Hit. *)
(*   Circ  A: O=(0,0) r=5 θ0=0 Δθ=π/2     γ: (5,0) → (0,5)                  *)
(*   Chord S: (5,5) → (0,0)                 line x = y                       *)
(*   Hit   P: (5√2/2, 5√2/2)               angle π/4 on A                    *)
(*   ti = 1/2  (sweep fraction, egg data — not atan2 of P)                    *)
(*   tj = 1 - √2/2                       (chord lerp)                        *)
(* -------------------------------------------------------------------------- *)

Definition proto_circ : CircularEgg :=
  mkCircularEgg (mkPoint 0 0) 5 0 (PI / 2).

Definition proto_chord : ChordEgg :=
  mkChordEgg (mkPoint 5 5) (mkPoint 0 0).

Definition proto_hit : Point :=
  mkPoint (5 * sqrt 2 / 2) (5 * sqrt 2 / 2).

Definition proto_ti : R := 1 / 2.
Definition proto_tj : R := 1 - sqrt 2 / 2.

Lemma proto_ti_in_01 : 0 <= proto_ti <= 1.
Proof. unfold proto_ti. lra. Qed.

Lemma proto_tj_in_01 : 0 <= proto_tj <= 1.
Proof.
  unfold proto_tj.
  pose proof sqrt2_neq_0.
  pose proof Rlt_sqrt2_0.
  split; lra.
Qed.

Lemma proto_circ_at_ti :
  circ_eval proto_circ proto_ti = proto_hit.
Proof.
  unfold circ_eval, proto_circ, proto_ti, proto_hit.
  cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  replace (0 + (1 / 2) * (PI / 2)) with (PI / 4) by (pose proof PI_RGT_0; field; lra).
  rewrite cos_PI4, sin_PI4.
  apply (f_equal2 mkPoint); field.
Qed.

Lemma proto_chord_at_tj :
  chord_eval proto_chord proto_tj = proto_hit.
Proof.
  unfold chord_eval, proto_chord, proto_tj, proto_hit.
  cbn [px py ce_p0 ce_p1].
  apply (f_equal2 mkPoint); field.
Qed.

Lemma proto_on_circ : on_circ proto_circ proto_ti proto_hit.
Proof.
  unfold on_circ. split; [exact proto_ti_in_01|].
  symmetry. exact proto_circ_at_ti.
Qed.

Lemma proto_on_chord : on_chord proto_chord proto_tj proto_hit.
Proof.
  unfold on_chord. split; [exact proto_tj_in_01|].
  symmetry. exact proto_chord_at_tj.
Qed.

(* ========================================================================== *)
(* Candidate A — existential / IVT-style                                      *)
(*                                                                            *)
(* IHit stops carrying ti. Membership is "there exists a parameter".          *)
(* Matches ArcSegmentCircles.arc_line_circle_intersect (a point on the        *)
(* circumcircle ∧ on the line), which does not produce a sweep fraction.      *)
(*                                                                            *)
(* Cost: IResult changes (letter); try_cook_hit must *invent* ti to split;    *)
(* inventing ti from P is either atan2 (B) or a fresh inverse of circ_eval.   *)
(* Rejected unless IResult itself is redrawn.                                 *)
(* ========================================================================== *)

Definition A_hit_exists (c : CircularEgg) (s : ChordEgg) (p : Point) : Prop :=
  (exists ti, on_circ c ti p) /\ (exists tj, on_chord s tj p).

Lemma A_inhabits_locked : A_hit_exists proto_circ proto_chord proto_hit.
Proof.
  split.
  - exists proto_ti. exact proto_on_circ.
  - exists proto_tj. exact proto_on_chord.
Qed.

(* ========================================================================== *)
(* Candidate B — constructed angle (Category C, forbidden on host)            *)
(*                                                                            *)
(* ti := (∠(P − O) − θ0) / Δθ. That is atan2 on a vector.                    *)
(* Host lane 3-axiom forbids Stdlib atan2 / classic Ratan. CircGamma sidecar  *)
(* already owns this retract. Do not remint it as host I_ok.                  *)
(*                                                                            *)
(* The definition is written so you can see the shape, then not use it.       *)
(* It is not computed. Print Assumptions on any user of it would go C.        *)
(* ========================================================================== *)

(* Intentionally not defined:
     Parameter atan2_host : R -> R -> R.
     Definition B_ti_from_point (c : CircularEgg) (p : Point) : R :=
       (atan2_host (py p - py (circ_o c)) (px p - px (circ_o c))
        - circ_theta0 c) / circ_sweep c.
   Rejected: Category C on host. *)

(* ========================================================================== *)
(* Candidate C — carry the egg parameter; cook does not compute it            *)
(*                                                                            *)
(* Same shape as today's circ×circ and chord×chord:
     IHit carries (p, ti, tj)
     I_ok *checks* on_circ c ti p ∧ on_chord s tj p
     try_cook_hit *consumes* ti, tj via circ_split / chord_split
     Nobody inverts γ.                                                        *)
(*                                                                            *)
(* Who constructs ti?
     - Host proofs: the fixture author, as CircularCookMkCirc does (2/3, 1/3).
     - Oracle / Z classifier: not this lane. I_line_arc decides Hit/Touch/
       Empty by sign tests and does not have to emit a host-grade ti.
       ARC_SEGMENT_XY already emits coordinates; hunters diff those.          *)
(* ========================================================================== *)

Definition C_I_ok_circ_chord (c : CircularEgg) (s : ChordEgg) (o : IResult) : Prop :=
  match o with
  | IHit p ti tj => on_circ c ti p /\ on_chord s tj p
  | IEmpty => ~ exists X t1 t2, on_circ c t1 X /\ on_chord s t2 X
  | IDecline => False
  end.

Definition C_locked_hit : IResult := IHit proto_hit proto_ti proto_tj.

Lemma C_locked_I_ok :
  C_I_ok_circ_chord proto_circ proto_chord C_locked_hit.
Proof.
  unfold C_I_ok_circ_chord, C_locked_hit.
  split; [exact proto_on_circ | exact proto_on_chord].
Qed.

(* Today host I_ok refuses the mixed Hit. That is the status quo this
   prototype is proposing to change — later, by letter, not here. *)
Lemma C_host_I_ok_still_false :
  ~ I_ok (MkCirc proto_circ) (MkChord proto_chord) C_locked_hit.
Proof.
  unfold I_ok, C_locked_hit. intro H. exact H.
Qed.

Definition C_cook_circ_chord
  (ckc cks : Chicken) (c : CircularEgg) (s : ChordEgg) (ti tj : R) (h : Hen)
  : CookedPair :=
  let sc := circ_split c ti in
  let ss := chord_split s tj in
  mkCookedPair h
    (mkChicken (ck_src ckc) h (MkCirc (fst sc)))
    (mkChicken h (ck_dst ckc) (MkCirc (snd sc)))
    (mkChicken (ck_src cks) h (MkChord (fst ss)))
    (mkChicken h (ck_dst cks) (MkChord (snd ss))).

(* Proposed try_cook_hit arm (not installed):
     | MkCirc c, MkChord s, IHit _ ti tj =>
         Some (C_cook_circ_chord c1 c2 c s ti tj h_new)
     | MkChord s, MkCirc c, IHit _ ti tj =>
         Some (C_cook_circ_chord c2 c1 c s tj ti h_new)
   The cook does not compute ti. It splits at the carried parameters. *)

Definition proto_ck_circ : Chicken :=
  mkChicken 0%nat 1%nat (MkCirc proto_circ).
Definition proto_ck_chord : Chicken :=
  mkChicken 2%nat 3%nat (MkChord proto_chord).
Definition proto_hen : Hen := 4%nat.

Definition C_cooked : CookedPair :=
  C_cook_circ_chord proto_ck_circ proto_ck_chord
    proto_circ proto_chord proto_ti proto_tj proto_hen.

Lemma C_cooked_shares : cooked_shares_hen C_cooked.
Proof. repeat split; reflexivity. Qed.

Lemma C_split_joins_at_hit :
  circ_eval (fst (circ_split proto_circ proto_ti)) 1 = proto_hit /\
  circ_eval (snd (circ_split proto_circ proto_ti)) 0 = proto_hit /\
  chord_eval (fst (chord_split proto_chord proto_tj)) 1 = proto_hit /\
  chord_eval (snd (chord_split proto_chord proto_tj)) 0 = proto_hit.
Proof.
  rewrite (proj1 (circ_split_join proto_circ proto_ti)).
  rewrite (proj2 (circ_split_join proto_circ proto_ti)).
  rewrite proto_circ_at_ti.
  rewrite (proj1 (chord_split_join proto_chord proto_tj)).
  rewrite (proj2 (chord_split_join proto_chord proto_tj)).
  rewrite proto_chord_at_tj.
  repeat split; reflexivity.
Qed.

(* Status quo: mixed Hit does not mint. *)
Lemma C_host_try_cook_none :
  try_cook_hit proto_ck_circ proto_ck_chord C_locked_hit proto_hen = None.
Proof. reflexivity. Qed.

(* ========================================================================== *)
(* What this prototype is *not* deciding                                      *)
(*   first_cook_scope EggCircularArc EggChord  — letter after Accept          *)
(*   Touch arm / MintTwo                       — letter after Accept          *)
(*   Span source when intake Δθ = ±2π         — Span source ticket            *)
(*   I_CIRC_CHORD keyword                      — ADR-0006 amendment           *)
(*   Bridging sidecar I_ok_interior            — Parks fence                  *)
(* ========================================================================== *)

Print Assumptions proto_on_circ.
Print Assumptions proto_on_chord.
Print Assumptions C_locked_I_ok.
Print Assumptions C_cooked_shares.
Print Assumptions C_split_joins_at_hit.
Print Assumptions C_host_I_ok_still_false.
Print Assumptions C_host_try_cook_none.
