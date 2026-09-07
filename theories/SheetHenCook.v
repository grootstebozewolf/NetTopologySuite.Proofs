(* ============================================================================
   NetTopologySuite.Proofs.SheetHenCook
   ----------------------------------------------------------------------------
   ADR-0007 vocabulary: sheet, hen, egg, chicken, cook / 𝓘.

   Thin host-lane types for the ticket stops in Adr0007NodingEpic.v.
   Not a noder. Not a Geometry subclass. Not a remint of CurveSegment,
   Exact* zoo types, Dart, or Hobby / NodingSeparation_b64.

   First cook scope is chord–chord only. Predicates never mint hens.
   Empty ≠ Decline. Snap-rounding ≠ 𝓘. Display is a view.

   Testable 𝓘 / cook results sit on the accepted Oracle line protocol
   (ADR-0006). This module mints no keyword and no second external seam.

   WITNESS topic: overlay · claimId: 0007 · witness: 0007-qed-qex
   lane: proofs
   board: ADR-0007
   ADR-0004: not a leftover numeral and not a 508-* / 522-* board mint.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Segment.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Sheet S = (O; e1, e2) with optional lattice flag. Changing S is a          *)
(* different instance. Not a remint of theories/Lattice.v (Rmin/Rmax).        *)
(* -------------------------------------------------------------------------- *)

Record Sheet : Type := mkSheet {
  sheet_origin : Point;
  sheet_e1 : Point;
  sheet_e2 : Point;
  sheet_has_lattice : bool
}.

Definition default_sheet : Sheet :=
  mkSheet (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1) false.

(* Hens are identifiers. Identity is structural, not numeric. *)
Definition Hen : Type := nat.

(* Egg classes named in ADR-0007. Not CurveSegment constructors. *)
Inductive EggClass : Type :=
| EggChord
| EggCircularArc
| EggClothoid
| EggSinusoid
| EggEllipse
| EggBezier
| EggNurbs.

(* Chord interpolant γ(t) = (1-t)·P + t·Q. Out-of-scope classes are tags. *)
Record ChordEgg : Type := mkChordEgg {
  ce_p0 : Point;
  ce_p1 : Point
}.

Definition chord_eval (c : ChordEgg) (t : R) : Point :=
  mkPoint ((1 - t) * px (ce_p0 c) + t * px (ce_p1 c))
          ((1 - t) * py (ce_p0 c) + t * py (ce_p1 c)).

Inductive Egg : Type :=
| MkChord : ChordEgg -> Egg
| MkOutOfScope : EggClass -> Egg.

Definition egg_class (e : Egg) : EggClass :=
  match e with
  | MkChord _ => EggChord
  | MkOutOfScope c => c
  end.

(* Chicken: directed use of an egg between two hens. Twin reverses. *)
Record Chicken : Type := mkChicken {
  ck_src : Hen;
  ck_dst : Hen;
  ck_egg : Egg
}.

Definition chicken_twin (c : Chicken) : Chicken :=
  mkChicken (ck_dst c) (ck_src c) (ck_egg c).

Lemma chicken_twin_involutive :
  forall c, chicken_twin (chicken_twin c) = c.
Proof.
  intros [s d e]. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Pairwise oracle 𝓘. Empty ≠ Decline. First scope = chord–chord.            *)
(* -------------------------------------------------------------------------- *)

Inductive IResult : Type :=
| IHit (p : Point) (ti tj : R)
| IEmpty
| IDecline.

Definition first_cook_scope (a b : EggClass) : Prop :=
  match a, b with
  | EggChord, EggChord => True
  | _, _ => False
  end.

Definition on_chord (c : ChordEgg) (t : R) (p : Point) : Prop :=
  0 <= t <= 1 /\ p = chord_eval c t.

(* Minimal 𝓘 obligations: Hit lies on both chords; Empty is disjoint;
   Decline is only for pairs outside first cook scope. *)
Definition I_ok (e1 e2 : Egg) (o : IResult) : Prop :=
  match e1, e2, o with
  | MkChord c1, MkChord c2, IHit p ti tj =>
      on_chord c1 ti p /\ on_chord c2 tj p
  | MkChord c1, MkChord c2, IEmpty =>
      ~ exists X, between (ce_p0 c1) (ce_p1 c1) X /\
                  between (ce_p0 c2) (ce_p1 c2) X
  | MkChord _, MkChord _, IDecline => False
  | _, _, IDecline => ~ first_cook_scope (egg_class e1) (egg_class e2)
  | _, _, IHit _ _ _ => False
  | _, _, IEmpty => False
  end.

Record CookWitness : Type := mkCookWitness {
  cw_e1 : Egg;
  cw_e2 : Egg;
  cw_result : IResult;
  cw_ok : I_ok cw_e1 cw_e2 cw_result
}.

Lemma first_cook_scope_chord_chord :
  first_cook_scope EggChord EggChord.
Proof.
  exact I.
Qed.

Lemma clothoid_clothoid_not_first_scope :
  ~ first_cook_scope EggClothoid EggClothoid.
Proof.
  intro H. exact H.
Qed.

Lemma ellipse_ellipse_not_first_scope :
  ~ first_cook_scope EggEllipse EggEllipse.
Proof.
  intro H. exact H.
Qed.

Lemma IEmpty_neq_IDecline : IEmpty <> IDecline.
Proof.
  discriminate.
Qed.

Lemma IHit_neq_IEmpty :
  forall p ti tj, IHit p ti tj <> IEmpty.
Proof.
  intros. discriminate.
Qed.

Lemma IHit_neq_IDecline :
  forall p ti tj, IHit p ti tj <> IDecline.
Proof.
  intros. discriminate.
Qed.

Lemma I_ok_chord_not_decline :
  forall c1 c2 o,
    I_ok (MkChord c1) (MkChord c2) o -> o <> IDecline.
Proof.
  intros c1 c2 o H.
  destruct o; try discriminate.
  destruct H.
Qed.

(* Snap-rounding is a different constructor. Display is a view. *)
Inductive ConstructorKind : Type :=
| CtorI
| CtorSnapRound.

Lemma snap_round_neq_I : CtorSnapRound <> CtorI.
Proof.
  discriminate.
Qed.

Inductive DisplayView : Type :=
| ViewWKT
| ViewWKB
| ViewSFA.

(* -------------------------------------------------------------------------- *)
(* Chord–chord inhabitance. Crossing diagonals Hit; disjoint horizontals      *)
(* Empty; clothoid–clothoid Decline. Not a total noder.                       *)
(* -------------------------------------------------------------------------- *)

Definition diag_ab : ChordEgg := mkChordEgg (mkPoint 0 0) (mkPoint 2 2).
Definition diag_cd : ChordEgg := mkChordEgg (mkPoint 0 2) (mkPoint 2 0).
Definition cross_pt : Point := mkPoint 1 1.

Definition hor_bot : ChordEgg := mkChordEgg (mkPoint 0 0) (mkPoint 1 0).
Definition hor_top : ChordEgg := mkChordEgg (mkPoint 0 1) (mkPoint 1 1).

Lemma crossing_midpoint_ab :
  between (mkPoint 0 0) (mkPoint 2 2) (mkPoint 1 1).
Proof.
  exists (1 / 2).
  repeat split; try lra; simpl; field.
Qed.

Lemma crossing_midpoint_cd :
  between (mkPoint 0 2) (mkPoint 2 0) (mkPoint 1 1).
Proof.
  exists (1 / 2).
  repeat split; try lra; simpl; field.
Qed.

Lemma crossing_on_diag_ab :
  on_chord diag_ab (1 / 2) cross_pt.
Proof.
  unfold on_chord, diag_ab, cross_pt, chord_eval.
  split; [lra|].
  apply (f_equal2 mkPoint); simpl; field.
Qed.

Lemma crossing_on_diag_cd :
  on_chord diag_cd (1 / 2) cross_pt.
Proof.
  unfold on_chord, diag_cd, cross_pt, chord_eval.
  split; [lra|].
  apply (f_equal2 mkPoint); simpl; field.
Qed.

Lemma crossing_I_ok :
  I_ok (MkChord diag_ab) (MkChord diag_cd)
       (IHit cross_pt (1 / 2) (1 / 2)).
Proof.
  unfold I_ok.
  split; [exact crossing_on_diag_ab | exact crossing_on_diag_cd].
Qed.

Definition crossing_witness : CookWitness :=
  mkCookWitness (MkChord diag_ab) (MkChord diag_cd)
    (IHit cross_pt (1 / 2) (1 / 2)) crossing_I_ok.

Lemma disjoint_horizontals :
  ~ exists X,
      between (mkPoint 0 0) (mkPoint 1 0) X /\
      between (mkPoint 0 1) (mkPoint 1 1) X.
Proof.
  intros [X [[t1 [_ [_ [_ Hy1]]]] [t2 [_ [_ [_ Hy2]]]]]].
  simpl in Hy1, Hy2.
  lra.
Qed.

Lemma disjoint_I_ok :
  I_ok (MkChord hor_bot) (MkChord hor_top) IEmpty.
Proof.
  unfold I_ok, hor_bot, hor_top.
  exact disjoint_horizontals.
Qed.

Definition disjoint_witness : CookWitness :=
  mkCookWitness (MkChord hor_bot) (MkChord hor_top) IEmpty disjoint_I_ok.

Lemma clothoid_decline_I_ok :
  I_ok (MkOutOfScope EggClothoid) (MkOutOfScope EggClothoid) IDecline.
Proof.
  unfold I_ok, first_cook_scope, egg_class.
  intro H. exact H.
Qed.

Definition clothoid_decline_witness : CookWitness :=
  mkCookWitness (MkOutOfScope EggClothoid) (MkOutOfScope EggClothoid)
    IDecline clothoid_decline_I_ok.

(* -------------------------------------------------------------------------- *)
(* Identity: cook decision is structural. Coord-pair dart_eq_dec is not hen   *)
(* identity. Local CoordDart mirrors theories/Dart.v:50 — not a remint.       *)
(* -------------------------------------------------------------------------- *)

Definition CoordDart : Type := (Point * Point)%type.

Inductive CookIdDecision : Type :=
| ShareOne (h : Hen)
| MintTwo (h1 h2 : Hen).

Definition apply_id_decision (d : CookIdDecision) : Hen * Hen :=
  match d with
  | ShareOne h => (h, h)
  | MintTwo a b => (a, b)
  end.

Lemma share_one_same_hen :
  forall h : Hen,
    fst (apply_id_decision (ShareOne h)) = snd (apply_id_decision (ShareOne h)).
Proof.
  intros h. reflexivity.
Qed.

Lemma mint_two_may_differ :
  exists a b : Hen, fst (apply_id_decision (MintTwo a b)) <>
                    snd (apply_id_decision (MintTwo a b)).
Proof.
  exists 0%nat, 1%nat.
  discriminate.
Qed.

Lemma points_10_neq_20 :
  mkPoint 1 0 <> mkPoint 2 0.
Proof.
  intro H.
  apply (f_equal px) in H.
  simpl in H.
  lra.
Qed.

Lemma coord_eq_not_hen_eq :
  ~ (forall (h1 h2 : Hen) (d1 d2 : CoordDart),
       h1 = h2 <-> d1 = d2).
Proof.
  intro H.
  pose proof (H 0%nat 0%nat
    (mkPoint 0 0, mkPoint 1 0)
    (mkPoint 0 0, mkPoint 2 0)) as [Hf _].
  assert (Heq : 0%nat = 0%nat) by reflexivity.
  apply Hf in Heq.
  apply (f_equal snd) in Heq.
  simpl in Heq.
  exact (points_10_neq_20 Heq).
Qed.

(* -------------------------------------------------------------------------- *)
(* Noded on S is cook evidence. Silent pairwise_nodable shadow excludes the   *)
(* proper-crossing case a noder exists for — not a Hobby rewrite.             *)
(* -------------------------------------------------------------------------- *)

Record NodedOnSheet : Type := mkNoded {
  noded_sheet : Sheet;
  noded_cook : CookWitness
}.

Definition noded_crossing : NodedOnSheet :=
  mkNoded default_sheet crossing_witness.

Lemma noded_on_sheet_carries_I_ok :
  forall n : NodedOnSheet,
    I_ok (cw_e1 (noded_cook n)) (cw_e2 (noded_cook n))
         (cw_result (noded_cook n)).
Proof.
  intros n. exact (cw_ok (noded_cook n)).
Qed.

Definition share_endpoint (A B C D : Point) : Prop :=
  A = C \/ A = D \/ B = C \/ B = D.

(* Shadow of NodingSeparation_b64.pairwise_nodable: share an endpoint or
   the images are disjoint. Proper crossings are excluded. *)
Definition pairwise_nodable_shadow (A B C D : Point) : Prop :=
  share_endpoint A B C D
  \/ ~ exists X, between A B X /\ between C D X.

Lemma crossing_no_shared_endpoint :
  ~ share_endpoint (mkPoint 0 0) (mkPoint 2 2) (mkPoint 0 2) (mkPoint 2 0).
Proof.
  intros [H | [H | [H | H]]].
  - apply (f_equal py) in H; simpl in H; lra.
  - apply (f_equal px) in H; simpl in H; lra.
  - apply (f_equal px) in H; simpl in H; lra.
  - apply (f_equal py) in H; simpl in H; lra.
Qed.

Lemma crossing_not_nodable_shadow :
  ~ pairwise_nodable_shadow
      (mkPoint 0 0) (mkPoint 2 2) (mkPoint 0 2) (mkPoint 2 0).
Proof.
  intros [Hshare | Hdisj].
  - exact (crossing_no_shared_endpoint Hshare).
  - apply Hdisj.
    exists (mkPoint 1 1).
    split; [exact crossing_midpoint_ab | exact crossing_midpoint_cd].
Qed.

Print Assumptions first_cook_scope_chord_chord.
Print Assumptions clothoid_clothoid_not_first_scope.
Print Assumptions IEmpty_neq_IDecline.
Print Assumptions crossing_witness.
Print Assumptions disjoint_witness.
Print Assumptions share_one_same_hen.
Print Assumptions coord_eq_not_hen_eq.
Print Assumptions noded_crossing.
Print Assumptions crossing_not_nodable_shadow.
Print Assumptions snap_round_neq_I.
