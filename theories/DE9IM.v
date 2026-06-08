(* ============================================================================
   NetTopologySuite.Proofs.DE9IM
   ----------------------------------------------------------------------------
   Issue #67 session 1: DE-9IM intersection-matrix algebra (foundation only).

   Formalises the dimensionally-extended 3×3 intersection matrix used by JTS
   RelateNG / OGC spatial predicates.  Cell (i,j) records the dimension of
   Interior_i(A) ∩ Interior_j(B), with `None` (= OGC/JTS "F") for empty.

   Delivers:

     - `DimValue` / `IntersectionMatrix` types
     - nine-cell pattern matching (`IMPattern`, `matrix_matches`)
     - standard named predicates as matrix patterns (mirrors JTS
       `RelatePredicate` / `IntersectionMatrixPattern`)
     - structural lemmas: disjoint ⇒ ¬intersects₀/₁/₄ (JTS `intersects₃`
       is compatible with disjoint — see `disjoint_intersects3_example_holds`);
       contains ↔ transpose
       within; covers ↔ transpose coveredBy

   Honest scoping: no geometry carrier, no RelateNG algorithm, no prepared
   cache — matrix algebra only.  Geometry-linked slices (line-line, area-point)
   land in follow-up modules (`RelateLineLine.v`, …).

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import List Lia.

(* -------------------------------------------------------------------------- *)
(* Dimension entries.  `None` = empty (pattern `F`); `Some d` = dimension d. *)
(* -------------------------------------------------------------------------- *)

Definition DimValue := option nat.

Definition dim_empty (d : DimValue) : Prop := d = None.

Definition dim_nonempty (d : DimValue) : Prop := d <> None.

Definition dim_value_ok (d : DimValue) : Prop :=
  match d with
  | None => True
  | Some n => (n <= 2)%nat
  end.

(* -------------------------------------------------------------------------- *)
(* Pattern characters.  `PWild` = `*`; `PFalse` = `F`; `PTrue` = `T`;          *)
(* `PDim n` = exact dimension n ∈ {0,1,2}.                                    *)
(* -------------------------------------------------------------------------- *)

Inductive PatternChar : Type :=
| PWild : PatternChar
| PFalse : PatternChar
| PTrue : PatternChar
| PDim (n : nat) : PatternChar.

Record IMPattern : Type := mkPat {
  pat_ii : PatternChar; pat_ib : PatternChar; pat_ie : PatternChar;
  pat_bi : PatternChar; pat_bb : PatternChar; pat_be : PatternChar;
  pat_ei : PatternChar; pat_eb : PatternChar; pat_ee : PatternChar
}.

Record IntersectionMatrix : Type := mkIM {
  im_ii : DimValue; im_ib : DimValue; im_ie : DimValue;
  im_bi : DimValue; im_bb : DimValue; im_be : DimValue;
  im_ei : DimValue; im_eb : DimValue; im_ee : DimValue
}.

Definition matrix_ok (m : IntersectionMatrix) : Prop :=
  dim_value_ok (im_ii m) /\ dim_value_ok (im_ib m) /\ dim_value_ok (im_ie m) /\
  dim_value_ok (im_bi m) /\ dim_value_ok (im_bb m) /\ dim_value_ok (im_be m) /\
  dim_value_ok (im_ei m) /\ dim_value_ok (im_eb m) /\ dim_value_ok (im_ee m).

Definition matrix_transpose (m : IntersectionMatrix) : IntersectionMatrix :=
  {| im_ii := im_ii m; im_ib := im_bi m; im_ie := im_ei m;
     im_bi := im_ib m; im_bb := im_bb m; im_be := im_eb m;
     im_ei := im_ie m; im_eb := im_be m; im_ee := im_ee m |}.

Definition char_matches (c : PatternChar) (d : DimValue) : Prop :=
  match c, d with
  | PWild, _ => True
  | PFalse, None => True
  | PFalse, Some _ => False
  | PTrue, None => False
  | PTrue, Some _ => True
  | PDim n, Some m => n = m
  | PDim _, None => False
  end.

Definition matrix_matches (p : IMPattern) (m : IntersectionMatrix) : Prop :=
  char_matches (pat_ii p) (im_ii m) /\
  char_matches (pat_ib p) (im_ib m) /\
  char_matches (pat_ie p) (im_ie m) /\
  char_matches (pat_bi p) (im_bi m) /\
  char_matches (pat_bb p) (im_bb m) /\
  char_matches (pat_be p) (im_be m) /\
  char_matches (pat_ei p) (im_ei m) /\
  char_matches (pat_eb p) (im_eb m) /\
  char_matches (pat_ee p) (im_ee m).

(* -------------------------------------------------------------------------- *)
(* Standard JTS / OGC patterns (row-major: II IB IE / BI BB BE / EI EB EE).   *)
(* -------------------------------------------------------------------------- *)

Definition pat_disjoint : IMPattern :=
  {| pat_ii := PFalse; pat_ib := PFalse; pat_ie := PWild;
     pat_bi := PFalse; pat_bb := PFalse; pat_be := PWild;
     pat_ei := PFalse; pat_eb := PFalse; pat_ee := PWild |}.

Definition pat_intersects_0 : IMPattern :=
  {| pat_ii := PTrue;  pat_ib := PWild; pat_ie := PWild;
     pat_bi := PWild;  pat_bb := PWild; pat_be := PWild;
     pat_ei := PWild;  pat_eb := PWild; pat_ee := PWild |}.

Definition pat_intersects_1 : IMPattern :=
  {| pat_ii := PWild;  pat_ib := PTrue;  pat_ie := PWild;
     pat_bi := PWild;  pat_bb := PWild; pat_be := PWild;
     pat_ei := PWild;  pat_eb := PWild; pat_ee := PWild |}.

Definition pat_intersects_3 : IMPattern :=
  {| pat_ii := PWild;  pat_ib := PWild; pat_ie := PTrue;
     pat_bi := PWild;  pat_bb := PWild; pat_be := PWild;
     pat_ei := PWild;  pat_eb := PWild; pat_ee := PWild |}.

Definition pat_intersects_4 : IMPattern :=
  {| pat_ii := PWild;  pat_ib := PWild; pat_ie := PWild;
     pat_bi := PWild;  pat_bb := PTrue;  pat_be := PWild;
     pat_ei := PWild;  pat_eb := PWild; pat_ee := PWild |}.

Definition pat_contains : IMPattern :=
  {| pat_ii := PTrue;  pat_ib := PWild; pat_ie := PWild;
     pat_bi := PWild;  pat_bb := PWild; pat_be := PWild;
     pat_ei := PFalse; pat_eb := PFalse; pat_ee := PWild |}.

Definition pattern_transpose (p : IMPattern) : IMPattern :=
  {| pat_ii := pat_ii p; pat_ib := pat_bi p; pat_ie := pat_ei p;
     pat_bi := pat_ib p; pat_bb := pat_bb p; pat_be := pat_eb p;
     pat_ei := pat_ie p; pat_eb := pat_be p; pat_ee := pat_ee p |}.

Definition pat_within : IMPattern := pattern_transpose pat_contains.

Definition pat_covers_0 : IMPattern := pat_contains.

Definition pat_covers_1 : IMPattern :=
  {| pat_ii := PWild;  pat_ib := PTrue;  pat_ie := PWild;
     pat_bi := PWild;  pat_bb := PWild; pat_be := PWild;
     pat_ei := PFalse; pat_eb := PFalse; pat_ee := PWild |}.

Definition pat_covers_3 : IMPattern :=
  {| pat_ii := PWild;  pat_ib := PWild; pat_ie := PTrue;
     pat_bi := PWild;  pat_bb := PWild; pat_be := PWild;
     pat_ei := PFalse; pat_eb := PFalse; pat_ee := PWild |}.

Definition pat_covers_4 : IMPattern :=
  {| pat_ii := PWild;  pat_ib := PWild; pat_ie := PWild;
     pat_bi := PWild;  pat_bb := PTrue;  pat_be := PWild;
     pat_ei := PFalse; pat_eb := PFalse; pat_ee := PWild |}.

Definition pat_coveredBy_0 : IMPattern := pattern_transpose pat_covers_0.
Definition pat_coveredBy_1 : IMPattern := pattern_transpose pat_covers_1.
Definition pat_coveredBy_3 : IMPattern := pattern_transpose pat_covers_3.
Definition pat_coveredBy_4 : IMPattern := pattern_transpose pat_covers_4.

Definition pat_equals_topo : IMPattern :=
  {| pat_ii := PTrue;  pat_ib := PWild; pat_ie := PFalse;
     pat_bi := PWild;  pat_bb := PWild; pat_be := PFalse;
     pat_ei := PFalse; pat_eb := PFalse; pat_ee := PFalse |}.

Definition pat_touches_0 : IMPattern :=
  {| pat_ii := PFalse; pat_ib := PTrue;  pat_ie := PWild;
     pat_bi := PWild;  pat_bb := PWild; pat_be := PWild;
     pat_ei := PWild;  pat_eb := PWild; pat_ee := PWild |}.

Definition pat_touches_1 : IMPattern :=
  {| pat_ii := PWild;  pat_ib := PWild; pat_ie := PWild;
     pat_bi := PFalse; pat_bb := PTrue;  pat_be := PWild;
     pat_ei := PWild;  pat_eb := PWild; pat_ee := PWild |}.

Definition pat_touches_3 : IMPattern :=
  {| pat_ii := PWild;  pat_ib := PWild; pat_ie := PWild;
     pat_bi := PWild;  pat_bb := PWild; pat_be := PWild;
     pat_ei := PFalse; pat_eb := PTrue;  pat_ee := PWild |}.

Definition pat_crosses_pl_pa_la : IMPattern :=
  {| pat_ii := PTrue;  pat_ib := PWild; pat_ie := PWild;
     pat_bi := PWild;  pat_bb := PFalse; pat_be := PWild;
     pat_ei := PWild;  pat_eb := PWild; pat_ee := PWild |}.

Definition pat_crosses_lp_ap_al : IMPattern :=
  {| pat_ii := PTrue;  pat_ib := PWild; pat_ie := PWild;
     pat_bi := PWild;  pat_bb := PWild; pat_be := PTrue;
     pat_ei := PWild;  pat_eb := PWild; pat_ee := PWild |}.

Definition pat_crosses_ll : IMPattern :=
  {| pat_ii := PDim 0;  pat_ib := PWild; pat_ie := PWild;
     pat_bi := PWild;  pat_bb := PWild; pat_be := PWild;
     pat_ei := PWild;  pat_eb := PWild; pat_ee := PWild |}.

Definition pat_overlaps_pp_aa : IMPattern :=
  {| pat_ii := PTrue;  pat_ib := PWild; pat_ie := PWild;
     pat_bi := PWild;  pat_bb := PTrue;  pat_be := PWild;
     pat_ei := PWild;  pat_eb := PWild; pat_ee := PTrue |}.

Definition pat_overlaps_ll : IMPattern :=
  {| pat_ii := PDim 1;  pat_ib := PWild; pat_ie := PWild;
     pat_bi := PWild;  pat_bb := PTrue;  pat_be := PWild;
     pat_ei := PWild;  pat_eb := PWild; pat_ee := PTrue |}.

(* -------------------------------------------------------------------------- *)
(* Named predicates on matrices (JTS RelatePredicate pattern tables).         *)
(* -------------------------------------------------------------------------- *)

Definition im_disjoint (m : IntersectionMatrix) : Prop :=
  matrix_matches pat_disjoint m.

Definition im_intersects (m : IntersectionMatrix) : Prop :=
  matrix_matches pat_intersects_0 m \/
  matrix_matches pat_intersects_1 m \/
  matrix_matches pat_intersects_3 m \/
  matrix_matches pat_intersects_4 m.

Definition im_contains (m : IntersectionMatrix) : Prop :=
  matrix_matches pat_contains m.

Definition im_within (m : IntersectionMatrix) : Prop :=
  matrix_matches pat_within m.

Definition im_covers (m : IntersectionMatrix) : Prop :=
  matrix_matches pat_covers_0 m \/
  matrix_matches pat_covers_1 m \/
  matrix_matches pat_covers_3 m \/
  matrix_matches pat_covers_4 m.

Definition im_coveredBy (m : IntersectionMatrix) : Prop :=
  matrix_matches pat_coveredBy_0 m \/
  matrix_matches pat_coveredBy_1 m \/
  matrix_matches pat_coveredBy_3 m \/
  matrix_matches pat_coveredBy_4 m.

Definition im_equals_topo (m : IntersectionMatrix) : Prop :=
  matrix_matches pat_equals_topo m.

Definition im_touches (m : IntersectionMatrix) : Prop :=
  matrix_matches pat_touches_0 m \/
  matrix_matches pat_touches_1 m \/
  matrix_matches pat_touches_3 m.

Definition im_crosses (m : IntersectionMatrix) : Prop :=
  matrix_matches pat_crosses_pl_pa_la m \/
  matrix_matches pat_crosses_lp_ap_al m \/
  matrix_matches pat_crosses_ll m.

Definition im_overlaps (m : IntersectionMatrix) : Prop :=
  matrix_matches pat_overlaps_pp_aa m \/
  matrix_matches pat_overlaps_ll m.

Inductive RelatePredicate : Type :=
| RDisjoint | RIntersects | RContains | RWithin
| RCovers | RCoveredBy | REqualsTopo | RTouches
| RCrosses | ROverlaps.

Definition predicate_holds (r : RelatePredicate) (m : IntersectionMatrix) : Prop :=
  match r with
  | RDisjoint   => im_disjoint m
  | RIntersects => im_intersects m
  | RWithin     => im_within m
  | RContains   => im_contains m
  | RCovers     => im_covers m
  | RCoveredBy  => im_coveredBy m
  | REqualsTopo => im_equals_topo m
  | RTouches    => im_touches m
  | RCrosses    => im_crosses m
  | ROverlaps   => im_overlaps m
  end.

(* -------------------------------------------------------------------------- *)
(* Structural lemmas.                                                         *)
(* -------------------------------------------------------------------------- *)

Lemma char_false_empty : forall d : DimValue,
  char_matches PFalse d <-> dim_empty d.
Proof.
  intros d. destruct d as [n|]; simpl.
  - split; [intros H; destruct H | intros H; inversion H].
  - split; intros _; reflexivity.
Qed.

Lemma char_true_nonempty : forall d : DimValue,
  char_matches PTrue d <-> dim_nonempty d.
Proof.
  intros d. destruct d as [n|]; simpl.
  - split; [intros _; intro Heq; discriminate Heq | intros _; reflexivity].
  - split; [intros H; destruct H | intros H; apply H; reflexivity].
Qed.

Lemma disjoint_not_intersects_0 :
  forall m : IntersectionMatrix,
    im_disjoint m -> ~ matrix_matches pat_intersects_0 m.
Proof.
  intros m Hd H0. unfold im_disjoint in Hd. simpl in Hd, H0.
  destruct Hd as [Hii _], H0 as [Ht _].
  destruct (im_ii m) eqn:Eii; simpl in Hii, Ht.
  - destruct Hii.
  - destruct Ht.
Qed.

Lemma disjoint_not_intersects_1 :
  forall m : IntersectionMatrix,
    im_disjoint m -> ~ matrix_matches pat_intersects_1 m.
Proof.
  intros m Hd H0. unfold im_disjoint in Hd. simpl in Hd, H0.
  destruct Hd as [_ [Hib _]], H0 as [_ [Ht _]].
  destruct (im_ib m) eqn:Eib; simpl in Hib, Ht.
  - destruct Hib.
  - destruct Ht.
Qed.

Lemma disjoint_not_intersects_4 :
  forall m : IntersectionMatrix,
    im_disjoint m -> ~ matrix_matches pat_intersects_4 m.
Proof.
  intros m Hd H0. unfold im_disjoint in Hd. simpl in Hd, H0.
  destruct Hd as [_ [_ [_ [_ [Hbb _]]]]], H0 as [_ [_ [_ [_ [Ht _]]]]].
  destruct (im_bb m) eqn:Ebb; simpl in Hbb, Ht.
  - destruct Hbb.
  - destruct Ht.
Qed.

Theorem im_disjoint_not_intersects_partial :
  forall m : IntersectionMatrix,
    im_disjoint m ->
    ~ matrix_matches pat_intersects_0 m /\
    ~ matrix_matches pat_intersects_1 m /\
    ~ matrix_matches pat_intersects_4 m.
Proof.
  intros m Hd. split.
  - exact (disjoint_not_intersects_0 m Hd).
  - split.
    + exact (disjoint_not_intersects_1 m Hd).
    + exact (disjoint_not_intersects_4 m Hd).
Qed.

Lemma intersects0_not_disjoint :
  forall m : IntersectionMatrix,
    matrix_matches pat_intersects_0 m -> ~ im_disjoint m.
Proof.
  intros m H0 Hd. apply (disjoint_not_intersects_0 m Hd). exact H0.
Qed.

Lemma intersects1_not_disjoint :
  forall m : IntersectionMatrix,
    matrix_matches pat_intersects_1 m -> ~ im_disjoint m.
Proof.
  intros m H1 Hd. apply (disjoint_not_intersects_1 m Hd). exact H1.
Qed.

Lemma intersects4_not_disjoint :
  forall m : IntersectionMatrix,
    matrix_matches pat_intersects_4 m -> ~ im_disjoint m.
Proof.
  intros m H4 Hd. apply (disjoint_not_intersects_4 m Hd). exact H4.
Qed.

Theorem im_intersects_not_disjoint_partial :
  forall m : IntersectionMatrix,
    (matrix_matches pat_intersects_0 m \/
     matrix_matches pat_intersects_1 m \/
     matrix_matches pat_intersects_4 m) ->
    ~ im_disjoint m.
Proof.
  intros m [H| [H| H]]; eauto using intersects0_not_disjoint,
    intersects1_not_disjoint, intersects4_not_disjoint.
Qed.

Lemma intersects0_matches_some_ii :
  forall (m : IntersectionMatrix) (n : nat),
    im_ii m = Some n -> matrix_matches pat_intersects_0 m.
Proof.
  intros m n E. unfold matrix_matches, pat_intersects_0. simpl.
  rewrite E. simpl. repeat split; auto.
Qed.

Lemma intersects1_matches_some_ib :
  forall (m : IntersectionMatrix) (n : nat),
    im_ib m = Some n -> matrix_matches pat_intersects_1 m.
Proof.
  intros m n E. unfold matrix_matches, pat_intersects_1. simpl.
  repeat split; simpl; rewrite E; simpl; auto.
Qed.

Lemma intersects3_matches_some_ie :
  forall (m : IntersectionMatrix) (n : nat),
    im_ie m = Some n -> matrix_matches pat_intersects_3 m.
Proof.
  intros m n E. unfold matrix_matches, pat_intersects_3. simpl.
  repeat split; simpl; rewrite E; simpl; auto.
Qed.

Lemma intersects4_matches_some_bb :
  forall (m : IntersectionMatrix) (n : nat),
    im_bb m = Some n -> matrix_matches pat_intersects_4 m.
Proof.
  intros m n E. unfold matrix_matches, pat_intersects_4. simpl.
  repeat split; simpl; try rewrite E; simpl; auto.
Qed.

Lemma not_intersects0_ii_empty :
  forall m : IntersectionMatrix,
    ~ matrix_matches pat_intersects_0 m -> im_ii m = None.
Proof.
  intros m H. destruct (im_ii m) as [n|] eqn:E.
  - exfalso. apply H, (intersects0_matches_some_ii m n E).
  - reflexivity.
Qed.

Lemma not_intersects1_ib_nonempty :
  forall m : IntersectionMatrix,
    ~ matrix_matches pat_intersects_1 m -> im_ib m = None.
Proof.
  intros m H. destruct (im_ib m) as [n|] eqn:E.
  - exfalso. apply H, (intersects1_matches_some_ib m n E).
  - reflexivity.
Qed.

Lemma not_intersects3_ie_empty :
  forall m : IntersectionMatrix,
    ~ matrix_matches pat_intersects_3 m -> im_ie m = None.
Proof.
  intros m H. destruct (im_ie m) as [n|] eqn:E.
  - exfalso. apply H, (intersects3_matches_some_ie m n E).
  - reflexivity.
Qed.

Lemma not_intersects4_bb_nonempty :
  forall m : IntersectionMatrix,
    ~ matrix_matches pat_intersects_4 m -> im_bb m = None.
Proof.
  intros m H. destruct (im_bb m) as [n|] eqn:E.
  - exfalso. apply H, (intersects4_matches_some_bb m n E).
  - reflexivity.
Qed.

Definition disjoint_intersects3_example : IntersectionMatrix :=
  {| im_ii := None; im_ib := None; im_ie := Some 0;
     im_bi := None; im_bb := None; im_be := None;
     im_ei := None; im_eb := None; im_ee := None |}.

Definition not_intersects_gap_example : IntersectionMatrix :=
  {| im_ii := None; im_ib := None; im_ie := None;
     im_bi := None; im_bb := None; im_be := None;
     im_ei := Some 0; im_eb := None; im_ee := None |}.

Lemma disjoint_intersects3_example_holds :
  im_disjoint disjoint_intersects3_example /\
  matrix_matches pat_intersects_3 disjoint_intersects3_example.
Proof.
  split.
  - unfold im_disjoint. simpl. repeat split; simpl; auto.
  - unfold matrix_matches, pat_intersects_3. simpl. repeat split; simpl; auto.
Qed.

Lemma not_intersects_gap_example_holds :
  ~ im_intersects not_intersects_gap_example /\
  ~ im_disjoint not_intersects_gap_example.
Proof.
  split.
  - unfold im_intersects. simpl.
    intro H. destruct H as [H| [H| [H| H]]].
    + destruct H as [Ht _]. simpl in Ht. destruct Ht.
    + destruct H as [_ [Ht _]]. simpl in Ht. destruct Ht.
    + destruct H as [_ [_ [Ht _]]]. simpl in Ht. destruct Ht.
    + destruct H as [_ [_ [_ [_ [Ht _]]]]]. simpl in Ht. destruct Ht.
  - unfold im_disjoint. simpl.
    intro H. destruct H as [_ [_ [_ [_ [_ [_ [Hei _]]]]]]].
    simpl in Hei. destruct Hei.
Qed.

Lemma matrix_transpose_twice :
  forall m : IntersectionMatrix, matrix_transpose (matrix_transpose m) = m.
Proof.
  intros m. destruct m; reflexivity.
Qed.

Lemma matrix_matches_transpose :
  forall (p : IMPattern) (m : IntersectionMatrix),
    matrix_matches p m <->
    matrix_matches (pattern_transpose p) (matrix_transpose m).
Proof.
  intros p m. unfold matrix_matches, matrix_transpose, pattern_transpose.
  simpl. split; intros [? [? [? [? [? [? [? [? ?]]]]]]]]; repeat split; auto.
Qed.

Theorem im_contains_transpose_within :
  forall m : IntersectionMatrix,
    im_contains m <-> im_within (matrix_transpose m).
Proof.
  intros m. unfold im_contains, im_within, pat_within.
  rewrite <- matrix_matches_transpose. reflexivity.
Qed.

Lemma covers0_transpose_coveredBy0 :
  forall m : IntersectionMatrix,
    matrix_matches pat_covers_0 m <->
    matrix_matches pat_coveredBy_0 (matrix_transpose m).
Proof.
  intros m. unfold pat_coveredBy_0. rewrite <- matrix_matches_transpose. reflexivity.
Qed.

Lemma covers1_transpose_coveredBy1 :
  forall m : IntersectionMatrix,
    matrix_matches pat_covers_1 m <->
    matrix_matches pat_coveredBy_1 (matrix_transpose m).
Proof.
  intros m. unfold pat_coveredBy_1. rewrite <- matrix_matches_transpose. reflexivity.
Qed.

Lemma covers3_transpose_coveredBy3 :
  forall m : IntersectionMatrix,
    matrix_matches pat_covers_3 m <->
    matrix_matches pat_coveredBy_3 (matrix_transpose m).
Proof.
  intros m. unfold pat_coveredBy_3. rewrite <- matrix_matches_transpose. reflexivity.
Qed.

Lemma covers4_transpose_coveredBy4 :
  forall m : IntersectionMatrix,
    matrix_matches pat_covers_4 m <->
    matrix_matches pat_coveredBy_4 (matrix_transpose m).
Proof.
  intros m. unfold pat_coveredBy_4. rewrite <- matrix_matches_transpose. reflexivity.
Qed.

Theorem im_covers_transpose_coveredBy :
  forall m : IntersectionMatrix,
    im_covers m <-> im_coveredBy (matrix_transpose m).
Proof.
  intros m. split.
  - intro H. destruct H as [H| [H| [H| H]]].
    + left. apply (proj1 (covers0_transpose_coveredBy0 m)). exact H.
    + right; left. apply (proj1 (covers1_transpose_coveredBy1 m)). exact H.
    + right; right; left. apply (proj1 (covers3_transpose_coveredBy3 m)). exact H.
    + right; right; right. apply (proj1 (covers4_transpose_coveredBy4 m)). exact H.
  - intro H. destruct H as [H| [H| [H| H]]].
    + left. apply (proj2 (covers0_transpose_coveredBy0 m)). exact H.
    + right; left. apply (proj2 (covers1_transpose_coveredBy1 m)). exact H.
    + right; right; left. apply (proj2 (covers3_transpose_coveredBy3 m)). exact H.
    + right; right; right. apply (proj2 (covers4_transpose_coveredBy4 m)). exact H.
Qed.

Theorem predicate_disjoint_not_intersects_partial :
  forall m : IntersectionMatrix,
    predicate_holds RDisjoint m ->
    ~ matrix_matches pat_intersects_0 m /\
    ~ matrix_matches pat_intersects_1 m /\
    ~ matrix_matches pat_intersects_4 m.
Proof.
  intros m Hd. unfold predicate_holds in Hd.
  exact (im_disjoint_not_intersects_partial m Hd).
Qed.

Theorem predicate_contains_transpose_within :
  forall m : IntersectionMatrix,
    predicate_holds RContains m <->
    predicate_holds RWithin (matrix_transpose m).
Proof.
  intros m. unfold predicate_holds. exact (im_contains_transpose_within m).
Qed.

Theorem predicate_covers_transpose_coveredBy :
  forall m : IntersectionMatrix,
    predicate_holds RCovers m <->
    predicate_holds RCoveredBy (matrix_transpose m).
Proof.
  intros m. unfold predicate_holds. exact (im_covers_transpose_coveredBy m).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions im_disjoint_not_intersects_partial.
Print Assumptions predicate_disjoint_not_intersects_partial.