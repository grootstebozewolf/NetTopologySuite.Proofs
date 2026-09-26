(* ============================================================================
   NetTopologySuite.Proofs.NurbsDeBoor
   ----------------------------------------------------------------------------
   Clean-room A4.1 (Piegl–Tiller), homogeneous coordinates. Not a copy of
   QGIS. GPL code is not imported. The cook of MkNurbs stays IDecline.

   Year-1 spec, degree-general where it is cheap and degree 1 for the
   chord-error claim:
     N-L1  a sample is an evaluation
     N-L2  clamped start (and clamped end) evaluate to the outer control
     N-L3  a degree-1 positive-weight curve is the chord, so the
           uniform polyline has chord error 0

   Knot denominators that are zero are outside these lemmas. QGIS skips
   that blend; here the proved region is the one where the denominator
   is the positive end span, so the skip does not fire.

   No Admitted. No Axiom. No Parameter.
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia PeanoNat.
From Stdlib Require Import List.
From NTS.Proofs Require Import Distance SheetHenCook.
Import ListNotations.
Local Open Scope R_scope.

Definition nthR (l : list R) (i : nat) : R := nth i l 0.

Definition hom_x (ctrl : list Point) (W : list R) (i : nat) : R :=
  px (nth i ctrl (mkPoint 0 0)) * nthR W i.
Definition hom_y (ctrl : list Point) (W : list R) (i : nat) : R :=
  py (nth i ctrl (mkPoint 0 0)) * nthR W i.

Definition knot_idx (span p j : nat) : nat := span - p + j.

Definition alpha_at (U : list R) (span p k j : nat) (u : R) : R :=
  let idx := knot_idx span p j in
  (u - nthR U idx) / (nthR U (idx + (p - k) + 1) - nthR U idx).

Definition blend (a prev cur : R) : R := (1 - a) * prev + a * cur.

Definition round_deboor (k span p : nat) (U : list R) (u : R) (row : list R)
  : list R :=
  map (fun j =>
    if Nat.ltb j k then nthR row j
    else blend (alpha_at U span p k j u) (nthR row (j - 1)) (nthR row j))
    (seq 0 (length row)).

Fixpoint deboor_rounds (m span p : nat) (U : list R) (u : R) (row : list R)
  : list R :=
  match m with
  | O => row
  | S m' =>
      round_deboor (S m') span p U u (deboor_rounds m' span p U u row)
  end.

Definition round_alpha0 (k : nat) (row : list R) : list R :=
  map (fun j => if Nat.ltb j k then nthR row j else nthR row (j - 1))
      (seq 0 (length row)).

Fixpoint rounds_alpha0 (m : nat) (row : list R) : list R :=
  match m with
  | O => row
  | S m' => round_alpha0 (S m') (rounds_alpha0 m' row)
  end.

Lemma nth_seq_start : forall start n i d,
  i < n -> nth i (seq start n) d = start + i.
Proof.
  intros start n. revert start.
  induction n as [|n IH]; intros start i d Hi; [lia|].
  destruct i as [|i]; simpl; [lia|].
  rewrite IH by lia. lia.
Qed.

Lemma map_nth_seq : forall (f : nat -> R) n i,
  i < n -> nth i (map f (seq 0 n)) 0 = f i.
Proof.
  intros f n i Hi.
  rewrite nth_map with (d:=0).
  - rewrite nth_seq_start by assumption. reflexivity.
  - rewrite length_seq. exact Hi.
Qed.

Lemma round_alpha0_length : forall k row,
  length (round_alpha0 k row) = length row.
Proof.
  intros. unfold round_alpha0. rewrite length_map, length_seq. reflexivity.
Qed.

Lemma rounds_alpha0_length : forall m row,
  length (rounds_alpha0 m row) = length row.
Proof.
  induction m; intros; simpl; [reflexivity|].
  rewrite round_alpha0_length. apply IHm.
Qed.

Lemma round_alpha0_nth : forall k row j,
  j < length row ->
  nth j (round_alpha0 k row) 0 =
    if Nat.ltb j k then nthR row j else nthR row (j - 1).
Proof.
  intros k row j Hj. unfold round_alpha0, nthR.
  rewrite map_nth_seq by exact Hj. reflexivity.
Qed.

Lemma rounds_alpha0_nth : forall m row j,
  m <= j ->
  j < length row ->
  nth j (rounds_alpha0 m row) 0 = nth (j - m) row 0.
Proof.
  induction m as [|m IH]; intros row j Hmj Hj.
  - simpl. rewrite Nat.sub_0_r. reflexivity.
  - simpl. rewrite round_alpha0_nth.
    + assert (Hlt : Nat.ltb j (S m) = false) by (apply Nat.ltb_ge; lia).
      rewrite Hlt. rewrite IH by lia.
      replace (j - 1 - m) with (j - S m) by lia. reflexivity.
    + rewrite rounds_alpha0_length. exact Hj.
Qed.

Lemma blend_zero : forall prev cur, blend 0 prev cur = prev.
Proof. intros. unfold blend. ring. Qed.

Lemma blend_one : forall prev cur, blend 1 prev cur = cur.
Proof. intros. unfold blend. ring. Qed.

Definition clamped_lo (U : list R) (p : nat) : Prop :=
  forall i, i <= p -> nthR U i = nthR U 0.

Definition clamped_hi (U : list R) (n p : nat) : Prop :=
  forall i, n <= i <= n + p -> nthR U i = nthR U n.

Lemma alpha_zero_on_prefix : forall U span p k j u,
  span = p ->
  j <= p ->
  u = nthR U 0 ->
  clamped_lo U p ->
  alpha_at U span p k j u = 0.
Proof.
  intros U span p k j u Hspan Hj Hu Hc.
  unfold alpha_at, knot_idx. rewrite Hspan.
  replace (p - p + j) with j by lia.
  assert (nthR U j = u) by (rewrite Hc by lia; exact Hu).
  rewrite H. unfold Rdiv. rewrite Rminus_diag_eq by reflexivity.
  apply Rmult_0_l.
Qed.

Lemma round_deboor_length : forall k span p U u row,
  length (round_deboor k span p U u row) = length row.
Proof.
  intros. unfold round_deboor. rewrite length_map, length_seq. reflexivity.
Qed.

Lemma deboor_rounds_length : forall m span p U u row,
  length (deboor_rounds m span p U u row) = length row.
Proof.
  induction m; intros; simpl; [reflexivity|].
  rewrite round_deboor_length. apply IHm.
Qed.

Lemma round_deboor_is_alpha0 : forall k p U u row,
  k <= p ->
  length row = S p ->
  clamped_lo U p ->
  u = nthR U 0 ->
  round_deboor k p p U u row = round_alpha0 k row.
Proof.
  intros k p U u row Hk Hlen Hc Hu.
  unfold round_deboor, round_alpha0.
  apply map_ext_in. intros j Hj.
  assert (Hj' : j < S p) by (apply in_seq in Hj; lia).
  destruct (Nat.ltb j k) eqn:Hlt.
  - reflexivity.
  - assert (Ha : alpha_at U p p k j u = 0).
    { apply alpha_zero_on_prefix; [reflexivity | lia | exact Hu | exact Hc]. }
    rewrite Ha. rewrite blend_zero. reflexivity.
Qed.

Lemma deboor_rounds_is_alpha0 : forall m p U u row,
  m <= p ->
  length row = S p ->
  clamped_lo U p ->
  u = nthR U 0 ->
  deboor_rounds m p p U u row = rounds_alpha0 m row.
Proof.
  induction m as [|m IH]; intros p U u row Hm Hlen Hc Hu; simpl.
  - reflexivity.
  - rewrite IH.
    + lia.
    + exact Hlen.
    + exact Hc.
    + exact Hu.
    rewrite round_deboor_is_alpha0.
    + reflexivity.
    + lia.
    + rewrite rounds_alpha0_length. exact Hlen.
    + exact Hc.
    + exact Hu.
Qed.

Lemma deboor_start_slot : forall p U u row,
  length row = S p ->
  clamped_lo U p ->
  u = nthR U 0 ->
  nth p (deboor_rounds p p p U u row) 0 = nth 0 row 0.
Proof.
  intros p U u row Hlen Hc Hu.
  rewrite deboor_rounds_is_alpha0.
  - lia.
  - exact Hlen.
  - exact Hc.
  - exact Hu.
  rewrite rounds_alpha0_nth.
  - lia.
  - rewrite Hlen. lia.
  rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma round_top_when_alpha_one : forall k span p U u row,
  k <= p ->
  length row = S p ->
  alpha_at U span p k p u = 1 ->
  nth p (round_deboor k span p U u row) 0 = nth p row 0.
Proof.
  intros k span p U u row Hk Hlen Ha.
  assert (Hp : p < length (round_deboor k span p U u row)).
  { rewrite round_deboor_length, Hlen. lia. }
  unfold round_deboor.
  rewrite map_nth_seq by (rewrite Hlen; lia).
  assert (Hlt : Nat.ltb p k = false) by (apply Nat.ltb_ge; lia).
  rewrite Hlt, Ha, blend_one. reflexivity.
Qed.

Lemma deboor_end_slot : forall p span U u row,
  length row = S p ->
  (forall k, 1 <= k <= p -> alpha_at U span p k p u = 1) ->
  nth p (deboor_rounds p span p U u row) 0 = nth p row 0.
Proof.
  intros p span U u row Hlen Ha.
  assert (Hgen : forall m,
    m <= p ->
    nth p (deboor_rounds m span p U u row) 0 = nth p row 0).
  { induction m as [|m IH]; intros Hm.
    - simpl. reflexivity.
    - simpl. rewrite round_top_when_alpha_one.
      + lia.
      + rewrite deboor_rounds_length. exact Hlen.
      + apply Ha. lia.
      + apply IH. lia. }
  apply Hgen. lia.
Qed.

Lemma alpha_one_at_end : forall U n p k u,
  1 <= k <= p ->
  (p < n)%nat ->
  clamped_hi U n p ->
  nthR U (n - 1) <> nthR U n ->
  u = nthR U n ->
  alpha_at U (n - 1) p k p u = 1.
Proof.
  intros U n p k u Hk Hpn Hc Hne Hu.
  unfold alpha_at, knot_idx.
  replace (n - 1 - p + p) with (n - 1) by lia.
  replace (n - 1 + (p - k) + 1) with (n + (p - k)) by lia.
  assert (Hhi : nthR U (n + (p - k)) = u).
  { rewrite Hc; [exact Hu | split; lia]. }
  rewrite Hhi, Hu.
  field. lra.
Qed.

Definition init_row (slot : nat -> R) (p : nat) : list R :=
  map slot (seq 0 (S p)).

Lemma init_row_length : forall slot p, length (init_row slot p) = S p.
Proof.
  intros. unfold init_row. rewrite length_map, length_seq. reflexivity.
Qed.

Lemma init_row_nth : forall slot p j,
  j <= p -> nth j (init_row slot p) 0 = slot j.
Proof.
  intros slot p j Hj. unfold init_row.
  rewrite map_nth_seq by lia. reflexivity.
Qed.

Lemma hom_div : forall x w, w <> 0 -> (x * w) / w = x.
Proof. intros x w Hw. field. exact Hw. Qed.

Theorem nurbs_nl2_start : forall ctrl W U p,
  (1 <= p)%nat ->
  (p < length ctrl)%nat ->
  length W = length ctrl ->
  clamped_lo U p ->
  0 < nthR W 0 ->
  let u := nthR U 0 in
  let rowX := init_row (fun j => hom_x ctrl W j) p in
  let rowW := init_row (fun j => nthR W j) p in
  let x := nth p (deboor_rounds p p p U u rowX) 0 in
  let w := nth p (deboor_rounds p p p U u rowW) 0 in
  w = nthR W 0 /\ x / w = px (nth 0 ctrl (mkPoint 0 0)).
Proof.
  intros ctrl W U p Hp Hpn Hlen Hc Hw u rowX rowW x w.
  assert (Hx0 : nth p (deboor_rounds p p p U u rowX) 0 = hom_x ctrl W 0).
  { rewrite deboor_start_slot.
    - apply init_row_length.
    - exact Hc.
    - reflexivity.
    - rewrite init_row_nth by lia. reflexivity. }
  assert (Hw0 : nth p (deboor_rounds p p p U u rowW) 0 = nthR W 0).
  { rewrite deboor_start_slot.
    - apply init_row_length.
    - exact Hc.
    - reflexivity.
    - rewrite init_row_nth by lia. reflexivity. }
  split.
  - unfold w. exact Hw0.
  - unfold x, w. rewrite Hx0, Hw0. unfold hom_x.
    apply hom_div. lra.
Qed.

Theorem nurbs_nl2_end : forall ctrl W U n p,
  (1 <= p < n)%nat ->
  length ctrl = n ->
  length W = n ->
  clamped_hi U n p ->
  nthR U (n - 1) <> nthR U n ->
  0 < nthR W (n - 1) ->
  let u := nthR U n in
  let span := n - 1 in
  let rowX := init_row (fun j => hom_x ctrl W (span - p + j)) p in
  let rowW := init_row (fun j => nthR W (span - p + j)) p in
  let x := nth p (deboor_rounds p span p U u rowX) 0 in
  let w := nth p (deboor_rounds p span p U u rowW) 0 in
  w = nthR W (n - 1) /\
  x / w = px (nth (n - 1) ctrl (mkPoint 0 0)).
Proof.
  intros ctrl W U n p Hp Hn HW Hc Hne Hwp u span rowX rowW x w.
  assert (Ha : forall k, 1 <= k <= p -> alpha_at U span p k p u = 1).
  { intros k Hk. unfold u, span.
    apply alpha_one_at_end.
    - exact Hk.
    - lia.
    - exact Hc.
    - exact Hne.
    - reflexivity. }
  assert (Hx : nth p (deboor_rounds p span p U u rowX) 0 =
               hom_x ctrl W (n - 1)).
  { rewrite deboor_end_slot.
    - apply init_row_length.
    - exact Ha.
    - unfold rowX. rewrite init_row_nth by lia.
      replace (span - p + p) with span by lia. reflexivity. }
  assert (Hw : nth p (deboor_rounds p span p U u rowW) 0 = nthR W (n - 1)).
  { rewrite deboor_end_slot.
    - apply init_row_length.
    - exact Ha.
    - unfold rowW. rewrite init_row_nth by lia.
      replace (span - p + p) with span by lia. reflexivity. }
  split.
  - unfold w. exact Hw.
  - unfold x, w. rewrite Hx, Hw. unfold hom_x. apply hom_div. lra.
Qed.

(* N-L1. Uniform samples are evaluations, so they lie on the curve. *)
Definition nurbs_sample (eval : R -> Point) (steps i : nat) : Point :=
  eval (INR i / INR steps).

Theorem n_l1_sample_is_eval : forall eval steps i,
  nurbs_sample eval steps i = eval (INR i / INR steps).
Proof. reflexivity. Qed.

(* Degree 1, positive weights: the single A4.1 step is a chord point. *)
Theorem n_l3_deg1_on_chord : forall x0 y0 w0 x1 y1 w1 a,
  0 <= a <= 1 ->
  0 < w0 -> 0 < w1 ->
  let den := (1 - a) * w0 + a * w1 in
  let x := ((1 - a) * (w0 * x0) + a * (w1 * x1)) / den in
  let y := ((1 - a) * (w0 * y0) + a * (w1 * y1)) / den in
  let t := (a * w1) / den in
  den <> 0 /\ 0 <= t <= 1 /\
  x = (1 - t) * x0 + t * x1 /\
  y = (1 - t) * y0 + t * y1.
Proof.
  intros x0 y0 w0 x1 y1 w1 a Ha Hw0 Hw1 den x y t.
  assert (H0 : 0 <= (1 - a) * w0) by (apply Rmult_le_pos; lra).
  assert (H1 : 0 <= a * w1) by (apply Rmult_le_pos; lra).
  assert (Hden : 0 < den).
  { assert (0 <= den) by (unfold den; lra).
    assert (Hnz : den <> 0).
    { intro E.
      assert (Hz0 : (1 - a) * w0 = 0) by (unfold den in E; lra).
      assert (Hz1 : a * w1 = 0) by (unfold den in E; lra).
      apply Rmult_integral in Hz0. destruct Hz0 as [Ha0|Hw].
      - assert (Ha1 : a = 1) by lra.
        rewrite Ha1 in Hz1. apply Rmult_integral in Hz1.
        destruct Hz1 as [Hw1|Hw1]; lra.
      - lra. }
    lra. }
  split; [lra|].
  split.
  - unfold t, den. split.
    + unfold Rdiv. apply Rmult_le_pos.
      * apply Rmult_le_pos; lra.
      * apply Rlt_le. apply Rinv_0_lt_compat. exact Hden.
    + apply (Rmult_le_reg_r den); [exact Hden|].
      unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l by lra.
      rewrite Rmult_1_r, Rmult_1_l. unfold den. lra.
  - split.
    + unfold x, t, den. field. lra.
    + unfold y, t, den. field. lra.
Qed.

(* QGIS block shape, not a string parser. Weights default to 1.
   Z/M/ZM are recorded and not evaluated here. *)
Inductive NurbsDim : Type :=
| ND_XY | ND_Z | ND_M | ND_ZM.

Record NurbsBlocks : Type := mkNurbsBlocks {
  nb_dim : NurbsDim;
  nb_degree : nat;
  nb_ctrl : list Point;
  nb_weight : option (list R);
  nb_knot : option (list R)
}.

Definition nb_weight_or_one (b : NurbsBlocks) : list R :=
  match nb_weight b with
  | Some w => w
  | None => map (fun _ => 1) (nb_ctrl b)
  end.

Lemma nb_weight_default_one : forall b i,
  nb_weight b = None ->
  i < length (nb_ctrl b) ->
  nthR (nb_weight_or_one b) i = 1.
Proof.
  intros b i Hw Hi. unfold nb_weight_or_one, nthR. rewrite Hw.
  rewrite nth_map with (d:=mkPoint 0 0) by exact Hi. reflexivity.
Qed.

Definition nurbs_wf (c : NurbsNet) : Prop :=
  let p := nn_degree c in
  let n := length (nn_ctrl c) in
  (1 <= p < n)%nat /\
  length (nn_knot c) = n + p + 1 /\
  length (nn_weight c) = n /\
  clamped_lo (nn_knot c) p /\
  clamped_hi (nn_knot c) n p /\
  nthR (nn_knot c) (n - 1) < nthR (nn_knot c) n /\
  forall i, i < n -> 0 < nthR (nn_weight c) i.

Theorem nurbs_wf_start : forall c,
  nurbs_wf c ->
  let p := nn_degree c in
  let u := nthR (nn_knot c) 0 in
  let rowX := init_row (fun j => hom_x (nn_ctrl c) (nn_weight c) j) p in
  let rowW := init_row (fun j => nthR (nn_weight c) j) p in
  nth p (deboor_rounds p p p (nn_knot c) u rowW) 0 <> 0 /\
  nth p (deboor_rounds p p p (nn_knot c) u rowX) 0 /
    nth p (deboor_rounds p p p (nn_knot c) u rowW) 0
  = px (nth 0 (nn_ctrl c) (mkPoint 0 0)).
Proof.
  intros c [Hp [Hlenk [Hlenw [Hlo [Hhi [Hspan Hpos]]]]]] p u rowX rowW.
  destruct (nurbs_nl2_start (nn_ctrl c) (nn_weight c) (nn_knot c) p)
    as [Hw Hx].
  - lia.
  - lia.
  - exact Hlenw.
  - exact Hlo.
  - apply Hpos. lia.
  - split.
    + rewrite Hw. apply Hpos. lia.
    + exact Hx.
Qed.

Print Assumptions nurbs_nl2_start.
Print Assumptions nurbs_nl2_end.
Print Assumptions n_l1_sample_is_eval.
Print Assumptions n_l3_deg1_on_chord.
Print Assumptions nurbs_wf_start.
Print Assumptions nb_weight_default_one.
