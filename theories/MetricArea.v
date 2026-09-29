(* ============================================================================
   NetTopologySuite.Proofs.MetricArea
   ----------------------------------------------------------------------------
   Generic signed-area FORMULA of a closed chain of members. A member is
   a chord or a circular arc. The formula is the shoelace of the spine
   (the start vertex of each member) plus a signed circular-segment bulge
   on each arc. A chord bulge is zero. The arc bulge is
   ArcArea.segment_area, already r²/2 · (θ − sin θ).

   An arc member is a CircularEgg. Its fields are not independent:
   p = γ(0), q = γ(1), r = circ_r, θ = circ_sweep (the signed sweep),
   with γ = circ_eval. That is the smart constructor MArc.

   ring_closed: consecutive members meet (end = next start) and the last
   end returns to the first start. signed_area2 closes that ring, and it
   is twice the shoelace, so the split divides it by two.

   The member-level Green identity (½∫(x y' − y x') = ½ cross + bulge)
   and the sum that makes members_area the curve's signed area live in
   MetricGreen.v.

   Deferrals, named:
     * clothoid and NURBS members are not circular segments. This file
       has only MChord and MArc.
     * segment_area is not reminted. arc_r_theta_is_curve_length is not
       this file.

   WITNESS topic: metric · claimId: 0001-metric-area
   · witness: members_area_split
   board: ADR-0001
   No Admitted / Axiom / Parameter.
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance RingArea979 ArcArea SheetHenCircEgg.
Import ListNotations.
Local Open Scope R_scope.

Inductive area_member : Type :=
| MChord : Point -> Point -> area_member
| MArc : CircularEgg -> area_member.

Definition member_start (m : area_member) : Point :=
  match m with
  | MChord p _ => p
  | MArc e => circ_eval e 0
  end.

Definition member_end (m : area_member) : Point :=
  match m with
  | MChord _ q => q
  | MArc e => circ_eval e 1
  end.

Definition member_bulge (m : area_member) : R :=
  match m with
  | MChord _ _ => 0
  | MArc e => segment_area (circ_r e) (circ_sweep e)
  end.

Lemma marc_from_egg : forall e,
  member_start (MArc e) = circ_eval e 0 /\
  member_end (MArc e) = circ_eval e 1 /\
  member_bulge (MArc e) = segment_area (circ_r e) (circ_sweep e).
Proof. intros e. repeat split; reflexivity. Qed.

Definition member_cross (m : area_member) : R :=
  edge_cross (member_start m) (member_end m).

Fixpoint bulges (ms : list area_member) : R :=
  match ms with
  | [] => 0
  | m :: t => member_bulge m + bulges t
  end.

Fixpoint crosses (ms : list area_member) : R :=
  match ms with
  | [] => 0
  | m :: t => member_cross m + crosses t
  end.

Definition members_area (ms : list area_member) : R :=
  crosses ms / 2 + bulges ms.

Definition spine (ms : list area_member) : list Point :=
  map member_start ms.

Fixpoint consec_closed (ms : list area_member) : Prop :=
  match ms with
  | [] => True
  | m :: t =>
      match t with
      | [] => True
      | m2 :: _ => member_end m = member_start m2 /\ consec_closed t
      end
  end.

Fixpoint mlast (ms : list area_member) : area_member :=
  match ms with
  | [] => MChord (mkPoint 0 0) (mkPoint 0 0)
  | [m] => m
  | _ :: t => mlast t
  end.

Definition ring_closed (ms : list area_member) : Prop :=
  consec_closed ms /\
  match ms with
  | [] => True
  | m :: _ => member_end (mlast ms) = member_start m
  end.

Lemma chord_bulge_zero : forall p q, member_bulge (MChord p q) = 0.
Proof. reflexivity. Qed.

Lemma arc_bulge_is_segment :
  forall e, member_bulge (MArc e) = segment_area (circ_r e) (circ_sweep e).
Proof. reflexivity. Qed.

Lemma arc_bulge_nonneg :
  forall e, 0 <= circ_sweep e -> 0 <= member_bulge (MArc e).
Proof.
  intros e Ht. rewrite arc_bulge_is_segment. apply segment_area_nonneg. exact Ht.
Qed.

Lemma crosses_cons : forall m ms, crosses (m :: ms) = member_cross m + crosses ms.
Proof. reflexivity. Qed.

Lemma spine_cons : forall m ms, spine (m :: ms) = member_start m :: spine ms.
Proof. reflexivity. Qed.

Lemma mlast_cons : forall m m2 t, mlast (m :: m2 :: t) = mlast (m2 :: t).
Proof. intros. simpl. destruct t; reflexivity. Qed.

Lemma crosses_closed_shoelace :
  forall ms p0,
    ms <> [] ->
    consec_closed ms ->
    member_end (mlast ms) = p0 ->
    crosses ms = shoelace_open (spine ms ++ [p0]).
Proof.
  induction ms as [|m ms IH]; intros p0 Hne Hcons Hend.
  - contradiction.
  - destruct ms as [|m2 rest].
    + simpl in Hend.
      rewrite crosses_cons. replace (crosses []) with 0 by reflexivity.
      rewrite Rplus_0_r.
      rewrite spine_cons. replace (spine []) with (@nil Point) by reflexivity.
      cbn [app].
      rewrite shoelace_open_cons2, shoelace_open_single.
      unfold member_cross. rewrite Hend. ring.
    + simpl in Hcons. destruct Hcons as [Hjoin Hcons'].
      assert (Hne2 : (m2 :: rest) <> []) by discriminate.
      assert (Hend2 : member_end (mlast (m2 :: rest)) = p0).
      { rewrite mlast_cons in Hend. exact Hend. }
      specialize (IH p0 Hne2 Hcons' Hend2).
      rewrite crosses_cons. rewrite IH.
      rewrite (spine_cons m (m2 :: rest)).
      rewrite (spine_cons m2 rest).
      cbn [app].
      rewrite shoelace_open_cons2.
      rewrite <- Hjoin. unfold member_cross. ring.
Qed.

(* WITNESS {"claimId":"0001-metric-area","topic":"metric","lemma":"members_area_split","title":"Shoelace plus circular-segment bulges","file":"theories/MetricArea.v","witness":"members_area_split","board":"ADR-0001"} *)
Theorem members_area_split :
  forall ms, ring_closed ms ->
    members_area ms = signed_area2 (spine ms) / 2 + bulges ms.
Proof.
  intros ms [Hcons Hclose].
  unfold members_area.
  destruct ms as [|m ms].
  - unfold crosses, bulges, signed_area2, spine. simpl. field.
  - assert (Hend : member_end (mlast (m :: ms)) = member_start m) by exact Hclose.
    assert (Hsh : crosses (m :: ms) =
                   shoelace_open (spine (m :: ms) ++ [member_start m])).
    { apply crosses_closed_shoelace; [discriminate | exact Hcons | exact Hend]. }
    assert (Hsa : signed_area2 (spine (m :: ms)) =
                   shoelace_open (spine (m :: ms) ++ [member_start m])).
    { unfold signed_area2, spine. simpl. reflexivity. }
    rewrite Hsh, <- Hsa. field.
Qed.

Print Assumptions marc_from_egg.
Print Assumptions chord_bulge_zero.
Print Assumptions arc_bulge_is_segment.
Print Assumptions arc_bulge_nonneg.
Print Assumptions crosses_cons.
Print Assumptions spine_cons.
Print Assumptions mlast_cons.
Print Assumptions crosses_closed_shoelace.
Print Assumptions members_area_split.
