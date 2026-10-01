(* ============================================================================
   NetTopologySuite.Proofs.IntakeCarried
   ----------------------------------------------------------------------------
   ADR-0009 / #866: CST span carrier beside CircSlice.
   CircSlice stays CircQuarter | CircFullOgc | CircUnknown.
   One optional (theta0, dtheta) slot per 3-point window.
   Intake checks; it does not compute atan2 for A <> B.
   CircFullOgc / A = B ignores the slot (0007-intake-angles).
   A slot try_carried accepts equals the computed egg:
   carried_slot_is_computed is circ_egg_eq after
   intake_angles_agree after try_carried_check.
   Not a Sheet remint. Not a TaggedCst remint. Not CircGamma.

   claimId: 0009-cst-span-carrier
   witness: 0009-cst-span-carrier
   board: ADR-0009
   3-axiom host. No Admitted / Axiom / Parameter.
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals List.
From NTS.Proofs Require Import Distance SheetHenCook IntakeAngles IntakeWalker.
Import ListNotations.
Local Open Scope R_scope.
Local Open Scope list_scope.

Definition CircSpanSlot : Type := option (R * R).
Definition CircSpanList : Type := list CircSpanSlot.

Inductive SpanDecline : Type :=
| ID_MissingCircSpan
| ID_CircSpanDisagree
| ID_SpanOther (r : IntakeDeclineReason).

Inductive SpanResult : Type :=
| SpanBag : ShcBag -> SpanResult
| SpanDeclineOf : SpanDecline -> SpanResult.

Definition span_of_angle_fail (f : AngleFail) : SpanDecline :=
  match f with
  | AF_SpanMismatch => ID_CircSpanDisagree
  | _ => ID_SpanOther (angle_fail_reason f)
  end.

(* circ_windows / circ_windows_from live in IntakeCompoundFold. *)

Definition map_window (s : Sheet) (sl : CircSlice)
  (a m b : Point) (slot : CircSpanSlot) : SpanResult :=
  match sl with
  | CircFullOgc =>
      match map_cs_unknown s [a; m; b] with
      | IntakeBag bag => SpanBag bag
      | IntakeDecline r => SpanDeclineOf (ID_SpanOther r)
      end
  | CircQuarter | CircUnknown =>
      if Req_EM_T (dist_sq a b) 0 then
        match map_cs_unknown s [a; m; b] with
        | IntakeBag bag => SpanBag bag
        | IntakeDecline r => SpanDeclineOf (ID_SpanOther r)
        end
      else
        match slot with
        | None => SpanDeclineOf ID_MissingCircSpan
        | Some (th, dth) =>
            match try_carried a m b th dth with
            | inr f => SpanDeclineOf (span_of_angle_fail f)
            | inl e => SpanBag (map_cs_from_build s [e] [a; b])
            end
        end
  end.

Fixpoint map_windows (s : Sheet) (sl : CircSlice)
  (ws : list (Point * Point * Point)) (slots : CircSpanList) {struct ws}
  : SpanResult :=
  match ws, slots with
  | [], [] => SpanDeclineOf (ID_SpanOther ID_Empty)
  | [], _ :: _ => SpanDeclineOf (ID_SpanOther ID_BadPointCount)
  | _ :: _, [] => SpanDeclineOf ID_MissingCircSpan
  | (a, m, b) :: rest, slot :: slots' =>
      match map_window s sl a m b slot with
      | SpanDeclineOf r => SpanDeclineOf r
      | SpanBag b0 =>
          match rest with
          | [] => SpanBag b0
          | _ =>
              match map_windows s sl rest slots' with
              | SpanDeclineOf r => SpanDeclineOf r
              | SpanBag b1 => SpanBag (append_bags s b0 b1)
              end
          end
      end
  end.

Definition map_cs_span_list (s : Sheet) (sl : CircSlice)
  (pts : list Point) (spans : CircSpanList) : SpanResult :=
  match sl with
  | CircFullOgc =>
      match map_cs_unknown s pts with
      | IntakeBag bag => SpanBag bag
      | IntakeDecline r => SpanDeclineOf (ID_SpanOther r)
      end
  | CircQuarter | CircUnknown => map_windows s sl (circ_windows pts) spans
  end.

Lemma circ_full_ogc_ignores_spans :
  forall s pts spans bag,
  map_cs_unknown s pts = IntakeBag bag ->
  map_cs_span_list s CircFullOgc pts spans = SpanBag bag.
Proof.
  intros s pts spans bag H.
  unfold map_cs_span_list. rewrite H. reflexivity.
Qed.

Lemma missing_slot_a_neq_b :
  forall s sl a m b,
  sl <> CircFullOgc ->
  dist_sq a b <> 0 ->
  map_window s sl a m b None = SpanDeclineOf ID_MissingCircSpan.
Proof.
  intros s sl a m b Hsl Hab.
  destruct sl; try (exfalso; apply Hsl; reflexivity).
  - unfold map_window.
    destruct (Req_EM_T (dist_sq a b) 0) as [Z|N]; [exfalso; exact (Hab Z)|].
    reflexivity.
  - unfold map_window.
    destruct (Req_EM_T (dist_sq a b) 0) as [Z|N]; [exfalso; exact (Hab Z)|].
    reflexivity.
Qed.

Lemma carried_window_bag :
  forall s sl a m b th dth e,
  sl <> CircFullOgc ->
  dist_sq a b <> 0 ->
  try_carried a m b th dth = inl e ->
  map_window s sl a m b (Some (th, dth)) =
    SpanBag (map_cs_from_build s [e] [a; b]).
Proof.
  intros s sl a m b th dth e Hsl Hab Ht.
  destruct sl; try (exfalso; apply Hsl; reflexivity).
  - unfold map_window.
    destruct (Req_EM_T (dist_sq a b) 0) as [Z|N]; [exfalso; exact (Hab Z)|].
    rewrite Ht. reflexivity.
  - unfold map_window.
    destruct (Req_EM_T (dist_sq a b) 0) as [Z|N]; [exfalso; exact (Hab Z)|].
    rewrite Ht. reflexivity.
Qed.

Lemma carried_window_disagree :
  forall s sl a m b th dth,
  sl <> CircFullOgc ->
  dist_sq a b <> 0 ->
  try_carried a m b th dth = inr AF_SpanMismatch ->
  map_window s sl a m b (Some (th, dth)) =
    SpanDeclineOf ID_CircSpanDisagree.
Proof.
  intros s sl a m b th dth Hsl Hab Ht.
  destruct sl; try (exfalso; apply Hsl; reflexivity).
  - unfold map_window.
    destruct (Req_EM_T (dist_sq a b) 0) as [Z|N]; [exfalso; exact (Hab Z)|].
    rewrite Ht. reflexivity.
  - unfold map_window.
    destruct (Req_EM_T (dist_sq a b) 0) as [Z|N]; [exfalso; exact (Hab Z)|].
    rewrite Ht. reflexivity.
Qed.

(* F2 try_carried_check, F3 intake_angles_agree, F5 circ_egg_eq.
   The slot (th, dth) is the (θ₀, Δθ) of that egg. *)
Lemma carried_slot_is_computed : forall a m b th dth c,
  try_carried a m b th dth = inl c ->
  th = circ_theta0 (egg_of_points a m b) /\
  dth = circ_sweep (egg_of_points a m b).
Proof.
  intros a m b th dth c H.
  destruct (try_carried_check a m b th dth c H) as [Hc Hmk].
  destruct (intake_angles_agree c a m b Hc) as [Ho [Hr [Hth Hs]]].
  assert (Heq : c = egg_of_points a m b).
  { apply circ_egg_eq; assumption. }
  assert (Hth' : circ_theta0 c = th).
  { rewrite Hmk. reflexivity. }
  assert (Hs' : circ_sweep c = dth).
  { rewrite Hmk. reflexivity. }
  rewrite Heq in Hth', Hs'.
  split; symmetry; assumption.
Qed.

(* WITNESS {"claimId":"0009-cst-span-carrier","topic":"core","lemma":"ticket_0009_cst_span_carrier_qed_or_qex","title":"A span slot try_carried accepts equals the computed egg angles; QED arm is carried_slot_is_computed; a disagreeing success is not claimed","file":"theories/IntakeCarried.v","witness":"0009-cst-span-carrier","board":"ADR-0009"} *)
Theorem ticket_0009_cst_span_carrier_qed_or_qex :
  (forall a m b th dth c,
     try_carried a m b th dth = inl c ->
     th = circ_theta0 (egg_of_points a m b) /\
     dth = circ_sweep (egg_of_points a m b))
  \/
  (exists a m b th dth c,
     try_carried a m b th dth = inl c /\
     (th <> circ_theta0 (egg_of_points a m b) \/
      dth <> circ_sweep (egg_of_points a m b))).
Proof.
  left. exact carried_slot_is_computed.
Qed.

Print Assumptions circ_full_ogc_ignores_spans.
Print Assumptions missing_slot_a_neq_b.
Print Assumptions carried_window_bag.
Print Assumptions carried_window_disagree.
Print Assumptions carried_slot_is_computed.
Print Assumptions ticket_0009_cst_span_carrier_qed_or_qex.
