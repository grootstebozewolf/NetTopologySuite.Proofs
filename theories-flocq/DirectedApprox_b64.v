(* ============================================================================
   NetTopologySuite.Proofs.Flocq.DirectedApprox_b64
   ----------------------------------------------------------------------------
   Instantiation of `DirectedApprox` for the binary64 passes-through filter.
   Experiment write-up: docs/directed-approximation-2026-11.md.

   Verdict recorded here as theorems:
     * on the int-safe grid the filter is OVER  (existing Slice-9 result);
     * on the tight grid it is EXACT, i.e. gap 0 (existing C1 result);
     * off the grid it is NOT under (existing b64_passes_through_compute_unsound).
     * what is NOT here: OVER off the grid (C2) and a gap bound.  Both open.
   ========================================================================== *)

From Stdlib Require Import Bool.
From NTS.Proofs Require Import DirectedApprox.
From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import HotPixel_b64.
From NTS.Proofs.Flocq Require Import PassesThrough_b64_grid_core.
From NTS.Proofs.Flocq Require Import PassesThrough_b64_compute.
From NTS.Proofs.Flocq Require Import PassesThrough_b64_compute_unsound.
From NTS.Proofs.Flocq Require Import PassesThrough_b64_grid_complete.
From NTS.Proofs.Flocq Require Import PassesThrough_b64_grid_separation.

Definition pt_input := (BPoint * BPoint * BPoint)%type.

Definition pt_spec (t : pt_input) : Prop :=
  let '(P0, P1, C) := t in b64_passes_through_hot_pixel P0 P1 C = true.

Definition pt_comp (t : pt_input) : Prop :=
  let '(P0, P1, C) := t in b64_passes_through_hot_pixel_compute P0 P1 C = true.

Definition int_safe_dom (t : pt_input) : Prop :=
  let '(P0, P1, C) := t in
  bpoint_int_safe P0 /\ bpoint_int_safe P1 /\ bpoint_int_safe C.

Definition tight_dom (t : pt_input) : Prop :=
  let '(P0, P1, C) := t in
  bpoint_int_tight P0 /\ bpoint_int_tight P1 /\ bpoint_int_tight C.

Theorem pt_over_on_int_safe : over_on int_safe_dom pt_spec pt_comp.
Proof.
  intros [[P0 P1] C] (H0 & H1 & HC) Hs.
  exact (b64_passes_through_complete_on_grid P0 P1 C H0 H1 HC Hs).
Qed.

Theorem pt_exact_on_tight : exact_on tight_dom pt_spec pt_comp.
Proof.
  intros [[P0 P1] C] (H0 & H1 & HC). simpl.
  rewrite (b64_passes_through_grid_exact P0 P1 C H0 H1 HC). tauto.
Qed.

Theorem pt_not_under_globally : ~ under_on (fun _ => True) pt_spec pt_comp.
Proof.
  intro H.
  destruct b64_passes_through_compute_unsound as (P0 & P1 & C & Hc & Hs).
  pose proof (H (P0, P1, C) I Hc) as Hbad. simpl in Hbad.
  rewrite Hs in Hbad. discriminate.
Qed.
