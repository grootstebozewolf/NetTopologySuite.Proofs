(* ============================================================================
   NetTopologySuite.Proofs.NurbsKnotSpans
   ----------------------------------------------------------------------------
   Issue #565 / claimId 508-g: knot-vector carrier + induction over spans.

   NurbsGeneralLength.nurbs_knot_span_additive is already the two-window
   special case (curve_length_additive on one curve).  This file does NOT
   remint that identifier.  It adds:

     1. knot_vector  = a weakly increasing chain of knots
     2. span_lengths = one is_curve_length per consecutive knot window
     3. nurbs_spans_additive : induction on the interior-knot list
        (curve_length_additive at each cons; no new analysis)

   The two-golden-quarter half-circle instance (π/2 + π/2 = π) lives in
   NurbsConicExact.v — Category C through 508-a atan.  This file stays
   3-axiom.

   Not Cox-de Boor multi-span evaluation.  Oracle N stays single-span.
   Not a CurveSegment / Exact* zoo type.  Does not steal 508-e / 508-h.
   Does not retire epic 508 (that is #566).

   WITNESS topic: metric · claimId: 508-g · witness: 508-g-nurbs-spans
   macro: metric
   lane: proofs
   issue: #565 / #508

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance CurveLength.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Knot-vector carrier and span-length induction.                             *)
(* -------------------------------------------------------------------------- *)

(* A knot vector is a weakly increasing chain.  Empty interior knots is
   a single span [k0, kend].  Repeated knots contribute dist x x = 0. *)
Definition knot_vector (k0 : R) (ks : list R) (kend : R) : Prop :=
  chain k0 ks kend.

(* One metric length per consecutive knot window.  Length-list shape
   must match: n interior knots need n+1 lengths. *)
Fixpoint span_lengths (g : Curve) (k0 : R) (ks : list R) (kend : R)
                      (Ls : list R) : Prop :=
  match ks, Ls with
  | [], [L] => is_curve_length g k0 kend L
  | k :: ks', L :: Ls' =>
      is_curve_length g k0 k L /\ span_lengths g k ks' kend Ls'
  | _, _ => False
  end.

Definition list_sum (xs : list R) : R := fold_right Rplus 0 xs.

(* WITNESS {"claimId":"508-g","witness":"508-g-nurbs-spans","topic":"metric","lemma":"nurbs_spans_additive","title":"Metric length on a knot vector is the sum of the per-span lengths","file":"theories/NurbsKnotSpans.v","board":"#565"} *)

Theorem nurbs_spans_additive :
  forall (g : Curve) k0 ks kend Ls,
    knot_vector k0 ks kend ->
    span_lengths g k0 ks kend Ls ->
    is_curve_length g k0 kend (list_sum Ls).
Proof.
  intros g k0 ks kend Ls.
  revert k0 Ls.
  induction ks as [|k ks' IH]; intros k0 Ls Hkv Hsp.
  - destruct Ls as [|L Ls']; [simpl in Hsp; contradiction Hsp |].
    destruct Ls' as [|L2 rest]; [| simpl in Hsp; contradiction Hsp].
    unfold list_sum. simpl.
    replace (L + 0) with L by ring.
    exact Hsp.
  - destruct Ls as [|L Ls']; [simpl in Hsp; contradiction Hsp |].
    destruct Hkv as [Hk0k Htail].
    destruct Hsp as [Hspan0 Hrest].
    unfold list_sum. simpl.
    apply curve_length_additive with (b := k).
    + exact Hk0k.
    + exact (chain_le ks' k kend Htail).
    + exact Hspan0.
    + exact (IH k Ls' Htail Hrest).
Qed.

Print Assumptions nurbs_spans_additive.

(* The two-window special case is already
   NurbsGeneralLength.nurbs_knot_span_additive
   (= CurveLength.curve_length_additive).  This file does not remint it.
   The golden half-circle instance is NurbsConicExact.golden_half_circle_length. *)
