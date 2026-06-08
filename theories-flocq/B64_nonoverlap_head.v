(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_nonoverlap_head
   ----------------------------------------------------------------------------
   Shewchuk Theorem 13, obligation O1 core (docs/shewchuk-thm13-pathb-plan.md):
   the two pure `compress` / `nonoverlap_strict` list lemmas that a pathB step's
   clause-(a) preservation composes from.

   A pathB cascade step does two things to the output chain `carry :: rev output`:
     (1) appends a zero low part (`snd (b64_TwoSum ..) = 0`), and
     (2) replaces the head `carry` by the exact cancellation residue `carry'`.

   These lemmas handle each, independently of the cascade machinery:

     - `nonoverlap_shewchuk_cons_zero` : a `B2R = 0` element in second position
        is invisible to `nonoverlap_shewchuk` (it is dropped by `compress`).
        Handles (1).
     - `nonoverlap_shewchuk_head_replace` : the head may be replaced by any `a'`
        that is either zero or dominates (`strict_succ_b64`) the first surviving
        output component.  Handles (2); its dominance precondition is exactly
        what `residue_ge_half_ulp` (obligation O1', PR #136) discharges for a
        nonzero pathB residue.

   Pure list reasoning over `compress` / `nonoverlap_strict`; no cascade state,
   no Pff, no deferred-headline dependence.  Qed-closed.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List.
From Flocq Require Import IEEE754.Binary Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_lib
                                     B64_Expansion B64_Expansion_Shewchuk.
Import ListNotations.
Local Open Scope R_scope.

(* A `B2R = 0` element in second position does not change `compress`. *)
Lemma compress_cons_zero :
  forall (a z : binary64) (L : list binary64),
    Binary.B2R prec emax z = 0 ->
    compress (a :: z :: L) = compress (a :: L).
Proof.
  intros a z L Hz. cbn [compress].
  rewrite (Rcompare_Eq (Binary.B2R prec emax z) 0 Hz).
  reflexivity.
Qed.

(* Hence such an element is invisible to nonoverlap_shewchuk. *)
Lemma nonoverlap_shewchuk_cons_zero :
  forall (a z : binary64) (L : list binary64),
    Binary.B2R prec emax z = 0 ->
    nonoverlap_shewchuk (a :: z :: L) <-> nonoverlap_shewchuk (a :: L).
Proof.
  intros a z L Hz. unfold nonoverlap_shewchuk.
  rewrite (compress_cons_zero a z L Hz). reflexivity.
Qed.

(* `compress` drops a zero element appended after the head cell. *)
Lemma compress_app_zero :
  forall (L : list binary64) (err : binary64),
    Binary.B2R prec emax err = 0 ->
    compress (L ++ [err]) = compress L.
Proof.
  induction L as [| x L' IH]; intros err Hz.
  - cbn [app compress]. rewrite (Rcompare_Eq _ _ Hz). reflexivity.
  - cbn [app compress].
    destruct (Rcompare (Binary.B2R prec emax x) 0) eqn:Hx.
    + exact (IH err Hz).
    + f_equal. exact (IH err Hz).
    + f_equal. exact (IH err Hz).
Qed.

Lemma compress_head_app_zero :
  forall (a err : binary64) (hs : list binary64),
    Binary.B2R prec emax err = 0 ->
    compress (a :: rev hs ++ [err]) = compress (a :: rev hs).
Proof.
  intros a err hs Hz.
  cbn [compress].
  destruct (Rcompare (Binary.B2R prec emax a) 0) eqn:Ha.
  - exact (compress_app_zero (rev hs) err Hz).
  - rewrite (compress_app_zero (rev hs) err Hz). reflexivity.
  - rewrite (compress_app_zero (rev hs) err Hz). reflexivity.
Qed.

(* Appending a zero low part after `rev hs` is invisible on a `q :: _` chain. *)
Lemma nonoverlap_shewchuk_tail_app_zero :
  forall (q err : binary64) (hs : list binary64),
    Binary.B2R prec emax err = 0 ->
    nonoverlap_shewchuk (q :: rev hs) ->
    nonoverlap_shewchuk (q :: (rev hs ++ [err])).
Proof.
  intros q err hs Hz Hout.
  unfold nonoverlap_shewchuk in *.
  rewrite (compress_head_app_zero q err hs Hz). exact Hout.
Qed.

(* The head of a nonoverlap_shewchuk chain may be replaced by any `a'` that is
   zero (compressed away) or dominates the first surviving component. *)
Lemma nonoverlap_shewchuk_head_replace :
  forall (a a' : binary64) (L : list binary64),
    nonoverlap_shewchuk (a :: L) ->
    ( Binary.B2R prec emax a' = 0 \/
      match compress L with
      | nil => True
      | h :: _ => strict_succ_b64 a' h
      end ) ->
    nonoverlap_shewchuk (a' :: L).
Proof.
  intros a a' L Hold Hdom.
  unfold nonoverlap_shewchuk in *.
  cbn [compress] in Hold |- *.
  (* Tail fact: nonoverlap_strict (compress L) holds regardless of a. *)
  assert (Htail : nonoverlap_strict (compress L)).
  { destruct (Rcompare (Binary.B2R prec emax a) 0) eqn:Ha.
    - exact Hold.
    - destruct (compress L) as [|h rest]; cbn [nonoverlap_strict] in Hold |- *.
      + exact I.
      + destruct Hold as [_ Ht]. exact Ht.
    - destruct (compress L) as [|h rest]; cbn [nonoverlap_strict] in Hold |- *.
      + exact I.
      + destruct Hold as [_ Ht]. exact Ht. }
  (* Now case on whether a' is compressed away. *)
  destruct (Rcompare (Binary.B2R prec emax a') 0) eqn:Ha'.
  - (* a' = 0: a' :: L compresses to compress L. *)
    exact Htail.
  - (* a' <> 0: need nonoverlap_strict (a' :: compress L). *)
    destruct (compress L) as [|h rest] eqn:HcL.
    + cbn [nonoverlap_strict]. exact I.
    + cbn [nonoverlap_strict]. split.
      * destruct Hdom as [Hz | Hd].
        -- rewrite (Rcompare_Eq _ _ Hz) in Ha'. discriminate.
        -- exact Hd.
      * exact Htail.
  - (* a' <> 0 (Gt): identical to Lt. *)
    destruct (compress L) as [|h rest] eqn:HcL.
    + cbn [nonoverlap_strict]. exact I.
    + cbn [nonoverlap_strict]. split.
      * destruct Hdom as [Hz | Hd].
        -- rewrite (Rcompare_Eq _ _ Hz) in Ha'. discriminate.
        -- exact Hd.
      * exact Htail.
Qed.

(* The first surviving compressed component is nonzero. *)
Lemma compress_head_nonzero :
  forall (L : list binary64) (h : binary64) (ts : list binary64),
    compress L = h :: ts ->
    Binary.B2R prec emax h <> 0.
Proof.
  induction L as [|a L' IH]; intros h ts Hc.
  - discriminate.
  - cbn [compress] in Hc.
    destruct (Rcompare (Binary.B2R prec emax a) 0) eqn:Ha.
    + eapply IH. exact Hc.
    + pose proof (f_equal (map (Binary.B2R prec emax)) Hc) as Hmap.
      cbn [map] in Hmap.
      injection Hmap as HB2R _.
      intro Hz. rewrite <- HB2R in Hz.
      assert (Heq : Rcompare (Binary.B2R prec emax a) 0 = Eq).
      { rewrite Hz. apply Rcompare_Eq. reflexivity. }
      rewrite Heq in Ha. discriminate.
    + pose proof (f_equal (map (Binary.B2R prec emax)) Hc) as Hmap.
      cbn [map] in Hmap.
      injection Hmap as HB2R _.
      intro Hz. rewrite <- HB2R in Hz.
      assert (Heq : Rcompare (Binary.B2R prec emax a) 0 = Eq).
      { rewrite Hz. apply Rcompare_Eq. reflexivity. }
      rewrite Heq in Ha. discriminate.
Qed.

(* Extract the half-ulp bound on the first surviving output component from
   clause (a) `nonoverlap_shewchuk (q :: rev hs)`. *)
Lemma nonoverlap_output_first_strict_succ :
  forall (q : binary64) (hs : list binary64) (h : binary64) (ts : list binary64),
    nonoverlap_shewchuk (q :: rev hs) ->
    compress (rev hs) = h :: ts ->
    Binary.B2R prec emax q <> 0 ->
    Binary.B2R prec emax h <> 0 ->
    strict_succ_b64 q h.
Proof.
  intros q hs h ts Hout Hch Hq0 Hh0.
  unfold nonoverlap_shewchuk in Hout.
  assert (Hcmp : compress (q :: rev hs) = q :: h :: ts).
  { cbn [compress].
    destruct (Rcompare (Binary.B2R prec emax q) 0) eqn:Hq.
    - apply Rcompare_Eq_inv in Hq. contradiction.
    - rewrite Hch. reflexivity.
    - rewrite Hch. reflexivity. }
  rewrite Hcmp in Hout.
  destruct (Rcompare (Binary.B2R prec emax h) 0) eqn:Hh.
  - apply Rcompare_Eq_inv in Hh. contradiction.
  - cbn [nonoverlap_strict] in Hout. destruct Hout as [Hss _]. exact Hss.
  - cbn [nonoverlap_strict] in Hout. destruct Hout as [Hss _]. exact Hss.
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions nonoverlap_shewchuk_cons_zero.
Print Assumptions nonoverlap_shewchuk_head_replace.
Print Assumptions nonoverlap_output_first_strict_succ.
