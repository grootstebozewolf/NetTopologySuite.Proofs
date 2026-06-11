(* ============================================================================
   NetTopologySuite.Proofs.JCTTautClearance
   ----------------------------------------------------------------------------
   ESCAPE DESCENT, rung 4b-1: the TAUT bridge -- the simplicity notion the
   boundary walk consumes, and the three lemmas that turn it into corridor
   clearances.

   The corpus's `ring_simple` forbids only PROPER (interior-interior)
   crossings; it deliberately admits T-touches and vertex-touches (the
   self-touching figure-8 is `ring_simple`, see Overlay.v).  A corridor at
   any positive offset is genuinely blocked by a T-touch on the carrier's
   west side, so the walk needs the classical notion:

     `ring_taut` : any meeting point of two ring edges is a shared ENDPOINT
     of both -- with the conclusion weakened by the pointwise-equal-edges
     escape hatch `(fst e = fst f /\ snd e = snd f)`, which makes the
     statement quantify over ALL pairs (edge equality over real coordinates
     is undecidable, so the carrier case is absorbed semantically instead
     of split off syntactically).  `ring_taut_implies_simple` confirms taut
     is a strengthening of the corpus predicate.

   Its consumer (`taut_no_line_touch`): inside a height window STRICTLY
   interior to the carrier's span, the carrier's line and its segment
   coincide -- so any edge meeting the LINE at a window height either is
   the carrier (pointwise) or violates tautness.  This is what orients
   every clearance sign in rung 4b-2's case tree.

   Supporting kit: `affine_root` (the constructive IVT for affine
   functions: an explicit root formula when the endpoint values have
   opposite signs -- no completeness needed) and `clip_ordered_asc`/`_desc`
   (the rung-3 clip points are ordered, lie in [0,1], and their heights
   stay inside the window).

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Arith Lia.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam.
From NTS.Proofs Require Import PointInRingCorrect JCT JCT_OnEdgeCounterexample.
From NTS.Proofs Require Import ConvexOffringSeam JCTParityTransport.
From NTS.Proofs Require Import JCTHalfOpenParity JCTGenericStability JCTLevelJump.
From NTS.Proofs Require Import JCTTrappedHalf JCTSeamAssembly JCTEscapeDescent.
From NTS.Proofs Require Import JCTEastApproach JCTCorridor JCTWalkKit JCTWalkStep.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §1  Tautness: edges meet only at shared endpoints.
   --------------------------------------------------------------------------- *)

Definition ring_taut (r : Ring) : Prop :=
  forall e f : Edge,
    In e (ring_edges r) -> In f (ring_edges r) ->
    forall t s : R,
      0 <= t <= 1 -> 0 <= s <= 1 ->
      (1 - t) * px (fst e) + t * px (snd e)
        = (1 - s) * px (fst f) + s * px (snd f) ->
      (1 - t) * py (fst e) + t * py (snd e)
        = (1 - s) * py (fst f) + s * py (snd f) ->
      (t = 0 \/ t = 1) \/ (fst e = fst f /\ snd e = snd f).

(* Tautness strengthens the corpus predicate: a PROPER crossing is an
   interior-interior meeting of distinct edges. *)
Lemma ring_taut_implies_simple : forall (r : Ring),
  ring_taut r -> ring_simple r.
Proof.
  intros r Htaut e1 e2 Hin1 Hin2 Hne [t [s [Ht [Hs [Hx Hy]]]]].
  destruct (Htaut e1 e2 Hin1 Hin2 t s
              ltac:(lra) ltac:(lra) Hx Hy) as [[H | H] | [Hf Hs']].
  - lra.
  - lra.
  - apply Hne. destruct e1 as [a1 b1]; destruct e2 as [a2 b2].
    cbn [fst snd] in *. rewrite Hf, Hs'. reflexivity.
Qed.

(* ---------------------------------------------------------------------------
   §2  The taut consumer: no line-touch inside a span-interior window.
   --------------------------------------------------------------------------- *)

Theorem taut_no_line_touch : forall (r : Ring) (e1 f : Edge) (ylo yhi : R),
  ring_taut r ->
  In e1 (ring_edges r) -> In f (ring_edges r) ->
  py (fst e1) <> py (snd e1) ->
  ((py (fst e1) < ylo /\ yhi < py (snd e1)) \/
   (py (snd e1) < ylo /\ yhi < py (fst e1))) ->
  forall (s y : R),
    0 <= s <= 1 ->
    ylo <= y <= yhi ->
    y = (1 - s) * py (fst f) + s * py (snd f) ->
    edge_x_at e1 y = (1 - s) * px (fst f) + s * px (snd f) ->
    fst e1 = fst f /\ snd e1 = snd f.
Proof.
  intros r e1 f ylo yhi Htaut Hin1 Hinf Hnh Hspan s y Hs Hw Hyf Hxf.
  set (t := (y - py (fst e1)) / (py (snd e1) - py (fst e1))).
  assert (Hd : py (snd e1) - py (fst e1) <> 0) by lra.
  (* t is strictly interior: the window is strictly inside the span *)
  assert (Htint : 0 < t < 1).
  { unfold t. destruct Hspan as [[H1 H2] | [H1 H2]].
    - split.
      + apply Rmult_lt_reg_r with (py (snd e1) - py (fst e1)); [ lra | ].
        replace ((y - py (fst e1)) / (py (snd e1) - py (fst e1))
                   * (py (snd e1) - py (fst e1)))
          with (y - py (fst e1)) by (field; lra). lra.
      + apply Rmult_lt_reg_r with (py (snd e1) - py (fst e1)); [ lra | ].
        replace ((y - py (fst e1)) / (py (snd e1) - py (fst e1))
                   * (py (snd e1) - py (fst e1)))
          with (y - py (fst e1)) by (field; lra). lra.
    - split.
      + apply Rmult_lt_reg_r with (py (fst e1) - py (snd e1)); [ lra | ].
        replace ((y - py (fst e1)) / (py (snd e1) - py (fst e1))
                   * (py (fst e1) - py (snd e1)))
          with (py (fst e1) - y) by (field; lra). lra.
      + apply Rmult_lt_reg_r with (py (fst e1) - py (snd e1)); [ lra | ].
        replace ((y - py (fst e1)) / (py (snd e1) - py (fst e1))
                   * (py (fst e1) - py (snd e1)))
          with (py (fst e1) - y) by (field; lra). lra. }
  (* e1 at parameter t sits exactly at (edge_x_at e1 y, y) *)
  assert (Hyt : (1 - t) * py (fst e1) + t * py (snd e1) = y)
    by (unfold t; field; lra).
  assert (Hxt : (1 - t) * px (fst e1) + t * px (snd e1) = edge_x_at e1 y).
  { rewrite <- Hyt. rewrite (on_carrier_x e1 t Hnh). reflexivity. }
  destruct (Htaut e1 f Hin1 Hinf t s ltac:(lra) Hs
              ltac:(rewrite Hxt, Hxf; reflexivity)
              ltac:(rewrite Hyt, <- Hyf; reflexivity))
    as [[H | H] | He]; [ lra | lra | exact He ].
Qed.

(* ---------------------------------------------------------------------------
   §3  The constructive affine IVT: an explicit root.
   --------------------------------------------------------------------------- *)

Lemma affine_root : forall (A B s0 s1 : R),
  s0 <= s1 ->
  (A * s0 + B) * (A * s1 + B) <= 0 ->
  exists s : R, s0 <= s <= s1 /\ A * s + B = 0.
Proof.
  intros A B s0 s1 Hle Hsign.
  destruct (Req_dec (A * s0 + B) 0) as [H0 | H0].
  { exists s0. split; [ lra | exact H0 ]. }
  destruct (Req_dec (A * s1 + B) 0) as [H1 | H1].
  { exists s1. split; [ lra | exact H1 ]. }
  (* strict opposite signs: A <> 0 and the explicit root lies inside *)
  assert (HA : A <> 0) by (intro Hz; rewrite Hz in *; nra).
  exists (- B / A).
  assert (Hroot : A * (- B / A) + B = 0) by (field; exact HA).
  split; [ | exact Hroot ].
  assert (Hlink : A * (- B / A) = - B) by (field; exact HA).
  split.
  - destruct (Rle_or_lt s0 (- B / A)) as [Hok | Hbad]; [ exact Hok | ].
    exfalso.
    destruct (Rtotal_order A 0) as [Hneg | [Hz | Hpos]]; [ | lra | ].
    + assert (Hs0 : A * s0 + B < 0) by nra.
      assert (Hmono : A * s1 <= A * s0) by nra.
      nra.
    + assert (Hs0 : 0 < A * s0 + B) by nra.
      assert (Hmono : A * s0 <= A * s1) by nra.
      nra.
  - destruct (Rle_or_lt (- B / A) s1) as [Hok | Hbad]; [ exact Hok | ].
    exfalso.
    destruct (Rtotal_order A 0) as [Hneg | [Hz | Hpos]]; [ | lra | ].
    + assert (Hs1 : 0 < A * s1 + B) by nra.
      assert (Hmono : A * s0 >= A * s1) by nra.
      nra.
    + assert (Hs1 : A * s1 + B < 0) by nra.
      assert (Hmono : A * s0 <= A * s1) by nra.
      nra.
Qed.

(* ---------------------------------------------------------------------------
   §4  Clip-point well-formedness.
   --------------------------------------------------------------------------- *)

Lemma clip_ordered_asc : forall (f : Edge) (ylo yhi : R),
  py (fst f) < py (snd f) ->
  ylo <= yhi ->
  py (fst f) <= yhi ->
  ylo <= py (snd f) ->
  let d := py (snd f) - py (fst f) in
  let s0 := Rmax 0 ((ylo - py (fst f)) / d) in
  let s1 := Rmin 1 ((yhi - py (fst f)) / d) in
  0 <= s0 /\ s0 <= s1 /\ s1 <= 1 /\
  ylo <= (1 - s0) * py (fst f) + s0 * py (snd f) /\
  (1 - s0) * py (fst f) + s0 * py (snd f) <= yhi /\
  ylo <= (1 - s1) * py (fst f) + s1 * py (snd f) /\
  (1 - s1) * py (fst f) + s1 * py (snd f) <= yhi.
Proof.
  intros f ylo yhi Hasc Hle Hfa Hfb d s0 s1.
  assert (Hd : 0 < d) by (unfold d; lra).
  assert (Hdef : d = py (snd f) - py (fst f)) by reflexivity.
  assert (HA : (ylo - py (fst f)) / d * d = ylo - py (fst f))
    by (field; lra).
  assert (HB : (yhi - py (fst f)) / d * d = yhi - py (fst f))
    by (field; lra).
  assert (HAle : (ylo - py (fst f)) / d <= (yhi - py (fst f)) / d)
    by (apply Rmult_le_reg_r with d; [ exact Hd | ]; lra).
  assert (HA1 : (ylo - py (fst f)) / d <= 1)
    by (apply Rmult_le_reg_r with d; [ exact Hd | ]; lra).
  assert (HB0 : 0 <= (yhi - py (fst f)) / d)
    by (apply Rmult_le_reg_r with d; [ exact Hd | ]; lra).
  assert (Hs00 : 0 <= s0) by (unfold s0; apply Rmax_l).
  assert (Hs11 : s1 <= 1) by (unfold s1; apply Rmin_l).
  assert (Hs01 : s0 <= s1).
  { unfold s0, s1. apply Rmax_lub.
    - apply Rmin_glb; lra.
    - apply Rmin_glb; lra. }
  split; [ exact Hs00 | ]. split; [ exact Hs01 | ]. split; [ exact Hs11 | ].
  assert (Hh0 : (1 - s0) * py (fst f) + s0 * py (snd f)
                  = py (fst f) + s0 * d) by (unfold d; ring).
  assert (Hh1 : (1 - s1) * py (fst f) + s1 * py (snd f)
                  = py (fst f) + s1 * d) by (unfold d; ring).
  rewrite Hh0, Hh1.
  assert (Hs0lo : ylo - py (fst f) <= s0 * d).
  { unfold s0. pose proof (Rmax_r 0 ((ylo - py (fst f)) / d)).
    assert (((ylo - py (fst f)) / d) * d <= Rmax 0 ((ylo - py (fst f)) / d) * d)
      by (apply Rmult_le_compat_r; lra).
    lra. }
  assert (Hs1hi : s1 * d <= yhi - py (fst f)).
  { unfold s1. pose proof (Rmin_r 1 ((yhi - py (fst f)) / d)).
    assert (Rmin 1 ((yhi - py (fst f)) / d) * d <= ((yhi - py (fst f)) / d) * d)
      by (apply Rmult_le_compat_r; lra).
    lra. }
  assert (Hs0s1d : s0 * d <= s1 * d)
    by (apply Rmult_le_compat_r; lra).
  split; [ lra | ]. split; [ lra | ]. split; lra.
Qed.

Lemma clip_ordered_desc : forall (f : Edge) (ylo yhi : R),
  py (snd f) < py (fst f) ->
  ylo <= yhi ->
  py (snd f) <= yhi ->
  ylo <= py (fst f) ->
  let d := py (fst f) - py (snd f) in
  let s0 := Rmax 0 ((py (fst f) - yhi) / d) in
  let s1 := Rmin 1 ((py (fst f) - ylo) / d) in
  0 <= s0 /\ s0 <= s1 /\ s1 <= 1 /\
  ylo <= (1 - s0) * py (fst f) + s0 * py (snd f) /\
  (1 - s0) * py (fst f) + s0 * py (snd f) <= yhi /\
  ylo <= (1 - s1) * py (fst f) + s1 * py (snd f) /\
  (1 - s1) * py (fst f) + s1 * py (snd f) <= yhi.
Proof.
  intros f ylo yhi Hdesc Hle Hfb Hfa d s0 s1.
  assert (Hd : 0 < d) by (unfold d; lra).
  assert (Hdef : d = py (fst f) - py (snd f)) by reflexivity.
  assert (HAle : (py (fst f) - yhi) / d <= (py (fst f) - ylo) / d)
    by (apply Rmult_le_reg_r with d; [ exact Hd | ];
        replace ((py (fst f) - yhi) / d * d) with (py (fst f) - yhi)
          by (field; lra);
        replace ((py (fst f) - ylo) / d * d) with (py (fst f) - ylo)
          by (field; lra);
        lra).
  assert (HA1 : (py (fst f) - yhi) / d <= 1)
    by (apply Rmult_le_reg_r with d; [ exact Hd | ];
        replace ((py (fst f) - yhi) / d * d) with (py (fst f) - yhi)
          by (field; lra);
        lra).
  assert (HB0 : 0 <= (py (fst f) - ylo) / d)
    by (apply Rmult_le_reg_r with d; [ exact Hd | ];
        replace ((py (fst f) - ylo) / d * d) with (py (fst f) - ylo)
          by (field; lra);
        lra).
  assert (Hs00 : 0 <= s0) by (unfold s0; apply Rmax_l).
  assert (Hs11 : s1 <= 1) by (unfold s1; apply Rmin_l).
  assert (Hs01 : s0 <= s1).
  { unfold s0, s1. apply Rmax_lub.
    - apply Rmin_glb; lra.
    - apply Rmin_glb; lra. }
  split; [ exact Hs00 | ]. split; [ exact Hs01 | ]. split; [ exact Hs11 | ].
  assert (Hh0 : (1 - s0) * py (fst f) + s0 * py (snd f)
                  = py (fst f) - s0 * d) by (unfold d; ring).
  assert (Hh1 : (1 - s1) * py (fst f) + s1 * py (snd f)
                  = py (fst f) - s1 * d) by (unfold d; ring).
  rewrite Hh0, Hh1.
  assert (Hs0hi : py (fst f) - yhi <= s0 * d).
  { unfold s0. pose proof (Rmax_r 0 ((py (fst f) - yhi) / d)).
    assert (((py (fst f) - yhi) / d) * d
              <= Rmax 0 ((py (fst f) - yhi) / d) * d)
      by (apply Rmult_le_compat_r; lra).
    assert ((py (fst f) - yhi) / d * d = py (fst f) - yhi) by (field; lra).
    lra. }
  assert (Hs1lo : s1 * d <= py (fst f) - ylo).
  { unfold s1. pose proof (Rmin_r 1 ((py (fst f) - ylo) / d)).
    assert (Rmin 1 ((py (fst f) - ylo) / d) * d
              <= ((py (fst f) - ylo) / d) * d)
      by (apply Rmult_le_compat_r; lra).
    assert ((py (fst f) - ylo) / d * d = py (fst f) - ylo) by (field; lra).
    lra. }
  assert (Hs0s1d : s0 * d <= s1 * d)
    by (apply Rmult_le_compat_r; lra).
  split; [ lra | ]. split; [ lra | ]. split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions ring_taut_implies_simple.
Print Assumptions taut_no_line_touch.
Print Assumptions affine_root.
Print Assumptions clip_ordered_asc.
