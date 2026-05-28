(* ============================================================================
   NetTopologySuite.Proofs.Flocq.HobbyTheorem_b64
   ----------------------------------------------------------------------------
   Hobby (1999) Theorem 4.1 -- the headline correctness statement of snap
   rounding -- placed in the same epistemic position as Shewchuk Theorem 13
   in this corpus: definitions and the conditional theorem are Qed-closed;
   the two supporting lemmas (4.2 monotone-coordinate, 4.3 piecewise-linear
   ordering) are Admitted with registered deferred-proof entries.

   Paper: J. D. Hobby, "Practical segment intersection with finite precision
   output," Computational Geometry: Theory and Applications 13(4):199-214,
   1999.  Section 4.

   See docs/hobby-theorem-proof-structure.md for the proof structure mapped
   to Coq obligations, the gap analysis (§6), and the resumption
   checklist (§7).

   File placement.  Hobby's `snap_round` (the discretisation operator D_T) is
   `snap_round` from HotPixel_b64.v -- Flocq-pinned -- so this file lives in
   the Flocq layer.  All the surrounding predicates (proper crossing,
   fully-intersected, the snap region) are pure-R; they live here for
   cohesion, not because they need Flocq.

   Audit footprint.  Like the other snap-rounding files (HotPixel_b64.v,
   SnapRounding_b64.v, TopologicalCorrectness_b64.v), `snap_round`'s closure
   pulls `Classical_Prop.classic` through Flocq's `round` / `round_mode`.
   This file is listed in docs/audit-exceptions.txt for that lineage.  Two
   Admitteds, both registered in docs/admitted-deferred-proofs.txt.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.

From NTS.Proofs        Require Import Distance HotPixel.
From NTS.Proofs.Flocq  Require Import Validate_binary64.
From NTS.Proofs.Flocq  Require Import HotPixel_b64.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1 The Hobby Theorem 4.1 definitions.                                      *)
(* -------------------------------------------------------------------------- *)

(* Two segments [P0,P1] and [Q0,Q1] intersect PROPERLY when they cross at an
   interior point: parameters t and s both strictly in (0,1) yield the same
   point.  This is Hobby's notion of "proper crossing" in §4. *)
Definition segments_intersect_properly (P0 P1 Q0 Q1 : Point) : Prop :=
  exists t s : R,
    0 < t < 1 /\ 0 < s < 1 /\
    (1 - t) * px P0 + t * px P1 =
    (1 - s) * px Q0 + s * px Q1 /\
    (1 - t) * py P0 + t * py P1 =
    (1 - s) * py Q0 + s * py Q1.

(* Two segments meet only at endpoints (or not at all): either there is no
   proper crossing, or they share an endpoint.  Hobby's "intersect only at
   endpoints" condition. *)
Definition segments_intersect_only_at_endpoints (s1 s2 : Point * Point) : Prop :=
  let '(P0, P1) := s1 in
  let '(Q0, Q1) := s2 in
  ~ segments_intersect_properly P0 P1 Q0 Q1 \/
  (P0 = Q0 \/ P0 = Q1 \/ P1 = Q0 \/ P1 = Q1).

(* An arrangement is FULLY INTERSECTED when distinct segments meet only at
   endpoints.  This is the input invariant Hobby's Theorem 4.1 requires. *)
Definition fully_intersected (segs : list (Point * Point)) : Prop :=
  forall s1 s2 : Point * Point,
    In s1 segs -> In s2 segs -> s1 <> s2 ->
    segments_intersect_only_at_endpoints s1 s2.

(* The discretisation operator D_T (Hobby §4): snap-round every segment
   endpoint.  `fst` / `snd` rather than a pattern match keeps the map term
   beta-reducible without an explicit `destruct` in proofs that consume it. *)
Definition snap_round_segments (segs : list (Point * Point)) : list (Point * Point) :=
  List.map (fun s => (snap_round (fst s) 1, snap_round (snd s) 1)) segs.

(* Snap region for a segment (Hobby 1999 p.210, written R^- in the
   paper).  The set of integer-grid points `p` such that some point
   `q = segment_point P0 P1 t` lies within R^- of `p`:

       R^- = {(x, y) | -1/2 < x <= 1/2, -1/2 < y <= 1/2}

   i.e., the half-open unit square with the bottom and left edges
   OPEN and the top and right edges CLOSED.  This is the OPPOSITE
   half-open convention to `in_hot_pixel`'s R = [-1/2, 1/2) x
   [-1/2, 1/2) -- Hobby's R^- is the "negated" pixel tile, with the
   complementary boundary inclusion that makes Lemma 4.3's
   piecewise-linear argument compose cleanly.

   Equivalently, this is the Minkowski sum of the segment with R^-:
   `p in segment(P0,P1) + R^-` constrained to integer coordinates.
   That formulation is strip-shaped (a thin neighbourhood of the
   segment), not the closed-staircase / lower-left-quadrant that the
   pre-fix rendering produced.

   Used in Lemma 4.2's monotone-coordinate statement.  See
   docs/hobby-lemma-4-2-session-1-outcome.md for the design history
   (counterexample on segment (0,0)-(2,2) that drove this fix). *)
Definition in_snap_region (P0 P1 p : Point) : Prop :=
  (exists nx ny : Z, px p = IZR nx /\ py p = IZR ny) /\
  exists t : R, 0 <= t <= 1 /\
    let q := segment_point P0 P1 t in
    - (1/2) < px p - px q <= 1/2 /\
    - (1/2) < py p - py q <= 1/2.

(* -------------------------------------------------------------------------- *)
(* §2 Hobby Lemma 4.2 -- monotone coordinate.                                 *)
(* Admitted; registered in docs/admitted-deferred-proofs.txt.                 *)
(* Proof sketch: docs/hobby-theorem-proof-structure.md §3.                    *)
(* -------------------------------------------------------------------------- *)

(* For any non-degenerate segment there is a diagonal direction (1, +/-1)
   such that distinct integer points in the segment's snap region have
   distinct linear projections.  Hobby chooses alpha_y by the sign of
   the slope product (px P1 - px P0) * (py P1 - py P0):
     non-negative product (slope >= 0, horizontal, or vertical):
       alpha_y = +1.
     negative product (slope < 0): alpha_y = -1.
   The proof: from f(p) = f(q) with p <> q, integer-injectivity of IZR
   forces a same-sum or same-difference relation on the integer coords.
   WLOG one coord differs by k >= 1, the other by -k or +k accordingly.
   The R^- strip bounds (half-open with strict lower / closed upper)
   then force px qp > px qq and py qp <> py qq with specific signs;
   colocation on the segment then forces the segment-direction product
   sign to be the OPPOSITE of the chosen-alpha_y case, contradicting
   the case assumption.

   The half-open R^- convention is load-bearing: the strict lower
   `-1/2 < ...` (rather than `<=`) is what forces strict inequalities
   in `px qp - px qq` and `py qp - py qq` and avoids boundary collisions
   (e.g., (1,0) and (0,1) for segment (0,0)-(1,1) are EXCLUDED from
   R^- by this strict bound, even though they sit at the half-open
   boundary of the natural pixel tiles). *)
Lemma hobby_lemma_4_2 :
  forall (P0 P1 : Point),
    P0 <> P1 ->
    exists alpha_y : R,
      (alpha_y = 1 \/ alpha_y = -1) /\
      forall p q : Point,
        in_snap_region P0 P1 p ->
        in_snap_region P0 P1 q ->
        p <> q ->
        px p + alpha_y * py p <> px q + alpha_y * py q.
Proof.
  intros P0 P1 Hne.
  destruct (Rle_or_lt 0 ((px P1 - px P0) * (py P1 - py P0))) as [Hprod | Hprod].
  - (* Product >= 0: choose alpha_y = +1 *)
    exists 1. split.
    { left. reflexivity. }
    intros p q Hp Hq Hpq Heq.
    destruct Hp as [[np [mp [Hnp Hmp]]] [tp [Htp [[Hxp_lo Hxp_hi] [Hyp_lo Hyp_hi]]]]].
    destruct Hq as [[nq [mq [Hnq Hmq]]] [tq [Htq [[Hxq_lo Hxq_hi] [Hyq_lo Hyq_hi]]]]].
    unfold segment_point in *. simpl in *.
    (* From Heq (with alpha_y = 1): (px p - px q) + (py p - py q) = 0. *)
    (* Substituting IZR: IZR ((np - nq) + (mp - mq)) = 0. *)
    assert (Hsum_z : ((np - nq) + (mp - mq))%Z = 0%Z).
    { apply eq_IZR_R0.
      rewrite plus_IZR, !minus_IZR, <- Hnp, <- Hnq, <- Hmp, <- Hmq.
      lra. }
    (* Case split: np = nq? *)
    destruct (Z.eq_dec np nq) as [Hnn | Hnn].
    + (* np = nq: then mp = mq from Hsum_z, so px p = px q and py p = py q. *)
      subst nq. assert (Hmm : mp = mq) by lia. subst mq.
      apply Hpq. destruct p as [pxp pyp], q as [pxq pyq]. simpl in *.
      rewrite Hnp, Hmp, Hnq, Hmq. reflexivity.
    + (* np <> nq.  WLOG np > nq via Z trichotomy. *)
      destruct (Ztrichotomy_inf np nq) as [[Hlt | Heq_z] | Hgt].
      * (* np < nq: swap roles of p, q (symmetric case). *)
        (* From Hsum_z and np < nq: mp - mq = -(np - nq) > 0, so mq < mp. *)
        assert (Hk : (nq - np >= 1)%Z) by lia.
        assert (Hk' : (mp - mq >= 1)%Z) by lia.
        (* Strip bounds: px qp ∈ [px p - 1/2, px p + 1/2), etc. *)
        (* With nq - np >= 1: px q >= px p + 1, so px qq > px qp. *)
        (* With mp - mq >= 1: py p >= py q + 1, so py qp > py qq. *)
        (* Segment monotonicity: (px qq - px qp) = (tq - tp)*(px P1 - px P0) > 0. *)
        (*                       (py qp - py qq) = (tp - tq)*(py P1 - py P0) > 0. *)
        (* So sign(tq - tp) = sign(px P1 - px P0), *)
        (*    sign(tp - tq) = sign(py P1 - py P0). *)
        (* These are opposite, so (px P1 - px P0)*(py P1 - py P0) < 0. *)
        (* Contradicts Hprod : (px P1 - px P0)*(py P1 - py P0) >= 0. *)
        assert (Hpx_pq : px p + 1 <= px q).
        { rewrite Hnp, Hnq.
          replace 1 with (IZR 1) by reflexivity.
          rewrite <- plus_IZR.
          apply IZR_le. lia. }
        assert (Hpy_pq : py q + 1 <= py p).
        { rewrite Hmp, Hmq. replace 1 with (IZR 1) by reflexivity.
          rewrite <- plus_IZR. apply IZR_le. lia. }
        (* From strip: px qp < px p + 1/2 (from Hxp_lo: -1/2 < px p - px qp). *)
        (* px qq >= px q - 1/2 (from Hxq_hi: px q - px qq <= 1/2). *)
        (* So px qq - px qp >= (px q - 1/2) - (px p + 1/2) = (px q - px p) - 1 >= 0. *)
        (* But we need STRICT > 0.  *)
        (* Use the strict half: px qp < px p + 1/2 (Hxp_lo is strict). *)
        assert (Hqq_qp_x : (1-tq) * px P0 + tq * px P1 > (1-tp) * px P0 + tp * px P1).
        { lra. }
        assert (Hqp_qq_y : (1-tp) * py P0 + tp * py P1 > (1-tq) * py P0 + tq * py P1).
        { lra. }
        (* Rewrite as (tq - tp) * (px P1 - px P0) > 0. *)
        assert (Hsx : (tq - tp) * (px P1 - px P0) > 0) by nra.
        assert (Hsy : (tp - tq) * (py P1 - py P0) > 0) by nra.
        (* Case split on sign of (tq - tp) to make the nonlinear
           combination tractable for nra. *)
        destruct (Rtotal_order tq tp) as [Htlt | [Hteq | Htgt]].
        -- (* tq < tp: derive sign of each segment difference, then product. *)
           assert (Hpx_neg : px P1 - px P0 < 0) by nra.
           assert (Hpy_pos : py P1 - py P0 > 0) by nra.
           nra.
        -- (* tq = tp: Hsx says 0 > 0, contradiction. *)
           subst tq. lra.
        -- (* tq > tp: symmetric. *)
           assert (Hpx_pos : px P1 - px P0 > 0) by nra.
           assert (Hpy_neg : py P1 - py P0 < 0) by nra.
           nra.
      * (* np = nq -- already handled by the earlier `destruct` case. *)
        exfalso. apply Hnn. exact Heq_z.
      * (* np > nq: the symmetric path of the previous bullet. *)
        assert (Hk : (np - nq >= 1)%Z) by lia.
        assert (Hk' : (mq - mp >= 1)%Z) by lia.
        assert (Hpx_qp : px q + 1 <= px p).
        { rewrite Hnp, Hnq. replace 1 with (IZR 1) by reflexivity.
          rewrite <- plus_IZR. apply IZR_le. lia. }
        assert (Hpy_qp : py p + 1 <= py q).
        { rewrite Hmp, Hmq. replace 1 with (IZR 1) by reflexivity.
          rewrite <- plus_IZR. apply IZR_le. lia. }
        assert (Hqp_qq_x : (1-tp) * px P0 + tp * px P1 > (1-tq) * px P0 + tq * px P1).
        { lra. }
        assert (Hqq_qp_y : (1-tq) * py P0 + tq * py P1 > (1-tp) * py P0 + tp * py P1).
        { lra. }
        assert (Hsx : (tp - tq) * (px P1 - px P0) > 0) by nra.
        assert (Hsy : (tq - tp) * (py P1 - py P0) > 0) by nra.
        destruct (Rtotal_order tp tq) as [Htlt | [Hteq | Htgt]].
        -- assert (Hpx_neg : px P1 - px P0 < 0) by nra.
           assert (Hpy_pos : py P1 - py P0 > 0) by nra.
           nra.
        -- subst tq. lra.
        -- assert (Hpx_pos : px P1 - px P0 > 0) by nra.
           assert (Hpy_neg : py P1 - py P0 < 0) by nra.
           nra.
  - (* Product < 0: choose alpha_y = -1 *)
    exists (-1). split.
    { right. reflexivity. }
    intros p q Hp Hq Hpq Heq.
    destruct Hp as [[np [mp [Hnp Hmp]]] [tp [Htp [[Hxp_lo Hxp_hi] [Hyp_lo Hyp_hi]]]]].
    destruct Hq as [[nq [mq [Hnq Hmq]]] [tq [Htq [[Hxq_lo Hxq_hi] [Hyq_lo Hyq_hi]]]]].
    unfold segment_point in *. simpl in *.
    (* From Heq (alpha_y = -1): (px p - px q) - (py p - py q) = 0. *)
    assert (Hsum_z : ((np - nq) - (mp - mq))%Z = 0%Z).
    { apply eq_IZR_R0.
      rewrite minus_IZR, !minus_IZR, <- Hnp, <- Hnq, <- Hmp, <- Hmq.
      lra. }
    destruct (Z.eq_dec np nq) as [Hnn | Hnn].
    + subst nq. assert (Hmm : mp = mq) by lia. subst mq.
      apply Hpq. destruct p as [pxp pyp], q as [pxq pyq]. simpl in *.
      rewrite Hnp, Hmp, Hnq, Hmq. reflexivity.
    + destruct (Ztrichotomy_inf np nq) as [[Hlt | Heq_z] | Hgt].
      * (* np < nq: same-sign differences. *)
        assert (Hk : (nq - np >= 1)%Z) by lia.
        assert (Hk' : (mq - mp >= 1)%Z) by lia.
        assert (Hpx_pq : px p + 1 <= px q).
        { rewrite Hnp, Hnq. replace 1 with (IZR 1) by reflexivity.
          rewrite <- plus_IZR. apply IZR_le. lia. }
        assert (Hpy_pq : py p + 1 <= py q).
        { rewrite Hmp, Hmq. replace 1 with (IZR 1) by reflexivity.
          rewrite <- plus_IZR. apply IZR_le. lia. }
        assert (Hqq_qp_x : (1-tq) * px P0 + tq * px P1 > (1-tp) * px P0 + tp * px P1).
        { lra. }
        assert (Hqq_qp_y : (1-tq) * py P0 + tq * py P1 > (1-tp) * py P0 + tp * py P1).
        { lra. }
        assert (Hsx : (tq - tp) * (px P1 - px P0) > 0) by nra.
        assert (Hsy : (tq - tp) * (py P1 - py P0) > 0) by nra.
        (* alpha_y = -1 case: same sign of (tq - tp) in both, so both
           segment differences have the same sign as (tq - tp).  Hence
           their product is positive, contradicting Hprod < 0. *)
        destruct (Rtotal_order tq tp) as [Htlt | [Hteq | Htgt]].
        -- assert (Hpx_neg : px P1 - px P0 < 0) by nra.
           assert (Hpy_neg : py P1 - py P0 < 0) by nra.
           nra.
        -- subst tq. lra.
        -- assert (Hpx_pos : px P1 - px P0 > 0) by nra.
           assert (Hpy_pos : py P1 - py P0 > 0) by nra.
           nra.
      * exfalso. apply Hnn. exact Heq_z.
      * assert (Hk : (np - nq >= 1)%Z) by lia.
        assert (Hk' : (mp - mq >= 1)%Z) by lia.
        assert (Hpx_qp : px q + 1 <= px p).
        { rewrite Hnp, Hnq. replace 1 with (IZR 1) by reflexivity.
          rewrite <- plus_IZR. apply IZR_le. lia. }
        assert (Hpy_qp : py q + 1 <= py p).
        { rewrite Hmp, Hmq. replace 1 with (IZR 1) by reflexivity.
          rewrite <- plus_IZR. apply IZR_le. lia. }
        assert (Hqp_qq_x : (1-tp) * px P0 + tp * px P1 > (1-tq) * px P0 + tq * px P1).
        { lra. }
        assert (Hqp_qq_y : (1-tp) * py P0 + tp * py P1 > (1-tq) * py P0 + tq * py P1).
        { lra. }
        assert (Hsx : (tp - tq) * (px P1 - px P0) > 0) by nra.
        assert (Hsy : (tp - tq) * (py P1 - py P0) > 0) by nra.
        destruct (Rtotal_order tp tq) as [Htlt | [Hteq | Htgt]].
        -- assert (Hpx_neg : px P1 - px P0 < 0) by nra.
           assert (Hpy_neg : py P1 - py P0 < 0) by nra.
           nra.
        -- subst tq. lra.
        -- assert (Hpx_pos : px P1 - px P0 > 0) by nra.
           assert (Hpy_pos : py P1 - py P0 > 0) by nra.
           nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3 Hobby Lemma 4.3 -- piecewise-linear ordering.                           *)
(* Admitted; registered in docs/admitted-deferred-proofs.txt.                 *)
(* Proof sketch: docs/hobby-theorem-proof-structure.md §4.                    *)
(* -------------------------------------------------------------------------- *)

(* Snap-rounding preserves "intersect only at endpoints" for any pair of
   segments.  The CORE of Hobby's correctness argument.

   The lemma's hypothesis `segments_intersect_only_at_endpoints` is a
   disjunction:
     (a) The originals don't intersect properly, OR
     (b) The originals share a literal endpoint.

   These two cases have very different proof complexity:
     (a) is the thesis-shaped piece -- requires a rotated-coordinate
         piecewise-linear ordering argument using Lemma 4.2 + the
         tolerance-square |F_j(xi) - beta_j - gamma_j * xi| < 1/2 bound.
         Estimated 4-6 weeks (Hobby Lemma 4.3 proper).
     (b) is trivial -- snap_round is a deterministic function, so
         literal equality of endpoints is preserved.

   We refactor `hobby_lemma_4_3` to compose these two pieces.  The
   shared-endpoint half (`hobby_lemma_4_3_shared_endpoint`) is
   Qed-closed below; the no-proper-intersection half
   (`hobby_lemma_4_3_no_proper`) inherits the thesis-shaped scope and
   stays Admitted with the deferred-proof registry entry pointing at
   it.  Net effect on the registry: the deferred entry is sharpened
   from the disjunctive lemma to the genuinely-hard sub-lemma.
   `hobby_theorem_4_1_conditional`'s premise shape is unchanged. *)

(* Sub-lemma (a): the thesis-shaped piece.  If the originals don't
   intersect properly, neither do the snapped versions.  Hobby (1999)
   §4's piecewise-linear ordering argument.  Estimated 4-6 weeks
   (matches the prior `hobby_lemma_4_3` scope estimate). *)
Lemma hobby_lemma_4_3_no_proper :
  forall (P0 P1 Q0 Q1 : Point),
    ~ segments_intersect_properly P0 P1 Q0 Q1 ->
    ~ segments_intersect_properly
        (snap_round P0 1) (snap_round P1 1)
        (snap_round Q0 1) (snap_round Q1 1).
Admitted.

(* Sub-lemma (b): if the originals share a literal endpoint, the
   snapped versions share that snapped endpoint.  Qed-closed via
   determinism of `snap_round`. *)
Lemma hobby_lemma_4_3_shared_endpoint :
  forall (P0 P1 Q0 Q1 : Point),
    P0 = Q0 \/ P0 = Q1 \/ P1 = Q0 \/ P1 = Q1 ->
    snap_round P0 1 = snap_round Q0 1 \/
    snap_round P0 1 = snap_round Q1 1 \/
    snap_round P1 1 = snap_round Q0 1 \/
    snap_round P1 1 = snap_round Q1 1.
Proof.
  intros P0 P1 Q0 Q1 [H | [H | [H | H]]].
  - left.            rewrite H. reflexivity.
  - right. left.     rewrite H. reflexivity.
  - right. right. left.  rewrite H. reflexivity.
  - right. right. right. rewrite H. reflexivity.
Qed.

(* Composition: `hobby_lemma_4_3` is now Qed-closed by case-splitting on
   the hypothesis disjunction and dispatching to the two sub-lemmas. *)
Lemma hobby_lemma_4_3 :
  forall (P0 P1 Q0 Q1 : Point),
    segments_intersect_only_at_endpoints (P0, P1) (Q0, Q1) ->
    forall sigma1 sigma2 : Point * Point,
      In sigma1 (snap_round_segments [(P0, P1)]) ->
      In sigma2 (snap_round_segments [(Q0, Q1)]) ->
      sigma1 <> sigma2 ->
      segments_intersect_only_at_endpoints sigma1 sigma2.
Proof.
  intros P0 P1 Q0 Q1 Horig sigma1 sigma2 Hin1 Hin2 Hne.
  (* Extract sigma1, sigma2 from the singleton-list `In` premises. *)
  simpl in Hin1, Hin2.
  destruct Hin1 as [Heq1 | []].
  destruct Hin2 as [Heq2 | []].
  subst sigma1 sigma2.
  simpl.
  destruct Horig as [Hnoprop | Hshare].
  - (* Case (a): originals don't intersect properly.  Apply
       hobby_lemma_4_3_no_proper. *)
    left. apply hobby_lemma_4_3_no_proper. exact Hnoprop.
  - (* Case (b): originals share a literal endpoint.  Apply
       hobby_lemma_4_3_shared_endpoint. *)
    right. apply hobby_lemma_4_3_shared_endpoint. exact Hshare.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4 Hobby Theorem 4.1 -- conditional.                                       *)
(* Qed-closed: structural list composition.                                   *)
(* -------------------------------------------------------------------------- *)

(* The headline of Hobby's Section 4, conditional on a per-pair preservation
   hypothesis `Hlemma43` (which the standalone `hobby_lemma_4_3` above would
   discharge if proved).  Proof: lift the per-pair preservation through the
   arrangement via `List.in_map_iff` -- the segment-list version of "if every
   PAIR is preserved, the whole ARRANGEMENT is preserved."

   `Hlemma43`'s signature here takes `segments_intersect_only_at_endpoints
   s1 s2` as a premise rather than re-deriving it; `Hfi : fully_intersected A`
   supplies that premise for the pair we extract from in_map_iff.

   (One revision from the prompt's sketch -- per the prompt's "one revision
   allowed" stopping condition -- to make `Hfi` actually feed in.  The
   prompt's sketch had `Hlemma43` repeat the `s1 <> s2` precondition with no
   way for `Hfi` to discharge it; this form composes cleanly.) *)
Theorem hobby_theorem_4_1_conditional :
  forall (A : list (Point * Point)),
    fully_intersected A ->
    (forall s1 s2 : Point * Point,
       segments_intersect_only_at_endpoints s1 s2 ->
       forall sigma1 sigma2 : Point * Point,
         In sigma1 (snap_round_segments [s1]) ->
         In sigma2 (snap_round_segments [s2]) ->
         sigma1 <> sigma2 ->
         segments_intersect_only_at_endpoints sigma1 sigma2) ->
    fully_intersected (snap_round_segments A).
Proof.
  intros A Hfi Hlemma43 sigma1 sigma2 Hin1' Hin2' Hne.
  unfold snap_round_segments in Hin1', Hin2'.
  apply List.in_map_iff in Hin1'.
  destruct Hin1' as [s1 [Heq1 Hin1]].
  apply List.in_map_iff in Hin2'.
  destruct Hin2' as [s2 [Heq2 Hin2]].
  assert (Hs12 : s1 <> s2).
  { intros E. apply Hne. subst s2. rewrite <- Heq1. exact Heq2. }
  apply (Hlemma43 s1 s2 (Hfi s1 s2 Hin1 Hin2 Hs12) sigma1 sigma2).
  - unfold snap_round_segments; simpl. left. exact Heq1.
  - unfold snap_round_segments; simpl. left. exact Heq2.
  - exact Hne.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions hobby_theorem_4_1_conditional.
