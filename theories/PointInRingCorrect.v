(* ============================================================================
   NetTopologySuite.Proofs.PointInRingCorrect
   ----------------------------------------------------------------------------
   Green-phase seam attempts for `point_in_ring_correct`.

   Seven seams.  Each section: simplest statement, simplest proof attempt,
   outcome (Qed or precise stuck goal).  Per-seam outcomes recorded in the
   companion document `docs/point-in-ring-seam-attempts.md`.

   Reference: `docs/point-in-ring-correct-seam-map.md` for the gap
   inventory this file probes.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.

From NTS.Proofs Require Import Distance.
From NTS.Proofs Require Import ArcOrient.   (* cross_R_pt *)
From NTS.Proofs Require Import Overlay.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Seam 1: segment_crosses_ray (bool) and its correctness.                *)
(* -------------------------------------------------------------------------- *)

(* Local bool wrapper around `Rlt_dec` -- Stdlib has the decidability
   sumbool but no `Rlt_b` (that one lives in `Flocq.Core.Raux` and
   the corpus restricts Flocq imports to theories-flocq/). *)
Definition Rlt_b (x y : R) : bool :=
  if Rlt_dec x y then true else false.

Lemma Rlt_b_iff_true : forall x y, Rlt_b x y = true <-> x < y.
Proof.
  intros x y. unfold Rlt_b. destruct (Rlt_dec x y); split;
    intros; try discriminate; try lra; reflexivity.
Qed.

Lemma Rlt_b_iff_false : forall x y, Rlt_b x y = false <-> ~ x < y.
Proof.
  intros x y. unfold Rlt_b. destruct (Rlt_dec x y); split;
    intros; try discriminate; try lra; reflexivity.
Qed.

(* Bool mirror of the corpus's `edge_crosses_ray` (Overlay.v:149-155).
   Strict y-straddle on BOTH sides -- endpoint touches (py P = py A or
   py P = py B) are NOT counted as crossings, matching the generic-
   position convention.  Two cases by y-orientation. *)
Definition segment_crosses_ray (P A B : Point) : bool :=
  if Rlt_b (py A) (py P) && Rlt_b (py P) (py B) then
    (* Case 1: py A < py P < py B (segment goes up through ray height) *)
    Rlt_b (px P) (px A + (px B - px A) * (py P - py A) / (py B - py A))
  else if Rlt_b (py B) (py P) && Rlt_b (py P) (py A) then
    (* Case 2: py B < py P < py A (segment goes down through ray height) *)
    Rlt_b (px P) (px B + (px A - px B) * (py P - py B) / (py A - py B))
  else
    false.

(* Soundness: bool predicate firing gives a parametric witness t in
   the OPEN interval (0, 1) at height py P with x-coordinate strictly
   right of P.  No precondition needed -- the strict-strict bool form
   already excludes endpoint hits. *)
Lemma segment_crosses_ray_sound :
  forall (P A B : Point),
    segment_crosses_ray P A B = true ->
    exists t : R,
      0 < t < 1 /\
      py A + t * (py B - py A) = py P /\
      px A + t * (px B - px A) > px P.
Proof.
  intros P A B H.
  unfold segment_crosses_ray in H.
  set (t := (py P - py A) / (py B - py A)) in *.
  destruct (Rlt_b (py A) (py P) && Rlt_b (py P) (py B)) eqn:HC1.
  - (* Case 1: py A < py P < py B *)
    apply andb_true_iff in HC1 as [HAlt HPB].
    apply Rlt_b_iff_true in HAlt, HPB, H.
    assert (Hd : 0 < py B - py A) by lra.
    exists t. split; [|split].
    + unfold t; split.
      * apply Rdiv_lt_0_compat; lra.
      * apply (Rmult_lt_reg_r (py B - py A)); [lra|].
        unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra.
    + unfold t. field. lra.
    + unfold t.
      replace (px A + (py P - py A) / (py B - py A) * (px B - px A))
        with (px A + (px B - px A) * (py P - py A) / (py B - py A))
        by (field; lra).
      exact H.
  - (* Case 1 fails; check Case 2: py B < py P < py A *)
    destruct (Rlt_b (py B) (py P) && Rlt_b (py P) (py A)) eqn:HC2;
      [|discriminate].
    apply andb_true_iff in HC2 as [HBlt HPA].
    apply Rlt_b_iff_true in HBlt, HPA, H.
    assert (Hd : py B < py A) by lra.
    exists t. split; [|split].
    + assert (Hdneg : py B - py A < 0) by lra.
      unfold t; split.
      * unfold Rdiv.
        assert (Hinv : / (py B - py A) < 0)
          by (apply Rinv_lt_0_compat; lra).
        nra.
      * unfold Rdiv.
        apply (Rmult_lt_reg_r (- (py B - py A))); [lra|].
        replace ((py P - py A) * / (py B - py A) * - (py B - py A))
          with (py A - py P) by (field; lra).
        lra.
    + unfold t. field. lra.
    + unfold t.
      replace (px A + (py P - py A) / (py B - py A) * (px B - px A))
        with (px B + (px A - px B) * (py P - py B) / (py A - py B))
        by (field; lra).
      exact H.
Qed.

(* Completeness: a parametric witness yields the bool predicate.

   PRECONDITION needed: py A <> py B.  A horizontal segment (py A =
   py B) lying ON the ray (py P = py A) admits a parametric witness
   t in (0, 1) with `px A + t*(px B - px A) > px P` for suitable
   geometry, but the bool predicate returns false (strict y-straddle
   fails).  This is the generic-position convention: horizontal edges
   are NOT counted as crossings.  See `docs/point-in-ring-correct-
   seam-map.md` §2 Seam 4. *)
Lemma segment_crosses_ray_complete :
  forall (P A B : Point) (t : R),
    py A <> py B ->
    0 < t < 1 ->
    py A + t * (py B - py A) = py P ->
    px A + t * (px B - px A) > px P ->
    segment_crosses_ray P A B = true.
Proof.
  intros P A B t Hne [Ht0 Ht1] Hty Htx.
  unfold segment_crosses_ray.
  destruct (Rlt_dec (py A) (py B)) as [Hab | Hge].
  - (* py A < py B: case py A < py P < py B *)
    assert (HpyA : py A < py P) by nra.
    assert (HpyB : py P < py B) by nra.
    assert (HAlt : Rlt_b (py A) (py P) = true)
      by (apply Rlt_b_iff_true; exact HpyA).
    assert (HPB : Rlt_b (py P) (py B) = true)
      by (apply Rlt_b_iff_true; exact HpyB).
    rewrite HAlt, HPB. cbn [andb].
    apply Rlt_b_iff_true.
    assert (Htform : t = (py P - py A) / (py B - py A)).
    { apply (Rmult_eq_reg_r (py B - py A)); [|lra].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
    assert (Heq : px A + (px B - px A) * (py P - py A) / (py B - py A)
                = px A + t * (px B - px A))
      by (rewrite Htform; field; lra).
    rewrite Heq. exact Htx.
  - (* py B <= py A and py A <> py B: py B < py A,
       case py B < py P < py A *)
    assert (Hba : py B < py A) by lra.
    assert (HpyA : py P < py A) by nra.
    assert (HpyB : py B < py P) by nra.
    assert (HAlt : Rlt_b (py A) (py P) = false)
      by (apply Rlt_b_iff_false; lra).
    rewrite HAlt. cbn [andb].
    assert (HBlt : Rlt_b (py B) (py P) = true)
      by (apply Rlt_b_iff_true; exact HpyB).
    assert (HPA : Rlt_b (py P) (py A) = true)
      by (apply Rlt_b_iff_true; exact HpyA).
    (* When HAlt fails, the if takes the else; we need to also know
       what the third Rlt_b branches to. *)
    destruct (Rlt_b (py P) (py B)) eqn:HPB.
    + (* HPB = true would mean py P < py B, contradicting py B < py P *)
      apply Rlt_b_iff_true in HPB. lra.
    + cbn [andb].
      rewrite HBlt, HPA. cbn [andb].
      apply Rlt_b_iff_true.
      assert (Htform : t = (py P - py A) / (py B - py A)).
      { apply (Rmult_eq_reg_r (py B - py A)); [|lra].
        unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
      assert (Heq : px B + (px A - px B) * (py P - py B) / (py A - py B)
                  = px A + t * (px B - px A))
        by (rewrite Htform; field; lra).
      rewrite Heq. exact Htx.
Qed.

(* Biconditional correctness statement.  Precondition `py A <> py B`
   is needed for completeness: a horizontal segment ON the ray admits
   parametric witnesses, but the bool predicate returns false.  Under
   non-horizontality, the two directions agree. *)
Theorem segment_crosses_ray_correct :
  forall (P A B : Point),
    py A <> py B ->
    segment_crosses_ray P A B = true <->
    exists t : R,
      0 < t < 1 /\
      py A + t * (py B - py A) = py P /\
      px A + t * (px B - px A) > px P.
Proof.
  intros P A B Hne; split.
  - apply segment_crosses_ray_sound.
  - intros [t [Ht01 [Hty Htx]]].
    apply (segment_crosses_ray_complete _ _ _ t Hne Ht01 Hty Htx).
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Seam 2: count_crossings_ray and agreement with point_in_ring.          *)
(* -------------------------------------------------------------------------- *)

(* The bool-side count of edges crossed by the rightward ray from p. *)
Definition count_crossings_ray (p : Point) (r : Ring) : nat :=
  fold_left
    (fun acc e =>
       let '(A, B) := e in
       if segment_crosses_ray p A B then S acc else acc)
    (ring_edges r) 0%nat.

(* Auxiliary: the Prop-side `edge_crosses_ray` and the bool-side
   `segment_crosses_ray` agree on non-horizontal edges with the rightward
   ray.

   Caveat: edge_crosses_ray uses the linear-interpolation formula with
   denominator (py b - py a) in the orientation-specific direction; the
   bool form's `t` uses (py B - py A).  Both reduce to the same
   x-intercept; the proof aligns them via Rmult/Rdiv arithmetic. *)
Lemma segment_crosses_ray_matches_edge_crosses_ray :
  forall (P A B : Point),
    py A <> py B ->
    segment_crosses_ray P A B = true <-> edge_crosses_ray P (A, B).
Proof.
  intros P A B Hne.
  unfold edge_crosses_ray.
  split.
  - intro Hb.
    pose proof (segment_crosses_ray_sound _ _ _ Hb) as [t [[Ht0 Ht1] [Hty Htx]]].
    (* Case-split on whether py A < py B or py B < py A *)
    destruct (Rlt_dec (py A) (py B)) as [Hlt | Hge].
    + (* py A < py B *)
      left. assert (Hd : py B - py A <> 0) by lra.
      assert (Htform : t = (py P - py A) / (py B - py A))
        by (apply (Rmult_eq_reg_r (py B - py A)); [|lra];
            unfold Rdiv; rewrite Rmult_assoc, Rinv_l by lra; lra).
      split; [nra|].
      replace (px A + (px B - px A) * (py P - py A) / (py B - py A))
        with (px A + t * (px B - px A))
        by (rewrite Htform; field; lra).
      exact Htx.
    + (* py B < py A *)
      right. assert (Hd : py A - py B <> 0) by lra.
      assert (Hlt' : py B < py A) by lra.
      assert (Htform : t = (py P - py A) / (py B - py A))
        by (apply (Rmult_eq_reg_r (py B - py A)); [|lra];
            unfold Rdiv; rewrite Rmult_assoc, Rinv_l by lra; lra).
      split; [nra|].
      (* edge_crosses_ray's RHS:
           px B + (px A - px B) * (py P - py B) / (py A - py B)
         Rewrite as px A + t * (px B - px A) via algebra. *)
      replace (px B + (px A - px B) * (py P - py B) / (py A - py B))
        with (px A + t * (px B - px A))
        by (rewrite Htform; field; lra).
      exact Htx.
  - intro Hp. destruct Hp as [[Hy Hx] | [Hy Hx]].
    + (* py a < py p < py b *)
      apply (segment_crosses_ray_complete _ _ _ ((py P - py A) / (py B - py A))).
      * exact Hne.
      * split.
        -- apply Rdiv_lt_0_compat; lra.
        -- apply (Rmult_lt_reg_r (py B - py A)); [lra|].
           unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra.
      * field. lra.
      * assert (Hd : py B - py A <> 0) by lra.
        replace (px A + (py P - py A) / (py B - py A) * (px B - px A))
          with (px A + (px B - px A) * (py P - py A) / (py B - py A))
          by (field; exact Hd).
        exact Hx.
    + (* py b < py p < py a *)
      apply (segment_crosses_ray_complete _ _ _ ((py P - py A) / (py B - py A))).
      * exact Hne.
      * split.
        -- assert (Hdneg : py B - py A < 0) by lra.
           unfold Rdiv.
           assert (Hinv : / (py B - py A) < 0)
             by (apply Rinv_lt_0_compat; lra).
           nra.
        -- apply (Rmult_lt_reg_r (- (py B - py A))); [lra|].
           unfold Rdiv.
           replace ((py P - py A) * / (py B - py A) * - (py B - py A))
             with (py A - py P) by (field; lra).
           lra.
      * field. lra.
      * assert (Hd : py A - py B <> 0) by lra.
        assert (Hd2 : py B - py A <> 0) by lra.
        replace (px A + (py P - py A) / (py B - py A) * (px B - px A))
          with (px B + (px A - px B) * (py P - py B) / (py A - py B))
          by (field; split; lra).
        exact Hx.
Qed.

(* Seam 2 outcome.

   Goal: `point_in_ring p r <-> Nat.odd (count_crossings_ray p r) = true`.

   point_in_ring is a Prop (ray_parity_odd), so the biconditional is
   Prop <-> bool.  The proof would proceed by induction on the edge
   list, alternating between the odd/even disjuncts of the mutual
   inductive AND tracking the fold accumulator's parity.

   STUCK at: cleanly tracking the fold_left accumulator's parity
   across the mutual induction.  The fold seeds at 0 and toggles on
   each crossing; ray_parity_odd/_even seed at the empty list and
   toggle in the same way -- BUT the bool agreement
   (segment_crosses_ray vs edge_crosses_ray) requires the
   non-horizontal-edge hypothesis on EVERY edge, not just one.
   Without a `Forall (fun e => py (fst e) <> py (snd e))` precondition
   this lemma does not hold in general (a horizontal edge fires
   neither bool nor Prop predicate, but the disagreement risk is
   nonzero at degenerate y-positions).

   Recording the agreement under that precondition is the natural
   load-bearing claim; it is the prompt's `ray_nondegenerate`
   characterisation (Seam 6).  See §6 below.
*)

(* -------------------------------------------------------------------------- *)
(* §3  Seam 3: geometric_interior via fourcolor realplane.                    *)
(* -------------------------------------------------------------------------- *)

(* DEFERRED -- import alone surfaces the Real.structure bridge gap.

   Attempt:

     From fourcolor Require Import realplane.

     Definition to_rplane (p : Point) : realplane.point :=
       realplane.Point (px p) (py p).

   STUCK at: `realplane.point` is `Inductive point := Point (x y :
   Real.val R)` -- parametric over a Section variable `R :
   Real.structure`.  The Section closes the variable; an external
   reference like `realplane.point` becomes `realplane.point R` and
   requires a concrete `Real.structure` argument.

   Stdlib's `R` is NOT a `Real.structure` instance.  Constructing one
   requires defining all of `Real.structure`'s fields (a Tarski-style
   axiomatic real line with `add`, `mul`, `opp`, `lt`, `min`, ...)
   over Stdlib `R` and proving each axiom -- the 2-3 session
   Real.structure bridge documented in
   `docs/ecosystem-search-2026-05-29.md` §5 and
   `docs/point-in-ring-correct-seam-map.md` §2 Seam 6.

   Without that bridge, `geometric_interior` cannot be stated in
   fourcolor's vocabulary.  The corpus's H1 hypothesis in
   `OverlayCorrectness.v` remains an opaque Section Variable.

   Coq-level outcome: no definition lands here.  The seam map's RED
   classification is reaffirmed -- the bridge is the gating piece, not
   a missing lemma. *)

(* -------------------------------------------------------------------------- *)
(* §4  Seam 4: point_in_ring_correct conditional form.                        *)
(* -------------------------------------------------------------------------- *)

(* The form that the corpus CAN state today: parameterised over an
   abstract `interior` predicate.  Mirrors OverlayCorrectness.v's
   Section-Variable pattern. *)
Section ConditionalPointInRingCorrect.

  Variable interior : Point -> Ring -> Prop.

  (* Trivially true.  The point of the statement is to record the
     SHAPE of the bidirectional correctness lemma we eventually want
     to discharge -- with `interior` plugged in by a future JCT
     toolkit.  `Lemma` not `Theorem` because the statement is
     vacuous; no `Print Assumptions` ceremony warranted. *)
  Lemma point_in_ring_correct_conditional :
    forall (p : Point) (r : Ring),
      ring_simple r ->
      ring_closed r ->
      ring_has_minimum_points r ->
      (point_in_ring p r <-> interior p r) ->
      point_in_ring p r <-> interior p r.
  Proof.
    intros p r _ _ _ Hiff. exact Hiff.
  Qed.

End ConditionalPointInRingCorrect.

(* Seam 4 outcome.

   Qed -- vacuously.  The conditional form is structurally
   well-formed and discharges trivially because every load-bearing
   step is assumed.  This documents what the headline statement looks
   like once an `interior` predicate exists; it does NOT advance the
   gap -- the iff is itself the hypothesis.

   Real Seam 4 work (deriving the iff from a richer hypothesis like
   "interior is the bounded component of R^2 \ image(r)") cannot be
   stated without first defining `interior` over a concrete topology,
   which is Seam 3's blocker. *)

(* -------------------------------------------------------------------------- *)
(* §5  Seam 5: winding_number for simple polygons.                            *)
(* -------------------------------------------------------------------------- *)

(* DEFERRED -- `winding_number` not in the corpus.

   The natural definition is a sum over edges of the signed angle
   subtended at p, divided by 2*pi.  In Coq this requires:
     1. atan2 over Stdlib R (Coquelicot has this; not in current
        imports).
     2. A polygon-edge fold computing the total angle.
     3. A characterisation that the result is in {-1, 0, +1} for
        simple closed polygons that don't pass through p.

   Without piece 1, the definition itself cannot be written.
   Coquelicot is NOT in the corpus's installed package set
   (see docs/ecosystem-search-2026-05-29.md). atan2 in Stdlib's
   Reals.v is `Ratan2`, which IS available -- let us confirm. *)

(* Probe: is atan2 / Ratan2 in Stdlib? *)
(* From Stdlib Require Import Ratan.  -- this works.  Defines
   `Ratan : R -> R` (signature R -> R) but NOT atan2 (R -> R -> R).
   atan2 is in Coquelicot or mathcomp-analysis; neither is imported
   here.  Without atan2 the signed-angle-per-edge fold cannot be
   written in the natural form.

   Alternative formulation (combinatorial):

     winding_number p r := (count_crossings_ray p r) / 2

   where the half-counted ray-crossing convention is used.  This
   ducks the trigonometric definition but only works for simple
   closed polygons in generic position (no vertex on the ray).
   Stated as the Seam 5 placeholder, it reduces to Seam 6's
   degeneracy handling.

   Coq-level outcome: no definition lands here.  Documenting that
   winding_number cannot be defined without either atan2
   (Coquelicot/mathcomp dependency) or a Seam 6 generic-position
   precondition. *)

(* -------------------------------------------------------------------------- *)
(* §6  Seam 6: ray-degenerate-safe characterisation.                          *)
(* -------------------------------------------------------------------------- *)

(* The corpus's `edge_crosses_ray` uses STRICT inequalities, so any
   horizontal edge (`py a = py b`) is classified as not-crossing -- the
   first disjunct's `py a < py p < py b` is impossible when py a =
   py b.  Same for the second disjunct.  Hence horizontal edges
   contribute zero to the parity, regardless of ray position.

   The natural generic-position precondition: "no edge of r is
   horizontal at height py p".  Under this precondition, the bool
   form `segment_crosses_ray` and the Prop form `edge_crosses_ray`
   agree edge-by-edge (Seam 2's auxiliary lemma). *)

Definition no_horizontal_edge_at (p : Point) (r : Ring) : Prop :=
  Forall (fun e : Edge => py (fst e) <> py (snd e)) (ring_edges r).

(* Equivalence of the bool fold with the Prop ray-parity under
   no-horizontal-edge.  Mutual-induction matching the mutual definition
   of ray_parity_odd/_even, with the fold accumulator's parity tracked
   in parallel.

   STUCK at: the fold accumulator is initialised at 0 and toggled per
   edge; the Prop predicate handles edges via the mutual inductive's
   constructors `rpo_cross` (consumes one crossing edge, demands
   ray_parity_even on the tail) and `rpo_skip` (demands
   ray_parity_odd on the tail).  Aligning the two requires
   simultaneous induction on the EDGE LIST with the fold accumulator
   as a parameter -- standard `fold_left` -> `fold_right`
   transformation plus a generalisation lemma.  Full proof is
   2-4 hours of routine bookkeeping; the simplest fact (Forall +
   per-edge agreement => list-level agreement on the COUNT) closes
   in the second-direction sketch below but the parity equivalence
   doesn't follow from the count without the bool/Prop classifier
   alignment which IS the load-bearing step. *)

(* Under no-horizontal-edge, the per-edge agreement between bool
   `segment_crosses_ray` and Prop `edge_crosses_ray` is exactly
   `segment_crosses_ray_matches_edge_crosses_ray` (§2 auxiliary)
   applied per edge of the `Forall`.  Downstream callers extract
   per-edge non-horizontality from `no_horizontal_edge_at` via
   `Forall_forall` and apply the §2 lemma directly. *)

(* -------------------------------------------------------------------------- *)
(* §6b  ray_parity_fold_bridge -- closes Seam 2 + Seam 6 list-level.          *)
(* -------------------------------------------------------------------------- *)

(* Helper: the count_crossings_ray's fold_left as a binary function of the
   accumulator -- so we can prove an accumulator-generalisation lemma. *)
Definition count_aux (p : Point) (l : list Edge) (acc : nat) : nat :=
  fold_left
    (fun a e => let '(A, B) := e in
                if segment_crosses_ray p A B then S a else a)
    l acc.

(* `count_aux` agrees with `count_crossings_ray` on `ring_edges r`. *)
Lemma count_crossings_ray_unfold :
  forall (p : Point) (r : Ring),
    count_crossings_ray p r = count_aux p (ring_edges r) 0.
Proof. reflexivity. Qed.

(* Standard fold_left-accumulator generalisation: starting from any acc is
   like starting from 0 and adding acc. *)
Lemma count_aux_acc :
  forall (p : Point) (l : list Edge) (acc : nat),
    count_aux p l acc = (acc + count_aux p l 0)%nat.
Proof.
  intros p l. induction l as [|[A B] l' IH]; intro acc.
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - simpl. destruct (segment_crosses_ray p A B).
    + rewrite (IH (S acc)), (IH 1%nat). lia.
    + rewrite (IH acc), (IH 0%nat). lia.
Qed.

(* Cons-form for count_aux at accumulator 0. *)
Lemma count_aux_cons :
  forall (p : Point) (A B : Point) (l : list Edge),
    count_aux p ((A, B) :: l) 0%nat
    = (if segment_crosses_ray p A B
       then S (count_aux p l 0%nat)
       else count_aux p l 0%nat).
Proof.
  intros p A B l.
  change (count_aux p ((A, B) :: l) 0%nat)
    with (count_aux p l (if segment_crosses_ray p A B then 1%nat else 0%nat)).
  destruct (segment_crosses_ray p A B).
  - rewrite (count_aux_acc p l 1%nat). lia.
  - reflexivity.
Qed.

(* The bridge: under `no_horizontal_edge_at`-style edge-list precondition,
   the Prop-side mutual inductive `ray_parity_odd` / `ray_parity_even`
   matches the bool-side fold parity.  Proved as a CONJUNCTION so the
   odd-half and even-half IHs are simultaneously available at each step. *)
Lemma ray_parity_fold_bridge :
  forall (p : Point) (edges : list Edge),
    Forall (fun e : Edge => py (fst e) <> py (snd e)) edges ->
    (ray_parity_odd  p edges <-> Nat.odd  (count_aux p edges 0%nat) = true) /\
    (ray_parity_even p edges <-> Nat.even (count_aux p edges 0%nat) = true).
Proof.
  intros p edges Hnh.
  induction edges as [|[A B] rest IH].
  - (* Base case: empty edge list. *)
    split; split; intro H.
    + inversion H.
    + cbn in H. discriminate.
    + reflexivity.
    + constructor.
  - (* Inductive step: (A, B) :: rest. *)
    inversion Hnh as [|? ? Hnh_ab Hnh_rest]; subst.
    cbn in Hnh_ab.
    pose proof (IH Hnh_rest) as [IH_odd IH_even].
    pose proof (segment_crosses_ray_matches_edge_crosses_ray p A B Hnh_ab)
      as [Hbool_to_prop Hprop_to_bool].
    rewrite count_aux_cons.
    destruct (segment_crosses_ray p A B) eqn:Hscr.
    + (* Edge crosses (bool = true): count grows by 1; parity flips. *)
      assert (Hec : edge_crosses_ray p (A, B)) by (apply Hbool_to_prop; reflexivity).
      rewrite Nat.odd_succ, Nat.even_succ.
      split; split; intro H.
      * (* odd ((A,B)::rest) -> even (count rest) *)
        inversion H; subst.
        -- apply IH_even. assumption.
        -- contradiction.
      * (* even (count rest) -> odd ((A,B)::rest) *)
        apply rpo_cross; [exact Hec | apply IH_even; exact H].
      * (* even ((A,B)::rest) -> odd (count rest) *)
        inversion H; subst.
        -- apply IH_odd. assumption.
        -- contradiction.
      * (* odd (count rest) -> even ((A,B)::rest) *)
        apply rpe_cross; [exact Hec | apply IH_odd; exact H].
    + (* Edge doesn't cross (bool = false): count unchanged; parity preserved. *)
      assert (Hnec : ~ edge_crosses_ray p (A, B)).
      { intro Hec. apply Hprop_to_bool in Hec. congruence. }
      split; split; intro H.
      * inversion H; subst.
        -- contradiction.
        -- apply IH_odd. assumption.
      * apply rpo_skip; [exact Hnec | apply IH_odd; exact H].
      * inversion H; subst.
        -- contradiction.
        -- apply IH_even. assumption.
      * apply rpe_skip; [exact Hnec | apply IH_even; exact H].
Qed.

(* Seam 2 list-level corollary: under no_horizontal_edge_at, point_in_ring
   agrees with the bool-side crossing-count parity. *)
Theorem point_in_ring_eq_parity :
  forall (p : Point) (r : Ring),
    no_horizontal_edge_at p r ->
    point_in_ring p r <-> Nat.odd (count_crossings_ray p r) = true.
Proof.
  intros p r Hnh.
  unfold point_in_ring, no_horizontal_edge_at in *.
  rewrite count_crossings_ray_unfold.
  apply (ray_parity_fold_bridge p (ring_edges r) Hnh).
Qed.

(* Seam 6 list-level corollary: the even-parity dual, useful for outside-
   the-ring callers. *)
Theorem point_outside_ring_eq_even_parity :
  forall (p : Point) (r : Ring),
    no_horizontal_edge_at p r ->
    ray_parity_even p (ring_edges r) <->
    Nat.even (count_crossings_ray p r) = true.
Proof.
  intros p r Hnh.
  unfold no_horizontal_edge_at in *.
  rewrite count_crossings_ray_unfold.
  apply (ray_parity_fold_bridge p (ring_edges r) Hnh).
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  Seam 7: segment_crosses_ray agrees with cross_R_pt orientation.        *)
(* -------------------------------------------------------------------------- *)

(* Bool firing iff intersection lies strictly right of P.  This is a
   direct restatement of segment_crosses_ray_sound's last conjunct,
   wrapped as a corollary so callers can extract the orientation
   conclusion without re-proving the t-witness. *)
Lemma segment_crosses_ray_implies_right :
  forall (P A B : Point),
    py A <> py B ->
    segment_crosses_ray P A B = true ->
    let t  := (py P - py A) / (py B - py A) in
    px A + t * (px B - px A) > px P.
Proof.
  intros P A B Hne H.
  pose proof (segment_crosses_ray_sound _ _ _ H) as [t' [[Ht0 Ht1] [Hty Htx]]].
  (* Show that t' coincides with the canonical t expression. *)
  assert (Htform : t' = (py P - py A) / (py B - py A)).
  { apply (Rmult_eq_reg_r (py B - py A)); [|lra].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
  cbv zeta. rewrite <- Htform. exact Htx.
Qed.

(* The orientation-cross-product connection.  Given a non-horizontal
   edge strictly above-below straddling py P, the intersection point on
   the ray satisfies a sign relation with cross_R_pt.

   Claim: segment_crosses_ray fires iff cross_R_pt P A B has the same
   sign as (py B - py A).

   Equivalent algebraic identity (for the y-straddle): the LB
   x-intercept exceeds px P iff the signed area (P, A, B) has the
   sign matching the y-direction.

   Worked at the algebra level:
     cross_R_pt P A B = (px A - px P) * (py B - py P)
                      - (px B - px P) * (py A - py P)
   Combine with t = (py P - py A) / (py B - py A): the bool firing
   condition `px A + t * (px B - px A) > px P` rearranges to
   `cross_R_pt P A B * sign(py B - py A) > 0`. *)

(* If the bool predicate fires, the segment is non-horizontal.  Used
   to discharge the y-orientation case split below. *)
Lemma segment_crosses_ray_non_horizontal :
  forall (P A B : Point),
    segment_crosses_ray P A B = true ->
    py A <> py B.
Proof.
  intros P A B H Heq.
  unfold segment_crosses_ray in H.
  destruct (Rlt_b (py A) (py P)) eqn:E1;
  destruct (Rlt_b (py P) (py B)) eqn:E2;
  cbn [andb] in H;
  try destruct (Rlt_b (py B) (py P)) eqn:E3;
  try destruct (Rlt_b (py P) (py A)) eqn:E4;
  cbn [andb] in H; try discriminate;
  try (apply Rlt_b_iff_true in E1);
  try (apply Rlt_b_iff_true in E2);
  try (apply Rlt_b_iff_true in E3);
  try (apply Rlt_b_iff_true in E4);
  lra.
Qed.

(* FORWARD direction.  The reverse direction (cross-product sign +
   y-straddle implies bool fires) requires algebraic re-derivation
   via `field_simplify` whose denominator-nonvanishing side conditions
   interact poorly with the bool case-split; the forward direction is
   sufficient as a downstream consumer's primitive. *)
Lemma segment_crosses_ray_implies_cross_R_pt :
  forall (P A B : Point),
    segment_crosses_ray P A B = true ->
    ( (py A < py P < py B /\ 0 < cross_R_pt P A B) \/
      (py B < py P < py A /\ cross_R_pt P A B < 0) ).
Proof.
  intros P A B H.
  pose proof (segment_crosses_ray_non_horizontal _ _ _ H) as Hyne.
  pose proof (segment_crosses_ray_sound _ _ _ H)
    as [t [[Ht0 Ht1] [Hty Htx]]].
  unfold cross_R_pt.
  destruct (Rlt_dec (py A) (py B)) as [Hab | Hba].
  - (* py A < py B *)
    left. split; [nra|].
    assert (Hd : py B - py A > 0) by lra.
    assert (Htform : t = (py P - py A) / (py B - py A)).
    { apply (Rmult_eq_reg_r (py B - py A)); [|lra].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
    assert (Hpos : 0 < py P - py A) by nra.
    assert (Hpos2 : 0 < py B - py P) by nra.
    assert (Htx' : (px A - px P) * (py B - py A)
                     > - (t * (px B - px A) * (py B - py A))) by nra.
    assert (Hts : t * (py B - py A) = py P - py A)
      by (rewrite Htform; field; lra).
    assert (Htxr : (px A - px P) * (py B - py A)
                     > - ((px B - px A) * (py P - py A))).
    { replace (- ((px B - px A) * (py P - py A)))
        with (- (t * (px B - px A) * (py B - py A))) by nra.
      exact Htx'. }
    nra.
  - (* py B < py A *)
    assert (Hba' : py B < py A) by lra.
    right. split; [nra|].
    assert (Hd : py B - py A < 0) by lra.
    assert (Htform : t = (py P - py A) / (py B - py A)).
    { apply (Rmult_eq_reg_r (py B - py A)); [|lra].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
    assert (Hneg : py P - py A < 0) by nra.
    assert (Hneg2 : py B - py P < 0) by nra.
    assert (Hts : t * (py B - py A) = py P - py A)
      by (rewrite Htform; field; lra).
    assert (Htx' : (px A - px P) * (py B - py A)
                   < - (t * (px B - px A) * (py B - py A))) by nra.
    assert (Htxr : (px A - px P) * (py B - py A)
                   < - ((px B - px A) * (py P - py A))).
    { replace (- ((px B - px A) * (py P - py A)))
        with (- (t * (px B - px A) * (py B - py A))) by nra.
      exact Htx'. }
    nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions segment_crosses_ray_sound.
Print Assumptions segment_crosses_ray_complete.
Print Assumptions segment_crosses_ray_correct.
Print Assumptions segment_crosses_ray_matches_edge_crosses_ray.
Print Assumptions point_in_ring_correct_conditional.
Print Assumptions count_aux_acc.
Print Assumptions count_aux_cons.
Print Assumptions ray_parity_fold_bridge.
Print Assumptions point_in_ring_eq_parity.
Print Assumptions point_outside_ring_eq_even_parity.
Print Assumptions segment_crosses_ray_implies_right.
Print Assumptions segment_crosses_ray_implies_cross_R_pt.
