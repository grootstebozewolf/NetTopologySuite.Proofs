(* ============================================================================
   NetTopologySuite.Proofs.Linearise
   ----------------------------------------------------------------------------
   Formal companion to docs/mathematics/curves.tex section 7 (Spatial
   operations via linearisation). The three-regime stratification of the
   Phase 3 deliverable of the jts-curved proposal
   (https://github.com/locationtech/jts/discussions/1193) is captured here:

     Regime 1.  Convergent scalar quantities:
                Refining a polyline cannot decrease its length
                (the chord-and-detour lemma).  Witnesses that polyline length
                lower-bounds the true arc length.

     Regime 2.  Convergent topological predicates with non-degenerate
                witnesses: if A is approximated by A' within eps, B by B'
                within eps, and the gap between A and B is at least delta,
                then the approximated shapes are still disjoint -- with a
                concrete gap of (delta - 2*eps).

     Regime 3.  Tolerance-sensitive predicates: there exist distinct shapes
                A and A' admitting a common eps-approximation B, witnessing
                that the linearised "EqualsExact" answer can differ from the
                curved one at arbitrarily small eps.

   No Admitted, no Axiom (except the classical real axioms inherited from
   the corpus's Real.v).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import List.
Import ListNotations.
From NTS.Proofs Require Import Distance Vec.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* A shape is a set of points (a unary predicate on Point).                   *)
(* -------------------------------------------------------------------------- *)

Definition Shape := Point -> Prop.

(* Extensional equality of shapes. *)
Definition shape_eq (A B : Shape) : Prop := forall p, A p <-> B p.

(* -------------------------------------------------------------------------- *)
(* One-sided Hausdorff bound: every point of A is within eps of some point    *)
(* of B.                                                                      *)
(* -------------------------------------------------------------------------- *)

Definition within_eps (A B : Shape) (eps : R) : Prop :=
  forall p, A p -> exists q, B q /\ dist p q <= eps.

(* Symmetric Hausdorff bound. *)
Definition hausdorff_le (A B : Shape) (eps : R) : Prop :=
  within_eps A B eps /\ within_eps B A eps.

(* Lower bound on the gap between two shapes: any pair of representatives is *)
(* at least delta apart.                                                     *)
Definition gap_ge (A B : Shape) (delta : R) : Prop :=
  forall p q, A p -> B q -> dist p q >= delta.

(* -------------------------------------------------------------------------- *)
(* Distance arithmetic.                                                       *)
(* dist is sqrt of dist_sq, so dist is non-negative and its square equals     *)
(* dist_sq.                                                                   *)
(* -------------------------------------------------------------------------- *)

Lemma dist_nonneg : forall p q, 0 <= dist p q.
Proof. intros p q. unfold dist. apply sqrt_pos. Qed.

Lemma dist_sq_eq_dist_sqr : forall p q, dist p q * dist p q = dist_sq p q.
Proof.
  intros p q. unfold dist.
  apply sqrt_sqrt. apply dist_sq_nonneg.
Qed.

Lemma dist_self : forall p, dist p p = 0.
Proof.
  intros p. unfold dist, dist_sq.
  replace ((px p - px p) * (px p - px p) + (py p - py p) * (py p - py p))
     with 0 by ring.
  apply sqrt_0.
Qed.

(* -------------------------------------------------------------------------- *)
(* Triangle inequality for Euclidean distance on R^2.                         *)
(* Proved via squared form + Cauchy-Schwarz from Vec.v.                       *)
(* -------------------------------------------------------------------------- *)

Lemma dist_triangle : forall p q r, dist p r <= dist p q + dist q r.
Proof.
  intros p q r.
  (* Let u = p - q (as a Vec), v = q - r. *)
  set (u := mkVec (px p - px q) (py p - py q)).
  set (v := mkVec (px q - px r) (py q - py r)).
  (* Cauchy-Schwarz in squared form: (u . v)^2 <= |u|^2 |v|^2. *)
  pose proof (cauchy_schwarz_sq u v) as HCS.
  (* |u|^2 = dist_sq p q, |v|^2 = dist_sq q r. *)
  assert (Hu : vmag_sq u = dist_sq p q).
  { unfold vmag_sq, vdot, u, dist_sq. cbn. ring. }
  assert (Hv : vmag_sq v = dist_sq q r).
  { unfold vmag_sq, vdot, v, dist_sq. cbn. ring. }
  (* Non-negativity of the squared magnitudes. *)
  pose proof (dist_sq_nonneg p q) as Hpqn.
  pose proof (dist_sq_nonneg q r) as Hqrn.
  pose proof (dist_nonneg p q) as Hpqd.
  pose proof (dist_nonneg q r) as Hqrd.
  (* Cauchy-Schwarz in linear form: u.v <= dist p q * dist q r. *)
  assert (HCSlin : vdot u v <= dist p q * dist q r).
  { (* (u.v)^2 <= |u|^2 |v|^2 = (dist p q)^2 (dist q r)^2 *)
    rewrite Hu, Hv in HCS.
    rewrite <- (dist_sq_eq_dist_sqr p q) in HCS.
    rewrite <- (dist_sq_eq_dist_sqr q r) in HCS.
    (* HCS : (u.v)^2 <= (dist p q * dist p q) * (dist q r * dist q r) *)
    (* Goal: u.v <= dist p q * dist q r *)
    assert (Hgoalsq :
      vdot u v * vdot u v <=
      (dist p q * dist q r) * (dist p q * dist q r)).
    { lra. }
    (* Take sqrt of both sides, but careful: u.v can be negative. *)
    destruct (Rle_or_lt (vdot u v) 0) as [Hneg | Hpos].
    - (* u.v <= 0 <= dist p q * dist q r. *)
      apply Rle_trans with 0; [exact Hneg |].
      apply Rmult_le_pos; lra.
    - (* u.v > 0. Apply sq_monotone_nonneg. *)
      apply (sq_monotone_nonneg (vdot u v) (dist p q * dist q r)).
      + lra.
      + apply Rmult_le_pos; lra.
      + exact Hgoalsq. }
  (* Now prove (dist p r)^2 <= (dist p q + dist q r)^2 by expansion. *)
  assert (Hsq : dist p r * dist p r <=
                (dist p q + dist q r) * (dist p q + dist q r)).
  { rewrite (dist_sq_eq_dist_sqr p r).
    (* Expand dist_sq p r = |u + v|^2 = |u|^2 + 2 u.v + |v|^2. *)
    assert (Hexpand : dist_sq p r =
                     dist_sq p q + 2 * vdot u v + dist_sq q r).
    { unfold dist_sq, vdot, u, v. cbn. ring. }
    rewrite Hexpand.
    rewrite <- (dist_sq_eq_dist_sqr p q).
    rewrite <- (dist_sq_eq_dist_sqr q r).
    (* Goal: dist p q * dist p q + 2*(u.v) + dist q r * dist q r
             <= (dist p q + dist q r)^2 *)
    nra. }
  (* Convert squared inequality to linear inequality. *)
  apply (sq_monotone_nonneg (dist p r) (dist p q + dist q r)) in Hsq.
  - exact Hsq.
  - apply dist_nonneg.
  - lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Regime 1: refining a polyline cannot decrease its length.                  *)
(* For a chord p-r and any intermediate point q, the two-segment polyline    *)
(* p-q-r has length at least the chord length.  This is the chord-and-       *)
(* detour lemma; iterated, it witnesses that polyline length is a lower      *)
(* bound on arc length and is monotone under refinement.                     *)
(* -------------------------------------------------------------------------- *)

Theorem chord_le_detour : forall p q r,
  dist p r <= dist p q + dist q r.
Proof. exact dist_triangle. Qed.

(* -------------------------------------------------------------------------- *)
(* Iterated form: a polyline-length lower bound by the chord between its     *)
(* endpoints.  Downstream code (length-based simplification, validation)     *)
(* needs the n-point version; the 3-point form above is the inductive step.  *)
(* -------------------------------------------------------------------------- *)

(* The length of a polyline visiting a list of points in order.  Defined    *)
(* via a helper that carries the previous vertex, which makes termination   *)
(* trivial (recursion on the tail).                                          *)
Fixpoint polyline_length_from (prev : Point) (pts : list Point) : R :=
  match pts with
  | []         => 0
  | q :: rest  => dist prev q + polyline_length_from q rest
  end.

Definition polyline_length (pts : list Point) : R :=
  match pts with
  | []         => 0
  | p :: rest  => polyline_length_from p rest
  end.

(* The chord between two points is a lower bound on any polyline that      *)
(* visits them in order, regardless of how many intermediate points the   *)
(* polyline passes through.  Corollary: refining a polyline by inserting  *)
(* intermediate points never decreases its length.                        *)
Theorem polyline_chord_lower_bound :
  forall (start ending : Point) (middle : list Point),
    dist start ending <= polyline_length (start :: middle ++ [ending]).
Proof.
  intros start ending middle. revert start.
  induction middle as [| m rest IH]; intros start.
  - (* middle = []  :  polyline_length [start; ending] = dist start ending + 0 *)
    unfold polyline_length. cbn. lra.
  - (* middle = m :: rest *)
    unfold polyline_length. cbn.
    specialize (IH m).
    unfold polyline_length in IH. cbn in IH.
    pose proof (dist_triangle start m ending) as Tri.
    lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Auxiliary: Hausdorff bound is symmetric.                                   *)
(* -------------------------------------------------------------------------- *)

Lemma hausdorff_sym : forall A B eps,
  hausdorff_le A B eps -> hausdorff_le B A eps.
Proof. intros A B eps [H1 H2]. split; assumption. Qed.

(* -------------------------------------------------------------------------- *)
(* Regime 2: predicate stability under linearisation.                         *)
(* If A and A' are within eps, B and B' are within eps, and gap(A,B) >= delta *)
(* with delta > 2*eps, then gap(A', B') is at least (delta - 2*eps) > 0.      *)
(* So Disjoint/Intersects survives linearisation when the truth is stable in *)
(* a 2*eps-neighbourhood of the inputs.                                      *)
(* -------------------------------------------------------------------------- *)

Theorem disjoint_under_linearise :
  forall (A A' B B' : Shape) (eps delta : R),
    0 <= eps ->
    hausdorff_le A A' eps ->
    hausdorff_le B B' eps ->
    gap_ge A B delta ->
    gap_ge A' B' (delta - 2 * eps).
Proof.
  intros A A' B B' eps delta Heps [HAAprime HAprimeA] [HBBprime HBprimeB] Hgap.
  unfold gap_ge.
  intros p' q' HpA' HqB'.
  (* From within_eps A' A eps, find p in A close to p'. *)
  destruct (HAprimeA p' HpA') as [p [HpA Hpp']].
  (* From within_eps B' B eps, find q in B close to q'. *)
  destruct (HBprimeB q' HqB') as [q [HqB Hqq']].
  (* gap A B delta gives dist p q >= delta. *)
  specialize (Hgap p q HpA HqB).
  (* Triangle: dist p q <= dist p p' + dist p' q' + dist q' q. *)
  pose proof (dist_triangle p p' q) as Tri1.
  pose proof (dist_triangle p' q' q) as Tri2.
  (* dist p q <= dist p p' + dist p' q
                <= dist p p' + (dist p' q' + dist q' q) *)
  assert (Tchain : dist p q <= dist p p' + dist p' q' + dist q' q) by lra.
  (* dist p p' = dist p' p, dist q' q is fine. *)
  (* Hpp' : dist p' p <= eps. By symmetry of dist (proved next), dist p p' <= eps. *)
  assert (Hpp'_sym : dist p p' <= eps).
  { unfold dist. rewrite dist_sq_sym. exact Hpp'. }
  (* Hqq' : dist q' q <= eps. *)
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Corollary: strict positivity. If the gap exceeds 2*eps strictly, the      *)
(* linearised gap is strictly positive (i.e., A' and B' are still disjoint). *)
(* -------------------------------------------------------------------------- *)

Corollary disjoint_under_linearise_strict :
  forall (A A' B B' : Shape) (eps delta : R),
    0 <= eps ->
    delta > 2 * eps ->
    hausdorff_le A A' eps ->
    hausdorff_le B B' eps ->
    gap_ge A B delta ->
    forall p' q', A' p' -> B' q' -> dist p' q' > 0.
Proof.
  intros A A' B B' eps delta Heps Hdelta HAA HBB Hgap p' q' HpA' HqB'.
  pose proof (disjoint_under_linearise A A' B B' eps delta
              Heps HAA HBB Hgap p' q' HpA' HqB') as Hgap'.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Regime 3: tolerance-sensitive predicates can fail under linearisation.    *)
(* For any eps > 0 we exhibit two distinct shapes A and A' that share a      *)
(* common eps-approximation B.  Hence EqualsExact(linearise A eps,           *)
(* linearise A' eps) can be true while EqualsExact(A, A') is false.          *)
(* The construction: A is the straight segment from (0,0) to (1,0); A' is   *)
(* the same segment plus a "bump" point at (1/2, eps/2).                    *)
(* -------------------------------------------------------------------------- *)

(* A canonical realisation of "the segment from (0,0) to (1,0)". *)
Definition straight_segment : Shape :=
  fun p => exists t, 0 <= t /\ t <= 1 /\ px p = t /\ py p = 0.

(* "The bump": the single point (1/2, eps/2). *)
Definition is_bump (eps : R) (p : Point) : Prop :=
  px p = 1/2 /\ py p = eps/2.

Definition segment_with_bump (eps : R) : Shape :=
  fun p => straight_segment p \/ is_bump eps p.

(* The two shapes are extensionally distinct for eps > 0: the bump point lies *)
(* in segment_with_bump but not in straight_segment.                          *)
Lemma bump_distinguishes : forall eps,
  0 < eps -> ~ shape_eq straight_segment (segment_with_bump eps).
Proof.
  intros eps Heps Heq.
  pose (bump := mkPoint (1/2) (eps/2)).
  specialize (Heq bump).
  destruct Heq as [_ Hback].
  assert (Hbump : segment_with_bump eps bump).
  { right. unfold is_bump, bump. cbn. split; reflexivity. }
  apply Hback in Hbump.
  destruct Hbump as [t [_ [_ [_ Hpy]]]].
  unfold bump in Hpy. cbn in Hpy. lra.
Qed.

(* Both shapes are within eps of the straight segment (the "common            *)
(* approximation B").                                                         *)
Lemma straight_self_approx : forall eps,
  0 <= eps -> hausdorff_le straight_segment straight_segment eps.
Proof.
  intros eps Heps. split.
  - intros p Hp. exists p. split.
    + exact Hp.
    + rewrite dist_self. exact Heps.
  - intros p Hp. exists p. split.
    + exact Hp.
    + rewrite dist_self. exact Heps.
Qed.

Lemma bump_approximates_straight : forall eps,
  0 <= eps -> hausdorff_le (segment_with_bump eps) straight_segment eps.
Proof.
  intros eps Heps. split.
  - (* within_eps (segment_with_bump eps) straight_segment eps *)
    intros p Hp. destruct Hp as [Hseg | Hbump].
    + (* p lies on the straight segment: take p itself. *)
      exists p. split.
      * exact Hseg.
      * rewrite dist_self. exact Heps.
    + (* p is the bump point: take (1/2, 0). *)
      exists (mkPoint (1/2) 0).
      destruct Hbump as [Hpx Hpy].
      split.
      * (* (1/2, 0) lies on straight_segment with parameter t = 1/2. *)
        exists (1/2). split.
        -- lra.
        -- split.
           ++ lra.
           ++ split; cbn; reflexivity.
      * (* dist (1/2, eps/2) (1/2, 0) = eps/2 <= eps. *)
        assert (Hd : dist p (mkPoint (1/2) 0) = eps/2).
        { unfold dist, dist_sq. cbn.
          rewrite Hpx, Hpy.
          replace ((1/2 - 1/2) * (1/2 - 1/2) + (eps/2 - 0) * (eps/2 - 0))
             with (Rsqr (eps/2)) by (unfold Rsqr; ring).
          apply sqrt_Rsqr. lra. }
        rewrite Hd. lra.
  - (* within_eps straight_segment (segment_with_bump eps) eps *)
    intros p Hp. exists p. split.
    + left. exact Hp.
    + rewrite dist_self. exact Heps.
Qed.

(* Headline regime-3 result: distinct shapes with a common eps-approximation. *)
Theorem regime3_counterexample : forall eps,
  0 < eps ->
  exists A A' B,
    ~ shape_eq A A' /\
    hausdorff_le A B eps /\
    hausdorff_le A' B eps.
Proof.
  intros eps Heps.
  exists straight_segment, (segment_with_bump eps), straight_segment.
  split; [| split].
  - apply bump_distinguishes; exact Heps.
  - apply straight_self_approx; lra.
  - apply bump_approximates_straight; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Downstream-facing alias: EqualsExact on shapes is extensional equality;   *)
(* the regime-3 result is precisely the statement that EqualsExact is not    *)
(* preserved by Hausdorff-eps approximation.  Use this name when citing the  *)
(* result from outside the file.                                              *)
(* -------------------------------------------------------------------------- *)

Definition EqualsExact : Shape -> Shape -> Prop := shape_eq.

Theorem EqualsExact_not_stable : forall eps,
  0 < eps ->
  exists A A' B,
    ~ EqualsExact A A' /\
    hausdorff_le A B eps /\
    hausdorff_le A' B eps.
Proof. exact regime3_counterexample. Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit: print the assumptions of the headline theorems.               *)
(* -------------------------------------------------------------------------- *)

Print Assumptions dist_triangle.
Print Assumptions disjoint_under_linearise.
Print Assumptions regime3_counterexample.
