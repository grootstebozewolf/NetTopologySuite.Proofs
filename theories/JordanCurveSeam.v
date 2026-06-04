(* ============================================================================
   NetTopologySuite.Proofs.JordanCurveSeam
   ----------------------------------------------------------------------------
   The Jordan-curve seam for `point_in_ring_correct`, examined head-on.

   `docs/jct-scout-2026-05-29.md` graded discharging `JCT_two_components`
   (the polygonal Jordan Curve Theorem) as RED / thesis-scale: no installed
   library shortcuts it, and the genuine theorem remains a multi-thesis
   effort.  This file does NOT claim to prove that theorem.  Instead it
   settles a prior question that turns out to be decisive for the whole
   seam, and it does so with fully Qed-closed, axiom-clean proofs.

   FINDING (Part 1).  The corpus's own interior predicate
   `geometric_interior_stdlib` (theories/PointInRingTangents.v:145) is
   *identically false* -- for every point `p` and every ring `r`.  The
   cause is purely definitional: `connected_in_complement` (ibid:127)
   quantifies over an ARBITRARY function `path : R -> Point` with no
   continuity requirement.  The "jump" function

       fun t => if t < 1 then p else q

   therefore witnesses `connected_in_complement r p q` for ANY two
   off-ring points, collapsing the relation to "both points lie off the
   ring".  `in_bounded_component` then demands the entire (always
   unbounded) complement be bounded -- impossible.  We prove
   `geometric_interior_stdlib_vacuous`: the conjunction is never
   inhabited.

   CONSEQUENCE.  The conditional headline `point_in_ring_correct_jct`
   (PointInRingTangents.v:235) is Qed-closed but only *vacuously*
   satisfiable: its hypothesis `geometric_interior_stdlib p r <->
   interior_pred p` forces `interior_pred` empty too
   (`jct_hypotheses_force_empty_interior`), so for any genuine interior
   point -- where `point_in_ring`/ray-parity is true -- the hypotheses
   cannot all hold.  The real Jordan Curve Theorem cannot even be stated
   correctly against the current definitions; it needs continuous paths.

   FINDING (Part 2/3).  We give the corrected, continuity-carrying
   definitions (`connected_in_complement_cont`, `in_bounded_component_cont`,
   `geometric_interior_cont`) and the genuine, thesis-scale hypothesis
   `JCT_two_components_cont` -- stated as a `Prop`, never axiomatised or
   `Admitted`.  We then prove the discontinuity (not the geometry) is the
   culprit: `far_points_connected_cont` exhibits a genuine CONTINUOUS path
   (a straight segment) between two points right of the ring's bounding
   box, so the corrected relation is non-degenerate exactly where the old
   one was trivial.

   What remains thesis-scale (unchanged): proving an INTERIOR point is
   trapped -- i.e. cannot continuously escape to infinity without crossing
   the ring image.  That is the load-bearing half of the polygonal JCT and
   is NOT discharged here.

   Seam references:
     - docs/jct-vacuity-finding.md      -- this finding, in full.
     - docs/jct-scout-2026-05-29.md     -- the RED tractability grade.
     - docs/point-in-ring-jct-path.md   -- the seven-step path + the
       proposed `JCT_two_components` whose continuous form is here.
     - docs/buffer-noder-pipeline.md §2 -- the shared JCT seam (`spec/JCT`
       row): the OverlayNG / buffer H1 hypothesis is itself stated over
       `geometric_interior_stdlib`, hence likewise vacuous as written.

   Pure-R; no atan / Flocq / `Classical_Prop.classic`.  No `Admitted`,
   no `Axiom`, no `Parameter`.  Axiom footprint: the standard
   classical-reals pair already used across the corpus.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import List.
From Stdlib Require Import Ranalysis.

From NTS.Proofs Require Import Distance.
From NTS.Proofs Require Import Overlay.
From NTS.Proofs Require Import PointInRingCorrect.
From NTS.Proofs Require Import PointInRingTangents.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Bounding the ring image in x.                                          *)
(*                                                                            *)
(* A ring is a finite list of edges; its image is a finite union of bounded  *)
(* segments, hence bounded.  We only need the x-extent: every point of the   *)
(* image has x-coordinate at most `edges_maxX (ring_edges r)`.               *)
(* -------------------------------------------------------------------------- *)

Fixpoint edges_maxX (es : list Edge) : R :=
  match es with
  | [] => 0
  | (a, b) :: es' => Rmax (Rmax (px a) (px b)) (edges_maxX es')
  end.

Lemma convex_le_max :
  forall a b t, 0 <= t <= 1 -> (1 - t) * a + t * b <= Rmax a b.
Proof.
  intros a b t Ht. pose proof (Rmax_l a b). pose proof (Rmax_r a b). nra.
Qed.

Lemma convex_ge_min :
  forall a b t, 0 <= t <= 1 -> Rmin a b <= (1 - t) * a + t * b.
Proof.
  intros a b t Ht. pose proof (Rmin_l a b). pose proof (Rmin_r a b). nra.
Qed.

Lemma in_edges_maxX :
  forall es e, In e es ->
    px (fst e) <= edges_maxX es /\ px (snd e) <= edges_maxX es.
Proof.
  induction es as [|[a b] es' IH]; intros e Hin; simpl in *.
  - contradiction.
  - destruct Hin as [He | He].
    + subst e. simpl. split.
      * eapply Rle_trans; [apply Rmax_l | apply Rmax_l].
      * eapply Rle_trans; [apply Rmax_r | apply Rmax_l].
    + destruct (IH e He) as [H1 H2]. split; eapply Rle_trans;
        try eassumption; apply Rmax_r.
Qed.

Lemma ring_image_px_bound :
  forall r q, ring_image r q -> px q <= edges_maxX (ring_edges r).
Proof.
  intros r q [e [t [Hin [Ht [Hx _]]]]].
  rewrite Hx. eapply Rle_trans; [apply convex_le_max; exact Ht |].
  destruct (in_edges_maxX _ _ Hin) as [H1 H2]. apply Rmax_lub; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The current seam is vacuous.                                           *)
(*                                                                            *)
(* `geometric_interior_stdlib p r` is never inhabited.  Given a candidate    *)
(* bound M for the bounded component, the point q = (max(B,M)+1, 0) is both  *)
(* off the ring (its x exceeds the image bound B) and reachable from p by    *)
(* the discontinuous jump path -- so it must satisfy the bound, yet it sits  *)
(* strictly outside radius M.  Contradiction.                                *)
(* -------------------------------------------------------------------------- *)

Theorem geometric_interior_stdlib_vacuous :
  forall (p : Point) (r : Ring), ~ geometric_interior_stdlib p r.
Proof.
  intros p r [Hcomp [M [HMpos Hbnd]]].
  set (B := edges_maxX (ring_edges r)).
  set (X := Rmax (B + 1) (M + 1)).
  assert (HXB : X > B) by (apply Rlt_le_trans with (B + 1); [lra | apply Rmax_l]).
  assert (HXM : X > M) by (apply Rlt_le_trans with (M + 1); [lra | apply Rmax_r]).
  set (q := mkPoint X 0).
  assert (Hqcomp : ring_complement r q).
  { intro Himg. apply ring_image_px_bound in Himg. simpl in Himg.
    unfold B in HXB. lra. }
  assert (Hcon : connected_in_complement r p q).
  { exists (fun t => if Rlt_dec t 1 then p else q). split; [| split].
    - destruct (Rlt_dec 0 1); [reflexivity | lra].
    - destruct (Rlt_dec 1 1); [lra | reflexivity].
    - intros t Ht. destruct (Rlt_dec t 1); assumption. }
  specialize (Hbnd q Hcon). simpl in Hbnd. nra.
Qed.

(* The conditional JCT headline's H3 hypothesis forces the abstract interior
   predicate to be empty as well -- so the headline is only vacuously
   satisfiable, never witnessing a genuine interior point. *)
Corollary jct_hypotheses_force_empty_interior :
  forall (p : Point) (r : Ring) (interior_pred : Point -> Prop),
    (geometric_interior_stdlib p r <-> interior_pred p) ->
    ~ interior_pred p.
Proof.
  intros p r ip Hiff Hip.
  apply (geometric_interior_stdlib_vacuous p r). apply Hiff, Hip.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The corrected, continuity-carrying definitions.                        *)
(*                                                                            *)
(* These mirror the corpus definitions but require the connecting path to be *)
(* continuous (componentwise, via Stdlib's `continuity`).  This is the only  *)
(* change needed to make the Jordan Curve Theorem statable -- and the only   *)
(* change that makes `geometric_interior_cont` capable of being inhabited.   *)
(* -------------------------------------------------------------------------- *)

Definition path_continuous (path : R -> Point) : Prop :=
  continuity (fun t => px (path t)) /\ continuity (fun t => py (path t)).

Definition connected_in_complement_cont (r : Ring) (p q : Point) : Prop :=
  exists path : R -> Point,
    path_continuous path /\
    path 0 = p /\ path 1 = q /\
    forall t : R, 0 <= t <= 1 -> ring_complement r (path t).

Definition in_bounded_component_cont (r : Ring) (p : Point) : Prop :=
  exists M : R,
    M > 0 /\
    forall q : Point,
      connected_in_complement_cont r p q ->
      px q * px q + py q * py q <= M * M.

Definition geometric_interior_cont (p : Point) (r : Ring) : Prop :=
  ring_complement r p /\ in_bounded_component_cont r p.

(* The genuine Jordan Curve Theorem for simple polygons (continuous version),
   stated as a Prop hypothesis -- the honest replacement for the vacuous
   `geometric_interior_stdlib`-based seam.  This is the thesis-scale fact;
   it is NOT proved here (and NOT axiomatised: it is a named Prop, exactly
   as `JCT_two_components` is described in docs/point-in-ring-jct-path.md).

   CANONICAL Phase 3 H1 TARGET.  This (continuity-carrying, separation-
   bearing) Prop is the canonical hypothesis the OverlayNG / buffer headline
   H1 is now stated against -- via `geometric_interior_cont`, discharged by
   `jct_cont_interior_is_geometric` below.  Do NOT re-introduce an H1 over
   `geometric_interior_stdlib`: that predicate is identically false (§2) and
   makes the headline vacuous.  See theories-flocq/OverlayCorrectness.v and
   docs/jct-vacuity-finding.md. *)
Definition JCT_two_components_cont (r : Ring) : Prop :=
  ring_simple r -> ring_closed r -> ring_has_minimum_points r ->
  exists interior_pred exterior_pred : Point -> Prop,
    (* Off-ring points split into exactly one of the two components. *)
    (forall q, ~ ring_image r q ->
       (interior_pred q \/ exterior_pred q) /\
       ~ (interior_pred q /\ exterior_pred q)) /\
    (* Each component is connected by continuous complement paths. *)
    (forall a b, interior_pred a -> interior_pred b ->
       connected_in_complement_cont r a b) /\
    (forall a b, exterior_pred a -> exterior_pred b ->
       connected_in_complement_cont r a b) /\
    (* Separation (the trapped-interior half of the JCT): no continuous
       complement path links an interior point to an exterior one.  Without
       this clause the partition does not force an interior point into a
       *bounded* component -- one could continuously escape to the unbounded
       exterior -- so `geometric_interior_cont` would not be inhabited.  See
       `jct_cont_interior_is_geometric` (§5) for why this is exactly the
       clause that makes the corrected H1 hypothesis dischargeable rather
       than vacuous. *)
    (forall a b, interior_pred a -> exterior_pred b ->
       ~ connected_in_complement_cont r a b) /\
    (* The interior is bounded; the exterior is unbounded. *)
    (exists M, M > 0 /\ forall q, interior_pred q ->
       px q * px q + py q * py q <= M * M) /\
    (forall M, exists q, exterior_pred q /\
       px q * px q + py q * py q > M * M).

(* SCOPE CAVEAT (see theories/JCT_Counterexample.v +
   docs/jct-bowtie-counterexample.md).  The three structural premises above
   are NOT sufficient as written: `ring_simple` forbids only PROPER
   (interior-interior) crossings, so a self-touching ring -- e.g. the figure-8
   bowtie, two triangles meeting only at a shared vertex -- is `ring_simple`,
   `ring_closed` and has >= 4 vertices yet has THREE complement components.
   Hence `forall r, JCT_two_components_cont r` is false as stated.  The fix is
   `JCT_two_components_cont_simple` (ibid.), which adds the OGC vertex-
   distinctness premise `ring_vertices_distinct r := NoDup (removelast r)`
   (curve injectivity / every vertex degree 2) -- the half `ring_simple`
   omits.  Any downstream H1 that needs the two-component conclusion should be
   stated against the strengthened premise set. *)

(* -------------------------------------------------------------------------- *)
(* §4  The continuous relation is genuinely non-degenerate.                   *)
(*                                                                            *)
(* The vacuity of §2 was caused by discontinuity, not geometry.  With        *)
(* continuity required, the relation is no longer trivial -- but it is also  *)
(* not empty: two points right of the ring's bounding box are joined by an   *)
(* honest straight-line (hence continuous) path that never meets the ring.   *)
(* -------------------------------------------------------------------------- *)

Lemma straight_path_continuous :
  forall x0 y0 x1 y1,
    path_continuous
      (fun t => mkPoint ((1 - t) * x0 + t * x1) ((1 - t) * y0 + t * y1)).
Proof.
  intros. unfold path_continuous. split; cbn [px py]; reg.
Qed.

Lemma far_points_connected_cont :
  forall (r : Ring) (x0 x1 : R),
    x0 > edges_maxX (ring_edges r) ->
    x1 > edges_maxX (ring_edges r) ->
    connected_in_complement_cont r (mkPoint x0 0) (mkPoint x1 0).
Proof.
  intros r x0 x1 H0 H1.
  exists (fun t => mkPoint ((1 - t) * x0 + t * x1) ((1 - t) * 0 + t * 0)).
  split; [apply straight_path_continuous |]. split; [| split].
  - simpl. f_equal; lra.
  - simpl. f_equal; lra.
  - intros t Ht Himg. apply ring_image_px_bound in Himg. simpl in Himg.
    pose proof (convex_ge_min x0 x1 t Ht) as Hge.
    pose proof (Rmin_glb_lt x0 x1 (edges_maxX (ring_edges r)) H0 H1) as Hlt.
    lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Sufficiency: the corrected hypothesis inhabits the interior predicate. *)
(*                                                                            *)
(* `geometric_interior_stdlib` was *identically false* (§2), so re-pointing a *)
(* conditional headline's H1 onto it makes the headline vacuous /             *)
(* uninstantiable.  Here we show the corrected `JCT_two_components_cont`      *)
(* (now carrying the §3 separation clause) is strong enough to put every one  *)
(* of its interior points into `geometric_interior_cont`.  Consequence:       *)
(* re-pointing H1 onto `geometric_interior_cont` yields a GENUINE, satisfiable *)
(* obligation -- the honest JCT gap -- rather than a contradiction.           *)
(*                                                                            *)
(* This does NOT prove the JCT.  `JCT_two_components_cont` remains an unproved *)
(* `Prop` hypothesis (thesis-scale).  What is proved is the implication       *)
(* "JCT_two_components_cont  =>  interior points are geometric-interior",      *)
(* i.e. that the deferred hypothesis is the right (sufficient) target.        *)
(* The separation clause is load-bearing: drop it and this proof fails at the *)
(* `Hsep` step -- exactly mirroring the discontinuity defect it repairs.      *)
(* -------------------------------------------------------------------------- *)

Theorem jct_cont_interior_is_geometric :
  forall (r : Ring),
    ring_simple r -> ring_closed r -> ring_has_minimum_points r ->
    JCT_two_components_cont r ->
    exists interior_pred exterior_pred : Point -> Prop,
      (* the JCT partition (re-exposed for the caller) ... *)
      (forall q, ~ ring_image r q ->
         (interior_pred q \/ exterior_pred q) /\
         ~ (interior_pred q /\ exterior_pred q)) /\
      (* ... and the new payload: every interior point is geometric-interior. *)
      (forall p, interior_pred p -> geometric_interior_cont p r).
Proof.
  intros r Hs Hc Hm HJCT.
  destruct (HJCT Hs Hc Hm)
    as [ip [ep [Hpart [Hicon [_Hecon [Hsep [Hbnd _Hunb]]]]]]].
  exists ip, ep. split; [exact Hpart |].
  intros p Hip. unfold geometric_interior_cont.
  (* p is off the ring: the trivial loop path from p to itself witnesses it. *)
  assert (Hpoff : ring_complement r p).
  { destruct (Hicon p p Hip Hip) as [path [_ [Hp0 [_ Hin]]]].
    rewrite <- Hp0. apply Hin. lra. }
  split; [exact Hpoff |].
  (* in_bounded_component_cont: the interior bound M works because separation
     keeps every point reachable from p inside the (bounded) interior. *)
  destruct Hbnd as [M [HMpos HMbnd]].
  exists M. split; [exact HMpos |].
  intros q Hreach.
  (* q is off-ring: it is the t=1 endpoint of a complement path. *)
  assert (Hqoff : ring_complement r q).
  { destruct Hreach as [path [_ [_ [Hp1 Hin]]]].
    rewrite <- Hp1. apply Hin. lra. }
  (* q is interior: it cannot be exterior, by separation from p. *)
  destruct (Hpart q Hqoff) as [[Hqi | Hqe] _].
  - apply HMbnd. exact Hqi.
  - exfalso. apply (Hsep p q Hip Hqe). exact Hreach.
Qed.
