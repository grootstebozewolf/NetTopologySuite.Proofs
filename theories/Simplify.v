(* ============================================================================
   NetTopologySuite.Proofs.Simplify
   ----------------------------------------------------------------------------
   Greedy polyline simplification with a formal tolerance contract.

   First downstream consumer of `Linearise.polyline_length` and
   `Linearise.chord_le_detour`.  Two structures are defined:

     `simp_step eps`     -- a single greedy drop of one interior point whose
                            chord-deficit (dist p q + dist q r) - (dist p r)
                            is at most 2*eps.  Endpoints are preserved by
                            construction.

     `simp_star eps`     -- the reflexive-transitive closure of `simp_step`,
                            capturing "an iterated greedy simplification at
                            tolerance eps".

   The headline guarantees:

     1. `simp_step_preserves_head`:   a single drop preserves the first vertex.
     2. `simp_step_length_monotone`:  simplification never increases polyline
                                       length (single-step form).
     3. `simp_star_length_monotone`:  ... iterated form.
     4. `simp_star_preserves_head`:   ... iterated form for the endpoint.
     5. `simp_drop_here_length_deficit`:  exact length identity (sharper than
                                           the monotonicity bound).

   Length-monotonicity proofs do NOT use the tolerance hypothesis -- they
   hold for any single-point drop.  The tolerance hypothesis is the marker
   that downstream code uses to certify "this simplification is faithful
   within eps"; the eventual Hausdorff-bound proof (future slice) will be
   the one that consumes it.

   No Admitted, no Axiom (except the three classical-reals axioms inherited
   from the corpus's Real.v).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import List.
Import ListNotations.
From NTS.Proofs Require Import Distance Orientation Linearise.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* A single greedy simplification step: drop one interior point.              *)
(* -------------------------------------------------------------------------- *)

Inductive simp_step (eps : R) : list Point -> list Point -> Prop :=
  | simp_drop_here :
      forall p q r rest,
        dist p q + dist q r <= dist p r + 2 * eps ->
        simp_step eps (p :: q :: r :: rest) (p :: r :: rest)
  | simp_drop_later :
      forall p pts pts',
        simp_step eps pts pts' ->
        simp_step eps (p :: pts) (p :: pts').

(* -------------------------------------------------------------------------- *)
(* Iterated form: the reflexive-transitive closure of simp_step.              *)
(* -------------------------------------------------------------------------- *)

Inductive simp_star (eps : R) : list Point -> list Point -> Prop :=
  | simp_star_refl :
      forall pts, simp_star eps pts pts
  | simp_star_step :
      forall pts pts' pts'',
        simp_step eps pts pts' ->
        simp_star eps pts' pts'' ->
        simp_star eps pts pts''.

(* -------------------------------------------------------------------------- *)
(* Endpoint preservation (single step).                                       *)
(* Both simp_step constructors prepend the same head; immediate from cbn.    *)
(* -------------------------------------------------------------------------- *)

Theorem simp_step_preserves_head :
  forall eps pts pts',
    simp_step eps pts pts' ->
    forall default,
      hd default pts = hd default pts'.
Proof.
  intros eps pts pts' Hstep default.
  induction Hstep; cbn; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* simp_step's source has at least three points (so the dropped position is  *)
(* a genuine interior vertex).  Useful as a structural invariant in proofs   *)
(* that pattern-match on the source list.                                    *)
(* -------------------------------------------------------------------------- *)

Lemma simp_step_source_three :
  forall eps pts pts',
    simp_step eps pts pts' ->
    exists p q r tail, pts = p :: q :: r :: tail.
Proof.
  intros eps pts pts' Hstep.
  induction Hstep as [p q r rest _Hdef | p pts pts' Hinner IH].
  - exists p, q, r, rest. reflexivity.
  - destruct IH as [p0 [q0 [r0 [tail0 Heq]]]].
    exists p, p0, q0, (r0 :: tail0). cbn. rewrite Heq. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Companion shape lemma: simp_step's target has at least two points.        *)
(* -------------------------------------------------------------------------- *)

Lemma simp_step_target_two :
  forall eps pts pts',
    simp_step eps pts pts' ->
    exists p r tail, pts' = p :: r :: tail.
Proof.
  intros eps pts pts' Hstep.
  induction Hstep as [p q r rest _Hdef | p pts pts' Hinner IH].
  - exists p, r, rest. reflexivity.
  - destruct IH as [p0 [r0 [tail0 Heq]]].
    exists p, p0, (r0 :: tail0). cbn. rewrite Heq. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Headline: a single drop never increases polyline length.                  *)
(* Proof does NOT use the tolerance hypothesis -- holds for any drop.        *)
(* -------------------------------------------------------------------------- *)

Theorem simp_step_length_monotone :
  forall eps pts pts',
    simp_step eps pts pts' ->
    polyline_length pts' <= polyline_length pts.
Proof.
  intros eps pts pts' Hstep.
  induction Hstep as [p q r rest _Hdef | p pts pts' Hinner IH].
  - (* simp_drop_here: q dropped from [p; q; r; rest...]. *)
    pose proof (chord_le_detour p q r) as Tri.
    unfold polyline_length. cbn. lra.
  - (* simp_drop_later: the simp_step is on the tail. *)
    (* Both pts and pts' have the same head (q below) thanks to
       simp_step_preserves_head. *)
    pose proof (simp_step_source_three _ _ _ Hinner) as Hsrc.
    pose proof (simp_step_target_two   _ _ _ Hinner) as Htgt.
    destruct Hsrc as [p0 [q0 [r0 [tail0 Hsrc_eq]]]].
    destruct Htgt as [p1 [r1 [tail1 Htgt_eq]]].
    (* From simp_step_preserves_head: head of pts = head of pts', so p0 = p1. *)
    pose proof (simp_step_preserves_head _ _ _ Hinner p0) as Hhead.
    rewrite Hsrc_eq, Htgt_eq in Hhead. cbn in Hhead. subst p1.
    subst pts pts'.
    unfold polyline_length. cbn.
    unfold polyline_length in IH. cbn in IH.
    lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Iterated headline: simp_star never increases polyline length.             *)
(* -------------------------------------------------------------------------- *)

Theorem simp_star_length_monotone :
  forall eps pts pts',
    simp_star eps pts pts' ->
    polyline_length pts' <= polyline_length pts.
Proof.
  intros eps pts pts' Hstar.
  induction Hstar as [pts | pts pts' pts'' Hstep _ IH].
  - apply Rle_refl.
  - pose proof (simp_step_length_monotone _ _ _ Hstep) as Hone.
    lra.
Qed.

Theorem simp_star_preserves_head :
  forall eps pts pts',
    simp_star eps pts pts' ->
    forall default,
      hd default pts = hd default pts'.
Proof.
  intros eps pts pts' Hstar default.
  induction Hstar as [pts | pts pts' pts'' Hstep _ IH].
  - reflexivity.
  - rewrite (simp_step_preserves_head _ _ _ Hstep). exact IH.
Qed.

(* -------------------------------------------------------------------------- *)
(* Sharper than monotonicity: a single direct drop changes the length by    *)
(* exactly the chord-deficit at the dropped point.                          *)
(* -------------------------------------------------------------------------- *)

Theorem simp_drop_here_length_deficit :
  forall p q r rest,
    polyline_length (p :: q :: r :: rest) =
    polyline_length (p :: r :: rest) + (dist p q + dist q r - dist p r).
Proof.
  intros p q r rest.
  unfold polyline_length. cbn. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Last-vertex preservation.                                                  *)
(*                                                                            *)
(* simp_step never drops the last vertex of the list (it only drops the      *)
(* middle of an interior 3-window), so `last pts default = last pts'         *)
(* default`.  Companion to simp_step_preserves_head; together they pin down  *)
(* both endpoints of any simplification, which is the formal basis for the   *)
(* "adjacent TINs share boundary vertices" claim in Tin.v.                   *)
(* -------------------------------------------------------------------------- *)

Lemma last_cons_nonempty :
  forall (l : list Point) (a d : Point),
    l <> [] -> last (a :: l) d = last l d.
Proof.
  intros l a d Hne. destruct l as [| x xs].
  - contradiction.
  - cbn. reflexivity.
Qed.

Theorem simp_step_preserves_last :
  forall eps pts pts' default,
    simp_step eps pts pts' ->
    last pts default = last pts' default.
Proof.
  intros eps pts pts' d Hstep.
  induction Hstep as [p q r rest _Hdef | p pts pts' Hinner IH].
  - cbn. reflexivity.
  - assert (Hne_pts : pts <> []).
    { destruct (simp_step_source_three _ _ _ Hinner)
        as [p0 [q0 [r0 [tail Heq]]]].
      rewrite Heq. discriminate. }
    assert (Hne_pts' : pts' <> []).
    { destruct (simp_step_target_two _ _ _ Hinner)
        as [p0 [r0 [tail Heq]]].
      rewrite Heq. discriminate. }
    rewrite (last_cons_nonempty pts p d Hne_pts).
    rewrite (last_cons_nonempty pts' p d Hne_pts').
    exact IH.
Qed.

Theorem simp_star_preserves_last :
  forall eps pts pts' default,
    simp_star eps pts pts' ->
    last pts default = last pts' default.
Proof.
  intros eps pts pts' d Hstar.
  induction Hstar as [pts | pts pts' pts'' Hstep _ IH].
  - reflexivity.
  - rewrite (simp_step_preserves_last _ _ _ d Hstep). exact IH.
Qed.

(* -------------------------------------------------------------------------- *)
(* Perpendicular-distance variant of simp_step.                               *)
(*                                                                            *)
(* The original simp_step uses the chord-deficit test                         *)
(*     dist p q + dist q r <= dist p r + 2*eps                                *)
(* which bounds the length-cost of a drop.  The classical Douglas-Peucker    *)
(* algorithm (as used in the DEM-generalisation pipeline of                  *)
(*   Zygmunt & R\'og, Measurement 260 (2026) 119849,                          *)
(*   doi:10.1016/j.measurement.2025.119849)                                  *)
(* instead drops a point whose perpendicular distance from the chord pr is   *)
(* below eps.  The squared form of that test avoids sqrt:                    *)
(*     (cross p r q)^2 <= eps^2 * dist_sq p r.                                *)
(*                                                                            *)
(* The two tests do NOT coincide in general -- perpendicular distance to    *)
(* the *line* pr can be small even when q is far past either endpoint        *)
(* (chord deficit then blows up).  They agree when the foot of               *)
(* perpendicular falls inside segment pr, which is the typical               *)
(* Douglas-Peucker setting on a polyline.  We keep both inductive            *)
(* relations so downstream code can certify either flavour of                *)
(* simplifier under the SAME length-monotonicity theorem.                    *)
(* -------------------------------------------------------------------------- *)

Inductive simp_step_perp (eps : R) : list Point -> list Point -> Prop :=
  | simp_drop_here_perp :
      forall p q r rest,
        cross p r q * cross p r q <= eps * eps * dist_sq p r ->
        simp_step_perp eps (p :: q :: r :: rest) (p :: r :: rest)
  | simp_drop_later_perp :
      forall p pts pts',
        simp_step_perp eps pts pts' ->
        simp_step_perp eps (p :: pts) (p :: pts').

Inductive simp_star_perp (eps : R) : list Point -> list Point -> Prop :=
  | simp_star_perp_refl :
      forall pts, simp_star_perp eps pts pts
  | simp_star_perp_step :
      forall pts pts' pts'',
        simp_step_perp eps pts pts' ->
        simp_star_perp eps pts' pts'' ->
        simp_star_perp eps pts pts''.

(* Shape witnesses, mirroring the chord-deficit form. *)

Lemma simp_step_perp_source_three :
  forall eps pts pts',
    simp_step_perp eps pts pts' ->
    exists p q r tail, pts = p :: q :: r :: tail.
Proof.
  intros eps pts pts' Hstep.
  induction Hstep as [p q r rest _ | p pts pts' Hinner IH].
  - exists p, q, r, rest. reflexivity.
  - destruct IH as [p0 [q0 [r0 [tail0 Heq]]]].
    exists p, p0, q0, (r0 :: tail0). cbn. rewrite Heq. reflexivity.
Qed.

Lemma simp_step_perp_target_two :
  forall eps pts pts',
    simp_step_perp eps pts pts' ->
    exists p r tail, pts' = p :: r :: tail.
Proof.
  intros eps pts pts' Hstep.
  induction Hstep as [p q r rest _ | p pts pts' Hinner IH].
  - exists p, r, rest. reflexivity.
  - destruct IH as [p0 [r0 [tail0 Heq]]].
    exists p, p0, (r0 :: tail0). cbn. rewrite Heq. reflexivity.
Qed.

Theorem simp_step_perp_preserves_head :
  forall eps pts pts',
    simp_step_perp eps pts pts' ->
    forall default,
      hd default pts = hd default pts'.
Proof.
  intros eps pts pts' Hstep default.
  induction Hstep; cbn; reflexivity.
Qed.

Theorem simp_step_perp_length_monotone :
  forall eps pts pts',
    simp_step_perp eps pts pts' ->
    polyline_length pts' <= polyline_length pts.
Proof.
  intros eps pts pts' Hstep.
  induction Hstep as [p q r rest _Hperp | p pts pts' Hinner IH].
  - pose proof (chord_le_detour p q r) as Tri.
    unfold polyline_length. cbn. lra.
  - pose proof (simp_step_perp_source_three _ _ _ Hinner) as Hsrc.
    pose proof (simp_step_perp_target_two   _ _ _ Hinner) as Htgt.
    destruct Hsrc as [p0 [q0 [r0 [tail0 Hsrc_eq]]]].
    destruct Htgt as [p1 [r1 [tail1 Htgt_eq]]].
    pose proof (simp_step_perp_preserves_head _ _ _ Hinner p0) as Hhead.
    rewrite Hsrc_eq, Htgt_eq in Hhead. cbn in Hhead. subst p1.
    subst pts pts'.
    unfold polyline_length. cbn.
    unfold polyline_length in IH. cbn in IH.
    lra.
Qed.

Theorem simp_star_perp_length_monotone :
  forall eps pts pts',
    simp_star_perp eps pts pts' ->
    polyline_length pts' <= polyline_length pts.
Proof.
  intros eps pts pts' Hstar.
  induction Hstar as [pts | pts pts' pts'' Hstep _ IH].
  - apply Rle_refl.
  - pose proof (simp_step_perp_length_monotone _ _ _ Hstep) as Hone.
    lra.
Qed.

Theorem simp_star_perp_preserves_head :
  forall eps pts pts',
    simp_star_perp eps pts pts' ->
    forall default,
      hd default pts = hd default pts'.
Proof.
  intros eps pts pts' Hstar default.
  induction Hstar as [pts | pts pts' pts'' Hstep _ IH].
  - reflexivity.
  - rewrite (simp_step_perp_preserves_head _ _ _ Hstep). exact IH.
Qed.

(* Last-vertex preservation for the perpendicular variant. *)

Theorem simp_step_perp_preserves_last :
  forall eps pts pts' default,
    simp_step_perp eps pts pts' ->
    last pts default = last pts' default.
Proof.
  intros eps pts pts' d Hstep.
  induction Hstep as [p q r rest _Hperp | p pts pts' Hinner IH].
  - cbn. reflexivity.
  - assert (Hne_pts : pts <> []).
    { destruct (simp_step_perp_source_three _ _ _ Hinner)
        as [p0 [q0 [r0 [tail Heq]]]].
      rewrite Heq. discriminate. }
    assert (Hne_pts' : pts' <> []).
    { destruct (simp_step_perp_target_two _ _ _ Hinner)
        as [p0 [r0 [tail Heq]]].
      rewrite Heq. discriminate. }
    rewrite (last_cons_nonempty pts p d Hne_pts).
    rewrite (last_cons_nonempty pts' p d Hne_pts').
    exact IH.
Qed.

Theorem simp_star_perp_preserves_last :
  forall eps pts pts' default,
    simp_star_perp eps pts pts' ->
    last pts default = last pts' default.
Proof.
  intros eps pts pts' d Hstar.
  induction Hstar as [pts | pts pts' pts'' Hstep _ IH].
  - reflexivity.
  - rewrite (simp_step_perp_preserves_last _ _ _ d Hstep). exact IH.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                              *)
(* -------------------------------------------------------------------------- *)

Print Assumptions simp_step_length_monotone.
Print Assumptions simp_star_length_monotone.
Print Assumptions simp_step_preserves_head.
Print Assumptions simp_step_preserves_last.
Print Assumptions simp_step_perp_length_monotone.
Print Assumptions simp_star_perp_length_monotone.
