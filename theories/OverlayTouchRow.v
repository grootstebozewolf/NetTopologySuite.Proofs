(* ============================================================================
   NetTopologySuite.Proofs.OverlayTouchRow
   ----------------------------------------------------------------------------
   The OverlayNGCurve Phase 0 case matrix is NOT candidate complete — and
   the repaired matrix IS.  Prove-or-disprove, both halves Qed.

   The ops-mnemonics matrix (docs/overlay-ng-curve-ops-mnemonics.md) claims
   seven case rows decide every two-region overlay: self, empty partner,
   disjoint, covers, coveredBy, crossing, disc-vs-polygon.  At the region
   level over two POSITIVE-radius discs that is five relations
   (`phase0_relation`): equal, disjoint, covers, coveredBy, properly
   crossing (the empty-partner row is excluded by positive radii; the
   disc-vs-polygon row is representation, not relation).

   REFUTED (`phase0_relation_complete_hypothesis_refuted`): two externally
   TANGENT unit discs — centres (0,0) and (2,0) — fit no row.  They share
   the kiss point (1,0), so they are not disjoint; each holds a far point
   the other misses, so neither covers; and `discs_properly_intersect`
   demands STRICT |r1 − r2| < d < r1 + r2, which fails at d = r1 + r2.

   The degenerate op values at the kiss (the ledger's dimension collapse):
     CAP  lens      = exactly the singleton {(1,0)}   (a 2-D ∩ 2-D query
          collapsing to dimension 0 — `ext_cap_singleton`, by the sum of
          squares 2(x−1)² + 2y² ≤ 0; regularized CAP is ∅, and R1's
          "representable as CurvePolygon" is unmeetable for a point)
     CUP  blob      = exact as a set, but the shell SELF-TOUCHES at the
          kiss — V1's wound check territory (`ext_kiss_on_both_circles`)
     SUB  crescent  = the full disc minus ONE point (`ext_sub_off_by_point`)
     XOR  crescents = the blob minus ONE point (`ext_xor_off_by_point`)

   INTERNAL tangency — discs (0,0,r=2) ⊇ (1,0,r=1) touching at (2,0) — is
   NOT a completeness gap: the covers row fires (`int_covers`).  It is an
   ANSWER degeneracy: the SUB annulus pinches where inner and outer
   boundary meet (`int_kiss_pinch`), and the closed-region crescent misses
   the pinch point itself (`int_kiss_not_in_crescent`) — again V1.

   REPAIRED (`disc_relations_complete_with_touch`, the headline): adding
   ONE row — TOUCH := nonempty intersection with disjoint interiors —
   makes the matrix complete over positive discs:

       phase0_relation A B  \/  disks_touch A B      (total, Qed)

   by trichotomy on d against |r1 − r2| and r1 + r2: nested → covers
   (via `covers_of_reach`), strict between → properly crossing, beyond →
   disjoint, and d = r1 + r2 → touch, with the kiss witness constructed
   radially at c1 + (r1/d)(c2 − c1).  Internal tangency lands in covers,
   external tangency is EXACTLY the touch row — matching DISC_OVERLAY
   configs (INT_TANGENT/EXT_TANGENT, discriminant = 0 in exact Q,
   generator family E), which the driver classified before the R-side
   had a spec.  This module supplies that spec.

   Named pin (`candidate_complete`): a family R of disc-pair relations
   is candidate-complete when every positive-radius pair satisfies R.
   Distinct from op-exactness (`overlayng_curve_phase0_exact_cells`):
   classifying the pair is not CAP/CUP/SUB/XOR cells collapsing.
   `seven_row_family` is the relation content of the seven-row matrix
   on this domain (= `phase0_relation`); `eight_row_family` adds T-ext.
   The §3 / §6 theorems inhabit those names; no second headline.

   kiss ≠ CAP.  The TOUCH contact is a 0-cell pinch; CAP is the closed
   intersection.  On T-ext that intersection collapses to the kiss and
   is therefore not a 2-cell (`T_cap_not_2cell` / `T_ext_cap_not_2cell`).
   This is not G1 (CAP self, A ∩ A = A).  T-int is covers, not TOUCH:
   closed CAP is the smaller disc and HAS nonempty interior
   (`int_cap_is_2cell`) — do not claim int(CAP)=∅ for T-int.  Every
   TOUCH pair still has no II 2-cell (`touch_no_II_2cell`: interiors
   disjoint).  The false "every tangency, int(CAP)=∅" is refuted
   (`T_int_cap_empty_interior_hypothesis_refuted`).

   Radial pair (single definition site): `on_circle_radial_out` (used
   by T_cap_not_2cell) and `on_circle_radial_in` (used by the kiss
   obligation).  `region_not_2cell` is also defined only here.

   WITNESS topic: overlay · claimId: laser-ov · witness: kiss-discs
   WITNESS topic: overlay · claimId: ov-t-cap-not-2cell · witness: kiss-discs
   ADR-0001 tripwire not needed: Overlay → Distance only; this module
   is a consumer; no Overlay ↔ Jordan / ArcOrient cycle.

   Pure math on R.  Classical-reals trio only (see Print Assumptions).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Disk Overlay DiscOverlay.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The Phase 0 relations, and the missing one.                             *)
(* -------------------------------------------------------------------------- *)

Definition disks_same (A B : Disk) : Prop :=
  forall p, in_disk A p <-> in_disk B p.

Definition disks_disjoint (A B : Disk) : Prop :=
  forall p, ~ (in_disk A p /\ in_disk B p).

Definition disk_covers (A B : Disk) : Prop :=
  forall p, in_disk B p -> in_disk A p.

(** The five relation rows of the Phase 0 matrix (self, disjoint, covers,
    coveredBy, crossing) at region level. *)
Definition phase0_relation (A B : Disk) : Prop :=
  disks_same A B \/ disks_disjoint A B \/
  disk_covers A B \/ disk_covers B A \/
  discs_properly_intersect A B.

(** Open-disc membership: strictly inside. *)
Definition in_disk_int (D : Disk) (p : Point) : Prop :=
  dist_sq (dcentre D) p < dradius D * dradius D.

(** The missing row: the regions MEET but their interiors do not — one
    kiss, no shared flesh. *)
Definition disks_touch (A B : Disk) : Prop :=
  (exists p, in_disk A p /\ in_disk B p) /\
  (forall p, ~ (in_disk_int A p /\ in_disk_int B p)).

(** Candidate-complete: family R classifies every pair in the
    positive-radius disc-pair domain.  The seven-row exactness matrix
    (self, empty partner, disjoint, covers, coveredBy, crossing,
    disc-vs-polygon) contributes five relations here: empty-partner is
    excluded by positive radii; disc-vs-polygon is representation, not
    a disc-pair relation.  Those five are [phase0_relation].  Not
    op-exactness — see OverlayNGCurve.overlayng_curve_phase0_exact_cells. *)
Definition candidate_complete (R : Disk -> Disk -> Prop) : Prop :=
  forall A B : Disk, 0 < dradius A -> 0 < dradius B -> R A B.

Definition seven_row_family : Disk -> Disk -> Prop :=
  phase0_relation.

(** Seven-row relation content plus T-ext (TOUCH).  T-int is covers,
    not a new row. *)
Definition eight_row_family (A B : Disk) : Prop :=
  phase0_relation A B \/ disks_touch A B.

(* WITNESS {"claimId":"laser-ov","topic":"overlay","lemma":"candidate_complete","title":"Disc-pair candidate-complete = every positive-radius pair is classified","witness":"kiss-discs","board":"#1200"} *)

(* -------------------------------------------------------------------------- *)
(* §2  Metric bridges.                                                         *)
(* -------------------------------------------------------------------------- *)

Lemma dist_eq_of_sq : forall (c p : Point) (t : R),
  0 <= t -> dist_sq c p = t * t -> dist c p = t.
Proof.
  intros c p t Ht Hsq.
  pose proof (dist_nonneg c p) as Hd.
  pose proof (dist_mul_self c p) as Hm.
  assert (Hz : (dist c p - t) * (dist c p + t) = 0) by nra.
  destruct (Rmult_integral _ _ Hz) as [H | H]; lra.
Qed.

Lemma in_disk_int_dist : forall (D : Disk) (p : Point),
  0 < dradius D -> in_disk_int D p -> dist (dcentre D) p < dradius D.
Proof.
  intros D p Hr Hp. unfold in_disk_int in Hp.
  assert (Hle : dist (dcentre D) p <= dradius D)
    by (apply (proj2 (dist_le_iff_dist_sq_le _ _ _ (Rlt_le _ _ Hr))); lra).
  destruct (Req_dec (dist (dcentre D) p) (dradius D)) as [Heq | Hne]; [| lra].
  exfalso. pose proof (dist_mul_self (dcentre D) p) as Hm.
  rewrite Heq in Hm. lra.
Qed.

(** Containment from reach: if B's centre plus its radius stays within A's
    radius, A covers B — the workhorse for every nested case. *)
Lemma covers_of_reach : forall A B : Disk,
  0 <= dradius B ->
  dist (dcentre A) (dcentre B) + dradius B <= dradius A ->
  disk_covers A B.
Proof.
  intros A B HrB Hreach p Hp.
  assert (HrA : 0 <= dradius A).
  { pose proof (dist_nonneg (dcentre A) (dcentre B)). lra. }
  assert (HpB : dist (dcentre B) p <= dradius B)
    by (apply (proj2 (dist_le_iff_dist_sq_le _ _ _ HrB)); exact Hp).
  pose proof (dist_triangle (dcentre A) (dcentre B) p) as Ht.
  unfold in_disk.
  apply (proj1 (dist_le_iff_dist_sq_le _ _ _ HrA)).
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The counterexample: externally tangent unit discs.                      *)
(* -------------------------------------------------------------------------- *)

Definition ext_A : Disk := mkDisk (mkPoint 0 0) 1.
Definition ext_B : Disk := mkDisk (mkPoint 2 0) 1.
Definition ext_kiss : Point := mkPoint 1 0.

Lemma ext_kiss_in_A : in_disk ext_A ext_kiss.
Proof. unfold in_disk, ext_A, ext_kiss, dist_sq. cbn. lra. Qed.

Lemma ext_kiss_in_B : in_disk ext_B ext_kiss.
Proof. unfold in_disk, ext_B, ext_kiss, dist_sq. cbn. lra. Qed.

Lemma ext_not_disjoint : ~ disks_disjoint ext_A ext_B.
Proof.
  intro H. apply (H ext_kiss).
  split; [exact ext_kiss_in_A | exact ext_kiss_in_B].
Qed.

Lemma ext_not_covers : ~ disk_covers ext_A ext_B.
Proof.
  intro H.
  assert (Hin : in_disk ext_B (mkPoint 3 0))
    by (unfold in_disk, ext_B, dist_sq; cbn; lra).
  specialize (H (mkPoint 3 0) Hin).
  unfold in_disk, ext_A, dist_sq in H. cbn in H. lra.
Qed.

Lemma ext_not_coveredBy : ~ disk_covers ext_B ext_A.
Proof.
  intro H.
  assert (Hin : in_disk ext_A (mkPoint (-1) 0))
    by (unfold in_disk, ext_A, dist_sq; cbn; lra).
  specialize (H (mkPoint (-1) 0) Hin).
  unfold in_disk, ext_B, dist_sq in H. cbn in H. lra.
Qed.

Lemma ext_not_same : ~ disks_same ext_A ext_B.
Proof.
  intro H. apply ext_not_covers. intros p Hp. apply (proj2 (H p)). exact Hp.
Qed.

Lemma ext_centre_dist : dist (mkPoint 0 0) (mkPoint 2 0) = 2.
Proof.
  apply dist_eq_of_sq; [lra |]. unfold dist_sq. cbn. lra.
Qed.

Lemma ext_not_crossing : ~ discs_properly_intersect ext_A ext_B.
Proof.
  unfold discs_properly_intersect, ext_A, ext_B. cbn [dcentre dradius].
  intros (H1 & H2 & H3 & H4 & H5).
  rewrite ext_centre_dist in H5. lra.
Qed.

(** HEADLINE (negative half): the Phase 0 relation matrix misses the
    kissing pair — it is not candidate complete. *)
Theorem phase0_relation_complete_hypothesis_refuted :
  ~ (forall A B : Disk,
       0 < dradius A -> 0 < dradius B -> phase0_relation A B).
Proof.
  intro H.
  assert (HrA : 0 < dradius ext_A) by (cbn; lra).
  assert (HrB : 0 < dradius ext_B) by (cbn; lra).
  destruct (H ext_A ext_B HrA HrB) as
    [Hsame | [Hdisj | [Hcov | [Hcovby | Hcross]]]].
  - exact (ext_not_same Hsame).
  - exact (ext_not_disjoint Hdisj).
  - exact (ext_not_covers Hcov).
  - exact (ext_not_coveredBy Hcovby).
  - exact (ext_not_crossing Hcross).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The degenerate op values at the kiss (dimension collapse).              *)
(* -------------------------------------------------------------------------- *)

(** CAP collapses to dimension 0: the lens IS the kiss point.  The whole
    proof is the sum of squares 2(x−1)² + 2y² ≤ 0. *)
Theorem ext_cap_singleton :
  forall p, lens ext_A ext_B p <-> p = ext_kiss.
Proof.
  intros p. split.
  - destruct p as [x y].
    unfold lens, in_disk, ext_A, ext_B, dist_sq. cbn.
    intros [H1 H2].
    assert (Hx : x = 1) by nra.
    assert (Hy : y = 0) by nra.
    rewrite Hx, Hy. reflexivity.
  - intros ->. unfold lens.
    split; [exact ext_kiss_in_A | exact ext_kiss_in_B].
Qed.

(** So the regularized CAP (interior of the intersection) is empty. *)
Corollary ext_cap_interiors_empty :
  forall p, ~ (in_disk_int ext_A p /\ in_disk_int ext_B p).
Proof.
  intros [x y]. unfold in_disk_int, ext_A, ext_B, dist_sq. cbn.
  intros [H1 H2]. nra.
Qed.

(** SUB is the full disc minus exactly ONE point. *)
Theorem ext_sub_off_by_point :
  forall p, crescent ext_A ext_B p <-> (in_disk ext_A p /\ p <> ext_kiss).
Proof.
  intros p. unfold crescent. split.
  - intros [HA HnB]. split; [exact HA |].
    intros ->. exact (HnB ext_kiss_in_B).
  - intros [HA Hne]. split; [exact HA |].
    intro HB. apply Hne.
    exact (proj1 (ext_cap_singleton p) (conj HA HB)).
Qed.

(** XOR is the blob minus exactly ONE point. *)
Theorem ext_xor_off_by_point :
  forall p, crescents ext_A ext_B p <-> (blob ext_A ext_B p /\ p <> ext_kiss).
Proof.
  intros p. unfold crescents, crescent, blob. split.
  - intros [[HA HnB] | [HB HnA]].
    + split; [left; exact HA |]. intros ->. exact (HnB ext_kiss_in_B).
    + split; [right; exact HB |]. intros ->. exact (HnA ext_kiss_in_A).
  - intros [[HA | HB] Hne].
    + left. split; [exact HA |]. intro HB. apply Hne.
      exact (proj1 (ext_cap_singleton p) (conj HA HB)).
    + right. split; [exact HB |]. intro HA. apply Hne.
      exact (proj1 (ext_cap_singleton p) (conj HA HB)).
Qed.

(** CUP is exact as a set, but its shell self-touches: the kiss lies on
    BOTH bounding circles — the V1 wound-check configuration. *)
Lemma ext_kiss_on_both_circles :
  dist_sq (dcentre ext_A) ext_kiss = dradius ext_A * dradius ext_A /\
  dist_sq (dcentre ext_B) ext_kiss = dradius ext_B * dradius ext_B.
Proof.
  unfold ext_A, ext_B, ext_kiss, dist_sq. cbn. split; lra.
Qed.

(** The tangent pair does satisfy the repaired row. *)
Lemma ext_touch : disks_touch ext_A ext_B.
Proof.
  split.
  - exists ext_kiss. split; [exact ext_kiss_in_A | exact ext_kiss_in_B].
  - exact ext_cap_interiors_empty.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Internal tangency: covers fires, but the answer pinches.                *)
(* -------------------------------------------------------------------------- *)

Definition int_A : Disk := mkDisk (mkPoint 0 0) 2.
Definition int_B : Disk := mkDisk (mkPoint 1 0) 1.
Definition int_kiss : Point := mkPoint 2 0.

Lemma int_centre_dist : dist (mkPoint 0 0) (mkPoint 1 0) = 1.
Proof.
  apply dist_eq_of_sq; [lra |]. unfold dist_sq. cbn. lra.
Qed.

(** No completeness gap: the covers row of the matrix fires. *)
Lemma int_covers : disk_covers int_A int_B.
Proof.
  apply covers_of_reach; unfold int_A, int_B; cbn [dcentre dradius];
    [lra |].
  rewrite int_centre_dist. lra.
Qed.

Lemma int_not_crossing : ~ discs_properly_intersect int_A int_B.
Proof.
  unfold discs_properly_intersect, int_A, int_B. cbn [dcentre dradius].
  intros (H1 & H2 & H3 & H4 & H5).
  rewrite int_centre_dist in H4.
  rewrite Rabs_right in H4 by lra. lra.
Qed.

(** The answer degeneracy: the SUB annulus's inner and outer boundaries
    MEET at the kiss — the pinched shell V1 must reject. *)
Lemma int_kiss_pinch :
  dist_sq (dcentre int_A) int_kiss = dradius int_A * dradius int_A /\
  dist_sq (dcentre int_B) int_kiss = dradius int_B * dradius int_B.
Proof.
  unfold int_A, int_B, int_kiss, dist_sq. cbn. split; lra.
Qed.

(** And the closed-region crescent misses its own pinch point. *)
Lemma int_kiss_not_in_crescent : ~ crescent int_A int_B int_kiss.
Proof.
  intros [_ HnB]. apply HnB.
  unfold in_disk, int_B, int_kiss, dist_sq. cbn. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  The repaired matrix is complete (the positive half).                    *)
(* -------------------------------------------------------------------------- *)

(** HEADLINE: over positive-radius discs, Phase 0's five relations plus
    the ONE new TOUCH row decide every pair.  Trichotomy on the centre
    distance against |r1 − r2| and r1 + r2; the touch witness is the
    radial point c1 + (r1/d)(c2 − c1). *)
Theorem disc_relations_complete_with_touch :
  forall A B : Disk, 0 < dradius A -> 0 < dradius B ->
    phase0_relation A B \/ disks_touch A B.
Proof.
  intros A B HrA HrB.
  destruct A as [cA r1]. destruct B as [cB r2].
  cbn [dcentre dradius] in *.
  destruct (Rle_dec (dist cA cB) (Rabs (r1 - r2))) as [Hnest | Hnotnest].
  - (* nested (incl. internal tangency and concentric): covers/coveredBy *)
    destruct (Rle_dec r2 r1) as [Hr21 | Hr12].
    + left. right. right. left.
      apply covers_of_reach; cbn [dcentre dradius]; [lra |].
      rewrite Rabs_right in Hnest by lra. lra.
    + left. right. right. right. left.
      apply covers_of_reach; cbn [dcentre dradius]; [lra |].
      rewrite Rabs_left in Hnest by lra.
      rewrite (dist_sym cB cA). lra.
  - destruct (Rtotal_order (dist cA cB) (r1 + r2)) as [Hlt | [Heq | Hgt]].
    + (* strictly between: properly crossing *)
      left. do 4 right.
      unfold discs_properly_intersect. cbn [dcentre dradius].
      pose proof (Rabs_pos (r1 - r2)).
      repeat split; lra.
    + (* external tangency: the TOUCH row *)
      right.
      assert (Hdpos : 0 < dist cA cB) by lra.
      assert (Hdne : dist cA cB <> 0) by lra.
      pose proof (dist_mul_self cA cB) as Hd2.
      split.
      * set (K := mkPoint
                    (px cA + (r1 / dist cA cB) * (px cB - px cA))
                    (py cA + (r1 / dist cA cB) * (py cB - py cA))).
        assert (HKA : dist_sq cA K
                      = (r1 / dist cA cB) * (r1 / dist cA cB)
                        * dist_sq cA cB).
        { unfold K, dist_sq. cbn [px py]. ring. }
        assert (HKB : dist_sq cB K
                      = (1 - r1 / dist cA cB) * (1 - r1 / dist cA cB)
                        * dist_sq cA cB).
        { unfold K, dist_sq. cbn [px py]. ring. }
        assert (HKA2 : dist_sq cA K = r1 * r1).
        { rewrite HKA, <- Hd2. field. exact Hdne. }
        assert (HKB2 : dist_sq cB K = r2 * r2).
        { rewrite HKB, <- Hd2.
          replace r2 with (dist cA cB - r1) by lra.
          field. exact Hdne. }
        exists K. unfold in_disk. cbn [dcentre dradius].
        rewrite HKA2, HKB2. split; lra.
      * intros p [HiA HiB].
        apply in_disk_int_dist in HiA; cbn [dcentre dradius] in HiA;
          [| cbn; lra].
        apply in_disk_int_dist in HiB; cbn [dcentre dradius] in HiB;
          [| cbn; lra].
        pose proof (dist_triangle cA p cB) as Ht.
        rewrite (dist_sym p cB) in Ht. lra.
    + (* beyond the sum: disjoint *)
      left. right. left.
      intros p [HpA HpB].
      unfold in_disk in HpA, HpB. cbn [dcentre dradius] in HpA, HpB.
      assert (HdA : dist cA p <= r1)
        by (apply (proj2 (dist_le_iff_dist_sq_le _ _ _ (Rlt_le _ _ HrA)));
            exact HpA).
      assert (HdB : dist cB p <= r2)
        by (apply (proj2 (dist_le_iff_dist_sq_le _ _ _ (Rlt_le _ _ HrB)));
            exact HpB).
      pose proof (dist_triangle cA p cB) as Ht.
      rewrite (dist_sym p cB) in Ht. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6b  Named predicate applied to the two families.                           *)
(*      Not a second headline: unfolds of the §3 / §6 theorems.                *)
(* -------------------------------------------------------------------------- *)

Lemma seven_row_not_candidate_complete :
  ~ candidate_complete seven_row_family.
Proof. exact phase0_relation_complete_hypothesis_refuted. Qed.

Lemma eight_row_is_candidate_complete :
  candidate_complete eight_row_family.
Proof. exact disc_relations_complete_with_touch. Qed.

Lemma t_ext_misses_seven_row : ~ seven_row_family ext_A ext_B.
Proof.
  intros [Hsame | [Hdisj | [Hcov | [Hcovby | Hcross]]]].
  - exact (ext_not_same Hsame).
  - exact (ext_not_disjoint Hdisj).
  - exact (ext_not_covers Hcov).
  - exact (ext_not_coveredBy Hcovby).
  - exact (ext_not_crossing Hcross).
Qed.

Lemma t_ext_is_eight_row_touch : eight_row_family ext_A ext_B.
Proof. right. exact ext_touch. Qed.

Lemma t_int_is_covers_not_a_gap : seven_row_family int_A int_B.
Proof.
  unfold seven_row_family, phase0_relation.
  right. right. left. exact int_covers.
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  TOUCH CAP is not a 2-cell.                                              *)
(*                                                                            *)
(* kiss ≠ CAP; this is not G1.  T-int does not get a false int(CAP)=∅          *)
(* claim: internal tangency is covers, and closed CAP is the smaller disc.     *)
(* -------------------------------------------------------------------------- *)

(** No open disc sits inside S — Euclidean interior empty; S is not a
    2-cell of the overlay arrangement.  Same shape as
    RelateTouchDiscs.region_no_ball; defined here so this overlay
    module does not import the relate lane. *)
Definition region_not_2cell (S : Point -> Prop) : Prop :=
  forall q rho, 0 < rho -> exists p, dist_sq q p < rho * rho /\ ~ S p.

(** Radial outward nudge: a positive-radius circle point has nearby
    points strictly outside the closed disc. *)
Lemma on_circle_radial_out :
  forall (c : Point) (r : R) (q : Point) (rho : R),
    0 < r ->
    0 < rho ->
    dist_sq c q = r * r ->
    exists p, dist_sq q p < rho * rho /\ r * r < dist_sq c p.
Proof.
  intros c r q rho Hr Hrho Hon.
  set (t := rho / (2 * r)).
  assert (Ht : 0 < t) by (unfold t; apply Rdiv_lt_0_compat; lra).
  set (p := mkPoint (px c + (1 + t) * (px q - px c))
                    (py c + (1 + t) * (py q - py c))).
  assert (Hcp : dist_sq c p = (1 + t) * (1 + t) * dist_sq c q).
  { unfold p, dist_sq. cbn [px py]. ring. }
  assert (Hqp : dist_sq q p = t * t * dist_sq c q).
  { unfold p, dist_sq. cbn [px py]. ring. }
  exists p. split.
  - rewrite Hqp, Hon.
    unfold t.
    assert (Hexp : rho / (2 * r) * (rho / (2 * r)) * (r * r)
                   = rho * rho / 4) by (field; lra).
    rewrite Hexp. nra.
  - rewrite Hcp, Hon.
    replace ((1 + t) * (1 + t) * (r * r))
      with (r * r + (2 * t + t * t) * (r * r)) by ring.
    assert (Hpos : 0 < (2 * t + t * t) * (r * r)).
    { apply Rmult_lt_0_compat; nra. }
    lra.
Qed.

(** Inward dual of [on_circle_radial_out]: a positive-radius circle
    point has nearby points strictly inside the open disc. *)
Lemma on_circle_radial_in :
  forall (c : Point) (r : R) (q : Point) (rho : R),
    0 < r ->
    0 < rho ->
    dist_sq c q = r * r ->
    exists p, dist_sq q p < rho * rho /\ dist_sq c p < r * r.
Proof.
  intros c r q rho Hr Hrho Hon.
  set (t := Rmin (rho / (2 * r)) (1 / 2)).
  assert (Ht : 0 < t).
  { unfold t. apply Rmin_glb_lt.
    - apply Rdiv_lt_0_compat; lra.
    - lra. }
  assert (Ht1 : t <= 1 / 2) by apply Rmin_r.
  assert (Htr : t <= rho / (2 * r)) by apply Rmin_l.
  set (p := mkPoint (px c + (1 - t) * (px q - px c))
                    (py c + (1 - t) * (py q - py c))).
  assert (Hcp : dist_sq c p = (1 - t) * (1 - t) * dist_sq c q).
  { unfold p, dist_sq. cbn [px py]. ring. }
  assert (Hqp : dist_sq q p = t * t * dist_sq c q).
  { unfold p, dist_sq. cbn [px py]. ring. }
  exists p. split.
  - rewrite Hqp, Hon.
    unfold t in Htr.
    assert (Hexp : (rho / (2 * r)) * (rho / (2 * r)) * (r * r)
                   = rho * rho / 4) by (field; lra).
    assert (Hle : t * t * (r * r)
                  <= (rho / (2 * r)) * (rho / (2 * r)) * (r * r)).
    { apply Rmult_le_compat_r.
      - nra.
      - apply Rmult_le_compat; try lra; exact Htr. }
    rewrite Hexp in Hle. nra.
  - rewrite Hcp, Hon.
    assert (Hlt : 0 < t < 1) by lra.
    replace ((1 - t) * (1 - t) * (r * r))
      with (r * r - (2 * t - t * t) * (r * r)) by ring.
    assert (Hpos : 0 < (2 * t - t * t) * (r * r)).
    { apply Rmult_lt_0_compat; nra. }
    lra.
Qed.

(** A singleton region contains no open disc. *)
Lemma singleton_not_2cell : forall (S : Point -> Prop) (k : Point),
  (forall p, S p -> p = k) ->
  region_not_2cell S.
Proof.
  intros S k Hsub q rho Hrho.
  destruct (Req_dec (px q) (px k)) as [Hx | Hnx];
    destruct (Req_dec (py q) (py k)) as [Hy | Hny].
  - set (p := mkPoint (px k + rho / 2) (py k)).
    exists p. split.
    + unfold p, dist_sq. cbn [px py].
      replace (px q - (px k + rho / 2)) with (- (rho / 2))
        by (rewrite Hx; ring).
      replace (py q - py k) with 0 by (rewrite Hy; ring).
      nra.
    + intros HS. apply Hsub in HS.
      assert (Hpx : px p = px k) by (rewrite HS; reflexivity).
      unfold p in Hpx. cbn [px] in Hpx. lra.
  - exists q. split.
    + rewrite dist_sq_self_zero. nra.
    + intros HS. apply Hsub in HS. apply Hny. rewrite HS. reflexivity.
  - exists q. split.
    + rewrite dist_sq_self_zero. nra.
    + intros HS. apply Hsub in HS. apply Hnx. rewrite HS. reflexivity.
  - exists q. split.
    + rewrite dist_sq_self_zero. nra.
    + intros HS. apply Hsub in HS. apply Hnx. rewrite HS. reflexivity.
Qed.

(** Fixture T-ext: CAP = {kiss} so the Euclidean interior is empty. *)
Corollary T_ext_cap_not_2cell : region_not_2cell (lens ext_A ext_B).
Proof.
  apply (singleton_not_2cell _ ext_kiss).
  intros p Hp. apply ext_cap_singleton. exact Hp.
Qed.

(* WITNESS {"claimId":"ov-t-cap-not-2cell","topic":"overlay","lemma":"T_cap_not_2cell","title":"On disks_touch, CAP contains no open disc (not a 2-cell); T-int scoped out","witness":"kiss-discs","board":"OverlayNGCurve / G-family"} *)

(** HEADLINE.  On TOUCH (T-ext for discs), closed CAP = A ∩ B contains
    no open disc: there is no II 2-cell of the overlay arrangement.
    Not G1.  T-int is out of scope — see [int_cap_is_2cell]. *)
Theorem T_cap_not_2cell : forall A B : Disk,
  0 < dradius A -> 0 < dradius B ->
  disks_touch A B ->
  region_not_2cell (lens A B).
Proof.
  intros A B HrA HrB [Hmeet Hii] q rho Hrho.
  destruct (Rle_dec (dist_sq (dcentre A) q) (dradius A * dradius A))
    as [HA | HnA].
  - destruct (Rle_dec (dist_sq (dcentre B) q) (dradius B * dradius B))
      as [HB | HnB].
    + destruct (Rlt_dec (dist_sq (dcentre A) q) (dradius A * dradius A))
        as [HiA | HnAi].
      * destruct (Rlt_dec (dist_sq (dcentre B) q) (dradius B * dradius B))
          as [HiB | HnBi].
        -- exfalso. apply (Hii q).
           split; [exact HiA | exact HiB].
        -- assert (HeqB : dist_sq (dcentre B) q = dradius B * dradius B)
             by lra.
           destruct (on_circle_radial_out (dcentre B) (dradius B) q rho
                       HrB Hrho HeqB) as [p [Hball Hout]].
           exists p. split; [exact Hball |].
           intros [_ HBp]. unfold in_disk in HBp. lra.
      * assert (HeqA : dist_sq (dcentre A) q = dradius A * dradius A)
          by lra.
        destruct (on_circle_radial_out (dcentre A) (dradius A) q rho
                    HrA Hrho HeqA) as [p [Hball Hout]].
        exists p. split; [exact Hball |].
        intros [HAp _]. unfold in_disk in HAp. lra.
    + exists q. split.
      * rewrite dist_sq_self_zero. nra.
      * intros [_ HB]. exact (HnB HB).
  - exists q. split.
    + rewrite dist_sq_self_zero. nra.
    + intros [HA _]. exact (HnA HA).
Qed.

(** (C) All TOUCH: no II 2-cell — interiors are disjoint.  Definitional
    from [disks_touch]; kiss ≠ shared flesh.  Does not claim int(CAP)=∅
    for T-int. *)
Corollary touch_no_II_2cell : forall A B : Disk,
  disks_touch A B ->
  forall p, ~ (in_disk_int A p /\ in_disk_int B p).
Proof.
  intros A B [_ Hii]. exact Hii.
Qed.

(** Honesty pin: T-int closed CAP is the covered smaller disc and HAS
    a metric ball — int(CAP)=∅ is FALSE for internal tangency. *)
Lemma int_cap_is_2cell :
  exists q rho, 0 < rho /\
    forall p, dist_sq q p < rho * rho -> lens int_A int_B p.
Proof.
  exists (mkPoint 1 0), (1 / 2). split; [lra |].
  intros [x y] Hp.
  unfold dist_sq in Hp. cbn in Hp.
  unfold lens, in_disk, int_A, int_B, dist_sq. cbn [dcentre dradius px py].
  split; nra.
Qed.

(** QEX of the false general headline "every tangency, int(CAP)=∅".
    Internal tangency (d = |r1 − r2|) is the cex: CAP is a 2-cell. *)
Theorem T_int_cap_empty_interior_hypothesis_refuted :
  ~ (forall A B : Disk,
       0 < dradius A -> 0 < dradius B ->
       dist (dcentre A) (dcentre B) = Rabs (dradius A - dradius B) ->
       region_not_2cell (lens A B)).
Proof.
  intro H.
  assert (HrA : 0 < dradius int_A) by (cbn; lra).
  assert (HrB : 0 < dradius int_B) by (cbn; lra).
  assert (Htang : dist (dcentre int_A) (dcentre int_B)
                  = Rabs (dradius int_A - dradius int_B)).
  { cbn [dcentre dradius int_A int_B].
    rewrite int_centre_dist. rewrite Rabs_right; lra. }
  specialize (H int_A int_B HrA HrB Htang).
  destruct int_cap_is_2cell as [q [rho [Hrho Hball]]].
  destruct (H q rho Hrho) as [p [Hin Hn]].
  exact (Hn (Hball p Hin)).
Qed.

(* -------------------------------------------------------------------------- *)
(* §8  Audit footprint (classical-reals trio only).                            *)
(* -------------------------------------------------------------------------- *)

Print Assumptions phase0_relation_complete_hypothesis_refuted.
Print Assumptions ext_cap_singleton.
Print Assumptions ext_sub_off_by_point.
Print Assumptions ext_xor_off_by_point.
Print Assumptions ext_touch.
Print Assumptions int_covers.
Print Assumptions int_kiss_pinch.
Print Assumptions disc_relations_complete_with_touch.
Print Assumptions seven_row_not_candidate_complete.
Print Assumptions eight_row_is_candidate_complete.
Print Assumptions t_ext_misses_seven_row.
Print Assumptions t_int_is_covers_not_a_gap.
Print Assumptions on_circle_radial_out.
Print Assumptions on_circle_radial_in.
Print Assumptions T_ext_cap_not_2cell.
Print Assumptions T_cap_not_2cell.
Print Assumptions touch_no_II_2cell.
Print Assumptions int_cap_is_2cell.
Print Assumptions T_int_cap_empty_interior_hypothesis_refuted.
