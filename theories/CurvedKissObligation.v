(* ============================================================================
   NetTopologySuite.Proofs.CurvedKissObligation
   ----------------------------------------------------------------------------
   Named modulo-QEX for two-body kiss on curved polygons after exact noding.

   Domain.  Pairs of curved polygons whose boundaries are finite unions of
   curve segments (chords and/or circular arcs), filled by the corpus
   Jordan/parity convention.  Positive-radius closed discs inhabit the
   domain as two-semicircle CurvePolygons whose fill is Disk.in_disk
   (reused from CurvedCapObligation — no reminted radical/disc stack).

   Kiss (relation).  cl(A) ∩ cl(B) ≠ ∅ ∧ int(A) ∩ int(B) = ∅.  On discs
   that is OverlayTouchRow.disks_touch.  kiss ≠ CAP; kiss ≠ self-kiss
   (#678); two-body T ≠ G1.

   External vs internal (containment of closures).
     * External: kiss and neither closure contains the other — on discs
       this is T-ext / TOUCH (`disks_touch`).
     * Internal tangency: one closure contains the other.  On discs that
       is the covers row, not TOUCH — interiors meet, so it is not kiss.
       The pinch sits on the shared boundary (`int_kiss_pinch`).  T-int
       CAP may have area (#677 refuted ∀tangency int(CAP)=∅).

   Conclusion (QEX until proved in general).  After exact noding of
   ∂A ∪ ∂B, kiss holds iff the extracted overlay has a boundary–boundary
   contact and no interior–interior 2-cell, and the external/internal
   split matches containment of closures.

   Honest recording (not CircGamma).  The obligation is a Prop/Record
   with domain + noding hyp + the kiss ↔ (BB ∧ no II) conclusion — not
   a status flag, not `ticket = QED \/ QEX` by `right`.  No new Axiom.
   The general CurvePolygon statement is the named residual
   `curved_kiss_on_curve_polygons`; we do not inhabit it (noding + BB
   extract are not constructed).  What is Qed:

     * `bodies_kiss_disc_iff_touch` — on discs the geometric kiss *is*
       `disks_touch`;
     * `disks_touch_iff_bb_and_no_II` — kiss ↔ (circle–circle contact
       ∧ interiors disjoint);
     * `disks_touch_no_II` / `disks_touch_cap_not_2cell` — reuse
       `touch_no_II_2cell` / `T_cap_not_2cell` (no remint);
     * `disks_touch_is_external` — T-ext is kiss and neither covers;
     * `t_int_is_covers_not_kiss` — T-int is covers, not TOUCH;
     * `t_ext_kiss` / `disc_kiss_eight_row_complete` — fixture + the
       already-Qed eight-row completeness;
     * `two_disc_kiss_discharges_curved_obligation` — Record inhabited
       on positive-radius discs (noding = radical-node uniqueness);
     * `curved_kiss_modulo_qex` — that inhabitant is equivalent to the
       already-Qed BB ∧ no-II identity (the remaining stop, restricted
       to discs);
     * `kiss_touch_cap_faces_not_II` — thin reuse of
       `touch_cap_faces_not_II` (do not duplicate the CAP-face argument).

   Not attempted: general curved noding, arrangement-face BB extract,
   OverlayNGCurve product wire, Merkator, atan2, CircGamma.

   WITNESS topic: overlay · claimId: ov-curved-kiss-qex
   witness: kiss-discs · board: OverlayNGCurve / G-family

   Full-only: imports CurvedCapObligation (and thus OverlayTouchRow /
   DiscOverlay).  Classical-reals trio only (see Print Assumptions).
   No new axioms.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Disk Overlay CurveGeometry
                               DiscOverlay OverlayTouchRow CurvedCapObligation.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Point-set kiss and the external / internal split.                      *)
(*                                                                            *)
(* cl = closed fill; int = specified open interior (supplied).  On discs      *)
(* those are [in_disk] / [in_disk_int].  Containment of closures is           *)
(* [fill_covers] — the same relation as [disk_covers] on disc fills.          *)
(* -------------------------------------------------------------------------- *)

Definition bodies_kiss (clA clB intA intB : Point -> Prop) : Prop :=
  (exists p, clA p /\ clB p) /\
  (forall p, ~ (intA p /\ intB p)).

Definition fill_covers (A B : CurvedFilled) : Prop :=
  forall p, cf_fill B p -> cf_fill A p.

(** External kiss: meet on the closures, interiors disjoint, neither
    closure contains the other. *)
Definition kiss_external (clA clB intA intB : Point -> Prop) : Prop :=
  bodies_kiss clA clB intA intB /\
  ~ (forall p, clB p -> clA p) /\
  ~ (forall p, clA p -> clB p).

(** Internal contact of closures (containment).  On discs this is the
    covers row — not kiss, because interiors meet. *)
Definition closure_internal (clA clB : Point -> Prop) : Prop :=
  (forall p, clB p -> clA p) \/ (forall p, clA p -> clB p).

Definition disc_on_circle (D : Disk) (p : Point) : Prop :=
  dist_sq (dcentre D) p = dradius D * dradius D.

Definition disc_bb_contact (A B : Disk) : Prop :=
  exists p, disc_on_circle A p /\ disc_on_circle B p.

Definition disc_no_II (A B : Disk) : Prop :=
  forall p, ~ (in_disk_int A p /\ in_disk_int B p).

(* -------------------------------------------------------------------------- *)
(* §2  The obligation — domain + noding + kiss ↔ (BB ∧ no II).                *)
(*                                                                            *)
(* [extracted_bb] / [extracted_no_II] are whatever a noder+extractor          *)
(* would emit (BB contact; no II 2-cell).  [intA]/[intB] are the              *)
(* specified interiors.  On discs those extracts are [disc_bb_contact]        *)
(* and [disc_no_II]; the noding hyp is [disc_pair_exactly_noded] (reused).    *)
(* The Record is the remaining stop; it is not a status enum.                 *)
(* -------------------------------------------------------------------------- *)

Record CurvedKissExactNodingObligation
    (A B : CurvedFilled)
    (intA intB : Point -> Prop)
    (H_exact_noding : Prop)
    (extracted_bb : Prop)
    (extracted_no_II : Prop) : Prop :=
  mk_curved_kiss_obligation {
    cko_domain : curved_filled_domain A B;
    cko_noding : H_exact_noding;
    cko_kiss_iff :
      bodies_kiss (cf_fill A) (cf_fill B) intA intB
      <-> (extracted_bb /\ extracted_no_II)
  }.

(** Named obligation Prop (Definition alias of the Record — the claims
    gate scans Definition/Theorem, not Record). *)
Definition curved_kiss_exact_noding_obligation :=
  CurvedKissExactNodingObligation.

(* -------------------------------------------------------------------------- *)
(* §3  Residual QEX on CurvePolygon.                                          *)
(*                                                                            *)
(* Same obligation on a CurvePolygon pair with abstract Jordan/parity         *)
(* fill and specified interiors (not [to_geometry] chord approximation).      *)
(* Domain is inhabited from [valid_curve_polygon].  Noding + BB extract       *)
(* are not constructed — that is the named remaining stop.                    *)
(* -------------------------------------------------------------------------- *)

Definition curved_kiss_on_curve_polygons (A B : CurvePolygon)
    (fillA fillB intA intB : Point -> Prop)
    (H_exact_noding : Prop)
    (extracted_bb extracted_no_II : Prop) : Prop :=
  valid_curve_polygon A ->
  valid_curve_polygon B ->
  curved_kiss_exact_noding_obligation
    (curve_polygon_filled A fillA)
    (curve_polygon_filled B fillB)
    intA intB
    H_exact_noding
    extracted_bb
    extracted_no_II.

Lemma valid_curve_polygon_inhabits_kiss_domain :
  forall (A B : CurvePolygon) (fillA fillB : Point -> Prop),
    valid_curve_polygon A ->
    valid_curve_polygon B ->
    curved_filled_domain (curve_polygon_filled A fillA)
                         (curve_polygon_filled B fillB).
Proof.
  intros A B fillA fillB.
  apply valid_curve_polygon_inhabits_domain.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Disc slice — geometric kiss is [disks_touch].                          *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"ov-curved-kiss-qex","topic":"overlay","lemma":"bodies_kiss_disc_iff_touch","title":"On full discs the geometric kiss is disks_touch","file":"theories/CurvedKissObligation.v","witness":"kiss-discs","board":"OverlayNGCurve / G-family"} *)

Theorem bodies_kiss_disc_iff_touch :
  forall A B : Disk,
    bodies_kiss (in_disk A) (in_disk B) (in_disk_int A) (in_disk_int B)
    <-> disks_touch A B.
Proof.
  intros A B. reflexivity.
Qed.

Theorem fill_covers_disc_iff :
  forall A B : Disk,
    fill_covers (disc_filled A) (disc_filled B) <-> disk_covers A B.
Proof.
  intros A B. reflexivity.
Qed.

Lemma disc_on_circle_in_disk :
  forall (D : Disk) (p : Point),
    disc_on_circle D p -> in_disk D p.
Proof.
  intros D p H. unfold in_disk, disc_on_circle in *. lra.
Qed.

Lemma closed_not_int_on_circle :
  forall (D : Disk) (p : Point),
    in_disk D p -> ~ in_disk_int D p -> disc_on_circle D p.
Proof.
  intros D p Hin Hn. unfold in_disk, in_disk_int, disc_on_circle in *. lra.
Qed.

Lemma in_disk_int_centre :
  forall D : Disk, 0 < dradius D -> in_disk_int D (dcentre D).
Proof.
  intros D Hr. unfold in_disk_int.
  rewrite dist_sq_self_zero. nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Open-disc ball and inward radial step (dual of on_circle_radial_out).  *)
(* -------------------------------------------------------------------------- *)

Lemma in_disk_int_open :
  forall (D : Disk) (p : Point),
    0 < dradius D ->
    in_disk_int D p ->
    exists rho, 0 < rho /\
      forall q, dist_sq p q < rho * rho -> in_disk_int D q.
Proof.
  intros D p Hr Hin.
  pose proof (in_disk_int_dist D p Hr Hin) as Hdp.
  set (rho := (dradius D - dist (dcentre D) p) / 2).
  assert (Hrho : 0 < rho) by (unfold rho; lra).
  exists rho. split; [exact Hrho|].
  intros q Hq.
  unfold in_disk_int.
  apply (proj1 (dist_lt_iff_dist_sq_lt (dcentre D) q (dradius D)
                 (Rlt_le _ _ Hr))).
  pose proof (dist_triangle (dcentre D) p q) as Ht.
  assert (Hpq : dist p q < rho).
  { apply (proj2 (dist_lt_iff_dist_sq_lt p q rho (Rlt_le _ _ Hrho))).
    exact Hq. }
  unfold rho in Hpq. lra.
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

Lemma int_and_other_circle_meets_II :
  forall (A B : Disk) (p : Point),
    0 < dradius A ->
    0 < dradius B ->
    in_disk_int A p ->
    disc_on_circle B p ->
    exists q, in_disk_int A q /\ in_disk_int B q.
Proof.
  intros A B p HrA HrB HinA HonB.
  destruct (in_disk_int_open A p HrA HinA) as [rho [Hrho Hall]].
  destruct (on_circle_radial_in (dcentre B) (dradius B) p rho
              HrB Hrho HonB) as [q [Hball Hinin]].
  exists q. split.
  - apply Hall. exact Hball.
  - unfold in_disk_int. exact Hinin.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  TOUCH ⇒ BB contact; kiss ↔ (BB ∧ no II) on discs.                      *)
(* -------------------------------------------------------------------------- *)

Lemma touch_point_on_both_circles :
  forall (A B : Disk) (p : Point),
    0 < dradius A ->
    0 < dradius B ->
    disks_touch A B ->
    in_disk A p ->
    in_disk B p ->
    disc_on_circle A p /\ disc_on_circle B p.
Proof.
  intros A B p HrA HrB [_ Hii] HA HB.
  split.
  - apply closed_not_int_on_circle; [exact HA|].
    intros HiA.
    destruct (Rlt_dec (dist_sq (dcentre B) p) (dradius B * dradius B))
      as [HiB | HnB].
    + apply (Hii p). split; [exact HiA | exact HiB].
    + assert (HonB : disc_on_circle B p).
      { apply closed_not_int_on_circle; [exact HB|].
        unfold in_disk_int. lra. }
      destruct (int_and_other_circle_meets_II A B p HrA HrB HiA HonB)
        as [q Hq].
      apply (Hii q). exact Hq.
  - apply closed_not_int_on_circle; [exact HB|].
    intros HiB.
    destruct (Rlt_dec (dist_sq (dcentre A) p) (dradius A * dradius A))
      as [HiA | HnA].
    + apply (Hii p). split; [exact HiA | exact HiB].
    + assert (HonA : disc_on_circle A p).
      { apply closed_not_int_on_circle; [exact HA|].
        unfold in_disk_int. lra. }
      destruct (int_and_other_circle_meets_II B A p HrB HrA HiB HonA)
        as [q [HqB HqA]].
      apply (Hii q). split; [exact HqA | exact HqB].
Qed.

Lemma disks_touch_bb_contact :
  forall A B : Disk,
    0 < dradius A ->
    0 < dradius B ->
    disks_touch A B ->
    disc_bb_contact A B.
Proof.
  intros A B HrA HrB Ht.
  destruct Ht as [[p [HA HB]] Hii].
  exists p.
  apply (touch_point_on_both_circles A B p HrA HrB);
    [split; [exists p; split; assumption | exact Hii] | exact HA | exact HB].
Qed.

(* WITNESS {"claimId":"ov-curved-kiss-qex","topic":"overlay","lemma":"disks_touch_iff_bb_and_no_II","title":"On positive discs, kiss iff BB contact and no II","file":"theories/CurvedKissObligation.v","witness":"kiss-discs","board":"OverlayNGCurve / G-family"} *)

Theorem disks_touch_iff_bb_and_no_II :
  forall A B : Disk,
    0 < dradius A ->
    0 < dradius B ->
    disks_touch A B <-> (disc_bb_contact A B /\ disc_no_II A B).
Proof.
  intros A B HrA HrB. split.
  - intros Ht. split.
    + apply disks_touch_bb_contact; assumption.
    + apply touch_no_II_2cell. exact Ht.
  - intros [[p [HA HB]] Hii].
    split.
    + exists p. split; apply disc_on_circle_in_disk; assumption.
    + exact Hii.
Qed.

(* WITNESS {"claimId":"ov-curved-kiss-qex","topic":"overlay","lemma":"disks_touch_no_II","title":"disks_touch implies no II 2-cell (reuse touch_no_II_2cell)","file":"theories/CurvedKissObligation.v","witness":"kiss-discs","board":"OverlayNGCurve / G-family"} *)

Theorem disks_touch_no_II :
  forall A B : Disk,
    disks_touch A B ->
    forall p, ~ (in_disk_int A p /\ in_disk_int B p).
Proof.
  apply touch_no_II_2cell.
Qed.

(* WITNESS {"claimId":"ov-curved-kiss-qex","topic":"overlay","lemma":"disks_touch_cap_not_2cell","title":"disks_touch implies CAP is not a 2-cell (reuse T_cap_not_2cell)","file":"theories/CurvedKissObligation.v","witness":"kiss-discs","board":"OverlayNGCurve / G-family"} *)

Theorem disks_touch_cap_not_2cell :
  forall A B : Disk,
    0 < dradius A ->
    0 < dradius B ->
    disks_touch A B ->
    region_not_2cell (lens A B).
Proof.
  apply T_cap_not_2cell.
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  External vs internal: T-ext is kiss; T-int is covers, not TOUCH.       *)
(* -------------------------------------------------------------------------- *)

Lemma covers_centre_in :
  forall A B : Disk,
    0 <= dradius B ->
    disk_covers A B ->
    in_disk A (dcentre B).
Proof.
  intros A B HrB Hcov.
  apply Hcov.
  apply in_disk_centre.
  unfold disk_is_valid. exact HrB.
Qed.

(** If A covers B at positive radii, B's centre sits in both interiors
    — so covers is never kiss.  Works for concentric and T-int alike. *)
Lemma disk_covers_meets_interiors :
  forall A B : Disk,
    0 < dradius A ->
    0 < dradius B ->
    disk_covers A B ->
    exists p, in_disk_int A p /\ in_disk_int B p.
Proof.
  intros A B HrA HrB Hcov.
  exists (dcentre B). split.
  - (* cB ∈ cl(A) and, if it were on ∂A, the far point of B would leave A. *)
    assert (Hin : in_disk A (dcentre B)).
    { apply covers_centre_in; [lra | exact Hcov]. }
    unfold in_disk, in_disk_int in *.
    destruct (Req_dec (dist (dcentre A) (dcentre B)) 0) as [Hz | Hnz].
    + pose proof (dist_mul_self (dcentre A) (dcentre B)) as Hm.
      rewrite Hz in Hm. nra.
    + destruct (Req_dec (dist (dcentre A) (dcentre B)) (dradius A))
        as [Heq | Hne].
      * (* d = rA: the outward far point of B leaves A. *)
        assert (Hdpos : 0 < dist (dcentre A) (dcentre B)) by lra.
        assert (Hdne : dist (dcentre A) (dcentre B) <> 0) by lra.
        set (K := mkPoint
                    (px (dcentre B)
                     + (dradius B / dist (dcentre A) (dcentre B))
                       * (px (dcentre B) - px (dcentre A)))
                    (py (dcentre B)
                     + (dradius B / dist (dcentre A) (dcentre B))
                       * (py (dcentre B) - py (dcentre A)))).
        pose proof (dist_mul_self (dcentre A) (dcentre B)) as Hd2.
        assert (HKB0 : dist_sq (dcentre B) K
                       = (dradius B / dist (dcentre A) (dcentre B))
                         * (dradius B / dist (dcentre A) (dcentre B))
                         * dist_sq (dcentre A) (dcentre B)).
        { unfold K, dist_sq. cbn [px py]. ring. }
        assert (HKB : dist_sq (dcentre B) K = dradius B * dradius B).
        { rewrite HKB0, <- Hd2. field. exact Hdne. }
        assert (HKA0 : dist_sq (dcentre A) K
                       = (1 + dradius B / dist (dcentre A) (dcentre B))
                         * (1 + dradius B / dist (dcentre A) (dcentre B))
                         * dist_sq (dcentre A) (dcentre B)).
        { unfold K, dist_sq. cbn [px py]. ring. }
        assert (HKA : dist_sq (dcentre A) K
                      = (dist (dcentre A) (dcentre B) + dradius B)
                        * (dist (dcentre A) (dcentre B) + dradius B)).
        { rewrite HKA0, <- Hd2. field. exact Hdne. }
        exfalso.
        assert (HinK : in_disk A K).
        { apply Hcov. unfold in_disk. rewrite HKB. lra. }
        unfold in_disk in HinK. rewrite HKA, Heq in HinK.
        nra.
      * pose proof (dist_mul_self (dcentre A) (dcentre B)) as Hm.
        assert (HdA : dist (dcentre A) (dcentre B) <= dradius A).
        { apply (proj2 (dist_le_iff_dist_sq_le
                          (dcentre A) (dcentre B) (dradius A)
                          (Rlt_le _ _ HrA))).
          exact Hin. }
        nra.
  - apply in_disk_int_centre. exact HrB.
Qed.

Lemma disks_touch_not_covers :
  forall A B : Disk,
    0 < dradius A ->
    0 < dradius B ->
    disks_touch A B ->
    ~ disk_covers A B.
Proof.
  intros A B HrA HrB Ht Hcov.
  destruct (disk_covers_meets_interiors A B HrA HrB Hcov) as [p Hp].
  apply (touch_no_II_2cell A B Ht p). exact Hp.
Qed.

(* WITNESS {"claimId":"ov-curved-kiss-qex","topic":"overlay","lemma":"disks_touch_is_external","title":"T-ext kiss is external: neither closure contains the other","file":"theories/CurvedKissObligation.v","witness":"kiss-discs","board":"OverlayNGCurve / G-family"} *)

Theorem disks_touch_is_external :
  forall A B : Disk,
    0 < dradius A ->
    0 < dradius B ->
    disks_touch A B ->
    kiss_external (in_disk A) (in_disk B) (in_disk_int A) (in_disk_int B).
Proof.
  intros A B HrA HrB Ht.
  split; [exact Ht|].
  split.
  - apply (disks_touch_not_covers A B HrA HrB Ht).
  - apply (disks_touch_not_covers B A HrB HrA).
    destruct Ht as [Hmeet Hii].
    split.
    + destruct Hmeet as [p [HA HB]]. exists p. split; assumption.
    + intros p [HiB HiA]. apply (Hii p). split; assumption.
Qed.

(* WITNESS {"claimId":"ov-curved-kiss-qex","topic":"overlay","lemma":"t_ext_kiss","title":"External-tangency fixture is a two-body kiss","file":"theories/CurvedKissObligation.v","witness":"kiss-discs","board":"OverlayNGCurve / G-family"} *)

Theorem t_ext_kiss :
  disks_touch ext_A ext_B /\
  kiss_external (in_disk ext_A) (in_disk ext_B)
                (in_disk_int ext_A) (in_disk_int ext_B).
Proof.
  split; [exact ext_touch|].
  apply disks_touch_is_external; [cbn; lra | cbn; lra | exact ext_touch].
Qed.

Lemma t_int_radii_pos :
  0 < dradius int_A /\ 0 < dradius int_B.
Proof. cbn. split; lra. Qed.

(* WITNESS {"claimId":"ov-curved-kiss-qex","topic":"overlay","lemma":"t_int_is_covers_not_kiss","title":"T-int is covers, not disks_touch; interiors meet","file":"theories/CurvedKissObligation.v","witness":"kiss-discs","board":"OverlayNGCurve / G-family"} *)

Theorem t_int_is_covers_not_kiss :
  disk_covers int_A int_B /\
  ~ disks_touch int_A int_B /\
  closure_internal (in_disk int_A) (in_disk int_B).
Proof.
  split; [exact int_covers|].
  split.
  - intros Ht.
    destruct t_int_radii_pos as [HrA HrB].
    exact (disks_touch_not_covers int_A int_B HrA HrB Ht int_covers).
  - left. exact int_covers.
Qed.

(* WITNESS {"claimId":"ov-curved-kiss-qex","topic":"overlay","lemma":"disc_kiss_eight_row_complete","title":"Eight-row family (phase0 ∨ TOUCH) is candidate-complete; reuse","file":"theories/CurvedKissObligation.v","witness":"kiss-discs","board":"OverlayNGCurve / G-family"} *)

Theorem disc_kiss_eight_row_complete :
  candidate_complete eight_row_family.
Proof.
  exact eight_row_is_candidate_complete.
Qed.

(* -------------------------------------------------------------------------- *)
(* §8  Disc slice discharges the Record.                                      *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"ov-curved-kiss-qex","topic":"overlay","lemma":"two_disc_kiss_discharges_curved_obligation","title":"Positive-radius discs inhabit the kiss obligation; noding is radical-node uniqueness","file":"theories/CurvedKissObligation.v","witness":"kiss-discs","board":"OverlayNGCurve / G-family"} *)

Theorem two_disc_kiss_discharges_curved_obligation :
  forall A B : Disk,
    0 < dradius A ->
    0 < dradius B ->
    curved_kiss_exact_noding_obligation
      (disc_filled A) (disc_filled B)
      (in_disk_int A) (in_disk_int B)
      (disc_pair_exactly_noded A B)
      (disc_bb_contact A B)
      (disc_no_II A B).
Proof.
  intros A B HrA HrB.
  refine (mk_curved_kiss_obligation _ _ _ _ _ _ _ _).
  - exact (disc_pair_domain A B HrA HrB).
  - exact (disc_pair_exactly_noded_hold A B).
  - intros. cbn [cf_fill disc_filled].
    rewrite bodies_kiss_disc_iff_touch.
    apply disks_touch_iff_bb_and_no_II; assumption.
Qed.

(* WITNESS {"claimId":"ov-curved-kiss-qex","topic":"overlay","lemma":"curved_kiss_modulo_qex","title":"Disc-slice kiss obligation is the Qed BB/no-II identity; CurvePolygon residual stays the named Prop","file":"theories/CurvedKissObligation.v","witness":"kiss-discs","board":"OverlayNGCurve / G-family"} *)

(** Named remaining stop.  On positive-radius discs the obligation is
    equivalent to kiss ↔ (BB contact ∧ no II), already Qed above.
    The same Record at a general CurvePolygon pair
    ([curved_kiss_on_curve_polygons]) is not constructed. *)
Theorem curved_kiss_modulo_qex :
  forall A B : Disk,
    0 < dradius A ->
    0 < dradius B ->
    curved_kiss_exact_noding_obligation
      (disc_filled A) (disc_filled B)
      (in_disk_int A) (in_disk_int B)
      (disc_pair_exactly_noded A B)
      (disc_bb_contact A B)
      (disc_no_II A B)
    <->
    (disks_touch A B <-> (disc_bb_contact A B /\ disc_no_II A B)).
Proof.
  intros A B HrA HrB. split.
  - intros [_ _ Hk].
    rewrite <- bodies_kiss_disc_iff_touch.
    exact Hk.
  - intros _.
    exact (two_disc_kiss_discharges_curved_obligation A B HrA HrB).
Qed.

(* -------------------------------------------------------------------------- *)
(* §9  Thin CAP-face bridge (reuse, do not duplicate).                        *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"ov-curved-kiss-qex","topic":"overlay","lemma":"kiss_touch_cap_faces_not_II","title":"On TOUCH, CAP-obligation faces are not an II 2-cell (reuse touch_cap_faces_not_II)","file":"theories/CurvedKissObligation.v","witness":"kiss-discs","board":"OverlayNGCurve / G-family"} *)

Theorem kiss_touch_cap_faces_not_II :
  forall (A B : Disk) (Hnod : Prop) (extracted_cap_faces : Point -> Prop),
    0 < dradius A ->
    0 < dradius B ->
    disks_touch A B ->
    curved_cap_exact_noding_obligation
      (disc_filled A) (disc_filled B) Hnod extracted_cap_faces ->
    region_not_2cell extracted_cap_faces /\
    (forall p, ~ (in_disk_int A p /\ in_disk_int B p)).
Proof.
  intros A B Hnod extract HrA HrB Ht Hcap.
  exact (touch_cap_faces_not_II A B Hnod extract HrA HrB Ht Hcap).
Qed.

(* -------------------------------------------------------------------------- *)
(* §10  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions bodies_kiss_disc_iff_touch.
Print Assumptions disks_touch_iff_bb_and_no_II.
Print Assumptions disks_touch_no_II.
Print Assumptions disks_touch_cap_not_2cell.
Print Assumptions disks_touch_is_external.
Print Assumptions t_ext_kiss.
Print Assumptions t_int_is_covers_not_kiss.
Print Assumptions disc_kiss_eight_row_complete.
Print Assumptions two_disc_kiss_discharges_curved_obligation.
Print Assumptions curved_kiss_modulo_qex.
Print Assumptions kiss_touch_cap_faces_not_II.
Print Assumptions valid_curve_polygon_inhabits_kiss_domain.
