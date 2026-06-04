(* ============================================================================
   NetTopologySuite.Proofs.BufferEndcap
   ----------------------------------------------------------------------------
   Buffer/noder pipeline, Stage 2c seam: LINE ENDCAPS.

   At a LineString endpoint E with final edge direction u, the offset curve
   reaches the two boundary points one buffer distance d to either side:
       cap_endpoint E u d   = E + d * unit_perp u   (left)
       cap_endpoint E u (-d) = E - d * unit_perp u  (right).
   The endcap closes the gap between them.  JTS offers three styles
   (BufferParameters.CAP_FLAT / CAP_ROUND / CAP_SQUARE); this file proves the
   defining geometry of each (JTS#739, #1028 -- flat-endcap artifacts).

     FLAT  (`flat_cap_length_sq`, `flat_cap_perp_edge`): the cap is the
       straight segment between the two boundary points; its length is the
       diameter 2|d| and it is perpendicular to the edge.

     ROUND (`round_cap_endpoints_on_circle`, `round_cap_apex_on_circle`):
       the cap is the semicircle of radius d about E; its two endpoints and
       its apex E + d*unit_dir u all lie on the circle of radius |d|.

     SQUARE (`square_cap_extension`, `square_cap_corner_dist_sq`): the cap
       extends the offset lines by d along the edge to two outer corners
       sq_corner = cap_endpoint + d*unit_dir u; each corner is distance |d|
       beyond its boundary point and distance sqrt(2)|d| from E.

   All pure-R, three-axiom (sqrt only; no atan / Flocq / classic).  No
   `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.8)
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Real Vec Direction Distance BufferOffset.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Unit edge direction (companion of BufferOffset.unit_perp).             *)
(* -------------------------------------------------------------------------- *)

Definition unit_dir (u : Vec) : Vec := vscale (/ vmag u) u.

(* The unit edge direction has unit length. *)
Lemma vmag_sq_unit_dir : forall v, v <> vzero -> vmag_sq (unit_dir v) = 1.
Proof.
  intros v Hv.
  pose proof (vmag_sq_pos v Hv) as Hpos.
  assert (Hmne : vmag v <> 0)
    by (unfold vmag; apply Rgt_not_eq; apply sqrt_lt_R0; exact Hpos).
  assert (Hss : vmag v * vmag v = vmag_sq v) by (unfold vmag; apply sqrt_sqrt; lra).
  assert (Hinv : / vmag v * vmag v = 1) by (apply Rinv_l; exact Hmne).
  assert (Hscale : forall c w, vmag_sq (vscale c w) = c * c * vmag_sq w)
    by (intros; unfold vmag_sq, vdot, vscale; cbn; ring).
  unfold unit_dir. rewrite Hscale. rewrite <- Hss.
  replace (/ vmag v * / vmag v * (vmag v * vmag v))
    with ((/ vmag v * vmag v) * (/ vmag v * vmag v)) by ring.
  rewrite Hinv. ring.
Qed.

(* The unit normal and the unit edge direction are perpendicular. *)
Lemma vdot_unit_perp_unit_dir : forall u, vdot (unit_perp u) (unit_dir u) = 0.
Proof.
  intros u. unfold unit_perp, unit_dir.
  rewrite vdot_scale_l, vdot_scale_r.
  replace (vdot (vperp u) u) with 0 by (unfold vdot, vperp; cbn; ring).
  ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Cap points.                                                            *)
(* -------------------------------------------------------------------------- *)

(* A boundary point: E offset by d along the edge's unit normal.  d and -d
   give the two sides. *)
Definition cap_endpoint (E : Point) (u : Vec) (d : R) : Point :=
  pt_translate E (d * vx (unit_perp u)) (d * vy (unit_perp u)).

(* A square-cap outer corner: the boundary point pushed d further along the
   edge direction. *)
Definition sq_corner (E : Point) (u : Vec) (d : R) : Point :=
  pt_translate (cap_endpoint E u d) (d * vx (unit_dir u)) (d * vy (unit_dir u)).

(* The round-cap apex: E pushed d along the edge direction (farthest point). *)
Definition round_apex (E : Point) (u : Vec) (d : R) : Point :=
  pt_translate E (d * vx (unit_dir u)) (d * vy (unit_dir u)).

(* -------------------------------------------------------------------------- *)
(* §3  Distance helper.                                                       *)
(* -------------------------------------------------------------------------- *)

(* Distance from a point to its displacement by c along a UNIT vector is |c|. *)
Lemma dist_scaled_unit : forall (P : Point) (n : Vec) (c : R),
  vmag_sq n = 1 ->
  dist P (pt_translate P (c * vx n) (c * vy n)) = Rabs c.
Proof.
  intros P n c Hn. unfold dist. rewrite dist_sq_translate.
  replace ((c * vx n) * (c * vx n) + (c * vy n) * (c * vy n))
    with (c * c * vmag_sq n) by (unfold vmag_sq, vdot; ring).
  rewrite Hn, Rmult_1_r.
  replace (c * c) with (Rsqr c) by (unfold Rsqr; ring).
  apply sqrt_Rsqr_abs.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Flat cap.                                                              *)
(* -------------------------------------------------------------------------- *)

(* The flat cap connects the two boundary points; its squared length is the
   squared diameter (2d)^2. *)
Theorem flat_cap_length_sq : forall E u d,
  u <> vzero ->
  dist_sq (cap_endpoint E u d) (cap_endpoint E u (- d)) = 4 * d ^ 2.
Proof.
  intros E u d Hu.
  unfold cap_endpoint, pt_translate, dist_sq. cbn [px py].
  replace
    ((px E + d * vx (unit_perp u) - (px E + - d * vx (unit_perp u))) *
     (px E + d * vx (unit_perp u) - (px E + - d * vx (unit_perp u))) +
     (py E + d * vy (unit_perp u) - (py E + - d * vy (unit_perp u))) *
     (py E + d * vy (unit_perp u) - (py E + - d * vy (unit_perp u))))
    with (4 * d ^ 2 * vmag_sq (unit_perp u))
    by (unfold vmag_sq, vdot; ring).
  rewrite (vmag_sq_unit_perp u Hu). ring.
Qed.

(* The flat cap is perpendicular to the edge direction. *)
Theorem flat_cap_perp_edge : forall E u d,
  vdot (seg_vec (cap_endpoint E u (- d)) (cap_endpoint E u d)) u = 0.
Proof.
  intros E u d.
  unfold seg_vec, cap_endpoint, pt_translate, unit_perp, vscale, vperp, vdot.
  cbn. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Round cap: endpoints and apex lie on the circle of radius |d|.         *)
(* -------------------------------------------------------------------------- *)

Theorem round_cap_endpoints_on_circle : forall E u d,
  u <> vzero ->
  dist E (cap_endpoint E u d) = Rabs d /\
  dist E (cap_endpoint E u (- d)) = Rabs d.
Proof.
  intros E u d Hu.
  pose proof (vmag_sq_unit_perp u Hu) as Hn.
  split.
  - unfold cap_endpoint. apply dist_scaled_unit; exact Hn.
  - unfold cap_endpoint.
    rewrite (dist_scaled_unit E (unit_perp u) (- d) Hn).
    apply Rabs_Ropp.
Qed.

Theorem round_cap_apex_on_circle : forall E u d,
  u <> vzero ->
  dist E (round_apex E u d) = Rabs d.
Proof.
  intros E u d Hu.
  unfold round_apex. apply dist_scaled_unit.
  apply vmag_sq_unit_dir; exact Hu.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Square cap: extension length and corner distance.                      *)
(* -------------------------------------------------------------------------- *)

(* Each square-cap corner is distance |d| beyond its boundary point (the
   extension along the edge). *)
Theorem square_cap_extension : forall E u d,
  u <> vzero ->
  dist (cap_endpoint E u d) (sq_corner E u d) = Rabs d.
Proof.
  intros E u d Hu.
  unfold sq_corner. apply dist_scaled_unit.
  apply vmag_sq_unit_dir; exact Hu.
Qed.

(* Each square-cap corner is distance sqrt(2)|d| from the endpoint E:
   dist_sq E corner = 2 d^2 (normal leg + tangential leg, both d, at right
   angles). *)
Theorem square_cap_corner_dist_sq : forall E u d,
  u <> vzero ->
  dist_sq E (sq_corner E u d) = 2 * d ^ 2.
Proof.
  intros E u d Hu.
  unfold sq_corner, cap_endpoint, pt_translate, dist_sq. cbn [px py].
  replace
    ((px E -
      (px E + d * vx (unit_perp u) + d * vx (unit_dir u))) *
     (px E -
      (px E + d * vx (unit_perp u) + d * vx (unit_dir u))) +
     (py E -
      (py E + d * vy (unit_perp u) + d * vy (unit_dir u))) *
     (py E -
      (py E + d * vy (unit_perp u) + d * vy (unit_dir u))))
    with (d ^ 2 * (vmag_sq (unit_perp u)
                   + 2 * vdot (unit_perp u) (unit_dir u)
                   + vmag_sq (unit_dir u)))
    by (unfold vmag_sq, vdot; ring).
  rewrite (vmag_sq_unit_perp u Hu), (vmag_sq_unit_dir u Hu),
          vdot_unit_perp_unit_dir.
  ring.
Qed.
