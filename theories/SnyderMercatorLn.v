(* ============================================================================
   NetTopologySuite.Proofs.SnyderMercatorLn
   ----------------------------------------------------------------------------
   Spherical Mercator, the literal ln form of (7-2), from J. P. Snyder,
   Map Projections -- A Working Manual, USGS Professional Paper 1395
   (1987), ch. 7. Book pages (PDF page - 12):

     (7-2)  y   = R ln tan (PI/4 + phi/2)        p. 41
     (7-4)  phi = PI/2 - 2 arctan (e^(-y/R))     p. 44

   ln is the 3-axiom LnIvt.ln3 (#972), not Stdlib ln (whose ln_exp,
   exp_ln and derivable_pt_lim_ln print Classical_Prop.classic). The exp
   form and (7-4) are SnyderMercatorSphere (#970).

   Lemmas:
     merc_sphere_tan_pos            tan (PI/4 + phi/2) > 0 on the band
     merc_sphere_phi_of_y_of_phi    (7-4) o (7-2) = id on |phi| < PI/2
     merc_sphere_y_of_phi_of_y      (7-2) o (7-4) = id on R
     merc_sphere_y_derivative_sec   dy/dphi = R / cos phi on the band

   Scope. Named "derivative", not "scale factor": the corpus has no
   scale-factor definition, so (7-3) h = k = sec phi is not claimed.
   Both round trips need Rs <> 0. Not the ellipsoid (7-7)/(7-9), not
   transverse Mercator, not a float implementation. No Q twin.

   topic: foundations
   claimId: snyder-merc-sphere-ln (ticket #972)
   witness: merc_sphere_phi_of_y_of_phi
   3-axiom host. No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import LnIvt SnyderMercatorSphere.
Local Open Scope R_scope.

(* (7-2), p. 41 *)
Definition merc_sphere_y (Rs phi : R) : R := Rs * ln3 (merc_sphere_tan phi).

Lemma merc_sphere_tan_pos (phi : R) :
  -(PI / 2) < phi < PI / 2 -> 0 < merc_sphere_tan phi.
Proof.
  intros [Hl Hh]. pose proof PI_RGT_0. unfold merc_sphere_tan.
  assert (0 < sin (PI / 4 + phi / 2)) by (apply sin_gt_0; lra).
  assert (0 < cos (PI / 4 + phi / 2)) by (apply cos_gt_0; lra).
  unfold tan. apply Rdiv_lt_0_compat; assumption.
Qed.

Lemma merc_sphere_phi_of_y_of_phi (Rs phi : R) :
  Rs <> 0 -> -(PI / 2) < phi < PI / 2 ->
  merc_sphere_phi_of_y Rs (merc_sphere_y Rs phi) = phi.
Proof.
  intros HR Hphi. apply merc_sphere_phi_of_y_of_tan_eq_exp; [exact Hphi|].
  unfold merc_sphere_y.
  replace (Rs * ln3 (merc_sphere_tan phi) / Rs) with (ln3 (merc_sphere_tan phi)) by (field; exact HR).
  rewrite exp_ln3; [reflexivity | apply merc_sphere_tan_pos; exact Hphi].
Qed.

Lemma merc_sphere_y_of_phi_of_y (Rs y : R) :
  Rs <> 0 -> merc_sphere_y Rs (merc_sphere_phi_of_y Rs y) = y.
Proof.
  intros HR. unfold merc_sphere_y. rewrite merc_sphere_tan_of_phi_of_y, ln3_exp.
  field. exact HR.
Qed.

Lemma merc_sphere_y_derivative_sec (Rs phi : R) :
  -(PI / 2) < phi < PI / 2 ->
  derivable_pt_lim (merc_sphere_y Rs) phi (Rs / cos phi).
Proof.
  intros Hphi.
  pose proof (merc_sphere_tan_pos phi Hphi) as Ht.
  assert (Hc : 0 < cos phi) by (apply cos_gt_0; lra).
  assert (D : derivable_pt_lim (comp ln3 merc_sphere_tan) phi (/ cos phi)).
  { replace (/ cos phi) with (/ merc_sphere_tan phi * (merc_sphere_tan phi / cos phi))
      by (field; split; lra).
    apply derivable_pt_lim_comp;
      [apply merc_sphere_tan_derivative; exact Hphi | apply derivable_pt_lim_ln3; exact Ht]. }
  replace (Rs / cos phi) with (Rs * / cos phi) by (unfold Rdiv; reflexivity).
  apply (derivable_pt_lim_scal (comp ln3 merc_sphere_tan) Rs phi (/ cos phi)) in D.
  unfold mult_real_fct, comp in D. unfold merc_sphere_y. exact D.
Qed.

Print Assumptions merc_sphere_phi_of_y_of_phi.
Print Assumptions merc_sphere_y_of_phi_of_y.
Print Assumptions merc_sphere_y_derivative_sec.
