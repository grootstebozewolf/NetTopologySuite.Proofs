(* ============================================================================
   NetTopologySuite.Proofs.SnyderMercatorSphere
   ----------------------------------------------------------------------------
   Spherical Mercator, exact identities over R, from J. P. Snyder,
   Map Projections -- A Working Manual, USGS Professional Paper 1395
   (1987), ch. 7. Book pages (PDF page - 12):

     (7-1)  x   = R (lam - lam0)                 p. 41
     (7-2)  y   = R ln tan (PI/4 + phi/2)        p. 41
     (7-2a) y   = (R/2) ln ((1 + sin phi) / (1 - sin phi))   p. 41
     (7-3)  h = k = sec phi                      p. 44
     (7-4)  phi = PI/2 - 2 arctan (e^(-y/R))     p. 44
     (7-4a) phi = arctan (sinh (y/R))            p. 44
     (7-5)  lam = x/R + lam0                     p. 44

   No ln. Stdlib ln_exp, exp_ln and derivable_pt_lim_ln (and Ratan
   atan_tan) print Classical_Prop.classic, so (7-2) is carried in its
   exponential form  e^(y/R) = tan (PI/4 + phi/2)  and arctan is the
   3-axiom AtanIvt.atan3. The literal ln statements are not in this file.

   Lemmas:
     merc_sphere_phi_of_y_of_tan_eq_exp  (7-4) inverts (7-2), exp form
     merc_sphere_phi_of_y_range          (7-4) lands in the open band
     merc_sphere_tan_of_phi_of_y         (7-4) satisfies (7-2), exp form
     merc_sphere_phi_of_y_eq_atan3_sinh  (7-4) = (7-4a) (Gudermannian)
     merc_sphere_tan_sq_eq_sin_ratio     (7-2) = (7-2a), squared exp form
     merc_sphere_tan_derivative          d/dphi tan(PI/4 + phi/2)
     merc_sphere_lam_of_x_of_lam         (7-5) undoes (7-1)

   Scope. Snyder's closed spherical formulas, |phi| < PI/2. Not the
   ellipsoid ((7-6)..(7-13)), not the (3-5) series, not transverse
   Mercator (ch. 8), not a float implementation. (7-1) is taken as
   printed; the +-180 deg reduction of lam - lam0 is not modelled.
   No Q twin: every statement is transcendental. Numbers from an mpmath
   / PROJ checker of Snyder's worked examples were review aids only and
   are not pinned here.

   topic: foundations
   claimId: snyder-merc-sphere (ticket #970)
   witness: merc_sphere_phi_of_y_of_tan_eq_exp
   3-axiom host. No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import AtanIvt.
Local Open Scope R_scope.

(* ---------- Snyder's spherical Mercator ---------- *)

(* (7-1), p. 41 *)
Definition merc_sphere_x (Rs lam0 lam : R) : R := Rs * (lam - lam0).
(* (7-2), p. 41, exponential form: e^(y/R) = merc_sphere_tan phi *)
Definition merc_sphere_tan (phi : R) : R := tan (PI / 4 + phi / 2).
(* (7-4), p. 44 *)
Definition merc_sphere_phi_of_y (Rs y : R) : R := PI / 2 - 2 * atan3 (exp (- (y / Rs))).
(* (7-5), p. 44 *)
Definition merc_sphere_lam_of_x (Rs lam0 x : R) : R := x / Rs + lam0.

(* ---------- local trig kit ---------- *)

Local Lemma tan_pos_open_quarter_turn (u : R) : 0 < u < PI / 2 -> 0 < tan u.
Proof.
  intros [H0 H1]. pose proof PI_RGT_0.
  assert (0 < sin u) by (apply sin_gt_0; lra).
  assert (0 < cos u) by (apply cos_gt_0; lra).
  unfold tan. apply Rdiv_lt_0_compat; assumption.
Qed.

Local Lemma tan_complement_inv (u : R) : 0 < u < PI / 2 -> tan (PI / 2 - u) = / tan u.
Proof.
  intros [H0 H1]. pose proof PI_RGT_0.
  assert (0 < sin u) by (apply sin_gt_0; lra).
  assert (0 < cos u) by (apply cos_gt_0; lra).
  unfold tan. rewrite sin_shift, cos_shift. field. split; lra.
Qed.

Local Lemma atan3_pos_of_pos (v : R) : 0 < v -> 0 < atan3 v < PI / 2.
Proof.
  intros Hv. destruct (atan3_spec v) as [[Hl Hh] Hs].
  split; [|exact Hh].
  assert (Hc : 0 < cos (atan3 v)) by (apply cos_gt_0; lra).
  assert (Hsn : 0 < sin (atan3 v)) by (rewrite Hs; nra).
  destruct (Rle_dec (atan3 v) 0) as [Hn|Hn]; [|lra].
  destruct (Req_dec (atan3 v) 0) as [Hz|Hz].
  - rewrite Hz, sin_0 in Hsn. lra.
  - pose proof (sin_gt_0 (- atan3 v) ltac:(lra) ltac:(pose proof PI_RGT_0; lra)).
    rewrite sin_neg in H. lra.
Qed.

Local Lemma tan_atan3 (v : R) : tan (atan3 v) = v.
Proof.
  destruct (atan3_spec v) as [[Hl Hh] Hs].
  assert (0 < cos (atan3 v)) by (apply cos_gt_0; lra).
  unfold tan. rewrite Hs. field. lra.
Qed.

Local Lemma inv_exp_neg (t : R) : / exp (- t) = exp t.
Proof.
  rewrite exp_Ropp. apply Rinv_inv.
Qed.

(* ---------- (7-4) inverts (7-2), p. 44 ----------
   Any open-band latitude whose exp-form (7-2) value is y is the (7-4)
   latitude of y. *)
Lemma merc_sphere_phi_of_y_of_tan_eq_exp (Rs y phi : R) :
  -(PI / 2) < phi < PI / 2 ->
  merc_sphere_tan phi = exp (y / Rs) ->
  merc_sphere_phi_of_y Rs y = phi.
Proof.
  intros [Hl Hh] Hy. pose proof PI_RGT_0.
  unfold merc_sphere_phi_of_y. unfold merc_sphere_tan in Hy.
  set (u := PI / 4 + phi / 2) in *.
  assert (Hu : 0 < u < PI / 2) by (unfold u; lra).
  rewrite exp_Ropp, <- Hy.
  rewrite <- tan_complement_inv by exact Hu.
  rewrite atan3_tan by (unfold u; lra).
  unfold u. field.
Qed.

(* (7-5) undoes (7-1). *)
Lemma merc_sphere_lam_of_x_of_lam (Rs lam0 lam : R) :
  Rs <> 0 -> merc_sphere_lam_of_x Rs lam0 (merc_sphere_x Rs lam0 lam) = lam.
Proof.
  intros HR. unfold merc_sphere_lam_of_x, merc_sphere_x. field. exact HR.
Qed.

(* ---------- (7-4) lands in the band and satisfies (7-2) ----------
   Exp form. With the lemma above, (7-4) is the unique open-band
   solution phi of  tan (PI/4 + phi/2) = e^(y/R). *)
Lemma merc_sphere_phi_of_y_range (Rs y : R) :
  -(PI / 2) < merc_sphere_phi_of_y Rs y < PI / 2.
Proof.
  unfold merc_sphere_phi_of_y.
  pose proof (atan3_pos_of_pos (exp (- (y / Rs))) (exp_pos _)). lra.
Qed.

Lemma merc_sphere_tan_of_phi_of_y (Rs y : R) :
  merc_sphere_tan (merc_sphere_phi_of_y Rs y) = exp (y / Rs).
Proof.
  unfold merc_sphere_tan, merc_sphere_phi_of_y.
  set (v := exp (- (y / Rs))).
  assert (Hv : 0 < v) by apply exp_pos.
  pose proof (atan3_pos_of_pos v Hv) as Ha.
  replace (PI / 4 + (PI / 2 - 2 * atan3 v) / 2) with (PI / 2 - atan3 v) by field.
  rewrite tan_complement_inv by exact Ha.
  rewrite tan_atan3. unfold v. apply inv_exp_neg.
Qed.

(* ---------- (7-4) = (7-4a), p. 44 ----------
   Snyder's two inverse forms agree, (7-4) = (7-4a): the Gudermannian
   identity  PI/2 - 2 arctan(e^-t) = arctan(sinh t). *)
Lemma merc_sphere_phi_of_y_eq_atan3_sinh (Rs y : R) :
  merc_sphere_phi_of_y Rs y = atan3 (sinh (y / Rs)).
Proof.
  apply atan3_unique; [apply merc_sphere_phi_of_y_range|].
  unfold merc_sphere_phi_of_y.
  set (t := y / Rs). set (v := exp (- t)).
  assert (Hv : 0 < v) by apply exp_pos.
  rewrite sin_shift, cos_shift, cos_2_atan3, sin_2_atan3.
  unfold sinh. fold v.
  assert (Ht : exp t = / v) by (unfold v; rewrite inv_exp_neg; reflexivity).
  rewrite Ht. assert (0 < 1 + v * v) by nra. field. split; lra.
Qed.

(* ---------- derivative of the exp form of (7-2) ----------
   With Y(phi) = e^(y/R) = tan(PI/4 + phi/2), dY/dphi = Y * sec phi on
   the open band. Taking logs would give dy/dphi = R sec phi, the
   meridian half of (7-3) h = k = sec phi (p. 44). That log step and
   the scale factors h, k themselves are NOT proved here: the corpus has
   no 3-axiom ln and no scale-factor definition. Hence "derivative",
   not "conformal" or "scale". *)
Lemma merc_sphere_tan_derivative (phi : R) :
  -(PI / 2) < phi < PI / 2 ->
  derivable_pt_lim merc_sphere_tan phi (merc_sphere_tan phi / cos phi).
Proof.
  intros [Hl Hh]. pose proof PI_RGT_0.
  set (u := PI / 4 + phi / 2).
  assert (Hu : 0 < u < PI / 2) by (unfold u; lra).
  assert (Hs : 0 < sin u) by (apply sin_gt_0; lra).
  assert (Hc : 0 < cos u) by (apply cos_gt_0; lra).
  assert (Dg : derivable_pt_lim (fun p => PI / 4 + p / 2) phi (/ 2)).
  { replace (/ 2) with (0 + / 2 * 1) by ring.
    apply derivable_pt_lim_plus; [apply derivable_pt_lim_const|].
    replace (fun p : R => p / 2) with (mult_real_fct (/ 2) id)
      by (apply FunctionalExtensionality.functional_extensionality; intro p;
          unfold mult_real_fct, id; field).
    apply derivable_pt_lim_scal, derivable_pt_lim_id. }
  assert (Dtan : derivable_pt_lim tan u ((cos u * cos u - (- sin u) * sin u) / (cos u)²)).
  { replace tan with (sin / cos)%F
      by (apply FunctionalExtensionality.functional_extensionality; intro w;
          unfold div_fct, tan; reflexivity).
    apply (derivable_pt_lim_div sin cos u (cos u) (- sin u));
      [apply derivable_pt_lim_sin | apply derivable_pt_lim_cos | lra]. }
  assert (D : derivable_pt_lim (fun p => tan (PI / 4 + p / 2)) phi
               ((cos u * cos u - (- sin u) * sin u) / (cos u)² * / 2)).
  { apply (derivable_pt_lim_comp (fun p => PI / 4 + p / 2) tan); [exact Dg | exact Dtan]. }
  unfold merc_sphere_tan. fold u.
  replace (tan u / cos phi) with ((cos u * cos u - (- sin u) * sin u) / (cos u)² * / 2).
  { exact D. }
  assert (Hc2 : cos phi = 2 * sin u * cos u).
  { rewrite <- sin_2a. unfold u.
    replace (2 * (PI / 4 + phi / 2)) with (PI / 2 - - phi) by field.
    rewrite sin_shift, cos_neg. reflexivity. }
  rewrite Hc2. unfold tan, Rsqr.
  pose proof (sin2_cos2 u) as Hpy. unfold Rsqr in Hpy.
  field_simplify; try lra.
  replace (cos u ^ 2 + sin u ^ 2) with 1 by (rewrite <- Hpy; ring). reflexivity.
Qed.


(* ---------- (7-2) = (7-2a), p. 41 ----------
   Snyder's two forward forms agree, in squared exp form:
   tan^2 (PI/4 + phi/2) = (1 + sin phi) / (1 - sin phi) on the open band. *)
Lemma merc_sphere_tan_sq_eq_sin_ratio (phi : R) :
  -(PI / 2) < phi < PI / 2 ->
  merc_sphere_tan phi * merc_sphere_tan phi = (1 + sin phi) / (1 - sin phi).
Proof.
  intros [Hl Hh]. pose proof PI_RGT_0.
  unfold merc_sphere_tan. set (u := PI / 4 + phi / 2).
  assert (Hu : 0 < u < PI / 2) by (unfold u; lra).
  assert (Hs : 0 < sin u) by (apply sin_gt_0; lra).
  assert (Hc : 0 < cos u) by (apply cos_gt_0; lra).
  assert (Hsp : sin phi = - cos (2 * u)).
  { unfold u. replace phi with (- (PI / 2 - 2 * (PI / 4 + phi / 2))) at 1 by field.
    rewrite sin_neg, sin_shift. reflexivity. }
  rewrite Hsp, cos_2a. unfold tan.
  pose proof (sin2_cos2 u) as Hpy. unfold Rsqr in Hpy.
  replace (1 + - (cos u * cos u - sin u * sin u)) with (2 * (sin u * sin u)) by lra.
  replace (1 - - (cos u * cos u - sin u * sin u)) with (2 * (cos u * cos u)) by lra.
  field. lra.
Qed.

(* WITNESS {"claimId":"snyder-merc-sphere","topic":"foundations","lemma":"merc_sphere_phi_of_y_of_tan_eq_exp","title":"Snyder 1987 spherical Mercator: (7-4) is the open-band inverse of (7-2) in exp form; (7-4) = (7-4a); (7-2) = (7-2a) squared; derivative of tan(PI/4 + phi/2)","file":"theories/SnyderMercatorSphere.v","witness":"merc_sphere_phi_of_y_of_tan_eq_exp","board":"#970"} *)

(* ---------- axiom audit (allowlisted trio only) ---------- *)
Print Assumptions merc_sphere_phi_of_y_of_tan_eq_exp.
Print Assumptions merc_sphere_lam_of_x_of_lam.
Print Assumptions merc_sphere_phi_of_y_range.
Print Assumptions merc_sphere_tan_of_phi_of_y.
Print Assumptions merc_sphere_phi_of_y_eq_atan3_sinh.
Print Assumptions merc_sphere_tan_derivative.
Print Assumptions merc_sphere_tan_sq_eq_sin_ratio.
