(* ============================================================================
   NetTopologySuite.Proofs.Atan2
   ----------------------------------------------------------------------------
   Option-A arc primitives, foundation 1/N: a two-argument arctangent
   `atan2 : R -> R -> R` built on Stdlib's one-argument `Ratan.atan` plus PI,
   with the JTS/`Math.atan2(y, x)` quadrant convention and range (-PI, PI].

   Stdlib `Reals` ships `atan : R -> R` (range (-pi/2, pi/2)) and the bridges
   `sin_atan`/`cos_atan` to sqrt, but NO two-argument `atan2`.  This file adds
   it WITHOUT any new dependency (no Coquelicot / mathcomp) and at the standard
   3-axiom footprint, by case analysis on the sign of x (and of y on the
   y-axis).  The load-bearing correctness lemmas are the cosine/sine
   characterisations

     (x,y) <> (0,0) ->
       cos (atan2 y x) = x / sqrt (x*x + y*y)   /\
       sin (atan2 y x) = y / sqrt (x*x + y*y),

   i.e. `atan2 y x` is the polar angle of the planar vector (x, y).  Every
   downstream arc primitive (central angle / sweep, short-vs-long arc, arc
   length r*theta) is stated and proved against these two identities.  Refs #64.
   ========================================================================== *)

Require Import Reals.
Require Import Lra.
Local Open Scope R_scope.

(* JTS Math.atan2(y, x) convention: angle of the vector (x, y), range (-PI, PI].
   First argument is y (the ordinate), second is x (the abscissa). *)
Definition atan2 (y x : R) : R :=
  if Rlt_dec 0 x then atan (y / x)
  else if Rlt_dec x 0 then
         (if Rle_dec 0 y then atan (y / x) + PI else atan (y / x) - PI)
  else (* x = 0 *)
         (if Rlt_dec 0 y then PI / 2
          else if Rlt_dec y 0 then - (PI / 2)
          else 0).

(* The radius is strictly positive away from the origin. *)
Lemma atan2_r_pos : forall x y : R,
  ~ (x = 0 /\ y = 0) -> 0 < sqrt (x * x + y * y).
Proof.
  intros x y H. apply sqrt_lt_R0.
  destruct (Req_dec x 0) as [Hx0|Hx0].
  - subst x. assert (Hy : y <> 0) by (intro Hy0; apply H; split; [ reflexivity | exact Hy0 ]).
    destruct (Rdichotomy y 0 Hy); nra.
  - destruct (Rdichotomy x 0 Hx0); nra.
Qed.

(* Core ratio identity: cos of atan(y/x) in closed sqrt form (x <> 0). *)
Lemma cos_atan_ratio : forall x y : R, x <> 0 ->
  cos (atan (y / x)) = Rabs x / sqrt (x * x + y * y).
Proof.
  intros x y Hx. rewrite cos_atan. unfold Rsqr.
  assert (Hxx : 0 < x * x) by (destruct (Rdichotomy x 0 Hx); nra).
  assert (E : 1 + y / x * (y / x) = (x * x + y * y) / (x * x))
    by (field; exact Hx).
  rewrite E, sqrt_div_alt by exact Hxx.
  assert (Hs : sqrt (x * x) = Rabs x).
  { replace (x * x) with (Rsqr x) by (unfold Rsqr; ring). apply sqrt_Rsqr_abs. }
  rewrite Hs.
  assert (Hr : 0 < sqrt (x * x + y * y)) by (apply sqrt_lt_R0; nra).
  assert (Ha : Rabs x <> 0) by (apply Rabs_no_R0; exact Hx).
  field. split; [ lra | exact Ha ].
Qed.

(* Companion sine identity, via sin(atan t) = t * cos(atan t). *)
Lemma sin_atan_ratio : forall x y : R, x <> 0 ->
  sin (atan (y / x)) = y / x * (Rabs x / sqrt (x * x + y * y)).
Proof.
  intros x y Hx.
  rewrite <- (cos_atan_ratio x y Hx).
  rewrite sin_atan, cos_atan.
  assert (Hpos : 0 < sqrt (1 + Rsqr (y / x))).
  { apply sqrt_lt_R0. assert (0 <= Rsqr (y / x)) by apply Rle_0_sqr. lra. }
  field. lra.
Qed.

(* ---- Headline 1: cosine characterisation. ------------------------------- *)
Theorem cos_atan2 : forall x y : R, ~ (x = 0 /\ y = 0) ->
  cos (atan2 y x) = x / sqrt (x * x + y * y).
Proof.
  intros x y Hxy. assert (Hr := atan2_r_pos x y Hxy).
  unfold atan2.
  destruct (Rlt_dec 0 x) as [Hx|Hx].
  - rewrite cos_atan_ratio by lra. rewrite (Rabs_right x) by lra. reflexivity.
  - destruct (Rlt_dec x 0) as [Hx2|Hx2].
    + destruct (Rle_dec 0 y) as [Hy|Hy].
      * rewrite neg_cos, cos_atan_ratio by lra.
        rewrite (Rabs_left x) by lra. field. lra.
      * rewrite cos_minus, cos_PI, sin_PI.
        rewrite cos_atan_ratio by lra.
        rewrite (Rabs_left x) by lra. field. lra.
    + assert (x = 0) by lra. subst x.
      destruct (Rlt_dec 0 y) as [Hy|Hy].
      * rewrite cos_PI2. field. lra.
      * destruct (Rlt_dec y 0) as [Hy2|Hy2].
        -- rewrite cos_neg, cos_PI2. field. lra.
        -- exfalso. apply Hxy. split; [ reflexivity | lra ].
Qed.

(* ---- Headline 2: sine characterisation. --------------------------------- *)
Theorem sin_atan2 : forall x y : R, ~ (x = 0 /\ y = 0) ->
  sin (atan2 y x) = y / sqrt (x * x + y * y).
Proof.
  intros x y Hxy. assert (Hr := atan2_r_pos x y Hxy).
  unfold atan2.
  destruct (Rlt_dec 0 x) as [Hx|Hx].
  - rewrite sin_atan_ratio by lra. rewrite (Rabs_right x) by lra. field. lra.
  - destruct (Rlt_dec x 0) as [Hx2|Hx2].
    + destruct (Rle_dec 0 y) as [Hy|Hy].
      * rewrite neg_sin, sin_atan_ratio by lra.
        rewrite (Rabs_left x) by lra. field. lra.
      * rewrite sin_minus, cos_PI, sin_PI.
        rewrite sin_atan_ratio by lra.
        rewrite (Rabs_left x) by lra. field. lra.
    + assert (x = 0) by lra. subst x.
      assert (Hyy : sqrt (0 * 0 + y * y) = Rabs y).
      { replace (0 * 0 + y * y) with (Rsqr y) by (unfold Rsqr; ring).
        apply sqrt_Rsqr_abs. }
      destruct (Rlt_dec 0 y) as [Hy|Hy].
      * rewrite sin_PI2, Hyy, (Rabs_right y) by lra. field. lra.
      * destruct (Rlt_dec y 0) as [Hy2|Hy2].
        -- rewrite sin_neg, sin_PI2, Hyy, (Rabs_left y) by lra. field. lra.
        -- exfalso. apply Hxy. split; [ reflexivity | lra ].
Qed.

(* ---- Pythagorean corollary: atan2 lands on the unit circle scaled by r. -- *)
Corollary atan2_on_circle : forall x y : R, ~ (x = 0 /\ y = 0) ->
  let r := sqrt (x * x + y * y) in
  (r * cos (atan2 y x) = x) /\ (r * sin (atan2 y x) = y).
Proof.
  intros x y Hxy. assert (Hr := atan2_r_pos x y Hxy). simpl.
  rewrite cos_atan2, sin_atan2 by exact Hxy. split; field; lra.
Qed.

Print Assumptions cos_atan2.
Print Assumptions sin_atan2.
