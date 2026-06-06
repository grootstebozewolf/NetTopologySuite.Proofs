(* ============================================================================
   NetTopologySuite.Proofs.HexXScaleBridge
   ----------------------------------------------------------------------------
   sqrt(3)/2 scaling on the x-axis bridges R (exact hex/equilateral geometry)
   and Q (rational preimage) for horizontal-ray crossing parity, with explicit
   treatment of horizontal darts (constant-y edges that contribute 0 to parity).

   The useful direction (Q proof → R geometry) is the `xscale_cross_bridge`
   lemma below.  Horizontal darts are handled by the dedicated no-cross lemmas.

   Pure-R; three-axiom.  No Admitted.

   Part of the special-case JCT programme (#65).
   ========================================================================== *)

From Stdlib Require Import Reals Lra Field.
From NTS.Proofs Require Import Distance Overlay.

Local Open Scope R_scope.

Definition xscale (s : R) (p : Point) : Point := mkPoint (s * px p) (py p).

Lemma horizontal_dart_no_cross :
  forall (s : R) (p a b : Point),
    0 < s ->
    py a = py b ->
    py p = py a ->
    ~ edge_crosses_ray (xscale s p) (xscale s a, xscale s b).
Proof.
  intros s p a b Hs Habeq Hpeq.
  unfold edge_crosses_ray, xscale; cbn [px py fst snd].
  destruct a as [ax ay], b as [bx by_], p as [px' py'];
    cbn [px py] in *; subst.
  intros [[Hstr _] | [Hstr _]]; exfalso; destruct Hstr as [H1 H2]; apply (Rlt_asym _ _ H1 H2).
Qed.

Lemma q_horizontal_dart_no_cross :
  forall (p a b : Point),
    py a = py b ->
    py p = py a ->
    ~ edge_crosses_ray p (a, b).
Proof.
  intros p a b Habeq Hpeq.
  unfold edge_crosses_ray; cbn [px py fst snd].
  destruct a as [ax ay], b as [bx by_], p as [px' py'];
    cbn [px py] in *; subst.
  intros [[Hstr _] | [Hstr _]]; exfalso; destruct Hstr as [H1 H2]; apply (Rlt_asym _ _ H1 H2).
Qed.

(* The bridge (Q preimage → R scaled geometry).  This is the direction used
   when you have a proof on the rational hex lattice and want the result in
   the exact-R geometry (with correct distances/angles for equilateral 60°
   sides) that the corpus uses for orientations, darts, and ray parity.
   The forward (R → Q) is symmetric by the identical positive-factor argument
   (y-straddles unchanged; x-intercepts factor the uniform positive s). *)
Lemma xscale_cross_bridge :
  forall (s : R) (qx qy qax qay qbx qby : R),
    0 < s ->
    let qp := mkPoint qx qy in
    let qa := mkPoint qax qay in
    let qb := mkPoint qbx qby in
    edge_crosses_ray qp (qa, qb) ->
    edge_crosses_ray (xscale s qp) (xscale s qa, xscale s qb).
Proof.
  intros s qx qy qax qay qbx qby Hs qp qa qb Hq.
  unfold edge_crosses_ray, xscale; cbn [px py fst snd].
  destruct Hq as [[Hya Hx] | [Hyb Hx]].
  - left; split; [exact Hya | ].
    apply (Rmult_lt_compat_l s) in Hx; [ | exact Hs ].
    replace (s * (px qa + (px qb - px qa) * (py qp - py qa) / (py qb - py qa)))
      with (s * px qa + (s * px qb - s * px qa) * (py qp - py qa) / (py qb - py qa))
      in Hx by (field; lra).
    exact Hx.
  - right; split; [exact Hyb | ].
    apply (Rmult_lt_compat_l s) in Hx; [ | exact Hs ].
    replace (s * (px qb + (px qa - px qb) * (py qp - py qb) / (py qa - py qb)))
      with (s * px qb + (s * px qa - s * px qb) * (py qp - py qb) / (py qa - py qb))
      in Hx by (field; lra).
    exact Hx.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions horizontal_dart_no_cross.
Print Assumptions q_horizontal_dart_no_cross.
Print Assumptions xscale_cross_bridge.
