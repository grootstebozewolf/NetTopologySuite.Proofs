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

From Stdlib Require Import Reals Lra Field List.
From NTS.Proofs Require Import Distance Overlay.
Import ListNotations.

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

Definition xscale_edge (s : R) (e : Edge) : Edge :=
  (xscale s (fst e), xscale s (snd e)).

Lemma edge_crosses_ray_xscale : forall s p a b,
  0 < s ->
  edge_crosses_ray p (a, b) ->
  edge_crosses_ray (xscale s p) (xscale_edge s (a, b)).
Proof.
  intros s p a b Hs H.
  destruct p as [px' py'], a as [ax ay], b as [bx by_].
  unfold xscale_edge; cbn [fst snd].
  apply (xscale_cross_bridge s px' py' ax ay bx by_ Hs H).
Qed.

(* Scaling by a positive s is invertible (scale back by 1/s), so xscale
   composed with its inverse is the identity. *)
Lemma xscale_inv : forall s p, s <> 0 -> xscale (/ s) (xscale s p) = p.
Proof.
  intros s [x y] Hs. unfold xscale; cbn [px py].
  replace (/ s * (s * x)) with x by (field; exact Hs).
  reflexivity.
Qed.

(* The reverse bridge (R scaled -> Q preimage): obtained from the forward
   bridge applied with the inverse factor 1/s, then cancelling. *)
Lemma edge_crosses_ray_xscale_rev : forall s p a b,
  0 < s ->
  edge_crosses_ray (xscale s p) (xscale_edge s (a, b)) ->
  edge_crosses_ray p (a, b).
Proof.
  intros s p a b Hs H.
  pose proof (edge_crosses_ray_xscale (/ s) (xscale s p) (xscale s a) (xscale s b)
                (Rinv_0_lt_compat s Hs)) as Hfwd.
  unfold xscale_edge in H; cbn [fst snd] in H.
  specialize (Hfwd H).
  unfold xscale_edge in Hfwd; cbn [fst snd] in Hfwd.
  rewrite !xscale_inv in Hfwd by lra.
  exact Hfwd.
Qed.

(* Parity is preserved by the positive x-scaling.  ray_parity_odd is mutually
   inductive with ray_parity_even, so the two statements are proved together
   by induction on the edge list (using the forward bridge on the cross step
   and the reverse bridge on the skip step). *)
Lemma ray_parity_xscale_both : forall s es p,
  0 < s ->
  (ray_parity_odd p es ->
     ray_parity_odd (xscale s p) (map (xscale_edge s) es)) /\
  (ray_parity_even p es ->
     ray_parity_even (xscale s p) (map (xscale_edge s) es)).
Proof.
  intros s es. induction es as [| e es' IH]; intros p Hs.
  - split.
    + intro H. inversion H.
    + intro H. cbn [map]. apply rpe_nil.
  - destruct e as [a b]. cbn [map]. split.
    + intro H. inversion H; subst.
      * apply rpo_cross.
        -- apply edge_crosses_ray_xscale; assumption.
        -- apply (IH p Hs); assumption.
      * apply rpo_skip.
        -- intro C. apply edge_crosses_ray_xscale_rev in C; [ | exact Hs ].
           contradiction.
        -- apply (IH p Hs); assumption.
    + intro H. inversion H; subst.
      * apply rpe_cross.
        -- apply edge_crosses_ray_xscale; assumption.
        -- apply (IH p Hs); assumption.
      * apply rpe_skip.
        -- intro C. apply edge_crosses_ray_xscale_rev in C; [ | exact Hs ].
           contradiction.
        -- apply (IH p Hs); assumption.
Qed.

Lemma ray_parity_odd_xscale : forall s p es,
  0 < s ->
  ray_parity_odd p es ->
  ray_parity_odd (xscale s p) (map (xscale_edge s) es).
Proof.
  intros s p es Hs. apply (ray_parity_xscale_both s es p Hs).
Qed.

(* One-step unfolding of ring_edges on a two-or-more-element list. *)
Lemma ring_edges_cons2 : forall (a b : Point) (l : list Point),
  ring_edges (a :: b :: l) = (a, b) :: ring_edges (b :: l).
Proof. reflexivity. Qed.

(* Edge extraction commutes with pointwise x-scaling of the ring vertices:
   scaling every vertex then taking edges = taking edges then scaling each. *)
Lemma ring_edges_map_xscale : forall s r,
  ring_edges (map (xscale s) r) = map (xscale_edge s) (ring_edges r).
Proof.
  intros s r. induction r as [| a r' IH].
  - reflexivity.
  - destruct r' as [| b r''].
    + reflexivity.
    + change (map (xscale s) (a :: b :: r''))
        with (xscale s a :: xscale s b :: map (xscale s) r'').
      rewrite ring_edges_cons2, ring_edges_cons2.
      cbn [map].
      rewrite <- IH.
      unfold xscale_edge; cbn [fst snd].
      reflexivity.
Qed.

Print Assumptions horizontal_dart_no_cross.
Print Assumptions q_horizontal_dart_no_cross.
Print Assumptions xscale_cross_bridge.
Print Assumptions ray_parity_odd_xscale.

Definition sqrt3_2 : R := sqrt 3 / 2.

Lemma sqrt3_2_pos : 0 < sqrt3_2.
Proof.
  unfold sqrt3_2.
  apply Rmult_lt_0_compat.
  - apply sqrt_lt_R0. lra.
  - apply Rinv_0_lt_compat. lra.
Qed.

Print Assumptions ray_parity_odd_xscale.
