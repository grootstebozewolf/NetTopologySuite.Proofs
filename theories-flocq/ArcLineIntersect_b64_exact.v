(* ============================================================================
   NetTopologySuite.Proofs.Flocq.ArcLineIntersect_b64_exact
   ----------------------------------------------------------------------------
   Phase 4 first slice (Scope A): first-stage bit-exactness for the binary64
   arc-line (circle-chord) intersection-point computation -- the prefix of
   the Cramer-rule chain that lands BEFORE the dividing step.

   Honest scoping note: the headline
       B2R (b64_arc_line_intersect_point_x ...) = arc_line_intersect_x_R ...
   does NOT hold on the nose in the integer regime, because the intersection
   parameter along the chord is generally a non-dyadic rational.  Round-chain
   identity (Scope B) and forward-error bound (Scope C) are queued as
   follow-up slices.

   What this file ships:

     - Total binary64 projections `b64_arc_line_intersect_point_x` /
       `b64_arc_line_intersect_point_y` (return `binary64`, not `option`).
     - Safety predicate `arc_line_intersect_inputs_int_safe` extending the
       ten-coordinate `inCircle_inputs_int_safe` regime with the R-side
       denominator-non-zero condition.
     - R-side reference expressions: `arc_line_intersect_param_s`,
       `arc_line_intersect_x_R`, `arc_line_intersect_y_R`.
     - First-stage exactness: the two outer inCircle evaluations (`sP`, `sQ`)
       and the two chord coordinate differences (`dx`, `dy`) are bit-exact
       integer-valued binary64.

   Mirrors `Intersect_b64_exact.v` Scope A; parallels the arc-chord existence
   predicate in `theories/ArcIntersect.v` with coordinate machinery.

   No `Admitted`, no `Axiom`, no `Parameter`.
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra.

From Flocq Require Import IEEE754.Binary Core.

From NTS.Proofs.Flocq Require Import Validate_binary64 InCircle_b64_compute
                                      InCircle_b64_exact Orient_b64_exact
                                      Intersect_b64.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* R-side Cramer's-rule reference expressions.                                *)
(*                                                                            *)
(* Arc S,M,E defines the circumcircle; chord P->Q is parameterised by         *)
(*   t := inCircle_R(S,M,E,P) / (inCircle_R(S,M,E,P) - inCircle_R(S,M,E,Q)). *)
(* This is the direct analogue of `intersect_param_s` with cross products      *)
(* replaced by inCircle determinants.                                         *)
(* -------------------------------------------------------------------------- *)

Definition arc_line_intersect_param_s (S M E P Q : BPoint) : R :=
  inCircle_R_BP S M E P
    / (inCircle_R_BP S M E P - inCircle_R_BP S M E Q).

Definition arc_line_intersect_x_R (S M E P Q : BPoint) : R :=
  Binary.B2R prec emax (bx P)
  + arc_line_intersect_param_s S M E P Q
    * (Binary.B2R prec emax (bx Q) - Binary.B2R prec emax (bx P)).

Definition arc_line_intersect_y_R (S M E P Q : BPoint) : R :=
  Binary.B2R prec emax (by_ P)
  + arc_line_intersect_param_s S M E P Q
    * (Binary.B2R prec emax (by_ Q) - Binary.B2R prec emax (by_ P)).

(* -------------------------------------------------------------------------- *)
(* Total binary64 projections.                                                *)
(* -------------------------------------------------------------------------- *)

Definition b64_arc_line_intersect_point_x (S M E P Q : BPoint) : binary64 :=
  let sP := b64_inCircle S M E P in
  let sQ := b64_inCircle S M E Q in
  let den := b64_minus sP sQ in
  let t   := b64_div sP den in
  let dx  := b64_minus (bx Q) (bx P) in
  b64_plus (bx P) (b64_mult t dx).

Definition b64_arc_line_intersect_point_y (S M E P Q : BPoint) : binary64 :=
  let sP := b64_inCircle S M E P in
  let sQ := b64_inCircle S M E Q in
  let den := b64_minus sP sQ in
  let t   := b64_div sP den in
  let dy  := b64_minus (by_ Q) (by_ P) in
  b64_plus (by_ P) (b64_mult t dy).

(* -------------------------------------------------------------------------- *)
(* Safety predicate.                                                          *)
(*                                                                            *)
(* Ten arc_coord_int_safe premises (|coord| <= 2^11) for the degree-4 inCircle *)
(* chain, plus the R-side denominator-non-zero condition.                     *)
(* -------------------------------------------------------------------------- *)

Definition arc_line_intersect_inputs_int_safe (S M E P Q : BPoint) : Prop :=
  inCircle_inputs_int_safe S M E P /\
  inCircle_inputs_int_safe S M E Q /\
  inCircle_R_BP S M E P <> inCircle_R_BP S M E Q.

Lemma arc_line_intersect_inputs_int_safe_SMP :
  forall S M E P Q : BPoint,
    arc_line_intersect_inputs_int_safe S M E P Q ->
    inCircle_inputs_int_safe S M E P.
Proof.
  intros S M E P Q [Hint [_ _]]. exact Hint.
Qed.

Lemma arc_line_intersect_inputs_int_safe_SMQ :
  forall S M E P Q : BPoint,
    arc_line_intersect_inputs_int_safe S M E P Q ->
    inCircle_inputs_int_safe S M E Q.
Proof.
  intros S M E P Q [_ [Hint _]]. exact Hint.
Qed.

(* -------------------------------------------------------------------------- *)
(* First-stage exactness lemmas: the prefix before division is bit-exact.      *)
(* -------------------------------------------------------------------------- *)

Lemma b64_arc_line_sP_R :
  forall S M E P Q : BPoint,
    arc_line_intersect_inputs_int_safe S M E P Q ->
    Binary.B2R prec emax (b64_inCircle S M E P)
    = inCircle_R_BP S M E P.
Proof.
  intros S M E P Q Hsafe.
  apply b64_inCircle_exact_for_small_int.
  apply (arc_line_intersect_inputs_int_safe_SMP _ _ _ _ _ Hsafe).
Qed.

Lemma b64_arc_line_sQ_R :
  forall S M E P Q : BPoint,
    arc_line_intersect_inputs_int_safe S M E P Q ->
    Binary.B2R prec emax (b64_inCircle S M E Q)
    = inCircle_R_BP S M E Q.
Proof.
  intros S M E P Q Hsafe.
  apply b64_inCircle_exact_for_small_int.
  apply (arc_line_intersect_inputs_int_safe_SMQ _ _ _ _ _ Hsafe).
Qed.

Lemma arc_chord_diff_bound_2p12 :
  forall (a b : Z),
    (Z.abs a <= 2 ^ 11)%Z -> (Z.abs b <= 2 ^ 11)%Z ->
    (Z.abs (a - b) <= 2 ^ 12)%Z.
Proof. intros. replace (2 ^ 12)%Z with (2 ^ 11 + 2 ^ 11)%Z by lia. lia. Qed.

Lemma b64_arc_line_dx_R :
  forall S M E P Q : BPoint,
    arc_line_intersect_inputs_int_safe S M E P Q ->
    Binary.B2R prec emax (b64_minus (bx Q) (bx P))
    = Binary.B2R prec emax (bx Q) - Binary.B2R prec emax (bx P)
    /\ Binary.is_finite prec emax (b64_minus (bx Q) (bx P)) = true.
Proof.
  intros S M E P Q Hsafe.
  destruct (arc_line_intersect_inputs_int_safe_SMP _ _ _ _ _ Hsafe) as
    (_ & _ & _ & _ & _ & _ & HxP & _).
  destruct (arc_line_intersect_inputs_int_safe_SMQ _ _ _ _ _ Hsafe) as
    (_ & _ & _ & _ & _ & _ & HxQ & _).
  destruct HxP as (FxP & nxP & HxPR & HxPb).
  destruct HxQ as (FxQ & nxQ & HxQR & HxQb).
  set (dx := (nxQ - nxP)%Z).
  pose proof (arc_chord_diff_bound_2p12 nxQ nxP HxQb HxPb) as Bdx.
  destruct (b64_minus_int_exact (bx Q) (bx P) nxQ nxP FxQ FxP HxQR HxPR
                (le_2p12_le_2pprec dx Bdx)) as [Hdx Fdx].
  rewrite HxQR, HxPR, <- minus_IZR. split; [exact Hdx | exact Fdx].
Qed.

Lemma b64_arc_line_dy_R :
  forall S M E P Q : BPoint,
    arc_line_intersect_inputs_int_safe S M E P Q ->
    Binary.B2R prec emax (b64_minus (by_ Q) (by_ P))
    = Binary.B2R prec emax (by_ Q) - Binary.B2R prec emax (by_ P)
    /\ Binary.is_finite prec emax (b64_minus (by_ Q) (by_ P)) = true.
Proof.
  intros S M E P Q Hsafe.
  destruct (arc_line_intersect_inputs_int_safe_SMP _ _ _ _ _ Hsafe) as
    (_ & _ & _ & _ & _ & _ & _ & HyP).
  destruct (arc_line_intersect_inputs_int_safe_SMQ _ _ _ _ _ Hsafe) as
    (_ & _ & _ & _ & _ & _ & _ & HyQ).
  destruct HyP as (FyP & nyP & HyPR & HyPb).
  destruct HyQ as (FyQ & nyQ & HyQR & HyQb).
  set (dy := (nyQ - nyP)%Z).
  pose proof (arc_chord_diff_bound_2p12 nyQ nyP HyQb HyPb) as Bdy.
  destruct (b64_minus_int_exact (by_ Q) (by_ P) nyQ nyP FyQ FyP HyQR HyPR
                (le_2p12_le_2pprec dy Bdy)) as [Hdy Fdy].
  rewrite HyQR, HyPR, <- minus_IZR. split; [exact Hdy | exact Fdy].
Qed.

(* -------------------------------------------------------------------------- *)
(* Perron worst-case witness (from InCircle_b64_exact).                       *)
(* -------------------------------------------------------------------------- *)

Lemma perron_arc_line_inputs_int_safe :
  arc_line_intersect_inputs_int_safe
    perron_sliver_S perron_sliver_M perron_sliver_E perron_chord_P perron_chord_Q.
Proof.
  unfold arc_line_intersect_inputs_int_safe.
  split; [| split].
  - exact perron_sliver_inputs_int_safe.
  - exact perron_chord_Q_inputs_int_safe.
  - destruct perron_chord_opposite_signs as [Hpos Hneg].
    lra.
Qed.

Theorem perron_arc_line_sP_exact :
  Binary.B2R prec emax
    (b64_inCircle perron_sliver_S perron_sliver_M perron_sliver_E perron_chord_P)
  = inCircle_R_BP perron_sliver_S perron_sliver_M perron_sliver_E perron_chord_P.
Proof.
  apply (b64_arc_line_sP_R _ _ _ _ _ perron_arc_line_inputs_int_safe).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_arc_line_sP_R.
Print Assumptions b64_arc_line_sQ_R.
Print Assumptions b64_arc_line_dx_R.
Print Assumptions b64_arc_line_dy_R.