(* ============================================================================
   NetTopologySuite.Proofs.Validate_decidable
   ----------------------------------------------------------------------------
   Parameterised executable validation layer.

   The chord-deficit test in Simplify.v uses sqrt (via `dist`) and so is hard
   to abstract over an arbitrary numeric carrier.  The PERPENDICULAR test --
   the form Zygmunt & Rog 2026 actually use, matching classical
   Douglas-Peucker -- is a pure polynomial inequality:

       (cross p r q)^2 <= eps^2 * dist_sq(p, r)

   which involves only +, -, *, and a decidable <=.  This module parameterises
   `greedy_simplify_perp` from Validate.v over a typeclass of "ordered ring
   coercible to R", so the same code can later be instantiated for:

     - R (provided here),
     - Q (rationals: yields a 100%-computable greedy_simplify_perp),
     - Flocq's binary64 (the eventual sound bridge to OCaml `float`,
       following Boldo et al. JAR 2015 \S5).

   The typeclass-based abstraction means every later instantiation gets the
   soundness theorem for free: each instance only has to discharge a handful
   of homomorphism obligations.

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
From NTS.Proofs Require Import Distance Orientation Linearise Simplify Validate.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Typeclass: "ordered ring coercible to R with decidable comparison".        *)
(*                                                                            *)
(* The homomorphism laws on to_real are the soundness contract: every       *)
(* operation on T must agree with its real-valued counterpart under the      *)
(* coercion.  The decidable comparison tle_dec is the operational primitive  *)
(* that makes the function executable; its semantic is fixed by being a     *)
(* sumbool of the corresponding R proposition.                              *)
(* -------------------------------------------------------------------------- *)

Class OrderedReal (T : Type) :=
  { t0     : T
  ; t2     : T
  ; tplus  : T -> T -> T
  ; tsub   : T -> T -> T
  ; tmult  : T -> T -> T
  ; to_real : T -> R
  ; to_real_t0    : to_real t0 = 0
  ; to_real_t2    : to_real t2 = 2
  ; to_real_tplus : forall x y, to_real (tplus x y) = to_real x + to_real y
  ; to_real_tsub  : forall x y, to_real (tsub x y)  = to_real x - to_real y
  ; to_real_tmult : forall x y, to_real (tmult x y) = to_real x * to_real y
  ; tle_dec : forall x y : T,
      { to_real x <= to_real y } + { ~ to_real x <= to_real y }
  }.

(* -------------------------------------------------------------------------- *)
(* Concrete instance: R itself, using Stdlib's Rle_dec.                       *)
(* -------------------------------------------------------------------------- *)

#[export]
Instance OrderedReal_R : OrderedReal R :=
  { t0     := 0
  ; t2     := 2
  ; tplus  := Rplus
  ; tsub   := Rminus
  ; tmult  := Rmult
  ; to_real := fun x => x
  ; to_real_t0    := eq_refl
  ; to_real_t2    := eq_refl
  ; to_real_tplus := fun x y => eq_refl
  ; to_real_tsub  := fun x y => eq_refl
  ; to_real_tmult := fun x y => eq_refl
  ; tle_dec := Rle_dec
  }.

(* -------------------------------------------------------------------------- *)
(* TPoint: a 2-D point with coordinates in the abstract carrier.              *)
(* -------------------------------------------------------------------------- *)

Record TPoint (T : Type) : Type := mkTPoint
  { tpx : T
  ; tpy : T }.

Arguments mkTPoint {T} _ _.
Arguments tpx {T} _.
Arguments tpy {T} _.

Section AbstractValidate.
  Context {T : Type} {OR : OrderedReal T}.

  Definition bpoint_to_point (p : TPoint T) : Point :=
    mkPoint (to_real (tpx p)) (to_real (tpy p)).

  Definition lift_points (pts : list (TPoint T)) : list Point :=
    map bpoint_to_point pts.

  (* Cross product of three TPoints, mirroring Orientation.cross.            *)
  Definition tcross (p0 p1 q : TPoint T) : T :=
    tsub
      (tmult (tsub (tpx p1) (tpx p0)) (tsub (tpy q)  (tpy p0)))
      (tmult (tsub (tpx q)  (tpx p0)) (tsub (tpy p1) (tpy p0))).

  (* Squared distance, mirroring Distance.dist_sq.                           *)
  Definition tdist_sq (p q : TPoint T) : T :=
    tplus
      (tmult (tsub (tpx p) (tpx q)) (tsub (tpx p) (tpx q)))
      (tmult (tsub (tpy p) (tpy q)) (tsub (tpy p) (tpy q))).

  (* Homomorphism: tcross and tdist_sq agree with cross and dist_sq under
     bpoint_to_point.  These are unfolded ring calculations once the
     homomorphism laws for plus/sub/mult are applied. *)

  Lemma to_real_tcross : forall p0 p1 q,
    to_real (tcross p0 p1 q) =
    cross (bpoint_to_point p0) (bpoint_to_point p1) (bpoint_to_point q).
  Proof.
    intros. unfold tcross, cross, bpoint_to_point. cbn.
    rewrite to_real_tsub.
    rewrite !to_real_tmult, !to_real_tsub.
    reflexivity.
  Qed.

  Lemma to_real_tdist_sq : forall p q,
    to_real (tdist_sq p q) = dist_sq (bpoint_to_point p) (bpoint_to_point q).
  Proof.
    intros. unfold tdist_sq, dist_sq, bpoint_to_point. cbn.
    rewrite to_real_tplus.
    rewrite !to_real_tmult, !to_real_tsub.
    reflexivity.
  Qed.

  (* -------------------------------------------------------------------------
     Decidable greedy simplifier (perpendicular form) over the abstract T.
     ------------------------------------------------------------------------- *)

  Fixpoint greedy_simplify_perp_T_aux
    (eps : T) (kept : TPoint T) (rest : list (TPoint T)) : list (TPoint T) :=
    match rest with
    | []          => [kept]
    | q :: more =>
        match more with
        | []          => [kept; q]
        | r :: _tail =>
            if tle_dec
                 (tmult (tcross kept r q) (tcross kept r q))
                 (tmult (tmult eps eps) (tdist_sq kept r))
            then greedy_simplify_perp_T_aux eps kept more
            else kept :: greedy_simplify_perp_T_aux eps q more
        end
    end.

  Definition greedy_simplify_perp_T (eps : T) (pts : list (TPoint T))
    : list (TPoint T) :=
    match pts with
    | []         => []
    | p :: rest  => greedy_simplify_perp_T_aux eps p rest
    end.

  (* -------------------------------------------------------------------------
     Soundness bridge: the abstract result is simp_star_perp-related to the
     abstract input, viewing both through to_real.

     Proof strategy: induction on the input list, mirroring the proof of
     greedy_simplify_perp_correct in Validate.v.  The tle_dec branches
     align with Rle_dec branches because both decide the same R proposition.
     ------------------------------------------------------------------------- *)

  Lemma greedy_simplify_perp_T_aux_correct :
    forall (eps : T) (kept : TPoint T) (rest : list (TPoint T)),
      simp_star_perp (to_real eps)
        (lift_points (kept :: rest))
        (lift_points (greedy_simplify_perp_T_aux eps kept rest)).
  Proof.
    intros eps kept rest. revert kept.
    induction rest as [| q more IH]; intros kept.
    - cbn. apply simp_star_perp_refl.
    - destruct more as [| r tail].
      + cbn. apply simp_star_perp_refl.
      + cbn.
        destruct (tle_dec
                    (tmult (tcross kept r q) (tcross kept r q))
                    (tmult (tmult eps eps) (tdist_sq kept r)))
          as [Hle | _].
        * (* drop branch: the perp hypothesis lifts to the R inductive. *)
          eapply simp_star_perp_step.
          -- apply simp_drop_here_perp.
             (* Goal: cross p r q * cross p r q <= eps^2 * dist_sq p r,
                with p, r, q the bpoint_to_point images of kept, r, q.
                Hle gives us the same inequality under to_real. *)
             rewrite to_real_tmult in Hle.
             rewrite (to_real_tcross kept r q) in Hle.
             rewrite to_real_tmult in Hle.
             rewrite (to_real_tmult eps eps) in Hle.
             rewrite (to_real_tdist_sq kept r) in Hle.
             exact Hle.
          -- apply IH.
        * (* keep branch: prepend bpoint_to_point kept to the recursive
             simp_star_perp via simp_star_perp_cons. *)
          unfold lift_points. cbn.
          apply simp_star_perp_cons.
          apply IH.
  Qed.

  Theorem greedy_simplify_perp_T_correct :
    forall (eps : T) (pts : list (TPoint T)),
      simp_star_perp (to_real eps)
        (lift_points pts)
        (lift_points (greedy_simplify_perp_T eps pts)).
  Proof.
    intros eps pts. destruct pts as [| p rest].
    - cbn. apply simp_star_perp_refl.
    - cbn. apply greedy_simplify_perp_T_aux_correct.
  Qed.

  (* -------------------------------------------------------------------------
     Inheritance corollaries.
     ------------------------------------------------------------------------- *)

  Corollary greedy_simplify_perp_T_length_monotone :
    forall (eps : T) (pts : list (TPoint T)),
      polyline_length (lift_points (greedy_simplify_perp_T eps pts)) <=
      polyline_length (lift_points pts).
  Proof.
    intros eps pts.
    apply simp_star_perp_length_monotone with (eps := to_real eps).
    apply greedy_simplify_perp_T_correct.
  Qed.

  Corollary greedy_simplify_perp_T_preserves_head :
    forall (eps : T) (pts : list (TPoint T)) (default : Point),
      hd default (lift_points pts) =
      hd default (lift_points (greedy_simplify_perp_T eps pts)).
  Proof.
    intros eps pts d.
    apply simp_star_perp_preserves_head with (eps := to_real eps).
    apply greedy_simplify_perp_T_correct.
  Qed.

  Corollary greedy_simplify_perp_T_preserves_last :
    forall (eps : T) (pts : list (TPoint T)) (default : Point),
      last (lift_points pts) default =
      last (lift_points (greedy_simplify_perp_T eps pts)) default.
  Proof.
    intros eps pts d.
    apply simp_star_perp_preserves_last with (eps := to_real eps).
    apply greedy_simplify_perp_T_correct.
  Qed.

End AbstractValidate.

(* -------------------------------------------------------------------------- *)
(* Concrete: specialise to R.  This is the existing greedy_simplify_perp     *)
(* in spirit (same algorithm, same R), but presented through the abstract   *)
(* interface so that future Flocq / rational instantiations get the same    *)
(* soundness theorem with zero re-proof.                                    *)
(* -------------------------------------------------------------------------- *)

Definition greedy_simplify_perp_R
  : R -> list (TPoint R) -> list (TPoint R) :=
  greedy_simplify_perp_T (T := R).

(* -------------------------------------------------------------------------- *)
(* Extraction directive: extract to OCaml.  Without a Flocq binding, OCaml's *)
(* real-arithmetic operations will be opaque (placeholder failures) -- the  *)
(* purpose of this directive is to confirm the function is in the           *)
(* extractable fragment (no Prop -> Set escapes) and to provide the surface *)
(* a future Flocq instance will plug into.                                  *)
(* -------------------------------------------------------------------------- *)

Require Extraction.
Extraction Language OCaml.
Extract Inductive bool   => "bool"   [ "true" "false" ].
Extract Inductive list   => "list"   [ "[]" "(::)" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].

(* No native binding for R, OrderedReal, or tle_dec yet -- those become
   extraction-time placeholders.  A future Validate_binary64.v will provide
   an OrderedReal instance for Flocq's binary64 with concrete OCaml bindings,
   at which point greedy_simplify_perp_T specialised to that instance will
   produce a runnable binary. *)

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                               *)
(* -------------------------------------------------------------------------- *)

Print Assumptions greedy_simplify_perp_T_correct.
Print Assumptions greedy_simplify_perp_T_length_monotone.
