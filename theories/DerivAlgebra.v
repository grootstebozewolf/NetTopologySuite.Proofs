(* ============================================================================
   NetTopologySuite.Proofs.DerivAlgebra
   ----------------------------------------------------------------------------
   derivable_pt_lim rules in pointwise-lambda shape (Stdlib states them on
   plus_fct / minus_fct / mult_fct / mult_real_fct, which `apply` does not
   unify with a lambda).  Moved verbatim from ClothoidShearLaw.v section 1
   so ClothoidArcSpline.v can reuse them in the host lane; ClothoidShearLaw
   re-exports this module.  Stdlib only.  claimId: none.
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)

From Stdlib Require Import Reals Ranalysis1.
Local Open Scope R_scope.

Lemma dpl_eq : forall f s l1 l2,
  derivable_pt_lim f s l1 -> l1 = l2 -> derivable_pt_lim f s l2.
Proof. intros f s l1 l2 H E. subst. exact H. Qed.

Lemma d_const : forall a s, derivable_pt_lim (fun _ => a) s 0.
Proof. intros. apply derivable_pt_lim_const. Qed.

Lemma d_plus : forall f g s df dg,
  derivable_pt_lim f s df -> derivable_pt_lim g s dg ->
  derivable_pt_lim (fun u => f u + g u) s (df + dg).
Proof.
  intros. apply derivable_pt_lim_ext with (f := plus_fct f g);
    [intro; reflexivity | apply derivable_pt_lim_plus; assumption].
Qed.

Lemma d_minus : forall f g s df dg,
  derivable_pt_lim f s df -> derivable_pt_lim g s dg ->
  derivable_pt_lim (fun u => f u - g u) s (df - dg).
Proof.
  intros. apply derivable_pt_lim_ext with (f := minus_fct f g);
    [intro; reflexivity | apply derivable_pt_lim_minus; assumption].
Qed.

Lemma d_mul : forall f g s df dg,
  derivable_pt_lim f s df -> derivable_pt_lim g s dg ->
  derivable_pt_lim (fun u => f u * g u) s (df * g s + f s * dg).
Proof.
  intros. apply derivable_pt_lim_ext with (f := mult_fct f g);
    [intro; reflexivity | apply derivable_pt_lim_mult; assumption].
Qed.

Lemma d_scal : forall a f s df,
  derivable_pt_lim f s df -> derivable_pt_lim (fun u => a * f u) s (a * df).
Proof.
  intros. apply derivable_pt_lim_ext with (f := mult_real_fct a f);
    [intro; reflexivity | apply derivable_pt_lim_scal; assumption].
Qed.

Lemma d_lin2 : forall a b f g s df dg,
  derivable_pt_lim f s df -> derivable_pt_lim g s dg ->
  derivable_pt_lim (fun u => a * f u + b * g u) s (a * df + b * dg).
Proof. intros. apply d_plus; apply d_scal; assumption. Qed.

Print Assumptions dpl_eq.
Print Assumptions d_const.
Print Assumptions d_plus.
Print Assumptions d_minus.
Print Assumptions d_mul.
Print Assumptions d_scal.
Print Assumptions d_lin2.
