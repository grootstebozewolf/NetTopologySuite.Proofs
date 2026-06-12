(* ============================================================================
   NetTopologySuite.Proofs.Flocq.ClothoidDegenerate_b64
   ----------------------------------------------------------------------------
   binary64 mirror of the degenerate straight-chord clothoid regime -- the
   `_small_int` integer-exactness pattern (Orient_b64_exact.v) applied to the
   residual f(L) = L^2 - d^2.  Route (A) follow-up slice of
   docs/clothoid-open-questions-triage.md (queued in its section 8).

   Context.  theories/ClothoidDegenerate.v proves, on the R side, that in the
   degenerate regime k0 = k1 = 0 the clothoid chord-length residual collapses
   to the bare polynomial f_deg(L) = L^2 - d^2 whose unique positive root is
   L = d, exactly.  This file shows the binary64 evaluation of that residual
   is EXACT in the integer-coordinate regime (`coord_int_safe`: integer-valued
   with |n| <= 2^25):

     - square of a coord:          integer in [0, 2^50]        <= 2^53 = exact
     - difference of two squares:  integer in [-2^51, 2^51]    <= 2^53 = exact

   so `B2R (b64_degenerate_residual d L)` equals the mathematical
   `degenerate_residual (B2R d) (B2R L)` ON THE NOSE -- no rounding error, no
   inequality -- and therefore the binary64 sign/root test decides the exact
   question: the residual is zero iff L = d, negative iff L < d, positive iff
   L > d (for positive inputs).  This mirrors
   `b64_orient_sign_filtered_sound_small_int`: full exactness inside the
   integer window, in exchange for no claim outside it.  The transcendental
   general regime is out of reach by design -- see the triage doc's Q2
   analysis (no integer regime makes the Fresnel integrals dyadic).

   Infrastructure reused (no new machinery):
     - `b64_mult_int_exact` / `b64_minus_int_exact`   (Orient_b64_exact.v)
     - `coord_int_safe`                                (Orient_b64_exact.v)
     - R-side closed form: `degenerate_residual`,
       `degenerate_unique_positive_root`, `degenerate_root_exact`
                                                       (ClothoidDegenerate.v)

   NTS mapping: the straight-chord fast path of a clothoid G^1 Hermite
   solver (clothoid-halley-coq, public EUPL-1.2 repro) under binary64
   coordinates, consumed through the RelateClothoid.v chord carrier on the
   NetTopologySuite.Curve side.

   No Admitted, no Axiom (beyond the corpus allowlist; this lane additionally
   inherits Classical_Prop.classic structurally from Flocq's binary
   operations, see docs/audit-exceptions.txt).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Lra.
From Stdlib Require Import Psatz.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Flocq Require Import Core.

From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import B64_bridge.
From NTS.Proofs.Flocq Require Import Orient_b64_exact.
From NTS.Proofs Require Import ClothoidDegenerate.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* The binary64 degenerate residual: L*L - d*d, evaluated in binary64.        *)
(* Argument order matches the R-side degenerate_residual d L = L*L - d*d.     *)
(* -------------------------------------------------------------------------- *)

Definition b64_degenerate_residual (d L : binary64) : binary64 :=
  b64_minus (b64_mult L L) (b64_mult d d).

(* -------------------------------------------------------------------------- *)
(* Integer-window bound plumbing: |n| <= 2^25 gives |n*n| <= 2^50 <= 2^53     *)
(* and |b*b - a*a| <= 2^51 <= 2^53.                                           *)
(* -------------------------------------------------------------------------- *)

Lemma square_int_window :
  forall n : Z, (Z.abs n <= 2 ^ 25)%Z -> (Z.abs (n * n) <= 2 ^ prec)%Z.
Proof.
  intros n Hn.
  rewrite Z.abs_mul.
  unfold prec.
  assert (H50 : (2 ^ 25 * 2 ^ 25 = 2 ^ 50)%Z) by reflexivity.
  assert (Habs : (0 <= Z.abs n)%Z) by apply Z.abs_nonneg.
  assert (Hsq : (Z.abs n * Z.abs n <= 2 ^ 25 * 2 ^ 25)%Z) by nia.
  lia.
Qed.

Lemma square_diff_int_window :
  forall a b : Z,
    (Z.abs a <= 2 ^ 25)%Z -> (Z.abs b <= 2 ^ 25)%Z ->
    (Z.abs (b * b - a * a) <= 2 ^ prec)%Z.
Proof.
  intros a b Ha Hb.
  pose proof (square_int_window a Ha) as HA.
  pose proof (square_int_window b Hb) as HB.
  unfold prec in *.
  lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* Exactness: in the integer regime the binary64 residual equals the          *)
(* mathematical residual on the nose.                                         *)
(* -------------------------------------------------------------------------- *)

Theorem b64_degenerate_residual_exact :
  forall d L : binary64,
    coord_int_safe d ->
    coord_int_safe L ->
    Binary.B2R prec emax (b64_degenerate_residual d L)
      = degenerate_residual (Binary.B2R prec emax d) (Binary.B2R prec emax L)
    /\ Binary.is_finite prec emax (b64_degenerate_residual d L) = true.
Proof.
  intros d L [Fd [a [HdR Ha]]] [FL [b [HLR Hb]]].
  unfold b64_degenerate_residual, degenerate_residual.
  (* L * L is exact: integer b*b in the window. *)
  destruct (b64_mult_int_exact L L b b FL FL HLR HLR
              (square_int_window b Hb)) as [HLL FLL].
  (* d * d is exact: integer a*a in the window. *)
  destruct (b64_mult_int_exact d d a a Fd Fd HdR HdR
              (square_int_window a Ha)) as [Hdd Fdd].
  (* The difference is exact: integer b*b - a*a in the window. *)
  destruct (b64_minus_int_exact (b64_mult L L) (b64_mult d d)
              (b * b) (a * a) FLL Fdd HLL Hdd
              (square_diff_int_window a b Ha Hb)) as [Hres Fres].
  split; [ | exact Fres ].
  rewrite Hres, HdR, HLR, minus_IZR, !mult_IZR.
  ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* The root/sign headline: for positive integer-regime inputs the binary64    *)
(* residual decides the exact comparison of L against the chord length d.     *)
(* Zero iff L = d (composing with the R-side uniqueness theorem), and the     *)
(* full sign trichotomy.                                                      *)
(* -------------------------------------------------------------------------- *)

Theorem b64_degenerate_root_exact :
  forall d L : binary64,
    coord_int_safe d ->
    coord_int_safe L ->
    0 < Binary.B2R prec emax d ->
    0 < Binary.B2R prec emax L ->
    (Binary.B2R prec emax (b64_degenerate_residual d L) = 0
       <-> Binary.B2R prec emax L = Binary.B2R prec emax d).
Proof.
  intros d L Hd HL Hdpos HLpos.
  destruct (b64_degenerate_residual_exact d L Hd HL) as [Hexact _].
  rewrite Hexact.
  split.
  - (* residual zero => L = d, by the R-side uniqueness of the positive root *)
    intro Hroot.
    apply (degenerate_unique_positive_root
             (Binary.B2R prec emax d) (Binary.B2R prec emax L)
             Hdpos HLpos Hroot).
  - (* L = d => residual zero, by the R-side closed form *)
    intro Heq. rewrite Heq.
    apply degenerate_root_exact.
Qed.

Theorem b64_degenerate_sign_trichotomy :
  forall d L : binary64,
    coord_int_safe d ->
    coord_int_safe L ->
    0 < Binary.B2R prec emax d ->
    0 < Binary.B2R prec emax L ->
    (Binary.B2R prec emax (b64_degenerate_residual d L) < 0
       <-> Binary.B2R prec emax L < Binary.B2R prec emax d)
    /\ (0 < Binary.B2R prec emax (b64_degenerate_residual d L)
       <-> Binary.B2R prec emax d < Binary.B2R prec emax L).
Proof.
  intros d L Hd HL Hdpos HLpos.
  destruct (b64_degenerate_residual_exact d L Hd HL) as [Hexact _].
  rewrite Hexact.
  unfold degenerate_residual.
  split; split; intro H; nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  This lane inherits Classical_Prop.classic structurally from  *)
(* Flocq's binary operations (Bmult/Bminus closure); see                       *)
(* docs/audit-exceptions.txt for the per-file policy.  The R-side content     *)
(* imported from ClothoidDegenerate.v contributes only the three allowlist    *)
(* axioms.                                                                    *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_degenerate_residual_exact.
Print Assumptions b64_degenerate_root_exact.
Print Assumptions b64_degenerate_sign_trichotomy.
