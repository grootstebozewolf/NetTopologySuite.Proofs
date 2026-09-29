(* ============================================================================
   NetTopologySuite.Proofs.LinearizeContract
   ----------------------------------------------------------------------------
   Curve-neutral densifier contract. Clothoid and NURBS import this
   module; the circular instance is ArcLinearizeContract.

   Linearizes γ revγ pts ts n tol does not assume uniform steps.
   ts is any strictly increasing sample sequence from 0 to 1.
   The arc instance sets ts k = k/n.

   S2-style forced control vertices are a non-uniform ts: the control
   parameter sits at some index k with ts k ≠ k/n. The record does not
   require uniform spacing, so that sequence inhabits Linearizes once
   its fields are proved. The uniform arc walk is the separate instance.

   claimId: 0007-arc-linearize. witness: 0007-arc-linearize.
   3-axiom host. No Admitted / Axiom / Parameter. No RiemannInt.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals List.
From NTS.Proofs Require Import Distance Linearise.
Local Open Scope R_scope.

Definition seg_at (a b : Point) (lam : R) : Point :=
  mkPoint ((1 - lam) * px a + lam * px b)
          ((1 - lam) * py a + lam * py b).

Definition curve_shape (g : R -> Point) : Shape :=
  fun p => exists t, 0 <= t <= 1 /\ p = g t.

Definition poly_shape (pts : list Point) : Shape :=
  fun q => exists k lam d,
    (S k < length pts)%nat /\
    0 <= lam <= 1 /\
    q = seg_at (nth k pts d) (nth (S k) pts d) lam.

Record Linearizes
    (g rev_g : R -> Point) (pts : list Point) (ts : nat -> R)
    (n : nat) (tol : R) : Prop :=
  Build_Linearizes {
    lz_n : (2 <= n)%nat;
    lz_length : length pts = S n;
    lz_ts_ends : ts 0%nat = 0 /\ ts n = 1;
    lz_ts_mono : forall i j, (i < j <= n)%nat -> ts i < ts j;
    lz_on_curve : forall k, (k <= n)%nat ->
      nth k pts (g 0) = g (ts k);
    lz_hausdorff : hausdorff_le (curve_shape g) (poly_shape pts) tol;
    lz_reverse_fun : forall t, rev_g t = g (1 - t);
    lz_reverse_pts : forall k, (k <= n)%nat ->
      nth k (rev pts) (g 0) = rev_g (1 - ts (n - k)%nat)
  }.
