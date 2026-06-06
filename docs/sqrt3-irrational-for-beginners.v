(*
  sqrt(3) is Irrational — A Number-Theory Example for Coq/Rocq Beginners

  See also the short companion note `docs/sqrt3-irrational.md` for an
  even more explicit "what this file does *not* claim about tilings".

  Welcome back! If you have worked through `pythagoras-for-beginners.v`,
  you already know the basic rhythm: define things precisely with Records
  and Definitions, state a clear Lemma/Theorem, and justify every single
  step so the machine can check it.

  This file continues that spirit, but now we move into *number theory*
  over the integers (Z) and then lift the result to the reals (R).

  HOW TO USE THIS FILE (same as pythagoras):
  - Open in CoqIDE, VS Code + VSCoq, or Emacs + Proof General.
  - Step forward line-by-line.
  - Watch the Goals window.
  - When you see "No more goals", the theorem is proved.

  WHAT WE WILL PROVE
  ------------------
  Theorem: sqrt 3 is irrational.
  That is: there are no integers p and q (with q ≠ 0) such that

      sqrt 3 = p / q

  (In Rocq notation:  `sqrt 3 <> IZR p / IZR q` when `q <> 0%Z`.)

  This is a classic result, traditionally proved by "infinite descent"
  (a method invented by Fermat).  We will follow that method, but every
  step will be checked by the computer.

  IMPORTANT HONESTY NOTE (the project philosophy)
  ----------------------------------------------
  This file proves *only* the number-theoretic statement above.

  It says *nothing* about:
  - aperiodic tilings,
  - the "einstein" monotile (the Spectre),
  - whether the hat or Spectre tile the plane,
  - any property of the hex grid used in HatMonotile.v or HexXScaleBridge.v.

  In the actual geometry code of this project we use `sqrt 3` *explicitly*
  (see `hexPt` in HatMonotile.v and the scaling in HexXScaleBridge.v).
  We never need to know that it is irrational for the lemmas we care about
  (closed rings, correct ray parity, non-convexity via `cross`, etc.).
  The tactics `lra`, `nra`, and `field` already know how to handle `sqrt 3`
  when they need to.

  The irrationality of `sqrt 3` is a beautiful fact in its own right,
  and a wonderful teaching example of descent and of moving between
  the integers (Z) and the reals (R).  That is why we include it here
  as a follow-on to the Pythagoras beginner file.

  The real geometric work in this corpus lives in the files under
  `theories/`.  This file is deliberately a side quest for learning.
*)

From Stdlib Require Import ZArith Znumtheory Reals Lra Lia.

Local Open Scope Z_scope.

(* ==========================================================================
   PART 1 — The integer heart of the proof

   We first prove a purely integer statement:

       If a*a = 3*(b*b) for integers a and b, then a = 0.

   Once we have that, the real-number statement follows easily.

   The proof uses *infinite descent*: we show that any nonzero solution
   would give a strictly smaller positive solution, which is impossible.
   ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* Step 1: 3 is prime, so if 3 divides a product, it divides one of the factors. *)
(* -------------------------------------------------------------------------- *)

(* In ordinary mathematics we just say "3 is prime, hence Euclid's lemma".
   In Rocq we must cite the exact lemma that has already been proved in
   the standard library. *)
Lemma euclid3 : forall a : Z, (3 | a * a) -> (3 | a).
Proof.
  intros a H.
  (* 'prime_mult' is the general statement: if a prime p divides x*y,
     then p divides x or p divides y. *)
  destruct (prime_mult 3 prime_3 a a H) as [Ha | Ha].
  - exact Ha.
  - exact Ha.
Qed.

(* -------------------------------------------------------------------------- *)
(* Step 2: The descent lemma (the engine of the proof)                        *)
(*                                                                        *)
(* We prove a *bounded* version first:
     If |a| ≤ n  (measured in natural numbers) and a² = 3 b²,
     then a = 0.
   This lets us do induction on the size of a.                            *)
(* -------------------------------------------------------------------------- *)

Lemma descent3 : forall (n : nat) (a b : Z),
  (Z.to_nat (Z.abs a) <= n)%nat ->
  a * a = 3 * (b * b) ->
  a = 0.
Proof.
  induction n as [| n IHn]; intros a b Hn Heq.
  - (* Base case: the only integer whose absolute value is ≤ 0 is 0. *)
    assert (Z.abs a = 0) by lia.
    lia.
  - (* Inductive case: assume the statement is true for n; prove it for S n. *)
    destruct (Z.eq_dec a 0) as [Ha0 | Hna]; [ exact Ha0 | exfalso ].

    (* Because a² = 3 b², 3 divides a², hence (by euclid3) 3 divides a. *)
    assert (Hda : (3 | a)).
    { apply euclid3. exists (b * b). lia. }
    destruct Hda as [a' Ha'].   (* Now we know a = 3 * a' *)

    rewrite Ha' in Heq.
    (* a' * a' * 9 = 3 * b * b   =>   a' * a' = 3 * (b*b / 3) *)
    assert (Hb2 : b * b = 3 * (a' * a')) by nia.

    (* Symmetrically, 3 divides b. *)
    assert (Hdb : (3 | b)).
    { apply euclid3. exists (a' * a'). lia. }
    destruct Hdb as [b' Hb'].   (* b = 3 * b' *)

    rewrite Hb' in Hb2.
    assert (Heq3 : a' * a' = 3 * (b' * b')) by nia.

    (* a' cannot be zero (otherwise a would have been zero). *)
    assert (Ha'0 : a' <> 0).
    { intro Hz. subst a'. apply Hna. lia. }

    (* Crucial: |a'| < |a| (because a = 3*a' and a ≠ 0).
       Therefore the "size" of a' (measured in nat) is strictly smaller
       than the size of a, so it is ≤ n.  We may apply the induction
       hypothesis. *)
    assert (Habs : Z.abs a = 3 * Z.abs a').
    { rewrite Ha', Z.abs_mul. lia. }

    assert (Hpos : 1 <= Z.abs a') by (apply Z.abs_pos in Ha'0; lia).

    assert (Hmeas : (Z.to_nat (Z.abs a') <= n)%nat).
    { assert (Z.to_nat (Z.abs a) = (3 * Z.to_nat (Z.abs a'))%nat).
      { rewrite Habs. rewrite Z2Nat.inj_mul by lia. reflexivity. }
      lia. }

    (* Here is the descent: a' is a smaller solution to the same equation. *)
    exact (Ha'0 (IHn a' b' Hmeas Heq3)).
Qed.

(* -------------------------------------------------------------------------- *)
(* Step 3: The clean integer statement                                        *)
(* -------------------------------------------------------------------------- *)

Lemma no_int_solution : forall a b : Z,
  a * a = 3 * (b * b) -> a = 0.
Proof.
  intros a b H.
  (* We just instantiate the descent lemma with a big enough n. *)
  apply (descent3 (Z.to_nat (Z.abs a)) a b); [ lia | exact H ].
Qed.

(* ==========================================================================
   PART 2 — Lifting the result to the real numbers

   Now that we know there are no nonzero integers satisfying a² = 3 b²,
   we can easily show that sqrt 3 cannot be a ratio of two integers.
   ========================================================================== *)

Local Open Scope R_scope.

Theorem sqrt3_irrational : forall p q : Z,
  q <> 0%Z -> sqrt 3 <> IZR p / IZR q.
Proof.
  intros p q Hq Hcontra.

  assert (Hqr : IZR q <> 0) by (apply IZR_neq; exact Hq).

  (* Multiply both sides by the denominator to clear the fraction. *)
  assert (Hpq : sqrt 3 * IZR q = IZR p).
  { rewrite Hcontra. field. exact Hqr. }

  (* Square both sides.  We know (sqrt 3)² = 3. *)
  assert (Hsq3 : sqrt 3 * sqrt 3 = 3) by (apply sqrt_sqrt; lra).

  assert (HR : IZR p * IZR p = 3 * (IZR q * IZR q)).
  { rewrite <- Hpq.
    replace (sqrt 3 * IZR q * (sqrt 3 * IZR q))
       with ((sqrt 3 * sqrt 3) * (IZR q * IZR q)) by ring.
    rewrite Hsq3. ring. }

  (* Convert the real equality back into an integer equality. *)
  assert (HZ : (p * p = 3 * (q * q))%Z).
  { apply eq_IZR.
    rewrite !mult_IZR.
    replace (IZR 3) with 3 by (simpl; ring).
    exact HR. }

  (* Now apply the integer lemma we proved earlier. *)
  pose proof (no_int_solution p q HZ) as Hp0.
  (* p = 0, therefore 3 q² = 0 in the reals, so q = 0 — contradiction. *)
  apply Hq.
  subst p.
  assert (q * q = 0)%Z by nia.
  nia.
Qed.

(* -------------------------------------------------------------------------- *)
(* What did we learn? (the pedagogical takeaway)                              *)
(* -------------------------------------------------------------------------- *)

(*
  1. Infinite descent is a beautiful and powerful proof technique.
     "If there were a positive solution, there would be a strictly smaller
      positive solution — impossible."

  2. Moving between Z and R is delicate but mechanical.
     - `IZR` embeds integers into reals.
     - `mult_IZR`, `eq_IZR`, etc. let us transport equalities.
     - Once we are back in Z we can use powerful integer tactics (`nia`, `lia`).

  3. Even "elementary" number theory requires care when formalised.
     Every divisibility step, every measure decrease, every sign case
     must be justified.

  4. (The honesty lesson again)  In the real geometric work of this
     corpus we almost never need this fact.  We keep `sqrt 3` in the
     expressions (see `hexPt` and the x-scale bridge) and let `lra`/`nra`/
     `field` do the heavy lifting.  The irrationality proof is here
     purely because it is an excellent teaching example of descent and
     of the Z ↔ R relationship.

  Next steps for a beginner who enjoyed this file:
  - If you haven't already, work through the "Logical Foundations" volume
    of Software Foundations (https://softwarefoundations.cis.upenn.edu/).
  - Look at how the real project uses `R` directly in `theories/Distance.v`,
    `theories/Orientation.v`, `theories/Overlay.v`, etc.
  - Try to prove a few small facts about `sqrt 2` being irrational using
    the same pattern (it is easier than sqrt 3 because you don't need
    a separate primality lemma for 2).

  The rest of NetTopologySuite.Proofs is the same spirit — precise
  definitions + machine-checked justification — but applied to the
  surprisingly subtle questions that arise when you try to make
  computational geometry robust for all possible inputs.
*)

(* End of sqrt(3) irrationality beginner example. *)
