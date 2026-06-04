(*
  Pythagorean Theorem - A Step-by-Step Example for Absolute Beginners to Rocq/Coq

  Welcome! This file is designed for people who have *zero* experience with
  the Rocq Prover (formerly Coq) or any interactive theorem prover.

  HOW TO USE THIS FILE:
  1. Install Rocq (see docs/development-environment.md for the pinned version
     used by this project, or use the project's Dockerfile).
  2. Open this file in:
     - CoqIDE (the official IDE)
     - VS Code + "Coq" or "VSCoq" extension (recommended for most users)
     - Emacs + Proof General
  3. Use the "Next" / "Step forward" command (often Ctrl+Down, Alt+Down,
     or a button) to execute one line at a time.
  4. Watch the "Goals" window: it shows what you still need to prove.
  5. When a goal is solved, it disappears. When the file ends with "No more goals",
     the theorem is proved.

  This is *not* a full tutorial. It is a "hello world" that lets you experience
  what formal proof feels like.

  WHY PYTHAGORAS?
  - It is one of the most famous "obvious" theorems in mathematics (high-school level).
  - In a proof assistant you cannot say "it's obvious" or "draw a picture".
  - You must define *everything* precisely and justify every single step from
    the axioms of the real numbers.
  - The machine checks every rewrite, every arithmetic fact.
  - This pre-bunks a common critique of projects like NetTopologySuite.Proofs:
    "Why are you spending so much compute time and effort on formal proofs?
     Can't you just trust the math?"
  - Answer: even the "simple" Pythagorean theorem requires non-trivial
    infrastructure when you have to be 100% certain for *all* real numbers
    and have the proof checked by a computer.

  After you finish this file, look at the real theories/Distance.v in this
  project. You will see that `dist_sq_pythagorean` is proved in *one line*
  using the powerful `ring` tactic — because all the foundational work
  (defining points, distance, the ring structure of reals, etc.) has already
  been done.

  The project's 1,100+ theorems are the same idea, but applied to the
  much harder problems of robust geometric predicates that must work
  correctly for floating-point inputs without sign flips on edge cases.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.   (* For linear arithmetic automation (lra) *)
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Step 1: We need a notion of 2D point.                                      *)
(* In real mathematics we would just say "a point is a pair of reals".        *)
(* In Rocq we have to define it.                                              *)
(* -------------------------------------------------------------------------- *)

Record Point : Type := mkPoint { px : R; py : R }.

(* -------------------------------------------------------------------------- *)
(* Step 2: Define squared Euclidean distance.                                 *)
(* We use squared distance in this project (see the big comment in            *)
(* theories/Distance.v) because it avoids the square root and is easier       *)
(* to reason about algebraically.                                             *)
(* -------------------------------------------------------------------------- *)

Definition dist_sq (p q : Point) : R :=
  (px p - px q) * (px p - px q) + (py p - py q) * (py p - py q).

(* -------------------------------------------------------------------------- *)
(* Step 3: State the Pythagorean theorem in coordinate form.                  *)
(*                                                                        *)
(* Place a right angle at the origin (0,0).                                   *)
(* One leg goes to (a, 0) on the x-axis.                                      *)
(* The other leg goes to (0, b) on the y-axis.                                *)
(* The hypotenuse goes from (0,0) to (a, b).                                  *)
(*                                                                        *)
(* The theorem says: dist²((0,0), (a,b)) = a² + b².                           *)
(*                                                                        *)
(* This is exactly the lemma `dist_sq_pythagorean` that appears in the        *)
(* real theories/Distance.v of this project.                                  *)
(* -------------------------------------------------------------------------- *)

Lemma dist_sq_pythagorean : forall a b : R,
  dist_sq (mkPoint 0 0) (mkPoint a b) = a * a + b * b.
Proof.
  (* 'Proof.' starts an interactive proof script. *)

  intros a b.
  (* 'intros' moves the universally quantified variables 'a' and 'b'
     from the goal into the context (the list of things we know).
     The goal now says: prove the equality for these particular a and b. *)

  unfold dist_sq.
  (* 'unfold' replaces the name 'dist_sq' by its definition.
     This is one of the most common first steps.
     After unfolding, the goal becomes a big expression with
     (px (mkPoint 0 0) - px (mkPoint a b)) etc. *)

  simpl.
  (* 'simpl' performs obvious simplifications:
     px (mkPoint x y) simplifies to x,
     py (mkPoint x y) simplifies to y,
     0 - a becomes -a, etc.
     After 'simpl' the goal is usually much smaller. *)

  ring.
  (* 'ring' is a powerful automation tactic.
     It knows that the real numbers form a ring (you can add, multiply,
     the usual algebraic rules hold) and can solve any polynomial
     equality automatically.

     In a beginner proof you will use 'ring' a lot for the "obvious
     algebra" parts.

     Behind the scenes 'ring' is doing a huge amount of work that a
     human would do in their head in one second. This is part of why
     formal proofs consume machine time. *)

Qed.
(* 'Qed.' ends the proof and tells Rocq to check that everything was
   justified. If Rocq accepts it, the lemma is now available for use
   in other proofs. *)

(* -------------------------------------------------------------------------- *)
(* Step 4: A more explicit, "from scratch" version of the same proof.         *)
(*                                                                        *)
(* The version above is what you would actually write in a real development.  *)
(* Below we do some of the work by hand (using 'assert' and 'rewrite') to     *)
(* show you what 'ring' is doing for us.                                      *)
(* This makes the proof longer, but each step is smaller and more visible.    *)
(* -------------------------------------------------------------------------- *)

Lemma dist_sq_pythagorean_step_by_step : forall a b : R,
  dist_sq (mkPoint 0 0) (mkPoint a b) = a * a + b * b.
Proof.
  intros a b.
  unfold dist_sq.
  simpl.
  (* Current goal (after simpl):
     (0 - a) * (0 - a) + (0 - b) * (0 - b) = a * a + b * b
  *)

  (* We know from algebra that 0 - x = -x. We can ask Coq to prove it. *)
  assert (Hminus_a : 0 - a = - a).
  { ring. }   (* The curly braces open a sub-proof. We solve it with ring. *)

  assert (Hminus_b : 0 - b = - b).
  { ring. }

  (* Now we replace the subexpressions in the goal using the facts we just proved. *)
  rewrite Hminus_a.
  rewrite Hminus_b.
  (* Goal is now:
     (- a) * (- a) + (- b) * (- b) = a * a + b * b
  *)

  (* Again, basic algebra: (-x)*(-x) = x*x. *)
  assert (Hsqr_a : (- a) * (- a) = a * a).
  { ring. }

  assert (Hsqr_b : (- b) * (- b) = b * b).
  { ring. }

  rewrite Hsqr_a.
  rewrite Hsqr_b.
  (* Goal is now literally:
     a * a + b * b = a * a + b * b
  *)

  reflexivity.
  (* 'reflexivity' says "the left side is identical to the right side".
     When both sides of an equality are syntactically the same, this tactic
     succeeds. It is the most basic way to finish a goal. *)

Qed.

(* -------------------------------------------------------------------------- *)
(* Step 5: What did we learn?                                                 *)
(*                                                                        *)
(* - Even a one-line proof in the real Distance.v relies on a huge amount     *)
(*   of prior work: the definition of R, the fact that R is a ring, the       *)
(*   'ring' tactic implementation, the Record for Point, etc.                 *)
(* - Every time you use 'ring' or 'lra' or 'simpl', the machine is doing      *)
(*   non-trivial computation to verify the step.                             *)
(* - If you removed all the automation and had to apply the ring axioms       *)
(*   (associativity, commutativity, distributivity, etc.) by hand for every   *)
(*   little expression, the proof of Pythagoras would be hundreds of lines.   *)
(* - That is exactly what happens at larger scale in this project.            *)
(*   Orientation, segment intersection, snap rounding, overlay, etc. all      *)
(*   require dozens or hundreds of supporting lemmas about reals, vectors,    *)
(*   and magnitudes. Each of those lemmas is itself non-trivial.              *)
(*                                                                        *)
(* This is why "spending compute time on formal proofs" is not a waste when   *)
(* the domain is geometry libraries that must be correct for safety-critical  *)
(* or high-reliability uses. A bug in a robust predicate can lie dormant for  *)
(* years until a particular coordinate configuration appears.                 *)
(*                                                                        *)
(* Next steps for a true beginner:                                            *)
(* - Work through the Software Foundations (Logical Foundations) book.        *)
(*   It is free and excellent: https://softwarefoundations.cis.upenn.edu/     *)
(* - Then look at the real theories/Distance.v and theories/Vec.v in this     *)
(*   project. You will recognize the same 'unfold', 'simpl', 'ring', 'lra'    *)
(*   pattern, just applied to many more lemmas.                               *)
(* - Read the actor cards in docs/HELP.md to see where you fit.               *)
(*                                                                        *)
(* The rest of this corpus is the same style of work, but for the hard parts  *)
(* of computational geometry instead of high-school Pythagoras.               *)
(* -------------------------------------------------------------------------- *)

(* For completeness, here is the exact lemma as it appears in the project's
   theories/Distance.v (the one-line version that real developers write). *)

Lemma project_style_dist_sq_pythagorean : forall a b : R,
  dist_sq (mkPoint 0 0) (mkPoint a b) = a * a + b * b.
Proof.
  intros a b. unfold dist_sq. simpl. ring.
Qed.

(* End of beginner example. *)
