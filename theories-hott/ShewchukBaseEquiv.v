(* ============================================================================
   NetTopologySuite.HoTT.ShewchukBaseEquiv
   ----------------------------------------------------------------------------
   HoTT-style linkage for the foundational Shewchuk exact orientation predicate.

   This is the "first real Shewchuk" / base equivalence in the RGR for the
   next big chunk (TIN / Hobby / Shewchuk / Curve) as analysed in
   `docs/hott-rgr-tin-hobby-shewchuk-curve-pivot.md`.

   Orientation (robust left-turn / CCW test) is the single most load-bearing
   geometric predicate: Delaunay, Voronoi (dual), TIN, Hobby curve lemmas,
   arc predicates, noding, overlay, everything composes on top of it.
   The classical corpus invested heavily in Shewchuk expansions + binary64
   exact sign (see B64_*_Shewchuk.v and the 7-piece Slice A structure).

   In HoTT: We define
     - formal geometric orient (sign of cross, exact over reals)
     - Shewchuk expansion model (the "how" of exactness, re-expressed)
     - NTS mirror (abstract model of C# RobustDeterminant.OrientationIndex)
   and prove (skeleton) that they are equivalent in the HoTT sense so that
   any theorem about formal orient transports to the NTS implementation
   (and to a b64 instance once Flocq bridge is re-expressed).

   Uses exactly one axiom: Univalence (justified for C# linkage / transport
   of orientation properties; per `docs/axiom-policy.md` and root README).
   All else Qed/Defined or loud Admitted with discharge plan.

   "Why Shewchuk first?" (per PR #89 review feedback):
   - It is the narrowest, highest-leverage primitive: every higher predicate
     (incircle for Delaunay/Voronoi, Hobby 4.1/4.3, TIN endpoints, arc
     orientation tests, curve linearise) ultimately reduces to orient/incircle
     decisions. Getting a solid orient_equiv + one transport example here
     gives a foundation that later chunks can cite via transport rather than
     re-proving from scratch.
   - The archive already has substantial Qed work (B64_Shewchuk_*, Orient_b64_* )
     that can be mined for the real proof of the maps/IsEquiv rather than
     invented.
   - Low risk/cost per the table in the chunk RGR doc: small surface, re-uses
     existing classical investment, immediate "we have proved the link for
     the base predicate that everything else trusts".
   - Deferred: full Thm 13 (the hard monotonicity/expansion growth lemmas),
     Hobby 4.x, TIN/CurveLinearise, native curves. Those come after this base
     is GREEN + filled.

   References (for transport/re-expression of the real proofs):
   - Archived `archive/theories-flocq/B64_Expansion_Shewchuk.v` (nonoverlap_shewchuk,
     sign_of_expansion_correct_shewchuk, compress, the weakened predicate that
     actually survives FastExpansionSum).
   - Archived `archive/theories-flocq/B64_FastExpansionSum_Shewchuk.v` and Route2.
   - Archived `archive/theories-flocq/B64_Shewchuk_Thm13_pathA_defect.v` (the
     known defect path for Thm13; documents what was hard).
   - Archived `archive/theories/Orientation.v` (cross, antisym, collinearity
     invariants, scaling/translation invariance — these become the "formal_orient
     satisfies geometry" side of the equiv).
   - Archived `archive/theories-flocq/Orient_b64_exact.v`, `Orient_b64_sound.v`,
     `Orient_b64_expansion.v` (the b64 bridges and soundness that we want to
     transport across the NTS ≃ formal link).
   - VoronoiEquivalence.v (this builds on the same Point + cross ideas; the
     Voronoi cell predicate is defined using orient in the full Delaunay dual).

   Build note (HoTT era): same as VoronoiEquivalence.v — self-contained with
   custom Equiv/IsEquiv records (no external HoTT lib required for the skeleton).
   The one axiom is Univalence. (pythagoras-for-beginners.v remains the
   classical on-ramp.)

   Author: (HoTT pivot contributors, following RGR)
   License: BSD-3-Clause
   ========================================================================== *)

(* We work in a HoTT setting. For classical base (Points, cross, orientation
   invariants) we re-express minimal pieces from the kept pythagoras +
   archived Orientation.v + B64_Shewchuk expansions. Keep self-contained for
   the equivalence skeleton so it stands alone as a small high-value link. *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import List.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Minimal shared geometry (re-expressed / will be transported from archive). *)
(* Point + cross (twice signed area) from archived Orientation.v.             *)
(* -------------------------------------------------------------------------- *)

Record Point : Type := mkPoint { px : R; py : R }.

Definition cross (p0 p1 q : Point) : R :=
  (px p1 - px p0) * (py q - py p0)
  - (px q - px p0) * (py p1 - py p0).

(* Re-expressed from archive/theories/Orientation.v (delivered as fill RGR   *)
(* infrastructure per the outcome note; used in degenerate proof + ready for *)
(* antisym etc.).                                                            *)
Lemma cross_antisymmetric : forall p0 p1 q,
  cross p0 p1 q = - cross p0 q p1.
Proof.
  intros. unfold cross. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Formal geometric orientation (exact).                                     *)
(* Dir encodes the trichotomy that the sign of cross gives.                  *)
(* In the full development this is proved to satisfy all the cross_* lemmas  *)
(* from archive/theories/Orientation.v (antisym, collinear sym, translation  *)
(* invariance, scaling, etc.).                                               *)
(* -------------------------------------------------------------------------- *)

Inductive Dir : Type := CCW | CW | COLLINEAR.

(* The formal (exact, real-arithmetic) orientation predicate.                *)
(* Defined as the sign of the cross product (twice signed area), matching    *)
(* the classical definition in archive/theories/Orientation.v (re-expressed  *)
(* here for the HoTT equiv layer).                                           *)
Definition formal_orient (p0 p1 q : Point) : Dir :=
  let c := cross p0 p1 q in
  if Rlt_dec c 0 then CW
  else if Rgt_dec c 0 then CCW
  else COLLINEAR.

(* For convenience alias — "exact" means the mathematical geometry one.      *)
Definition exact_orient := formal_orient.

(* Real Qed progress for this fill RGR slice (degenerate/collinear case,     *)
(* ported from archive cross invariants).                                    *)
Lemma formal_orient_degenerate (p0 p1 : Point) :
  formal_orient p0 p1 p0 = COLLINEAR.
Proof.
  unfold formal_orient.
  assert (cross p0 p1 p0 = 0) by (unfold cross; ring).
  rewrite H.
  destruct (Rlt_dec 0 0); destruct (Rgt_dec 0 0); try reflexivity; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Shewchuk expansion model (the exactness engine from the archive).         *)
(* In the classical corpus the b64 exact orient is built by:                 *)
(*   compress + nonoverlap_shewchuk + fast-expansion-sum + sign_of_expansion *)
(*   + compose into orient2d_exact_sign_correct.                             *)
(* Here we model the "expansion" and a sign function abstractly for the      *)
(* skeleton; the real proof will re-express or transport the Qed lemmas      *)
(* from B64_Expansion_Shewchuk.v etc.                                        *)
(* -------------------------------------------------------------------------- *)

Record Expansion : Type := mkExpansion { coeffs : list R }.

(* Shewchuk-style sign of an expansion (the key that lets us do exact orient *)
(* without fp error). For skeleton we Admitted the decision procedure.       *)
Definition sign_of_expansion (e : Expansion) : Dir.
Admitted.

(* The Shewchuk orient (p0,p1,q) computed via two expansions (for the two    *)
(* terms in the cross) and their difference sign. This is the "bridge"       *)
(* implementation that the b64 oracles actually ran.                         *)
Definition shewchuk_orient (p0 p1 q : Point) : Dir :=
  formal_orient p0 p1 q.
(* For this fill RGR step: Shewchuk model is the formal exact (the expansion
   sign_of_expansion will be the refinement in next bounded work, per
   B64_Expansion_Shewchuk.v). This lets us make orient_equiv maps id-based. *)

(* -------------------------------------------------------------------------- *)
(* NTS-side model (abstract mirror of C# NetTopologySuite).                  *)
(* In real NTS: RobustDeterminant.OrientationIndex(p0, p1, q) returns        *)
(*   +1 (CCW / LEFT), -1 (CW / RIGHT), 0 (COLLINEAR / ON_SEGMENT etc.).       *)
(* We model the observable behaviour as a Dir for direct comparison.         *)
(* This is the "NTSOrient" that we will prove equivalent to the formal one.  *)
(* -------------------------------------------------------------------------- *)

Definition nts_orient (p0 p1 q : Point) : Dir :=
  formal_orient p0 p1 q.
(* For the NTS model in this stage, we take it to coincide with the formal verified one (the "C# RobustDeterminant" is assumed to match the exact; the b64 oracle/expansion will provide the justification in the full link). *)

(* -------------------------------------------------------------------------- *)
(* Equivalence in HoTT sense.                                                *)
(* We show that the formal geometric orient is equivalent to the NTS         *)
(* implementation (the link). Shewchuk expansions are the witness on one   *)
(* side; properties (e.g. orient-is-antisymmetric / collinear-is-translation-invariant)
   transport via univalence.                                                 *)
(* -------------------------------------------------------------------------- *)

(* HoTT primitives — duplicated per small-equiv module for self-contained    *)
(* skeletons (we can factor later once we have two+ working examples).       *)

Record IsEquiv {A B} (f : A -> B) := mkIsEquiv
  { equiv_inv : B -> A
  ; equiv_sect : forall x, f (equiv_inv x) = x   (* section *)
  ; equiv_retr : forall x, equiv_inv (f x) = x   (* retraction *)
  ; equiv_adj : forall (x : A), True   (* coherence placeholder; see header for why one axiom *)
  }.

Record Equiv (A B : Type) := mkEquiv
  { equiv_fun : A -> B
  ; equiv_isequiv : IsEquiv equiv_fun
  }.

(* The one allowed axiom (Univalence). This is the "generous" one per policy.*)
(* It says equivalences are paths (identities) in the universe.              *)
(* This is what lets us transport theorems across the NTS <-> formal link    *)
(* for the base predicate that Delaunay, TIN, Hobby, curves etc. all trust.  *)
(* Justification: without univalence we have no principled transport of      *)
(* "NTS orient behaves exactly as the verified geometric orient" into the    *)
(* C# call sites. The cost is paid exactly once here and cited by dependents.*)
(* What it would take to remove: a full computational model of NTS's         *)
(* RobustDeterminant that computes the same Dir, plus a proof that it        *)
(* coincides with formal_orient (no axiom, but much more work).              *)
Axiom univalence : forall (A B : Type), Equiv A B -> A = B.

(* The equivalence (core statement of the Shewchuk base link).               *)
(* We claim formal/exact orient ≃ NTS orient (with Shewchuk as the concrete  *)
(* exact implementation path). In a full development the IsEquiv witness     *)
(* is built from the classical sign-correctness + soundness lemmas.          *)
Definition orient_equiv :
  Equiv (Point -> Point -> Point -> Dir) (Point -> Point -> Point -> Dir) :=
  mkEquiv _ _ (fun f => f)
    (mkIsEquiv _ _ (fun f => f) (fun f => f) (fun _ => eq_refl) (fun _ => eq_refl) (fun _ => I)).
(* For this stage, since shewchuk_orient and nts_orient are both aliases to the
   formal (the "exact" and the "NTS mirror" coincide in the model), the equivalence
   is the identity (with trivial IsEquiv). This sets up the transport mechanism.
   The full non-trivial witness (using b64 expansions to justify the match between
   formal and actual NTS) will come when we fill the remaining Admitteds. *)

(* The one axiom in action: univalence gives us a path between the two function
   types, allowing transport of properties (the "link"). *)
Lemma orient_types_equal_via_univalence :
  (Point -> Point -> Point -> Dir) = (Point -> Point -> Point -> Dir) :> Type.
Proof.
  change ( (Point -> Point -> Point -> Dir) = (Point -> Point -> Point -> Dir) :> Type ).
  apply univalence.
  exact orient_equiv.
Qed.

(* -------------------------------------------------------------------------- *)
(* Transport example (the payoff of the HoTT link).                          *)
(* Any theorem proved about formal_orient (e.g. cross_antisymmetric from     *)
(* the archive, re-expressed) can be transported to the NTS side.            *)
(* -------------------------------------------------------------------------- *)

(* Example formal property (re-expressed from archive/theories/Orientation.v). *)
Lemma formal_orient_antisym (p0 p1 q : Point) :
  formal_orient p0 p1 q = match formal_orient p0 q p1 with
                          | CCW => CW
                          | CW => CCW
                          | COLLINEAR => COLLINEAR
                          end.
Proof.
  (* Using the locally re-expressed cross_antisymmetric + concrete formal_orient *)
  (* definition. Case analysis on the sign decisions for d = cross p0 q p1 and *)
  (* -d directly gives the Dir swap. This is the small "transport example"     *)
  (* (formal antisym property proved) recommended in the PR #92 review.        *)
  unfold formal_orient.
  rewrite cross_antisymmetric.
  set (d := cross p0 q p1).
  destruct (Rlt_dec d 0); destruct (Rgt_dec d 0);
  destruct (Rlt_dec (-d) 0); destruct (Rgt_dec (-d) 0);
  try (exfalso; lra); reflexivity.
Qed.

(* The transported property on the NTS side.                                 *)
Lemma nts_orient_antisym (p0 p1 q : Point) :
  (* By univalence + orient_equiv we can transport the antisym fact.         *)
  (* In practice:                                                            *)
  (*   let eqv := orient_equiv in                                            *)
  (*   let path := univalence eqv in                                         *)
  (*   transport (fun f => forall ... , f p0 p1 q = match f p0 q p1 ...)     *)
  (*             path formal_orient_antisym                                  *)
  (* gives the version that holds for nts_orient.                            *)
  nts_orient p0 p1 q = match nts_orient p0 q p1 with
                       | CCW => CW
                       | CW => CCW
                       | COLLINEAR => COLLINEAR
                       end.
Proof.
  (* Since nts_orient is defined as formal_orient in this model stage, the    *)
  (* property follows directly from the now-Qed formal_orient_antisym.        *)
  (* In a full development, this would be obtained by transport along the     *)
  (* path given by univalence orient_equiv (see orient_types_equal_via_univalence). *)
  unfold nts_orient.
  apply formal_orient_antisym.
Qed.

(* -------------------------------------------------------------------------- *)
(* Notes for continuation (RGR style, per chunk decision).                   *)
(* - Formal side + model aliases + id equiv + univalence demo + one Qed      *)
(*   transport example (antisym) landed (this slice).                        *)
(* - Next: wire real IsEquiv/maps from the B64_Expansion_Shewchuk.v +        *)
(*   sign_of_expansion_correct_shewchuk + Orient_b64_exact/sound lemmas      *)
(*   (the classical already did the hard work; we need the equiv wrapper).   *)
(* - Once the real orient_equiv is Qed, subsequent chunks (Hobby, TIN,       *)
(*   Curve) + Voronoi can cite "transport (univalence orient_equiv)          *)
(*   formal_foo".                                                            *)
(* - Add incircle base (dual to orient; archived InCircle_b64 + ArcOrient).  *)
(* - This is the "Shewchuk first" step recommended by the chunk RGR and the  *)
(*   PR #89 review. Bounded scope per slice.                                 *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* Hobby noding RGR start (per chunk decision after Shewchuk base solid).    *)
(* Re-express b64 Hobby lemmas (4.1/4.3 biarc approximation, residual        *)
(* monotonicity) using transport via orient_equiv (univalence) for the NTS   *)
(* linkage. Start NTS_Hobby model equiv. See archived HobbyTheorem_b64.v.    *)
(* This branch: feature/hott-rgr-hobby-noding.                               *)
(* ========================================================================== *)