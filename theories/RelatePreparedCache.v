(* ============================================================================
   NetTopologySuite.Proofs.RelatePreparedCache
   ----------------------------------------------------------------------------
   Issue #67 — prepared-mode cache correctness (ask #5; NTS#819 / JTS#1099).

   RelateNG offers a *prepared* path: `RelateNG.prepare(A)` builds spatial
   indexes over A once, and each subsequent `evaluate(B)` reuses them.  The
   correctness obligation is a REFINEMENT (memoisation) statement, not a new
   geometric fact: the prepared answer must equal the one-shot answer

       evaluate(prepare(A), B)  =  relate(A, B)

   regardless of how the cache is built or in what order the index returns its
   candidates.  This is exactly the "result-independent-of-cache-path" property
   the NTS#819 perf work must preserve.

   A spatial index (STRtree) used for relate/overlay has one externally
   observable contract: a query with envelope `qb` returns precisely the
   indexed items whose envelope is NOT disjoint from `qb` — each such item once,
   in some index-internal order.  We model that contract directly: the query
   result is a PERMUTATION of `filter keep items`, where `keep` is the
   bbox-overlap test.  Under that contract we prove the prepared evaluation
   equals the brute-force all-pairs evaluation, for any contribution that forms
   a commutative monoid and for which bbox-disjoint candidates contribute the
   neutral element (the soundness of envelope rejection — `Bbox.v`).

   Two layers:

     - GENERIC (`evaluate_eq_brute`, `evaluate_path_independent`): any commutative
       monoid + drop-sound filter; the index is abstract (its query is any
       permutation of the kept items).  No geometry.
     - CONCRETE (`prepared_intersects_eq_brute`): the boolean "does any segment
       of A intersect segment t" predicate, with `keep` = bbox-overlap and the
       drop-soundness discharged from `Bbox.disjoint_bboxes_imply_no_shared_point`.

   No `Admitted`, no `Axiom`, no `Parameter` (Section variables are discharged).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import List Permutation Reals Lra Bool.
From NTS.Proofs Require Import Segment Bbox.
Import ListNotations.
Open Scope R_scope.

(* ========================================================================== *)
(* 0. List-fold building blocks (fully general).                               *)
(* ========================================================================== *)

Lemma negb_false_iff : forall b : bool, negb b = false <-> b = true.
Proof.
  intros b. destruct b; split; auto.
Qed.

Lemma Permutation_map :
  forall (A B : Type) (f : A -> B) l l',
    Permutation l l' -> Permutation (map f l) (map f l').
Proof.
  intros A B f l l' H.
  induction H as [|x l l' IH|x y l|l l' l'' IH1 IH2]; simpl.
  - apply perm_nil.
  - apply perm_skip. exact IHIH.
  - apply perm_swap.
  - eapply perm_trans; eauto.
Qed.

(* Folding a commutative-associative operation is permutation invariant. *)
Lemma fold_right_permutation :
  forall {A : Type} (op : A -> A -> A) (e : A),
    (forall x y, op x y = op y x) ->
    (forall x y z, op x (op y z) = op (op x y) z) ->
    forall l l', Permutation l l' ->
      fold_right op e l = fold_right op e l'.
Proof.
  intros A op e comm assoc l l' Hperm.
  induction Hperm; simpl.
  - reflexivity.
  - now rewrite IHHperm.
  - now rewrite assoc, (comm y x), <- assoc.
  - rewrite IHHperm1. exact IHHperm2.
Qed.

(* Items the filter rejects contribute the neutral element, so dropping them
   leaves the fold unchanged.  (Only a left identity is needed.) *)
Lemma fold_filter_drop :
  forall {I A : Type} (op : A -> A -> A) (e : A) (f : I -> A) (keep : I -> bool),
    (forall x, op e x = x) ->
    (forall i, keep i = false -> f i = e) ->
    forall l,
      fold_right op e (map f (filter keep l)) = fold_right op e (map f l).
Proof.
  intros I A op e f keep id_l drop l.
  induction l as [| a l IH]; simpl.
  - reflexivity.
  - destruct (keep a) eqn:Hk; simpl.
    + now rewrite IH.
    + rewrite (drop a Hk), id_l. exact IH.
Qed.

(* ========================================================================== *)
(* 1. Generic prepared-vs-brute refinement.                                    *)
(* ========================================================================== *)

Section Generic.
  Context {I A : Type}.

  (* The accumulated answer lives in a commutative monoid (op, e). *)
  Variable op : A -> A -> A.
  Variable e : A.
  Hypothesis op_comm  : forall x y, op x y = op y x.
  Hypothesis op_assoc : forall x y z, op x (op y z) = op (op x y) z.
  Hypothesis op_id_l  : forall x, op e x = x.

  (* Per-item contribution and the index's bbox-overlap retention test. *)
  Variable f    : I -> A.
  Variable keep : I -> bool.

  (* Envelope rejection is sound: a candidate the index drops contributes the
     neutral element (it cannot affect the answer). *)
  Hypothesis drop_sound : forall i, keep i = false -> f i = e.

  (* The full set of A's indexed items. *)
  Variable items : list I.

  (* Evaluating over an arbitrary candidate list. *)
  Definition eval_list (q : list I) : A := fold_right op e (map f q).

  (* Brute force: evaluate over every item, no index. *)
  Definition brute : A := eval_list items.

  (* A query result is any permutation of the kept items (the STRtree contract:
     it returns each bbox-overlapping item exactly once, in index order). *)
  Definition valid_query (q : list I) : Prop :=
    Permutation q (filter keep items).

  (* THE REFINEMENT: a prepared evaluation over any valid query equals brute. *)
  Theorem evaluate_eq_brute :
    forall q, valid_query q -> eval_list q = brute.
  Proof.
    intros q Hq. unfold valid_query in Hq. unfold brute, eval_list.
    rewrite <- (fold_filter_drop op e f keep op_id_l drop_sound items).
    apply fold_right_permutation; auto using Permutation_map.
  Qed.

  (* CACHE-PATH INDEPENDENCE (the NTS#819 obligation made explicit): any two
     index implementations / build orders that honour the query contract give
     the same answer. *)
  Corollary evaluate_path_independent :
    forall q1 q2, valid_query q1 -> valid_query q2 -> eval_list q1 = eval_list q2.
  Proof.
    intros q1 q2 H1 H2.
    rewrite (evaluate_eq_brute q1 H1), (evaluate_eq_brute q2 H2). reflexivity.
  Qed.

End Generic.

(* ========================================================================== *)
(* 2. Decidable bbox overlap (the index's retention predicate).               *)
(* ========================================================================== *)

Definition Rlt_b (a b : R) : bool := if Rlt_dec a b then true else false.

Lemma Rlt_b_true : forall a b, Rlt_b a b = true <-> a < b.
Proof.
  intros a b. unfold Rlt_b.
  destruct (Rlt_dec a b) as [Hlt|Hnlt].
  - split; [intros _; exact Hlt | intros _; reflexivity].
  - split; [discriminate | lra].
Qed.

(* Boolean reflection of `bbox_disjoint`. *)
Definition bbox_disjoint_b (b1 b2 : Bbox) : bool :=
  Rlt_b (xhi b1) (xlo b2) || Rlt_b (xhi b2) (xlo b1) ||
  Rlt_b (yhi b1) (ylo b2) || Rlt_b (yhi b2) (ylo b1).

Lemma bbox_disjoint_b_spec :
  forall b1 b2, bbox_disjoint_b b1 b2 = true <-> bbox_disjoint b1 b2.
Proof.
  intros b1 b2. unfold bbox_disjoint_b, bbox_disjoint.
  rewrite !orb_true_iff, !Rlt_b_true. tauto.
Qed.

(* The index keeps a candidate iff its envelope is NOT disjoint from the query
   envelope — i.e. the two envelopes overlap. *)
Definition bbox_overlap_keep (qb : Bbox) (s : Segment) : bool :=
  negb (bbox_disjoint_b (bbox_of_seg s) qb).

Lemma keep_false_disjoint :
  forall qb s,
    bbox_overlap_keep qb s = false ->
    bbox_disjoint (bbox_of_seg s) qb.
Proof.
  intros qb s H. unfold bbox_overlap_keep in H.
  apply negb_false_iff in H. apply bbox_disjoint_b_spec in H.
  exact H.
Qed.

(* ========================================================================== *)
(* 3. Concrete instance: prepared "intersects segment t" = brute force.        *)
(* ========================================================================== *)

Section ConcreteIntersects.

  (* A pluggable, *sound* boolean segment-intersection test (the role NTS's
     LineIntersector plays).  Soundness: a `true` verdict witnesses a genuine
     shared point on both closed segments. *)
  Variable intersect_test : Segment -> Segment -> bool.
  Hypothesis intersect_test_sound :
    forall s t, intersect_test s t = true ->
      exists X, between (sp0 s) (sp1 s) X /\ between (sp0 t) (sp1 t) X.

  (* The B-segment being evaluated and the A-segments held by the prepared
     geometry. *)
  Variable t : Segment.
  Variable a_segs : list Segment.

  (* The index uses t's envelope as the query box. *)
  Let qb : Bbox := bbox_of_seg t.

  (* Per-candidate contribution into the boolean "any intersection" monoid. *)
  Let contrib (s : Segment) : bool := intersect_test s t.

  (* Envelope rejection is sound at this contribution: a dropped (bbox-disjoint)
     candidate cannot intersect t, so it contributes `false`.  This is the
     geometric content, discharged from Bbox.v. *)
  Lemma intersects_drop_sound :
    forall s, bbox_overlap_keep qb s = false -> contrib s = false.
  Proof.
    intros s Hk. unfold contrib.
    destruct (intersect_test s t) eqn:Hit; [exfalso | reflexivity].
    apply (disjoint_bboxes_imply_no_shared_point s t).
    - exact (keep_false_disjoint qb s Hk).
    - exact (intersect_test_sound s t Hit).
  Qed.

  (* Brute-force "does any A-segment intersect t". *)
  Definition intersects_any_brute : bool :=
    fold_right orb false (map contrib a_segs).

  (* Prepared evaluation over an index query. *)
  Definition intersects_any_prepared (q : list Segment) : bool :=
    fold_right orb false (map contrib q).

  (* THE CONCRETE REFINEMENT: the prepared boolean predicate, evaluated over any
     spatial-index query honouring the bbox-overlap contract, equals brute force. *)
  Theorem prepared_intersects_eq_brute :
    forall q,
      Permutation q (filter (bbox_overlap_keep qb) a_segs) ->
      intersects_any_prepared q = intersects_any_brute.
  Proof.
    intros q Hq. unfold intersects_any_prepared, intersects_any_brute.
    rewrite <- (fold_filter_drop orb false contrib (bbox_overlap_keep qb)
      orb_false_l intersects_drop_sound a_segs).
    apply (fold_right_permutation orb false orb_comm); auto using Permutation_map.
    intros x y z. destruct x, y, z; reflexivity.
  Qed.

  (* And it is independent of which conforming index / build order produced q. *)
  Corollary prepared_intersects_path_independent :
    forall q1 q2,
      Permutation q1 (filter (bbox_overlap_keep qb) a_segs) ->
      Permutation q2 (filter (bbox_overlap_keep qb) a_segs) ->
      intersects_any_prepared q1 = intersects_any_prepared q2.
  Proof.
    intros q1 q2 H1 H2.
    rewrite (prepared_intersects_eq_brute q1 H1),
            (prepared_intersects_eq_brute q2 H2). reflexivity.
  Qed.

End ConcreteIntersects.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions evaluate_eq_brute.
Print Assumptions evaluate_path_independent.
Print Assumptions prepared_intersects_eq_brute.