(* ============================================================================
   NetTopologySuite.Proofs.RayParityDegenerate
   ----------------------------------------------------------------------------
   Issue #67 (curve→matrix transport foundation): a ZERO-LENGTH EDGE is
   parity-neutral for the crossing-number point-in-ring test.

   Motivation.  The curve relate lane linearises a CurveRing by `flat_map`-ing
   `chord_approx_segment` over its segments (`CurveGeometry.chord_approx_ring`).
   Each chord contributes `[p; q]`, so adjacent segments share a vertex and the
   resulting ring carries DEGENERATE edges `(v, v)` at every join.  To transport
   a Phase-3 `point_in_ring` fact (e.g. the S4 rectangle Contains/Touches
   witnesses) to the linearised curve ring, we must know those `(v, v)` edges do
   not change the ray-crossing parity.

   They cannot: `Overlay.edge_crosses_ray` demands a STRICT y-straddle
   (`py a < py p < py b` or the reverse), which `(v, v)` never satisfies.  Hence
   a zero-length edge always takes the `_skip` branch of `ray_parity_odd` /
   `ray_parity_even`, leaving the parity unchanged — anywhere in the edge list.

   Delivers (pure inductive + `lra`, zero axioms):
     - `edge_crosses_ray_degenerate` : a zero-length edge never crosses.
     - `rpo_cons_iff` / `rpe_cons_iff` : the head-edge parity recurrences.
     - `ray_parity_zero_edge_irrelevant` : inserting/removing a `(v, v)` edge
       anywhere preserves both parities.
     - `point_in_ring_dup_head` : a leading duplicate vertex is irrelevant.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Setoid.
From NTS.Proofs Require Import Distance Overlay.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  A zero-length edge never crosses the ray (strict y-straddle fails).     *)
(* -------------------------------------------------------------------------- *)

Lemma edge_crosses_ray_degenerate :
  forall (p v : Point), ~ edge_crosses_ray p (v, v).
Proof.
  intros p v H. unfold edge_crosses_ray in H. cbn in H.
  destruct H as [ [[H1 H2] _] | [[H1 H2] _] ]; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Head-edge parity recurrences (inversion ↔ constructors).               *)
(* -------------------------------------------------------------------------- *)

Lemma rpo_cons_iff :
  forall p e es,
    ray_parity_odd p (e :: es) <->
      (edge_crosses_ray p e /\ ray_parity_even p es)
      \/ (~ edge_crosses_ray p e /\ ray_parity_odd p es).
Proof.
  intros p e es. split.
  - intro H. inversion H; subst; [ left | right ]; split; assumption.
  - intros [[Hc He] | [Hn Ho]]; [ apply rpo_cross | apply rpo_skip ]; assumption.
Qed.

Lemma rpe_cons_iff :
  forall p e es,
    ray_parity_even p (e :: es) <->
      (edge_crosses_ray p e /\ ray_parity_odd p es)
      \/ (~ edge_crosses_ray p e /\ ray_parity_even p es).
Proof.
  intros p e es. split.
  - intro H. inversion H; subst; [ left | right ]; split; assumption.
  - intros [[Hc Ho] | [Hn He]]; [ apply rpe_cross | apply rpe_skip ]; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  A zero-length edge anywhere is parity-neutral (both parities).          *)
(* -------------------------------------------------------------------------- *)

Lemma ray_parity_zero_edge_irrelevant :
  forall p v es es',
    (ray_parity_odd  p (es ++ (v, v) :: es') <-> ray_parity_odd  p (es ++ es'))
    /\ (ray_parity_even p (es ++ (v, v) :: es') <-> ray_parity_even p (es ++ es')).
Proof.
  intros p v es es'.
  pose proof (edge_crosses_ray_degenerate p v) as Hnc.
  induction es as [| e0 es0 [IHo IHe]]; simpl.
  - split.
    + rewrite rpo_cons_iff. split.
      * intros [[Hc _] | [_ Ho]]; [ contradiction | exact Ho ].
      * intro Ho. right. split; assumption.
    + rewrite rpe_cons_iff. split.
      * intros [[Hc _] | [_ He]]; [ contradiction | exact He ].
      * intro He. right. split; assumption.
  - split.
    + rewrite (rpo_cons_iff p e0 (es0 ++ (v, v) :: es')),
              (rpo_cons_iff p e0 (es0 ++ es')), IHo, IHe. reflexivity.
    + rewrite (rpe_cons_iff p e0 (es0 ++ (v, v) :: es')),
              (rpe_cons_iff p e0 (es0 ++ es')), IHo, IHe. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Ring-level corollary: a leading duplicate vertex is irrelevant.         *)
(*                                                                            *)
(* `ring_edges (a :: a :: r') = (a, a) :: ring_edges (a :: r')`, so a leading  *)
(* duplicate prepends exactly one zero-length edge.                            *)
(* -------------------------------------------------------------------------- *)

Lemma point_in_ring_dup_head :
  forall p a r',
    point_in_ring p (a :: a :: r') <-> point_in_ring p (a :: r').
Proof.
  intros p a r'. unfold point_in_ring. cbn [ring_edges].
  exact (proj1 (ray_parity_zero_edge_irrelevant p a [] (ring_edges (a :: r')))).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4b  An adjacent duplicate vertex ANYWHERE is irrelevant.                   *)
(*                                                                            *)
(* The join structure of every linearised curve ring: `chord_approx_ring`     *)
(* concatenates each segment's `start :: … :: end`, and adjacency makes the    *)
(* end of one segment equal the start of the next, so the flattened vertex     *)
(* list carries an adjacent duplicate `… ; v ; v ; …` at every join.  Removing *)
(* one copy turns the two ring edges `(z, v); (v, w)` into the single `(z, w)` *)
(* with the degenerate `(v, v)` excised.  `ring_edges_dup` exhibits exactly    *)
(* that excision; `point_in_ring_dup_at` is the parity corollary (generalising *)
(* `point_in_ring_dup_head` from the leading position to any position).        *)
(* -------------------------------------------------------------------------- *)

(* Inserting a second copy of `a` after the first inserts exactly one `(a, a)`
   edge into `ring_edges`, at the position the shared prefix `l ++ [a]` ends. *)
Lemma ring_edges_dup :
  forall (l : Ring) (a : Point) (r' : Ring),
    exists es es',
      ring_edges (l ++ a :: a :: r') = es ++ (a, a) :: es'
      /\ ring_edges (l ++ a :: r')    = es ++ es'.
Proof.
  induction l as [| x l0 IH]; intros a r'.
  - (* leading position *)
    exists [], (ring_edges (a :: r')). split; reflexivity.
  - (* l = x :: l0 *)
    destruct l0 as [| y l0'].
    + (* l = [x] : the shared prefix ends right at x *)
      exists [ (x, a) ], (ring_edges (a :: r')). split; reflexivity.
    + (* l = x :: y :: l0' : peel the shared head edge (x, y), recurse on y::l0' *)
      destruct (IH a r') as [es0 [es0' [H1 H2]]].
      exists ((x, y) :: es0), es0'.
      assert (E1 : ring_edges ((x :: y :: l0') ++ a :: a :: r')
                   = (x, y) :: ring_edges ((y :: l0') ++ a :: a :: r'))
        by reflexivity.
      assert (E2 : ring_edges ((x :: y :: l0') ++ a :: r')
                   = (x, y) :: ring_edges ((y :: l0') ++ a :: r'))
        by reflexivity.
      rewrite E1, E2, H1, H2. split; reflexivity.
Qed.

Lemma point_in_ring_dup_at :
  forall p (l : Ring) (a : Point) (r' : Ring),
    point_in_ring p (l ++ a :: a :: r') <-> point_in_ring p (l ++ a :: r').
Proof.
  intros p l a r'. unfold point_in_ring.
  destruct (ring_edges_dup l a r') as [es [es' [H1 H2]]].
  rewrite H1, H2.
  exact (proj1 (ray_parity_zero_edge_irrelevant p a es es')).
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions edge_crosses_ray_degenerate.
Print Assumptions ray_parity_zero_edge_irrelevant.
Print Assumptions point_in_ring_dup_head.
Print Assumptions ring_edges_dup.
Print Assumptions point_in_ring_dup_at.
