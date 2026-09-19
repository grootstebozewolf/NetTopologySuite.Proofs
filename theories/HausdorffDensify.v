(* ============================================================================
   NetTopologySuite.Proofs.HausdorffDensify
   ----------------------------------------------------------------------------
   #423 ticket-10 line 1: the DISCRETE-vs-LOCUS densification bound for the
   directed Hausdorff distance on polylines (claimId 423-t10-densify).

   Two values on point lists A, B read as polylines (consecutive edges):

     directed_discrete_h A B  = max_{a vertex of A} d(a, locus B)
         -- JTS DiscreteHausdorffDistance's h: vertices of A against the
            WHOLE geometry B (point-to-segment, LECSegmentRow.seg_dist),
            not vertex-to-vertex.  It is therefore NOT the 423-a value
            HausdorffDiscrete.directed_hausdorff_sq (vertex-to-vertex,
            squared); 423-a is not restated here.

     directed_locus_h A B     = sup_{q on locus A} d(q, locus B)
         -- the JTS DirectedHausdorffDistance locus value, built as a term
            with Stdlib's completeness (least upper bound of a bounded,
            nonempty set of reals).  The set is bounded by
            discrete + max edge length (Lipschitz) and nonempty (a vertex).

   Proved (unsquared dist = sqrt dist_sq; the triangle inequality lives there):
     discrete_le_locus     : edges A <> [] -> discrete A B <= locus A B
     densify_step_bound    : for any A' with the same locus as A and every
                             edge of length <= delta,
                             0 <= locus A B - discrete A' B <= delta.
   f(delta) = delta: distance-to-a-set is 1-Lipschitz, so refining A to
   edge length delta closes the gap linearly.  This is the polyline twin of
   ArcChordDensity.n_chords_achieve_eps (the arc side: sagitta <= L^2/(n^2 r),
   quadratic in the refinement) -- quoted, not remade; no arc appears here.

   Locked pair (the JTS DiscreteHausdorffDistance javadoc example):
     A = LINESTRING (0 0, 100 0, 10 100)      B = LINESTRING (0 100, 0 10, 80 10)
     discrete h(A,B) = sqrt 500 (~22.36)      locus h(A,B) >= 910/19 (~47.89)
   and sqrt 500 < 910/19: the vertex value is a strict under-estimate on this
   pair (JTS: "22.36 ... 47.8").  The locus value is pinned from below by the
   on-edge witness q0 = (910/19, 1100/19); its equality with 910/19 is not
   claimed here.

   Not: 423-a / 423-b / FrechetMaxmin remint; no HAUSDORFF_* keyword; no
   NTS/GEOS port; no CurveSegment growth; no first_cook_scope;
   Linearise.hausdorff_le is not used.

   WITNESS topic: metric · claimId: 423-t10-densify · witness: 423-t10-densify
   3-axiom (Stdlib Reals). No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay LECSegmentRow.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Polyline locus, distance to a polyline, and the two h values.           *)
(* -------------------------------------------------------------------------- *)

(* The point set of a polyline: the union of its consecutive edges. *)
Definition polyline_locus (A : list Point) (q : Point) : Prop :=
  exists e, In e (ring_edges A) /\ on_seg (fst e) (snd e) q.

Fixpoint dist_to_edges (p : Point) (es : list Edge) : R :=
  match es with
  | [] => 0
  | [e] => seg_dist (fst e) (snd e) p
  | e :: es' => Rmin (seg_dist (fst e) (snd e) p) (dist_to_edges p es')
  end.

Definition dist_to_polyline (p : Point) (B : list Point) : R :=
  dist_to_edges p (ring_edges B).

Fixpoint list_max {X : Type} (f : X -> R) (l : list X) : R :=
  match l with
  | [] => 0
  | [x] => f x
  | x :: l' => Rmax (f x) (list_max f l')
  end.

(* JTS DiscreteHausdorffDistance: vertices of A against the locus of B. *)
Definition directed_discrete_h (A B : list Point) : R :=
  list_max (fun a => dist_to_polyline a B) A.

Definition max_edge_len (A : list Point) : R :=
  list_max (fun e : Edge => dist (fst e) (snd e)) (ring_edges A).

(* -------------------------------------------------------------------------- *)
(* §2  Fold facts.                                                            *)
(* -------------------------------------------------------------------------- *)

Lemma list_max_ge : forall {X : Type} (f : X -> R) (l : list X) (x : X),
  In x l -> f x <= list_max f l.
Proof.
  intros X f l. induction l as [| y l' IH]; intros x Hin; [ contradiction | ].
  destruct l' as [| z l''].
  - destruct Hin as [-> | []]. cbn. lra.
  - change (list_max f (y :: z :: l'')) with (Rmax (f y) (list_max f (z :: l''))).
    destruct Hin as [-> | Hin].
    + apply Rmax_l.
    + eapply Rle_trans; [ apply (IH x Hin) | apply Rmax_r ].
Qed.

Lemma list_max_le : forall {X : Type} (f : X -> R) (l : list X) (M : R),
  l <> [] -> (forall x, In x l -> f x <= M) -> list_max f l <= M.
Proof.
  intros X f l. induction l as [| y l' IH]; intros M Hne Hall; [ contradiction | ].
  destruct l' as [| z l''].
  - cbn. apply Hall. left. reflexivity.
  - change (list_max f (y :: z :: l'')) with (Rmax (f y) (list_max f (z :: l''))).
    apply Rmax_lub.
    + apply Hall. left. reflexivity.
    + apply IH; [ discriminate | ]. intros x Hx. apply Hall. right. exact Hx.
Qed.

Lemma dist_to_edges_le : forall (p : Point) (es : list Edge) (e : Edge),
  In e es -> dist_to_edges p es <= seg_dist (fst e) (snd e) p.
Proof.
  intros p es. induction es as [| e0 es' IH]; intros e Hin; [ contradiction | ].
  destruct es' as [| e1 es''].
  - destruct Hin as [-> | []]. cbn. lra.
  - change (dist_to_edges p (e0 :: e1 :: es''))
      with (Rmin (seg_dist (fst e0) (snd e0) p) (dist_to_edges p (e1 :: es''))).
    destruct Hin as [-> | Hin].
    + apply Rmin_l.
    + eapply Rle_trans; [ apply Rmin_r | apply (IH e Hin) ].
Qed.

Lemma dist_to_edges_attained : forall (p : Point) (es : list Edge),
  es <> [] -> exists e, In e es /\ dist_to_edges p es = seg_dist (fst e) (snd e) p.
Proof.
  intros p es. induction es as [| e0 es' IH]; intros Hne; [ contradiction | ].
  destruct es' as [| e1 es''].
  - exists e0. split; [ left; reflexivity | reflexivity ].
  - change (dist_to_edges p (e0 :: e1 :: es''))
      with (Rmin (seg_dist (fst e0) (snd e0) p) (dist_to_edges p (e1 :: es''))).
    destruct (IH ltac:(discriminate)) as [e [Hin Heq]].
    destruct (Rle_dec (seg_dist (fst e0) (snd e0) p) (dist_to_edges p (e1 :: es''))) as [Hle | Hgt].
    + exists e0. split; [ left; reflexivity | ]. rewrite Rmin_left; [ reflexivity | exact Hle ].
    + exists e. split; [ right; exact Hin | ]. rewrite Rmin_right; [ exact Heq | lra ].
Qed.

Lemma dist_to_edges_nonneg : forall (p : Point) (es : list Edge),
  0 <= dist_to_edges p es.
Proof.
  intros p es. induction es as [| e0 es' IH].
  - cbn. lra.
  - destruct es' as [| e1 es''].
    + cbn. apply dist_nonneg.
    + change (dist_to_edges p (e0 :: e1 :: es''))
        with (Rmin (seg_dist (fst e0) (snd e0) p) (dist_to_edges p (e1 :: es''))).
      apply Rmin_glb; [ apply dist_nonneg | exact IH ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Polyline geometry: edge endpoints are vertices, vertices are on the     *)
(*     locus, a segment point is within the edge length of its start.         *)
(* -------------------------------------------------------------------------- *)

Lemma edge_ends_in : forall (l : list Point) (e : Edge),
  In e (ring_edges l) -> In (fst e) l /\ In (snd e) l.
Proof.
  intros l. induction l as [| a l' IH]; intros e Hin; [ contradiction | ].
  destruct l' as [| b l''].
  - contradiction.
  - change (ring_edges (a :: b :: l'')) with ((a, b) :: ring_edges (b :: l'')) in Hin.
    destruct Hin as [<- | Hin].
    + cbn [fst snd]. split; [ left; reflexivity | right; left; reflexivity ].
    + destruct (IH e Hin) as [H1 H2]. split; right; assumption.
Qed.

Lemma seg_point_0 : forall a b : Point, seg_point a b 0 = a.
Proof. intros [x y] b. unfold seg_point. cbn. f_equal; ring. Qed.

Lemma seg_point_1 : forall a b : Point, seg_point a b 1 = b.
Proof. intros a [x y]. unfold seg_point. cbn. f_equal; ring. Qed.

Lemma vertex_in_locus : forall (A : list Point) (a : Point),
  ring_edges A <> [] -> In a A -> polyline_locus A a.
Proof.
  intros A. induction A as [| a0 A' IH]; intros a Hne Hin; [ contradiction | ].
  destruct A' as [| a1 A''].
  - cbn in Hne. contradiction.
  - change (ring_edges (a0 :: a1 :: A'')) with ((a0, a1) :: ring_edges (a1 :: A'')) in *.
    destruct Hin as [<- | Hin].
    + exists (a0, a1). split; [ left; reflexivity | ].
      exists 0. split; [ lra | ]. cbn [fst snd]. rewrite seg_point_0. reflexivity.
    + destruct A'' as [| a2 A'''].
      * destruct Hin as [<- | []].
        exists (a0, a1). split; [ left; reflexivity | ].
        exists 1. split; [ lra | ]. cbn [fst snd]. rewrite seg_point_1. reflexivity.
      * destruct (IH a ltac:(discriminate) Hin) as [e [He Hon]].
        exists e. split; [ right; exact He | exact Hon ].
Qed.

Lemma on_seg_dist_start : forall (a b q : Point),
  on_seg a b q -> dist q a <= dist a b.
Proof.
  intros a b q [t [[Ht0 Ht1] ->]].
  unfold dist. apply sqrt_le_1_alt.
  unfold dist_sq, seg_point. cbn [px py].
  assert (Ht2 : t * t <= 1) by nra.
  pose proof (dist_sq_nonneg a b) as Hd. unfold dist_sq in Hd.
  nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Distance to a polyline: lower bound, attained, 1-Lipschitz.             *)
(* -------------------------------------------------------------------------- *)

Lemma dist_to_polyline_le : forall (p Q : Point) (B : list Point),
  polyline_locus B Q -> dist_to_polyline p B <= dist p Q.
Proof.
  intros p Q B [e [He Hon]].
  eapply Rle_trans; [ apply (dist_to_edges_le p _ e He) | ].
  apply seg_dist_lower. exact Hon.
Qed.

Lemma dist_to_polyline_attained : forall (p : Point) (B : list Point),
  ring_edges B <> [] ->
  exists Q, polyline_locus B Q /\ dist p Q = dist_to_polyline p B.
Proof.
  intros p B Hne.
  destruct (dist_to_edges_attained p (ring_edges B) Hne) as [e [He Heq]].
  destruct (seg_dist_attained (fst e) (snd e) p) as [Q [HQ HdQ]].
  exists Q. split; [ exists e; split; assumption | ].
  unfold dist_to_polyline. rewrite Heq. exact HdQ.
Qed.

Lemma dist_to_polyline_lipschitz : forall (q a : Point) (B : list Point),
  dist_to_polyline q B <= dist_to_polyline a B + dist q a.
Proof.
  intros q a B.
  destruct (ring_edges B) as [| e es] eqn:HB.
  - unfold dist_to_polyline. rewrite HB. cbn. pose proof (dist_nonneg q a). lra.
  - assert (Hne : ring_edges B <> []) by (rewrite HB; discriminate).
    destruct (dist_to_polyline_attained a B Hne) as [Q [HQ HdQ]].
    eapply Rle_trans; [ apply (dist_to_polyline_le q Q B HQ) | ].
    rewrite <- HdQ. rewrite Rplus_comm. apply dist_triangle.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  The locus value as a least upper bound.                                 *)
(* -------------------------------------------------------------------------- *)

(* The set of distances realised on the locus of A; the second disjunct only
   contributes when A has no edge, keeping the set nonempty (value 0). *)
Definition locus_values (A B : list Point) (x : R) : Prop :=
  (exists q, polyline_locus A q /\ x = dist_to_polyline q B)
  \/ (ring_edges A = [] /\ x = 0).

Lemma locus_values_bound : forall A B, bound (locus_values A B).
Proof.
  intros A B.
  exists (Rmax 0 (directed_discrete_h A B + max_edge_len A)).
  intros x [[q [[e [He Hon]] ->]] | [_ ->]].
  - apply Rle_trans with (directed_discrete_h A B + max_edge_len A); [ | apply Rmax_r ].
    destruct (edge_ends_in A e He) as [Hfst _].
    eapply Rle_trans; [ apply (dist_to_polyline_lipschitz q (fst e) B) | ].
    apply Rplus_le_compat.
    + unfold directed_discrete_h. apply (list_max_ge (fun a => dist_to_polyline a B) A (fst e) Hfst).
    + eapply Rle_trans; [ apply (on_seg_dist_start (fst e) (snd e) q Hon) | ].
      unfold max_edge_len. apply (list_max_ge (fun e' : Edge => dist (fst e') (snd e')) _ e He).
  - apply Rmax_l.
Qed.

Lemma locus_values_nonempty : forall A B, exists x, locus_values A B x.
Proof.
  intros A B.
  destruct (ring_edges A) as [| e es] eqn:HA.
  - exists 0. right. split; [ exact HA | reflexivity ].
  - exists (dist_to_polyline (fst e) B). left.
    exists (fst e). split; [ | reflexivity ].
    exists e. split; [ rewrite HA; left; reflexivity | ].
    exists 0. split; [ lra | ]. rewrite seg_point_0. reflexivity.
Qed.

(* THE LOCUS h(A,B): a real number, by completeness of R. *)
Definition directed_locus_h (A B : list Point) : R :=
  proj1_sig (completeness (locus_values A B) (locus_values_bound A B)
                          (locus_values_nonempty A B)).

Lemma directed_locus_h_lub : forall A B,
  is_lub (locus_values A B) (directed_locus_h A B).
Proof. intros A B. unfold directed_locus_h. apply proj2_sig. Qed.

Lemma locus_h_ge_point : forall (A B : list Point) (q : Point),
  polyline_locus A q -> dist_to_polyline q B <= directed_locus_h A B.
Proof.
  intros A B q Hq. destruct (directed_locus_h_lub A B) as [Hub _].
  apply Hub. left. exists q. split; [ exact Hq | reflexivity ].
Qed.

Lemma locus_h_le_bound : forall (A B : list Point) (M : R),
  (forall x, locus_values A B x -> x <= M) -> directed_locus_h A B <= M.
Proof.
  intros A B M HM. destruct (directed_locus_h_lub A B) as [_ Hleast].
  apply Hleast. exact HM.
Qed.

(* Same locus, same value. *)
Lemma locus_nonempty_edges : forall (A : list Point) (q : Point),
  polyline_locus A q -> ring_edges A <> [].
Proof.
  intros A q [e [He _]] HA. rewrite HA in He. contradiction.
Qed.

Lemma directed_locus_h_same_locus : forall (A A' B : list Point),
  ring_edges A <> [] -> ring_edges A' <> [] ->
  (forall q, polyline_locus A q <-> polyline_locus A' q) ->
  directed_locus_h A B = directed_locus_h A' B.
Proof.
  intros A A' B HA HA' Hiff.
  assert (Hset : forall x, locus_values A B x <-> locus_values A' B x).
  { intros x. split; intros [[q [Hq ->]] | [H _]].
    - left. exists q. split; [ apply Hiff; exact Hq | reflexivity ].
    - contradiction.
    - left. exists q. split; [ apply Hiff; exact Hq | reflexivity ].
    - contradiction. }
  destruct (directed_locus_h_lub A B) as [Hub Hleast].
  destruct (directed_locus_h_lub A' B) as [Hub' Hleast'].
  apply Rle_antisym.
  - apply Hleast. intros x Hx. apply Hub'. apply Hset. exact Hx.
  - apply Hleast'. intros x Hx. apply Hub. apply Hset. exact Hx.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Line 1: discrete <= locus, and the densify-step bound.                  *)
(* -------------------------------------------------------------------------- *)

Lemma edges_nonempty_list_nonempty : forall A : list Point,
  ring_edges A <> [] -> A <> [].
Proof. intros A H HA. apply H. rewrite HA. reflexivity. Qed.

(* WITNESS {"claimId":"423-t10-densify","topic":"metric","lemma":"discrete_le_locus","title":"directed discrete Hausdorff (vertices of A against the locus of B, JTS DiscreteHausdorffDistance) is at most the directed locus Hausdorff (sup over the locus of A) on any polyline A with an edge","file":"theories/HausdorffDensify.v","witness":"423-t10-densify"} *)
Theorem discrete_le_locus : forall A B : list Point,
  ring_edges A <> [] ->
  directed_discrete_h A B <= directed_locus_h A B.
Proof.
  intros A B Hne.
  unfold directed_discrete_h.
  apply list_max_le; [ exact (edges_nonempty_list_nonempty A Hne) | ].
  intros a Ha. apply locus_h_ge_point. apply vertex_in_locus; assumption.
Qed.

(* WITNESS {"claimId":"423-t10-densify","topic":"metric","lemma":"densify_step_bound","title":"densify-step bound: for any refinement A' of A (same locus) whose every edge has length at most delta, 0 <= locus h(A,B) - discrete h(A',B) <= delta; f(delta) = delta because distance-to-a-set is 1-Lipschitz (polyline twin of ArcChordDensity.n_chords_achieve_eps)","file":"theories/HausdorffDensify.v","witness":"423-t10-densify"} *)
Theorem densify_step_bound : forall (A A' B : list Point) (delta : R),
  ring_edges A' <> [] ->
  (forall q, polyline_locus A' q <-> polyline_locus A q) ->
  (forall e, In e (ring_edges A') -> dist (fst e) (snd e) <= delta) ->
  0 <= directed_locus_h A B - directed_discrete_h A' B <= delta.
Proof.
  intros A A' B delta Hne' Hiff Hdelta.
  assert (HneA : ring_edges A <> []).
  { destruct (ring_edges A') as [| e es] eqn:HA'; [ contradiction | ].
    apply (locus_nonempty_edges A (fst e)). apply Hiff.
    exists e. split; [ rewrite HA'; left; reflexivity | ].
    exists 0. split; [ lra | ]. rewrite seg_point_0. reflexivity. }
  rewrite (directed_locus_h_same_locus A A' B HneA Hne' (fun q => iff_sym (Hiff q))).
  split.
  - pose proof (discrete_le_locus A' B Hne'). lra.
  - assert (Hub : directed_locus_h A' B <= directed_discrete_h A' B + delta).
    { apply locus_h_le_bound.
      intros x [[q [[e [He Hon]] ->]] | [H _]]; [ | contradiction ].
      destruct (edge_ends_in A' e He) as [Hfst _].
      eapply Rle_trans; [ apply (dist_to_polyline_lipschitz q (fst e) B) | ].
      apply Rplus_le_compat.
      + unfold directed_discrete_h.
        apply (list_max_ge (fun a => dist_to_polyline a B) A' (fst e) Hfst).
      + eapply Rle_trans; [ apply (on_seg_dist_start (fst e) (snd e) q Hon) | ].
        apply Hdelta. exact He. }
    lra.
Qed.

(* The canonical delta: the refinement's own maximal edge length. *)
Corollary densify_step_bound_max_edge : forall (A A' B : list Point),
  ring_edges A' <> [] ->
  (forall q, polyline_locus A' q <-> polyline_locus A q) ->
  0 <= directed_locus_h A B - directed_discrete_h A' B <= max_edge_len A'.
Proof.
  intros A A' B Hne' Hiff.
  apply densify_step_bound; [ exact Hne' | exact Hiff | ].
  intros e He. unfold max_edge_len.
  apply (list_max_ge (fun e' : Edge => dist (fst e') (snd e')) _ e He).
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  The locked JTS pair: discrete = sqrt 500, locus >= 910/19, strict gap.  *)
(* -------------------------------------------------------------------------- *)

Definition mp (x y : R) : Point := mkPoint x y.
Definition jts_A : list Point := [mp 0 0; mp 100 0; mp 10 100].
Definition jts_B : list Point := [mp 0 100; mp 0 10; mp 80 10].

(* seg_dist with the clamp resolved to a known parameter. *)
Lemma seg_dist_at : forall (a b p : Point) (t : R),
  dist_sq a b <> 0 ->
  Rmax 0 (Rmin 1 (seg_dot a b p / dist_sq a b)) = t ->
  seg_dist a b p = dist p (seg_point a b t).
Proof.
  intros a b p t Hne Ht. unfold seg_dist, seg_t.
  destruct (Req_EM_T (dist_sq a b) 0) as [H | _]; [ contradiction | ].
  rewrite Ht. reflexivity.
Qed.

Ltac jts_dist_sq_ne :=
  let H := fresh in intro H; unfold dist_sq, mp in H; cbn in H; lra.

(* B's two edges. *)
Definition jB1 : Edge := (mp 0 100, mp 0 10).
Definition jB2 : Edge := (mp 0 10, mp 80 10).

Lemma jts_B_edges : ring_edges jts_B = [jB1; jB2].
Proof. reflexivity. Qed.

Lemma sd_B1_00 : seg_dist (mp 0 100) (mp 0 10) (mp 0 0) = 10.
Proof.
  rewrite (seg_dist_at _ _ _ 1); [ | jts_dist_sq_ne | ].
  - unfold dist. replace (dist_sq (mp 0 0) (seg_point (mp 0 100) (mp 0 10) 1)) with (10 * 10)
      by (unfold dist_sq, seg_point, mp; cbn; ring).
    rewrite sqrt_square; lra.
  - replace (seg_dot (mp 0 100) (mp 0 10) (mp 0 0) / dist_sq (mp 0 100) (mp 0 10)) with (10 / 9)
      by (unfold seg_dot, dist_sq, mp; cbn; field).
    rewrite Rmin_left by lra. rewrite Rmax_right by lra. reflexivity.
Qed.

Lemma sd_B2_00 : seg_dist (mp 0 10) (mp 80 10) (mp 0 0) = 10.
Proof.
  rewrite (seg_dist_at _ _ _ 0); [ | jts_dist_sq_ne | ].
  - unfold dist. replace (dist_sq (mp 0 0) (seg_point (mp 0 10) (mp 80 10) 0)) with (10 * 10)
      by (unfold dist_sq, seg_point, mp; cbn; ring).
    rewrite sqrt_square; lra.
  - replace (seg_dot (mp 0 10) (mp 80 10) (mp 0 0) / dist_sq (mp 0 10) (mp 80 10)) with 0
      by (unfold seg_dot, dist_sq, mp; cbn; field).
    rewrite Rmin_right by lra. rewrite Rmax_left by lra. reflexivity.
Qed.

Lemma sd_B1_1000 : seg_dist (mp 0 100) (mp 0 10) (mp 100 0) = sqrt 10100.
Proof.
  rewrite (seg_dist_at _ _ _ 1); [ | jts_dist_sq_ne | ].
  - unfold dist. f_equal. unfold dist_sq, seg_point, mp; cbn; ring.
  - replace (seg_dot (mp 0 100) (mp 0 10) (mp 100 0) / dist_sq (mp 0 100) (mp 0 10)) with (10 / 9)
      by (unfold seg_dot, dist_sq, mp; cbn; field).
    rewrite Rmin_left by lra. rewrite Rmax_right by lra. reflexivity.
Qed.

Lemma sd_B2_1000 : seg_dist (mp 0 10) (mp 80 10) (mp 100 0) = sqrt 500.
Proof.
  rewrite (seg_dist_at _ _ _ 1); [ | jts_dist_sq_ne | ].
  - unfold dist. f_equal. unfold dist_sq, seg_point, mp; cbn; ring.
  - replace (seg_dot (mp 0 10) (mp 80 10) (mp 100 0) / dist_sq (mp 0 10) (mp 80 10)) with (5 / 4)
      by (unfold seg_dot, dist_sq, mp; cbn; field).
    rewrite Rmin_left by lra. rewrite Rmax_right by lra. reflexivity.
Qed.

Lemma sd_B1_10100 : seg_dist (mp 0 100) (mp 0 10) (mp 10 100) = 10.
Proof.
  rewrite (seg_dist_at _ _ _ 0); [ | jts_dist_sq_ne | ].
  - unfold dist. replace (dist_sq (mp 10 100) (seg_point (mp 0 100) (mp 0 10) 0)) with (10 * 10)
      by (unfold dist_sq, seg_point, mp; cbn; ring).
    rewrite sqrt_square; lra.
  - replace (seg_dot (mp 0 100) (mp 0 10) (mp 10 100) / dist_sq (mp 0 100) (mp 0 10)) with 0
      by (unfold seg_dot, dist_sq, mp; cbn; field).
    rewrite Rmin_right by lra. rewrite Rmax_left by lra. reflexivity.
Qed.

Lemma sd_B2_10100 : seg_dist (mp 0 10) (mp 80 10) (mp 10 100) = 90.
Proof.
  rewrite (seg_dist_at _ _ _ (1 / 8)); [ | jts_dist_sq_ne | ].
  - unfold dist. replace (dist_sq (mp 10 100) (seg_point (mp 0 10) (mp 80 10) (1 / 8))) with (90 * 90)
      by (unfold dist_sq, seg_point, mp; cbn; field).
    rewrite sqrt_square; lra.
  - replace (seg_dot (mp 0 10) (mp 80 10) (mp 10 100) / dist_sq (mp 0 10) (mp 80 10)) with (1 / 8)
      by (unfold seg_dot, dist_sq, mp; cbn; field).
    rewrite Rmin_right by lra. rewrite Rmax_right by lra. reflexivity.
Qed.

Lemma sqrt_10_le_500 : 10 <= sqrt 500.
Proof.
  replace 10 with (sqrt (10 * 10)) at 1 by (rewrite sqrt_square; lra).
  apply sqrt_le_1_alt. lra.
Qed.

Lemma sqrt_500_le_10100 : sqrt 500 <= sqrt 10100.
Proof. apply sqrt_le_1_alt. lra. Qed.

(* WITNESS {"claimId":"423-t10-densify","topic":"metric","lemma":"jts_discrete_value","title":"locked JTS pair A = (0 0, 100 0, 10 100), B = (0 100, 0 10, 80 10): the vertex-against-locus discrete h(A,B) is sqrt 500 (~22.36)","file":"theories/HausdorffDensify.v","witness":"423-t10-densify"} *)
Lemma jts_discrete_value : directed_discrete_h jts_A jts_B = sqrt 500.
Proof.
  unfold directed_discrete_h, jts_A, dist_to_polyline. rewrite jts_B_edges.
  cbn [list_max dist_to_edges jB1 jB2 fst snd].
  rewrite sd_B1_00, sd_B2_00, sd_B1_1000, sd_B2_1000, sd_B1_10100, sd_B2_10100.
  rewrite (Rmin_left 10 10) by lra.
  rewrite (Rmin_right (sqrt 10100) (sqrt 500)) by exact sqrt_500_le_10100.
  rewrite (Rmin_left 10 90) by lra.
  rewrite (Rmax_left (sqrt 500) 10) by exact sqrt_10_le_500.
  rewrite (Rmax_right 10 (sqrt 500)) by exact sqrt_10_le_500.
  reflexivity.
Qed.

(* The on-edge witness on A's diagonal edge (100,0)-(10,100) at t = 11/19. *)
Definition q0 : Point := mp (910 / 19) (1100 / 19).

Lemma q0_on_A : polyline_locus jts_A q0.
Proof.
  exists (mp 100 0, mp 10 100). split.
  - right. left. reflexivity.
  - exists (11 / 19). split; [ lra | ].
    unfold q0, seg_point, mp. cbn. f_equal; field.
Qed.

Lemma sd_B1_q0 : seg_dist (mp 0 100) (mp 0 10) q0 = 910 / 19.
Proof.
  rewrite (seg_dist_at _ _ _ (80 / 171)); [ | jts_dist_sq_ne | ].
  - unfold dist.
    replace (dist_sq q0 (seg_point (mp 0 100) (mp 0 10) (80 / 171))) with ((910 / 19) * (910 / 19))
      by (unfold dist_sq, seg_point, q0, mp; cbn; field).
    rewrite sqrt_square; lra.
  - replace (seg_dot (mp 0 100) (mp 0 10) q0 / dist_sq (mp 0 100) (mp 0 10)) with (80 / 171)
      by (unfold seg_dot, dist_sq, q0, mp; cbn; field).
    rewrite Rmin_right by lra. rewrite Rmax_right by lra. reflexivity.
Qed.

Lemma sd_B2_q0 : seg_dist (mp 0 10) (mp 80 10) q0 = 910 / 19.
Proof.
  rewrite (seg_dist_at _ _ _ (91 / 152)); [ | jts_dist_sq_ne | ].
  - unfold dist.
    replace (dist_sq q0 (seg_point (mp 0 10) (mp 80 10) (91 / 152))) with ((910 / 19) * (910 / 19))
      by (unfold dist_sq, seg_point, q0, mp; cbn; field).
    rewrite sqrt_square; lra.
  - replace (seg_dot (mp 0 10) (mp 80 10) q0 / dist_sq (mp 0 10) (mp 80 10)) with (91 / 152)
      by (unfold seg_dot, dist_sq, q0, mp; cbn; field).
    rewrite Rmin_right by lra. rewrite Rmax_right by lra. reflexivity.
Qed.

Lemma q0_dist_to_B : dist_to_polyline q0 jts_B = 910 / 19.
Proof.
  unfold dist_to_polyline. rewrite jts_B_edges.
  cbn [dist_to_edges jB1 jB2 fst snd].
  rewrite sd_B1_q0, sd_B2_q0. apply Rmin_left. lra.
Qed.

(* WITNESS {"claimId":"423-t10-densify","topic":"metric","lemma":"jts_locus_lower","title":"locked JTS pair: the locus h(A,B) is at least 910/19 (~47.89), witnessed by the on-edge point (910/19, 1100/19)","file":"theories/HausdorffDensify.v","witness":"423-t10-densify"} *)
Lemma jts_locus_lower : 910 / 19 <= directed_locus_h jts_A jts_B.
Proof.
  rewrite <- q0_dist_to_B. apply locus_h_ge_point. exact q0_on_A.
Qed.

Lemma sqrt_500_lt_910_19 : sqrt 500 < 910 / 19.
Proof.
  apply Rsqr_incrst_0; [ | apply sqrt_pos | lra ].
  rewrite Rsqr_sqrt by lra. unfold Rsqr. lra.
Qed.

(* WITNESS {"claimId":"423-t10-densify","topic":"metric","lemma":"jts_discrete_strictly_below_locus","title":"locked JTS pair: discrete h(A,B) = sqrt 500 < 910/19 <= locus h(A,B); the vertex value is a strict under-estimate (JTS 22.36 vs 47.8), consistent with discrete_le_locus","file":"theories/HausdorffDensify.v","witness":"423-t10-densify"} *)
Theorem jts_discrete_strictly_below_locus :
  directed_discrete_h jts_A jts_B < directed_locus_h jts_A jts_B.
Proof.
  rewrite jts_discrete_value.
  eapply Rlt_le_trans; [ exact sqrt_500_lt_910_19 | exact jts_locus_lower ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §8  Ticket stop.                                                           *)
(* -------------------------------------------------------------------------- *)

Inductive HausdorffLocusPark : Type :=
| LocusHNotConstructible.

Definition hausdorff_locus_park_inhabits (_ : HausdorffLocusPark) : Prop := False.

(* WITNESS {"claimId":"423-t10-densify","topic":"metric","lemma":"ticket_423_t10_line1_qed_or_qex","title":"#423 ticket-10 line 1: locus h is a constructible term (completeness lub), discrete <= locus on every polyline with an edge, densify-step bound 0 <= locus - discrete(A') <= delta with f(delta) = delta, and on the locked JTS pair discrete = sqrt 500 < 910/19 <= locus (QED); or the locus value is a named missing constructor and only the discrete side is pinned (QEX); discharged QED","file":"theories/HausdorffDensify.v","witness":"423-t10-densify"} *)
Theorem ticket_423_t10_line1_qed_or_qex :
  ((forall A B : list Point, ring_edges A <> [] ->
      directed_discrete_h A B <= directed_locus_h A B)
   /\ (forall (A A' B : list Point) (delta : R),
         ring_edges A' <> [] ->
         (forall q, polyline_locus A' q <-> polyline_locus A q) ->
         (forall e, In e (ring_edges A') -> dist (fst e) (snd e) <= delta) ->
         0 <= directed_locus_h A B - directed_discrete_h A' B <= delta)
   /\ directed_discrete_h jts_A jts_B = sqrt 500
   /\ 910 / 19 <= directed_locus_h jts_A jts_B
   /\ directed_discrete_h jts_A jts_B < directed_locus_h jts_A jts_B)
  \/
  (hausdorff_locus_park_inhabits LocusHNotConstructible
   /\ directed_discrete_h jts_A jts_B = sqrt 500).
Proof.
  left.
  split; [ exact discrete_le_locus | ].
  split; [ exact densify_step_bound | ].
  split; [ exact jts_discrete_value | ].
  split; [ exact jts_locus_lower | ].
  exact jts_discrete_strictly_below_locus.
Qed.

Print Assumptions discrete_le_locus.
Print Assumptions densify_step_bound.
Print Assumptions jts_discrete_value.
Print Assumptions jts_locus_lower.
Print Assumptions ticket_423_t10_line1_qed_or_qex.
