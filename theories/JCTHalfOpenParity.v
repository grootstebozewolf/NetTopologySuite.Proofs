(* ============================================================================
   NetTopologySuite.Proofs.JCTHalfOpenParity
   ----------------------------------------------------------------------------
   H1 PROPER, part 2: the HALF-OPEN ray parity -- the invariant the transport
   engine was built for -- with its guard-agreement, decidability, and
   far-field evenness in all four directions.  The trapped half of H1 is now
   reduced to ONE concrete named kernel about ONE concrete invariant.

   `JCTParityTransport.v` showed the strict parity of `point_in_ring` cannot
   be the locally-constant invariant (a far-west point's strict count jumps
   at a pass-through-vertex height).  The classical invariant is the
   HALF-OPEN convention: edge (a,b) counts at level h when

     py a <= h < py b   (ascending; bottom endpoint INCLUDED)   or
     py b <= h < py a   (descending)

   and the ray condition is the same strict x-inequality.  This file:

     §1  `edge_crosses_ray_ho`, the parity pair `ho_parity_odd/_even`,
         `point_in_ring_ho`, plus decidability and exclusivity (mirroring
         the strict versions).
     §2  Guard agreement: under `ray_avoids_vertices p r` alone, the
         half-open and strict parities agree at p
         (`point_in_ring_ho_agrees`): the two conventions differ only when
         p's height equals an edge's bottom-endpoint height, and there the
         half-open crossing point IS that vertex -- excluded east of p by
         the guard, and irrelevant west of p.
     §3  Far-field evenness, all four directions (`ho_far_false`):
         right/up/down because no edge can cross at all; WEST by the cyclic
         walk argument -- far west of every vertex, an edge crosses iff its
         endpoints' below-flags differ (`ho_cross_far_west_iff`), and around
         a CLOSED walk the below-flag returns to its start, so the number of
         flips is even (`ho_walk_parity` / `ho_far_west_even`).  This is the
         place the ring's closedness genuinely enters.
     §4  THE CAPSTONE (`odd_parity_trapped_of_ho_kernel`): for any closed
         ring and guarded odd-parity point, `in_bounded_component_cont`
         follows from the single named kernel

           ho_parity_locally_constant r

         (local constancy of the half-open parity along complement paths).
         Everything else in H1's trapped half is now Qed.

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam.
From NTS.Proofs Require Import PointInRingCorrect JCT JCT_OnEdgeCounterexample.
From NTS.Proofs Require Import ConvexOffringSeam JCTParityTransport.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §1  The half-open crossing and its parity.
   --------------------------------------------------------------------------- *)

Definition edge_crosses_ray_ho (p : Point) (e : Edge) : Prop :=
  let (a, b) := e in
  (py a <= py p < py b /\
     px p < px a + (px b - px a) * (py p - py a) / (py b - py a))
  \/
  (py b <= py p < py a /\
     px p < px b + (px a - px b) * (py p - py b) / (py a - py b)).

Inductive ho_parity_odd (p : Point) : list Edge -> Prop :=
| hpo_cross : forall e es,
    edge_crosses_ray_ho p e -> ho_parity_even p es -> ho_parity_odd p (e :: es)
| hpo_skip : forall e es,
    ~ edge_crosses_ray_ho p e -> ho_parity_odd p es -> ho_parity_odd p (e :: es)
with ho_parity_even (p : Point) : list Edge -> Prop :=
| hpe_nil : ho_parity_even p []
| hpe_cross : forall e es,
    edge_crosses_ray_ho p e -> ho_parity_odd p es -> ho_parity_even p (e :: es)
| hpe_skip : forall e es,
    ~ edge_crosses_ray_ho p e -> ho_parity_even p es -> ho_parity_even p (e :: es).

Definition point_in_ring_ho (p : Point) (r : Ring) : Prop :=
  ho_parity_odd p (ring_edges r).

Lemma edge_crosses_ray_ho_dec : forall (p : Point) (e : Edge),
  {edge_crosses_ray_ho p e} + {~ edge_crosses_ray_ho p e}.
Proof.
  intros p [a b]. unfold edge_crosses_ray_ho.
  assert (D1 : {py a <= py p < py b /\
                px p < px a + (px b - px a) * (py p - py a) / (py b - py a)}
             + {~ (py a <= py p < py b /\
                px p < px a + (px b - px a) * (py p - py a) / (py b - py a))}).
  { destruct (Rle_dec (py a) (py p)) as [H1 | H1];
      [ destruct (Rlt_dec (py p) (py b)) as [H2 | H2];
        [ destruct (Rlt_dec (px p)
            (px a + (px b - px a) * (py p - py a) / (py b - py a))) as [H3 | H3];
          [ left; tauto | right; intros [_ Hc]; exact (H3 Hc) ]
        | right; intros [[_ Hc] _]; exact (H2 Hc) ]
      | right; intros [[Hc _] _]; exact (H1 Hc) ]. }
  assert (D2 : {py b <= py p < py a /\
                px p < px b + (px a - px b) * (py p - py b) / (py a - py b)}
             + {~ (py b <= py p < py a /\
                px p < px b + (px a - px b) * (py p - py b) / (py a - py b))}).
  { destruct (Rle_dec (py b) (py p)) as [H1 | H1];
      [ destruct (Rlt_dec (py p) (py a)) as [H2 | H2];
        [ destruct (Rlt_dec (px p)
            (px b + (px a - px b) * (py p - py b) / (py a - py b))) as [H3 | H3];
          [ left; tauto | right; intros [_ Hc]; exact (H3 Hc) ]
        | right; intros [[_ Hc] _]; exact (H2 Hc) ]
      | right; intros [[Hc _] _]; exact (H1 Hc) ]. }
  destruct D1 as [Hy | Hn1]; [ left; left; exact Hy | ].
  destruct D2 as [Hy | Hn2]; [ left; right; exact Hy | ].
  right; intros [Hc | Hc]; [ exact (Hn1 Hc) | exact (Hn2 Hc) ].
Qed.

Lemma ho_parity_dec : forall (p : Point) (es : list Edge),
  {ho_parity_odd p es} + {ho_parity_even p es}.
Proof.
  intros p; induction es as [| e es' IH].
  - right; constructor.
  - destruct (edge_crosses_ray_ho_dec p e) as [Hc | Hn]; destruct IH as [Ho | He].
    + right; apply hpe_cross; assumption.
    + left; apply hpo_cross; assumption.
    + left; apply hpo_skip; assumption.
    + right; apply hpe_skip; assumption.
Qed.

Lemma ho_parity_excl : forall (p : Point) (es : list Edge),
  ho_parity_odd p es -> ho_parity_even p es -> False.
Proof.
  intros p; induction es as [| e es' IH]; intros Ho He.
  - inversion Ho.
  - inversion Ho as [? ? Hc1 Ht1 | ? ? Hn1 Ht1]; subst;
    inversion He as [| ? ? Hc2 Ht2 | ? ? Hn2 Ht2]; subst.
    + exact (IH Ht2 Ht1).
    + exact (Hn2 Hc1).
    + exact (Hn1 Hc2).
    + exact (IH Ht1 Ht2).
Qed.

Theorem point_in_ring_ho_dec : forall (p : Point) (r : Ring),
  {point_in_ring_ho p r} + {~ point_in_ring_ho p r}.
Proof.
  intros p r. unfold point_in_ring_ho.
  destruct (ho_parity_dec p (ring_edges r)) as [Ho | He].
  - left; exact Ho.
  - right; intro Ho; exact (ho_parity_excl p _ Ho He).
Qed.

(* Cons-step iff helpers (used by the walk induction). *)
Lemma ho_odd_cons_cross : forall p e es,
  edge_crosses_ray_ho p e ->
  (ho_parity_odd p (e :: es) <-> ho_parity_even p es).
Proof.
  intros p e es Hc. split.
  - intro H; inversion H as [? ? ? Ht | ? ? Hn Ht]; subst;
      [ exact Ht | exact (False_ind _ (Hn Hc)) ].
  - intro He; apply hpo_cross; assumption.
Qed.

Lemma ho_odd_cons_skip : forall p e es,
  ~ edge_crosses_ray_ho p e ->
  (ho_parity_odd p (e :: es) <-> ho_parity_odd p es).
Proof.
  intros p e es Hn. split.
  - intro H; inversion H as [? ? Hc Ht | ? ? ? Ht]; subst;
      [ exact (False_ind _ (Hn Hc)) | exact Ht ].
  - intro Ho; apply hpo_skip; assumption.
Qed.

Lemma ho_even_cons_cross : forall p e es,
  edge_crosses_ray_ho p e ->
  (ho_parity_even p (e :: es) <-> ho_parity_odd p es).
Proof.
  intros p e es Hc. split.
  - intro H; inversion H as [| ? ? ? Ht | ? ? Hn Ht]; subst;
      [ exact Ht | exact (False_ind _ (Hn Hc)) ].
  - intro Ho; apply hpe_cross; assumption.
Qed.

Lemma ho_even_cons_skip : forall p e es,
  ~ edge_crosses_ray_ho p e ->
  (ho_parity_even p (e :: es) <-> ho_parity_even p es).
Proof.
  intros p e es Hn. split.
  - intro H; inversion H as [| ? ? Hc Ht | ? ? ? Ht]; subst;
      [ exact (False_ind _ (Hn Hc)) | exact Ht ].
  - intro He; apply hpe_skip; assumption.
Qed.

(* ---------------------------------------------------------------------------
   §2  Guard agreement: under `ray_avoids_vertices` the two parities agree.
   --------------------------------------------------------------------------- *)

Lemma ho_edge_agree : forall (p : Point) (r : Ring) (e : Edge),
  ray_avoids_vertices p r ->
  In e (ring_edges r) ->
  (edge_crosses_ray_ho p e <-> edge_crosses_ray p e).
Proof.
  intros p r [a b] Hrav Hin.
  destruct (ring_edges_endpoints_in r _ Hin) as [Ha Hb].
  cbn [fst snd] in Ha, Hb.
  assert (GA : py a = py p -> px a < px p).
  { intro Hy. destruct (Rle_or_lt (px p) (px a)) as [Hle | Hlt]; [ | exact Hlt ].
    exfalso. exact (Hrav a Ha (conj Hy Hle)). }
  assert (GB : py b = py p -> px b < px p).
  { intro Hy. destruct (Rle_or_lt (px p) (px b)) as [Hle | Hlt]; [ | exact Hlt ].
    exfalso. exact (Hrav b Hb (conj Hy Hle)). }
  unfold edge_crosses_ray_ho, edge_crosses_ray. split.
  - intros [[Hy Hx] | [Hy Hx]].
    + destruct (Req_dec (py a) (py p)) as [He | Hne].
      * exfalso. specialize (GA He).
        replace (px a + (px b - px a) * (py p - py a) / (py b - py a))
          with (px a) in Hx by (rewrite <- He; field; lra).
        lra.
      * left. split; [ lra | exact Hx ].
    + destruct (Req_dec (py b) (py p)) as [He | Hne].
      * exfalso. specialize (GB He).
        replace (px b + (px a - px b) * (py p - py b) / (py a - py b))
          with (px b) in Hx by (rewrite <- He; field; lra).
        lra.
      * right. split; [ lra | exact Hx ].
  - intros [[Hy Hx] | [Hy Hx]]; [ left | right ]; (split; [ lra | exact Hx ]).
Qed.

(* Lift the edge-wise agreement to the parity pair. *)
Lemma ho_strict_parity_agree : forall (p : Point) (es : list Edge),
  (forall e, In e es -> (edge_crosses_ray_ho p e <-> edge_crosses_ray p e)) ->
  (ho_parity_odd p es <-> ray_parity_odd p es)
  /\ (ho_parity_even p es <-> ray_parity_even p es).
Proof.
  intros p; induction es as [| e es' IH]; intros Hag.
  - split; split; intro H; try (inversion H; fail); constructor.
  - assert (Hag' : forall e', In e' es' ->
        (edge_crosses_ray_ho p e' <-> edge_crosses_ray p e'))
      by (intros e' He'; apply Hag; right; exact He').
    destruct (IH Hag') as [IHodd IHeven].
    assert (Hhd : edge_crosses_ray_ho p e <-> edge_crosses_ray p e)
      by (apply Hag; left; reflexivity).
    split; split; intro H.
    + inversion H as [? ? Hc Ht | ? ? Hn Ht]; subst.
      * apply rpo_cross; [ tauto | tauto ].
      * apply rpo_skip; [ tauto | tauto ].
    + inversion H as [? ? Hc Ht | ? ? Hn Ht]; subst.
      * apply hpo_cross; [ tauto | tauto ].
      * apply hpo_skip; [ tauto | tauto ].
    + inversion H as [| ? ? Hc Ht | ? ? Hn Ht]; subst.
      * apply rpe_cross; [ tauto | tauto ].
      * apply rpe_skip; [ tauto | tauto ].
    + inversion H as [| ? ? Hc Ht | ? ? Hn Ht]; subst.
      * apply hpe_cross; [ tauto | tauto ].
      * apply hpe_skip; [ tauto | tauto ].
Qed.

Theorem point_in_ring_ho_agrees : forall (p : Point) (r : Ring),
  ray_avoids_vertices p r ->
  (point_in_ring_ho p r <-> point_in_ring p r).
Proof.
  intros p r Hrav. unfold point_in_ring_ho, point_in_ring.
  apply ho_strict_parity_agree.
  intros e He. apply (ho_edge_agree p r e Hrav He).
Qed.

(* ---------------------------------------------------------------------------
   §3  Far-field evenness in all four directions.
   --------------------------------------------------------------------------- *)

(* Vertex coordinate bound. *)
Fixpoint verts_absmax (l : list Point) : R :=
  match l with
  | [] => 0
  | v :: l' => Rmax (Rmax (Rabs (px v)) (Rabs (py v))) (verts_absmax l')
  end.

Lemma verts_absmax_nonneg : forall l, 0 <= verts_absmax l.
Proof.
  induction l as [| v l' IH]; cbn [verts_absmax]; [ lra | ].
  eapply Rle_trans; [ exact IH | apply Rmax_r ].
Qed.

Lemma verts_absmax_ub : forall l v, In v l ->
  Rabs (px v) <= verts_absmax l /\ Rabs (py v) <= verts_absmax l.
Proof.
  induction l as [| w l' IH]; intros v Hin; [ contradiction | ].
  cbn [verts_absmax]. destruct Hin as [He | Hin].
  - subst w. split.
    + eapply Rle_trans; [ apply Rmax_l | apply Rmax_l ].
    + eapply Rle_trans; [ apply Rmax_r | apply Rmax_l ].
  - destruct (IH v Hin) as [H1 H2].
    split; (eapply Rle_trans; [ eassumption | apply Rmax_r ]).
Qed.

(* No crossing at all means even parity. *)
Lemma ho_even_of_no_cross : forall p es,
  (forall e, In e es -> ~ edge_crosses_ray_ho p e) ->
  ho_parity_even p es.
Proof.
  intros p; induction es as [| e es' IH]; intros Hno; [ constructor | ].
  apply hpe_skip.
  - apply Hno; left; reflexivity.
  - apply IH; intros e' He'; apply Hno; right; exact He'.
Qed.

(* Generic per-edge no-cross facts, given vertex coordinate bounds. *)
Lemma ho_no_cross_of_bounds : forall (p : Point) (r : Ring) (K : R) (e : Edge),
  (forall v, In v r -> Rabs (px v) <= K /\ Rabs (py v) <= K) ->
  In e (ring_edges r) ->
  (K < px p \/ K < py p \/ py p < - K) ->
  ~ edge_crosses_ray_ho p e.
Proof.
  intros p r K [a b] Hbnd Hin Hdir Hc.
  destruct (ring_edges_endpoints_in r _ Hin) as [Ha Hb].
  cbn [fst snd] in Ha, Hb.
  destruct (Hbnd a Ha) as [Hax Hay]. destruct (Hbnd b Hb) as [Hbx Hby].
  pose proof (Rle_abs (px a)). pose proof (Rle_abs (px b)).
  pose proof (Rle_abs (py a)). pose proof (Rle_abs (py b)).
  pose proof (Rabs_pos (px a)).
  assert (Hax' : - K <= px a) by (pose proof (Rabs_left1 (px a)); unfold Rabs in *; destruct (Rcase_abs (px a)); lra).
  assert (Hbx' : - K <= px b) by (unfold Rabs in *; destruct (Rcase_abs (px b)); lra).
  assert (Hay' : - K <= py a) by (unfold Rabs in *; destruct (Rcase_abs (py a)); lra).
  assert (Hby' : - K <= py b) by (unfold Rabs in *; destruct (Rcase_abs (py b)); lra).
  unfold Rabs in Hax, Hay, Hbx, Hby;
    destruct (Rcase_abs (px a)); destruct (Rcase_abs (px b));
    destruct (Rcase_abs (py a)); destruct (Rcase_abs (py b)).
  all: destruct Hc as [[Hy Hx] | [Hy Hx]]; destruct Hdir as [Hd | [Hd | Hd]];
       try lra.
  (* remaining cases: K < px p with a genuine height straddle -- the crossing
     x is a convex combination of px a, px b <= K < px p *)
  all: assert (Hd0 : py b - py a <> 0) by lra || assert (Hd0 : py a - py b <> 0) by lra.
  all: try (revert Hx; apply Rle_not_lt;
            apply (Rmult_le_reg_r (py b - py a)); [ lra | ];
            replace ((px a + (px b - px a) * (py p - py a) / (py b - py a)) * (py b - py a))
              with (px a * (py b - py p) + px b * (py p - py a)) by (field; lra);
            nra).
  all: try (revert Hx; apply Rle_not_lt;
            apply (Rmult_le_reg_r (py a - py b)); [ lra | ];
            replace ((px b + (px a - px b) * (py p - py b) / (py a - py b)) * (py a - py b))
              with (px b * (py a - py p) + px a * (py p - py b)) by (field; lra);
            nra).
Qed.

(* The far-west crossing characterisation: an edge crosses iff its endpoints'
   below-flags differ. *)
Lemma ho_cross_far_west_iff : forall (p a b : Point),
  px p < px a -> px p < px b ->
  (edge_crosses_ray_ho p (a, b)
     <-> ~ ((py a <= py p) <-> (py b <= py p))).
Proof.
  intros p a b Hwa Hwb. unfold edge_crosses_ray_ho. split.
  - intros [[Hy _] | [Hy _]]; intro Hiff; destruct Hiff as [Hf Hg]; lra.
  - intro Hne.
    destruct (Rle_dec (py a) (py p)) as [HA | HA];
    destruct (Rle_dec (py b) (py p)) as [HB | HB].
    + exfalso; apply Hne; tauto.
    + left. split; [ lra | ].
      apply (Rmult_lt_reg_r (py b - py a)); [ lra | ].
      replace ((px a + (px b - px a) * (py p - py a) / (py b - py a)) * (py b - py a))
        with (px a * (py b - py p) + px b * (py p - py a)) by (field; lra).
      nra.
    + right. split; [ lra | ].
      apply (Rmult_lt_reg_r (py a - py b)); [ lra | ].
      replace ((px b + (px a - px b) * (py p - py b) / (py a - py b)) * (py a - py b))
        with (px b * (py a - py p) + px a * (py p - py b)) by (field; lra).
      nra.
    + exfalso; apply Hne; tauto.
Qed.

(* `last` with an irrelevant default. *)
Lemma last_irrel : forall (l : list Point) (a d1 d2 : Point),
  last (a :: l) d1 = last (a :: l) d2.
Proof.
  induction l as [| b l' IH]; intros a d1 d2; [ reflexivity | ].
  cbn [last]. apply (IH b d1 d2).
Qed.

(* The cyclic walk argument: far west of all vertices, the parity of the walk
   equals the flip of the endpoint below-flags. *)
Lemma ho_walk_parity : forall (p : Point) (l : list Point) (v : Point),
  (forall w, In w (v :: l) -> px p < px w) ->
  (ho_parity_odd p (ring_edges (v :: l))
     <-> ~ ((py v <= py p) <-> (py (last l v) <= py p)))
  /\ (ho_parity_even p (ring_edges (v :: l))
     <-> ((py v <= py p) <-> (py (last l v) <= py p))).
Proof.
  intros p l. induction l as [| w l' IH]; intros v Hwest.
  - cbn [ring_edges last]. split.
    + split; [ intro Ho; inversion Ho | intro Hne; exfalso; apply Hne; tauto ].
    + split; [ intros _; tauto | intros _; constructor ].
  - assert (Hwest' : forall u, In u (w :: l') -> px p < px u)
      by (intros u Hu; apply Hwest; right; exact Hu).
    destruct (IH w Hwest') as [IHodd IHeven].
    assert (Hcr : edge_crosses_ray_ho p (v, w)
                    <-> ~ ((py v <= py p) <-> (py w <= py p))).
    { apply ho_cross_far_west_iff;
        apply Hwest; [ left; reflexivity | right; left; reflexivity ]. }
    assert (Hlast : last (w :: l') v = last l' w).
    { destruct l' as [| u l'']; [ reflexivity | ].
      cbn [last]. apply last_irrel. }
    cbn [ring_edges]. rewrite Hlast.
    destruct (Rle_dec (py v) (py p)) as [Bv | Bv];
    destruct (Rle_dec (py w) (py p)) as [Bw | Bw].
    + assert (Hnc : ~ edge_crosses_ray_ho p (v, w))
        by (intro Hc; apply (proj1 Hcr Hc); tauto).
      rewrite (ho_odd_cons_skip _ _ _ Hnc), (ho_even_cons_skip _ _ _ Hnc).
      rewrite IHodd, IHeven.
      destruct (Rle_dec (py (last l' w)) (py p)) as [BL | BL];
        split; split; tauto.
    + assert (Hc : edge_crosses_ray_ho p (v, w))
        by (apply (proj2 Hcr); intro Hiff; destruct Hiff as [Hf _]; auto;
            pose proof (Hf Bv); lra).
      rewrite (ho_odd_cons_cross _ _ _ Hc), (ho_even_cons_cross _ _ _ Hc).
      rewrite IHodd, IHeven.
      destruct (Rle_dec (py (last l' w)) (py p)) as [BL | BL];
        split; split; intros; tauto.
    + assert (Hc : edge_crosses_ray_ho p (v, w))
        by (apply (proj2 Hcr); intro Hiff; destruct Hiff as [_ Hg];
            pose proof (Hg Bw); lra).
      rewrite (ho_odd_cons_cross _ _ _ Hc), (ho_even_cons_cross _ _ _ Hc).
      rewrite IHodd, IHeven.
      destruct (Rle_dec (py (last l' w)) (py p)) as [BL | BL];
        split; split; intros; tauto.
    + assert (Hnc : ~ edge_crosses_ray_ho p (v, w))
        by (intro Hc; apply (proj1 Hcr Hc); split; intro; lra).
      rewrite (ho_odd_cons_skip _ _ _ Hnc), (ho_even_cons_skip _ _ _ Hnc).
      rewrite IHodd, IHeven.
      destruct (Rle_dec (py (last l' w)) (py p)) as [BL | BL];
        split; split; tauto.
Qed.

Lemma last_app_single : forall (l : list Point) (v d : Point),
  last (l ++ [v]) d = v.
Proof.
  induction l as [| a l' IH]; intros v d; [ reflexivity | ].
  cbn [app]. rewrite <- (IH v d) at 2.
  destruct l' as [| b l'']; [ reflexivity | ].
  cbn [last app]. reflexivity.
Qed.

(* Far WEST of a CLOSED ring: even parity -- the below-flag returns home. *)
Lemma ho_far_west_even : forall (p : Point) (r : Ring),
  ring_closed r ->
  (forall w, In w r -> px p < px w) ->
  ho_parity_even p (ring_edges r).
Proof.
  intros p r [v [ls Heq]] Hwest. subst r.
  destruct (ho_walk_parity p (ls ++ [v]) v Hwest) as [_ Heven].
  apply Heven. rewrite last_app_single. tauto.
Qed.

(* The four directions assembled: half-open parity is false beyond a radius. *)
Theorem ho_far_false : forall (r : Ring),
  ring_closed r ->
  exists Mq, 0 < Mq /\
    forall q, Mq < px q * px q + py q * py q -> ~ point_in_ring_ho q r.
Proof.
  intros r Hclosed.
  set (K := verts_absmax r + 1).
  assert (HK0 : 1 <= K)
    by (unfold K; pose proof (verts_absmax_nonneg r); lra).
  assert (HKb : forall v, In v r -> Rabs (px v) <= K /\ Rabs (py v) <= K).
  { intros v Hv. destruct (verts_absmax_ub r v Hv) as [H1 H2].
    unfold K; lra. }
  exists (2 * ((K + 1) * (K + 1))). split; [ nra | ].
  intros q Hfar Hodd.
  (* some coordinate exceeds K + 1 in absolute value *)
  assert (Hbig : K + 1 < px q \/ px q < - (K + 1)
              \/ K + 1 < py q \/ py q < - (K + 1)).
  { destruct (Rle_dec (px q) (K + 1)) as [H1 | H1]; [ | left; lra ].
    destruct (Rle_dec (- (K + 1)) (px q)) as [H2 | H2]; [ | right; left; lra ].
    destruct (Rle_dec (py q) (K + 1)) as [H3 | H3]; [ | right; right; left; lra ].
    destruct (Rle_dec (- (K + 1)) (py q)) as [H4 | H4]; [ | right; right; right; lra ].
    exfalso. nra. }
  destruct Hbig as [Hd | [Hd | [Hd | Hd]]].
  - (* far right *)
    apply (ho_parity_excl q (ring_edges r) Hodd).
    apply ho_even_of_no_cross. intros e He.
    apply (ho_no_cross_of_bounds q r K e HKb He). left; lra.
  - (* far west: the cyclic walk argument *)
    apply (ho_parity_excl q (ring_edges r) Hodd).
    apply ho_far_west_even; [ exact Hclosed | ].
    intros w Hw. destruct (HKb w Hw) as [Hx _].
    unfold Rabs in Hx; destruct (Rcase_abs (px w)); lra.
  - (* far up *)
    apply (ho_parity_excl q (ring_edges r) Hodd).
    apply ho_even_of_no_cross. intros e He.
    apply (ho_no_cross_of_bounds q r K e HKb He). right; left; lra.
  - (* far down *)
    apply (ho_parity_excl q (ring_edges r) Hodd).
    apply ho_even_of_no_cross. intros e He.
    apply (ho_no_cross_of_bounds q r K e HKb He). right; right; lra.
Qed.

(* ---------------------------------------------------------------------------
   §4  THE CAPSTONE: H1's trapped half, reduced to one concrete kernel.
   --------------------------------------------------------------------------- *)

(* THE kernel: local constancy of the half-open parity along complement
   paths.  This is the y-monotone vertex-pairing content of the polygonal
   JCT -- the single remaining obligation of the trapped half. *)
Definition ho_parity_locally_constant (r : Ring) : Prop :=
  forall g : R -> Point,
    path_continuous g ->
    (forall t, 0 <= t <= 1 -> ring_complement r (g t)) ->
    forall t, 0 <= t <= 1 ->
      exists d, 0 < d /\
        forall s, 0 <= s <= 1 -> Rabs (s - t) < d ->
          (point_in_ring_ho (g s) r <-> point_in_ring_ho (g t) r).

Theorem odd_parity_trapped_of_ho_kernel : forall (r : Ring) (p : Point),
  ring_closed r ->
  ho_parity_locally_constant r ->
  ray_avoids_vertices p r ->
  point_in_ring p r ->
  in_bounded_component_cont r p.
Proof.
  intros r p Hclosed Hker Hrav Hpir.
  apply (odd_parity_trapped_of_invariant r p (fun q => point_in_ring_ho q r)).
  - intro pt. apply point_in_ring_ho_dec.
  - split; [ exact Hker | exact (ho_far_false r Hclosed) ].
  - apply point_in_ring_ho_agrees. exact Hrav.
  - exact Hpir.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions point_in_ring_ho_agrees.
Print Assumptions ho_far_west_even.
Print Assumptions ho_far_false.
Print Assumptions odd_parity_trapped_of_ho_kernel.
