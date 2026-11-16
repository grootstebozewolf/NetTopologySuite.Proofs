(* ============================================================================
   NetTopologySuite.Proofs.JCTShearLift
   ----------------------------------------------------------------------------
   The polygonal Jordan seam WITHOUT `no_horizontal_edges`.

   `JCTEscapeDescentHolds.v : parity_seam_offring_taut` closes the corrected
   off-ring seam for taut, core-nodup rings with no horizontal edge.  The
   horizontal guard excludes every axis-aligned rectangle.  This file removes
   it by a change of sheet, not by re-running the descent:

     1. A small vertical shear S_k (x, y) |-> (x, y + k x) (det 1) makes every
        edge non-horizontal and keeps the sheared east ray off the sheared
        vertices, for all but finitely many k.
     2. For k small enough, the east-ray crossing test is edge-by-edge the
        same before and after the shear (`edge_cross_shear`).  The crossing
        condition is a sign test on cross(a - p, b - p), which S_k preserves
        (det 1); every vertex height off p's height keeps its sign for small
        k; and a vertex AT p's height is strictly west of p (the ray guard),
        where the sign test rejects the edge on both sheets (the arithmetic
        core `ray_sign_shear_core` holds for either sign of k; the headline
        picks k > 0).  So `point_in_ring` is unchanged (`point_in_ring_shear`).
     3. The interior transports along any invertible affine map
        (`SheetRingPip.v : geo_act`), and so do tautness, core-nodup and the
        point count; the horizontal-free seam applies on the sheared sheet.

   Headline: `parity_seam_offring_taut_nh`.  The remaining ring guards are
   `ring_taut` and `ring_core_nodup`; the point guards are off-ring and
   `ray_avoids_vertices` (both necessary: JCT_OnEdgeCounterexample.v,
   JCT_VertexGrazingCounterexample.v; the notch hexagon of
   JCT_HorizontalEdgeCounterexample.v fails `ray_avoids_vertices`).

   Pure R; no Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam
  PointInRingCorrect JCT_OnEdgeCounterexample JCTTautClearance JCTRingCycle
  JCTHugStep JCTEscapeDescentHolds ClothoidPlacement ClothoidAffineStmt
  SheetRingPipStmt SheetRingPip GeneralTriangleSeparation TriangleTautBridge.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The crossing test as a sign test.                                      *)
(* -------------------------------------------------------------------------- *)

Lemma div_pos_iff : forall x d, 0 < d -> (0 < x / d <-> 0 < x).
Proof.
  intros x d Hd. split; intro H.
  - replace x with ((x / d) * d) by (field; lra). apply Rmult_lt_0_compat; lra.
  - apply Rdiv_lt_0_compat; assumption.
Qed.

(* edge_crosses_ray, read relative to p: a strict straddle of p's height plus
   the sign of cross(a - p, b - p). *)
Lemma ecr_iff : forall p a b,
  edge_crosses_ray p (a, b) <->
  ((py a - py p < 0 < py b - py p /\
      0 < (px a - px p) * (py b - py p) - (py a - py p) * (px b - px p)) \/
   (py b - py p < 0 < py a - py p /\
      (px a - px p) * (py b - py p) - (py a - py p) * (px b - px p) < 0)).
Proof.
  intros p a b. unfold edge_crosses_ray.
  set (C := (px a - px p) * (py b - py p) - (py a - py p) * (px b - px p)).
  split; intros [[Hs Hx] | [Hs Hx]].
  - left. split; [lra|].
    assert (E : px a + (px b - px a) * (py p - py a) / (py b - py a) - px p
                = C / (py b - py a)) by (unfold C; field; lra).
    apply (div_pos_iff C (py b - py a)); lra.
  - right. split; [lra|].
    assert (E : px b + (px a - px b) * (py p - py b) / (py a - py b) - px p
                = (- C) / (py a - py b)) by (unfold C; field; lra).
    assert (0 < - C) by (apply (div_pos_iff (- C) (py a - py b)); lra). lra.
  - left. split; [lra|].
    assert (E : px a + (px b - px a) * (py p - py a) / (py b - py a) - px p
                = C / (py b - py a)) by (unfold C; field; lra).
    assert (0 < C / (py b - py a)) by (apply div_pos_iff; lra). lra.
  - right. split; [lra|].
    assert (E : px b + (px a - px b) * (py p - py b) / (py a - py b) - px p
                = (- C) / (py a - py b)) by (unfold C; field; lra).
    assert (0 < (- C) / (py a - py b)) by (apply div_pos_iff; lra). lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The arithmetic core: the sign test survives a small shear.             *)
(* -------------------------------------------------------------------------- *)

Lemma sign_keep : forall x y, x * y > 0 -> (x < 0 -> y < 0) /\ (0 < x -> 0 < y).
Proof.
  intros x y H. split; intro Hx.
  - destruct (Rlt_le_dec y 0) as [Hy|Hy]; [exact Hy|].
    assert (x * y <= 0) by nra. lra.
  - destruct (Rlt_le_dec 0 y) as [Hy|Hy]; [exact Hy|].
    assert (x * y <= 0) by nra. lra.
Qed.

Lemma sign_keep_back : forall x y, x * y > 0 -> (y < 0 -> x < 0) /\ (0 < y -> 0 < x).
Proof.
  intros x y H. rewrite Rmult_comm in H. apply sign_keep. exact H.
Qed.

Lemma ray_sign_shear_core : forall a1 a2 b1 b2 k,
  (a2 <> 0 -> a2 * (a2 + k * a1) > 0) ->
  (b2 <> 0 -> b2 * (b2 + k * b1) > 0) ->
  (a2 = 0 -> a1 < 0) ->
  (b2 = 0 -> b1 < 0) ->
  (((a2 < 0 < b2 /\ 0 < a1 * b2 - a2 * b1) \/
    (b2 < 0 < a2 /\ a1 * b2 - a2 * b1 < 0)) <->
   ((a2 + k * a1 < 0 < b2 + k * b1 /\ 0 < a1 * b2 - a2 * b1) \/
    (b2 + k * b1 < 0 < a2 + k * a1 /\ a1 * b2 - a2 * b1 < 0))).
Proof.
  intros a1 a2 b1 b2 k Ha Hb Ha0 Hb0.
  destruct (Req_dec a2 0) as [Ea | Na]; destruct (Req_dec b2 0) as [Eb | Nb].
  - (* both at p's height: C = 0 *)
    subst a2 b2. split; intros [[_ HC] | [_ HC]]; nra.
  - (* a at p's height, strictly west *)
    subst a2. pose proof (Ha0 eq_refl) as Ha1.
    destruct (sign_keep _ _ (Hb Nb)) as [Hb1 Hb2].
    destruct (sign_keep_back _ _ (Hb Nb)) as [Hb3 Hb4].
    split; intros [[Hs HC] | [Hs HC]]; exfalso.
    + lra.
    + lra.
    + assert (0 < b2) by (apply Hb4; lra). nra.
    + assert (b2 < 0) by (apply Hb3; lra). nra.
  - (* b at p's height, strictly west *)
    subst b2. pose proof (Hb0 eq_refl) as Hb1.
    destruct (sign_keep _ _ (Ha Na)) as [Ha1 Ha2].
    destruct (sign_keep_back _ _ (Ha Na)) as [Ha3 Ha4].
    split; intros [[Hs HC] | [Hs HC]]; exfalso.
    + lra.
    + lra.
    + assert (a2 < 0) by (apply Ha3; lra). nra.
    + assert (0 < a2) by (apply Ha4; lra). nra.
  - destruct (sign_keep _ _ (Ha Na)) as [Ha1 Ha2].
    destruct (sign_keep_back _ _ (Ha Na)) as [Ha3 Ha4].
    destruct (sign_keep _ _ (Hb Nb)) as [Hb1 Hb2].
    destruct (sign_keep_back _ _ (Hb Nb)) as [Hb3 Hb4].
    split; intros [[[Hs1 Hs2] HC] | [[Hs1 Hs2] HC]].
    + left. split; [split|]; auto.
    + right. split; [split|]; auto.
    + left. split; [split|]; auto.
    + right. split; [split|]; auto.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The vertical shear and the per-edge crossing.                          *)
(* -------------------------------------------------------------------------- *)

Definition vsh (k : R) : Aff2 := mkAff2 (mkPoint 0 0) (mkLin2 1 0 k 1).

Lemma vsh_det : forall k, lin_det (af_L (vsh k)) <> 0.
Proof. intro k. unfold lin_det. cbn. lra. Qed.

Lemma vsh_px : forall k q, px (aff_ap (vsh k) q) = px q.
Proof. intros k q. rewrite aff_px. cbn. ring. Qed.

Lemma vsh_py : forall k q, py (aff_ap (vsh k) q) = py q + k * px q.
Proof. intros k q. rewrite aff_py. cbn. ring. Qed.

(* A vertex is "k-stable" for p when its height off p keeps its sign. *)
Definition k_stable (k : R) (p v : Point) : Prop :=
  py v <> py p ->
  (py v - py p) * ((py v - py p) + k * (px v - px p)) > 0.

Lemma edge_cross_shear : forall k p a b,
  k_stable k p a -> k_stable k p b ->
  ~ (py a = py p /\ px p <= px a) -> ~ (py b = py p /\ px p <= px b) ->
  (edge_crosses_ray p (a, b) <->
   edge_crosses_ray (aff_ap (vsh k) p) (aff_ap (vsh k) a, aff_ap (vsh k) b)).
Proof.
  intros k p a b Hsa Hsb Hra Hrb.
  rewrite (ecr_iff p a b), ecr_iff.
  rewrite !vsh_px, !vsh_py.
  replace (py a + k * px a - (py p + k * px p))
    with ((py a - py p) + k * (px a - px p)) by ring.
  replace (py b + k * px b - (py p + k * px p))
    with ((py b - py p) + k * (px b - px p)) by ring.
  replace ((px a - px p) * (py b - py p + k * (px b - px p))
           - (py a - py p + k * (px a - px p)) * (px b - px p))
    with ((px a - px p) * (py b - py p) - (py a - py p) * (px b - px p)) by ring.
  apply ray_sign_shear_core.
  - intro N. apply Hsa. intro E. apply N. lra.
  - intro N. apply Hsb. intro E. apply N. lra.
  - intro E. destruct (Rlt_le_dec (px a) (px p)) as [L|L]; [lra|].
    exfalso. apply Hra. split; lra.
  - intro E. destruct (Rlt_le_dec (px b) (px p)) as [L|L]; [lra|].
    exfalso. apply Hrb. split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Parity along a pointwise-equivalent edge map.                          *)
(* -------------------------------------------------------------------------- *)

Lemma parity_map : forall (p p' : Point) (g : Edge -> Edge) (es : list Edge),
  (forall e, In e es -> (edge_crosses_ray p e <-> edge_crosses_ray p' (g e))) ->
  (ray_parity_odd p es <-> ray_parity_odd p' (map g es)) /\
  (ray_parity_even p es <-> ray_parity_even p' (map g es)).
Proof.
  intros p p' g es. induction es as [|e es IH]; intro Hpt.
  - cbn. split; split; intro H.
    + inversion H.
    + inversion H.
    + constructor.
    + constructor.
  - assert (He := Hpt e (or_introl eq_refl)).
    destruct (IH (fun x Hx => Hpt x (or_intror Hx))) as [Io Ie].
    cbn [map]. split; split; intro H; inversion H; subst.
    + apply rpo_cross; [apply He; assumption | apply Ie; assumption].
    + apply rpo_skip; [rewrite <- He; assumption | apply Io; assumption].
    + apply rpo_cross; [apply He; assumption | apply Ie; assumption].
    + apply rpo_skip; [rewrite He; assumption | apply Io; assumption].
    + apply rpe_cross; [apply He; assumption | apply Io; assumption].
    + apply rpe_skip; [rewrite <- He; assumption | apply Ie; assumption].
    + apply rpe_cross; [apply He; assumption | apply Io; assumption].
    + apply rpe_skip; [rewrite He; assumption | apply Ie; assumption].
Qed.

Lemma in_ring_edges_in : forall (r : Ring) a b,
  In (a, b) (ring_edges r) -> In a r /\ In b r.
Proof.
  induction r as [|x r IH]; intros a b H; [contradiction|].
  destruct r as [|y r']; [contradiction|].
  change (ring_edges (x :: y :: r')) with ((x, y) :: ring_edges (y :: r')) in H.
  destruct H as [E | H].
  - inversion E; subst. split; [left; reflexivity | right; left; reflexivity].
  - destruct (IH a b H) as [Ha Hb]. split; right; assumption.
Qed.

Theorem point_in_ring_shear : forall k p r,
  (forall v, In v r -> k_stable k p v) ->
  ray_avoids_vertices p r ->
  (point_in_ring p r <-> point_in_ring (aff_ap (vsh k) p) (ring_act (vsh k) r)).
Proof.
  intros k p r Hst Hrav. unfold point_in_ring, ring_act.
  rewrite pip_ring_edges_map.
  apply parity_map. intros [a b] He. cbn [fst snd].
  destruct (in_ring_edges_in r a b He) as [Ha Hb].
  apply edge_cross_shear; auto.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Choosing k.                                                            *)
(* -------------------------------------------------------------------------- *)

Lemma k_stable_small : forall (p : Point) (l : list Point),
  exists d, 0 < d /\ forall k, 0 < k < d -> forall v, In v l -> k_stable k p v.
Proof.
  intros p l. induction l as [|v l IH].
  - exists 1. split; [lra | intros k _ v []].
  - destruct IH as (d0 & Hd0 & H0).
    set (x := px v - px p). set (y := py v - py p).
    set (D := x * x + y * y + 1).
    assert (HD : 0 < D) by (unfold D; nra).
    destruct (Req_dec y 0) as [Ey | Ny].
    + exists d0. split; [exact Hd0|].
      intros k Hk w [<- | Hw].
      * intro N. exfalso. apply N. unfold y in Ey. lra.
      * exact (H0 k Hk w Hw).
    + assert (Hy2 : 0 < y * y) by (apply Rsqr_pos_lt in Ny; unfold Rsqr in Ny; exact Ny).
      exists (Rmin d0 (y * y / D)). split.
      { apply Rmin_pos; [exact Hd0 | apply Rdiv_lt_0_compat; assumption]. }
      intros k Hk w [<- | Hw].
      * intros _. fold x y.
        assert (Hk1 : k < y * y / D) by (eapply Rlt_le_trans; [apply Hk | apply Rmin_r]).
        assert (Hk2 : k * D < y * y).
        { apply (Rmult_lt_compat_r D) in Hk1; [|exact HD].
          replace (y * y / D * D) with (y * y) in Hk1 by (field; lra). exact Hk1. }
        assert (Hxy : - (x * y) <= (x * x + y * y) / 2).
        { assert (Hs : 0 <= (x + y) * (x + y)) by apply Rle_0_sqr.
          replace ((x + y) * (x + y)) with (x * x + y * y + 2 * (x * y)) in Hs by ring.
          lra. }
        assert (Hk3 : k * (- (x * y)) <= k * ((x * x + y * y) / 2))
          by (apply Rmult_le_compat_l; lra).
        assert (Hsq : 0 <= x * x + y * y) by nra.
        assert (Hk4 : k * ((x * x + y * y) / 2) <= k * D)
          by (apply Rmult_le_compat_l; [lra | unfold D; lra]).
        replace (y * (y + k * x)) with (y * y - k * (- (x * y))) by ring.
        lra.
      * apply (H0 k); [|exact Hw].
        split; [lra|]. eapply Rlt_le_trans; [apply Hk | apply Rmin_l].
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Core-nodup rings have no degenerate edge.                              *)
(* -------------------------------------------------------------------------- *)

Lemma ring_edges_snoc : forall (l : list Point) x d, l <> [] ->
  ring_edges (l ++ [x]) = ring_edges l ++ [(last l d, x)].
Proof.
  induction l as [|a l IH]; intros x d Hne; [contradiction|].
  destruct l as [|b l'].
  - reflexivity.
  - change ((a :: b :: l') ++ [x]) with (a :: ((b :: l') ++ [x])).
    change (ring_edges (a :: (b :: l') ++ [x]))
      with ((a, b) :: ring_edges ((b :: l') ++ [x])).
    rewrite (IH x d) by discriminate.
    reflexivity.
Qed.

Lemma nodup_edges_proper : forall (l : list Point), NoDup l ->
  forall a b, In (a, b) (ring_edges l) -> a <> b.
Proof.
  induction l as [|x l IH]; intros Hnd a b H; [contradiction|].
  destruct l as [|y l']; [contradiction|].
  change (ring_edges (x :: y :: l')) with ((x, y) :: ring_edges (y :: l')) in H.
  inversion Hnd as [|? ? Hx Hnd']; subst.
  destruct H as [E | H].
  - inversion E; subst. intro Eq. subst. apply Hx. left. reflexivity.
  - exact (IH Hnd' a b H).
Qed.

Lemma core_nodup_edges_proper : forall r,
  ring_core_nodup r -> ring_has_minimum_points r ->
  forall a b, In (a, b) (ring_edges r) -> a <> b.
Proof.
  intros r (p & ps & Hr & Hnd) Hmin a b H. subst r.
  assert (Hps : ps <> []).
  { intro E. subst ps. unfold ring_has_minimum_points in Hmin. cbn in Hmin. lia. }
  change (p :: ps ++ [p]) with ((p :: ps) ++ [p]) in H.
  rewrite (ring_edges_snoc (p :: ps) p p) in H by discriminate.
  apply in_app_or in H. destruct H as [H | [E | []]].
  - exact (nodup_edges_proper (p :: ps) Hnd a b H).
  - injection E as Ea Eb. subst a b.
    intro Eq.
    inversion Hnd as [|? ? Hp _]; subst.
    apply Hp.
    destruct ps as [|q qs]; [contradiction|].
    assert (Hl : In (last (q :: qs) p) (q :: qs)) by (apply last_In; discriminate).
    change (last (p :: q :: qs) p) with (last (q :: qs) p) in Eq.
    rewrite Eq in Hl. exact Hl.
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  The headline.                                                          *)
(* -------------------------------------------------------------------------- *)

(* The corrected off-ring seam with the horizontal-edge guard dropped.  Its
   premise list mirrors `parity_characterises_interior_cont_offring` minus
   `no_horizontal_edge_at`, for shape parity with the guarded seam; the proof
   of `parity_seam_offring_taut_nh` does not use `ring_simple` / `ring_closed`
   (taut and core-nodup imply them).  `parity_seam_offring_taut_guard_free` is
   the same fact with only the premises it needs. *)
Definition parity_characterises_interior_cont_offring_nh (p : Point) (r : Ring) : Prop :=
  ring_simple r -> ring_closed r -> ring_has_minimum_points r ->
  ring_complement r p ->
  ray_avoids_vertices p r ->
  (geometric_interior_cont p r <-> point_in_ring p r).

Theorem parity_seam_offring_taut_nh : forall (r : Ring) (p : Point),
  ring_taut r ->
  ring_core_nodup r ->
  parity_characterises_interior_cont_offring_nh p r.
Proof.
  intros r p Ht Hnd _ _ Hmin Hc Hrav.
  destruct (k_stable_small p r) as (d & Hd & Hst).
  set (bad := map (fun e => - (py (snd e) - py (fst e)) / (px (snd e) - px (fst e)))
                  (ring_edges r)
              ++ map (fun v => (py p - py v) / (px v - px p)) r).
  destruct (avoid_list bad d Hd) as (k & Hk & Hav).
  set (f := vsh k).
  assert (HD : lin_det (af_L f) <> 0) by apply vsh_det.
  (* the sheared ring is a horizontal-free seam ring *)
  assert (Hnoh' : no_horizontal_edges (ring_act f r)).
  { intros g' Hg'. unfold ring_act in Hg'. rewrite pip_ring_edges_map in Hg'.
    apply in_map_iff in Hg'. destruct Hg' as ([a b] & <- & Hab). cbn [fst snd].
    unfold f. rewrite !vsh_py. intro E.
    destruct (Req_dec (px b) (px a)) as [Ex | Nx].
    - apply (core_nodup_edges_proper r Hnd Hmin a b Hab).
      destruct a as [ax ay], b as [bx by_]. cbn in Ex, E |- *.
      rewrite Ex in E. assert (ay = by_) by lra. subst. reflexivity.
    - apply (Hav (- (py b - py a) / (px b - px a))).
      + apply in_or_app. left. apply in_map_iff. exists (a, b). split; [reflexivity | exact Hab].
      + field_simplify_eq; [lra | lra]. }
  assert (Hrav' : ray_avoids_vertices (aff_ap f p) (ring_act f r)).
  { intros v' Hv' [Ey Ex]. unfold ring_act in Hv'. apply in_map_iff in Hv'.
    destruct Hv' as (v & <- & Hv). unfold f in Ey, Ex.
    rewrite !vsh_py in Ey. rewrite !vsh_px in Ex.
    destruct (Req_dec (px v) (px p)) as [E | N].
    - apply (Hrav v Hv). split; [rewrite E in Ey; lra | lra].
    - apply (Hav ((py p - py v) / (px v - px p))).
      + apply in_or_app. right. apply in_map_iff. exists v. split; [reflexivity | exact Hv].
      + field_simplify_eq; [lra | lra]. }
  assert (Ht' : ring_taut (ring_act f r)) by (apply taut_act; assumption).
  assert (Hnd' : ring_core_nodup (ring_act f r)) by (apply core_nodup_act; assumption).
  assert (Hc' : ring_complement (ring_act f r) (aff_ap f p))
    by (apply (proj1 (complement_act f r p HD)); exact Hc).
  rewrite (geo_act f r p HD).
  rewrite (parity_seam_offring_taut (ring_act f r) (aff_ap f p) Ht' Hnd' Hnoh'
             (ring_taut_implies_simple _ Ht')
             (ring_core_nodup_closed _ Hnd')
             (min_points_act f r Hmin) Hc'
             (proj2 (Forall_forall _ _) Hnoh') Hrav').
  symmetry. apply point_in_ring_shear; [|exact Hrav].
  intros v Hv. apply Hst; [exact Hk | exact Hv].
Qed.

(* The headline restated as "the old guard is redundant": on taut, core-nodup
   rings the guarded seam of JCT_OnEdgeCounterexample.v holds without its
   `no_horizontal_edge_at` premise doing any work. *)
Corollary parity_seam_offring_taut_guard_free : forall (r : Ring) (p : Point),
  ring_taut r -> ring_core_nodup r -> ring_has_minimum_points r ->
  ring_complement r p -> ray_avoids_vertices p r ->
  (geometric_interior_cont p r <-> point_in_ring p r).
Proof.
  intros r p Ht Hnd Hmin Hc Hrav.
  apply (parity_seam_offring_taut_nh r p Ht Hnd); try assumption.
  - apply ring_taut_implies_simple. exact Ht.
  - apply ring_core_nodup_closed. exact Hnd.
Qed.

(* -------------------------------------------------------------------------- *)
(* §8  Witness: a ring with a horizontal edge, and a real interior point.     *)
(* -------------------------------------------------------------------------- *)

(* The right triangle (0,0), (4,0), (0,4): its bottom edge is horizontal, so
   `parity_seam_offring_taut` does not apply; (1,1) is off the ring, its ray
   misses every vertex, the ray parity is odd, and the new seam concludes it
   is geometric interior. *)
Definition rt_ring : Ring := gtri_ring 0 0 4 0 0 4.
Definition rt_pt : Point := mkPoint 1 1.

Lemma rt_ccw : 0 < gdbl 0 0 4 0 0 4.
Proof. unfold gdbl. lra. Qed.

Lemma rt_has_horizontal_edge : ~ no_horizontal_edges rt_ring.
Proof.
  intro H. apply (H (mkPoint 0 0, mkPoint 4 0)); [|reflexivity].
  unfold rt_ring. rewrite ring_edges_gtri. left. reflexivity.
Qed.

Lemma rt_pt_off_ring : ring_complement rt_ring rt_pt.
Proof.
  intros (e & t & He & Ht & Hx & Hy).
  unfold rt_ring in He. rewrite ring_edges_gtri in He.
  destruct He as [E | [E | [E | []]]]; subst e; cbn in Hx, Hy; lra.
Qed.

Lemma rt_pt_ray_guard : ray_avoids_vertices rt_pt rt_ring.
Proof.
  intros v Hv [Hy _]. unfold rt_ring, gtri_ring in Hv.
  destruct Hv as [E | [E | [E | [E | []]]]]; subst v; cbn in Hy; lra.
Qed.

Lemma rt_pt_in_ring : point_in_ring rt_pt rt_ring.
Proof.
  unfold point_in_ring, rt_ring. rewrite ring_edges_gtri.
  apply rpo_skip; [unfold edge_crosses_ray; cbn; lra|].
  apply rpo_cross; [unfold edge_crosses_ray; cbn; left; split; [lra|]|].
  { replace (0 - 4) with (-4) by ring. lra. }
  apply rpe_skip; [unfold edge_crosses_ray; cbn; intros [[? ?] | [? ?]]; lra|].
  apply rpe_nil.
Qed.

Theorem shear_lift_witness :
  ~ no_horizontal_edges rt_ring /\ geometric_interior_cont rt_pt rt_ring.
Proof.
  split; [exact rt_has_horizontal_edge|].
  apply (parity_seam_offring_taut_guard_free rt_ring rt_pt).
  - apply tri_ring_taut. exact rt_ccw.
  - apply tri_core_nodup. exact rt_ccw.
  - unfold ring_has_minimum_points, rt_ring, gtri_ring. cbn. lia.
  - exact rt_pt_off_ring.
  - exact rt_pt_ray_guard.
  - exact rt_pt_in_ring.
Qed.

Print Assumptions parity_seam_offring_taut_nh.
Print Assumptions parity_seam_offring_taut_guard_free.
Print Assumptions shear_lift_witness.
