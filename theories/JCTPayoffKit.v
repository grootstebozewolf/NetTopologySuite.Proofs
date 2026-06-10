(* ============================================================================
   NetTopologySuite.Proofs.JCTPayoffKit
   ----------------------------------------------------------------------------
   ESCAPE DESCENT, rung 5c-16a: THE PAYOFF KIT.  At the eastmost vertex
   the walk's corner-band points have computable crossing counts; this
   file supplies the kernels:

     - the OUT-edge counting symmetry (`out_edge_prefix_unique`,
       `out_edge_count_le1`, `ho_count_one_out`) completing rung 5c-15;
     - `ho_count_zero_of_no_cross` (no crossings, count zero);
     - `noncross_far`: a non-incident edge never crosses the ray of a
       band point near the EASTMOST vertex -- its crossing abscissa is a
       convex combination of endpoint abscissae (hence at most px vS),
       and the corner disk (rung 5c-10) excludes the near range, so the
       crossing point would lie strictly west of the band point;
     - the incident-edge kernels: spans missing the band height never
       cross (`incident_above_nocross`/`_below_nocross`), a carrier at
       or west of the point never crosses (`carrier_west_nocross`), and
       a strictly straddling carrier strictly east always does
       (`carrier_east_cross`);
     - `wall_corridor_clear_corner_east_top`, the last clearance mirror
       (east corridor abutting a TOP vertex).

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Arith Lia.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam.
From NTS.Proofs Require Import PointInRingCorrect JCT JCT_OnEdgeCounterexample.
From NTS.Proofs Require Import ConvexOffringSeam JCTParityTransport.
From NTS.Proofs Require Import JCTHalfOpenParity JCTGenericStability JCTLevelJump.
From NTS.Proofs Require Import JCTTrappedHalf JCTSeamAssembly JCTEscapeDescent.
From NTS.Proofs Require Import JCTEastApproach JCTCorridor JCTWalkKit JCTWalkStep.
From NTS.Proofs Require Import JCTTautClearance JCTWallClear JCTCornerSector.
From NTS.Proofs Require Import JCTCornerClear JCTMirrorKit JCTTopPassage.
From NTS.Proofs Require Import JCTPassageKit JCTTipCrossing JCTCornerBox.
From NTS.Proofs Require Import JCTRingCycle JCTHugStep JCTHugMirror.
From NTS.Proofs Require Import JCTMinOpenStep JCTMinOpenMirror JCTCornerDisk.
From NTS.Proofs Require Import JCTPinchedStep JCTPinchedMirror.
From NTS.Proofs Require Import JCTCornerDispatch JCTHugCycle JCTEdgeCount.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §1  The out-edge counting symmetry.
   --------------------------------------------------------------------------- *)

Lemma out_edge_prefix_unique : forall (r : Ring) (p : Point)
                                      (ps : list Point)
                                      (b b' v : Point)
                                      (l1 l2 l1' l2' : list Point),
  r = p :: ps ++ [p] ->
  NoDup (p :: ps) ->
  r = l1 ++ v :: b :: l2 ->
  r = l1' ++ v :: b' :: l2' ->
  l1 = l1'.
Proof.
  intros r p ps b b' v l1 l2 l1' l2' Hr Hnd Hs1 Hs2.
  pose proof Hnd as Hnd'. apply NoDup_cons_iff in Hnd'.
  destruct Hnd' as [Hp Hndps].
  destruct (coord_point_dec v p) as [Hvp | Hvp].
  - subst v.
    (* the seam's out-edge starts at the head: both prefixes are empty *)
    assert (Hkey : forall (lA lB : list Point) (bb : Point),
              p :: ps ++ [p] = lA ++ p :: bb :: lB -> lA = []).
    { intros lA lB bb HsA.
      destruct lA as [| x lAc]; [ reflexivity | ].
      cbn in HsA. injection HsA as Hxp Htail. subst x.
      exfalso.
      assert (Hcnt : (count_occ coord_point_dec (ps ++ [p]) p = 1)%nat).
      { rewrite count_occ_app. cbn [count_occ].
        destruct (coord_point_dec p p) as [_ | Hc]; [ | congruence ].
        pose proof (proj1 (count_occ_not_In coord_point_dec ps p) Hp).
        lia. }
      assert (Hcnt2 : (count_occ coord_point_dec lAc p
               + S (count_occ coord_point_dec (bb :: lB) p) = 1)%nat).
      { rewrite Htail in Hcnt.
        rewrite count_occ_app in Hcnt.
        rewrite count_occ_cons_eq in Hcnt by reflexivity.
        exact Hcnt. }
      assert (HpIn : In p (bb :: lB)).
      { assert (Hl1 : last (ps ++ [p]) p = p) by apply last_snoc.
        rewrite Htail in Hl1.
        rewrite (last_app_nonempty lAc (p :: bb :: lB) p
                   ltac:(discriminate)) in Hl1.
        assert (Hl1' : last (bb :: lB) p = p) by exact Hl1.
        rewrite <- Hl1'. apply last_In. discriminate. }
      apply (count_occ_In coord_point_dec) in HpIn. lia. }
    rewrite Hr in Hs1, Hs2.
    rewrite (Hkey l1 l2 b Hs1), (Hkey l1' l2' b' Hs2). reflexivity.
  - assert (HIn : In v r)
      by (rewrite Hs1; apply in_or_app; right; left; reflexivity).
    pose proof (core_vertex_count r p ps v Hr Hnd Hvp HIn) as Hcnt.
    assert (Hfree : forall (lA lB : list Point) (bb : Point),
              r = lA ++ v :: bb :: lB -> ~ In v lA).
    { intros lA lB bb HsA HIn'.
      apply (count_occ_In coord_point_dec) in HIn'.
      rewrite HsA, count_occ_app in Hcnt.
      rewrite count_occ_cons_eq in Hcnt by reflexivity.
      lia. }
    assert (Hs1' : l1 ++ v :: (b :: l2) = l1' ++ v :: (b' :: l2'))
      by congruence.
    destruct (split_unique_pref l1 l1' (b :: l2) (b' :: l2') v Hs1'
                (Hfree l1 l2 b Hs1) (Hfree l1' l2' b' Hs2)) as [Hpre _].
    exact Hpre.
Qed.

Lemma out_edge_count_le1 : forall (r : Ring) (v b : Point),
  ring_core_nodup r ->
  (count_occ edge_dec (ring_edges r) (v, b) <= 1)%nat.
Proof.
  intros r v b Hcore.
  pose proof Hcore as [p [ps [Hr Hnd]]].
  destruct (le_lt_dec (count_occ edge_dec (ring_edges r) (v, b)) 1)
    as [H | H]; [ exact H | exfalso ].
  destruct (count_occ_two_split (ring_edges r) (v, b) ltac:(lia))
    as [m1 [m2 [m3 Hm]]].
  destruct (ring_edges_split_pos r m1 (m2 ++ (v, b) :: m3) v b Hm)
    as [l1 [l2 [Hs1 Htail]]].
  destruct (ring_edges_split_pos (b :: l2) m2 m3 v b Htail)
    as [l1' [l2' [Hs2 _]]].
  assert (Hs2' : r = (l1 ++ v :: l1') ++ v :: b :: l2').
  { rewrite Hs1, Hs2. rewrite <- app_assoc. reflexivity. }
  pose proof (out_edge_prefix_unique r p ps b b v l1 l2
                (l1 ++ v :: l1') l2' Hr Hnd Hs1 Hs2') as Hpre.
  pose proof (f_equal (length (A := Point)) Hpre) as Hlen.
  rewrite length_app in Hlen. cbn in Hlen. lia.
Qed.

Lemma ho_count_one_out : forall (r : Ring) (W : Point) (v b : Point),
  ring_core_nodup r ->
  In (v, b) (ring_edges r) ->
  (forall g, In g (ring_edges r) ->
     (edge_crosses_ray_ho W g <-> g = (v, b))) ->
  ho_count W (ring_edges r) = 1%nat.
Proof.
  intros r W v b Hcore Hin Hiff.
  rewrite (ho_count_single W (ring_edges r) (v, b) Hiff).
  pose proof (out_edge_count_le1 r v b Hcore).
  pose proof (proj1 (count_occ_In edge_dec (ring_edges r) (v, b)) Hin).
  lia.
Qed.

(* ---------------------------------------------------------------------------
   §2  Crossing kernels at a corner-band point.
   --------------------------------------------------------------------------- *)

Lemma ho_count_zero_of_no_cross : forall (W : Point) (l : list Edge),
  (forall g, In g l -> ~ edge_crosses_ray_ho W g) ->
  ho_count W l = 0%nat.
Proof.
  intros W l Hno.
  induction l as [| e l IH]; [ reflexivity | ].
  cbn [ho_count].
  rewrite IH; [ | intros g Hg; apply Hno; right; exact Hg ].
  destruct (edge_crosses_ray_ho_dec W e) as [Hc | Hn]; [ | reflexivity ].
  exfalso. exact (Hno e (or_introl eq_refl) Hc).
Qed.

(* A non-incident edge never crosses a band point's ray near the eastmost
   vertex: the crossing abscissa is a convex combination of the endpoint
   abscissae (at most px vS), and the disk excludes the near range. *)
Lemma noncross_far : forall (r : Ring) (g : Edge) (vS W : Point) (rad : R),
  In g (ring_edges r) ->
  (forall w, In w r -> px w <= px vS) ->
  (forall x y, px vS - rad <= x <= px vS + rad ->
               py vS - rad <= y <= py vS + rad ->
     ~ (exists s : R, 0 <= s <= 1 /\
          x = (1 - s) * px (fst g) + s * px (snd g) /\
          y = (1 - s) * py (fst g) + s * py (snd g))) ->
  py vS - rad <= py W <= py vS + rad ->
  px vS - rad < px W ->
  ~ edge_crosses_ray_ho W g.
Proof.
  intros r g vS W rad Hing Hub Hdisk HyW HxW Hc.
  destruct g as [ga gb].
  destruct (ring_edges_endpoints_in r _ Hing) as [Hga Hgb];
    cbn [fst snd] in Hga, Hgb.
  pose proof (Hub ga Hga) as Hxa. pose proof (Hub gb Hgb) as Hxb.
  destruct Hc as [[Hband Hx] | [Hband Hx]].
  - set (s := (py W - py ga) / (py gb - py ga)).
    assert (Hs1 : s * (py gb - py ga) = py W - py ga)
      by (unfold s; field; lra).
    assert (Hsb : 0 <= s <= 1) by nra.
    assert (Hterm : px ga + (px gb - px ga) * (py W - py ga)
                      / (py gb - py ga)
                    = (1 - s) * px ga + s * px gb)
      by (unfold s; field; lra).
    rewrite Hterm in Hx.
    set (X := (1 - s) * px ga + s * px gb).
    assert (HXle : X <= px vS) by (unfold X; nra).
    assert (HXgt : px vS - rad < X) by (unfold X in *; lra).
    assert (HXdef : X = (1 - s) * px ga + s * px gb) by reflexivity.
    apply (Hdisk X (py W) ltac:(lra) ltac:(lra)).
    exists s. cbn [fst snd]. repeat split; nra.
  - set (s := (py W - py gb) / (py ga - py gb)).
    assert (Hs1 : s * (py ga - py gb) = py W - py gb)
      by (unfold s; field; lra).
    assert (Hsb : 0 <= s <= 1) by nra.
    assert (Hterm : px gb + (px ga - px gb) * (py W - py gb)
                      / (py ga - py gb)
                    = (1 - s) * px gb + s * px ga)
      by (unfold s; field; lra).
    rewrite Hterm in Hx.
    set (X := (1 - s) * px gb + s * px ga).
    assert (HXle : X <= px vS) by (unfold X; nra).
    assert (HXgt : px vS - rad < X) by (unfold X in *; lra).
    assert (HXdef : X = (1 - s) * px gb + s * px ga) by reflexivity.
    apply (Hdisk X (py W) ltac:(lra) ltac:(lra)).
    exists (1 - s). cbn [fst snd]. repeat split; nra.
Qed.

(* Incident edges whose span misses the band height never cross. *)
Lemma incident_above_nocross : forall (W : Point) (g : Edge),
  py W < py (fst g) -> py W < py (snd g) ->
  ~ edge_crosses_ray_ho W g.
Proof.
  intros W [ga gb] H1 H2 Hc. cbn [fst snd] in *.
  destruct Hc as [[Hband _] | [Hband _]]; lra.
Qed.

Lemma incident_below_nocross : forall (W : Point) (g : Edge),
  py (fst g) <= py W -> py (snd g) <= py W ->
  ~ edge_crosses_ray_ho W g.
Proof.
  intros W [ga gb] H1 H2 Hc. cbn [fst snd] in *.
  destruct Hc as [[Hband _] | [Hband _]]; lra.
Qed.

(* A carrier at or west of the point never crosses. *)
Lemma carrier_west_nocross : forall (W : Point) (g : Edge),
  py (fst g) <> py (snd g) ->
  edge_x_at g (py W) <= px W ->
  ~ edge_crosses_ray_ho W g.
Proof.
  intros W [ga gb] Hnh Hwest Hc. cbn [fst snd] in *.
  unfold edge_x_at in Hwest.
  destruct Hc as [[Hband Hx] | [Hband Hx]].
  - lra.
  - assert (Heq : px gb + (px ga - px gb) * (py W - py gb)
                    / (py ga - py gb)
                  = px ga + (px gb - px ga) * (py W - py ga)
                    / (py gb - py ga))
      by (field; lra).
    lra.
Qed.

(* A strictly straddling carrier strictly east always crosses. *)
Lemma carrier_east_cross : forall (W : Point) (g : Edge),
  (py (fst g) < py W < py (snd g) \/ py (snd g) < py W < py (fst g)) ->
  px W < edge_x_at g (py W) ->
  edge_crosses_ray_ho W g.
Proof.
  intros W [ga gb] Hstr Heast. cbn [fst snd] in *.
  unfold edge_x_at in Heast.
  destruct Hstr as [Hstr | Hstr].
  - left. split; [ lra | exact Heast ].
  - right. split; [ lra | ].
    assert (Heq : px gb + (px ga - px gb) * (py W - py gb)
                    / (py ga - py gb)
                  = px ga + (px gb - px ga) * (py W - py ga)
                    / (py gb - py ga))
      by (field; lra).
    lra.
Qed.

(* ---------------------------------------------------------------------------
   §3  The last clearance mirror: east corridor abutting a TOP vertex.
   --------------------------------------------------------------------------- *)

Theorem wall_corridor_clear_corner_east_top : forall (r : Ring) (e1 : Edge)
                                                     (v u : Point)
                                                     (ylo : R),
  ring_taut r ->
  In e1 (ring_edges r) ->
  e1 = (v, u) \/ e1 = (u, v) ->
  py v < py u ->
  py v < ylo ->
  ylo <= py u ->
  corner_opens_west_top r e1 u ->
  exists delta0, 0 < delta0 /\
    forall delta, 0 < delta < delta0 ->
      forall y, ylo <= y < py u ->
        ~ ring_image r (mkPoint (edge_x_at e1 y + delta) y).
Proof.
  intros r e1 v u ylo Htaut Hin Hor Hvu Hlo Hhi Hopen.
  destruct e1 as [ea eb].
  assert (Hnh : py ea <> py eb)
    by (destruct Hor as [He | He]; inversion He; subst; cbn; lra).
  set (r' := map ymir r).
  set (e1' := (ymir ea, ymir eb)).
  assert (Htaut' : ring_taut r') by (apply ring_taut_ymir; exact Htaut).
  assert (Hin' : In e1' (ring_edges r')).
  { unfold r'. rewrite ring_edges_map.
    exact (in_map (fun e0 => (ymir (fst e0), ymir (snd e0)))
             (ring_edges r) (ea, eb) Hin). }
  assert (Hor' : e1' = (ymir u, ymir v) \/ e1' = (ymir v, ymir u)).
  { destruct Hor as [He | He]; inversion He; subst; [ right | left ];
      reflexivity. }
  assert (Hopen' : corner_opens_west r' e1' (ymir u)).
  { intros g' Hing' Hinc'.
    unfold r' in Hing'. rewrite ring_edges_map in Hing'.
    apply in_map_iff in Hing'. destruct Hing' as [g [Hgeq Hing]].
    subst g'. cbn [fst snd] in *.
    assert (Hinc : fst g = u \/ snd g = u).
    { destruct Hinc' as [H | H]; [ left | right ]; apply ymir_inj; exact H. }
    destruct (Hopen g Hing Hinc) as [HA HB].
    split.
    - intro Hyy.
      assert (Hyy' : py (fst g) <= py u)
        by (unfold ymir in Hyy; cbn [py] in Hyy; lra).
      specialize (HA Hyy').
      unfold e1'.
      replace (py (ymir (fst g))) with (- py (fst g))
        by (unfold ymir; cbn [py]; reflexivity).
      rewrite (edge_x_at_ymir ea eb (py (fst g)) Hnh).
      replace (px (ymir (fst g))) with (px (fst g))
        by (unfold ymir; cbn [px]; reflexivity).
      exact HA.
    - intro Hyy.
      assert (Hyy' : py (snd g) <= py u)
        by (unfold ymir in Hyy; cbn [py] in Hyy; lra).
      specialize (HB Hyy').
      unfold e1'.
      replace (py (ymir (snd g))) with (- py (snd g))
        by (unfold ymir; cbn [py]; reflexivity).
      rewrite (edge_x_at_ymir ea eb (py (snd g)) Hnh).
      replace (px (ymir (snd g))) with (px (snd g))
        by (unfold ymir; cbn [px]; reflexivity).
      exact HB. }
  destruct (wall_corridor_clear_corner_east r' e1' (ymir u) (ymir v)
              (- ylo) Htaut' Hin' Hor'
              ltac:(unfold ymir; cbn [py]; lra)
              ltac:(unfold ymir; cbn [py]; lra)
              ltac:(unfold ymir; cbn [py]; lra)
              Hopen') as [delta0 [Hd0 Hfree]].
  exists delta0. split; [ exact Hd0 | ].
  intros delta Hd y Hy Himg.
  apply (Hfree delta Hd (- y) ltac:(unfold ymir; cbn [py]; lra)).
  assert (HptEq : mkPoint (edge_x_at e1' (- y) + delta) (- y)
                    = ymir (mkPoint (edge_x_at (ea, eb) y + delta) y)).
  { unfold e1'.
    rewrite (edge_x_at_ymir ea eb y Hnh).
    unfold ymir; cbn [px py]. reflexivity. }
  rewrite HptEq.
  apply (ring_image_ymir r _). exact Himg.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions ho_count_one_out.
Print Assumptions noncross_far.
Print Assumptions carrier_east_cross.
Print Assumptions wall_corridor_clear_corner_east_top.
