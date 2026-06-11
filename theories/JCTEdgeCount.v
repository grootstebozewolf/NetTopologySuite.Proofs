(* ============================================================================
   NetTopologySuite.Proofs.JCTEdgeCount
   ----------------------------------------------------------------------------
   ESCAPE DESCENT, rung 5c-15: EDGE-ENTRY COUNTING.  `ho_count` folds over
   the ring's edge LIST, so the payoff's "exactly one crossing" needs that
   the crossing pair occurs exactly ONCE as a list entry.  In a proper
   ring it does: the in-edge (and out-edge) at a vertex sits at a unique
   list position (`in_edge_prefix_unique` / `out_edge_prefix_unique`, the
   positional strengthenings of rung 5c-5's uniqueness lemmas), so a
   double entry would force a prefix to equal a strictly longer prefix
   (`in_edge_count_le1`, `out_edge_count_le1` -- killed by lengths).

   `ho_count_single` then converts "the crossing edges are exactly the
   entries equal to gc" into `ho_count = count_occ ... gc`, and
   `ho_count_one_in` / `ho_count_one_out` package the payoff's odd case:
   the count is exactly 1.

   Pure lists; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

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
From NTS.Proofs Require Import JCTCornerDispatch JCTHugCycle.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §0  Edge equality is decidable.
   --------------------------------------------------------------------------- *)

Lemma edge_dec : forall e f : Edge, {e = f} + {e <> f}.
Proof.
  intros [ea eb] [fa fb].
  destruct (coord_point_dec ea fa) as [H1 | H1].
  - destruct (coord_point_dec eb fb) as [H2 | H2].
    + left. subst. reflexivity.
    + right. intro He. injection He as Ha Hb. exact (H2 Hb).
  - right. intro He. injection He as Ha Hb. exact (H1 Ha).
Qed.

(* ---------------------------------------------------------------------------
   §1  Positional splits and prefix uniqueness.
   --------------------------------------------------------------------------- *)

(* An occurrence of (a,b) inside the edge list locates a vertex split,
   with the remaining edge tail tracked. *)
Lemma ring_edges_split_pos : forall (l : list Point) (m1 m2 : list Edge)
                                    (a b : Point),
  ring_edges l = m1 ++ (a, b) :: m2 ->
  exists l1 l2, l = l1 ++ a :: b :: l2 /\ ring_edges (b :: l2) = m2.
Proof.
  intros l m1. revert l.
  induction m1 as [| e0 m1 IH]; intros l m2 a b He.
  - destruct l as [| x l']; [ discriminate | ].
    destruct l' as [| y l'']; [ discriminate | ].
    cbn [ring_edges app] in He. injection He as Hx Hy Hm. subst.
    exists [], l''. split; reflexivity.
  - destruct l as [| x l']; [ discriminate | ].
    destruct l' as [| y l'']; [ discriminate | ].
    cbn [ring_edges] in He. injection He as H1 H2.
    destruct (IH (y :: l'') m2 a b H2) as [l1 [l2 [Hs Hm]]].
    exists (x :: l1), l2. split; [ | exact Hm ].
    cbn [app]. rewrite <- Hs. reflexivity.
Qed.

(* The positional strengthening of in_edge_unique: any two splits at an
   incoming edge of v share the same prefix-with-source. *)
Lemma in_edge_prefix_unique : forall (r : Ring) (p : Point)
                                     (ps : list Point)
                                     (a a' v : Point)
                                     (l1 l2 l1' l2' : list Point),
  r = p :: ps ++ [p] ->
  NoDup (p :: ps) ->
  r = l1 ++ a :: v :: l2 ->
  r = l1' ++ a' :: v :: l2' ->
  l1 ++ [a] = l1' ++ [a'].
Proof.
  intros r p ps a a' v l1 l2 l1' l2' Hr Hnd Hs1 Hs2.
  pose proof Hnd as Hnd'. apply NoDup_cons_iff in Hnd'.
  destruct Hnd' as [Hp Hndps].
  destruct (coord_point_dec v p) as [Hvp | Hvp].
  - subst v.
    assert (Hkey : forall (lA lB : list Point) (aa : Point),
              p :: ps ++ [p] = lA ++ aa :: p :: lB ->
              lA ++ [aa] = p :: ps).
    { intros lA lB aa HsA.
      destruct lA as [| x lAc].
      + cbn in HsA. injection HsA as Hap Htail. subst aa.
        destruct ps as [| q ps'].
        * cbn. reflexivity.
        * cbn in Htail. injection Htail as Hqp _.
          exfalso. apply Hp. left. exact Hqp.
      + cbn in HsA. injection HsA as Hxp Htail. subst x.
        assert (Hcnt : (count_occ coord_point_dec (ps ++ [p]) p = 1)%nat).
        { rewrite count_occ_app. cbn [count_occ].
          destruct (coord_point_dec p p) as [_ | Hc]; [ | congruence ].
          pose proof (proj1 (count_occ_not_In coord_point_dec ps p) Hp).
          lia. }
        rewrite Htail in Hcnt.
        replace (lAc ++ aa :: p :: lB)
          with ((lAc ++ [aa]) ++ p :: lB) in Hcnt
          by (rewrite <- app_assoc; reflexivity).
        rewrite count_occ_app in Hcnt.
        rewrite count_occ_cons_eq in Hcnt by reflexivity.
        assert (HcA1 : ~ In p (lAc ++ [aa]))
          by (intro HIn; apply (count_occ_In coord_point_dec) in HIn; lia).
        assert (Htail' : (lAc ++ [aa]) ++ p :: lB = ps ++ p :: []).
        { rewrite <- app_assoc. cbn [app]. rewrite <- Htail. reflexivity. }
        destruct (split_unique_pref (lAc ++ [aa]) ps lB [] p Htail'
                    HcA1 Hp) as [Hpref _].
        rewrite <- Hpref. cbn [app]. reflexivity. }
    rewrite Hr in Hs1, Hs2.
    pose proof (Hkey l1 l2 a Hs1) as Hk1.
    pose proof (Hkey l1' l2' a' Hs2) as Hk2.
    congruence.
  - assert (HIn : In v r)
      by (rewrite Hs1; apply in_or_app; right; right; left; reflexivity).
    pose proof (core_vertex_count r p ps v Hr Hnd Hvp HIn) as Hcnt.
    assert (Hfree : forall (lA lB : list Point) (aa : Point),
              r = lA ++ aa :: v :: lB -> ~ In v (lA ++ [aa])).
    { intros lA lB aa HsA HIn'.
      apply (count_occ_In coord_point_dec) in HIn'.
      rewrite HsA in Hcnt.
      replace (lA ++ aa :: v :: lB) with ((lA ++ [aa]) ++ v :: lB) in Hcnt
        by (rewrite <- app_assoc; reflexivity).
      rewrite count_occ_app in Hcnt.
      rewrite count_occ_cons_eq in Hcnt by reflexivity.
      lia. }
    assert (Hs1' : (l1 ++ [a]) ++ v :: l2 = (l1' ++ [a']) ++ v :: l2').
    { rewrite <- !app_assoc. cbn [app]. congruence. }
    destruct (split_unique_pref (l1 ++ [a]) (l1' ++ [a']) l2 l2' v Hs1'
                (Hfree l1 l2 a Hs1) (Hfree l1' l2' a' Hs2)) as [Hpre _].
    exact Hpre.
Qed.

(* ---------------------------------------------------------------------------
   §2  Each in-edge occurs at most once as a list entry.
   --------------------------------------------------------------------------- *)

(* count >= 2 yields a double decomposition. *)
Lemma count_occ_two_split : forall (l : list Edge) (x : Edge),
  (2 <= count_occ edge_dec l x)%nat ->
  exists m1 m2 m3, l = m1 ++ x :: m2 ++ x :: m3.
Proof.
  induction l as [| e l IH]; intros x Hc; cbn [count_occ] in Hc.
  - lia.
  - destruct (edge_dec e x) as [He | He].
    + subst e.
      assert (Hc1 : (1 <= count_occ edge_dec l x)%nat) by lia.
      apply (count_occ_In edge_dec) in Hc1.
      apply in_split in Hc1. destruct Hc1 as [m2 [m3 Hl]].
      exists [], m2, m3. rewrite Hl. reflexivity.
    + destruct (IH x Hc) as [m1 [m2 [m3 Hl]]].
      exists (e :: m1), m2, m3. rewrite Hl. reflexivity.
Qed.

Lemma in_edge_count_le1 : forall (r : Ring) (a v : Point),
  ring_core_nodup r ->
  (count_occ edge_dec (ring_edges r) (a, v) <= 1)%nat.
Proof.
  intros r a v Hcore.
  pose proof Hcore as [p [ps [Hr Hnd]]].
  destruct (le_lt_dec (count_occ edge_dec (ring_edges r) (a, v)) 1)
    as [H | H]; [ exact H | exfalso ].
  destruct (count_occ_two_split (ring_edges r) (a, v) ltac:(lia))
    as [m1 [m2 [m3 Hm]]].
  destruct (ring_edges_split_pos r m1 (m2 ++ (a, v) :: m3) a v Hm)
    as [l1 [l2 [Hs1 Htail]]].
  destruct (ring_edges_split_pos (v :: l2) m2 m3 a v Htail)
    as [l1' [l2' [Hs2 _]]].
  (* the second occurrence rewrites r with a strictly longer prefix *)
  assert (Hs2' : r = (l1 ++ a :: l1') ++ a :: v :: l2').
  { rewrite Hs1, Hs2.
    rewrite <- app_assoc. reflexivity. }
  pose proof (in_edge_prefix_unique r p ps a a v l1 l2
                (l1 ++ a :: l1') l2' Hr Hnd Hs1 Hs2') as Hpre.
  assert (Hlen : length (l1 ++ [a]) = length ((l1 ++ a :: l1') ++ [a]))
    by (rewrite Hpre; reflexivity).
  rewrite !length_app in Hlen. cbn in Hlen. lia.
Qed.

(* ---------------------------------------------------------------------------
   §3  The exactly-one-crossing count.
   --------------------------------------------------------------------------- *)

Lemma ho_count_single : forall (W : Point) (l : list Edge) (gc : Edge),
  (forall g, In g l -> (edge_crosses_ray_ho W g <-> g = gc)) ->
  ho_count W l = count_occ edge_dec l gc.
Proof.
  intros W l gc Hiff.
  induction l as [| e l IH]; [ reflexivity | ].
  cbn [ho_count count_occ].
  rewrite IH; [ | intros g Hg; apply Hiff; right; exact Hg ].
  destruct (edge_crosses_ray_ho_dec W e) as [Hc | Hn];
  destruct (edge_dec e gc) as [He | He]; try reflexivity.
  - exfalso. apply He. exact (proj1 (Hiff e (or_introl eq_refl)) Hc).
  - exfalso. apply Hn. exact (proj2 (Hiff e (or_introl eq_refl)) He).
Qed.

(* THE PAYOFF COUNT: if the crossing edges are exactly the entries equal
   to the in-edge (a, v), the count is exactly one. *)
Lemma ho_count_one_in : forall (r : Ring) (W : Point) (a v : Point),
  ring_core_nodup r ->
  In (a, v) (ring_edges r) ->
  (forall g, In g (ring_edges r) ->
     (edge_crosses_ray_ho W g <-> g = (a, v))) ->
  ho_count W (ring_edges r) = 1%nat.
Proof.
  intros r W a v Hcore Hin Hiff.
  rewrite (ho_count_single W (ring_edges r) (a, v) Hiff).
  pose proof (in_edge_count_le1 r a v Hcore).
  pose proof (proj1 (count_occ_In edge_dec (ring_edges r) (a, v)) Hin).
  lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions ring_edges_split_pos.
Print Assumptions in_edge_count_le1.
Print Assumptions ho_count_one_in.
