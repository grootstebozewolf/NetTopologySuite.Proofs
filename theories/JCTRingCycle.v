(* ============================================================================
   NetTopologySuite.Proofs.JCTRingCycle
   ----------------------------------------------------------------------------
   ESCAPE DESCENT, rung 5c-5: THE RING-CYCLE STRUCTURE.  The traversal
   walks the edge cycle corner by corner; this rung supplies the pure list
   combinatorics it consumes -- no new geometry.

   A PROPER ring (`ring_core_nodup`): r = p :: ps ++ [p] with NoDup
   (p :: ps) -- closed, with distinct core vertices.  Then:

     - `ring_edges_in_split`: edge membership IS list splitting
       (In (a,b) (ring_edges l) <-> l = l1 ++ a :: b :: l2);
     - `in_edge_unique` / `out_edge_unique`: each vertex has at most one
       incoming and one outgoing edge (count_occ on the unique core
       occurrence; the seam vertex p needs its own analysis: its in-edge
       ends at the closing copy, its out-edge starts at the head);
     - `incident_two`: every edge incident at v is THE in-edge or THE
       out-edge -- the lemma that discharges the corner conditions'
       "forall incident g" against the two cycle neighbours;
     - `cyclic_next` / `cyclic_prev`: the cycle successor and predecessor
       exist for every edge (closedness wraps the seam).

   Also here, the traversal's terminal-count tools sharpened:
   `vertex_xmax_achieved` (a maximal-abscissa vertex exists) and
   `ho_count_zero_east_ub` (any point weakly east of ALL vertices has
   crossing count zero -- the `xsup`-free form of rung 5c-1's terminal
   count, immune to the empty-fold base value).

   Pure lists + R order; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

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
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §0  Small list kit.
   --------------------------------------------------------------------------- *)

Lemma last_snoc : forall (l : list Point) (x d : Point),
  last (l ++ [x]) d = x.
Proof.
  induction l as [| a l IH]; intros x d; [ reflexivity | ].
  cbn [app last].
  destruct (l ++ [x]) eqn:Hl.
  - destruct l; discriminate.
  - rewrite <- Hl. apply IH.
Qed.

Lemma last_app_nonempty : forall (l l' : list Point) (d : Point),
  l' <> [] -> last (l ++ l') d = last l' d.
Proof.
  induction l as [| x l IH]; intros l' d Hne; [ reflexivity | ].
  cbn [app last].
  destruct (l ++ l') eqn:Hl.
  - destruct l; cbn in Hl; [ congruence | discriminate ].
  - rewrite <- Hl. apply IH. exact Hne.
Qed.

Lemma last_In : forall (l : list Point) (d : Point),
  l <> [] -> In (last l d) l.
Proof.
  induction l as [| x l IH]; intros d Hne; [ congruence | ].
  destruct l as [| y l'].
  - left. reflexivity.
  - cbn [last]. right. apply IH. discriminate.
Qed.

Lemma split_unique_pref : forall (l1 : list Point) (l1' l2 l2' : list Point)
                                 (v : Point),
  l1 ++ v :: l2 = l1' ++ v :: l2' ->
  ~ In v l1 -> ~ In v l1' ->
  l1 = l1' /\ l2 = l2'.
Proof.
  induction l1 as [| x l1 IH]; intros l1' l2 l2' v Heq H1 H1'.
  - destruct l1' as [| x' l1'].
    + cbn in Heq. injection Heq as He. auto.
    + cbn in Heq. injection Heq as Hx He.
      exfalso. apply H1'. left. exact (eq_sym Hx).
  - destruct l1' as [| x' l1'].
    + cbn in Heq. injection Heq as Hx He.
      exfalso. apply H1. left. exact Hx.
    + cbn in Heq. injection Heq as Hx He. subst x'.
      destruct (IH l1' l2 l2' v He
                  ltac:(intro Hc; apply H1; right; exact Hc)
                  ltac:(intro Hc; apply H1'; right; exact Hc)) as [Ha Hb].
      subst. auto.
Qed.

(* ---------------------------------------------------------------------------
   §1  Edge membership is list splitting.
   --------------------------------------------------------------------------- *)

Lemma ring_edges_in_split : forall (l : list Point) (a b : Point),
  In (a, b) (ring_edges l) <-> exists l1 l2, l = l1 ++ a :: b :: l2.
Proof.
  intros l a b; split.
  - induction l as [| x l IH]; [ cbn; intros [] | ].
    cbn [ring_edges]. destruct l as [| y l'].
    + intros [].
    + intros [He | Hin].
      * injection He as H1 H2. subst. exists [], l'. reflexivity.
      * destruct (IH Hin) as [l1 [l2 Hsplit]].
        exists (x :: l1), l2. rewrite Hsplit. reflexivity.
  - intros [l1 [l2 Hsplit]]. subst l.
    induction l1 as [| x l1 IH].
    + cbn. left. reflexivity.
    + cbn [app].
      destruct (l1 ++ a :: b :: l2) eqn:Hl;
        [ destruct l1; discriminate | ].
      cbn [ring_edges].
      apply in_cons. exact IH.
Qed.

(* ---------------------------------------------------------------------------
   §2  The proper-ring predicate and the degree-2 lemmas.
   --------------------------------------------------------------------------- *)

(* Closed with pairwise-distinct core vertices. *)
Definition ring_core_nodup (r : Ring) : Prop :=
  exists (p : Point) (ps : list Point),
    r = p :: ps ++ [p] /\ NoDup (p :: ps).

Lemma ring_core_nodup_closed : forall r, ring_core_nodup r -> ring_closed r.
Proof.
  intros r [p [ps [Hr _]]]. exists p, ps. exact Hr.
Qed.

(* The single-occurrence count of a non-seam vertex. *)
Lemma core_vertex_count : forall (r : Ring) (p : Point) (ps : list Point)
                                 (v : Point),
  r = p :: ps ++ [p] ->
  NoDup (p :: ps) ->
  v <> p ->
  In v r ->
  (count_occ coord_point_dec r v = 1)%nat.
Proof.
  intros r p ps v Hr Hnd Hvp HIn.
  apply NoDup_cons_iff in Hnd. destruct Hnd as [Hp Hndps].
  assert (HInps : In v ps).
  { rewrite Hr in HIn. destruct HIn as [He | HIn]; [ congruence | ].
    apply in_app_or in HIn.
    destruct HIn as [HIn | [He | []]]; [ exact HIn | congruence ]. }
  rewrite Hr. cbn [count_occ].
  destruct (coord_point_dec p v) as [Hc | _]; [ congruence | ].
  rewrite count_occ_app. cbn [count_occ].
  destruct (coord_point_dec p v) as [Hc | _]; [ congruence | ].
  pose proof (proj1 (NoDup_count_occ coord_point_dec ps) Hndps v).
  pose proof (proj1 (count_occ_In coord_point_dec ps v) HInps).
  lia.
Qed.

(* Every vertex has at most one INCOMING edge. *)
Lemma in_edge_unique : forall (r : Ring) (a a' v : Point),
  ring_core_nodup r ->
  In (a, v) (ring_edges r) ->
  In (a', v) (ring_edges r) ->
  a = a'.
Proof.
  intros r a a' v Hcore H1 H2.
  pose proof Hcore as [p [ps [Hr Hnd]]].
  pose proof Hnd as Hnd'. apply NoDup_cons_iff in Hnd'.
  destruct Hnd' as [Hp Hndps].
  apply ring_edges_in_split in H1, H2.
  destruct H1 as [l1 [l2 Hs1]]. destruct H2 as [l1' [l2' Hs2]].
  destruct (coord_point_dec v p) as [Hvp | Hvp].
  - subst v.
    (* any in-edge of the seam vertex satisfies lA ++ [aa] = p :: ps *)
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
    assert (Heq : l1 ++ [a] = l1' ++ [a']) by congruence.
    apply app_inj_tail in Heq. destruct Heq as [_ Ha]. exact Ha.
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
    apply app_inj_tail in Hpre. destruct Hpre as [_ Ha]. exact Ha.
Qed.

(* Every vertex has at most one OUTGOING edge. *)
Lemma out_edge_unique : forall (r : Ring) (b b' v : Point),
  ring_core_nodup r ->
  In (v, b) (ring_edges r) ->
  In (v, b') (ring_edges r) ->
  b = b'.
Proof.
  intros r b b' v Hcore H1 H2.
  pose proof Hcore as [p [ps [Hr Hnd]]].
  pose proof Hnd as Hnd'. apply NoDup_cons_iff in Hnd'.
  destruct Hnd' as [Hp Hndps].
  apply ring_edges_in_split in H1, H2.
  destruct H1 as [l1 [l2 Hs1]]. destruct H2 as [l1' [l2' Hs2]].
  destruct (coord_point_dec v p) as [Hvp | Hvp].
  - subst v.
    (* the seam's out-edge starts at the head: the prefix must be empty *)
    assert (Hkey : forall (lA lB : list Point) (bb : Point),
              p :: ps ++ [p] = lA ++ p :: bb :: lB ->
              bb :: lB = ps ++ [p]).
    { intros lA lB bb HsA.
      destruct lA as [| x lAc].
      + cbn in HsA. injection HsA as Htail. exact (eq_sym Htail).
      + cbn in HsA. injection HsA as Hxp Htail. subst x.
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
    pose proof (Hkey l1 l2 b Hs1) as Hk1.
    pose proof (Hkey l1' l2' b' Hs2) as Hk2.
    assert (Heq : b :: l2 = b' :: l2') by congruence.
    injection Heq as Hb _. exact Hb.
  - assert (HIn : In v r)
      by (rewrite Hs1; apply in_or_app; right; left; reflexivity).
    pose proof (core_vertex_count r p ps v Hr Hnd Hvp HIn) as Hcnt.
    assert (Hfree : forall (lA lB : list Point) (bb : Point),
              r = lA ++ v :: bb :: lB -> ~ In v lA).
    { intros lA lB bb HsA HIn'.
      apply (count_occ_In coord_point_dec) in HIn'.
      rewrite HsA in Hcnt.
      rewrite count_occ_app in Hcnt.
      rewrite count_occ_cons_eq in Hcnt by reflexivity.
      lia. }
    assert (Hs1' : l1 ++ v :: (b :: l2) = l1' ++ v :: (b' :: l2'))
      by congruence.
    destruct (split_unique_pref l1 l1' (b :: l2) (b' :: l2') v Hs1'
                (Hfree l1 l2 b Hs1) (Hfree l1' l2' b' Hs2)) as [_ Hsuf].
    injection Hsuf as Hb _. exact Hb.
Qed.

(* THE DEGREE-2 LEMMA: every edge incident at v is the in-edge or the
   out-edge -- discharging the corner conditions against the two cycle
   neighbours. *)
Lemma incident_two : forall (r : Ring) (e f g : Edge) (v : Point),
  ring_core_nodup r ->
  In e (ring_edges r) -> snd e = v ->
  In f (ring_edges r) -> fst f = v ->
  In g (ring_edges r) -> fst g = v \/ snd g = v ->
  g = e \/ g = f.
Proof.
  intros r [e1 e2] [f1 f2] [g1 g2] v Hnd Hine Hsnde Hinf Hfstf Hing Hinc.
  cbn [fst snd] in *.
  destruct Hinc as [Hg | Hg].
  - right. subst g1 f1.
    rewrite (out_edge_unique r g2 f2 v Hnd Hing Hinf). reflexivity.
  - left. subst g2 e2.
    rewrite (in_edge_unique r g1 e1 v Hnd Hing Hine). reflexivity.
Qed.

(* ---------------------------------------------------------------------------
   §3  The cycle successor and predecessor.
   --------------------------------------------------------------------------- *)

Lemma cyclic_next : forall (r : Ring) (e : Edge),
  ring_closed r ->
  In e (ring_edges r) ->
  exists f, In f (ring_edges r) /\ fst f = snd e.
Proof.
  intros r [a b] [p [ps Hr]] Hin. cbn [fst snd].
  apply ring_edges_in_split in Hin. destruct Hin as [l1 [l2 Hs]].
  destruct l2 as [| c l2'].
  - assert (Hbp : b = p).
    { assert (Hl1 : last r p = b).
      { rewrite Hs.
        replace (l1 ++ [a; b]) with ((l1 ++ [a]) ++ [b])
          by (rewrite <- app_assoc; reflexivity).
        apply last_snoc. }
      assert (Hl2 : last r p = p).
      { rewrite Hr. cbn [last].
        destruct (ps ++ [p]) eqn:Hl; [ destruct ps; discriminate | ].
        rewrite <- Hl. apply last_snoc. }
      congruence. }
    subst b.
    destruct ps as [| q ps'].
    + exists (p, p). split; [ | reflexivity ].
      rewrite Hr. cbn. left. reflexivity.
    + exists (p, q). split; [ | reflexivity ].
      apply ring_edges_in_split. exists [], (ps' ++ [p]).
      rewrite Hr. reflexivity.
  - exists (b, c). split; [ | reflexivity ].
    apply ring_edges_in_split. exists (l1 ++ [a]), l2'.
    rewrite Hs, <- app_assoc. reflexivity.
Qed.

Lemma cyclic_prev : forall (r : Ring) (e : Edge),
  ring_closed r ->
  In e (ring_edges r) ->
  exists f, In f (ring_edges r) /\ snd f = fst e.
Proof.
  intros r [a b] [p [ps Hr]] Hin. cbn [fst snd].
  apply ring_edges_in_split in Hin. destruct Hin as [l1 [l2 Hs]].
  destruct l1 as [| x l1c].
  - assert (Hap : a = p) by (rewrite Hr in Hs; cbn in Hs; congruence).
    subst a.
    exists (last (p :: ps) p, p). split; [ | reflexivity ].
    apply ring_edges_in_split.
    set (RL := removelast (p :: ps)). set (L := last (p :: ps) p).
    exists RL, [].
    rewrite Hr.
    assert (Hrl : p :: ps = RL ++ [L])
      by (unfold RL, L; apply app_removelast_last; discriminate).
    change (p :: ps ++ [p]) with ((p :: ps) ++ [p]).
    rewrite Hrl. rewrite <- app_assoc. reflexivity.
  - destruct (exists_last (l := x :: l1c) ltac:(discriminate))
      as [l1'' [z Hz]].
    exists (z, a). split; [ | reflexivity ].
    apply ring_edges_in_split. exists l1'', (b :: l2).
    rewrite Hs, Hz, <- app_assoc. reflexivity.
Qed.

(* ---------------------------------------------------------------------------
   §4  The achieved eastmost vertex and the sharpened terminal count.
   --------------------------------------------------------------------------- *)

Lemma vertex_xmax_achieved : forall (l : list Point),
  l <> [] ->
  exists v, In v l /\ forall w, In w l -> px w <= px v.
Proof.
  induction l as [| x l IH]; intros Hne; [ congruence | ].
  destruct l as [| y l'].
  - exists x. split; [ left; reflexivity | ].
    intros w [Hw | []]. subst. lra.
  - destruct (IH ltac:(discriminate)) as [m [Hm Hmax]].
    destruct (Rle_dec (px x) (px m)) as [Hle | Hgt].
    + exists m. split; [ right; exact Hm | ].
      intros w [Hw | Hw]; [ subst; lra | exact (Hmax w Hw) ].
    + exists x. split; [ left; reflexivity | ].
      intros w [Hw | Hw]; [ subst; lra | ].
      pose proof (Hmax w Hw). lra.
Qed.

(* The xsup-free terminal count: weakly east of EVERY vertex, the
   eastward ray crosses nothing. *)
Lemma ho_cross_east_none_ub : forall (r : Ring) (q : Point) (a b : Point),
  In (a, b) (ring_edges r) ->
  (forall vt, In vt r -> px vt <= px q) ->
  ~ edge_crosses_ray_ho q (a, b).
Proof.
  intros r q a b Hin Hub Hc.
  destruct (ring_edges_endpoints_in r _ Hin) as [Ha Hb];
    cbn [fst snd] in Ha, Hb.
  pose proof (Hub a Ha) as Hxa.
  pose proof (Hub b Hb) as Hxb.
  destruct Hc as [[Hband Hx] | [Hband Hx]].
  - set (t := (py q - py a) / (py b - py a)).
    assert (Ht1 : t * (py b - py a) = py q - py a)
      by (unfold t; field; lra).
    assert (Htb : 0 <= t <= 1) by nra.
    assert (Hterm : px a + (px b - px a) * (py q - py a) / (py b - py a)
                      = (1 - t) * px a + t * px b)
      by (unfold t; field; lra).
    rewrite Hterm in Hx. nra.
  - set (t := (py q - py b) / (py a - py b)).
    assert (Ht1 : t * (py a - py b) = py q - py b)
      by (unfold t; field; lra).
    assert (Htb : 0 <= t <= 1) by nra.
    assert (Hterm : px b + (px a - px b) * (py q - py b) / (py a - py b)
                      = (1 - t) * px b + t * px a)
      by (unfold t; field; lra).
    rewrite Hterm in Hx. nra.
Qed.

Lemma ho_count_zero_east_ub : forall (r : Ring) (q : Point),
  (forall vt, In vt r -> px vt <= px q) ->
  ho_count q (ring_edges r) = 0%nat.
Proof.
  intros r q Hub.
  assert (Hsub : forall l, (forall e, In e l -> In e (ring_edges r)) ->
            ho_count q l = 0%nat).
  { induction l as [| e l' IH]; intros Hsubl; [ reflexivity | ].
    cbn [ho_count].
    rewrite IH; [ | intros e' He'; apply Hsubl; right; exact He' ].
    destruct (edge_crosses_ray_ho_dec q e) as [Hc | Hn]; [ | reflexivity ].
    exfalso. destruct e as [a b].
    exact (ho_cross_east_none_ub r q a b
             (Hsubl (a, b) (or_introl eq_refl)) Hub Hc). }
  apply Hsub. intros e He. exact He.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions ring_edges_in_split.
Print Assumptions incident_two.
Print Assumptions cyclic_next.
Print Assumptions ho_count_zero_east_ub.
