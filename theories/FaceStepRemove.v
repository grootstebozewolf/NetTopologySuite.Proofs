(* ==========================================================================
   FaceStepRemove.v

   extract_rings_valid R5 / H_bridge Euler route, Rung 3b-xv: the POINTWISE
   SURGERY description of the face step `fstep` under deleting an edge.

   Composes `ArrangementEMinus.fstep_E_minus_eq_away` (fstep unchanged away from
   the endpoints) with `DartNextRemove.next_remove` (the next-reroute at a fan)
   into the exact form of `fstep (darts_of (E_minus E d))`:

     deleting `d` removes the darts `d`, `twin d`; the face-predecessor of `d`
     reroutes to `fstep (twin d)`, the face-predecessor of `twin d` reroutes to
     `fstep d`, and every other dart keeps its face step.

   This is the precise input the (subsequent, harder) generic cycle-count
   argument consumes to prove `num_faces (E_minus E d) = num_faces E`.  Same-face
   is NOT needed here -- only for that cycle-count conclusion.

   Stated in the well-noded bridge setting `In d E /\ ~ In (twin d) E` (as
   `EdgeFaceBridge.same_face_twin_disconnect`): `E_minus` filters only the
   `E`-part of `darts_of E = E ++ map twin E`, so the fan at `dbase d` loses
   exactly `d` only when `twin d ∉ E`.

   Pure dart/angular combinatorics; no `Admitted` / `Axiom` / `Parameter`;
   allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay OverlayGraph Dart DartNext
                               DartNextSpec DartFace DartNextRemove
                               EdgeConnectivity ArrangementEMinus.

Import ListNotations.

Lemma fstep_E_minus_splice : forall (E : list Edge) (d x : Dart),
  (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
  In d E -> ~ In (twin d) E ->
  dbase d <> dtip d ->
  In x (darts_of (E_minus E d)) ->
  fstep (darts_of (E_minus E d)) x =
    (if dart_eq_dec (fstep (darts_of E) x) d then fstep (darts_of E) (twin d)
     else if dart_eq_dec (fstep (darts_of E) x) (twin d) then fstep (darts_of E) d
     else fstep (darts_of E) x).
Proof.
  intros E d x Hfan Hd Hndtw Hprop Hx.
  (* membership / twin algebra for x *)
  assert (HxE : In x (darts_of E)) by (apply (incl_darts_of_E_minus E d); exact Hx).
  assert (HtwxE : In (twin x) (darts_of E)) by (apply darts_of_closed_under_twin; exact HxE).
  pose proof (proj1 (in_darts_of_E_minus_iff E d x Hndtw) Hx) as Hxdec.
  destruct Hxdec as [_ [Hxne_d Hxne_td]].
  assert (Htwxd : twin x <> d).
  { intro H. apply Hxne_td. apply (f_equal twin) in H.
    rewrite twin_involutive in H. exact H. }
  assert (Htwx_twd : twin x <> twin d).
  { intro H. apply Hxne_d. apply (f_equal twin) in H.
    rewrite !twin_involutive in H. exact H. }
  (* fstep (darts_of E) x is based at dtip x *)
  assert (Htwx_out : In (twin x) (outgoing (dtip x) (darts_of E))).
  { apply in_outgoing. split; [ exact HtwxE | rewrite dbase_twin; reflexivity ]. }
  assert (Hbase : dbase (fstep (darts_of E) x) = dtip x).
  { unfold fstep. apply (next_base (dtip x) (darts_of E) (twin x) Htwx_out). }
  (* reduced-fan membership at the two endpoint vertices *)
  assert (HmemF : forall y, In y (outgoing (dbase d) (darts_of (E_minus E d))) <->
                            (In y (outgoing (dbase d) (darts_of E)) /\ y <> d)).
  { intro y. rewrite (in_outgoing_darts_of_E_minus E d (dbase d) y Hndtw). split.
    - intros [Hy1 [Hy2 _]]. split; [ exact Hy1 | exact Hy2 ].
    - intros [Hy1 Hy2]. split; [ exact Hy1 | split; [ exact Hy2 | ] ].
      intro Hytd. subst y. apply in_outgoing in Hy1. destruct Hy1 as [_ Hb].
      rewrite dbase_twin in Hb. apply Hprop. symmetry. exact Hb. }
  assert (HmemG : forall y, In y (outgoing (dtip d) (darts_of (E_minus E d))) <->
                            (In y (outgoing (dtip d) (darts_of E)) /\ y <> twin d)).
  { intro y. rewrite (in_outgoing_darts_of_E_minus E d (dtip d) y Hndtw). split.
    - intros [Hy1 [_ Hy3]]. split; [ exact Hy1 | exact Hy3 ].
    - intros [Hy1 Hy2]. split; [ exact Hy1 | split; [ | exact Hy2 ] ].
      intro Hyd. subst y. apply in_outgoing in Hy1. destruct Hy1 as [_ Hb].
      apply Hprop. exact Hb. }
  (* case split on dtip x relative to the two endpoints *)
  destruct (point_eq_dec (dtip x) (dbase d)) as [Heb | Hneb].
  - (* dtip x = dbase d : fan loses d *)
    assert (HinTwxF : In (twin x) (outgoing (dbase d) (darts_of E))).
    { apply in_outgoing. split; [ exact HtwxE | rewrite dbase_twin; exact Heb ]. }
    assert (HinDF : In d (outgoing (dbase d) (darts_of E))).
    { apply in_outgoing. split; [ apply in_darts_of_orig; exact Hd | reflexivity ]. }
    assert (HKEY1 : next (outgoing (dbase d) (darts_of E)) d = fstep (darts_of E) (twin d)).
    { unfold fstep. rewrite dtip_twin, twin_involutive. reflexivity. }
    assert (Hfsx : fstep (darts_of E) x = next (outgoing (dbase d) (darts_of E)) (twin x)).
    { unfold fstep. rewrite Heb. reflexivity. }
    assert (Hlhs : fstep (darts_of (E_minus E d)) x =
                   next (outgoing (dbase d) (darts_of (E_minus E d))) (twin x)).
    { unfold fstep. rewrite Heb. reflexivity. }
    rewrite Hlhs.
    rewrite (next_remove (outgoing (dbase d) (darts_of E))
                         (outgoing (dbase d) (darts_of (E_minus E d)))
                         (twin x) d (Hfan (dbase d)) HinTwxF HinDF Htwxd HmemF).
    rewrite <- Hfsx. rewrite HKEY1.
    destruct (dart_eq_dec (fstep (darts_of E) x) d) as [E1 | E1].
    + reflexivity.
    + destruct (dart_eq_dec (fstep (darts_of E) x) (twin d)) as [E2 | E2].
      * exfalso.
        assert (Hb2 : dbase (fstep (darts_of E) x) = dbase d) by (rewrite Hbase; exact Heb).
        rewrite E2, dbase_twin in Hb2. apply Hprop. symmetry. exact Hb2.
      * reflexivity.
  - (* dtip x <> dbase d *)
    destruct (point_eq_dec (dtip x) (dtip d)) as [Het | Hnet].
    + (* dtip x = dtip d : fan loses twin d *)
      assert (HinTwxG : In (twin x) (outgoing (dtip d) (darts_of E))).
      { apply in_outgoing. split; [ exact HtwxE | rewrite dbase_twin; exact Het ]. }
      assert (HinTwdG : In (twin d) (outgoing (dtip d) (darts_of E))).
      { apply in_outgoing. split; [ apply in_darts_of_twin; exact Hd
                                  | rewrite dbase_twin; reflexivity ]. }
      assert (HKEY2 : next (outgoing (dtip d) (darts_of E)) (twin d) = fstep (darts_of E) d).
      { unfold fstep. reflexivity. }
      assert (Hfsx : fstep (darts_of E) x = next (outgoing (dtip d) (darts_of E)) (twin x)).
      { unfold fstep. rewrite Het. reflexivity. }
      assert (Hlhs : fstep (darts_of (E_minus E d)) x =
                     next (outgoing (dtip d) (darts_of (E_minus E d))) (twin x)).
      { unfold fstep. rewrite Het. reflexivity. }
      rewrite Hlhs.
      rewrite (next_remove (outgoing (dtip d) (darts_of E))
                           (outgoing (dtip d) (darts_of (E_minus E d)))
                           (twin x) (twin d) (Hfan (dtip d)) HinTwxG HinTwdG Htwx_twd HmemG).
      rewrite <- Hfsx. rewrite HKEY2.
      destruct (dart_eq_dec (fstep (darts_of E) x) d) as [E1 | E1].
      * exfalso.
        assert (Hb2 : dbase (fstep (darts_of E) x) = dtip d) by (rewrite Hbase; exact Het).
        rewrite E1 in Hb2. apply Hprop. exact Hb2.
      * reflexivity.
    + (* away : fstep unchanged, and fstep_E x is neither d nor twin d *)
      rewrite (fstep_E_minus_eq_away E d x Hneb Hnet).
      destruct (dart_eq_dec (fstep (darts_of E) x) d) as [E1 | E1].
      * exfalso. assert (Hb2 : dbase (fstep (darts_of E) x) = dtip x) by exact Hbase.
        rewrite E1 in Hb2. apply Hneb. symmetry. exact Hb2.
      * destruct (dart_eq_dec (fstep (darts_of E) x) (twin d)) as [E2 | E2].
        -- exfalso. assert (Hb2 : dbase (fstep (darts_of E) x) = dtip x) by exact Hbase.
           rewrite E2, dbase_twin in Hb2. apply Hnet. symmetry. exact Hb2.
        -- reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure dart/angular combinatorics; allowlist axioms only.       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions fstep_E_minus_splice.
