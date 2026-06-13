(* ============================================================================
   NetTopologySuite.Proofs.NoShortFaces
   ----------------------------------------------------------------------------
   extract_rings_valid R5, bridge follow-up: step (4b) of the corrected
   discharge plan (docs/extract-faces-bridge.md) -- H3 (`no_short_faces`),
   plus the integrating capstone over the well-noded condition.

   `no_short_faces D` says every face has period >= 3.  Since `face_period`
   is the FIRST return time, `period >= 3` follows from `face_period_spec`
   (the period IS a genuine return) by refuting the two short candidates:

     - period = 1 (self-loop): `fstep D d` is based at `dtip d` (next stays
       in the fan at the head vertex), so `fstep D d = d` forces
       `dbase d = dtip d` -- a degenerate dart.  `all_proper_darts D` kills it.
     - period = 2 (bigon): if `fstep D (fstep D d) = d` then `e := fstep D d`
       runs `dtip d -> dbase d`, i.e. `e = twin d` -- a SPUR.  A no-spur
       hypothesis kills it.

   So `no_short_faces` reduces EXACTLY to properness + no-spurs.  This is
   strictly weaker than `face_twin_free` (rung 1's per-face hypothesis):
   a bigon is a period-2 face, which is a spur; but `face_twin_free` also
   excludes twin pairs reachable across a BRIDGE edge with no spur (the
   dumbbell, step-3 doc).  So H3 lands here from a clean named condition,
   while `face_twin_free` still awaits the 2-edge-connected input.

   Capstone: `extract_faces_valid_well_noded` discharges H1 (twin-aware),
   H2 (`fan_ok`) and H3 from `well_noded_darts` + `no_spurs`, leaving ONLY
   the per-face `face_twin_free` hypothesis of
   `FaceTwinAware.extract_faces_valid_twin_aware` open -- the precise
   residual of the bridge.

   Pure dart + orbit combinatorics; no `Admitted` / `Axiom` / `Parameter`;
   allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Arith Lia.
From NTS.Proofs Require Import Distance Overlay OverlayGraph BufferAssembly
                               RingExtract RingSimple Vec Direction Azimuth
                               Dart DartAngularOrder DartNext DartNextSpec
                               DartNextInjective OrbitCycle DartFace FaceChain
                               FaceRingSimple FacePolygon FacePolygonHoles
                               ExtractFaces ExtractFacesHoles FaceTwinAware
                               NodedGeneralPosition VertexGeneralPosition.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The face step is based at the head vertex.                              *)
(* -------------------------------------------------------------------------- *)

Lemma dbase_fstep :
  forall D d, (forall x, In x D -> In (twin x) D) -> In d D ->
    dbase (fstep D d) = dtip d.
Proof.
  intros D d Htw Hd. unfold fstep. apply next_base.
  apply in_outgoing. split; [ apply Htw; exact Hd | apply dbase_twin ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  No period-1 faces under properness.                                     *)
(* -------------------------------------------------------------------------- *)

Lemma fstep_neq_self_of_proper :
  forall D d, (forall x, In x D -> In (twin x) D) -> In d D ->
    proper_dart d -> fstep D d <> d.
Proof.
  intros D d Htw Hd Hpr Heq.
  pose proof (dbase_fstep D d Htw Hd) as Hb.
  rewrite Heq in Hb.                 (* Hb : dbase d = dtip d *)
  apply Hpr. unfold ddir. rewrite Hb.
  unfold point_diff, vzero. apply Vec_eq; cbn [vx vy]; ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  A period-2 face is a spur (`fstep D d = twin d`).                        *)
(* -------------------------------------------------------------------------- *)

Lemma period2_imp_spur :
  forall D d, (forall x, In x D -> In (twin x) D) -> In d D ->
    fstep D (fstep D d) = d -> fstep D d = twin d.
Proof.
  intros D d Htw Hd Hiter.
  pose proof (dbase_fstep D d Htw Hd) as Hbe.       (* fst (fstep d) = snd d *)
  assert (HeD : In (fstep D d) D) by (apply fstep_in; assumption).
  pose proof (dbase_fstep D (fstep D d) Htw HeD) as Hbd.
  rewrite Hiter in Hbd.                             (* fst d = snd (fstep d) *)
  unfold twin.
  rewrite (surjective_pairing (fstep D d)).
  unfold dbase, dtip in Hbe, Hbd.
  rewrite Hbe, <- Hbd. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  H3: no_short_faces from properness + no-spurs.                          *)
(* -------------------------------------------------------------------------- *)

(* The no-spur structural condition: no face step folds a dart onto its twin. *)
Definition no_spurs (D : list Dart) : Prop :=
  forall d, In d D -> fstep D d <> twin d.

Theorem no_short_faces_of_proper_nospur :
  forall D, arrangement_ok D ->
    all_proper_darts D ->
    no_spurs D ->
    no_short_faces D.
Proof.
  intros D Hok Hproper Hnospur d Hd.
  assert (Htw : forall x, In x D -> In (twin x) D) by (exact (proj1 Hok)).
  destruct (face_period_spec D Hok d Hd) as [Hge1 Hret].
  destruct (le_lt_dec 3 (face_period D d)) as [H3 | Hlt]; [ exact H3 | exfalso ].
  assert (Hcase : face_period D d = 1%nat \/ face_period D d = 2%nat) by lia.
  destruct Hcase as [H1 | H2].
  - rewrite H1 in Hret. cbn [iter] in Hret.    (* Hret : fstep D d = d *)
    exact (fstep_neq_self_of_proper D d Htw Hd (Hproper d Hd) Hret).
  - rewrite H2 in Hret. cbn [iter] in Hret.    (* Hret : fstep D (fstep D d) = d *)
    exact (Hnospur d Hd (period2_imp_spur D d Htw Hd Hret)).
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Capstone: H1 + H2 + H3 from the well-noded + no-spur condition.         *)
(*                                                                            *)
(* Discharges every structural hypothesis of                                  *)
(* FaceTwinAware.extract_faces_valid_twin_aware EXCEPT the per-face            *)
(* `face_twin_free` -- the precise residual of the extract_rings_valid bridge. *)
(* -------------------------------------------------------------------------- *)

(* arrangement_ok of a dart set is automatic from the twin closure of         *)
(* `darts_of` and a fan_ok witness.                                           *)
Lemma arrangement_ok_of_fan_ok :
  forall E : list Edge,
    (forall v, fan_ok (outgoing v (darts_of E))) ->
    arrangement_ok (darts_of E).
Proof.
  intros E Hfan. split.
  - intros d Hd. apply darts_of_closed_under_twin. exact Hd.
  - exact Hfan.
Qed.

Theorem extract_faces_valid_well_noded :
  forall op g,
    well_noded_darts (result_edges op g) ->
    no_spurs (result_darts op g) ->
    (forall d, In d (result_darts op g) ->
       face_twin_free (result_darts op g) d (face_period (result_darts op g) d)) ->
    forall poly, In poly (extract_faces op g) -> valid_polygon poly.
Proof.
  intros op g Hwn Hns Htf.
  assert (Hfan : forall v, fan_ok (outgoing v (result_darts op g)))
    by (intro v; apply well_noded_fan_ok; exact Hwn).
  apply (extract_faces_valid_twin_aware op g).
  - exact Hfan.
  - apply well_noded_twin_aware. exact Hwn.
  - apply no_short_faces_of_proper_nospur.
    + apply arrangement_ok_of_fan_ok. exact Hfan.
    + destruct Hwn as (_ & Hp & _). exact Hp.
    + exact Hns.
  - exact Htf.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure dart + orbit combinatorics; allowlist axioms only.       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions dbase_fstep.
Print Assumptions fstep_neq_self_of_proper.
Print Assumptions period2_imp_spur.
Print Assumptions no_short_faces_of_proper_nospur.
Print Assumptions extract_faces_valid_well_noded.
