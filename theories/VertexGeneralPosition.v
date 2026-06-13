(* ============================================================================
   NetTopologySuite.Proofs.VertexGeneralPosition
   ----------------------------------------------------------------------------
   extract_rings_valid R5, bridge follow-up: step (4a) of the corrected
   discharge plan (docs/extract-faces-bridge.md) -- H2 (`fan_ok`) from a
   vertex-level general-position condition.

   Step (3) (NodedGeneralPosition.v) gave H1 (twin-aware non-crossing) from
   `noded_general_position`.  H2 is `fan_ok (outgoing v D)`: every dart at a
   vertex has nonzero direction, and distinct darts at a vertex have
   NON-PARALLEL directions.

   FINDING (refines the plan doc's step-4 wording).  `noded_general_position`
   does NOT imply `fan_ok`.  Its shared-endpoint clause only constrains pairs
   that PROPERLY CROSS; two anti-parallel collinear darts at a vertex (a
   straight-through degree-2 vertex, e.g. `(0,0)-(1,0)` and `(0,0)-(-1,0)`)
   meet only at that vertex, do NOT properly cross, yet have parallel
   directions -- so they satisfy `noded_general_position` while breaking
   `fan_ok`.  `straight_through_not_fan_ok` is the machine-checked witness.

   The right H2 input is therefore a genuinely additional, UNCONDITIONAL
   vertex condition: `vertex_general_position D` -- distinct survivors that
   share an endpoint have non-parallel directions, regardless of crossing.
   This is exactly "no two collinear edges meet at a vertex", which a planar
   subdivision with collinear runs merged satisfies.  `fan_ok_of_vertex_gp`
   derives H2 from it (plus properness).  The full bridge precondition is the
   CONJUNCTION of step (3)'s edge condition and this vertex condition
   (`well_noded_darts`); `well_noded_imp_fan_ok` packages H2 from it.

   Key bridge: `seg_dir_cross d e = vcross (ddir d) (ddir e)`, so the §1
   cross-product vocabulary of step (3) IS the `parallel`/`ddir` vocabulary
   of `fan_ok`.

   Pure dart + vector algebra; no `Admitted` / `Axiom` / `Parameter`;
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
                               NodedGeneralPosition.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The bridge: seg_dir_cross is the direction cross product.               *)
(* -------------------------------------------------------------------------- *)

Lemma seg_dir_cross_eq_vcross_ddir :
  forall d e : Dart, seg_dir_cross d e = vcross (ddir d) (ddir e).
Proof.
  intros [a b] [c f].
  unfold seg_dir_cross, vcross, ddir, point_diff, dtip, dbase. cbn [fst snd vx vy].
  ring.
Qed.

(* Non-zero direction cross product is exactly non-parallel directions. *)
Lemma seg_dir_cross_nz_iff_not_parallel :
  forall d e : Dart,
    seg_dir_cross d e <> 0 <-> ~ parallel (ddir d) (ddir e).
Proof.
  intros d e. unfold parallel.
  rewrite seg_dir_cross_eq_vcross_ddir. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The vertex-level general-position condition (corrected step-4 input).   *)
(* -------------------------------------------------------------------------- *)

(* Distinct survivors sharing an endpoint have non-parallel directions --
   UNCONDITIONALLY (not gated on proper crossing).  "No two collinear edges
   meet at a vertex." *)
Definition vertex_general_position (D : list Dart) : Prop :=
  forall d e : Dart,
    In d D -> In e D -> d <> e -> share_endpoint d e -> seg_dir_cross d e <> 0.

(* All darts non-degenerate. *)
Definition all_proper_darts (D : list Dart) : Prop :=
  forall d : Dart, In d D -> proper_dart d.

(* -------------------------------------------------------------------------- *)
(* §3  H2: fan_ok at every vertex.                                             *)
(* -------------------------------------------------------------------------- *)

Theorem fan_ok_of_vertex_gp :
  forall D : list Dart,
    all_proper_darts D ->
    vertex_general_position D ->
    forall v : Point, fan_ok (outgoing v D).
Proof.
  intros D Hproper Hvgp v. split.
  - (* properness *)
    intros d Hd. apply in_outgoing in Hd. apply Hproper, (proj1 Hd).
  - (* non-parallel directions *)
    intros d e Hd He Hne.
    apply in_outgoing in Hd. destruct Hd as [HdD Hdv].
    apply in_outgoing in He. destruct He as [HeD Hev].
    apply seg_dir_cross_nz_iff_not_parallel.
    apply (Hvgp d e HdD HeD Hne).
    (* both darts have dbase = v, so fst d = fst e: first share_endpoint case *)
    left. unfold dbase in Hdv, Hev. rewrite Hdv, Hev. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The combined well-noded condition packages H1 and H2.                   *)
(* -------------------------------------------------------------------------- *)

(* The full structural precondition of the extractor headlines, over an
   UNDIRECTED survivor set E: edge-level general position (step 3, for H1
   on darts_of E) and vertex-level general position + properness on the
   resulting dart set (step 4, for H2). *)
Definition well_noded_darts (E : list Edge) : Prop :=
  noded_general_position E
  /\ all_proper_darts (darts_of E)
  /\ vertex_general_position (darts_of E).

(* H1 from the well-noded condition (re-export through step 3). *)
Corollary well_noded_twin_aware :
  forall E : list Edge,
    well_noded_darts E ->
    pairwise_no_proper_cross_twin_aware (darts_of E).
Proof.
  intros E (Hgp & _ & _). apply noded_gp_twin_aware, Hgp.
Qed.

(* H2 from the well-noded condition. *)
Corollary well_noded_fan_ok :
  forall E : list Edge,
    well_noded_darts E ->
    forall v : Point, fan_ok (outgoing v (darts_of E)).
Proof.
  intros E (_ & Hproper & Hvgp). apply fan_ok_of_vertex_gp; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Honesty: step (3)'s edge condition does NOT give H2.                     *)
(* The straight-through vertex -- two anti-parallel collinear edges meeting    *)
(* at a point -- satisfies `noded_general_position` yet breaks `fan_ok`.       *)
(* -------------------------------------------------------------------------- *)

Definition st_right : Edge := (mkPoint 0 0, mkPoint 1 0).
Definition st_left  : Edge := (mkPoint 0 0, mkPoint (-1) 0).

(* The two edges meet only at the origin: they do NOT properly cross. *)
Lemma straight_through_no_proper :
  ~ segments_intersect_properly (fst st_right) (snd st_right)
                                (fst st_left) (snd st_left).
Proof.
  unfold st_right, st_left. cbn [fst snd].
  intros (t & s & Ht & Hs & Hx & Hy). cbn [px py] in *.
  (* x: (1-t)*0 + t*1 = (1-s)*0 + s*(-1)  ->  t = -s, impossible for t,s>0 *)
  lra.
Qed.

(* Hence the pair satisfies the step-(3) edge predicate ... *)
Lemma straight_through_noded_gp :
  noded_general_position [st_right; st_left].
Proof.
  intros s1 s2 H1 H2 Hne.
  (* enumerate the off-diagonal pairs; both reduce to "do not properly cross" *)
  cbn in H1, H2.
  destruct H1 as [<- | [<- | []]]; destruct H2 as [<- | [<- | []]].
  - exfalso. apply Hne. reflexivity.
  - left. apply straight_through_no_proper.
  - left. intro Hsip. apply straight_through_no_proper.
    (* symmetric pair: swap both segments back *)
    apply sip_swap_left in Hsip. apply sip_swap_right in Hsip.
    revert Hsip. unfold st_right, st_left. cbn [fst snd].
    intros (t & s & Ht & Hs & Hx & Hy). cbn [px py] in *.
    exists s, t. cbn [px py]. repeat split; lra.
  - exfalso. apply Hne. reflexivity.
Qed.

(* ... but the fan at the shared vertex is NOT fan_ok: the two darts there       *)
(* have parallel (anti-parallel) directions.                                    *)
Lemma straight_through_not_fan_ok :
  ~ fan_ok (outgoing (mkPoint 0 0) (darts_of [st_right; st_left])).
Proof.
  intros [_ Hnp].
  assert (Hr : In st_right (darts_of [st_right; st_left])).
  { apply in_darts_of_orig. cbn. left. reflexivity. }
  assert (Hl : In st_left (darts_of [st_right; st_left])).
  { apply in_darts_of_orig. cbn. right. left. reflexivity. }
  assert (HrO : In st_right (outgoing (mkPoint 0 0) (darts_of [st_right; st_left]))).
  { apply in_outgoing. split; [ exact Hr | reflexivity ]. }
  assert (HlO : In st_left (outgoing (mkPoint 0 0) (darts_of [st_right; st_left]))).
  { apply in_outgoing. split; [ exact Hl | reflexivity ]. }
  assert (Hne : st_right <> st_left).
  { unfold st_right, st_left. intro H. inversion H as [H1].
    assert (px (mkPoint 1 0) = px (mkPoint (-1) 0)) by (rewrite H1; reflexivity).
    cbn in *. lra. }
  apply (Hnp st_right st_left HrO HlO Hne).
  (* directions (1,0) and (-1,0): vcross = 0, parallel *)
  unfold parallel, st_right, st_left, ddir, point_diff, vcross, dtip, dbase.
  cbn [fst snd px py vx vy]. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure dart + vector algebra; allowlist axioms only.            *)
(* -------------------------------------------------------------------------- *)

Print Assumptions seg_dir_cross_eq_vcross_ddir.
Print Assumptions fan_ok_of_vertex_gp.
Print Assumptions well_noded_twin_aware.
Print Assumptions well_noded_fan_ok.
Print Assumptions straight_through_noded_gp.
Print Assumptions straight_through_not_fan_ok.
