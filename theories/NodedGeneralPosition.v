(* ============================================================================
   NetTopologySuite.Proofs.NodedGeneralPosition
   ----------------------------------------------------------------------------
   extract_rings_valid R5, bridge follow-up: step (3) of the corrected
   discharge plan (docs/extract-faces-bridge.md) -- the genuine geometric
   step.

   Slice 3i showed `fully_intersected`'s shared-endpoint disjunct admits
   collinear overlaps: `(0,0)-(2,0)` and `(0,0)-(1,0)` share an endpoint yet
   properly cross at `(1/2, 0)` (fully_intersected_not_pairwise_collinear).
   The missing ingredient is general position: when two distinct segments
   share an endpoint AND their directions are non-parallel (direction cross
   product nonzero), they CANNOT properly cross.  Proof shape, uniform over
   the four endpoint-identification cases: substituting the shared point
   into the proper-crossing equations gives a vector identity
   `a * u = c * v` with `a > 0` (one of `t`, `1-t`); crossing both sides
   with `v` kills the right-hand side, leaving `a * (u x v) = 0` -- and
   `a > 0`, `u x v <> 0` is absurd.

   Deliverables:
     - `noncollinear_share_no_proper` -- the four-case geometric lemma.
     - `noded_general_position`      -- the strengthened noding predicate:
       distinct survivors either do not properly cross or share an endpoint
       in general position.  (The Hobby-side renaming of this predicate onto
       `fully_intersected` + a side condition lives with the other
       cross-lane plumbing in theories-flocq/ExtractFacesBridge.v's lineage;
       this file stays host-lane.)
     - `noded_gp_pairwise`           -- it implies the UNDIRECTED
       `pairwise_no_proper_cross` -- the premise of rung 1's
       `darts_of_twin_aware`.
     - `noded_gp_twin_aware`         -- the composition: a general-position
       noded survivor set yields the twin-aware predicate on its darts, the
       H1 of the twin-aware extractor headlines (FaceTwinAware.v).
     - `collinear_pair_not_gp`       -- honesty: slice 3i's collinear
       counterexample pair genuinely fails the strengthened predicate.

   Pure R algebra (cross-product reparametrisation); no `Admitted` /
   `Axiom` / `Parameter`; allowlist axioms only.

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
                               ExtractFaces ExtractFacesHoles FaceTwinAware.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Shared endpoints and direction cross products.                          *)
(* -------------------------------------------------------------------------- *)

Definition share_endpoint (s1 s2 : Edge) : Prop :=
  fst s1 = fst s2 \/ fst s1 = snd s2 \/ snd s1 = fst s2 \/ snd s1 = snd s2.

(* Cross product of the two segment directions. *)
Definition seg_dir_cross (s1 s2 : Edge) : R :=
  (px (snd s1) - px (fst s1)) * (py (snd s2) - py (fst s2))
  - (py (snd s1) - py (fst s1)) * (px (snd s2) - px (fst s2)).

(* -------------------------------------------------------------------------- *)
(* §2  The geometric step: non-collinear endpoint-share excludes proper        *)
(* crossing.                                                                   *)
(* -------------------------------------------------------------------------- *)

(* Scalar core, shared by all four cases: a*u = c*v componentwise with
   a <> 0 forces the cross product of u and v to vanish. *)
Lemma scaled_dirs_cross_zero :
  forall (a c ux uy vx vy : R),
    a * ux = c * vx ->
    a * uy = c * vy ->
    a <> 0 ->
    ux * vy - uy * vx = 0.
Proof.
  intros a c ux uy vx vy Hx Hy Ha.
  assert (Hz : a * (ux * vy - uy * vx) = 0).
  { replace (a * (ux * vy - uy * vx))
      with ((a * ux) * vy - (a * uy) * vx) by ring.
    rewrite Hx, Hy. ring. }
  apply Rmult_integral in Hz. destruct Hz as [Hz | Hz]; [contradiction | exact Hz].
Qed.

Theorem noncollinear_share_no_proper :
  forall s1 s2 : Edge,
    share_endpoint s1 s2 ->
    seg_dir_cross s1 s2 <> 0 ->
    ~ segments_intersect_properly (fst s1) (snd s1) (fst s2) (snd s2).
Proof.
  intros [P0 P1] [Q0 Q1] Hsh Hcr (t & s & Ht & Hs & Hx & Hy).
  cbn [fst snd] in *.
  unfold seg_dir_cross in Hcr. cbn [fst snd] in Hcr.
  set (ux := px P1 - px P0) in *. set (uy := py P1 - py P0) in *.
  set (vx := px Q1 - px Q0) in *. set (vy := py Q1 - py Q0) in *.
  destruct Hsh as [HP | [HP | [HP | HP]]]; cbn [fst snd] in HP.
  - (* P0 = Q0 :  t*u = s*v *)
    apply Hcr.
    apply (scaled_dirs_cross_zero t s); unfold ux, uy, vx, vy;
      [ rewrite HP in Hx | rewrite HP in Hy | ]; subst; lra.
  - (* P0 = Q1 :  t*u = -(1-s)*v *)
    apply Hcr.
    apply (scaled_dirs_cross_zero t (- (1 - s))); unfold ux, uy, vx, vy;
      [ rewrite HP in Hx | rewrite HP in Hy | ]; subst; lra.
  - (* P1 = Q0 :  (1-t)*u = -s*v *)
    apply Hcr.
    apply (scaled_dirs_cross_zero (1 - t) (- s)); unfold ux, uy, vx, vy;
      [ rewrite HP in Hx | rewrite HP in Hy | ]; subst; lra.
  - (* P1 = Q1 :  (1-t)*u = (1-s)*v *)
    apply Hcr.
    apply (scaled_dirs_cross_zero (1 - t) (1 - s)); unfold ux, uy, vx, vy;
      [ rewrite HP in Hx | rewrite HP in Hy | ]; subst; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The strengthened noding predicate and its consequences.                 *)
(* -------------------------------------------------------------------------- *)

(* Distinct survivors either do not properly cross, or meet at a shared
   endpoint in general position (non-parallel directions).  This is the
   no-collinear-overlap strengthening of `fully_intersected`: the collinear
   configurations its shared-endpoint disjunct admitted are excluded by the
   cross-product clause. *)
Definition noded_general_position (S : list Edge) : Prop :=
  forall s1 s2 : Edge,
    In s1 S -> In s2 S -> s1 <> s2 ->
    ~ segments_intersect_properly (fst s1) (snd s1) (fst s2) (snd s2)
    \/ (share_endpoint s1 s2 /\ seg_dir_cross s1 s2 <> 0).

(* General position delivers the UNDIRECTED pairwise guarantee ... *)
Theorem noded_gp_pairwise :
  forall S : list Edge,
    noded_general_position S -> pairwise_no_proper_cross S.
Proof.
  intros S Hgp e1 e2 H1 H2 Hne.
  destruct (Hgp e1 e2 H1 H2 Hne) as [Hnp | [Hsh Hcr]].
  - exact Hnp.
  - apply noncollinear_share_no_proper; assumption.
Qed.

(* ... and hence, through rung 1's lift, the twin-aware H1 on the darts. *)
Corollary noded_gp_twin_aware :
  forall E : list Edge,
    noded_general_position E ->
    pairwise_no_proper_cross_twin_aware (darts_of E).
Proof.
  intros E Hgp. apply darts_of_twin_aware, noded_gp_pairwise, Hgp.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Honesty: the strengthening genuinely excludes slice 3i's collinear      *)
(* counterexample.                                                             *)
(* -------------------------------------------------------------------------- *)

Definition gp_cx_long : Edge := (mkPoint 0 0, mkPoint 2 0).
Definition gp_cx_short : Edge := (mkPoint 0 0, mkPoint 1 0).

Lemma collinear_pair_crosses :
  segments_intersect_properly (fst gp_cx_long) (snd gp_cx_long)
                              (fst gp_cx_short) (snd gp_cx_short).
Proof.
  exists (1/4), (1/2). cbn. repeat split; lra.
Qed.

Lemma collinear_pair_not_gp :
  ~ noded_general_position [gp_cx_long; gp_cx_short].
Proof.
  intro Hgp.
  assert (Hne : gp_cx_long <> gp_cx_short).
  { unfold gp_cx_long, gp_cx_short. intro H. inversion H as [H1].
    assert (px (mkPoint 2 0) = px (mkPoint 1 0)) by (rewrite H1; reflexivity).
    cbn in *. lra. }
  destruct (Hgp gp_cx_long gp_cx_short
              (or_introl eq_refl) (or_intror (or_introl eq_refl)) Hne)
    as [Hnp | [_ Hcr]].
  - exact (Hnp collinear_pair_crosses).
  - apply Hcr. unfold seg_dir_cross, gp_cx_long, gp_cx_short. cbn. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure R algebra; allowlist axioms only.                        *)
(* -------------------------------------------------------------------------- *)

Print Assumptions scaled_dirs_cross_zero.
Print Assumptions noncollinear_share_no_proper.
Print Assumptions noded_gp_pairwise.
Print Assumptions noded_gp_twin_aware.
Print Assumptions collinear_pair_not_gp.
