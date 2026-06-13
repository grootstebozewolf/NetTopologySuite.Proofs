(* ============================================================================
   NetTopologySuite.Proofs.FaceOrbitSep
   ----------------------------------------------------------------------------
   extract_rings_valid R5, bridge follow-up: face_twin_free rung 1 -- reduce
   the per-face `face_twin_free` hypothesis of the capstones to a single
   GLOBAL orbit condition.

   The capstones (NoShortFaces.extract_faces_valid_well_noded and the holes
   mirror) discharge H1/H2/H3 from `well_noded_darts` + `no_spurs` but still
   carry a per-face `face_twin_free`.  Working the structure pins the exact
   residual:

     - `no_spurs` is precisely "no degree-1 vertex / no leaf": `fstep d =
       twin d` iff `outgoing (dtip d) D = {twin d}`, i.e. the head vertex is
       a leaf (next on a singleton fan returns its argument).  So `no_spurs`
       already excludes the antenna.
     - The residual obstruction is the DUMBBELL bridge edge: a cut edge with
       no leaf, traversed in both directions by one face walk.  Equivalently,
       a dart shares a face-ORBIT with its twin.

   So `face_twin_free` across all faces is exactly: no dart is in the same
   `fstep`-orbit as its twin.  This file makes `same_face` an equivalence
   (reusing the finite-permutation return machinery), shows the period walk
   enumerates the orbit, and reduces both capstones to
   `twins_in_different_faces`.  The deeper rung -- deriving
   `twins_in_different_faces` from a graph-theoretic 2-edge-connected /
   no-cut-edge condition -- is the remaining (deferred) step.

   Pure orbit combinatorics; no `Admitted` / `Axiom` / `Parameter`; allowlist
   axioms only.

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
                               NodedGeneralPosition VertexGeneralPosition
                               NoShortFaces ExtractHolesWellNoded.

Import ListNotations.
Local Open Scope nat_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Iterating a multiple of a period is the identity.                       *)
(* -------------------------------------------------------------------------- *)

Lemma iter_period_mult :
  forall (f : Dart -> Dart) (a : Dart) (n q : nat),
    iter f n a = a -> iter f (q * n) a = a.
Proof.
  intros f a n q Hn. induction q as [| q IHq].
  - simpl. reflexivity.
  - replace (S q * n)%nat with (n + q * n)%nat by lia.
    rewrite iter_comp, IHq. exact Hn.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Walk membership is bounded iteration.                                   *)
(* -------------------------------------------------------------------------- *)

Lemma dart_walk_iter_iff :
  forall D (d x : Dart) (n : nat),
    In x (dart_walk D d n) <-> exists k, (k < n)%nat /\ iter (fstep D) k d = x.
Proof.
  intros D d x n. revert d. induction n as [| n IHn]; intros d.
  - simpl. split.
    + intros [].
    + intros [k [Hk _]]. lia.
  - simpl. split.
    + intros [Hh | Ht].
      * exists 0%nat. split; [ lia | cbn; exact Hh ].
      * apply IHn in Ht. destruct Ht as [k [Hk Hit]].
        exists (S k). split; [ lia | ].
        replace (S k) with (k + 1)%nat by lia.
        rewrite iter_comp. cbn [iter] in *. exact Hit.
    + intros [k [Hk Hit]]. destruct k as [| k].
      * left. cbn [iter] in Hit. exact Hit.
      * right. apply IHn. exists k. split; [ lia | ].
        replace (S k) with (k + 1)%nat in Hit by lia.
        rewrite iter_comp in Hit. cbn [iter] in Hit. exact Hit.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  `same_face`: reachability under the face step, an equivalence on D.     *)
(* -------------------------------------------------------------------------- *)

Definition same_face (D : list Dart) (a b : Dart) : Prop :=
  exists k, iter (fstep D) k a = b.

Lemma same_face_refl : forall D a, same_face D a a.
Proof. intros D a. exists 0%nat. reflexivity. Qed.

Lemma same_face_trans :
  forall D a b c, same_face D a b -> same_face D b c -> same_face D a c.
Proof.
  intros D a b c [k1 H1] [k2 H2]. exists (k2 + k1)%nat.
  rewrite iter_comp, H1, H2. reflexivity.
Qed.

Lemma same_face_sym :
  forall D, arrangement_ok D ->
    forall a b, In a D -> same_face D a b -> same_face D b a.
Proof.
  intros D Hok a b Ha [k Hk].
  destruct (face_orbit_finite D Hok a Ha) as [n [Hn1 Hnid]].
  exists (k * n - k)%nat.
  rewrite <- Hk, <- iter_comp.
  replace (k * n - k + k)%nat with (k * n)%nat by nia.
  apply (iter_period_mult (fstep D) a n k Hnid).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The period walk enumerates the orbit.                                   *)
(* -------------------------------------------------------------------------- *)

Lemma walk_at_period_iff_same_face :
  forall D, arrangement_ok D -> forall d, In d D ->
    forall x, In x (dart_walk D d (face_period D d)) <-> same_face D d x.
Proof.
  intros D Hok d Hd x. split.
  - intros Hin. apply dart_walk_iter_iff in Hin.
    destruct Hin as [k [_ Hit]]. exists k. exact Hit.
  - intros [k Hk].
    destruct (face_period_spec D Hok d Hd) as [Hp1 Hpid].
    apply dart_walk_iter_iff.
    exists (k mod face_period D d). split.
    + apply Nat.mod_upper_bound. lia.
    + assert (Hsplit : k = k mod face_period D d
                           + (k / face_period D d) * face_period D d).
      { pose proof (Nat.div_mod k (face_period D d) ltac:(lia)) as Hdm. nia. }
      rewrite <- Hk. rewrite Hsplit at 2.
      rewrite iter_comp.
      rewrite (iter_period_mult (fstep D) d (face_period D d)
                 (k / face_period D d) Hpid).
      reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  The global condition and the per-face discharge.                        *)
(* -------------------------------------------------------------------------- *)

(* No dart shares a face orbit with its twin -- the no-cut-edge content. *)
Definition twins_in_different_faces (D : list Dart) : Prop :=
  forall x, In x D -> ~ same_face D x (twin x).

Theorem face_twin_free_of_sep :
  forall D, arrangement_ok D ->
    twins_in_different_faces D ->
    forall d, In d D -> face_twin_free D d (face_period D d).
Proof.
  intros D Hok Hsep d Hd x Hx Htwx.
  assert (HxD : In x D)
    by (apply (dart_walk_subset D (proj1 Hok) (face_period D d) d Hd x Hx)).
  apply (walk_at_period_iff_same_face D Hok d Hd) in Hx.
  apply (walk_at_period_iff_same_face D Hok d Hd) in Htwx.
  apply (Hsep x HxD).
  apply (same_face_trans D x d (twin x)).
  - apply (same_face_sym D Hok d x Hd Hx).
  - exact Htwx.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Capstones over the single global hypothesis.                            *)
(* -------------------------------------------------------------------------- *)

Theorem extract_faces_valid_sep :
  forall op g,
    well_noded_darts (result_edges op g) ->
    no_spurs (result_darts op g) ->
    twins_in_different_faces (result_darts op g) ->
    forall poly, In poly (extract_faces op g) -> valid_polygon poly.
Proof.
  intros op g Hwn Hns Hsep.
  apply (extract_faces_valid_well_noded op g Hwn Hns).
  intros d Hd. apply face_twin_free_of_sep.
  - apply arrangement_ok_of_fan_ok. intro v. apply well_noded_fan_ok. exact Hwn.
  - exact Hsep.
  - exact Hd.
Qed.

Theorem extract_faces_holes_valid_sep :
  forall (hassign : Dart -> list Dart) (op : BooleanOp) (g : TopologyGraph),
    well_noded_darts (result_edges op g) ->
    no_spurs (result_darts op g) ->
    twins_in_different_faces (result_darts op g) ->
    (forall d, In d (result_darts op g) ->
       forall h, In h (hassign d) -> In h (result_darts op g)) ->
    (forall d, In d (result_darts op g) ->
       forall h, In h (hassign d) ->
       hole_inside_outer
         (ring_of_chain (face_chain (result_darts op g) d
                           (face_period (result_darts op g) d)))
         (hole_ring_of (result_darts op g)
            (h, face_period (result_darts op g) h))) ->
    forall poly, In poly (extract_faces_holes hassign op g) -> valid_polygon poly.
Proof.
  intros hassign op g Hwn Hns Hsep Hwf Hinside.
  apply (extract_faces_holes_valid_well_noded hassign op g Hwn Hns).
  - intros d Hd. apply face_twin_free_of_sep.
    + apply arrangement_ok_of_fan_ok. intro v. apply well_noded_fan_ok. exact Hwn.
    + exact Hsep.
    + exact Hd.
  - exact Hwf.
  - exact Hinside.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure orbit combinatorics; allowlist axioms only.              *)
(* -------------------------------------------------------------------------- *)

Print Assumptions dart_walk_iter_iff.
Print Assumptions same_face_sym.
Print Assumptions walk_at_period_iff_same_face.
Print Assumptions face_twin_free_of_sep.
Print Assumptions extract_faces_valid_sep.
Print Assumptions extract_faces_holes_valid_sep.
