(* ==========================================================================
   NumFacesShrink.v

   [EF-4 partial] Euler ladder: cycle-count SHRINK, the INSTANTIATION.

   Third member of the `num_faces_E_minus_*` family, alongside
   `NumFacesSplice.num_faces_E_minus_splice` (same-face SPLIT, faces +1) and
   `NumFacesMerge.num_faces_E_minus_merge` (non-same-face MERGE, faces -1):
   deleting a degree-1 (leaf) vertex's unique edge changes the face count by
   ZERO.

   `PermCycleShrink.cycle_count_shrink` is the generic fact: given a
   permutation `f` of `S` with `f d = td` DIRECTLY (the `k = 1` case
   `PermCycleSplice.v`'s SPLIT excludes outright, `Hk_range : 2 <= k <=
   per-2`) and `d`'s orbit has period `>= 3` (excluding the further
   degenerate isolated-2-cycle sub-case), the SAME same_face-agnostic
   cross-wiring redirect `FaceStepRemove.fstep_E_minus_splice` leaves the
   orbit count of the surgered map UNCHANGED.

   Here we instantiate it at the face-step permutation for a leaf edge `d`
   (`dbase d` a degree-1 vertex whose unique outgoing dart is `d` itself):
   `EulerWitness.fstep_of_singleton_fan` gives exactly the spur this needs --
   `fstep (darts_of E) (twin d) = d` -- directly from the singleton-fan
   hypothesis `outgoing (dbase d) (darts_of E) = [d]`.  The period lower
   bound `3 <= per` is derived (not assumed) from properness (rules out
   `per = 1`) plus the one honestly new hypothesis this file adds --
   `fstep (darts_of E) d <> twin d`, i.e. the FAR endpoint `dtip d` is not
   ITSELF a reciprocal leaf (rules out `per = 2`, via `NoShortFaces.
   period2_imp_spur`'s converse direction: `per = 2` would force
   `fstep (darts_of E) d = twin d`).  Every other `SpliceSpec`-shaped
   hypothesis is discharged from the SAME established Dart-layer facts
   `NumFacesSplice.v`/`NumFacesMerge.v` use.

   Pure combinatorial wiring; no `Admitted` / `Axiom` / `Parameter`; allowlist
   axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import List Arith Lia.
From NTS.Proofs Require Import Distance Overlay Dart DartNextSpec DartAngularOrder
                               DartNextSpec DartFace FaceOrbitSep NoShortFaces
                               ExtractFaces EdgeConnectivity EdgeFaceBridge
                               ArrangementEMinus FaceStepRemove MapCounts
                               EulerWitness
                               OrbitCycle PermCycleCount PermCycleShrink.

Import ListNotations.

(* Deleting a leaf edge (whose base is a degree-1 vertex, and whose far
   endpoint is not itself a reciprocal degree-1 vertex) leaves the face
   count UNCHANGED. *)
Lemma num_faces_E_minus_shrink : forall (E : list Edge) (d : Dart),
  (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
  In d E -> ~ In (twin d) E ->
  dbase d <> dtip d ->
  outgoing (dbase d) (darts_of E) = [d] ->
  fstep (darts_of E) d <> twin d ->
  num_faces (E_minus E d) = num_faces E.
Proof.
  intros E d Hfan HdE Hntwin Hproper Hleaf Hnotrecip.
  (* The arrangement is well-formed (twin-closed + per-vertex fan_ok). *)
  assert (Hao : arrangement_ok (darts_of E))
    by (split; [ exact (darts_of_closed_under_twin E) | exact Hfan ]).
  assert (HdS : In d (darts_of E))
    by (unfold darts_of; apply in_or_app; left; exact HdE).
  assert (Htwin_in : In (twin d) (darts_of E))
    by (apply darts_of_closed_under_twin; exact HdS).
  assert (Hdtd : twin d <> d) by (apply twin_neq_self; exact Hproper).
  (* The spur: the far endpoint's unique-fan forces fstep (twin d) = d. *)
  assert (Hspur : fstep (darts_of E) (twin d) = d).
  { pose proof (fstep_of_singleton_fan E (twin d)) as Hgen.
    rewrite dtip_twin, twin_involutive in Hgen.
    apply Hgen. exact Hleaf. }
  (* Period of the (shared) face orbit, taken at `twin d`. *)
  destruct (face_period_spec (darts_of E) Hao (twin d) Htwin_in) as [Hper_pos Hper_ret].
  assert (Hper_min : forall j, (1 <= j < face_period (darts_of E) (twin d))%nat ->
                       OrbitCycle.iter (fstep (darts_of E)) j (twin d) <> twin d)
    by (intros j Hj; exact (face_period_no_early_return (darts_of E) (twin d) j Hao Htwin_in Hj)).
  assert (Hper_ne1 : face_period (darts_of E) (twin d) <> 1%nat).
  { intro Heq. rewrite Heq in Hper_ret. cbn [OrbitCycle.iter] in Hper_ret.
    rewrite Hper_ret in Hspur. apply Hdtd. exact Hspur. }
  assert (Hper_ne2 : face_period (darts_of E) (twin d) <> 2%nat).
  { intro Heq. rewrite Heq in Hper_ret. cbn [OrbitCycle.iter] in Hper_ret.
    rewrite Hspur in Hper_ret. apply Hnotrecip. exact Hper_ret. }
  assert (Hper_ge3 : (3 <= face_period (darts_of E) (twin d))%nat) by lia.
  (* SpliceSpec hypotheses for the (f,S) side. *)
  assert (Hclos : forall x, In x (darts_of E) -> In (fstep (darts_of E) x) (darts_of E))
    by (intros x Hx; exact (fstep_in (darts_of E) x (darts_of_closed_under_twin E) Hx)).
  assert (Hinj : forall a b, In a (darts_of E) -> In b (darts_of E) ->
                   fstep (darts_of E) a = fstep (darts_of E) b -> a = b)
    by (exact (fstep_inj (darts_of E) Hao)).
  (* SpliceSpec hypotheses for the (f',S') side. *)
  assert (Hao' : arrangement_ok (darts_of (E_minus E d)))
    by (apply arrangement_ok_E_minus; exact Hfan).
  assert (Hcarrier : forall x, In x (darts_of (E_minus E d)) <->
                       (In x (darts_of E) /\ x <> twin d /\ x <> d)).
  { intro x. rewrite (in_darts_of_E_minus_iff E d x Hntwin). tauto. }
  assert (Hclos' : forall x, In x (darts_of (E_minus E d)) ->
                     In (fstep (darts_of (E_minus E d)) x) (darts_of (E_minus E d)))
    by (intros x Hx; exact (fstep_in (darts_of (E_minus E d)) x (proj1 Hao') Hx)).
  assert (Hinj' : forall a b, In a (darts_of (E_minus E d)) -> In b (darts_of (E_minus E d)) ->
                    fstep (darts_of (E_minus E d)) a = fstep (darts_of (E_minus E d)) b -> a = b)
    by (exact (fstep_inj (darts_of (E_minus E d)) Hao')).
  assert (Hf'spec : forall x, In x (darts_of (E_minus E d)) ->
            fstep (darts_of (E_minus E d)) x =
              (if dart_eq_dec (fstep (darts_of E) x) (twin d) then fstep (darts_of E) d
               else if dart_eq_dec (fstep (darts_of E) x) d then fstep (darts_of E) (twin d)
               else fstep (darts_of E) x)).
  { intros x Hx.
    rewrite (fstep_E_minus_splice E d x Hfan HdE Hntwin Hproper Hx).
    destruct (dart_eq_dec (fstep (darts_of E) x) d) as [H1 | H1];
      destruct (dart_eq_dec (fstep (darts_of E) x) (twin d)) as [H2 | H2].
    - exfalso. rewrite H1 in H2. apply Hdtd. symmetry. exact H2.
    - reflexivity.
    - reflexivity.
    - reflexivity. }
  (* Apply the generic capstone. *)
  unfold num_faces.
  exact (cycle_count_shrink dart_eq_dec (fstep (darts_of E)) (darts_of E)
           Hclos Hinj (twin d) d Htwin_in Hspur
           (face_period (darts_of E) (twin d)) Hper_ret Hper_ge3 Hper_min
           (fstep (darts_of (E_minus E d))) (darts_of (E_minus E d))
           Hcarrier Hclos' Hinj' Hf'spec).
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Combinatorial wiring; allowlist axioms only.                  *)
(* -------------------------------------------------------------------------- *)

Print Assumptions num_faces_E_minus_shrink.
