(* ==========================================================================
   NumFacesMerge.v

   [EF-2] Euler ladder: cycle-count MERGE, the INSTANTIATION.

   `PermCycleMerge.cycle_count_merge` is the generic mirror-image fact: given
   a permutation `f` of `S` whose orbit of `d` (period `per1`) and orbit of
   `td` (period `per2`) are DISTINCT (`~ same_orbit f d td`), the surgered map
   `f'` on `S' = S minus {d, td}` that cross-connects the predecessors of `d`
   and `td` (the SAME redirect the split case uses) has
   `cycle_count f' S' = cycle_count f S - 1`.

   Here we instantiate it at the face-step permutation to discharge [EF-2]:
       num_faces (E_minus E d) = num_faces E - 1
   for a NON-same-face edge `d`.  `f := fstep (darts_of E)`, `S := darts_of E`,
   `td := twin d`, `f' := fstep (darts_of (E_minus E d))`,
   `S' := darts_of (E_minus E d))`, `per1 := face_period (darts_of E) d`,
   `per2 := face_period (darts_of E) (twin d)`.  Every `SpliceSpec`-shaped
   hypothesis is discharged from the SAME established Dart-layer facts
   `NumFacesSplice.v` uses (`fstep_in`/`fstep_inj`, `face_period_spec`/
   `_no_early_return`, `in_darts_of_E_minus_iff`, `arrangement_ok_E_minus`,
   `fstep_E_minus_splice` -- proved WITHOUT any same-face hypothesis, so it
   serves both directions unchanged); the only new step is the period lower
   bound `3 <= per1`, `3 <= per2` from `NoShortFaces.no_short_faces_of_proper_
   nospur` (properness + no-spurs alone, the same guard `no_short_faces`
   already names).

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
                               VertexGeneralPosition
                               OrbitCycle PermCycleCount PermCycleMerge.

Import ListNotations.

(* Deleting a non-same-face edge merges the two faces it borders: the orbit
   count falls by one. *)
Lemma num_faces_E_minus_merge : forall (E : list Edge) (d : Dart),
  (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
  all_proper_darts (darts_of E) ->
  no_spurs (darts_of E) ->
  In d E -> ~ In (twin d) E ->
  dbase d <> dtip d ->
  ~ same_face (darts_of E) d (twin d) ->
  num_faces (E_minus E d) = (num_faces E - 1)%nat.
Proof.
  intros E d Hfan Hprop Hns HdE Hntwin Hproper Hnsf.
  (* The arrangement is well-formed (twin-closed + per-vertex fan_ok). *)
  assert (Hao : arrangement_ok (darts_of E))
    by (split; [ exact (darts_of_closed_under_twin E) | exact Hfan ]).
  assert (HdS : In d (darts_of E))
    by (unfold darts_of; apply in_or_app; left; exact HdE).
  assert (Htwin_in : In (twin d) (darts_of E))
    by (apply darts_of_closed_under_twin; exact HdS).
  (* Periods of both face orbits. *)
  destruct (face_period_spec (darts_of E) Hao d HdS) as [Hper1_pos Hper1_ret].
  destruct (face_period_spec (darts_of E) Hao (twin d) Htwin_in) as [Hper2_pos Hper2_ret].
  assert (Hnsf_ao : no_short_faces (darts_of E))
    by (apply no_short_faces_of_proper_nospur; [ exact Hao | exact Hprop | exact Hns ]).
  assert (Hper1_ge2 : (2 <= face_period (darts_of E) d)%nat)
    by (pose proof (Hnsf_ao d HdS); lia).
  assert (Hper2_ge2 : (2 <= face_period (darts_of E) (twin d))%nat)
    by (pose proof (Hnsf_ao (twin d) Htwin_in); lia).
  assert (Hper1_min : forall j, (1 <= j < face_period (darts_of E) d)%nat ->
                       OrbitCycle.iter (fstep (darts_of E)) j d <> d)
    by (intros j Hj; exact (face_period_no_early_return (darts_of E) d j Hao HdS Hj)).
  assert (Hper2_min : forall j, (1 <= j < face_period (darts_of E) (twin d))%nat ->
                       OrbitCycle.iter (fstep (darts_of E)) j (twin d) <> twin d)
    by (intros j Hj; exact (face_period_no_early_return (darts_of E) (twin d) j Hao Htwin_in Hj)).
  (* SpliceSpec hypotheses for the (f,S) side. *)
  assert (Hclos : forall x, In x (darts_of E) -> In (fstep (darts_of E) x) (darts_of E))
    by (intros x Hx; exact (fstep_in (darts_of E) x (darts_of_closed_under_twin E) Hx)).
  assert (Hinj : forall a b, In a (darts_of E) -> In b (darts_of E) ->
                   fstep (darts_of E) a = fstep (darts_of E) b -> a = b)
    by (exact (fstep_inj (darts_of E) Hao)).
  assert (Hdtd : d <> twin d).
  { intro He. apply (twin_neq_self d Hproper). symmetry. exact He. }
  (* SpliceSpec hypotheses for the (f',S') side. *)
  assert (Hao' : arrangement_ok (darts_of (E_minus E d)))
    by (apply arrangement_ok_E_minus; exact Hfan).
  assert (Hcarrier : forall x, In x (darts_of (E_minus E d)) <->
                       (In x (darts_of E) /\ x <> d /\ x <> twin d))
    by (intro x; exact (in_darts_of_E_minus_iff E d x Hntwin)).
  assert (Hclos' : forall x, In x (darts_of (E_minus E d)) ->
                     In (fstep (darts_of (E_minus E d)) x) (darts_of (E_minus E d)))
    by (intros x Hx; exact (fstep_in (darts_of (E_minus E d)) x (proj1 Hao') Hx)).
  assert (Hinj' : forall a b, In a (darts_of (E_minus E d)) -> In b (darts_of (E_minus E d)) ->
                    fstep (darts_of (E_minus E d)) a = fstep (darts_of (E_minus E d)) b -> a = b)
    by (exact (fstep_inj (darts_of (E_minus E d)) Hao')).
  assert (Hf'spec : forall x, In x (darts_of (E_minus E d)) ->
            fstep (darts_of (E_minus E d)) x =
              (if dart_eq_dec (fstep (darts_of E) x) d then fstep (darts_of E) (twin d)
               else if dart_eq_dec (fstep (darts_of E) x) (twin d) then fstep (darts_of E) d
               else fstep (darts_of E) x))
    by (intros x Hx; exact (fstep_E_minus_splice E d x Hfan HdE Hntwin Hproper Hx)).
  (* Apply the generic capstone. *)
  unfold num_faces.
  exact (cycle_count_merge dart_eq_dec (fstep (darts_of E)) (darts_of E)
           Hclos Hinj d (twin d) HdS Htwin_in Hdtd Hnsf
           (face_period (darts_of E) d) Hper1_ret Hper1_ge2 Hper1_min
           (face_period (darts_of E) (twin d)) Hper2_ret Hper2_ge2 Hper2_min
           (fstep (darts_of (E_minus E d))) (darts_of (E_minus E d))
           Hcarrier Hclos' Hinj' Hf'spec).
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Combinatorial wiring; allowlist axioms only.                  *)
(* -------------------------------------------------------------------------- *)

Print Assumptions num_faces_E_minus_merge.
