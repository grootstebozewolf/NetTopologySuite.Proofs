(* ==========================================================================
   NumFacesSplice.v

   Cycle-count SPLICE, stage 5: the INSTANTIATION.

   Dual of `NumFacesMerge.num_faces_E_minus_merge` ([EF-2]): the same_face
   case here is a SPLIT (faces +1), the non-same_face case is a MERGE
   (faces -1). Together they close the face-delta half of the Euler
   induction step.

   `PermCycleSplice.cycle_count_surgery` is a generic fact about a permutation cut:
   given a permutation `f` of `S` whose orbit of `d` (minimal period `per`)
   reaches `td` first at index `k` (`2 <= k <= per-2`), the surgered map `f'` on
   `S' = S minus {d, td}` that cross-connects the predecessors of `d` and `td`
   has `cycle_count f' S' = cycle_count f S + 1`.

   Here we instantiate it at the face-step permutation to discharge the single
   residual fact the Euler route (EulerBridge.v) carries:
       num_faces (E_minus E d) = num_faces E + 1
   for a same-face edge.  `f := fstep (darts_of E)`, `S := darts_of E`,
   `td := twin d`, `f' := fstep (darts_of (E_minus E d))`,
   `S' := darts_of (E_minus E d)`, `per := face_period (darts_of E) d`, and `k`
   from `same_face_twin_first_step_index`.  Each `SpliceSpec` hypothesis is
   discharged from the established Dart-layer facts (`fstep_in`/`fstep_inj`,
   `face_period_spec`/`_no_early_return`, `in_darts_of_E_minus_iff`,
   `arrangement_ok_E_minus`, `fstep_E_minus_splice`); the only new step is the
   upper index bound `k <= per-2`, from `no_spurs` applied to `twin d`.

   Pure combinatorial wiring; no `Admitted` / `Axiom` / `Parameter`; allowlist
   axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import List Arith Lia.
From NTS.Proofs Require Import Distance Overlay Dart DartNextSpec DartAngularOrder
                               DartNextSpec DartFace FaceOrbitSep NoShortFaces
                               ExtractFaces EdgeConnectivity EdgeFaceBridge
                               ArrangementEMinus FaceStepRemove MapCounts
                               OrbitCycle PermCycleCount PermCycleSplice.

Import ListNotations.

(* Deleting a same-face edge splits its face: the orbit count rises by one. *)
Lemma num_faces_E_minus_splice : forall (E : list Edge) (d : Dart),
  (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
  no_spurs (darts_of E) ->
  In d E -> ~ In (twin d) E ->
  dbase d <> dtip d ->
  same_face (darts_of E) d (twin d) ->
  num_faces (E_minus E d) = (num_faces E + 1)%nat.
Proof.
  intros E d Hfan Hns HdE Hntwin Hproper Hsf.
  (* The arrangement is well-formed (twin-closed + per-vertex fan_ok). *)
  assert (Hao : arrangement_ok (darts_of E))
    by (split; [ exact (darts_of_closed_under_twin E) | exact Hfan ]).
  assert (HdS : In d (darts_of E))
    by (unfold darts_of; apply in_or_app; left; exact HdE).
  assert (Htwin_in : In (twin d) (darts_of E))
    by (apply darts_of_closed_under_twin; exact HdS).
  (* Period of d's face orbit. *)
  destruct (face_period_spec (darts_of E) Hao d HdS) as [Hper_pos Hper_ret].
  (* First-return index of d to twin d. *)
  destruct (same_face_twin_first_step_index E d Hfan Hns HdS Hsf)
    as [k [Hkrng [Hktd Hkfirst]]].
  (* The upper bound k <= per-2: else twin d would fstep back to d (a spur). *)
  assert (Hkup : (k <= face_period (darts_of E) d - 2)%nat).
  { destruct (Nat.eq_dec k (face_period (darts_of E) d - 1)) as [Hke | Hkne];
      [ exfalso | lia ].
    assert (Hfd : fstep (darts_of E) (twin d) = d).
    { rewrite <- Hktd, Hke.
      rewrite <- (iter_add1 (fstep (darts_of E)) (face_period (darts_of E) d - 1) d).
      replace (face_period (darts_of E) d - 1 + 1)%nat
        with (face_period (darts_of E) d) by lia.
      exact Hper_ret. }
    apply (Hns (twin d) Htwin_in). rewrite twin_involutive. exact Hfd. }
  (* SpliceSpec hypotheses for the (f,S) side. *)
  assert (Hclos : forall x, In x (darts_of E) -> In (fstep (darts_of E) x) (darts_of E))
    by (intros x Hx; exact (fstep_in (darts_of E) x (darts_of_closed_under_twin E) Hx)).
  assert (Hinj : forall a b, In a (darts_of E) -> In b (darts_of E) ->
                   fstep (darts_of E) a = fstep (darts_of E) b -> a = b)
    by (exact (fstep_inj (darts_of E) Hao)).
  assert (Hdtd : d <> twin d).
  { intro He. apply (twin_neq_self d Hproper). symmetry. exact He. }
  assert (Hper_min : forall j, (1 <= j < face_period (darts_of E) d)%nat ->
                       OrbitCycle.iter (fstep (darts_of E)) j d <> d)
    by (intros j Hj; exact (face_period_no_early_return (darts_of E) d j Hao HdS Hj)).
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
  exact (cycle_count_surgery dart_eq_dec (fstep (darts_of E)) (darts_of E)
           Hclos Hinj d (twin d) HdS Hdtd
           (face_period (darts_of E) d) Hper_ret Hper_pos Hper_min
           k Hktd (conj (proj1 Hkrng) Hkup) Hkfirst
           (fstep (darts_of (E_minus E d))) (darts_of (E_minus E d))
           Hcarrier Hclos' Hinj' Hf'spec).
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Combinatorial wiring; allowlist axioms only.                  *)
(* -------------------------------------------------------------------------- *)

Print Assumptions num_faces_E_minus_splice.
