(* ============================================================================
   NetTopologySuite.Proofs.DartNext
   ----------------------------------------------------------------------------
   extract_rings_valid R5 / general assembler, slice 2b: the cyclic `next`
   (rotational successor) on the outgoing dart fan
   (docs/extract-rings-proof-structure.md §5 step 1; docs/dart-next.md).

   Slice 2a (theories/DartAngularOrder.v) proved `dir_lt` / `dart_lt` a strict
   total order on directions in general position -- but as a `Prop`.  To SELECT
   the rotational successor from a fan (a `list Dart`, `Dart.outgoing`) the order
   must be COMPUTABLE.  This slice:

     - reflects the comparator into `bool` (`dir_ltb` / `dart_ltb`) with the
       soundness/completeness bridges `dir_ltb_spec` / `dart_ltb_spec`;
     - defines `list_min` (the `dart_ltb`-minimum of a list) and `next`, the
       rotational successor: the minimal strictly-greater dart in the fan, or
       (wrap-around) the global minimum when `d` is the fan maximum;
     - proves `next` WELL-DEFINED on the fan:
         `next_in`       : the successor stays in the fan (orbit closure),
         `next_base`     : it stays based at the same vertex,
         `next_advances` : while a strictly-greater dart exists, `next` is one
                           (`dart_lt d (next d)`) -- so `next` advances in angle.

   DELIBERATELY DEFERRED (slice 2c): that `next` selects the MINIMAL successor
   (its full rotational-correctness spec, needing transitivity threaded through
   the fold under general position), that it is INJECTIVE / a cyclic permutation
   of the fan, and -- the §9 crux -- FINITENESS of the `face_of` orbit of
   `next o twin`.

   Pure list + order combinatorics over the slice-2a order; no `Admitted` /
   `Axiom` / `Parameter`.  Axioms: the allowlisted classical-reals pair, via the
   real-order decisions reused from slice 2a.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Vec Direction Azimuth Dart DartAngularOrder.

Import ListNotations.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Boolean reflection of the angular comparator.                           *)
(* -------------------------------------------------------------------------- *)

(* The decidable mirror of `dir_lt`, reusing slice 2a's `first_half_dec` and the
   real-order decision on `vcross`.  Cases match `dir_lt` exactly:
     fh p,  fh q  -> vcross p q > 0      (same half, q is CCW of p)
     fh p, ~fh q  -> true                (p in first half, q in second)
    ~fh p,  fh q  -> false               (p in second half, q in first)
    ~fh p, ~fh q  -> vcross p q > 0       (same half, q is CCW of p)            *)
Definition dir_ltb (p q : Vec) : bool :=
  if first_half_dec p then
    if first_half_dec q then (if Rlt_dec 0 (vcross p q) then true else false)
    else true
  else
    if first_half_dec q then false
    else (if Rlt_dec 0 (vcross p q) then true else false).

Lemma dir_ltb_spec : forall p q, dir_ltb p q = true <-> dir_lt p q.
Proof.
  intros p q. unfold dir_ltb, dir_lt.
  destruct (first_half_dec p) as [Fp | Fp];
  destruct (first_half_dec q) as [Fq | Fq].
  - destruct (Rlt_dec 0 (vcross p q)) as [Hc | Hc]; split; intro H.
    + right. split; [ left; split; assumption | lra ].
    + reflexivity.
    + discriminate.
    + destruct H as [[_ Hnf] | [_ Hcc]]; [ contradiction | lra ].
  - split; intro H.
    + left. split; assumption.
    + reflexivity.
  - split; intro H.
    + discriminate.
    + destruct H as [[Hf _] | [[ [Hf _] | [_ Hnf] ] _]]; contradiction.
  - destruct (Rlt_dec 0 (vcross p q)) as [Hc | Hc]; split; intro H.
    + right. split; [ right; split; assumption | lra ].
    + reflexivity.
    + discriminate.
    + destruct H as [[Hf _] | [_ Hcc]]; [ contradiction | lra ].
Qed.

Definition dart_ltb (d1 d2 : Dart) : bool := dir_ltb (ddir d1) (ddir d2).

Lemma dart_ltb_spec : forall d1 d2, dart_ltb d1 d2 = true <-> dart_lt d1 d2.
Proof. intros d1 d2. apply dir_ltb_spec. Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Minimum of a list under the boolean comparator.                         *)
(* -------------------------------------------------------------------------- *)

(* `step` keeps the smaller of the running minimum and the next element. *)
Definition min_step (acc x : Dart) : Dart := if dart_ltb x acc then x else acc.

Definition list_min (l : list Dart) : option Dart :=
  match l with
  | [] => None
  | d0 :: rest => Some (fold_left min_step rest d0)
  end.

(* The fold lands on the seed or somewhere in the list. *)
Lemma fold_min_in :
  forall l d0, fold_left min_step l d0 = d0 \/ In (fold_left min_step l d0) l.
Proof.
  induction l as [| a l IH]; intros d0; cbn.
  - left. reflexivity.
  - destruct (IH (min_step d0 a)) as [Hm | Hm].
    + rewrite Hm. unfold min_step. destruct (dart_ltb a d0).
      * right. left. reflexivity.
      * left. reflexivity.
    + right. right. exact Hm.
Qed.

Lemma list_min_in : forall l m, list_min l = Some m -> In m l.
Proof.
  intros [| d0 rest] m H; cbn in H; [ discriminate | ].
  injection H as <-.
  destruct (fold_min_in rest d0) as [Hm | Hm].
  - rewrite Hm. left. reflexivity.
  - right. exact Hm.
Qed.

Lemma list_min_none_iff : forall l, list_min l = None <-> l = [].
Proof.
  intros [| d0 rest]; cbn; split; intro H; try reflexivity; discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The rotational successor.                                               *)
(* -------------------------------------------------------------------------- *)

(* `next F d`: the minimal dart in `F` strictly greater than `d` in angle; or,
   when `d` is the fan maximum (no strictly-greater dart), the global minimum of
   `F` -- the wrap-around that closes the cycle.

   `F` is meant to be the outgoing fan `Dart.outgoing v D` (all darts based at a
   vertex `v`; see `Dart.in_outgoing` / `Dart.outgoing_base`), so `next` is the
   rotational successor AROUND that vertex.  The face walk of the next slice will
   iterate `next (outgoing (dbase ·) D) o twin`: `twin` crosses an edge to the
   opposite vertex, then `next` turns to the rotationally adjacent outgoing dart,
   and the orbit of that composite is a face boundary (`face_of`).  `next_in` /
   `next_base` below are exactly what keeps that orbit inside the arrangement and
   based at honest vertices. *)
Definition next (F : list Dart) (d : Dart) : Dart :=
  match list_min (filter (fun e => dart_ltb d e) F) with
  | Some e => e
  | None => match list_min F with Some e => e | None => d end
  end.

(* Orbit closure: the successor never leaves the fan. *)
Lemma next_in : forall F d, In d F -> In (next F d) F.
Proof.
  intros F d Hd. unfold next.
  destruct (list_min (filter (fun e => dart_ltb d e) F)) as [e |] eqn:Hf.
  - apply list_min_in in Hf. apply filter_In in Hf. apply Hf.
  - destruct (list_min F) as [e |] eqn:Hg.
    + apply list_min_in in Hg. exact Hg.
    + exact Hd.
Qed.

(* The successor stays based at the vertex. *)
Lemma next_base :
  forall v D d, In d (outgoing v D) -> dbase (next (outgoing v D) d) = v.
Proof.
  intros v D d Hd.
  apply (outgoing_base v D). apply next_in. exact Hd.
Qed.

(* While a strictly-greater dart exists, `next` is one of them: it advances in
   angle (the non-wrap case). *)
Lemma next_advances :
  forall F d,
    (exists e, In e F /\ dart_lt d e) ->
    dart_lt d (next F d).
Proof.
  intros F d [e [HeF Helt]].
  (* the filtered successor set is nonempty, so its min is Some _ *)
  assert (Hin : In e (filter (fun x => dart_ltb d x) F)).
  { apply filter_In. split; [ exact HeF | apply dart_ltb_spec; exact Helt ]. }
  unfold next.
  destruct (list_min (filter (fun x => dart_ltb d x) F)) as [m |] eqn:Hf.
  - apply list_min_in in Hf. apply filter_In in Hf. destruct Hf as [_ Hlt].
    apply dart_ltb_spec. exact Hlt.
  - (* impossible: a nonempty list has a minimum *)
    apply list_min_none_iff in Hf.
    rewrite Hf in Hin. cbn in Hin. contradiction.
Qed.
