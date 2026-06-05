(* ============================================================================
   NetTopologySuite.Proofs.DartAngularOrder
   ----------------------------------------------------------------------------
   extract_rings_valid R5 / general assembler, slice 2a: the angular comparator
   on darts (docs/extract-rings-proof-structure.md §5 step 1, the cyclic-order
   primitive).

   The half-edge foundation (theories/Dart.v, slice 1) gives the `outgoing v`
   fan of darts based at a vertex.  To define the cyclic `next` (rotational
   successor) the fan must be ORDERED BY ANGLE -- and, per the Azimuth design,
   WITHOUT a materialised `atan2`: a pure half-plane + cross-product
   (`Azimuth.turn_sign`) comparator.

   This slice delivers that comparator and proves it is a STRICT TOTAL ORDER on
   directions in general position (pairwise non-parallel):
     - `dir_lt` orders direction vectors by angle in [0, 2pi) via
       (first-half-plane, then `vcross` sign);
     - `dir_lt_irrefl`, `dir_lt_asym`           : strict;
     - `dir_lt_trans`  (the crux)                : transitive, via the algebraic
       certificate `vcross_chain_cert`
         vy w * vcross u z = vy z * vcross u w + vy u * vcross w z
       (pure `ring`) -- so within a half-plane the cross-sign order is the real
       order of the slopes, and `nra` closes it;
     - `dir_lt_total`                            : total on non-parallel pairs.
   `dart_lt` lifts this to darts via `ddir d = tip - base` (base-independent, so
   it orders any fan regardless of the shared base vertex), with the same four
   order laws.

   DELIBERATELY DEFERRED to later slices: the cyclic `next` = rotational
   successor in `outgoing v` built FROM this order; the `face_of` orbit of
   `next o twin` and its FINITENESS (the `face_orbit_finite` crux of §9).

   Pure 2-D vector arithmetic over `R`; no `Admitted` / `Axiom` / `Parameter`.
   Axioms: only the allowlisted classical-reals decidability pair, inherited via
   the real-order decision used in `first_half_dec`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra Psatz.
From NTS.Proofs Require Import Vec Direction Azimuth Dart.

Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The first half-plane and its sign characterisation.                     *)
(* -------------------------------------------------------------------------- *)

(* A direction is in the FIRST half (angle in [0, pi): the +x axis and the
   open upper half-plane) iff `vy > 0`, or it lies on the positive x-axis
   (`vy = 0` and `vx > 0`).  The two halves partition the nonzero directions
   into [0, pi) and [pi, 2pi). *)
Definition first_half (p : Vec) : Prop :=
  vy p > 0 \/ (vy p = 0 /\ vx p > 0).

Lemma first_half_dec : forall p, {first_half p} + {~ first_half p}.
Proof.
  intros p. unfold first_half.
  destruct (Rlt_dec 0 (vy p)) as [Hy | Hy].
  - left. left. exact Hy.
  - destruct (Req_EM_T (vy p) 0) as [Hy0 | Hy0].
    + destruct (Rlt_dec 0 (vx p)) as [Hx | Hx].
      * left. right. split; [ exact Hy0 | exact Hx ].
      * right. intros [H | [_ H]]; [ lra | lra ].
    + right. intros [H | [H _]]; [ lra | lra ].
Qed.

(* Sign facts fed to `nra`: a first-half direction has `vy >= 0`, and on the
   axis (`vy = 0`) it points in `+x`. *)
Lemma first_half_signs :
  forall p, first_half p -> vy p >= 0 /\ (vy p = 0 -> vx p > 0).
Proof.
  intros p [H | [H0 Hx]].
  - split; [ lra | intros; lra ].
  - split; [ lra | intros; exact Hx ].
Qed.

(* The complementary half (angle in [pi, 2pi)): `vy <= 0`, and on the axis
   (`vy = 0`) it points in `-x` -- provided the direction is nonzero. *)
Lemma not_first_half_signs :
  forall p, p <> vzero -> ~ first_half p ->
    vy p <= 0 /\ (vy p = 0 -> vx p < 0).
Proof.
  intros p Hnz Hnf. unfold first_half in Hnf.
  split.
  - destruct (Rle_or_lt (vy p) 0) as [H | H]; [ exact H | exfalso; apply Hnf; left; lra ].
  - intros Hy0.
    destruct (Rtotal_order (vx p) 0) as [Hx | [Hx | Hx]].
    + exact Hx.
    + exfalso. apply Hnz. apply Vec_eq; cbn; lra.
    + exfalso. apply Hnf. right. split; [ exact Hy0 | exact Hx ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The angular comparator on direction vectors.                            *)
(* -------------------------------------------------------------------------- *)

(* `dir_lt p q`: direction `p` has strictly smaller angle than `q`.  Either `p`
   is in the first half and `q` is not, or they share a half and `q` is CCW of
   `p` (positive `vcross`). *)
Definition dir_lt (p q : Vec) : Prop :=
  (first_half p /\ ~ first_half q)
  \/ (((first_half p /\ first_half q) \/ (~ first_half p /\ ~ first_half q))
      /\ vcross p q > 0).

(* The algebraic engine of transitivity: a pure ring identity tying the three
   pairwise cross-products together through the middle direction's `vy`. *)
Lemma vcross_chain_cert :
  forall u w z : Vec,
    vy w * vcross u z = vy z * vcross u w + vy u * vcross w z.
Proof. intros u w z. unfold vcross. ring. Qed.

Lemma dir_lt_irrefl : forall p, ~ dir_lt p p.
Proof.
  intros p [[H1 H2] | [_ Hc]].
  - contradiction.
  - unfold vcross in Hc. lra.
Qed.

Lemma dir_lt_asym : forall p q, dir_lt p q -> ~ dir_lt q p.
Proof.
  intros p q Hpq Hqp.
  unfold dir_lt in Hpq, Hqp.
  (* `vcross q p = - vcross p q` will kill the same-half/same-half clash. *)
  pose proof (vcross_antisym p q) as Hanti.
  destruct Hpq as [[Hfp Hnfq] | [Hsame Hc]];
  destruct Hqp as [[Hfq Hnfp] | [Hsame' Hc']].
  - contradiction.
  - destruct Hsame' as [[Hq2 _] | [_ Hnp2]]; contradiction.
  - destruct Hsame as [[Hp2 _] | [_ Hnq2]]; contradiction.
  - lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Transitivity.                                                           *)
(* -------------------------------------------------------------------------- *)

(* Same-half transitivity, first (upper) half.  Within a half the cross-sign
   order is the real order of slopes, so `nra` closes it via the certificate;
   strictness needs the endpoints non-parallel (distinct directions). *)
Lemma cross_trans_fh :
  forall u w z,
    first_half u -> first_half w -> first_half z ->
    vcross u w > 0 -> vcross w z > 0 -> vcross u z <> 0 ->
    vcross u z > 0.
Proof.
  intros u w z Hu Hw Hz Huw Hwz Hne.
  apply first_half_signs in Hu as [Huy _].
  apply first_half_signs in Hw as [Hwy Hwb].
  apply first_half_signs in Hz as [Hzy _].
  (* the middle direction is strictly off-axis (else cross u w <= 0) *)
  assert (Hwpos : vy w > 0).
  { destruct (Rtotal_order (vy w) 0) as [H | [H | H]].
    - lra.
    - exfalso. specialize (Hwb H). unfold vcross in Huw. nra.
    - exact H. }
  assert (Hge : vcross u z >= 0).
  { pose proof (vcross_chain_cert u w z) as Hcert. nra. }
  destruct (Rdichotomy (vcross u z) 0 Hne) as [H | H]; lra.
Qed.

(* Same-half transitivity, second (lower) half -- symmetric, signs flipped. *)
Lemma cross_trans_nfh :
  forall u w z,
    u <> vzero -> w <> vzero -> z <> vzero ->
    ~ first_half u -> ~ first_half w -> ~ first_half z ->
    vcross u w > 0 -> vcross w z > 0 -> vcross u z <> 0 ->
    vcross u z > 0.
Proof.
  intros u w z Hnu Hnw Hnz Hu Hw Hz Huw Hwz Hne.
  apply not_first_half_signs in Hu as [Huy _]; [ | exact Hnu ].
  apply not_first_half_signs in Hw as [Hwy Hwb]; [ | exact Hnw ].
  apply not_first_half_signs in Hz as [Hzy _]; [ | exact Hnz ].
  assert (Hwneg : vy w < 0).
  { destruct (Rtotal_order (vy w) 0) as [H | [H | H]].
    - exact H.
    - exfalso. specialize (Hwb H). unfold vcross in Huw. nra.
    - lra. }
  assert (Hge : vcross u z >= 0).
  { pose proof (vcross_chain_cert u w z) as Hcert. nra. }
  destruct (Rdichotomy (vcross u z) 0 Hne) as [H | H]; lra.
Qed.

(* Transitivity of `dir_lt`, for distinct (non-parallel) endpoints.  Of the
   eight half-membership configurations of (p, q, r) only all-first and
   all-second need the cross certificate; the others are immediate or have a
   false hypothesis (`dir_lt` cannot hold against the half ordering). *)
Lemma dir_lt_trans :
  forall p q r,
    p <> vzero -> q <> vzero -> r <> vzero ->
    ~ parallel p r ->
    dir_lt p q -> dir_lt q r -> dir_lt p r.
Proof.
  intros p q r Hp Hq Hr Hnpar Hpq Hqr.
  (* non-parallel endpoints give a nonzero cross-product both ways *)
  assert (Hne : vcross p r <> 0).
  { intros H0. apply Hnpar. apply (proj2 (parallel_iff_vcross_zero _ _)). exact H0. }
  destruct (first_half_dec p) as [Fp | Fp];
  destruct (first_half_dec q) as [Fq | Fq];
  destruct (first_half_dec r) as [Fr | Fr].
  - (* p q r all first half *)
    destruct Hpq as [[_ Hc] | [_ Hpq']]; [ contradiction | ].
    destruct Hqr as [[_ Hc] | [_ Hqr']]; [ contradiction | ].
    right. split; [ left; split; assumption | ].
    apply (cross_trans_fh p q r); assumption.
  - (* T T F : p<q same half, q<r by half split -> p<r by half split *)
    left. split; assumption.
  - (* T F T : q first, r... dir_lt q r impossible (q not first, r first) *)
    exfalso. destruct Hqr as [[Hq' _] | [[ [Hq' _] | [_ Hnr'] ] _]]; contradiction.
  - (* T F F : p first, r not -> p<r by half split *)
    left. split; assumption.
  - (* F T T : dir_lt p q impossible (p not first, q first) *)
    exfalso. destruct Hpq as [[Hp' _] | [[ [Hp' _] | [_ Hq'] ] _]]; contradiction.
  - (* F T F : dir_lt p q impossible *)
    exfalso. destruct Hpq as [[Hp' _] | [[ [Hp' _] | [_ Hq'] ] _]]; contradiction.
  - (* F F T : dir_lt q r impossible (q not first, r first) *)
    exfalso. destruct Hqr as [[Hq' _] | [[ [Hq' _] | [_ Hnr'] ] _]]; contradiction.
  - (* p q r all second half *)
    destruct Hpq as [[Hp' _] | [_ Hpq']]; [ contradiction | ].
    destruct Hqr as [[Hq' _] | [_ Hqr']]; [ contradiction | ].
    right. split; [ right; split; assumption | ].
    apply (cross_trans_nfh p q r); assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Totality on non-parallel pairs.                                         *)
(* -------------------------------------------------------------------------- *)

(* GENERAL POSITION.  The `~ parallel` hypothesis here (and the endpoint
   non-parallelism in `dir_lt_trans`) is exactly the general-position guarantee
   the noded JCT seam supplies: after noding/dedup, no two darts based at a
   vertex share a direction, so the fan's directions are pairwise non-parallel
   and `dir_lt` is a genuine strict total order on it.  Parallel co-directional
   darts are angle-equal (`vcross = 0`), and the order does not separate them --
   which is why totality is stated modulo `~ parallel` rather than on all
   pairs. *)
Lemma dir_lt_total :
  forall p q, ~ parallel p q -> dir_lt p q \/ dir_lt q p.
Proof.
  intros p q Hnpar.
  assert (Hne : vcross p q <> 0).
  { intros H0. apply Hnpar. apply (proj2 (parallel_iff_vcross_zero _ _)). exact H0. }
  pose proof (vcross_antisym p q) as Hanti.
  destruct (first_half_dec p) as [Fp | Fp];
  destruct (first_half_dec q) as [Fq | Fq].
  - (* both first half: decide by cross sign *)
    destruct (Rdichotomy (vcross p q) 0 Hne) as [H | H].
    + right. right. split; [ left; split; assumption | lra ].
    + left.  right. split; [ left; split; assumption | lra ].
  - left. left. split; assumption.
  - right. left. split; assumption.
  - (* both second half: decide by cross sign *)
    destruct (Rdichotomy (vcross p q) 0 Hne) as [H | H].
    + right. right. split; [ right; split; assumption | lra ].
    + left.  right. split; [ right; split; assumption | lra ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  The order lifted to darts (by direction tip - base).                    *)
(* -------------------------------------------------------------------------- *)

(* A dart's direction; base-independent, so `dart_lt` orders any fan of darts
   regardless of which vertex they emanate from. *)
Definition ddir (d : Dart) : Vec := point_diff (dtip d) (dbase d).

Definition dart_lt (d1 d2 : Dart) : Prop := dir_lt (ddir d1) (ddir d2).

(* A dart is PROPER when base <> tip, i.e. its direction is nonzero -- the
   non-degeneracy a fan of real edges satisfies. *)
Definition proper_dart (d : Dart) : Prop := ddir d <> vzero.

Lemma dart_lt_irrefl : forall d, ~ dart_lt d d.
Proof. intros d. apply dir_lt_irrefl. Qed.

Lemma dart_lt_asym : forall d1 d2, dart_lt d1 d2 -> ~ dart_lt d2 d1.
Proof. intros d1 d2. apply dir_lt_asym. Qed.

Lemma dart_lt_trans :
  forall d1 d2 d3,
    proper_dart d1 -> proper_dart d2 -> proper_dart d3 ->
    ~ parallel (ddir d1) (ddir d3) ->
    dart_lt d1 d2 -> dart_lt d2 d3 -> dart_lt d1 d3.
Proof. intros d1 d2 d3. apply dir_lt_trans. Qed.

Lemma dart_lt_total :
  forall d1 d2, ~ parallel (ddir d1) (ddir d2) -> dart_lt d1 d2 \/ dart_lt d2 d1.
Proof. intros d1 d2. apply dir_lt_total. Qed.
