(* ============================================================================
   NetTopologySuite.Proofs.CurveLength
   ----------------------------------------------------------------------------
   The corpus-canonical metric-length SPEC (#508 M-LEN-ZOO, ADR-0004;
   CONTEXT.md "Metric length"): the length of a parameterized curve over
   [a, b] is the supremum of the lengths of its inscribed polylines — the
   classical rectifiable length, integration-free.

   The spec is a PREDICATE, not a function:

     is_curve_length g a b L  :=  is_lub (inscribed_len g a b) L

   so no completeness axiom is spent constructing L; each per-type length
   obligation (#508 order: ellipse -> cubic Bezier -> clothoid -> NURBS,
   arc first as the served member) states that its formula SATISFIES the
   spec, at whatever tier it can reach.

   Proven here (the base facts every obligation leans on), all Qed:
     - curve_length_ge_chord  : chord <= L     (the lower sandwich half)
     - curve_length_nonneg    : 0 <= L
     - curve_length_unique    : the spec pins L
     - curve_length_additive  : L(a,c) = L(a,b) + L(b,c)
     - is_curve_length_ext    : pointwise-equal curves carry the same lengths
     - is_curve_length_ext_on : same, with equality required only on [a,b]
       (the spec samples that window; used by piecewise/golden consumers)
     - is_curve_length_shift  : translated parameterizations too (t ↦ g (c+t))
     - is_curve_length_reparam: any weakly monotone map with explicit
       preimages carries lengths over (t ↦ g (φ t)) — the general monotone
       form (ext stays orthogonal; shift also covers a > b)
     - is_curve_length_reflect: t ↦ g (a+b−t) carries the same length
       (the orientation-reversing half; #560 / 508-b)
     - is_curve_length_reparam_anti: reflect ∘ reparam, so weakly
       non-increasing φ with explicit preimages is not a new induction
       — all reparameterization invariances funext-free
     - curve_length_upper_of_chord_modulus (+ polyline_le_of_chord_modulus,
       chain_le) : a chord modulus F on [a,b] telescopes, so L <= F b − F a
       — the one upper-half telescoping every Lipschitz/primitive lane uses

   curve_length_additive is the aggregation theorem behind LENGTH_UNIFIED's
   "CC: sum of member lengths" semantics — before this file that was a
   differential observation only (#508 differential datapoint, 2026-08-22).
   The arc obligation itself (r*theta satisfies is_curve_length for the
   circular-arc parameterization) is the NEXT rung, not this file.

   WITNESS topic: metric · claimId: 508-b · witness: 508-b-reflect
   macro: metric
   lane: proofs
   issue: #560 / #508

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* A parameterized curve.  No continuity is assumed by the spec itself:       *)
(* inscribed polylines and their supremum make sense for any map R -> Point,  *)
(* and each per-type obligation supplies its own parameterization.            *)
(* -------------------------------------------------------------------------- *)

Definition Curve : Type := R -> Point.

(* Length of the polyline that starts at (g t) and visits (g u) for each u
   along ts, in order. *)
Fixpoint polyline_len (g : Curve) (t : R) (ts : list R) : R :=
  match ts with
  | [] => 0
  | u :: tl => dist (g t) (g u) + polyline_len g u tl
  end.

(* ts is a weakly increasing chain of parameters from lo to hi.  Weak
   inequalities: a repeated parameter contributes dist x x = 0, so nothing
   is lost and refinements stay painless. *)
Fixpoint chain (lo : R) (ts : list R) (hi : R) : Prop :=
  match ts with
  | [] => lo <= hi
  | u :: tl => lo <= u /\ chain u tl hi
  end.

(* l is the length of an inscribed polyline of g over [a, b]: interior
   sample parameters ts, endpoints always included. *)
Definition inscribed_len (g : Curve) (a b l : R) : Prop :=
  exists ts, chain a ts b /\ l = polyline_len g a (ts ++ [b]).

(* THE SPEC (#508): L is the metric length of g over [a, b]. *)
Definition is_curve_length (g : Curve) (a b L : R) : Prop :=
  is_lub (inscribed_len g a b) L.

Definition rectifiable (g : Curve) (a b : R) : Prop :=
  exists L, is_curve_length g a b L.

(* -------------------------------------------------------------------------- *)
(* Polyline and chain plumbing.                                               *)
(* -------------------------------------------------------------------------- *)

(* Splitting a polyline at a listed waypoint: an exact decomposition. *)
Lemma polyline_len_app_mid : forall (g : Curve) xs t u ys,
  polyline_len g t (xs ++ u :: ys)
  = polyline_len g t (xs ++ [u]) + polyline_len g u ys.
Proof.
  intros g xs; induction xs as [|v xs IH]; intros t u ys; simpl.
  - lra.
  - rewrite IH. lra.
Qed.

(* Rerouting the final vertex from v to w costs at most dist (g v) (g w):
   the triangle inequality lifted along the polyline. *)
Lemma polyline_len_last_triangle : forall (g : Curve) xs t v w,
  polyline_len g t (xs ++ [w])
  <= polyline_len g t (xs ++ [v]) + dist (g v) (g w).
Proof.
  intros g xs; induction xs as [|u xs IH]; intros t v w; simpl.
  - pose proof (dist_triangle (g t) (g v) (g w)). lra.
  - specialize (IH u v w). lra.
Qed.

(* Chains concatenate through a shared waypoint. *)
Lemma chain_app : forall xs lo mid ys hi,
  chain lo xs mid -> chain mid ys hi -> chain lo (xs ++ mid :: ys) hi.
Proof.
  induction xs as [|u xs IH]; simpl; intros lo mid ys hi H1 H2.
  - split; assumption.
  - destruct H1 as [Hlu H1]. split; [exact Hlu | apply IH; assumption].
Qed.

(* A chain's endpoints are ordered. *)
Lemma chain_le : forall xs lo hi, chain lo xs hi -> lo <= hi.
Proof.
  induction xs as [|u xs IH]; simpl; intros lo hi Hch.
  - exact Hch.
  - destruct Hch as [Hlu Hch]. specialize (IH u hi Hch). lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* The generic upper-half telescoping: a chord MODULUS F — every chord        *)
(* within [a, b] bounded by its F-increment — telescopes over any inscribed   *)
(* polyline, so every metric-length value is at most F b − F a.  Instances:  *)
(* F = K·x for the Lipschitz lanes (circle, ellipse, Bézier control net),    *)
(* F = the elliptic-E primitive for the conditional ellipse tier.            *)
(* -------------------------------------------------------------------------- *)

Lemma polyline_le_of_chord_modulus :
  forall (g : Curve) (F : R -> R) (a b : R) ts t,
  (forall s u, a <= s -> s <= u -> u <= b -> dist (g s) (g u) <= F u - F s) ->
  a <= t -> chain t ts b ->
  polyline_len g t (ts ++ [b]) <= F b - F t.
Proof.
  intros g F a b ts; induction ts as [|u tl IH]; simpl;
    intros t Hmod Hat Hch.
  - pose proof (Hmod t b Hat Hch (Rle_refl b)). lra.
  - destruct Hch as [Htu Hch].
    pose proof (chain_le tl u b Hch) as Hub.
    pose proof (Hmod t u Hat Htu Hub) as Hc.
    assert (Hau : a <= u) by lra.
    specialize (IH u Hmod Hau Hch). lra.
Qed.

Theorem curve_length_upper_of_chord_modulus :
  forall (g : Curve) (F : R -> R) a b L,
  (forall s t, a <= s -> s <= t -> t <= b -> dist (g s) (g t) <= F t - F s) ->
  is_curve_length g a b L ->
  L <= F b - F a.
Proof.
  intros g F a b L Hmod [_ Hlst].
  apply Hlst. intros l (ts & Hch & Hl). subst l.
  apply (polyline_le_of_chord_modulus g F a b ts a Hmod (Rle_refl a) Hch).
Qed.

(* A chain over [lo, hi] splits at any waypoint m of [lo, hi]. *)
Lemma chain_split : forall xs lo m hi,
  lo <= m -> m <= hi -> chain lo xs hi ->
  exists ys zs, xs = ys ++ zs /\ chain lo ys m /\ chain m zs hi.
Proof.
  induction xs as [|u xs IH]; simpl; intros lo m hi Hlom Hmhi Hch.
  - exists [], []. simpl. repeat split; auto.
  - destruct Hch as [Hlu Hch].
    destruct (Rle_dec u m) as [Hum | Hum].
    + destruct (IH u m hi Hum Hmhi Hch) as (ys & zs & Heq & Hy & Hz).
      exists (u :: ys), zs. subst xs. simpl. repeat split; assumption.
    + exists [], (u :: xs). simpl.
      repeat split; try assumption; try reflexivity; lra.
Qed.

(* The two halves of a split partition over-estimate the whole: only the
   seam edge changes, and it changes by a triangle inequality. *)
Lemma polyline_split_le : forall (g : Curve) ys zs a m c,
  polyline_len g a (ys ++ zs ++ [c])
  <= polyline_len g a (ys ++ [m]) + polyline_len g m (zs ++ [c]).
Proof.
  intros g ys zs a m c.
  destruct zs as [|w zs]; simpl.
  - pose proof (polyline_len_last_triangle g ys a m c). lra.
  - rewrite polyline_len_app_mid.
    pose proof (polyline_len_last_triangle g ys a m w). lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Base facts.                                                                *)
(* -------------------------------------------------------------------------- *)

(* The single chord is an inscribed polyline (the empty refinement). *)
Lemma inscribed_chord : forall (g : Curve) a b,
  a <= b -> inscribed_len g a b (dist (g a) (g b)).
Proof.
  intros g a b Hab. exists []. split.
  - exact Hab.
  - simpl. lra.
Qed.

(* Lower sandwich half: no curve is shorter than its chord. *)
Theorem curve_length_ge_chord : forall (g : Curve) a b L,
  a <= b -> is_curve_length g a b L -> dist (g a) (g b) <= L.
Proof.
  intros g a b L Hab [Hub _].
  exact (Hub _ (inscribed_chord g a b Hab)).
Qed.

Theorem curve_length_nonneg : forall (g : Curve) a b L,
  a <= b -> is_curve_length g a b L -> 0 <= L.
Proof.
  intros g a b L Hab HL.
  apply Rle_trans with (dist (g a) (g b)).
  - apply dist_nonneg.
  - exact (curve_length_ge_chord g a b L Hab HL).
Qed.

(* The spec pins its value: lub uniqueness. *)
Theorem curve_length_unique : forall (g : Curve) a b L1 L2,
  is_curve_length g a b L1 -> is_curve_length g a b L2 -> L1 = L2.
Proof.
  intros g a b L1 L2 [Hub1 Hlst1] [Hub2 Hlst2].
  apply Rle_antisym; [apply Hlst1, Hub2 | apply Hlst2, Hub1].
Qed.

(* -------------------------------------------------------------------------- *)
(* Aggregation: length is additive at any waypoint.                           *)
(* -------------------------------------------------------------------------- *)

Theorem curve_length_additive : forall (g : Curve) a b c L1 L2,
  a <= b -> b <= c ->
  is_curve_length g a b L1 -> is_curve_length g b c L2 ->
  is_curve_length g a c (L1 + L2).
Proof.
  intros g a b c L1 L2 Hab Hbc [Hub1 Hlst1] [Hub2 Hlst2].
  split.
  - (* L1 + L2 bounds every inscribed polyline of [a, c]: split its chain
       at b, pay one triangle inequality at the seam. *)
    intros l (ts & Hch & Hl). subst l.
    destruct (chain_split ts a b c Hab Hbc Hch) as (ys & zs & Heq & Hy & Hz).
    subst ts. rewrite <- app_assoc.
    eapply Rle_trans; [apply polyline_split_le with (m := b) |].
    apply Rplus_le_compat.
    + apply Hub1. exists ys. split; [exact Hy | reflexivity].
    + apply Hub2. exists zs. split; [exact Hz | reflexivity].
  - (* Least: any bound M of [a, c] bounds every concatenated pair, and the
       two lub minimalities peel off L1 then L2 — no epsilon needed. *)
    intros M HM.
    assert (Hstep : forall l2, inscribed_len g b c l2 -> L1 <= M - l2).
    { intros l2 (ts2 & Hc2 & Hl2). subst l2.
      apply Hlst1. intros l1 (ts1 & Hc1 & Hl1). subst l1.
      assert (Hin : inscribed_len g a c
        (polyline_len g a (ts1 ++ [b]) + polyline_len g b (ts2 ++ [c]))).
      { exists (ts1 ++ b :: ts2). split.
        - apply chain_app; assumption.
        - rewrite <- app_assoc. simpl. symmetry.
          apply polyline_len_app_mid. }
      specialize (HM _ Hin). lra. }
    assert (HL2 : L2 <= M - L1).
    { apply Hlst2. intros l2 Hl2m. specialize (Hstep _ Hl2m). lra. }
    lra.
Qed.

Print Assumptions curve_length_additive.

(* -------------------------------------------------------------------------- *)
(* Reparameterization invariances (#508 ellipse rung 2 consumers): the spec   *)
(* only sees curves through dist, so pointwise-equal curves and translated    *)
(* parameterizations carry the same lengths.  Both proven without funext.     *)
(* -------------------------------------------------------------------------- *)

Lemma polyline_len_ext : forall (g1 g2 : Curve),
  (forall t, g1 t = g2 t) ->
  forall ts t, polyline_len g1 t ts = polyline_len g2 t ts.
Proof.
  intros g1 g2 Hg ts; induction ts as [|u tl IH]; intro t; simpl.
  - reflexivity.
  - rewrite !Hg, IH. reflexivity.
Qed.

Lemma is_curve_length_ext : forall (g1 g2 : Curve) a b L,
  (forall t, g1 t = g2 t) ->
  is_curve_length g1 a b L -> is_curve_length g2 a b L.
Proof.
  intros g1 g2 a b L Hg [Hub Hlst].
  assert (H21 : forall l, inscribed_len g2 a b l -> inscribed_len g1 a b l).
  { intros l (ts & Hch & Hl). exists ts. split; [exact Hch |].
    rewrite (polyline_len_ext g1 g2 Hg). exact Hl. }
  assert (H12 : forall l, inscribed_len g1 a b l -> inscribed_len g2 a b l).
  { intros l (ts & Hch & Hl). exists ts. split; [exact Hch |].
    rewrite <- (polyline_len_ext g1 g2 Hg). exact Hl. }
  split.
  - intros l Hl. exact (Hub _ (H21 _ Hl)).
  - intros M HM. apply Hlst. intros l Hl. exact (HM _ (H12 _ Hl)).
Qed.

(* Windowed sibling: inscribed polylines only sample [a,b], so pointwise
   equality on that interval is enough.  Lifted from the 508-a golden
   quarter (was a local copy in NurbsConicExact.v). *)
Lemma polyline_len_ext_on :
  forall (g1 g2 : Curve) a b ts t,
    (forall u, a <= u -> u <= b -> g1 u = g2 u) ->
    a <= t -> chain t ts b ->
    polyline_len g1 t (ts ++ [b]) = polyline_len g2 t (ts ++ [b]).
Proof.
  intros g1 g2 a b ts; induction ts as [|u tl IH];
    intros t Hg Hat Hch; simpl.
  - assert (Htb : t <= b) by exact Hch.
    assert (Hab : a <= b) by lra.
    rewrite (Hg t Hat Htb), (Hg b Hab (Rle_refl b)).
    reflexivity.
  - destruct Hch as [Htu Hch].
    pose proof (chain_le tl u b Hch) as Hub.
    assert (Hau : a <= u) by lra.
    rewrite (Hg t Hat ltac:(lra)), (Hg u Hau Hub).
    rewrite (IH u Hg Hau Hch).
    reflexivity.
Qed.

Lemma is_curve_length_ext_on : forall (g1 g2 : Curve) a b L,
  (forall t, a <= t -> t <= b -> g1 t = g2 t) ->
  is_curve_length g1 a b L -> is_curve_length g2 a b L.
Proof.
  intros g1 g2 a b L Hg [Hub Hlst].
  split.
  - intros l (ts & Hch & Hl). subst l.
    apply Hub. exists ts. split; [exact Hch |].
    rewrite <- (polyline_len_ext_on g1 g2 a b ts a Hg (Rle_refl a) Hch).
    reflexivity.
  - intros M HM. apply Hlst. intros l (ts & Hch & Hl). subst l.
    apply HM. exists ts. split; [exact Hch |].
    rewrite (polyline_len_ext_on g1 g2 a b ts a Hg (Rle_refl a) Hch).
    reflexivity.
Qed.

Lemma chain_shift : forall c ts lo hi,
  chain lo ts hi -> chain (c + lo) (map (Rplus c) ts) (c + hi).
Proof.
  intros c ts; induction ts as [|u tl IH]; simpl; intros lo hi Hch.
  - lra.
  - destruct Hch as [Hlu Hch]. split; [lra | exact (IH u hi Hch)].
Qed.

Lemma map_shift_cancel : forall c ts,
  map (Rplus c) (map (Rplus (- c)) ts) = ts.
Proof.
  intros c ts; induction ts as [|u tl IH]; simpl.
  - reflexivity.
  - rewrite IH. f_equal. ring.
Qed.

(* The general form: polylines compose through any parameter map. *)
Lemma polyline_len_compose : forall (g : Curve) (phi : R -> R) ts t,
  polyline_len (fun u => g (phi u)) t ts
  = polyline_len g (phi t) (map phi ts).
Proof.
  intros g phi ts; induction ts as [|u tl IH]; intro t; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma polyline_len_shift : forall (g : Curve) c ts t,
  polyline_len (fun u => g (c + u)) t ts
  = polyline_len g (c + t) (map (Rplus c) ts).
Proof.
  intros g c ts t. exact (polyline_len_compose g (Rplus c) ts t).
Qed.

Lemma is_curve_length_shift : forall (g : Curve) c a b L,
  is_curve_length g (c + a) (c + b) L ->
  is_curve_length (fun t => g (c + t)) a b L.
Proof.
  intros g c a b L [Hub Hlst].
  split.
  - intros l (ts & Hch & Hl). subst l.
    apply Hub. exists (map (Rplus c) ts). split.
    + exact (chain_shift c ts a b Hch).
    + rewrite polyline_len_shift, map_app. reflexivity.
  - intros M HM. apply Hlst. intros l (ts & Hch & Hl). subst l.
    apply HM.
    exists (map (Rplus (- c)) ts). split.
    + pose proof (chain_shift (- c) ts (c + a) (c + b) Hch) as H.
      replace (- c + (c + a)) with a in H by ring.
      replace (- c + (c + b)) with b in H by ring.
      exact H.
    + rewrite polyline_len_shift, map_app, map_shift_cancel. reflexivity.
Qed.

Print Assumptions is_curve_length_shift.

(* -------------------------------------------------------------------------- *)
(* Monotone reparameterization invariance (#508): the spec only sees ordered  *)
(* samples through dist, so composing with a weakly monotone map that covers  *)
(* the target window carries metric lengths over.  With ext and shift this    *)
(* completes the invariance kit; the intended consumer is the conic exact     *)
(* tier (the rational quarter circle re-parameterized onto the angular arc).  *)
(* The surjectivity premise asks for an EXPLICIT preimage (no IVT machinery); *)
(* weak monotonicity suffices — flat stretches are handled by reusing the     *)
(* previous preimage when consecutive samples coincide.  Both directions     *)
(* hold under the same premises (the inscribed sets correspond both ways),   *)
(* so the transfer is an equivalence.  Orientation-REVERSING maps (t ↦ 1−t,  *)
(* an arc run backwards) are the next block: is_curve_length_reflect, then   *)
(* is_curve_length_reparam_anti = reflect ∘ reparam.  ext and shift stay     *)
(* independent — they are not instances of either form.                      *)
(* -------------------------------------------------------------------------- *)

Lemma chain_map_mono : forall (phi : R -> R) a b,
  (forall s t, a <= s -> s <= t -> t <= b -> phi s <= phi t) ->
  forall ts lo,
    a <= lo -> chain lo ts b ->
    chain (phi lo) (map phi ts) (phi b).
Proof.
  intros phi a b Hmono ts; induction ts as [|u tl IH]; simpl;
    intros lo Halo Hch.
  - apply Hmono; lra.
  - destruct Hch as [Hlu Hch].
    pose proof (chain_le tl u b Hch) as Hub'.
    split.
    + apply Hmono; lra.
    + apply IH; [lra | exact Hch].
Qed.

Lemma reparam_preimage_chain : forall (phi : R -> R) a b,
  (forall s t, a <= s -> s <= t -> t <= b -> phi s <= phi t) ->
  (forall v, phi a <= v -> v <= phi b ->
     exists u, a <= u /\ u <= b /\ phi u = v) ->
  forall us t0,
    a <= t0 -> t0 <= b ->
    chain (phi t0) us (phi b) ->
    exists ts, chain t0 ts b /\ map phi ts = us.
Proof.
  intros phi a b Hmono Hsurj us;
    induction us as [|v tl IH]; simpl; intros t0 Ha0 Hb0 Hch.
  - exists []. simpl. split; [exact Hb0 | reflexivity].
  - destruct Hch as [Hlov Hch].
    assert (Hvb : v <= phi b) by (apply (chain_le tl); exact Hch).
    assert (Hav : phi a <= v).
    { assert (phi a <= phi t0) by (apply Hmono; lra). lra. }
    destruct (Hsurj v Hav Hvb) as (t1 & Ht1a & Ht1b & Hphit1).
    destruct (Rle_dec t0 t1) as [Hle | Hgt].
    + (* the fresh preimage sits past t0: use it *)
      assert (Hch1 : chain (phi t1) tl (phi b))
        by (rewrite Hphit1; exact Hch).
      destruct (IH t1 Ht1a Ht1b Hch1) as (ts & Hchts & Hmap).
      exists (t1 :: ts). simpl. split.
      * split; [exact Hle | exact Hchts].
      * rewrite Hmap, Hphit1. reflexivity.
    + (* flat stretch: phi t0 = v already, reuse t0 *)
      assert (Hveq : v = phi t0).
      { assert (phi t1 <= phi t0) by (apply Hmono; lra). lra. }
      assert (Hch0 : chain (phi t0) tl (phi b))
        by (rewrite <- Hveq; exact Hch).
      destruct (IH t0 Ha0 Hb0 Hch0) as (ts & Hchts & Hmap).
      exists (t0 :: ts). simpl. split.
      * split; [lra | exact Hchts].
      * rewrite Hmap, <- Hveq. reflexivity.
Qed.

(* WITNESS {"claimId":"curvelength-is-curve-length-reparam","topic":"metric","lemma":"is_curve_length_reparam","title":"Metric length is invariant under weakly monotone reparameterization with explicit preimages","file":"theories/CurveLength.v"} *)

Theorem is_curve_length_reparam : forall (g : Curve) (phi : R -> R) a b L,
  a <= b ->
  (forall s t, a <= s -> s <= t -> t <= b -> phi s <= phi t) ->
  (forall v, phi a <= v -> v <= phi b ->
     exists u, a <= u /\ u <= b /\ phi u = v) ->
  is_curve_length g (phi a) (phi b) L ->
  is_curve_length (fun t => g (phi t)) a b L.
Proof.
  intros g phi a b L Hab Hmono Hsurj [Hub Hlst].
  split.
  - intros l (ts & Hch & Hl). subst l.
    apply Hub.
    exists (map phi ts). split.
    + exact (chain_map_mono phi a b Hmono ts a (Rle_refl a) Hch).
    + rewrite (polyline_len_compose g phi (ts ++ [b]) a), map_app.
      reflexivity.
  - intros M HM. apply Hlst. intros l (us & Hch & Hl). subst l.
    destruct (reparam_preimage_chain phi a b Hmono Hsurj us a
                (Rle_refl a) Hab Hch) as (ts & Hchts & Hmap).
    apply HM.
    exists ts. split; [exact Hchts |].
    rewrite (polyline_len_compose g phi (ts ++ [b]) a), map_app, Hmap.
    reflexivity.
Qed.

(* The converse holds under the same premises: the two inscribed-set
   correspondences above are used with the roles swapped, so the transfer
   is an equivalence. *)
Corollary is_curve_length_reparam_inv : forall (g : Curve) (phi : R -> R) a b L,
  a <= b ->
  (forall s t, a <= s -> s <= t -> t <= b -> phi s <= phi t) ->
  (forall v, phi a <= v -> v <= phi b ->
     exists u, a <= u /\ u <= b /\ phi u = v) ->
  is_curve_length (fun t => g (phi t)) a b L ->
  is_curve_length g (phi a) (phi b) L.
Proof.
  intros g phi a b L Hab Hmono Hsurj [Hub Hlst].
  split.
  - intros l (us & Hch & Hl). subst l.
    destruct (reparam_preimage_chain phi a b Hmono Hsurj us a
                (Rle_refl a) Hab Hch) as (ts & Hchts & Hmap).
    apply Hub.
    exists ts. split; [exact Hchts |].
    rewrite (polyline_len_compose g phi (ts ++ [b]) a), map_app, Hmap.
    reflexivity.
  - intros M HM. apply Hlst. intros l (ts & Hch & Hl). subst l.
    apply HM.
    exists (map phi ts). split.
    + exact (chain_map_mono phi a b Hmono ts a (Rle_refl a) Hch).
    + rewrite (polyline_len_compose g phi (ts ++ [b]) a), map_app.
      reflexivity.
Qed.

Print Assumptions is_curve_length_reparam.
Print Assumptions is_curve_length_reparam_inv.

(* -------------------------------------------------------------------------- *)
(* Orientation-reversing reparameterization (#560 / 508-b): reflection        *)
(* ρ(t) = a+b−t sends a chain of [a,b] to the reversed chain.  polyline_len   *)
(* of a reversed visit equals the original by dist_sym (rev induction).       *)
(* A weakly non-increasing φ is then reflection ∘ a non-decreasing ψ, so      *)
(* is_curve_length_reparam_anti reuses reparam_preimage_chain rather than     *)
(* re-proving the order-repair induction.  ext and shift stay independent.    *)
(* -------------------------------------------------------------------------- *)

Definition reflect (a b t : R) : R := a + b - t.

Lemma reflect_invo : forall a b t, reflect a b (reflect a b t) = t.
Proof. intros a b t. unfold reflect. ring. Qed.

Lemma reflect_left : forall a b, reflect a b a = b.
Proof. intros a b. unfold reflect. ring. Qed.

Lemma reflect_right : forall a b, reflect a b b = a.
Proof. intros a b. unfold reflect. ring. Qed.

Lemma reflect_anti : forall a b s t,
  s <= t -> reflect a b t <= reflect a b s.
Proof. intros a b s t H. unfold reflect. lra. Qed.

Lemma map_reflect_invo : forall a b ts,
  map (reflect a b) (map (reflect a b) ts) = ts.
Proof.
  intros a b ts; induction ts as [|u tl IH]; simpl.
  - reflexivity.
  - rewrite IH, reflect_invo. reflexivity.
Qed.

Lemma map_rev_reflect : forall a b ts,
  map (reflect a b) (rev ts) = rev (map (reflect a b) ts).
Proof.
  intros a b ts; induction ts as [|u tl IH]; simpl.
  - reflexivity.
  - rewrite map_app, IH. reflexivity.
Qed.

(* Snoc form: a chain that ends by visiting m, then stepping to hi. *)
Lemma chain_snoc : forall xs lo m hi,
  chain lo xs m -> m <= hi -> chain lo (xs ++ [m]) hi.
Proof.
  induction xs as [|u xs IH]; simpl; intros lo m hi Hch Hmh.
  - split; assumption.
  - destruct Hch as [Hlu Hch]. split; [exact Hlu | apply IH; assumption].
Qed.

(* Weakly antitone image of a chain, reversed, is a chain. *)
Lemma chain_map_anti : forall (phi : R -> R) a b,
  (forall s t, a <= s -> s <= t -> t <= b -> phi t <= phi s) ->
  forall ts lo,
    a <= lo -> chain lo ts b ->
    chain (phi b) (rev (map phi ts)) (phi lo).
Proof.
  intros phi a b Hanti ts; induction ts as [|u tl IH]; simpl;
    intros lo Halo Hch.
  - apply Hanti; lra.
  - destruct Hch as [Hlu Hch].
    pose proof (chain_le tl u b Hch) as Hub'.
    apply chain_snoc.
    + apply (IH u); [lra | exact Hch].
    + apply (Hanti lo u); lra.
Qed.

(* (xs ++ [x]) ++ [y] = xs ++ x :: [y], proved by induction so we never
   fight app_assoc's association. *)
Lemma app_snoc_cons : forall (A : Type) (xs : list A) (x y : A),
  (xs ++ [x]) ++ [y] = xs ++ x :: [y].
Proof.
  intros A xs x y; induction xs as [|z zs IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* Reversing the visit order preserves polyline length (dist is symmetric). *)
Lemma polyline_len_rev : forall (g : Curve) ts t u,
  polyline_len g t (ts ++ [u]) = polyline_len g u (rev ts ++ [t]).
Proof.
  intros g ts; induction ts as [|v tl IH]; intros t u.
  - simpl. rewrite dist_sym. reflexivity.
  - replace ((v :: tl) ++ [u]) with (v :: tl ++ [u]) by reflexivity.
    simpl polyline_len.
    rewrite IH.
    change (rev (v :: tl)) with (rev tl ++ [v]).
    rewrite (app_snoc_cons R (rev tl) v t).
    rewrite (polyline_len_app_mid g (rev tl) u v [t]).
    simpl polyline_len.
    rewrite dist_sym, Rplus_0_r.
    apply Rplus_comm.
Qed.

Lemma inscribed_len_reflect : forall (g : Curve) a b l,
  inscribed_len (fun t => g (reflect a b t)) a b l <->
  inscribed_len g a b l.
Proof.
  intros g a b l. split.
  - intros (ts & Hch & Hl).
    exists (rev (map (reflect a b) ts)). split.
    + pose proof (chain_map_anti (reflect a b) a b
                    (fun s t Hs Hst Ht => reflect_anti a b s t Hst)
                    ts a (Rle_refl a) Hch) as Hrev.
      rewrite reflect_right, reflect_left in Hrev. exact Hrev.
    + rewrite Hl.
      rewrite (polyline_len_compose g (reflect a b) (ts ++ [b]) a).
      rewrite map_app. simpl. rewrite reflect_left, reflect_right.
      rewrite (polyline_len_rev g (map (reflect a b) ts) b a).
      reflexivity.
  - intros (ts & Hch & Hl).
    exists (rev (map (reflect a b) ts)). split.
    + pose proof (chain_map_anti (reflect a b) a b
                    (fun s t Hs Hst Ht => reflect_anti a b s t Hst)
                    ts a (Rle_refl a) Hch) as Hrev.
      rewrite reflect_right, reflect_left in Hrev. exact Hrev.
    + rewrite Hl.
      rewrite (polyline_len_compose g (reflect a b)
                 (rev (map (reflect a b) ts) ++ [b]) a).
      rewrite map_app. simpl. rewrite reflect_left, reflect_right.
      rewrite map_rev_reflect, map_reflect_invo.
      rewrite <- (polyline_len_rev g ts a b).
      reflexivity.
Qed.

(* WITNESS {"claimId":"508-b","topic":"metric","lemma":"is_curve_length_reflect","title":"Metric length is invariant under parameter reflection t ↦ a+b−t","file":"theories/CurveLength.v","witness":"508-b-reflect","board":"#560"} *)

Theorem is_curve_length_reflect : forall (g : Curve) (a b L : R),
  is_curve_length g a b L ->
  is_curve_length (fun t => g (a + b - t)) a b L.
Proof.
  intros g a b L [Hub Hlst].
  split.
  - intros l Hl. apply Hub. apply inscribed_len_reflect. exact Hl.
  - intros M HM. apply Hlst. intros l Hl. apply HM.
    apply inscribed_len_reflect. exact Hl.
Qed.

(* A weakly non-increasing φ with explicit preimages is reflection of a
   weakly non-decreasing ψ(t) := φ(a+b−t).  The preimage-chain order-repair
   is reused via is_curve_length_reparam; this is not a new induction. *)
Corollary is_curve_length_reparam_anti :
  forall (g : Curve) (phi : R -> R) a b L,
    a <= b ->
    (forall s t, a <= s -> s <= t -> t <= b -> phi t <= phi s) ->
    (forall v, phi b <= v -> v <= phi a ->
       exists u, a <= u /\ u <= b /\ phi u = v) ->
    is_curve_length g (phi b) (phi a) L ->
    is_curve_length (fun t => g (phi t)) a b L.
Proof.
  intros g phi a b L Hab Hanti Hsurj HL.
  set (rho := fun t => a + b - t).
  set (psi := fun t => phi (rho t)).
  assert (Hmono : forall s t, a <= s -> s <= t -> t <= b -> psi s <= psi t).
  { intros s t Hs Hst Ht. unfold psi, rho. apply Hanti; lra. }
  assert (Hsurj' : forall v, psi a <= v -> v <= psi b ->
                    exists u, a <= u /\ u <= b /\ psi u = v).
  { intros v Hv1 Hv2.
    unfold psi, rho in Hv1, Hv2.
    replace (a + b - a) with b in Hv1 by ring.
    replace (a + b - b) with a in Hv2 by ring.
    destruct (Hsurj v Hv1 Hv2) as (w & Hwa & Hwb & Hph).
    exists (a + b - w). split; [lra | split; [lra |]].
    unfold psi, rho. replace (a + b - (a + b - w)) with w by ring.
    exact Hph. }
  assert (Hpsi : is_curve_length (fun t => g (psi t)) a b L).
  { apply (is_curve_length_reparam g psi a b L Hab Hmono Hsurj').
    unfold psi, rho.
    replace (a + b - a) with b by ring.
    replace (a + b - b) with a by ring.
    exact HL. }
  apply is_curve_length_reflect in Hpsi.
  eapply is_curve_length_ext; [| exact Hpsi].
  intros t. unfold psi, rho.
    replace (a + b - (a + b - t)) with t by ring.
    reflexivity.
Qed.

Print Assumptions is_curve_length_reflect.
Print Assumptions is_curve_length_reparam_anti.
