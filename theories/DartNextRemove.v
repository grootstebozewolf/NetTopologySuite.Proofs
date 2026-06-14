(* ==========================================================================
   DartNextRemove.v

   extract_rings_valid R5 / H_bridge Euler route, Rung 3b-xiv: the `next`-reroute.

   How the rotational successor `next` (DartNext.v) changes when exactly ONE dart
   `x0` leaves a fan `F`.  This is the first self-contained sub-step of the
   orbit-count SPLICE that the residual `num_faces (E_minus E d) = num_faces E`
   delta needs (the fan substrate is `ArrangementEMinus` §3).

   Main result:

     next_remove : fan_ok F -> In d F -> In x0 F -> d <> x0 ->
       (forall y, In y F' <-> (In y F /\ y <> x0)) ->
       next F' d = (if dart_eq_dec (next F d) x0 then next F x0 else next F d).

   i.e. removing `x0`, the unique dart whose successor was `x0` skips to `x0`'s
   successor; every other dart keeps its successor.

   Pure angular-order combinatorics over DartNext / DartNextSpec; no `Admitted`
   / `Axiom` / `Parameter`.  Axioms: the allowlisted classical-reals pair only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Vec Direction Azimuth Dart DartAngularOrder
                               DartNext DartNextSpec.

Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  `next` read off from `list_min`.                                        *)
(* -------------------------------------------------------------------------- *)

Lemma next_succ_some : forall F d sd,
  list_min (filter (fun e => dart_ltb d e) F) = Some sd -> next F d = sd.
Proof. intros F d sd H. unfold next. rewrite H. reflexivity. Qed.

Lemma next_succ_none_glob : forall F d g,
  list_min (filter (fun e => dart_ltb d e) F) = None ->
  list_min F = Some g -> next F d = g.
Proof. intros F d g Hs Hg. unfold next. rewrite Hs, Hg. reflexivity. Qed.

(* A list with no members has no minimum. *)
Lemma list_min_no_mem : forall L, (forall y, ~ In y L) -> list_min L = None.
Proof.
  intros [| a l] H; [ reflexivity | ].
  exfalso. apply (H a). left. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Reusable `list_min` facts under a strict total order.                   *)
(* -------------------------------------------------------------------------- *)

(* `list_min` depends only on the element SET (under a strict total order). *)
Lemma list_min_set_invariant : forall L1 L2,
  sto_on L1 -> (forall x, In x L1 <-> In x L2) -> list_min L1 = list_min L2.
Proof.
  intros L1 L2 Hsto1 Hmem.
  assert (Hsto2 : sto_on L2)
    by (apply (sto_on_subset L1 L2 Hsto1); intros x Hx; apply Hmem; exact Hx).
  destruct (list_min L1) as [m1 |] eqn:H1; destruct (list_min L2) as [m2 |] eqn:H2.
  - f_equal.
    assert (Hm1L1 : In m1 L1) by (apply list_min_in; exact H1).
    assert (Hm2L2 : In m2 L2) by (apply list_min_in; exact H2).
    assert (Hm1L2 : In m1 L2) by (apply Hmem; exact Hm1L1).
    assert (Hm2L1 : In m2 L1) by (apply Hmem; exact Hm2L2).
    pose proof (list_min_lb L1 m1 Hsto1 H1 m2 Hm2L1) as Hba.
    pose proof (list_min_lb L2 m2 Hsto2 H2 m1 Hm1L2) as Hab.
    destruct Hsto1 as [_ Hto1].
    destruct (Hto1 m1 m2 Hm1L1 Hm2L1) as [Eq | [Hlt | Hgt]].
    + exact Eq.
    + rewrite Hlt in Hab; discriminate.
    + rewrite Hgt in Hba; discriminate.
  - exfalso. apply list_min_none_iff in H2.
    assert (Hin : In m1 L2) by (apply Hmem; apply list_min_in; exact H1).
    rewrite H2 in Hin. exact Hin.
  - exfalso. apply list_min_none_iff in H1.
    assert (Hin : In m2 L1) by (apply Hmem; apply list_min_in; exact H2).
    rewrite H1 in Hin. exact Hin.
  - reflexivity.
Qed.

(* Removing a NON-minimum element leaves the minimum unchanged. *)
Lemma list_min_remove_non_min : forall F F' m x0,
  sto_on F -> list_min F = Some m -> m <> x0 ->
  (forall y, In y F' <-> (In y F /\ y <> x0)) ->
  list_min F' = Some m.
Proof.
  intros F F' m x0 Hsto Hm Hne Hmem.
  assert (Hsto' : sto_on F')
    by (apply (sto_on_subset F F' Hsto); intros y Hy; apply Hmem in Hy; apply Hy).
  assert (HmF : In m F) by (apply list_min_in; exact Hm).
  assert (HmF' : In m F') by (apply Hmem; split; [ exact HmF | exact Hne ]).
  destruct (list_min F') as [m' |] eqn:H'.
  - f_equal.
    assert (Hm'F' : In m' F') by (apply list_min_in; exact H').
    assert (Hm'F : In m' F) by (apply Hmem in Hm'F'; apply Hm'F').
    pose proof (list_min_lb F m Hsto Hm m' Hm'F) as Hb1.
    pose proof (list_min_lb F' m' Hsto' H' m HmF') as Hb2.
    destruct Hsto as [_ Hto].
    destruct (Hto m m' HmF Hm'F) as [Eq | [Hlt | Hgt]].
    + symmetry; exact Eq.
    + rewrite Hlt in Hb2; discriminate.
    + rewrite Hgt in Hb1; discriminate.
  - exfalso. apply list_min_none_iff in H'. rewrite H' in HmF'. exact HmF'.
Qed.

(* The d-successor set of `F'` = that of `F` minus `x0` (predicate-agnostic). *)
Lemma filter_set_minus : forall (p : Dart -> bool) F F' x0,
  (forall y, In y F' <-> (In y F /\ y <> x0)) ->
  forall y, In y (filter p F') <-> (In y (filter p F) /\ y <> x0).
Proof.
  intros p F F' x0 Hmem y. rewrite !filter_In. split.
  - intros [Hy Hp]. apply Hmem in Hy. destruct Hy as [HyF Hyne].
    split; [ split; [ exact HyF | exact Hp ] | exact Hyne ].
  - intros [[HyF Hp] Hyne]. split; [ apply Hmem; split; assumption | exact Hp ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The reroute.                                                            *)
(* -------------------------------------------------------------------------- *)

Lemma next_remove : forall (F F' : list Dart) (d x0 : Dart),
  fan_ok F -> In d F -> In x0 F -> d <> x0 ->
  (forall y, In y F' <-> (In y F /\ y <> x0)) ->
  next F' d = (if dart_eq_dec (next F d) x0 then next F x0 else next F d).
Proof.
  intros F F' d x0 HF Hd Hx0 Hdx0 Hmem.
  assert (HstoF : sto_on F) by (apply fan_ok_sto; exact HF).
  assert (HdF' : In d F') by (apply Hmem; split; [ exact Hd | exact Hdx0 ]).
  assert (HstoF' : sto_on F')
    by (apply (sto_on_subset F F' HstoF); intros y Hy; apply Hmem in Hy; apply Hy).
  (* the d-successor sets *)
  pose proof (filter_set_minus (fun e => dart_ltb d e) F F' x0 Hmem) as HSmem.
  (* F, F' are nonempty (contain d), so their list_min is Some _ *)
  destruct (list_min F) as [g |] eqn:HLF;
    [ | apply list_min_none_iff in HLF; rewrite HLF in Hd; destruct Hd ].
  destruct (list_min F') as [g' |] eqn:HLF';
    [ | apply list_min_none_iff in HLF'; rewrite HLF' in HdF'; destruct HdF' ].
  destruct (dart_eq_dec (next F d) x0) as [Heq | Hne].
  - (* Branch II : next F d = x0 ; goal next F' d = next F x0 *)
    destruct (list_min (filter (fun e => dart_ltb d e) F)) as [sd |] eqn:HS.
    + (* II.b : list_min (succ d F) = Some sd ; next F d = sd = x0 *)
      assert (Hsd : next F d = sd) by (apply next_succ_some; exact HS).
      assert (Hsdx0 : sd = x0) by (rewrite <- Hsd; exact Heq).
      (* d < x0 : x0 = sd is in the d-successor set *)
      assert (Hx0S : In x0 (filter (fun e => dart_ltb d e) F)).
      { rewrite <- Hsdx0. apply (list_min_in _ _ HS). }
      apply filter_In in Hx0S. destruct Hx0S as [_ Hdx0lt].  (* dart_ltb d x0 = true *)
      (* set-equality: succ x0 F  ==  succ d F'  *)
      assert (Hset : forall y,
        In y (filter (fun e => dart_ltb x0 e) F) <->
        In y (filter (fun e => dart_ltb d e) F')).
      { intro y. rewrite HSmem. rewrite !filter_In. split.
        - intros [HyF Hx0y].  (* x0 < y *)
          assert (Hdy : dart_ltb d y = true).
          { destruct HstoF as [Htr _]. apply (Htr d x0 y Hd Hx0 HyF Hdx0lt Hx0y). }
          assert (Hyne : y <> x0).
          { intros ->. rewrite dart_ltb_irrefl in Hx0y. discriminate. }
          split; [ split; [ exact HyF | exact Hdy ] | exact Hyne ].
        - intros [[HyF Hdy] Hyne].
          (* y in succ d F, y<>x0, and x0 = min(succ d F) => x0 < y *)
          assert (HyS : In y (filter (fun e => dart_ltb d e) F))
            by (apply filter_In; split; [ exact HyF | exact Hdy ]).
          assert (HstoS : sto_on (filter (fun e => dart_ltb d e) F))
            by (apply (sto_on_subset F _ HstoF); intros z Hz; apply filter_In in Hz; apply Hz).
          pose proof (list_min_lb _ x0 HstoS ltac:(rewrite Hsdx0 in HS; exact HS) y HyS) as Hyx0.
          (* dart_ltb y x0 = false ; totality => x0 < y *)
          destruct HstoF as [_ Hto].
          destruct (Hto y x0 HyF Hx0) as [Eq | [Hlt | Hgt]].
          + exfalso. apply Hyne. exact Eq.
          + rewrite Hlt in Hyx0; discriminate.
          + split; [ exact HyF | exact Hgt ]. }
      assert (HstoSx0 : sto_on (filter (fun e => dart_ltb x0 e) F))
        by (apply (sto_on_subset F _ HstoF); intros z Hz; apply filter_In in Hz; apply Hz).
      pose proof (list_min_set_invariant _ _ HstoSx0 Hset) as Hlmeq.
      (* now compute both sides from list_min (succ d F') = list_min (succ x0 F) *)
      destruct (list_min (filter (fun e => dart_ltb d e) F')) as [s |] eqn:HS'.
      * (* next F' d = s ; next F x0 = list_min(succ x0 F) = s *)
        rewrite (next_succ_some F' d s HS').
        rewrite (next_succ_some F x0 s); [ reflexivity | exact Hlmeq ].
      * (* both wrap: next F' d = g', next F x0 = g, and g = g' *)
        assert (Hgx0 : g <> x0).
        { intro Hgeq. subst g.
          pose proof (list_min_lb F x0 HstoF HLF d Hd) as Hdg.
          rewrite Hdx0lt in Hdg. discriminate. }
        pose proof (list_min_remove_non_min F F' g x0 HstoF HLF Hgx0 Hmem) as HE.
        rewrite (next_succ_none_glob F' d g' HS' HLF').
        rewrite (next_succ_none_glob F x0 g);
          [ congruence | exact Hlmeq | exact HLF ].
    + (* II.a : list_min (succ d F) = None ; next F d wraps to g = x0 *)
      assert (Hg : next F d = g) by (apply (next_succ_none_glob F d g HS HLF)).
      assert (Hgx0 : g = x0) by (rewrite <- Hg; exact Heq).
      (* succ d F' is empty too *)
      assert (HS'empty : list_min (filter (fun e => dart_ltb d e) F') = None).
      { apply list_min_no_mem. intros y Hy. apply HSmem in Hy.
        destruct Hy as [Hy _]. apply list_min_none_iff in HS. rewrite HS in Hy. exact Hy. }
      (* x0 = g = global min of F. set-equality: succ x0 F == F' *)
      assert (Hset : forall y,
        In y (filter (fun e => dart_ltb x0 e) F) <-> In y F').
      { intro y. rewrite filter_In, Hmem. split.
        - intros [HyF Hx0y]. split; [ exact HyF | ].
          intros ->. rewrite dart_ltb_irrefl in Hx0y. discriminate.
        - intros [HyF Hyne].
          pose proof (list_min_lb F g HstoF HLF y HyF) as Hyg.  (* dart_ltb y g = false *)
          rewrite Hgx0 in Hyg.  (* dart_ltb y x0 = false *)
          destruct HstoF as [_ Hto].
          destruct (Hto y x0 HyF Hx0) as [Eq | [Hlt | Hgt]].
          + exfalso. apply Hyne. exact Eq.
          + rewrite Hlt in Hyg; discriminate.
          + split; [ exact HyF | exact Hgt ]. }
      assert (HstoSx0 : sto_on (filter (fun e => dart_ltb x0 e) F))
        by (apply (sto_on_subset F _ HstoF); intros z Hz; apply filter_In in Hz; apply Hz).
      pose proof (list_min_set_invariant _ _ HstoSx0 Hset) as Hlmeq.
      (* list_min (succ x0 F) = list_min F' = Some g' *)
      rewrite HLF' in Hlmeq.
      rewrite (next_succ_none_glob F' d g' HS'empty HLF').
      rewrite (next_succ_some F x0 g' Hlmeq). reflexivity.
  - (* Branch I : next F d <> x0 ; goal next F' d = next F d *)
    destruct (list_min (filter (fun e => dart_ltb d e) F)) as [sd |] eqn:HS.
    + (* I.b : next F d = sd <> x0 ; list_min (succ d F') = Some sd *)
      assert (Hsd : next F d = sd) by (apply next_succ_some; exact HS).
      assert (Hsdne : sd <> x0) by (rewrite <- Hsd; exact Hne).
      assert (HstoS : sto_on (filter (fun e => dart_ltb d e) F))
        by (apply (sto_on_subset F _ HstoF); intros z Hz; apply filter_In in Hz; apply Hz).
      pose proof (list_min_remove_non_min _ _ sd x0 HstoS HS Hsdne HSmem) as HS'.
      rewrite (next_succ_some F' d sd HS'). rewrite Hsd. reflexivity.
    + (* I.a : next F d = g <> x0 ; succ d F' empty, wrap, g unchanged *)
      assert (Hg : next F d = g) by (apply (next_succ_none_glob F d g HS HLF)).
      assert (Hgne : g <> x0) by (rewrite <- Hg; exact Hne).
      assert (HS'empty : list_min (filter (fun e => dart_ltb d e) F') = None).
      { apply list_min_no_mem. intros y Hy. apply HSmem in Hy.
        destruct Hy as [Hy _]. apply list_min_none_iff in HS. rewrite HS in Hy. exact Hy. }
      rewrite (next_succ_none_glob F' d g' HS'empty HLF'). rewrite Hg.
      (* goal g' = g *)
      pose proof (list_min_remove_non_min F F' g x0 HstoF HLF Hgne Hmem) as HE.
      rewrite HLF' in HE. injection HE as HE'. exact HE'.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure angular-order combinatorics; allowlist axioms only.      *)
(* -------------------------------------------------------------------------- *)

Print Assumptions list_min_set_invariant.
Print Assumptions next_remove.
