(* AlpogeTopShape.v -- the TopShape link facts of the claimed RH/GRH Lean
   development (CocoSgt/riemann-hypothesis-lean @ 7cbf7a0), REFINED.

   AlpogeSixthBatch.v refines TopG (ShapeWin.lean : shapeWin) with three
   inventory hypotheses: link_ex, a bundle `links`, and topDesWin.  This
   file opens that bundle and replays the proofs read from source:

     LinkEx.lean                         link_ex
     DesignExistsOfChoices.lean          designExists_of_choices
     LinkGl.lean                         link_gl
     LinkEta.lean                        link_eta
     LinkG.lean                          link_g
     LinkBrest.lean                      link_brest (the call bRest_all)
     LinkAlt.lean                        link_alt (the call theoremS_transport)
     LinkIRROfJoinEx.lean                link_irr (the outer Closed algebra;
                                         sizesRec_at stays inventory)
     ClosedFamilyAdmissibleTwistLink.lean
     SelectionClosedOfWuDecay.lean
     SmallLevelRankEqClosedOfLevelProjectionSurjective.lean
     DesWin.lean                         topDesWin
     ShapeWin.lean                       the hsub / hBR wiring into TopG

   Closed-class algebra (of_class, and, imp, sub), the bounds 3 <= 3,
   0 < 3, 0 <= 2 and exp 1 <= 3, the subclass projections and the
   wiring are proved.  Arithmetic calls are named hypotheses, tagged
   [Mathlib] or [inventory].  Definitions marked "reading" are not
   claimed to be the Lean types.  askExp is not part of this link.

   The assembly concludes AlpogeDeepStatements.TopG.  This is not a
   proof of RH.  Within docs/axiom-allowlist.txt.  No Admitted.

   Evidence for docs/attacks/2026-11-22-alpoge-topshape.md.
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude (Cursor Grok 4.7)
*)
From Stdlib Require Import Reals Lra Psatz.
From NTS.Proofs.Probes Require Import AlpogeDeepStatements.
Local Open Scope R_scope.

Section TopShapeLinks.
Variable Ranks : Type.
Variable Host : Ranks -> Type.
Variable HostCT2 : forall Rk, Host Rk -> R.
Variable RankVal : Scale -> Ranks -> Prop.
Variable HostGood : Scale -> R -> R -> R -> R -> forall Rk, Host Rk -> nat -> Prop.
Variable FamP : R -> Type.
Variable fx1 : forall eps, FamP eps -> R.
Variable fIx : forall eps, FamP eps -> R -> Type.
Variable fWin : forall eps, FamP eps -> R -> Prop.
Variable ChainTied : forall eps, FamP eps -> R -> R -> R -> R -> R -> R -> R -> Prop.
Variable VV : forall eps (Fm : FamP eps) x, fIx eps Fm x -> Prop.
Variable FReq : Type.
Variable req : FReq -> HostReq Ranks Host.
Variable At : FReq -> forall eps (Fm : FamP eps) x, fIx eps Fm x -> Prop.

Local Notation FamCl := (forall eps, FamP eps -> Prop).
Local Notation HEW := (HostExW Ranks Host HostCT2 RankVal HostGood).
Local Notation Cls := (cls FamP fx1 fIx fWin FReq At).
Definition hv {eps : R} (Fm : FamP eps) : Prop := @HypV FamP fIx VV eps Fm.
Local Notation FCC := (FamilyClassConnected FamP fWin ChainTied).
Local Notation TG := (TopG Ranks Host HostCT2 RankVal HostGood FamP fx1 fIx fWin ChainTied VV FReq req At).

(* reading: Lean's CH.  A real in DesignChoices; an index in the link facts. *)
Variable Chan : forall eps, FamP eps -> Type.
(* reading: the Large token designExists_of_choices splits into hL1 / hL2
   and that topDesWin passes to the closed eliminator.  One predicate
   stands for that token. *)
Variable Side : forall eps, FamP eps -> Prop.

Definition CPred := forall eps (Fm : FamP eps) (ch : Chan eps Fm), Prop.

(* Pk.Closed at the eliminator used by designExists_of_choices (`e <= ε`)
   and by topDesWin (`hK Fm CH mem hL`). *)
Definition Closed (C : FamCl) (P : CPred) : Prop :=
  exists e, 0 < e /\ forall eps, 0 < eps -> eps <= e ->
    exists _page : R, forall (Fm : FamP eps) (ch : Chan eps Fm),
      C eps Fm -> Side eps Fm -> P eps Fm ch.

Definition sub (B C : FamCl) : Prop := forall eps (Fm : FamP eps), B eps Fm -> C eps Fm.

Lemma shrink2 : forall a b, 0 < a -> 0 < b ->
  exists c, 0 < c /\ c <= a /\ c <= b.
Proof.
  intros a b Ha Hb.
  set (c := a * b / (a + b)).
  assert (Hs : 0 < a + b) by lra.
  assert (Hp : 0 < a * b) by (apply Rmult_lt_0_compat; assumption).
  assert (Hc0 : 0 < c) by (unfold c; apply Rdiv_lt_0_compat; assumption).
  assert (Hca : c * (a + b) = a * b) by (unfold c; field; lra).
  assert (Hlt_a : c < a).
  { apply Rmult_lt_reg_r with (a + b); [exact Hs|].
    rewrite Hca. apply Rmult_lt_compat_l; lra. }
  assert (Hlt_b : c < b).
  { apply Rmult_lt_reg_r with (a + b); [exact Hs|].
    rewrite Hca.
    replace (b * (a + b)) with (a * b + b * b) by ring.
    rewrite <- (Rplus_0_r (a * b)) at 1.
    apply Rplus_lt_compat_l. apply Rmult_lt_0_compat; lra. }
  exists c. split; [exact Hc0|]. split; apply Rlt_le; assumption.
Qed.

Lemma closed_of_class : forall (C : FamCl) (P : CPred),
  (forall eps Fm, C eps Fm -> forall ch, P eps Fm ch) -> Closed C P.
Proof.
  intros C P H. exists 1. split; [lra|].
  intros eps H0 Hle. exists 0. intros Fm ch HC _. apply H. exact HC.
Qed.

Lemma closed_and : forall C P Q, Closed C P -> Closed C Q ->
  Closed C (fun eps Fm ch => P eps Fm ch /\ Q eps Fm ch).
Proof.
  intros C P Q [e1 [He1 H1]] [e2 [He2 H2]].
  destruct (shrink2 e1 e2 He1 He2) as [c [Hc [Hc1 Hc2]]].
  exists c. split; [exact Hc|].
  intros eps H0 Hle.
  destruct (H1 eps H0 (Rle_trans _ _ _ Hle Hc1)) as [k1 Hk1].
  destruct (H2 eps H0 (Rle_trans _ _ _ Hle Hc2)) as [k2 Hk2].
  exists k1. intros Fm ch HC HS. split; [apply Hk1|apply Hk2]; assumption.
Qed.

Lemma closed_imp : forall C P Q, Closed C P ->
  (forall eps Fm ch, C eps Fm -> P eps Fm ch -> Q eps Fm ch) -> Closed C Q.
Proof.
  intros C P Q [e [He H]] HQ.
  exists e. split; [exact He|].
  intros eps H0 Hle. destruct (H eps H0 Hle) as [k Hk].
  exists k. intros Fm ch HC HS. apply HQ; [exact HC|]. apply Hk; assumption.
Qed.

(* same arrow, with the scale `0 < eps` that the eliminator already has *)
Lemma closed_imp_eps : forall C P Q, Closed C P ->
  (forall eps Fm ch, 0 < eps -> C eps Fm -> P eps Fm ch -> Q eps Fm ch) -> Closed C Q.
Proof.
  intros C P Q [e [He H]] HQ.
  exists e. split; [exact He|].
  intros eps H0 Hle. destruct (H eps H0 Hle) as [k Hk].
  exists k. intros Fm ch HC HS. apply HQ; [exact H0|exact HC|]. apply Hk; assumption.
Qed.

Lemma closed_sub : forall B C P, Closed C P -> sub B C -> Closed B P.
Proof.
  intros B C P [e [He H]] HB.
  exists e. split; [exact He|].
  intros eps H0 Hle. destruct (H eps H0 Hle) as [k Hk].
  exists k. intros Fm ch HC HS. apply Hk; [apply HB|]; assumption.
Qed.

Lemma closed_9 : forall C P1 P2 P3 P4 P5 P6 P7 P8 P9,
  Closed C P1 -> Closed C P2 -> Closed C P3 -> Closed C P4 -> Closed C P5 ->
  Closed C P6 -> Closed C P7 -> Closed C P8 -> Closed C P9 ->
  Closed C (fun eps Fm ch =>
    P1 eps Fm ch /\ P2 eps Fm ch /\ P3 eps Fm ch /\ P4 eps Fm ch /\
    P5 eps Fm ch /\ P6 eps Fm ch /\ P7 eps Fm ch /\ P8 eps Fm ch /\ P9 eps Fm ch).
Proof.
  intros C P1 P2 P3 P4 P5 P6 P7 P8 P9 H1 H2 H3 H4 H5 H6 H7 H8 H9.
  apply (closed_and _ _ _ H1).
  apply (closed_and _ _ _ H2).
  apply (closed_and _ _ _ H3).
  apply (closed_and _ _ _ H4).
  apply (closed_and _ _ _ H5).
  apply (closed_and _ _ _ H6).
  apply (closed_and _ _ _ H7).
  apply (closed_and _ _ _ H8).
  exact H9.
Qed.

Variable ChN Sm Tw : forall eps, FamP eps -> Prop.
Variable TuSize DGamSize : forall eps, FamP eps -> Prop.

Definition cap (B C : FamCl) : FamCl := fun eps Fm => B eps Fm /\ C eps Fm.
Definition WithChN (E : FamCl) : FamCl := fun eps Fm => E eps Fm /\ ChN eps Fm.
Definition WithSm (E : FamCl) : FamCl := fun eps Fm => E eps Fm /\ Sm eps Fm.
Definition WithTw (E : FamCl) : FamCl := fun eps Fm => E eps Fm /\ Tw eps Fm.

(* reading: Des C C0, channel split out into Chan.  D3 3 A is defined as
   Des (WithChN A) because shapeWin passes link_eta A where topDesWin
   expects a fact on Des (WithChN A). *)
Definition Des (C : FamCl) : FamCl :=
  fun eps Fm => WithTw (WithSm C) eps Fm /\ TuSize eps Fm /\ DGamSize eps Fm.
Definition D3 (A : FamCl) : FamCl := Des (WithChN A).

Lemma hsub_base : forall E eps Fm, WithTw (WithSm (WithChN E)) eps Fm -> E eps Fm.
Proof.
  intros E eps Fm H.
  destruct H as [Hsm _]. destruct Hsm as [Hch _]. destruct Hch as [HE _]. exact HE.
Qed.

Lemma hsub_cls : forall (A B : FamCl) eps Fm,
  WithTw (WithSm (WithChN (cap A B))) eps Fm ->
  WithTw (WithSm (WithChN A)) eps Fm.
Proof.
  intros A B eps Fm H.
  destruct H as [Hsm Htw]. destruct Hsm as [Hch HsmF]. destruct Hch as [Hcap HchF].
  destruct Hcap as [HA _].
  split; [split; [split; [exact HA|exact HchF]|exact HsmF]|exact Htw].
Qed.

Lemma d3_tu : forall A eps Fm, D3 A eps Fm -> TuSize eps Fm.
Proof. intros A eps Fm H. exact (proj1 (proj2 H)). Qed.
Lemma d3_dg : forall A eps Fm, D3 A eps Fm -> DGamSize eps Fm.
Proof. intros A eps Fm H. exact (proj2 (proj2 H)). Qed.
Lemma d3_a : forall A eps Fm, D3 A eps Fm -> A eps Fm.
Proof. intros A eps Fm H. apply (hsub_base A). exact (proj1 H). Qed.

Lemma des_mk : forall (C : FamCl) eps Fm,
  C eps Fm -> Sm eps Fm -> Tw eps Fm -> TuSize eps Fm -> DGamSize eps Fm -> Des C eps Fm.
Proof.
  intros C eps Fm HC HS HT HU HD.
  split; [split; [split; [exact HC|exact HS]|exact HT]|split; [exact HU|exact HD]].
Qed.

Lemma le_max2 : forall a b x, Rmax a b <= x -> a <= x /\ b <= x.
Proof.
  intros a b x Hx. split.
  - apply Rle_trans with (Rmax a b); [apply Rmax_l|exact Hx].
  - apply Rle_trans with (Rmax a b); [apply Rmax_r|exact Hx].
Qed.

(* [Mathlib] lt_trans Real.exp_one_lt_d9 (by norm_num). *)
Hypothesis exp_one_lt_3 : exp 1 < 3.
Lemma exp_one_le_3 : exp 1 <= 3.
Proof. left. exact exp_one_lt_3. Qed.
Lemma three_le_three : 3 <= 3.
Proof. apply Rle_refl. Qed.
Lemma zero_lt_three : 0 < 3.
Proof. lra. Qed.
Lemma zero_le_two : 0 <= 2.
Proof. lra. Qed.

(* ===================================================================== *)
(* designExists_of_choices (DesignExistsOfChoices.lean)                   *)
(* ===================================================================== *)
Variable Pack : forall eps, FamP eps -> R -> Prop.
Variable sup : R -> R -> R.
Variable CTLe Boxes QDRows DGamDvd ChosenBits ChosenProviso
  : forall eps, FamP eps -> Prop.
Variable ChosenQD : forall eps, FamP eps -> R -> Prop.
Variable ChosenThin : forall eps, FamP eps -> R -> Prop.
Variable ChosenE : forall eps (Fm : FamP eps), Chan eps Fm -> Prop.

Definition DesignChoices (C : FamCl) : Prop :=
  exists e0, 0 < e0 /\ forall eps, 0 < eps -> eps <= e0 -> forall K : R,
    exists Fm, C eps Fm /\ Pack eps Fm K.

Definition DesignExists (C : FamCl) : Prop :=
  exists e, 0 < e /\ forall eps, 0 < eps -> eps <= e -> forall _K : R,
    exists (Fm : FamP eps) (ch : Chan eps Fm),
      C eps Fm /\ Side eps Fm /\ ChosenE eps Fm ch /\ TuSize eps Fm /\ DGamSize eps Fm.

Definition ThinArrow (eps : R) (Fm : FamP eps) : Prop :=
  Boxes eps Fm -> QDRows eps Fm -> (exists C5, 0 < C5 /\ ChosenQD eps Fm C5) ->
  exists c6, 0 < c6 /\ ChosenThin eps Fm c6.

Hypothesis pack_ch : forall eps Fm K, Pack eps Fm K -> Chan eps Fm.
Hypothesis pack_le : forall eps Fm K, Pack eps Fm K -> CTLe eps Fm.
Hypothesis pack_boxes : forall eps Fm K, Pack eps Fm K -> Boxes eps Fm.
Hypothesis pack_qdrows : forall eps Fm K, Pack eps Fm K -> QDRows eps Fm.
Hypothesis pack_qd : forall eps Fm K, Pack eps Fm K -> exists C5, 0 < C5 /\ ChosenQD eps Fm C5.
Hypothesis pack_dvd : forall eps Fm K, Pack eps Fm K -> DGamDvd eps Fm.
Hypothesis pack_bits : forall eps Fm K, Pack eps Fm K -> ChosenBits eps Fm.
(* [inventory] (Fm.large_sup K K' CH).1 — both projections are Side *)
Hypothesis large_sup : forall eps Fm K K', Pack eps Fm (sup K K') -> Side eps Fm.
(* [inventory] dGamSize_of_dvd; its log_minkM proof is not replayed *)
Hypothesis dGamSize_of_dvd : forall eps Fm, DGamDvd eps Fm -> DGamSize eps Fm.
Hypothesis chosenE_of_pack : forall eps Fm (ch : Chan eps Fm),
  ChosenBits eps Fm -> ChosenProviso eps Fm ->
  (exists c6, 0 < c6 /\ ChosenThin eps Fm c6) -> ChosenE eps Fm ch.

Theorem designExists_of_choices_r : forall (C : FamCl),
  DesignChoices C ->
  Closed C (fun eps Fm _ => CTLe eps Fm -> TuSize eps Fm) ->
  Closed C (fun eps Fm _ => ChosenProviso eps Fm) ->
  Closed C (fun eps Fm _ => ThinArrow eps Fm) ->
  DesignExists C.
Proof.
  intros C [e0 [He0 Hch]] HTu HPr HTh.
  assert (Hand : Closed C (fun eps Fm ch =>
      (CTLe eps Fm -> TuSize eps Fm) /\ ChosenProviso eps Fm /\ ThinArrow eps Fm)).
  { apply (closed_and _ _ _ HTu). apply (closed_and _ _ _ HPr). exact HTh. }
  destruct Hand as [e1 [He1 HA]].
  destruct (shrink2 e0 e1 He0 He1) as [c [Hc [Hc0 Hc1]]].
  exists c. split; [exact Hc|].
  intros eps Heps Hle K.
  destruct (HA eps Heps (Rle_trans _ _ _ Hle Hc1)) as [K' HK'].
  destruct (Hch eps Heps (Rle_trans _ _ _ Hle Hc0) (sup K K')) as [Fm [Hmem Hpack]].
  assert (HS : Side eps Fm) by (apply (large_sup _ _ K K' Hpack)).
  set (ch := pack_ch _ _ _ Hpack).
  destruct (HK' Fm ch Hmem HS) as [Hb1 [Hb2 Hb3]].
  assert (Hthin : exists c6, 0 < c6 /\ ChosenThin eps Fm c6).
  { apply Hb3; [apply (pack_boxes _ _ _ Hpack)|apply (pack_qdrows _ _ _ Hpack)|apply (pack_qd _ _ _ Hpack)]. }
  exists Fm, ch. split; [exact Hmem|]. split; [exact HS|]. split; [|split].
  - apply (chosenE_of_pack _ _ ch); [apply (pack_bits _ _ _ Hpack)|exact Hb2|exact Hthin].
  - apply Hb1. apply (pack_le _ _ _ Hpack).
  - apply dGamSize_of_dvd. apply (pack_dvd _ _ _ Hpack).
Qed.

(* ===================================================================== *)
(* link_ex (LinkEx.lean), at the subclass shapeWin instantiates           *)
(* ===================================================================== *)
Variable Acl : FamCl.
Variable LitThin : Prop.
Variable RankClass : FamCl.
Variable RankTies HN4 : forall eps, FamP eps -> Prop.
Variable MinkDiv : Prop.

Hypothesis hTu : Closed (WithTw (WithSm (WithChN Acl)))
  (fun eps Fm _ => CTLe eps Fm -> TuSize eps Fm).
Hypothesis hn4 : Closed (WithTw (WithSm (WithChN Acl))) (fun eps Fm _ => HN4 eps Fm).
(* [inventory] (class_of_record_of_choice (sel) (class_duties_of_choice _)).c2s *)
Hypothesis hRec_c2s : forall eps Fm, Acl eps Fm -> RankClass eps Fm.
(* [inventory] closed_rankTiesF_C2S *)
Hypothesis closed_rankTies : Closed RankClass (fun eps Fm _ => RankTies eps Fm).
(* [inventory] chosenProviso_min *)
Hypothesis chosenProviso_min : forall eps Fm,
  exp 1 <= 3 -> HN4 eps Fm -> RankTies eps Fm -> ChosenProviso eps Fm.
(* [inventory] chosenThin_closed *)
Hypothesis chosenThin_closed : LitThin ->
  Closed (WithTw (WithSm (WithChN Acl))) (fun eps Fm _ => ThinArrow eps Fm).
(* [inventory] minkowski_bound_rat *)
Hypothesis minkowski_bound_rat : MinkDiv.
Hypothesis hLit : LitThin.
(* reading of ExS A cT at (la, G, hla, hH) *)
Hypothesis hEx : MinkDiv -> forall la (G : FReq), 1 < la -> HEW la (req G) ->
  DesignChoices (WithTw (cap Acl (Cls G la))).
(* [inventory] designChoices_upN *)
Hypothesis designChoices_upN : forall B,
  DesignChoices (WithTw B) -> DesignChoices (WithTw (WithSm (WithChN B))).

Theorem link_ex_r : forall (C : FamCl),
  DesignChoices (WithTw (cap Acl C)) ->
  DesignExists (WithTw (WithSm (WithChN (cap Acl C)))).
Proof.
  intros C Hdc.
  set (B := cap Acl C).
  apply designExists_of_choices_r.
  - apply designChoices_upN. exact Hdc.
  - apply closed_sub with (C := WithTw (WithSm (WithChN Acl))); [exact hTu|].
    intros eps Fm H. apply (hsub_cls Acl C). exact H.
  - apply (closed_imp _ (fun eps Fm ch => HN4 eps Fm /\ RankTies eps Fm)).
    + apply closed_and.
      * apply closed_sub with (C := WithTw (WithSm (WithChN Acl))); [exact hn4|].
        intros eps Fm H. apply (hsub_cls Acl C). exact H.
      * apply closed_sub with (C := RankClass); [exact closed_rankTies|].
        intros eps Fm H. apply hRec_c2s. apply (hsub_base B). exact H.
    + intros eps Fm ch _ [Hh Hr]. apply chosenProviso_min; [apply exp_one_le_3|exact Hh|exact Hr].
  - apply closed_sub with (C := WithTw (WithSm (WithChN Acl))); [apply chosenThin_closed; exact hLit|].
    intros eps Fm H. apply (hsub_cls Acl C). exact H.
Qed.

(* ===================================================================== *)
(* link_gl (LinkGl.lean)                                                  *)
(* ===================================================================== *)
(* reading of Duty's field .2.2.2.2.1: five nested conjuncts, then the
   GL component.  The other five conjuncts stay abstract. *)
Variable D1 D2 D3f D4 D6 DutyGL : forall eps, FamP eps -> Prop.
Definition DutyAt (eps : R) (Fm : FamP eps) : Prop :=
  D1 eps Fm /\ D2 eps Fm /\ D3f eps Fm /\ D4 eps Fm /\ DutyGL eps Fm /\ D6 eps Fm.
Hypothesis hduty : forall eps Fm, Acl eps Fm -> DutyAt eps Fm.

Lemma duty_gl_proj : forall eps Fm, Acl eps Fm -> DutyGL eps Fm.
Proof.
  intros eps Fm HA.
  destruct (hduty eps Fm HA) as [_ [_ [_ [_ [Hg _]]]]]. exact Hg.
Qed.

Variable NuFull MuRank : forall eps, FamP eps -> Prop.
Variable LinkG LinkS LinkN LinkEta LinkIRR SmallRank : forall eps, FamP eps -> Prop.
Variable DivN HDiv MuLink : forall eps, FamP eps -> Prop.

Definition LinkPack (eD eL : R) (eps : R) (Fm : FamP eps) : Prop :=
  exists K cHH eK CL x0, forall x : R, x0 <= x -> fWin eps Fm x ->
    ChainTied eps Fm eD eL K cHH eK CL x.

(* reading of `aGL hT hDG hCh ⟨aG, aS, aI, hD, linkMu⟩` *)
Definition GLArrow (eD eL : R) (eps : R) (Fm : FamP eps) (ch : Chan eps Fm) : Prop :=
  TuSize eps Fm -> DGamSize eps Fm -> ChosenE eps Fm ch ->
  LinkG eps Fm -> (TuSize eps Fm -> LinkS eps Fm) -> LinkIRR eps Fm ->
  HDiv eps Fm -> MuLink eps Fm -> LinkPack eD eL eps Fm.

(* [inventory] famGLmin_of_realPlaceSecondLayer _ .muRank *)
Hypothesis muRank : 0 < 3 ->
  Closed (D3 Acl) (fun eps Fm ch =>
    TuSize eps Fm -> ChosenE eps Fm ch -> NuFull eps Fm /\ MuRank eps Fm).
(* [inventory] famGLmin _ .link8 , at Cabs = 2, C0 = 3, eD = 2, eL = 0 *)
Hypothesis link8 : 0 <= 2 -> 3 <= 3 ->
  (forall eps Fm, D3 Acl eps Fm -> DutyGL eps Fm) ->
  Closed (D3 Acl) (fun eps Fm ch => GLArrow 2 0 eps Fm ch).

Theorem link_gl_r :
  Closed (D3 Acl) (fun eps Fm ch => ChosenE eps Fm ch -> NuFull eps Fm /\ MuRank eps Fm) /\
  Closed (D3 Acl) (fun eps Fm ch => GLArrow 2 0 eps Fm ch).
Proof.
  split.
  - apply (closed_imp _ (fun eps Fm ch =>
      (TuSize eps Fm -> ChosenE eps Fm ch -> NuFull eps Fm /\ MuRank eps Fm) /\ TuSize eps Fm)).
    + apply closed_and; [apply muRank; apply zero_lt_three|].
      apply closed_of_class. intros eps Fm HC ch. exact (d3_tu Acl eps Fm HC).
    + intros eps Fm ch _ [Hf Ht] HcE. exact (Hf Ht HcE).
  - apply link8; [apply zero_le_two|apply three_le_three|].
    intros eps Fm HC. apply duty_gl_proj. exact (d3_a Acl eps Fm HC).
Qed.

(* ===================================================================== *)
(* link_eta (LinkEta.lean)                                                *)
(* ===================================================================== *)
Variable EtaParts : forall eps, FamP eps -> R -> Prop.
(* [inventory] tied_families_of_choice *)
Hypothesis tied_families : forall eps Fm, Acl eps Fm -> exists x0,
  forall x : R, fx1 eps Fm < x -> x0 <= x -> EtaParts eps Fm x.
(* [inventory] linkEta_closed; the triple ⟨mt, cover, hecke⟩ is its premise *)
Hypothesis eta_of_parts : forall eps Fm,
  (exists x0, forall x : R, x0 <= x -> EtaParts eps Fm x) -> LinkEta eps Fm.

Theorem link_eta_r : Closed (D3 Acl) (fun eps Fm _ => LinkEta eps Fm).
Proof.
  apply closed_of_class. intros eps Fm HC _.
  destruct (tied_families eps Fm (d3_a _ _ _ HC)) as [x0 Hx0].
  apply eta_of_parts. exists (Rmax x0 (fx1 eps Fm + 1)). intros x Hle.
  destruct (le_max2 x0 (fx1 eps Fm + 1) x Hle) as [H0 H1].
  apply Hx0; [lra|exact H0].
Qed.

(* ===================================================================== *)
(* link_g (LinkG.lean)                                                    *)
(* ===================================================================== *)
Variable LayerTwo GTied AdmTops : forall eps, FamP eps -> Prop.
(* [inventory] class_of_record_of_choice *)
Hypothesis hRec : forall eps Fm, Acl eps Fm -> LayerTwo eps Fm.
(* [inventory] gTiedF_of_C2Rec *)
Hypothesis gtied_of_rec : forall eps Fm, LayerTwo eps Fm -> GTied eps Fm.
(* [inventory] admissible_tops_mertens (topsF_of_chosenE _) *)
Hypothesis tops_mertens : forall eps Fm, D3 Acl eps Fm -> AdmTops eps Fm.
(* [inventory] linkG_concrete5 *)
Hypothesis linkG_concrete5 :
  Closed (D3 Acl) (fun eps Fm _ => GTied eps Fm) ->
  Closed (D3 Acl) (fun eps Fm _ => AdmTops eps Fm) ->
  Closed (D3 Acl) (fun eps Fm _ => LinkG eps Fm).

Theorem link_g_r : Closed (D3 Acl) (fun eps Fm _ => LinkG eps Fm).
Proof.
  apply linkG_concrete5.
  - apply closed_of_class. intros eps Fm HC _.
    apply gtied_of_rec. apply hRec. exact (d3_a Acl eps Fm HC).
  - apply closed_of_class. intros eps Fm HC _. apply tops_mertens. exact HC.
Qed.

(* ===================================================================== *)
(* link_brest, link_alt: the Lean proofs are single calls                 *)
(* ===================================================================== *)
Variable RemAt : forall eps, FamP eps -> Prop.
(* [inventory] bRest_all — the whole of LinkBrest.lean *)
Hypothesis bRest_all : Closed (D3 Acl) (fun eps Fm _ => RemAt eps Fm).
Theorem link_brest_r : Closed (D3 Acl) (fun eps Fm _ => RemAt eps Fm).
Proof. exact bRest_all. Qed.

(* [inventory] theoremS_transport_link_zero — the whole of LinkAlt.lean
   (the file also binds exp 1 <= 3; that bound is not applied) *)
Hypothesis theoremS_transport :
  Closed (D3 Acl) (fun eps Fm _ => TuSize eps Fm -> LinkS eps Fm).
Theorem link_alt_r : Closed (D3 Acl) (fun eps Fm _ => TuSize eps Fm -> LinkS eps Fm).
Proof. exact theoremS_transport. Qed.

(* ===================================================================== *)
(* link_irr (LinkIRROfJoinEx.lean): the Closed algebra, not sizesRec_at   *)
(* ===================================================================== *)
Variable Green : Prop.
Variable sel1 : forall eps, FamP eps -> R.
(* RawAt x : the ∃ A, good ∧ join ∧ count witness at x.
   FullAt x : that witness plus admLq and SizesRec. *)
Variable RawAt FullAt : forall eps, FamP eps -> R -> Prop.
(* [inventory] irrC *)
Hypothesis irrC : Closed (D3 Acl) (fun eps Fm _ => exists x0, forall x : R, x0 <= x -> RawAt eps Fm x).
(* [inventory] admissibleLabelWeights_of_green… and sizesRec_at.
   sizesRec_at's rpow chain is not replayed; the max-threshold arithmetic
   below is. *)
Hypothesis rows_extend : Green -> forall eps Fm x0 x,
  (forall y : R, x0 <= y -> RawAt eps Fm y) ->
  Rmax (Rmax x0 (sel1 eps Fm)) (Rmax (fx1 eps Fm + 1) 4) <= x ->
  FullAt eps Fm x.
(* [inventory] closed_eps_le_one *)
Hypothesis closed_eps_le_one : Closed (D3 Acl) (fun eps Fm _ => eps <= 1).
(* [inventory] linkIRR_of_join_ex, including its rpow step 3/2 <= x^ez *)
Hypothesis linkIRR_of_join_ex : forall eps Fm,
  0 < eps -> eps <= 1 -> (exists x0, forall x : R, x0 <= x -> FullAt eps Fm x) -> LinkIRR eps Fm.

Theorem link_irr_r : Green -> Closed (D3 Acl) (fun eps Fm _ => LinkIRR eps Fm).
Proof.
  intros hG.
  apply (closed_imp_eps _ (fun eps Fm ch =>
      (exists x0, forall x : R, x0 <= x -> FullAt eps Fm x) /\ eps <= 1)).
  - apply closed_and; [|exact closed_eps_le_one].
    apply (closed_imp _ (fun eps Fm _ => exists x0, forall x : R, x0 <= x -> RawAt eps Fm x)).
    + exact irrC.
    + intros eps Fm ch _ [x0 Hx0].
      exists (Rmax (Rmax x0 (sel1 eps Fm)) (Rmax (fx1 eps Fm + 1) 4)).
      intros x Hle. apply (rows_extend hG eps Fm x0 x Hx0 Hle).
  - intros eps Fm ch Heps _ [Hf He]. apply linkIRR_of_join_ex; assumption.
Qed.

(* ===================================================================== *)
(* closed_family_admissible_twist_link                                    *)
(* ===================================================================== *)
Variable Pt0 PtTw Per0 PerTw P10 AtG Serv Dgt Adm2 AdmRest : forall eps, FamP eps -> Prop.
Hypothesis aPt0 : Closed (D3 Acl) (fun eps Fm _ => Pt0 eps Fm).
Hypothesis aPtTw : Closed (D3 Acl) (fun eps Fm _ => PtTw eps Fm).
Hypothesis aPer0 : Closed (D3 Acl) (fun eps Fm _ => Per0 eps Fm).
Hypothesis aPerTw : Closed (D3 Acl) (fun eps Fm _ => PerTw eps Fm).
Hypothesis aP10 : Closed (D3 Acl) (fun eps Fm _ => P10 eps Fm).
Hypothesis aAtG : Closed (D3 Acl) (fun eps Fm _ => AtG eps Fm).
(* [inventory] servF_of_servT, after hDG : of_class (hc.2.2.2) *)
Hypothesis servF_of_servT : forall eps Fm, DGamSize eps Fm -> Serv eps Fm.
(* [inventory] closed_eventually_levelPrimeCoprimeStabiliser *)
Hypothesis levelPrime_closed : Closed (D3 Acl) (fun eps Fm _ => Dgt eps Fm).
(* [inventory] admissible_family_of_inclusion; the record pack is the conjunction *)
Hypothesis admissible_of_inclusion :
  Closed (D3 Acl) (fun eps Fm _ =>
    Pt0 eps Fm /\ PtTw eps Fm /\ Per0 eps Fm /\ PerTw eps Fm /\
    Serv eps Fm /\ P10 eps Fm /\ Dgt eps Fm /\ AtG eps Fm) ->
  Closed (D3 Acl) (fun eps Fm _ => Adm2 eps Fm /\ AdmRest eps Fm).

Theorem admissible_twist_link_r : Closed (D3 Acl) (fun eps Fm _ => Adm2 eps Fm).
Proof.
  apply (closed_imp _ (fun eps Fm ch => Adm2 eps Fm /\ AdmRest eps Fm)).
  - apply admissible_of_inclusion.
    assert (hDG : Closed (D3 Acl) (fun eps Fm _ => DGamSize eps Fm)).
    { apply closed_of_class. intros eps Fm HC _. exact (d3_dg Acl eps Fm HC). }
    assert (hServ : Closed (D3 Acl) (fun eps Fm _ => Serv eps Fm)).
    { apply (closed_imp _ (fun eps Fm _ => DGamSize eps Fm)); [exact hDG|].
      intros eps Fm ch _ HD. apply servF_of_servT. exact HD. }
    apply (closed_and _ _ _ aPt0).
    apply (closed_and _ _ _ aPtTw).
    apply (closed_and _ _ _ aPer0).
    apply (closed_and _ _ _ aPerTw).
    apply (closed_and _ _ _ hServ).
    apply (closed_and _ _ _ aP10).
    apply (closed_and _ _ _ levelPrime_closed).
    exact aAtG.
  - intros eps Fm ch _ [Ha _]. exact Ha.
Qed.

(* ===================================================================== *)
(* selection_closed_of_wu_decay                                           *)
(* ===================================================================== *)
Variable MI RowRest FinX Comp5 ImageFull : forall eps, FamP eps -> Prop.
Variable GapAt : forall eps, FamP eps -> R -> Prop.
Hypothesis gap_raw : Closed (D3 Acl) (fun eps Fm _ =>
  exists y, forall x (u v : True), y <= x -> GapAt eps Fm x).
(* [inventory] finXRow_of_gap (finXC_of hWu hRF) *)
Hypothesis finX_of_gap :
  Closed (D3 Acl) (fun eps Fm _ => exists y, forall x : R, y <= x -> GapAt eps Fm x) ->
  Closed (D3 Acl) (fun eps Fm _ => FinX eps Fm).
Hypothesis rRows_info : Closed (D3 Acl) (fun eps Fm _ =>
  exists (C : R) (x0 : R), forall x : R, MI eps Fm /\ RowRest eps Fm).
(* jOn : BaseVectorImageFull, an input of TopShape *)
Hypothesis jOn_full : Closed (D3 Acl) (fun eps Fm _ => ImageFull eps Fm).
(* [inventory] closed_complementFiveFamily_of_evSel_imageFull *)
Hypothesis complement_five : forall (hM : Closed (D3 Acl) (fun eps Fm _ => exists x0, forall x : R, x0 <= x -> MI eps Fm)),
  Closed (D3 Acl) (fun eps Fm _ => FinX eps Fm) ->
  Closed (D3 Acl) (fun eps Fm _ => ImageFull eps Fm) ->
  Closed (D3 Acl) (fun eps Fm _ => Comp5 eps Fm).

Theorem selection_closed_r : Closed (D3 Acl) (fun eps Fm _ => Comp5 eps Fm).
Proof.
  assert (jGap : Closed (D3 Acl) (fun eps Fm _ => exists y, forall x : R, y <= x -> GapAt eps Fm x)).
  { apply (closed_imp _ (fun eps Fm _ => exists y, forall x (u v : True), y <= x -> GapAt eps Fm x)); [exact gap_raw|].
    intros eps Fm ch _ [y hy]. exists y. intros x hx. apply (hy x I I hx). }
  assert (hM : Closed (D3 Acl) (fun eps Fm _ => exists x0, forall x : R, x0 <= x -> MI eps Fm)).
    { apply (closed_imp _ (fun eps Fm _ => exists (C : R) (x0 : R), forall x : R, MI eps Fm /\ RowRest eps Fm)); [exact rRows_info|].
    intros eps Fm ch _ [C [x0 Hx]]. exists x0. intros x hx. exact (proj1 (Hx x)). }
  apply (complement_five hM); [apply finX_of_gap; exact jGap|exact jOn_full].
Qed.

(* ===================================================================== *)
(* smallLevelRankEq                                                       *)
(* ===================================================================== *)
Variable SurjAt : forall eps, FamP eps -> R -> Prop.
Hypothesis zL : Closed (D3 Acl) (fun eps Fm _ =>
  exists xr, forall x : R, sel1 eps Fm <= x -> xr <= x -> SurjAt eps Fm x).
(* [inventory] rank_zero_of_row_conditions, fed the max-bounded callbacks.
   hDivG.toRows and rowsHold0_of stay inside this hypothesis. *)
Hypothesis rank_zero : forall eps Fm xr,
  (forall x : R, sel1 eps Fm <= x -> xr <= x -> SurjAt eps Fm x) -> SmallRank eps Fm.

Theorem small_level_rank_eq_r : Closed (D3 Acl) (fun eps Fm _ => SmallRank eps Fm).
Proof.
  apply (closed_imp _ (fun eps Fm _ => exists xr, forall x : R, sel1 eps Fm <= x -> xr <= x -> SurjAt eps Fm x)); [exact zL|].
  intros eps Fm ch _ [xr Hxr]. apply (rank_zero eps Fm xr).
  intros x Hs Hx. exact (Hxr x Hs Hx).
Qed.

(* The max that Lean writes as `max (sel) xr` is the bound rank_zero is
   called at; le_max2 is what `le_trans (le_max_left) h0` is.  State the
   threshold form as well, so the max is not only a lemma. *)
Lemma small_level_at_max : forall eps Fm xr x,
  (forall y : R, sel1 eps Fm <= y -> xr <= y -> SurjAt eps Fm y) ->
  Rmax (sel1 eps Fm) xr <= x -> SurjAt eps Fm x.
Proof.
  intros eps Fm xr x H Hmx. destruct (le_max2 _ _ _ Hmx) as [Hs Hx]. apply H; assumption.
Qed.

(* ===================================================================== *)
(* shapeWin's hBR: and / of_class / imp                                   *)
(* ===================================================================== *)
Variable Cut OneMap CszGe Comp2 : forall eps, FamP eps -> Prop.
(* [inventory] cut_of_stable (hMt _) *)
Hypothesis cut_of_stable : forall eps Fm, D3 Acl eps Fm -> Cut eps Fm.
(* [inventory] ⟨0, fun j => (hRB i).oneMap j⟩ *)
Hypothesis oneMap_of_hRB : forall eps Fm, D3 Acl eps Fm -> OneMap eps Fm.
(* [inventory] closed_Csz_ge_fn _ (fun _ => 0) *)
Hypothesis closed_Csz : Closed (D3 Acl) (fun eps Fm _ => CszGe eps Fm).
Hypothesis aC2 : Closed (D3 Acl) (fun eps Fm _ => Comp2 eps Fm).
(* [inventory] (r hc hT hD).toRows (wire_sel _ hN) o a (complement_two_of_items c) c5.
   Conclusion is the hDIV arrow topDesWin applies as `aD hT hDG aE divinN`. *)
Hypothesis toRows_wire : forall eps Fm,
  RemAt eps Fm -> Cut eps Fm ->
  (exists (C : R) (x0 : R), forall x : R, MI eps Fm /\ RowRest eps Fm) ->
  OneMap eps Fm -> CszGe eps Fm -> Adm2 eps Fm -> Comp2 eps Fm -> Comp5 eps Fm ->
  TuSize eps Fm -> DGamSize eps Fm -> LinkEta eps Fm -> DivN eps Fm -> HDiv eps Fm.

Theorem bridge_rows_r :
  Closed (D3 Acl) (fun eps Fm _ => Adm2 eps Fm) ->
  Closed (D3 Acl) (fun eps Fm _ => Comp5 eps Fm) ->
  Closed (D3 Acl) (fun eps Fm _ =>
    TuSize eps Fm -> DGamSize eps Fm -> LinkEta eps Fm -> DivN eps Fm -> HDiv eps Fm).
Proof.
  intros hA2 hC5.
  apply (closed_imp _ (fun eps Fm ch =>
      RemAt eps Fm /\ Cut eps Fm /\
      (exists (C : R) (x0 : R), forall x : R, MI eps Fm /\ RowRest eps Fm) /\
      OneMap eps Fm /\ CszGe eps Fm /\ Adm2 eps Fm /\ Comp2 eps Fm /\ Comp5 eps Fm)).
  - apply (closed_and _ _ _ link_brest_r).
    apply closed_and; [apply closed_of_class; intros eps Fm HC _; apply cut_of_stable; exact HC|].
    apply (closed_and _ _ _ rRows_info).
    apply closed_and; [apply closed_of_class; intros eps Fm HC _; apply oneMap_of_hRB; exact HC|].
    apply (closed_and _ _ _ closed_Csz).
    apply (closed_and _ _ _ hA2).
    apply (closed_and _ _ _ aC2).
    exact hC5.
  - intros eps Fm ch _ [Hr [Hcut [Hrows [Hom [Hcz [Ha [Hc2 Hc5]]]]]]].
    intros HU HD HE HDN. apply toRows_wire; assumption.
Qed.

(* ===================================================================== *)
(* topDesWin (DesWin.lean)                                                *)
(* ===================================================================== *)
(* [inventory] divinN_of_hypV *)
Hypothesis divinN_of_hypV : forall eps Fm, 0 < eps -> hv Fm -> LinkN eps Fm -> SmallRank eps Fm -> DivN eps Fm.
(* [inventory] muTu_of_tuSize *)
Hypothesis muTu_of_tuSize : forall eps Fm, 0 < eps -> TuSize eps Fm -> True.
(* [inventory] muDGam_of_fact.  Carried as a premise of linkMu rather than a
   separate Prop, so it is not erased. *)
Hypothesis muDGam_fact : forall eps Fm, DGamSize eps Fm -> True.
(* [inventory] linkMu_of_linkDIV Fm hD (aR hCh).1 (aR hCh).2 (muTu _) (muDGam _) *)
Hypothesis linkMu_of_linkDIV : forall eps Fm (ch : Chan eps Fm),
  HDiv eps Fm -> NuFull eps Fm -> MuRank eps Fm -> True -> True -> MuLink eps Fm.

Theorem topDesWin_r : forall (C C' E : FamCl) (eD eL : R),
  DesignExists (WithTw (WithSm C')) ->
  (forall eps Fm, C' eps Fm -> C eps Fm) ->
  (forall eps Fm, C' eps Fm -> E eps Fm) ->
  (forall eps Fm, E eps Fm -> hv Fm) ->
  Closed (Des C) (fun eps Fm _ => LinkN eps Fm) ->
  Closed (Des C) (fun eps Fm _ => TuSize eps Fm -> DGamSize eps Fm -> LinkEta eps Fm -> DivN eps Fm -> HDiv eps Fm) ->
  Closed (Des C) (fun eps Fm _ => LinkEta eps Fm) ->
  Closed (Des C) (fun eps Fm _ => LinkIRR eps Fm) ->
  Closed (Des C) (fun eps Fm _ => SmallRank eps Fm) ->
  Closed (Des C) (fun eps Fm ch => ChosenE eps Fm ch -> NuFull eps Fm /\ MuRank eps Fm) ->
  Closed (Des C) (fun eps Fm _ => LinkG eps Fm) ->
  Closed (Des C) (fun eps Fm _ => TuSize eps Fm -> LinkS eps Fm) ->
  Closed (Des C) (fun eps Fm ch => GLArrow eD eL eps Fm ch) ->
  FCC E.
Proof.
  intros C C' E eD eL Hex h1 h2 hV hN hDIV hEta hIRR hZ hRk hG hS hGL.
  assert (Hall : Closed (Des C) (fun eps Fm ch =>
      LinkN eps Fm /\
      (TuSize eps Fm -> DGamSize eps Fm -> LinkEta eps Fm -> DivN eps Fm -> HDiv eps Fm) /\
      LinkEta eps Fm /\ LinkIRR eps Fm /\ SmallRank eps Fm /\
      (ChosenE eps Fm ch -> NuFull eps Fm /\ MuRank eps Fm) /\
      LinkG eps Fm /\ (TuSize eps Fm -> LinkS eps Fm) /\ GLArrow eD eL eps Fm ch)).
  { apply closed_9; assumption. }
  destruct Hall as [e1 [He1 HA]].
  destruct Hex as [e3 [He3 HEx]].
  destruct (shrink2 e1 e3 He1 He3) as [c [Hc [Hc1 Hc3]]].
  exists eD, eL, c. split; [exact Hc|].
  intros eps Heps Hlt.
  assert (Hle : eps <= c) by lra.
  destruct (HA eps Heps (Rle_trans _ _ _ Hle Hc1)) as [Kpage HK].
  destruct (HEx eps Heps (Rle_trans _ _ _ Hle Hc3) Kpage) as [Fm [ch [HC' [HS [Hch [Ht Hdg]]]]]].
  destruct HC' as [Hsm Htw]. destruct Hsm as [HC's HsmF].
  assert (Hdes : Des C eps Fm).
  { apply des_mk; [apply h1; exact HC's|exact HsmF|exact Htw|exact Ht|exact Hdg]. }
  destruct (HK Fm ch Hdes HS) as [aN [aD [aE [aI [aZ [aR [aG [aS aGL]]]]]]]].
  assert (HdN : DivN eps Fm).
  { apply divinN_of_hypV; [exact Heps|apply hV; apply h2; exact HC's|exact aN|exact aZ]. }
  assert (Hd : HDiv eps Fm).
  { apply aD; [exact Ht|exact Hdg|exact aE|exact HdN]. }
  assert (Hm : MuLink eps Fm).
  { apply (linkMu_of_linkDIV eps Fm ch); [exact Hd|exact (proj1 (aR Hch))|exact (proj2 (aR Hch))|
      exact (muTu_of_tuSize eps Fm Heps Ht)|exact (muDGam_fact eps Fm Hdg)]. }
  assert (Hp : LinkPack eD eL eps Fm).
  { apply aGL; [exact Ht|exact Hdg|exact Hch|exact aG|exact aS|exact aI|exact Hd|exact Hm]. }
  exists Fm. split; [apply h2; exact HC's|exact Hp].
Qed.

(* ===================================================================== *)
(* shapeWin: hsub, the link facts, topDesWin, concluding TopG             *)
(* ===================================================================== *)
(* nRest : TopShape's `N (D3 3 A)`, i.e. Closed _ LinkN.  Not a link fact. *)
Hypothesis nRest : Closed (D3 Acl) (fun eps Fm _ => LinkN eps Fm).
Lemma incl_withChN : forall B eps Fm, WithChN (cap Acl B) eps Fm -> WithChN Acl eps Fm.
Proof.
  intros B eps Fm H. destruct H as [[HA _] HN]. split; assumption.
Qed.

Lemma incl_right : forall (A B : FamCl) eps Fm, WithChN (cap A B) eps Fm -> B eps Fm.
Proof.
  intros A B eps Fm H. destruct H as [[_ HB] _]. exact HB.
Qed.

Theorem shapeWin_from_links_r : Green -> TG.
Proof.
  intros hG la G hla hH hV.
  set (B := Cls G la).
  assert (Hex : DesignExists (WithTw (WithSm (WithChN (cap Acl B))))).
  { apply link_ex_r. exact (hEx minkowski_bound_rat la G hla hH). }
  destruct link_gl_r as [hRk hGL].
  apply (topDesWin_r (WithChN Acl) (WithChN (cap Acl B)) B 2 0 Hex).
  - intros eps Fm H. apply (incl_withChN B). exact H.
  - intros eps Fm H. apply (incl_right Acl B). exact H.
  - intros eps Fm HE. apply hV. exact HE.
  - exact nRest.
  - apply bridge_rows_r; [exact admissible_twist_link_r|exact selection_closed_r].
  - exact link_eta_r.
  - apply link_irr_r. exact hG.
  - exact small_level_rank_eq_r.
  - exact hRk.
  - exact link_g_r.
  - exact link_alt_r.
  - exact hGL.
Qed.
End TopShapeLinks.

Print Assumptions designExists_of_choices_r.
Print Assumptions link_ex_r.
Print Assumptions link_gl_r.
Print Assumptions link_eta_r.
Print Assumptions link_g_r.
Print Assumptions link_brest_r.
Print Assumptions link_alt_r.
Print Assumptions link_irr_r.
Print Assumptions admissible_twist_link_r.
Print Assumptions selection_closed_r.
Print Assumptions small_level_rank_eq_r.
Print Assumptions bridge_rows_r.
Print Assumptions topDesWin_r.
Print Assumptions shapeWin_from_links_r.
