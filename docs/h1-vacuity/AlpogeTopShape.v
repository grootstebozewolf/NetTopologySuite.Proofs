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

(* Reading of Lean's Fin.  Stdlib Vectors.fin is not imported: that
   module binds the name R and would hide the reals. *)
Inductive fin : nat -> Type :=
| fin1 : forall n, fin (S n)
| finS : forall n, fin n -> fin (S n).

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

Local Abbreviation FamCl := (forall eps, FamP eps -> Prop).
Local Abbreviation HEW := (HostExW Ranks Host HostCT2 RankVal HostGood).
Local Abbreviation Cls := (cls FamP fx1 fIx fWin FReq At).
Definition hv {eps : R} (Fm : FamP eps) : Prop := @HypV FamP fIx VV eps Fm.
Local Abbreviation FCC := (FamilyClassConnected FamP fWin ChainTied).
Local Abbreviation TG := (TopG Ranks Host HostCT2 RankVal HostGood FamP fx1 fIx fWin ChainTied VV FReq req At).

(* Lean's CH is a real (DesignExistsOfChoices.lean, the witness beside Fm). *)
Definition Chan (eps : R) (Fm : FamP eps) : Type := R.
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

(* reading: Des C C0.  D3 3 A is Des (WithChN A) at the literal level 3
   (every Lean call below is D3 3 𝒜).  The equation keeps 3 in the type. *)
Definition Des (C : FamCl) : FamCl :=
  fun eps Fm => WithTw (WithSm C) eps Fm /\ TuSize eps Fm /\ DGamSize eps Fm.
Variable AtC0 : R -> forall eps, FamP eps -> Prop.
(* c0 = 3 is the level.  D3 3 A is equivalent to Des (WithChN A);
   D3 at any other real is empty. *)
Definition D3 (c0 : R) (A : FamCl) : FamCl :=
  fun eps Fm => c0 = 3 /\ Des (WithChN A) eps Fm.

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

Lemma d3_tu : forall c0 A eps Fm, D3 c0 A eps Fm -> TuSize eps Fm.
Proof. intros c0 A eps Fm H. exact (proj1 (proj2 (proj2 H))). Qed.
Lemma d3_dg : forall c0 A eps Fm, D3 c0 A eps Fm -> DGamSize eps Fm.
Proof. intros c0 A eps Fm H. exact (proj2 (proj2 (proj2 H))). Qed.
Lemma d3_a : forall c0 A eps Fm, D3 c0 A eps Fm -> A eps Fm.
Proof. intros c0 A eps Fm H. apply (hsub_base A). exact (proj1 (proj2 H)). Qed.
Lemma d3_withChN : forall c0 A eps Fm, D3 c0 A eps Fm -> WithChN A eps Fm.
Proof.
  intros c0 A eps Fm H.
  destruct (proj2 H) as [Hsm _]. destruct Hsm as [Hch _]. destruct Hch as [Hwn _].
  exact Hwn.
Qed.

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
(* ChosenE Fm C0 CH.  Link facts instantiate C0 with the literal 3. *)
Variable ChosenE : R -> forall eps (Fm : FamP eps), R -> Prop.

Definition DesignChoices (C : FamCl) : Prop :=
  exists e0, 0 < e0 /\ forall eps, 0 < eps -> eps <= e0 -> forall K : R,
    exists Fm, C eps Fm /\ Pack eps Fm K.

(* DesignExists 𝒞 C0.  The witness keeps CH, 0 ≤ CH, hL1 and ChosenE at
   that CH (DesignExistsOfChoices.lean:65-68). *)
Definition DesignExists (C0 : R) (C : FamCl) : Prop :=
  exists e, 0 < e /\ forall eps, 0 < eps -> eps <= e -> forall K : R,
    exists (Fm : FamP eps) (CH : R),
      C eps Fm /\ 0 <= CH /\ Side eps Fm /\
      ChosenE C0 eps Fm CH /\ TuSize eps Fm /\ DGamSize eps Fm.

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
Hypothesis pack_bad : forall eps Fm K, Pack eps Fm K -> exists Cb, 0 < Cb.
Hypothesis pack_CH_nonneg : forall eps Fm K (H : Pack eps Fm K), 0 <= pack_ch eps Fm K H.
(* [inventory] (Fm.large_sup K K' CH).1 hL = ⟨hL1, hL2⟩.
   hL2 is the eliminator side; hL1 is the DesignExists witness. *)
Hypothesis large_sup : forall eps Fm K K', Pack eps Fm (sup K K') ->
  Side eps Fm /\ Side eps Fm.
(* [inventory] dGamSize_of_dvd; its log_minkM proof is not replayed *)
Hypothesis dGamSize_of_dvd : forall eps Fm, DGamDvd eps Fm -> DGamSize eps Fm.
(* The record fields of ⟨C5, c6, Cb, …⟩ are the premises; the result is
   ChosenE at the witness CH, not at an unrelated channel. *)
Hypothesis chosenE_of_pack : forall (C0 : R) eps Fm (CH C5 c6 Cb : R),
  0 <= CH -> 0 < C5 -> 0 < c6 -> 0 < Cb ->
  ChosenBits eps Fm -> ChosenProviso eps Fm ->
  ChosenQD eps Fm C5 -> ChosenThin eps Fm c6 ->
  ChosenE C0 eps Fm CH.

Theorem designExists_of_choices_r : forall (C0 : R) (C : FamCl),
  DesignChoices C ->
  Closed C (fun eps Fm _ => CTLe eps Fm -> TuSize eps Fm) ->
  Closed C (fun eps Fm _ => ChosenProviso eps Fm) ->
  Closed C (fun eps Fm _ => ThinArrow eps Fm) ->
  DesignExists C0 C.
Proof.
  intros C0 C [e0 [He0 Hch]] HTu HPr HTh.
  assert (Hand : Closed C (fun eps Fm ch =>
      (CTLe eps Fm -> TuSize eps Fm) /\ ChosenProviso eps Fm /\ ThinArrow eps Fm)).
  { apply (closed_and _ _ _ HTu). apply (closed_and _ _ _ HPr). exact HTh. }
  destruct Hand as [e1 [He1 HA]].
  destruct (shrink2 e0 e1 He0 He1) as [c [Hc [Hc0 Hc1]]].
  exists c. split; [exact Hc|].
  intros eps Heps Hle K.
  destruct (HA eps Heps (Rle_trans _ _ _ Hle Hc1)) as [K' HK'].
  destruct (Hch eps Heps (Rle_trans _ _ _ Hle Hc0) (sup K K')) as [Fm [Hmem Hpack]].
  destruct (large_sup eps Fm K K' Hpack) as [hL1 hL2].
  set (CH := pack_ch eps Fm (sup K K') Hpack).
  destruct (HK' Fm CH Hmem hL2) as [Hb1 [Hb2 Hb3]].
  destruct (pack_qd eps Fm _ Hpack) as [C5 [HC5 Hqd]].
  assert (Hthin : exists c6, 0 < c6 /\ ChosenThin eps Fm c6).
  { apply Hb3; [apply (pack_boxes eps Fm _ Hpack)|apply (pack_qdrows eps Fm _ Hpack)|exists C5; split; assumption]. }
  destruct Hthin as [c6 [Hc6 Hthin1]].
  destruct (pack_bad eps Fm _ Hpack) as [Cb HCb].
  exists Fm, CH. split; [exact Hmem|].
  split; [apply (pack_CH_nonneg eps Fm _ Hpack)|].
  split; [exact hL1|]. split; [|split].
  - apply (chosenE_of_pack C0 eps Fm CH C5 c6 Cb);
      [apply (pack_CH_nonneg eps Fm _ Hpack)|exact HC5|exact Hc6|exact HCb|
       apply (pack_bits eps Fm _ Hpack)|exact Hb2|exact Hqd|exact Hthin1].
  - apply Hb1. apply (pack_le eps Fm _ Hpack).
  - apply dGamSize_of_dvd. apply (pack_dvd eps Fm _ Hpack).
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
  DesignExists 3 (WithTw (WithSm (WithChN (cap Acl C)))).
Proof.
  intros C Hdc.
  set (B := cap Acl C).
  apply (designExists_of_choices_r 3).
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
Variable LinkG LinkN LinkEta LinkIRR SmallRank : forall eps, FamP eps -> Prop.
(* LinkS Fm C0.  link_alt instantiates C0 with the literal 3. *)
Variable LinkS : R -> forall eps, FamP eps -> Prop.
Variable DivN HDiv MuLink : forall eps, FamP eps -> Prop.
(* LinkGLOBAL's Cabs.  The literal used below is 2. *)
Variable TiedScale : R -> R -> R -> forall eps, FamP eps -> R -> Prop.

Definition LinkPack (Cabs eD eL : R) (eps : R) (Fm : FamP eps) : Prop :=
  exists K cHH eK CL x0, forall x : R, x0 <= x -> fWin eps Fm x ->
    TiedScale Cabs eD eL eps Fm x /\ ChainTied eps Fm eD eL K cHH eK CL x.

(* LinkGLOBAL Fm Cabs CH C0 eD eL, instantiated as Fm 2 CH 3 2 0.
   CH is the channel real `ch`. *)
Definition GLArrow (Cabs C0 eD eL : R) (eps : R) (Fm : FamP eps) (ch : R) : Prop :=
  TuSize eps Fm -> DGamSize eps Fm -> ChosenE C0 eps Fm ch ->
  LinkG eps Fm -> (TuSize eps Fm -> LinkS C0 eps Fm) -> LinkIRR eps Fm ->
  HDiv eps Fm -> MuLink eps Fm -> LinkPack Cabs eD eL eps Fm.

(* [inventory] famGLmin_of_realPlaceSecondLayer _ .muRank *)
Hypothesis muRank : 0 < 3 ->
  Closed (D3 3 Acl) (fun eps Fm ch =>
    TuSize eps Fm -> ChosenE 3 eps Fm ch -> NuFull eps Fm /\ MuRank eps Fm).
(* [inventory] famGLmin _ .link8 , at Cabs = 2, C0 = 3, eD = 2, eL = 0 *)
Hypothesis link8 : 0 <= 2 -> 3 <= 3 ->
  (forall eps Fm, D3 3 Acl eps Fm -> DutyGL eps Fm) ->
  Closed (D3 3 Acl) (fun eps Fm ch => GLArrow 2 3 2 0 eps Fm ch).

Theorem link_gl_r :
  Closed (D3 3 Acl) (fun eps Fm ch => ChosenE 3 eps Fm ch -> NuFull eps Fm /\ MuRank eps Fm) /\
  Closed (D3 3 Acl) (fun eps Fm ch => GLArrow 2 3 2 0 eps Fm ch).
Proof.
  split.
  - apply (closed_imp _ (fun eps Fm ch =>
      (TuSize eps Fm -> ChosenE 3 eps Fm ch -> NuFull eps Fm /\ MuRank eps Fm) /\ TuSize eps Fm)).
    + apply closed_and; [apply muRank; apply zero_lt_three|].
      apply closed_of_class. intros eps Fm HC ch. exact (d3_tu 3 Acl eps Fm HC).
    + intros eps Fm ch _ [Hf Ht] HcE. exact (Hf Ht HcE).
  - apply link8; [apply zero_le_two|apply three_le_three|].
    intros eps Fm HC. apply duty_gl_proj. exact (d3_a 3 Acl eps Fm HC).
Qed.

(* ===================================================================== *)
(* link_eta (LinkEta.lean)                                                *)
(* ===================================================================== *)
Variable Mt Cover Hecke : forall eps (Fm : FamP eps) (x : R) (i : fIx eps Fm x), Prop.
(* [inventory] tied_families_of_choice.  The witness at each i is
   ⟨T.n.gal.mt, T.n.cover, T.n.gal.hecke⟩ (LinkEta.lean:16-17). *)
Hypothesis tied_families : forall eps Fm, Acl eps Fm -> exists x0,
  forall (x : R) (i : fIx eps Fm x), fx1 eps Fm < x -> x0 <= x ->
    Mt eps Fm x i /\ Cover eps Fm x i /\ Hecke eps Fm x i.
(* [inventory] linkEta_closed, fed that triple *)
Hypothesis eta_of_parts : forall eps Fm,
  (exists x0, forall (x : R) (i : fIx eps Fm x), x0 <= x ->
     Mt eps Fm x i /\ Cover eps Fm x i /\ Hecke eps Fm x i) ->
  LinkEta eps Fm.

Theorem link_eta_r : Closed (D3 3 Acl) (fun eps Fm _ => LinkEta eps Fm).
Proof.
  apply closed_of_class. intros eps Fm HC _.
  destruct (tied_families eps Fm (d3_a 3 _ _ _ HC)) as [x0 Hx0].
  apply eta_of_parts. exists (Rmax x0 (fx1 eps Fm + 1)). intros x i Hle.
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
Hypothesis tops_mertens : forall eps Fm, D3 3 Acl eps Fm -> AdmTops eps Fm.
(* [inventory] linkG_concrete5 *)
Hypothesis linkG_concrete5 :
  Closed (D3 3 Acl) (fun eps Fm _ => GTied eps Fm) ->
  Closed (D3 3 Acl) (fun eps Fm _ => AdmTops eps Fm) ->
  Closed (D3 3 Acl) (fun eps Fm _ => LinkG eps Fm).

Theorem link_g_r : Closed (D3 3 Acl) (fun eps Fm _ => LinkG eps Fm).
Proof.
  apply linkG_concrete5.
  - apply closed_of_class. intros eps Fm HC _.
    apply gtied_of_rec. apply hRec. exact (d3_a 3 Acl eps Fm HC).
  - apply closed_of_class. intros eps Fm HC _. apply tops_mertens. exact HC.
Qed.

(* ===================================================================== *)
(* link_brest (LinkBrest.lean:23), link_alt (LinkAlt.lean:34-48)          *)
(* ===================================================================== *)
(* RemainingDivisionBounds Fm 2 CH, depending on the channel and the two sizes. *)
Variable RemAt : forall eps (Fm : FamP eps) (CH : R), Prop.
Variable RowsB PrimAll DivG DcPt RealPlaceLayer : Prop.
Hypothesis hRB : RowsB.
Hypothesis hPA : PrimAll.
Hypothesis hDivG_b : DivG.
Hypothesis hDcPtG : DcPt.
Hypothesis tie_layer : RealPlaceLayer.
(* [inventory] bRest_all, applied to those premises.  The literal 2 is Cabs. *)
Hypothesis bRest_all : RowsB -> PrimAll -> DivG -> DcPt -> RealPlaceLayer ->
  Closed (D3 3 Acl) (fun eps Fm CH =>
    forall hc : D3 3 Acl eps Fm,
      TuSize eps Fm -> DGamSize eps Fm -> RemAt eps Fm CH).
Theorem link_brest_r : Closed (D3 3 Acl) (fun eps Fm CH =>
  forall hc : D3 3 Acl eps Fm,
    TuSize eps Fm -> DGamSize eps Fm -> RemAt eps Fm CH).
Proof. apply bRest_all; assumption. Qed.

Variable ResidEv : forall eps, FamP eps -> Prop.
Variable SSelPack LocTiedPack InstTiePack OneLePack : Prop.
(* [inventory] the SSel built from sel / selS at d3_a (LinkAlt.lean:39-40) *)
Hypothesis ssel : SSelPack.
(* [inventory] residEv_closed_free *)
Hypothesis residEv_closed_free : Closed (D3 3 Acl) (fun eps Fm _ => ResidEv eps Fm).
(* [inventory] (selS …).locTied *)
Hypothesis locTied : LocTiedPack.
(* [inventory] instTie_of_record *)
Hypothesis instTie_of_record : InstTiePack.
(* [inventory] one_le_qqI_of_inst *)
Hypothesis one_le_qqI_of_inst : OneLePack.
(* [inventory] theoremS_transport_link_zero at C0 = 3.
   The three C0 facts are premises, not a single opaque arrow. *)
Hypothesis theoremS_transport :
  3 <= 3 -> 0 < 3 -> exp 1 <= 3 ->
  SSelPack -> LocTiedPack -> InstTiePack -> OneLePack ->
  Closed (D3 3 Acl) (fun eps Fm _ => ResidEv eps Fm) ->
  Closed (D3 3 Acl) (fun eps Fm _ => TuSize eps Fm -> LinkS 3 eps Fm).
Theorem link_alt_r : Closed (D3 3 Acl) (fun eps Fm _ => TuSize eps Fm -> LinkS 3 eps Fm).
Proof.
  apply theoremS_transport.
  - apply three_le_three.
  - apply zero_lt_three.
  - apply exp_one_le_3.
  - exact ssel.
  - exact locTied.
  - exact instTie_of_record.
  - exact one_le_qqI_of_inst.
  - exact residEv_closed_free.
Qed.

(* ===================================================================== *)
(* link_irr (LinkIRROfJoinEx.lean): the Closed algebra, not sizesRec_at   *)
(* ===================================================================== *)
Variable Green : Prop.
Variable sel1 : forall eps, FamP eps -> R.
(* RawAt x : the ∃ A, good ∧ join ∧ count witness at x.
   FullAt Cs x : that witness plus admLq and SizesRec at the literal Cs.
   link_irr instantiates Cs with 6 and requires 0 < cIc. *)
Variable RawAt : forall eps, FamP eps -> R -> Prop.
Variable FullAt : R -> forall eps, FamP eps -> R -> Prop.
Variable cIc : R.
Hypothesis cIc_pos : 0 < cIc.
(* [inventory] irrC *)
Hypothesis irrC : Closed (D3 3 Acl) (fun eps Fm _ => exists x0, forall x : R, x0 <= x -> RawAt eps Fm x).
(* [inventory] admissibleLabelWeights_of_greenCuspidalParametrisation and
   sizesRec_at at Cs = 6.  The rpow chain stays a hypothesis. *)
Hypothesis rows_extend : Green -> forall eps Fm x0 x,
  (forall y : R, x0 <= y -> RawAt eps Fm y) ->
  Rmax (Rmax x0 (sel1 eps Fm)) (Rmax (fx1 eps Fm + 1) 4) <= x ->
  FullAt 6 eps Fm x.
(* [inventory] closed_eps_le_one *)
Hypothesis closed_eps_le_one : Closed (D3 3 Acl) (fun eps Fm _ => eps <= 1).
(* [inventory] linkIRR_of_join_ex _ 6 cIc, including 3/2 <= x^ez *)
Hypothesis linkIRR_of_join_ex : forall eps Fm,
  0 < eps -> eps <= 1 -> 0 < cIc ->
  (exists x0, forall x : R, x0 <= x -> FullAt 6 eps Fm x) -> LinkIRR eps Fm.

Theorem link_irr_r : Green -> Closed (D3 3 Acl) (fun eps Fm _ => LinkIRR eps Fm).
Proof.
  intros hG.
  apply (closed_imp_eps _ (fun eps Fm ch =>
      (exists x0, forall x : R, x0 <= x -> FullAt 6 eps Fm x) /\ eps <= 1)).
  - apply closed_and; [|exact closed_eps_le_one].
    apply (closed_imp _ (fun eps Fm _ => exists x0, forall x : R, x0 <= x -> RawAt eps Fm x)).
    + exact irrC.
    + intros eps Fm ch _ [x0 Hx0].
      exists (Rmax (Rmax x0 (sel1 eps Fm)) (Rmax (fx1 eps Fm + 1) 4)).
      intros x Hle. apply (rows_extend hG eps Fm x0 x Hx0 Hle).
  - intros eps Fm ch Heps _ [Hf He].
    apply linkIRR_of_join_ex; [exact Heps|exact He|exact cIc_pos|exact Hf].
Qed.

(* ===================================================================== *)
(* closed_family_admissible_twist_link                                    *)
(* ===================================================================== *)
Variable Pt0 PtTw Per0 PerTw P10 AtG Serv Dgt AdmRest : forall eps, FamP eps -> Prop.
Variable Adm2At : forall eps (Fm : FamP eps) (x : R) (i : fIx eps Fm x), Prop.
(* adm2 tail: ∃ x0, ∀ x ≥ x0, x1 < x → ∀ i, adm2 (ClosedFamilyAdmissibleTwistLink.lean:26). *)
Definition Adm2 (eps : R) (Fm : FamP eps) : Prop :=
  exists x0, forall (x : R) (i : fIx eps Fm x), x0 <= x -> fx1 eps Fm < x -> Adm2At eps Fm x i.
Hypothesis aPt0 : Closed (D3 3 Acl) (fun eps Fm _ => Pt0 eps Fm).
Hypothesis aPtTw : Closed (D3 3 Acl) (fun eps Fm _ => PtTw eps Fm).
Hypothesis aPer0 : Closed (D3 3 Acl) (fun eps Fm _ => Per0 eps Fm).
Hypothesis aPerTw : Closed (D3 3 Acl) (fun eps Fm _ => PerTw eps Fm).
Hypothesis aP10 : Closed (D3 3 Acl) (fun eps Fm _ => P10 eps Fm).
Hypothesis aAtG : Closed (D3 3 Acl) (fun eps Fm _ => AtG eps Fm).
(* [inventory] servF_of_servT, after hDG : of_class (hc.2.2.2) *)
Hypothesis servF_of_servT : forall eps Fm, DGamSize eps Fm -> Serv eps Fm.
(* [inventory] closed_eventually_levelPrimeCoprimeStabiliser (WithChN 𝒜) 3 *)
Hypothesis levelPrime_closed : Closed (WithChN Acl) (fun eps Fm _ => Dgt eps Fm /\ AtC0 3 eps Fm).
(* [inventory] admissible_family_of_inclusion; the record pack is the conjunction *)
Hypothesis admissible_of_inclusion :
  Closed (D3 3 Acl) (fun eps Fm _ =>
    Pt0 eps Fm /\ PtTw eps Fm /\ Per0 eps Fm /\ PerTw eps Fm /\
    Serv eps Fm /\ P10 eps Fm /\ Dgt eps Fm /\ AtG eps Fm) ->
  Closed (D3 3 Acl) (fun eps Fm _ => Adm2 eps Fm /\ AdmRest eps Fm).

Theorem admissible_twist_link_r : Closed (D3 3 Acl) (fun eps Fm _ => Adm2 eps Fm).
Proof.
  apply (closed_imp _ (fun eps Fm ch => Adm2 eps Fm /\ AdmRest eps Fm)).
  - apply admissible_of_inclusion.
    assert (hDG : Closed (D3 3 Acl) (fun eps Fm _ => DGamSize eps Fm)).
    { apply closed_of_class. intros eps Fm HC _. exact (d3_dg 3 Acl eps Fm HC). }
    assert (hServ : Closed (D3 3 Acl) (fun eps Fm _ => Serv eps Fm)).
    { apply (closed_imp _ (fun eps Fm _ => DGamSize eps Fm)); [exact hDG|].
      intros eps Fm ch _ HD. apply servF_of_servT. exact HD. }
    apply (closed_and _ _ _ aPt0).
    apply (closed_and _ _ _ aPtTw).
    apply (closed_and _ _ _ aPer0).
    apply (closed_and _ _ _ aPerTw).
    apply (closed_and _ _ _ hServ).
    apply (closed_and _ _ _ aP10).
    apply closed_and.
    + apply closed_sub with (C := WithChN Acl).
      * apply (closed_imp _ (fun eps Fm _ => Dgt eps Fm /\ AtC0 3 eps Fm)); [exact levelPrime_closed|].
        intros eps Fm ch _ [Hd _]. exact Hd.
      * intros eps Fm HD. apply (d3_withChN 3 Acl eps Fm HD).
    + exact aAtG.
  - intros eps Fm ch _ [Ha _]. exact Ha.
Qed.

(* ===================================================================== *)
(* selection_closed_of_wu_decay                                           *)
(* ===================================================================== *)
Variable FinX Comp5 ImageFull : forall eps, FamP eps -> Prop.
(* GapHyp at index i.  The two guards are x1 < x and sel ≤ x. *)
Variable GapAt : forall eps (Fm : FamP eps) (x : R) (i : fIx eps Fm x), Prop.
(* miStar at the counting constant C, the scale x and the index i. *)
Variable MiStar : forall eps (Fm : FamP eps) (C x : R) (i : fIx eps Fm x), Prop.
(* SelectionClosedOfWuDecay.lean:28-31.  hc, then ∃ y, then the two guards, y ≤ x, ∀ i. *)
Hypothesis gap_raw : Closed (D3 3 Acl) (fun eps Fm _ =>
  forall hc : D3 3 Acl eps Fm,
    exists y : R, forall (x : R) (i : fIx eps Fm x),
      fx1 eps Fm < x -> sel1 eps Fm <= x -> y <= x -> GapAt eps Fm x i).
(* [inventory] finXRow_of_gap.  Same guards and index as gap_raw. *)
Hypothesis finX_of_gap :
  Closed (D3 3 Acl) (fun eps Fm _ =>
    forall hc : D3 3 Acl eps Fm,
      exists y : R, forall (x : R) (i : fIx eps Fm x),
        fx1 eps Fm < x -> sel1 eps Fm <= x -> y <= x -> GapAt eps Fm x i) ->
  Closed (D3 3 Acl) (fun eps Fm _ => FinX eps Fm).
(* SelectionClosedOfWuDecay.lean:34-36: ∀ hc, ∃ C _ x0, ∀ x, three guards, ∀ i, miStar.
   C, x0, the guards and i all occur. *)
Hypothesis rRows_info : Closed (D3 3 Acl) (fun eps Fm _ =>
  forall hc : D3 3 Acl eps Fm,
    exists (C spare x0 : R), forall (x : R) (i : fIx eps Fm x),
      fx1 eps Fm < x -> sel1 eps Fm <= x -> x0 <= x ->
      MiStar eps Fm C x i /\ spare = spare).
Hypothesis jOn_full : Closed (D3 3 Acl) (fun eps Fm _ => ImageFull eps Fm).
(* [inventory] closed_complementFiveFamily_of_evSel_imageFull.
   hM is the projected tail: the three guards and ∀ i, C dropped. *)
Hypothesis complement_five : forall (hM : Closed (D3 3 Acl) (fun eps Fm _ =>
    forall hc : D3 3 Acl eps Fm,
      exists x0 : R, forall (x : R) (i : fIx eps Fm x),
        fx1 eps Fm < x -> sel1 eps Fm <= x -> x0 <= x ->
        exists C : R, MiStar eps Fm C x i)),
  Closed (D3 3 Acl) (fun eps Fm _ => FinX eps Fm) ->
  Closed (D3 3 Acl) (fun eps Fm _ => ImageFull eps Fm) ->
  Closed (D3 3 Acl) (fun eps Fm _ => Comp5 eps Fm).

Theorem selection_closed_r : Closed (D3 3 Acl) (fun eps Fm _ => Comp5 eps Fm).
Proof.
  assert (jGap : Closed (D3 3 Acl) (fun eps Fm _ =>
      forall hc : D3 3 Acl eps Fm,
        exists y : R, forall (x : R) (i : fIx eps Fm x),
          fx1 eps Fm < x -> sel1 eps Fm <= x -> y <= x -> GapAt eps Fm x i)).
  { exact gap_raw. }
  assert (hM : Closed (D3 3 Acl) (fun eps Fm _ =>
      forall hc : D3 3 Acl eps Fm,
        exists x0 : R, forall (x : R) (i : fIx eps Fm x),
          fx1 eps Fm < x -> sel1 eps Fm <= x -> x0 <= x ->
          exists C : R, MiStar eps Fm C x i)).
  { apply (closed_imp _ (fun eps Fm _ =>
        forall hc : D3 3 Acl eps Fm,
          exists (C spare x0 : R), forall (x : R) (i : fIx eps Fm x),
            fx1 eps Fm < x -> sel1 eps Fm <= x -> x0 <= x ->
            MiStar eps Fm C x i /\ spare = spare)); [exact rRows_info|].
    intros eps Fm ch _ Hrows hc. destruct (Hrows hc) as [C [spare [x0 Hx]]].
    exists x0. intros x i Hx1 Hs Hx0. exists C. exact (proj1 (Hx x i Hx1 Hs Hx0)). }
  apply (complement_five hM); [apply finX_of_gap; exact jGap|exact jOn_full].
Qed.

(* ===================================================================== *)
(* smallLevelRankEq                                                       *)
(* ===================================================================== *)
Variable mOf : forall eps (Fm : FamP eps) (x : R) (i : fIx eps Fm x), nat.
Variable SurjPrj : forall eps (Fm : FamP eps) (x : R) (i : fIx eps Fm x), fin (mOf eps Fm x i) -> Prop.
(* SmallLevelRankEq…lean:25-28.  hc, x1 < x, sel ≤ x, xr ≤ x, i, k : Fin m. *)
Hypothesis zL : Closed (D3 3 Acl) (fun eps Fm _ =>
  forall hc : D3 3 Acl eps Fm, exists xr : R, forall x : R,
    fx1 eps Fm < x -> sel1 eps Fm <= x -> xr <= x ->
    forall (i : fIx eps Fm x) (k : fin (mOf eps Fm x i)), SurjPrj eps Fm x i k).
(* [inventory] rank_zero_of_row_conditions at `max (sel).1 xr`.
   The callbacks that use le_max_left / le_max_right stay inside this hypothesis.
   What is proved here is the call at that max. *)
Hypothesis rank_zero : forall eps Fm xr,
  (forall x : R, fx1 eps Fm < x -> Rmax (sel1 eps Fm) xr <= x ->
     forall (i : fIx eps Fm x) (k : fin (mOf eps Fm x i)), SurjPrj eps Fm x i k) ->
  SmallRank eps Fm.

(* le_max_left gives sel ≤ x; le_max_right gives xr ≤ x. *)
Lemma small_level_at_max : forall eps Fm xr x,
  (forall y : R, fx1 eps Fm < y -> sel1 eps Fm <= y -> xr <= y ->
     forall (i : fIx eps Fm y) (k : fin (mOf eps Fm y i)), SurjPrj eps Fm y i k) ->
  fx1 eps Fm < x -> Rmax (sel1 eps Fm) xr <= x ->
  forall (i : fIx eps Fm x) (k : fin (mOf eps Fm x i)), SurjPrj eps Fm x i k.
Proof.
  intros eps Fm xr x H Hx1 Hmx i k.
  destruct (le_max2 (sel1 eps Fm) xr x Hmx) as [Hs Hx].
  apply H; assumption.
Qed.

Theorem small_level_rank_eq_r : Closed (D3 3 Acl) (fun eps Fm _ => SmallRank eps Fm).
Proof.
  apply (closed_imp _ (fun eps Fm _ =>
      forall hc : D3 3 Acl eps Fm, exists xr : R, forall x : R,
        fx1 eps Fm < x -> sel1 eps Fm <= x -> xr <= x ->
        forall (i : fIx eps Fm x) (k : fin (mOf eps Fm x i)), SurjPrj eps Fm x i k)); [exact zL|].
  intros eps Fm ch HC Hz.
  destruct (Hz HC) as [xr Hxr].
  apply (rank_zero eps Fm xr).
  intros x Hx1 Hmx i k.
  apply (small_level_at_max eps Fm xr x Hxr Hx1 Hmx i k).
Qed.

(* ===================================================================== *)
(* shapeWin's hBR: and / of_class / imp                                   *)
(* ===================================================================== *)
Variable Cut OneMap CszGe Comp2 : forall eps, FamP eps -> Prop.
(* [inventory] cut_of_stable (hMt _) *)
Hypothesis cut_of_stable : forall eps Fm, D3 3 Acl eps Fm -> Cut eps Fm.
(* [inventory] ⟨0, fun j => (hRB i).oneMap j⟩ *)
Hypothesis oneMap_of_hRB : forall eps Fm, D3 3 Acl eps Fm -> OneMap eps Fm.
(* [inventory] closed_Csz_ge_fn _ (fun _ => 0) *)
Hypothesis closed_Csz : Closed (D3 3 Acl) (fun eps Fm _ => CszGe eps Fm).
Hypothesis aC2 : Closed (D3 3 Acl) (fun eps Fm _ => Comp2 eps Fm).
(* [inventory] (r hc hT hD).toRows (wire_sel _ hN) o a (complement_two_of_items c) c5.
   Conclusion is the hDIV arrow topDesWin applies as `aD hT hDG aE divinN`. *)
Hypothesis toRows_wire : forall eps Fm (ch : R),
  (forall hc : D3 3 Acl eps Fm, TuSize eps Fm -> DGamSize eps Fm -> RemAt eps Fm ch) ->
  Cut eps Fm ->
  (forall hc : D3 3 Acl eps Fm,
     exists (C spare x0 : R), forall (x : R) (i : fIx eps Fm x),
       fx1 eps Fm < x -> sel1 eps Fm <= x -> x0 <= x ->
       MiStar eps Fm C x i /\ spare = spare) ->
  OneMap eps Fm -> CszGe eps Fm -> Adm2 eps Fm -> Comp2 eps Fm -> Comp5 eps Fm ->
  TuSize eps Fm -> DGamSize eps Fm -> LinkEta eps Fm -> DivN eps Fm -> HDiv eps Fm.

Theorem bridge_rows_r :
  Closed (D3 3 Acl) (fun eps Fm _ => Adm2 eps Fm) ->
  Closed (D3 3 Acl) (fun eps Fm _ => Comp5 eps Fm) ->
  Closed (D3 3 Acl) (fun eps Fm _ =>
    TuSize eps Fm -> DGamSize eps Fm -> LinkEta eps Fm -> DivN eps Fm -> HDiv eps Fm).
Proof.
  intros hA2 hC5.
  apply (closed_imp _ (fun eps Fm ch =>
      (forall hc : D3 3 Acl eps Fm, TuSize eps Fm -> DGamSize eps Fm -> RemAt eps Fm ch) /\
      Cut eps Fm /\
      (forall hc : D3 3 Acl eps Fm,
         exists (C spare x0 : R), forall (x : R) (i : fIx eps Fm x),
           fx1 eps Fm < x -> sel1 eps Fm <= x -> x0 <= x ->
           MiStar eps Fm C x i /\ spare = spare) /\
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
    intros HU HD HE HDN.
    apply (toRows_wire eps Fm ch Hr Hcut Hrows Hom Hcz Ha Hc2 Hc5 HU HD HE HDN).
Qed.

(* ===================================================================== *)
(* topDesWin (DesWin.lean)                                                *)
(* ===================================================================== *)
(* [inventory] divinN_of_hypV *)
Hypothesis divinN_of_hypV : forall eps Fm, 0 < eps -> hv Fm -> LinkN eps Fm -> SmallRank eps Fm -> DivN eps Fm.
Variable FactDGam MuTuAt MuDGamAt :
  forall eps (Fm : FamP eps) (C x : R) (i : fIx eps Fm x), Prop.
(* MuTu / MuDGam as in SumLogPrimeFactorsLe.lean:720-726. *)
Definition MuTu (eps : R) (Fm : FamP eps) : Prop :=
  exists (C x0 : R), forall (x : R) (i : fIx eps Fm x), x0 <= x -> MuTuAt eps Fm C x i.
Definition MuDGam (eps : R) (Fm : FamP eps) : Prop :=
  exists (C x0 : R), forall (x : R) (i : fIx eps Fm x), x0 <= x -> MuDGamAt eps Fm C x i.
(* [inventory] muTu_of_tuSize : 0 < eps → TuSize → MuTu.  The tendsto proof stays here. *)
Hypothesis muTu_of_tuSize : forall eps Fm, 0 < eps -> TuSize eps Fm -> MuTu eps Fm.
(* [inventory] muDGam_of_fact (SumLogPrimeFactorsLe.lean:756).
   DesWin passes DGamSize; the lemma's parameter is the FactDGam tail.
   dGamSize_fact is that reading, left QEX. *)
Hypothesis dGamSize_fact : forall eps Fm, DGamSize eps Fm ->
  exists (C x0 : R), forall (x : R) (i : fIx eps Fm x), x0 <= x -> FactDGam eps Fm C x i.
Hypothesis muDGam_of_fact : forall eps Fm,
  (exists (C x0 : R), forall (x : R) (i : fIx eps Fm x), x0 <= x -> FactDGam eps Fm C x i) ->
  MuDGam eps Fm.
(* [inventory] linkMu_of_linkDIV Fm hD nuFull muRank muTu muDGam (DesWin.lean:31). *)
Hypothesis linkMu_of_linkDIV : forall eps Fm,
  HDiv eps Fm -> NuFull eps Fm -> MuRank eps Fm -> MuTu eps Fm -> MuDGam eps Fm -> MuLink eps Fm.

Theorem topDesWin_r : forall (C C' E : FamCl) (Cabs C0 eD eL : R),
  DesignExists C0 (WithTw (WithSm C')) ->
  (forall eps Fm, C' eps Fm -> C eps Fm) ->
  (forall eps Fm, C' eps Fm -> E eps Fm) ->
  (forall eps Fm, E eps Fm -> hv Fm) ->
  Closed (Des C) (fun eps Fm _ => LinkN eps Fm) ->
  Closed (Des C) (fun eps Fm _ => TuSize eps Fm -> DGamSize eps Fm -> LinkEta eps Fm -> DivN eps Fm -> HDiv eps Fm) ->
  Closed (Des C) (fun eps Fm _ => LinkEta eps Fm) ->
  Closed (Des C) (fun eps Fm _ => LinkIRR eps Fm) ->
  Closed (Des C) (fun eps Fm _ => SmallRank eps Fm) ->
  Closed (Des C) (fun eps Fm ch => ChosenE C0 eps Fm ch -> NuFull eps Fm /\ MuRank eps Fm) ->
  Closed (Des C) (fun eps Fm _ => LinkG eps Fm) ->
  Closed (Des C) (fun eps Fm _ => TuSize eps Fm -> LinkS C0 eps Fm) ->
  Closed (Des C) (fun eps Fm ch => GLArrow Cabs C0 eD eL eps Fm ch) ->
  FCC E.
Proof.
  intros C C' E Cabs C0 eD eL Hex h1 h2 hV hN hDIV hEta hIRR hZ hRk hG hS hGL.
  assert (Hall : Closed (Des C) (fun eps Fm ch =>
      LinkN eps Fm /\
      (TuSize eps Fm -> DGamSize eps Fm -> LinkEta eps Fm -> DivN eps Fm -> HDiv eps Fm) /\
      LinkEta eps Fm /\ LinkIRR eps Fm /\ SmallRank eps Fm /\
      (ChosenE C0 eps Fm ch -> NuFull eps Fm /\ MuRank eps Fm) /\
      LinkG eps Fm /\ (TuSize eps Fm -> LinkS C0 eps Fm) /\ GLArrow Cabs C0 eD eL eps Fm ch)).
  { apply closed_9; assumption. }
  destruct Hall as [e1 [He1 HA]].
  destruct Hex as [e3 [He3 HEx]].
  destruct (shrink2 e1 e3 He1 He3) as [c [Hc [Hc1 Hc3]]].
  exists eD, eL, c. split; [exact Hc|].
  intros eps Heps Hlt.
  assert (Hle : eps <= c) by lra.
  destruct (HA eps Heps (Rle_trans _ _ _ Hle Hc1)) as [Kpage HK].
  destruct (HEx eps Heps (Rle_trans _ _ _ Hle Hc3) Kpage)
    as [Fm [CH [HC' [Hnn [HS [Hch [Ht Hdg]]]]]]].
  destruct HC' as [Hsm Htw]. destruct Hsm as [HC's HsmF].
  assert (Hdes : Des C eps Fm).
  { apply des_mk; [apply h1; exact HC's|exact HsmF|exact Htw|exact Ht|exact Hdg]. }
  destruct (HK Fm CH Hdes HS) as [aN [aD [aE [aI [aZ [aR [aG [aS aGL]]]]]]]].
  assert (HdN : DivN eps Fm).
  { apply divinN_of_hypV; [exact Heps|apply hV; apply h2; exact HC's|exact aN|exact aZ]. }
  assert (Hd : HDiv eps Fm).
  { apply aD; [exact Ht|exact Hdg|exact aE|exact HdN]. }
  assert (Hm : MuLink eps Fm).
  { apply linkMu_of_linkDIV; [exact Hd|exact (proj1 (aR Hch))|exact (proj2 (aR Hch))|
      exact (muTu_of_tuSize eps Fm Heps Ht)|apply muDGam_of_fact; apply dGamSize_fact; exact Hdg]. }
  assert (Hp : LinkPack Cabs eD eL eps Fm).
  { apply aGL; [exact Ht|exact Hdg|exact Hch|exact aG|exact aS|exact aI|exact Hd|exact Hm]. }
  destruct Hp as [K [cHH [eK [CL [x0 Htie]]]]].
  exists Fm. split; [apply h2; exact HC's|].
  exists K, cHH, eK, CL, x0. intros x Hx Hw. exact (proj2 (Htie x Hx Hw)).
Qed.

(* ===================================================================== *)
(* shapeWin: hsub, the link facts, topDesWin, concluding TopG             *)
(* ===================================================================== *)
(* nRest : TopShape's `N (D3 3 A)`, i.e. Closed _ LinkN.  Not a link fact. *)
Hypothesis nRest : Closed (D3 3 Acl) (fun eps Fm _ => LinkN eps Fm).
Lemma incl_withChN : forall B eps Fm, WithChN (cap Acl B) eps Fm -> WithChN Acl eps Fm.
Proof.
  intros B eps Fm H. destruct H as [[HA _] HN]. split; assumption.
Qed.

Lemma incl_right : forall (A B : FamCl) eps Fm, WithChN (cap A B) eps Fm -> B eps Fm.
Proof.
  intros A B eps Fm H. destruct H as [[_ HB] _]. exact HB.
Qed.

(* D3 3 Acl is Des (WithChN Acl) conjoined with 3 = 3, so a fact on
   D3 3 Acl is a fact on Des (WithChN Acl). *)
Lemma closed_at_des : forall P,
  Closed (D3 3 Acl) P -> Closed (Des (WithChN Acl)) P.
Proof.
  intros P [e [He H]].
  exists e. split; [exact He|].
  intros eps H0 Hle. destruct (H eps H0 Hle) as [k Hk].
  exists k. intros Fm ch Hdes HS. apply Hk; [split; [reflexivity|exact Hdes]|exact HS].
Qed.

Theorem shapeWin_from_links_r : Green -> TG.
Proof.
  intros hG la G hla hH hV.
  set (B := Cls G la).
  assert (Hex : DesignExists 3 (WithTw (WithSm (WithChN (cap Acl B))))).
  { apply link_ex_r. exact (hEx minkowski_bound_rat la G hla hH). }
  destruct link_gl_r as [hRk hGL].
  apply (topDesWin_r (WithChN Acl) (WithChN (cap Acl B)) B 2 3 2 0 Hex).
  - intros eps Fm H. apply (incl_withChN B). exact H.
  - intros eps Fm H. apply (incl_right Acl B). exact H.
  - intros eps Fm HE. apply hV. exact HE.
  - apply closed_at_des. exact nRest.
  - apply closed_at_des. apply bridge_rows_r; [exact admissible_twist_link_r|exact selection_closed_r].
  - apply closed_at_des. exact link_eta_r.
  - apply closed_at_des. apply link_irr_r. exact hG.
  - apply closed_at_des. exact small_level_rank_eq_r.
  - apply closed_at_des. exact hRk.
  - apply closed_at_des. exact link_g_r.
  - apply closed_at_des. exact link_alt_r.
  - apply closed_at_des. exact hGL.
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
