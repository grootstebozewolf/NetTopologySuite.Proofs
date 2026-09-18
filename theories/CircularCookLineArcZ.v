(* ============================================================================
   NetTopologySuite.Proofs.CircularCookLineArcZ
   ----------------------------------------------------------------------------
   Exact chord × three-point-arc classifier + named-root hen mint.

   I_line_arc_q / I_line_arc_z classify a chord (segment P→P1) against the
   circular arc through A, M, C. An extractable seam in the shape of
   CircularCookZ.I_circles_z, not glossary 𝓘 (no γ / [0,1] parameter is
   produced; hens 0/1 are birth certificates of the two radical roots).

       I_line_arc : Hit2 | Hit1 (named root) | Touch | Empty | Decline

   Every decision is a sign test on a polynomial in the coordinates: the
   circumcircle discriminant Δ = b² − 4ac of f(t) = |P + t·d − O|² − r²;
   root ∈ [0,1] from the signs of f(0), f(1), b, b + 2a (no root is ever
   computed); arc-span membership as "same side of chord A–C as M" (the
   test ArcIntersect.arc_span_contains, which ArcSpanAtan2 proves equal to
   the atan2 sector test for every sweep). The chord-side function is affine
   along the segment, so its sign at an irrational root F ± ρ·d is the sign
   of U ± √Δ·κ, decided by comparing U² with Δ·κ². No square root, no atan2.
   Tangency (Δ = 0) has a rational kiss point.

   Tags route the ι gate (SidecarCircIotaGate, cells 3 / 4): (ChordEnd,
   ArcAtStart) and (ChordStart, ArcAtEnd) are the μ joints of cell 3
   (SidecarCircMixed.mixed_joint_params (1,0) / (0,1)); (ChordInterior,
   ArcInterior) is the cell-4 ι candidate (interior_span_params); the other
   endpoint combinations are the half-open or reversed joints of cell 6.

   Decline is degenerate input only: collinear or coincident controls
   (D = 0, which includes the SQL/MM full circle A = C) or a zero-length
   chord. Hit2 mints (hen_plus, hen_minus) — the MintTwo shape of I.7.

   Both forms feed one decision tree, classify_signs, with a record of eleven
   exact signs: q_signs computes them over ℚ, z_signs over ℤ after replacing
   every point X by D·(X − O) ∈ ℤ² (the centre is never formed, each tested
   quantity is a positive multiple of its ℚ counterpart). ℤ ≡ ℚ agreement is
   locked on every integer vector below (each ℚ vector has a ℤ twin); the
   general theorem is exactly "q_signs ∘ lift = z_signs". The partition
   theorem and the ℚ→ℝ soundness bridge to ArcIntersect.arc_chord_intersects
   are the other named next steps (wayfinder map #767; research #772).

   WITNESS topic: overlay · claimId: 0007-line-arc-z · witness: 0007-line-arc-z-locked
   board: ADR-0007
   0-axiom (Q/Z only). No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import ZArith QArith Qfield Bool Lia.
From NTS.Proofs Require Import CircularCookZ.

(* -------------------------------------------------------------------------- *)
(* Result vocabulary.                                                          *)
(* -------------------------------------------------------------------------- *)

Inductive ChordEndTag : Type := ChordInterior | ChordStart | ChordEnd.
Inductive ArcEndTag   : Type := ArcInterior | ArcAtStart | ArcAtEnd.

Record RootTag : Type := mkRootTag { rt_chord : ChordEndTag; rt_arc : ArcEndTag }.

Inductive ILAResult : Type :=
| ILAHit2  (h_plus h_minus : HenZ) (tag_plus tag_minus : RootTag)
| ILAHit1  (r : RadicalRoot) (h : HenZ) (tag : RootTag)
| ILATouch (h : HenZ) (tag : RootTag)
| ILAEmpty
| ILADecline.

(* The three tags the ι gate reads. *)
Definition tag_interior     : RootTag := mkRootTag ChordInterior ArcInterior.  (* ι candidate *)
Definition tag_mu_end_start : RootTag := mkRootTag ChordEnd ArcAtStart.        (* μ joint (1,0) *)
Definition tag_mu_start_end : RootTag := mkRootTag ChordStart ArcAtEnd.        (* μ joint (0,1) *)

(* Comparison helpers. *)
Definition cmp_eqb (a b : comparison) : bool :=
  match a, b with Eq, Eq | Lt, Lt | Gt, Gt => true | _, _ => false end.
Definition is_le0 (c : comparison) : bool := match c with Gt => false | _ => true end.
Definition is_ge0 (c : comparison) : bool := match c with Lt => false | _ => true end.
Definition is_eq0 (c : comparison) : bool := match c with Eq => true | _ => false end.

(* Sign of u + v·√R (R ≥ 0) from sign u, sign v and compare (u·u) (R·v·v). *)
Definition comp_sign_lin_rad (cu cv cuu : comparison) : comparison :=
  match cu, cv with
  | Eq, sv => sv
  | su, Eq => su
  | Gt, Gt => Gt
  | Lt, Lt => Lt
  | su, _  => match cuu with Eq => Eq | Gt => su | Lt => CompOpp su end
  end.

(* On-span from sign σ(X) and sign σ(M): same side of chord A–C, or X ∈ {A, C}. *)
Definition on_span_b (sgX sgM : comparison) : bool :=
  match sgX with Eq => true | _ => cmp_eqb sgX sgM end.

(* -------------------------------------------------------------------------- *)
(* Shared decision tree over exact signs.                                      *)
(* -------------------------------------------------------------------------- *)

(* Everything the classifier decides on: eleven comparisons against 0.
   q_signs / z_signs fill the record over ℚ / ℤ; classify_signs is the one
   decision tree, so the ℤ ≡ ℚ agreement theorem is "the two records agree". *)
Record LineArcSigns : Type := mkLineArcSigns {
  sg_disc  : comparison;  (* Δ = b² − 4ac *)
  sg_f0    : comparison;  (* f(0): power of P *)
  sg_f1    : comparison;  (* f(1): power of P1 *)
  sg_b     : comparison;  (* b       (foot s ≥ 0 ⇔ b ≤ 0) *)
  sg_b2a   : comparison;  (* b + 2a  (foot s ≤ 1 ⇔ b + 2a ≥ 0) *)
  sg_M     : comparison;  (* σ(M): the side of chord A–C carrying the arc *)
  sg_U     : comparison;  (* U = 2a·σ(F): chord-side value at the foot F *)
  sg_kappa : comparison;  (* κ = (C − A) × d: chord-side slope along P→P1 *)
  sg_U2_vs_disc_kappa2 : comparison;  (* compare U² (Δ·κ²): σ(F ± ρd) = sign(U ± √Δ·κ) *)
  sg_A_side : comparison; (* cross(P, P1, A): A on the chord's line ⇔ Eq *)
  sg_tA_minus_s : comparison  (* 2(A − P)·d + b = 2a·(t_A − s): which root is A *)
}.

Definition classify_signs (sd : LineArcSigns) : ILAResult :=
  let s_ge0 := is_le0 (sg_b sd) in
  let s_le1 := is_ge0 (sg_b2a sd) in
  let sgn_sig (cv : comparison) : comparison :=
      comp_sign_lin_rad (sg_U sd) cv (sg_U2_vs_disc_kappa2 sd) in
  let arc_tag (sg root_sign : comparison) : ArcEndTag :=
      match sg with
      | Eq => if is_eq0 (sg_A_side sd) && cmp_eqb (sg_tA_minus_s sd) root_sign
              then ArcAtStart else ArcAtEnd
      | _ => ArcInterior
      end in
  match sg_disc sd with
  | Lt => ILAEmpty
  | Eq =>
      let sgF := sg_U sd in
      if s_ge0 && s_le1 && on_span_b sgF (sg_M sd) then
        let ct := if is_eq0 (sg_b sd) then ChordStart
                  else if is_eq0 (sg_b2a sd) then ChordEnd else ChordInterior in
        ILATouch hen_plus (mkRootTag ct (arc_tag sgF Eq))
      else ILAEmpty
  | Gt =>
      let cP := sg_f0 sd in let cQ := sg_f1 sd in
      let sB := sg_b sd in let sB2 := sg_b2a sd in
      let plus_in01  := (is_le0 cP || s_ge0) && (is_ge0 cQ && s_le1) in
      let minus_in01 := (is_ge0 cP && s_ge0) && (is_le0 cQ || s_le1) in
      let sg_plus  := sgn_sig (sg_kappa sd) in
      let sg_minus := sgn_sig (CompOpp (sg_kappa sd)) in
      let keep_plus  := plus_in01  && on_span_b sg_plus  (sg_M sd) in
      let keep_minus := minus_in01 && on_span_b sg_minus (sg_M sd) in
      let ct_plus  := if is_eq0 cP && cmp_eqb sB Gt then ChordStart
                      else if is_eq0 cQ && cmp_eqb sB2 Gt then ChordEnd else ChordInterior in
      let ct_minus := if is_eq0 cP && cmp_eqb sB Lt then ChordStart
                      else if is_eq0 cQ && cmp_eqb sB2 Lt then ChordEnd else ChordInterior in
      let tag_plus  := mkRootTag ct_plus  (arc_tag sg_plus Gt) in
      let tag_minus := mkRootTag ct_minus (arc_tag sg_minus Lt) in
      match keep_plus, keep_minus with
      | true, true   => ILAHit2 hen_plus hen_minus tag_plus tag_minus
      | true, false  => ILAHit1 RootPlus hen_plus tag_plus
      | false, true  => ILAHit1 RootMinus hen_minus tag_minus
      | false, false => ILAEmpty
      end
  end.

(* -------------------------------------------------------------------------- *)
(* ℚ classifier (specification form).                                          *)
(* -------------------------------------------------------------------------- *)

Open Scope Q_scope.

Record QPt : Type := mkQPt { qx : Q; qy : Q }.

Definition qsgn (q : Q) : comparison := Qcompare q 0.

(* σ: signed area test, = ArcOrient.cross_R_pt on rationals. *)
Definition qcross (A C X : QPt) : Q :=
  (qx C - qx A) * (qy X - qy A) - (qx X - qx A) * (qy C - qy A).

(* 2 × twice the signed area of A M C: the circumcentre denominator
   (CurveGeometry.arc_center). D = 0 ⇔ collinear / coincident controls. *)
Definition qarc_D (A M C : QPt) : Q :=
  2 * (qx A * (qy M - qy C) + qx M * (qy C - qy A) + qx C * (qy A - qy M)).

Definition qchord_L2 (P P1 : QPt) : Q :=
  let dx := qx P1 - qx P in let dy := qy P1 - qy P in dx*dx + dy*dy.

(* The eleven signs over ℚ. Assumes D ≠ 0 and a non-degenerate chord (the
   wrapper Declines otherwise). ox, oy = arc_center (CurveGeometry); r² from A. *)
Definition q_signs (P P1 A M C : QPt) : LineArcSigns :=
  let ax := qx A in let ay := qy A in
  let mx := qx M in let my := qy M in
  let cx := qx C in let cy := qy C in
  let D := qarc_D A M C in
  let dx := qx P1 - qx P in let dy := qy P1 - qy P in
  let L2 := dx*dx + dy*dy in
  let na := ax*ax + ay*ay in let nm := mx*mx + my*my in let nc := cx*cx + cy*cy in
  let ox := (na*(my - cy) + nm*(cy - ay) + nc*(ay - my)) / D in
  let oy := (na*(cx - mx) + nm*(ax - cx) + nc*(mx - ax)) / D in
  let r2 := (ax - ox)*(ax - ox) + (ay - oy)*(ay - oy) in
  let wx := qx P - ox in let wy := qy P - oy in
  let a := L2 in
  let b := 2 * (wx*dx + wy*dy) in
  let c := wx*wx + wy*wy - r2 in
  let disc := b*b - 4*a*c in
  let kap := (cx - ax) * dy - dx * (cy - ay) in
  let U := 2*a*(qcross A C P) - b*kap in
  mkLineArcSigns (qsgn disc) (qsgn c) (qsgn (a + b + c)) (qsgn b) (qsgn (b + 2*a))
                 (qsgn (qcross A C M)) (qsgn U) (qsgn kap)
                 (Qcompare (U*U) (disc*kap*kap))
                 (qsgn (qcross P P1 A))
                 (qsgn (2*((ax - qx P)*dx + (ay - qy P)*dy) + b)).

Definition I_line_arc_q (P P1 A M C : QPt) : ILAResult :=
  if Qeq_bool (qarc_D A M C) 0 then ILADecline
  else if Qeq_bool (qchord_L2 P P1) 0 then ILADecline
  else classify_signs (q_signs P P1 A M C).

Close Scope Q_scope.

(* -------------------------------------------------------------------------- *)
(* ℤ classifier (extraction seam; mirrors I_CIRCULAR's digits-only wire).      *)
(* -------------------------------------------------------------------------- *)

Open Scope Z_scope.

Record ZPt : Type := mkZPt { zx : Z; zy : Z }.

Definition zsgn (z : Z) : comparison := Z.compare z 0.

Definition zcross (A C X : ZPt) : Z :=
  (zx C - zx A) * (zy X - zy A) - (zx X - zx A) * (zy C - zy A).

Definition zarc_D (A M C : ZPt) : Z :=
  2 * (zx A * (zy M - zy C) + zx M * (zy C - zy A) + zx C * (zy A - zy M)).

(* The eleven signs over ℤ: every point X is replaced by D·(X − O) ∈ ℤ²; the
   centre is never formed. a, b, c carry D², disc D⁴, U D²: the same signs. *)
Definition z_signs (P P1 A M C : ZPt) : LineArcSigns :=
  let ax := zx A in let ay := zy A in
  let mx := zx M in let my := zy M in
  let cx := zx C in let cy := zy C in
  let D := zarc_D A M C in
  let dx := zx P1 - zx P in let dy := zy P1 - zy P in
  let na := ax*ax + ay*ay in let nm := mx*mx + my*my in let nc := cx*cx + cy*cy in
  let Nx := na*(my - cy) + nm*(cy - ay) + nc*(ay - my) in   (* D · ox *)
  let Ny := na*(cx - mx) + nm*(ax - cx) + nc*(mx - ax) in   (* D · oy *)
  let px' := D * zx P - Nx in let py' := D * zy P - Ny in   (* D (P − O) *)
  let ax' := D * ax - Nx in let ay' := D * ay - Ny in       (* D (A − O) *)
  let dx' := D * dx in let dy' := D * dy in                 (* D d *)
  let a := dx'*dx' + dy'*dy' in                             (* D² L2 *)
  let b := 2 * (px'*dx' + py'*dy') in                       (* D² b *)
  let c := px'*px' + py'*py' - (ax'*ax' + ay'*ay') in       (* D² c *)
  let disc := b*b - 4*a*c in                                (* D⁴ disc *)
  let kap := (cx - ax) * dy - dx * (cy - ay) in
  let U := 2*a*(zcross A C P) - b*kap in                    (* D² U *)
  mkLineArcSigns (zsgn disc) (zsgn c) (zsgn (a + b + c)) (zsgn b) (zsgn (b + 2*a))
                 (zsgn (zcross A C M)) (zsgn U) (zsgn kap)
                 (Z.compare (U*U) (disc*kap*kap))
                 (zsgn (zcross P P1 A))
                 (zsgn (2*((ax' - px')*dx' + (ay' - py')*dy') + b)).

Definition I_line_arc_z (P P1 A M C : ZPt) : ILAResult :=
  if zarc_D A M C =? 0 then ILADecline
  else if (zx P1 - zx P =? 0) && (zy P1 - zy P =? 0) then ILADecline
  else classify_signs (z_signs P P1 A M C).

Close Scope Z_scope.

(* -------------------------------------------------------------------------- *)
(* lift : ZPt -> QPt, the embedding the general agreement theorem is stated   *)
(* over ("q_signs ∘ lift = z_signs", header above). Landed here: the          *)
(* embedding itself, plus the primitive identities (cross, D, chord L2) any   *)
(* such proof needs — each closed by pushing inject_Z through +/-/*, since    *)
(* qcross/qarc_D/qchord_L2 and zcross/zarc_D are literally the same formula   *)
(* over Q and Z. The full q_signs ∘ lift = z_signs theorem — which additionally *)
(* has to track the D²/D⁴ scaling through the division in ox/oy — is not      *)
(* attempted here; it stays the named next step (0007-line-arc-z, #784).      *)
(* -------------------------------------------------------------------------- *)

Definition lift_pt (p : ZPt) : QPt := mkQPt (inject_Z (zx p)) (inject_Z (zy p)).

Lemma inject_Z_minus :
  forall x y : Z, inject_Z (x - y) = (inject_Z x - inject_Z y)%Q.
Proof.
  intros x y. unfold Z.sub.
  rewrite inject_Z_plus, inject_Z_opp. reflexivity.
Qed.

Ltac push_inject_Z :=
  repeat first
    [ rewrite <- inject_Z_plus
    | rewrite <- inject_Z_minus
    | rewrite <- inject_Z_mult
    | rewrite <- inject_Z_opp ].

Lemma lift_qcross :
  forall A C X : ZPt,
    qcross (lift_pt A) (lift_pt C) (lift_pt X) = inject_Z (zcross A C X).
Proof.
  intros A C X. unfold qcross, zcross, lift_pt. simpl.
  push_inject_Z. reflexivity.
Qed.

Lemma lift_qarc_D :
  forall A M C : ZPt,
    qarc_D (lift_pt A) (lift_pt M) (lift_pt C) = inject_Z (zarc_D A M C).
Proof.
  intros A M C. unfold qarc_D, zarc_D, lift_pt. simpl.
  push_inject_Z. reflexivity.
Qed.

Lemma lift_qchord_L2 :
  forall P P1 : ZPt,
    qchord_L2 (lift_pt P) (lift_pt P1)
      = inject_Z ((zx P1 - zx P) * (zx P1 - zx P)
                  + (zy P1 - zy P) * (zy P1 - zy P)).
Proof.
  intros P P1. unfold qchord_L2, lift_pt. simpl.
  push_inject_Z. reflexivity.
Qed.

(* Decline agrees under lift: both forms Decline on exactly the same          *)
(* degenerate condition, read through the embedding.                          *)
Lemma lift_decline_iff :
  forall P P1 A M C : ZPt,
    (qarc_D (lift_pt A) (lift_pt M) (lift_pt C) == 0
     \/ qchord_L2 (lift_pt P) (lift_pt P1) == 0)%Q
    <-> (zarc_D A M C = 0
         \/ (zx P1 - zx P) * (zx P1 - zx P)
            + (zy P1 - zy P) * (zy P1 - zy P) = 0)%Z.
Proof.
  intros P P1 A M C.
  rewrite lift_qarc_D, lift_qchord_L2.
  unfold Qeq. simpl.
  rewrite ? Z.mul_1_r.
  split; intros [H | H]; [left | right | left | right];
    (apply inject_Z_injective; rewrite H; reflexivity) || exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* Structure: constructors are distinct; the kernels never Decline; Decline    *)
(* is exactly degenerate input; hens are the canonical birth certificates.    *)
(* -------------------------------------------------------------------------- *)

Lemma ILAEmpty_neq_ILADecline : ILAEmpty <> ILADecline.
Proof. discriminate. Qed.

Lemma ILATouch_neq_ILAEmpty : forall h t, ILATouch h t <> ILAEmpty.
Proof. intros. discriminate. Qed.

Lemma ILAHit1_neq_ILATouch : forall r h t h' t', ILAHit1 r h t <> ILATouch h' t'.
Proof. intros. discriminate. Qed.

Lemma ILAHit2_neq_ILAHit1 : forall hp hm tp tm r h t, ILAHit2 hp hm tp tm <> ILAHit1 r h t.
Proof. intros. discriminate. Qed.

Ltac ila_cases :=
  repeat match goal with
  | |- context [match ?c with Eq => _ | Lt => _ | Gt => _ end] =>
      match type of c with comparison => destruct c end
  | |- context [match ?b with true => _ | false => _ end] =>
      match type of b with bool => destruct b end
  end.

Lemma classify_signs_not_decline :
  forall sd, classify_signs sd <> ILADecline.
Proof.
  intro sd. unfold classify_signs. cbv zeta beta.
  ila_cases; discriminate.
Qed.

(* WITNESS {"claimId":"0007-line-arc-z","topic":"overlay","lemma":"I_line_arc_z_decline_iff","title":"Exact chord x arc classifier Declines exactly on degenerate input: collinear or coincident controls (D = 0) or a zero-length chord","file":"theories/CircularCookLineArcZ.v","witness":"0007-line-arc-z-locked","board":"ADR-0007"} *)

Lemma I_line_arc_z_decline_iff :
  forall P P1 A M C,
    I_line_arc_z P P1 A M C = ILADecline <->
    (zarc_D A M C = 0 \/ (zx P1 - zx P = 0 /\ zy P1 - zy P = 0))%Z.
Proof.
  intros P P1 A M C. unfold I_line_arc_z.
  destruct (zarc_D A M C =? 0)%Z eqn:HD.
  - apply Z.eqb_eq in HD. split; intros; [left; exact HD | reflexivity].
  - apply Z.eqb_neq in HD.
    destruct ((zx P1 - zx P =? 0) && (zy P1 - zy P =? 0))%Z eqn:Hd.
    + apply andb_true_iff in Hd. destruct Hd as [H1 H2].
      apply Z.eqb_eq in H1, H2.
      split; intros; [right; split; assumption | reflexivity].
    + split.
      * intro H. exfalso. exact (classify_signs_not_decline _ H).
      * intros [H | [H1 H2]]; [contradiction |].
        apply Z.eqb_eq in H1, H2. rewrite H1, H2 in Hd. discriminate.
Qed.

Lemma I_line_arc_q_decline_iff :
  forall P P1 A M C,
    I_line_arc_q P P1 A M C = ILADecline <->
    (qarc_D A M C == 0 \/ qchord_L2 P P1 == 0)%Q.
Proof.
  intros P P1 A M C. unfold I_line_arc_q.
  destruct (Qeq_bool (qarc_D A M C) 0) eqn:HD.
  - apply Qeq_bool_iff in HD. split; intros; [left; exact HD | reflexivity].
  - apply Qeq_bool_neq in HD.
    destruct (Qeq_bool (qchord_L2 P P1) 0) eqn:HL.
    + apply Qeq_bool_iff in HL. split; intros; [right; exact HL | reflexivity].
    + apply Qeq_bool_neq in HL. split.
      * intro H. exfalso. exact (classify_signs_not_decline _ H).
      * intros [H | H]; contradiction.
Qed.

(* Hens are birth certificates: Hit2 mints (hen_plus, hen_minus) in that
   order (the MintTwo shape), Hit1 mints the hen of its named root, Touch
   mints hen_plus (as CircularCookZ.mint_touch). *)
Definition hens_canonical (r : ILAResult) : Prop :=
  match r with
  | ILAHit2 hp hm _ _ => hp = hen_plus /\ hm = hen_minus
  | ILAHit1 rt h _    => h = hen_of_root rt
  | ILATouch h _      => h = hen_plus
  | ILAEmpty | ILADecline => True
  end.

Lemma classify_signs_hens :
  forall sd, hens_canonical (classify_signs sd).
Proof.
  intro sd. unfold classify_signs. cbv zeta beta.
  ila_cases; simpl; auto.
Qed.

(* WITNESS {"claimId":"0007-line-arc-z","topic":"overlay","lemma":"I_line_arc_z_hens","title":"Exact chord x arc classifier mints only canonical hens: Hit2 = (hen_plus, hen_minus), Hit1 = hen of its named root, Touch = hen_plus","file":"theories/CircularCookLineArcZ.v","witness":"0007-line-arc-z-locked","board":"ADR-0007"} *)

Lemma I_line_arc_z_hens :
  forall P P1 A M C, hens_canonical (I_line_arc_z P P1 A M C).
Proof.
  intros. unfold I_line_arc_z.
  destruct (zarc_D A M C =? 0)%Z; [exact I |].
  destruct ((zx P1 - zx P =? 0) && (zy P1 - zy P =? 0))%Z; [exact I |].
  apply classify_signs_hens.
Qed.

Lemma I_line_arc_q_hens :
  forall P P1 A M C, hens_canonical (I_line_arc_q P P1 A M C).
Proof.
  intros. unfold I_line_arc_q.
  destruct (Qeq_bool (qarc_D A M C) 0); [exact I |].
  destruct (Qeq_bool (qchord_L2 P P1) 0); [exact I |].
  apply classify_signs_hens.
Qed.

(* -------------------------------------------------------------------------- *)
(* Δ = 4·L2·h²: the parametric discriminant equals the oracle's exact foot     *)
(* form (ARC_SEGMENT_XY's h2q), so its count decision is already this sign.   *)
(* -------------------------------------------------------------------------- *)

Open Scope Q_scope.

Lemma line_arc_disc_eq_four_L2_h2 :
  forall px py qx qy ox oy r2 : Q,
    let dx := qx - px in let dy := qy - py in
    let L2 := dx*dx + dy*dy in
    let s := ((ox - px)*dx + (oy - py)*dy) / L2 in
    let fx := px + s*dx in let fy := py + s*dy in
    let d2 := (ox - fx)*(ox - fx) + (oy - fy)*(oy - fy) in
    let h2 := r2 - d2 in
    let wx := px - ox in let wy := py - oy in
    let a := L2 in let b := 2*(wx*dx + wy*dy) in let c := wx*wx + wy*wy - r2 in
    ~ L2 == 0 ->
    b*b - 4*a*c == 4 * L2 * h2.
Proof.
  intros px py qx qy ox oy r2. cbv zeta. intro H. field. exact H.
Qed.

Close Scope Q_scope.

(* -------------------------------------------------------------------------- *)
(* Locked vectors (research #772 §12). Fixtures on the circle O = (0,0), r = 5 *)
(* unless noted; arcL = locked_mixed_cs, arcQ = span_arc_A,                    *)
(* arcMaj = the 270° major arc, arcR / arcRQ / arcG = GEOS ILI / test 30.      *)
(* Every expectation was produced by hand and is checked by vm_compute here.   *)
(* -------------------------------------------------------------------------- *)

Definition zp (x y : Z) : ZPt := mkZPt x y.
Definition qp (x y : Z) : QPt := mkQPt (x # 1) (y # 1).
Definition q_of_z (p : ZPt) : QPt := qp (zx p) (zy p).

(* Arc fixtures, declared once over ℤ and lifted to ℚ. *)
Definition zU_A := zp (-5) 0.    Definition zU_M := zp 0 5.       Definition zU_C := zp 5 0.       (* upper semicircle *)
Definition zL_A := zp 5 0.       Definition zL_M := zp 0 (-5).    Definition zL_C := zp (-5) 0.    (* lower semicircle *)
Definition zR_A := zp 0 5.       Definition zR_M := zp 5 0.       Definition zR_C := zp 0 (-5).    (* right semicircle *)
Definition zQ_A := zp 5 0.       Definition zQ_M := zp 3 4.       Definition zQ_C := zp 0 5.       (* quarter *)
Definition zMaj_A := zp 5 0.     Definition zMaj_M := zp (-5) 0.  Definition zMaj_C := zp 0 5.     (* 270° major arc *)
Definition zRQ_A := zp 0 5.      Definition zRQ_M := zp 3 4.      Definition zRQ_C := zp 5 0.      (* GEOS test_3d quarter *)
Definition zG_A := zp 0 0.       Definition zG_M := zp 2 2.       Definition zG_C := zp 4 0.       (* GEOS test 30: O=(2,0), r=2 *)

Definition arcU_A := q_of_z zU_A.     Definition arcU_M := q_of_z zU_M.     Definition arcU_C := q_of_z zU_C.
Definition arcL_A := q_of_z zL_A.     Definition arcL_M := q_of_z zL_M.     Definition arcL_C := q_of_z zL_C.
Definition arcR_A := q_of_z zR_A.     Definition arcR_M := q_of_z zR_M.     Definition arcR_C := q_of_z zR_C.
Definition arcQ_A := q_of_z zQ_A.     Definition arcQ_M := q_of_z zQ_M.     Definition arcQ_C := q_of_z zQ_C.
Definition arcMaj_A := q_of_z zMaj_A. Definition arcMaj_M := q_of_z zMaj_M. Definition arcMaj_C := q_of_z zMaj_C.
Definition arcRQ_A := q_of_z zRQ_A.   Definition arcRQ_M := q_of_z zRQ_M.   Definition arcRQ_C := q_of_z zRQ_C.
Definition arcG_A := q_of_z zG_A.     Definition arcG_M := q_of_z zG_M.     Definition arcG_C := q_of_z zG_C.

(* ℚ vectors *)
Lemma lv_T01 : I_line_arc_q (qp (-5) 4) (qp 5 4) arcU_A arcU_M arcU_C = ILAHit2 hen_plus hen_minus tag_interior tag_interior.
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T02 : I_line_arc_q (qp 0 4) (qp 5 4) arcU_A arcU_M arcU_C = ILAHit1 RootPlus hen_plus tag_interior.
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T03 : I_line_arc_q (qp (-5) 5) (qp 5 5) arcU_A arcU_M arcU_C = ILATouch hen_plus tag_interior.   (* tangent at M *)
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T04 : I_line_arc_q (qp (-5) 6) (qp 5 6) arcU_A arcU_M arcU_C = ILAEmpty.               (* Δ < 0 *)
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T05 : I_line_arc_q (qp (-5) (-4)) (qp 5 (-4)) arcU_A arcU_M arcU_C = ILAEmpty.         (* both roots off the arc *)
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T06 : I_line_arc_q (qp (-1) 4) (qp 1 4) arcU_A arcU_M arcU_C = ILAEmpty.               (* both roots off the chord *)
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T07 : I_line_arc_q (qp 3 4) (qp 3 0) arcU_A arcU_M arcU_C
  = ILAHit1 RootMinus hen_minus (mkRootTag ChordStart ArcInterior).                              (* half-open joint *)
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T08 : I_line_arc_q (qp (-5) 0) (qp 5 0) arcL_A arcL_M arcL_C
  = ILAHit2 hen_plus hen_minus tag_mu_end_start tag_mu_start_end.                                (* double μ joint *)
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T09 : I_line_arc_q (qp 5 5) (qp 5 0) arcR_A arcR_M arcR_C
  = ILATouch hen_plus (mkRootTag ChordEnd ArcInterior).                                          (* tangent at chord end *)
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T10 : I_line_arc_q (qp 0 10) (qp 0 5) arcR_A arcR_M arcR_C
  = ILAHit1 RootMinus hen_minus tag_mu_end_start.                                                (* single μ joint (1,0) *)
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T11 : I_line_arc_q (qp (-5) 4) (qp 5 4) arcMaj_A arcMaj_M arcMaj_C = ILAHit1 RootMinus hen_minus tag_interior.  (* major arc *)
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T12 : I_line_arc_q (qp (-5) (-4)) (qp 5 (-4)) arcMaj_A arcMaj_M arcMaj_C = ILAHit2 hen_plus hen_minus tag_interior tag_interior.
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T13 : I_line_arc_q (qp (-6) 0) (qp 6 0) arcU_A arcU_M arcU_C
  = ILAHit2 hen_plus hen_minus (mkRootTag ChordInterior ArcAtEnd) (mkRootTag ChordInterior ArcAtStart). (* κ = 0 ∧ σ_F = 0 *)
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T14 : I_line_arc_q (qp 1 5) (qp 5 5) arcU_A arcU_M arcU_C = ILAEmpty.                  (* tangent point off the chord *)
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T15 : I_line_arc_q (qp (-5) 5) (qp 5 5) arcL_A arcL_M arcL_C = ILAEmpty.               (* tangent on the complementary arc *)
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T16a : I_line_arc_q (qp 0 1) (qp 1 1) (qp 0 0) (qp 1 0) (qp 2 0) = ILADecline.        (* collinear controls *)
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T16b : I_line_arc_q (qp 1 1) (qp 1 1) arcU_A arcU_M arcU_C = ILADecline.               (* zero-length chord *)
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T16c : I_line_arc_q (qp 0 1) (qp 1 1) (qp 0 0) (qp 0 0) (qp 1 1) = ILADecline.        (* coincident controls *)
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T16d : I_line_arc_q (qp 0 1) (qp 1 1) (qp 5 0) (qp (-5) 0) (qp 5 0) = ILADecline.     (* full circle A = C *)
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T17q : I_line_arc_q (mkQPt (3#2) 0) (mkQPt (3#2) (5#2))
                             (mkQPt (5#2) 0) (mkQPt (3#2) 2) (mkQPt 0 (5#2))
  = ILAHit1 RootPlus hen_plus tag_interior.                                                                (* rational coordinates *)
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T17z : I_line_arc_z (zp 3 0) (zp 3 5) (zp 5 0) (zp 3 4) (zp 0 5) = ILAHit1 RootPlus hen_plus tag_interior. (* = lv_T17q × 2 *)
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T18 : I_line_arc_q (qp 0 (-5)) (qp 0 6) arcQ_A arcQ_M arcQ_C
  = ILAHit1 RootPlus hen_plus (mkRootTag ChordInterior ArcAtEnd).                                (* U² = Δκ² branch *)
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T19 : I_line_arc_q (qp 1 0) (qp 3 4) arcG_A arcG_M arcG_C = ILAHit1 RootPlus hen_plus tag_interior.   (* GEOS test 30 *)
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T20 : I_line_arc_q (qp 4 5) (qp 4 (-5)) arcR_A arcR_M arcR_C = ILAHit2 hen_plus hen_minus tag_interior tag_interior. (* GEOS ILI 3a *)
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T21 : I_line_arc_q (qp 4 5) (qp 4 (-5)) arcRQ_A arcRQ_M arcRQ_C = ILAHit1 RootMinus hen_minus tag_interior. (* GEOS ILI 3d *)
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T22 : I_line_arc_q (qp 4 5) (qp 4 0) arcR_A arcR_M arcR_C = ILAHit1 RootMinus hen_minus tag_interior.   (* GEOS ILI 3e *)
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T24 : I_line_arc_q (qp 5 0) (qp 5 5) arcQ_A arcQ_M arcQ_C
  = ILATouch hen_plus (mkRootTag ChordStart ArcAtStart).                                         (* tangent at P = A: reversed joint *)
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T25 : I_line_arc_q (qp 5 0) (qp 0 0) arcQ_A arcQ_M arcQ_C
  = ILAHit1 RootMinus hen_minus (mkRootTag ChordStart ArcAtStart).
Proof. vm_compute. reflexivity. Qed.

(* ℤ twins: the extraction form agrees with the ℚ form on every integer vector *)

Lemma lv_Z01 : I_line_arc_z (zp (-5) 4) (zp 5 4) zU_A zU_M zU_C = ILAHit2 hen_plus hen_minus tag_interior tag_interior. Proof. vm_compute. reflexivity. Qed.
Lemma lv_Z02 : I_line_arc_z (zp 0 4) (zp 5 4) zU_A zU_M zU_C = ILAHit1 RootPlus hen_plus tag_interior. Proof. vm_compute. reflexivity. Qed.
Lemma lv_Z03 : I_line_arc_z (zp (-5) 5) (zp 5 5) zU_A zU_M zU_C = ILATouch hen_plus tag_interior. Proof. vm_compute. reflexivity. Qed.
Lemma lv_Z04 : I_line_arc_z (zp (-5) 6) (zp 5 6) zU_A zU_M zU_C = ILAEmpty. Proof. vm_compute. reflexivity. Qed.
Lemma lv_Z05 : I_line_arc_z (zp (-5) (-4)) (zp 5 (-4)) zU_A zU_M zU_C = ILAEmpty. Proof. vm_compute. reflexivity. Qed.
Lemma lv_Z06 : I_line_arc_z (zp (-1) 4) (zp 1 4) zU_A zU_M zU_C = ILAEmpty. Proof. vm_compute. reflexivity. Qed.
Lemma lv_Z07 : I_line_arc_z (zp 3 4) (zp 3 0) zU_A zU_M zU_C = ILAHit1 RootMinus hen_minus (mkRootTag ChordStart ArcInterior). Proof. vm_compute. reflexivity. Qed.
Lemma lv_Z08 : I_line_arc_z (zp (-5) 0) (zp 5 0) zL_A zL_M zL_C = ILAHit2 hen_plus hen_minus tag_mu_end_start tag_mu_start_end. Proof. vm_compute. reflexivity. Qed.
Lemma lv_Z09 : I_line_arc_z (zp 5 5) (zp 5 0) zR_A zR_M zR_C = ILATouch hen_plus (mkRootTag ChordEnd ArcInterior). Proof. vm_compute. reflexivity. Qed.
Lemma lv_Z10 : I_line_arc_z (zp 0 10) (zp 0 5) zR_A zR_M zR_C = ILAHit1 RootMinus hen_minus tag_mu_end_start. Proof. vm_compute. reflexivity. Qed.
Lemma lv_Z11 : I_line_arc_z (zp (-5) 4) (zp 5 4) zMaj_A zMaj_M zMaj_C = ILAHit1 RootMinus hen_minus tag_interior. Proof. vm_compute. reflexivity. Qed.
Lemma lv_Z12 : I_line_arc_z (zp (-5) (-4)) (zp 5 (-4)) zMaj_A zMaj_M zMaj_C = ILAHit2 hen_plus hen_minus tag_interior tag_interior. Proof. vm_compute. reflexivity. Qed.
Lemma lv_Z13 : I_line_arc_z (zp (-6) 0) (zp 6 0) zU_A zU_M zU_C = ILAHit2 hen_plus hen_minus (mkRootTag ChordInterior ArcAtEnd) (mkRootTag ChordInterior ArcAtStart). Proof. vm_compute. reflexivity. Qed.
Lemma lv_Z14 : I_line_arc_z (zp 1 5) (zp 5 5) zU_A zU_M zU_C = ILAEmpty. Proof. vm_compute. reflexivity. Qed.
Lemma lv_Z15 : I_line_arc_z (zp (-5) 5) (zp 5 5) zL_A zL_M zL_C = ILAEmpty. Proof. vm_compute. reflexivity. Qed.
Lemma lv_Z16a : I_line_arc_z (zp 0 1) (zp 1 1) (zp 0 0) (zp 1 0) (zp 2 0) = ILADecline. Proof. vm_compute. reflexivity. Qed.
Lemma lv_Z16b : I_line_arc_z (zp 1 1) (zp 1 1) zU_A zU_M zU_C = ILADecline. Proof. vm_compute. reflexivity. Qed.
Lemma lv_Z16c : I_line_arc_z (zp 0 1) (zp 1 1) (zp 0 0) (zp 0 0) (zp 1 1) = ILADecline. Proof. vm_compute. reflexivity. Qed.
Lemma lv_Z16d : I_line_arc_z (zp 0 1) (zp 1 1) (zp 5 0) (zp (-5) 0) (zp 5 0) = ILADecline. Proof. vm_compute. reflexivity. Qed.
Lemma lv_Z18 : I_line_arc_z (zp 0 (-5)) (zp 0 6) zQ_A zQ_M zQ_C = ILAHit1 RootPlus hen_plus (mkRootTag ChordInterior ArcAtEnd). Proof. vm_compute. reflexivity. Qed.
Lemma lv_Z19 : I_line_arc_z (zp 1 0) (zp 3 4) zG_A zG_M zG_C = ILAHit1 RootPlus hen_plus tag_interior. Proof. vm_compute. reflexivity. Qed.
Lemma lv_Z20 : I_line_arc_z (zp 4 5) (zp 4 (-5)) zR_A zR_M zR_C = ILAHit2 hen_plus hen_minus tag_interior tag_interior. Proof. vm_compute. reflexivity. Qed.
Lemma lv_Z21 : I_line_arc_z (zp 4 5) (zp 4 (-5)) zRQ_A zRQ_M zRQ_C = ILAHit1 RootMinus hen_minus tag_interior. Proof. vm_compute. reflexivity. Qed.
Lemma lv_Z22 : I_line_arc_z (zp 4 5) (zp 4 0) zR_A zR_M zR_C = ILAHit1 RootMinus hen_minus tag_interior. Proof. vm_compute. reflexivity. Qed.
Lemma lv_Z24 : I_line_arc_z (zp 5 0) (zp 5 5) zQ_A zQ_M zQ_C = ILATouch hen_plus (mkRootTag ChordStart ArcAtStart). Proof. vm_compute. reflexivity. Qed.
Lemma lv_Z25 : I_line_arc_z (zp 5 0) (zp 0 0) zQ_A zQ_M zQ_C = ILAHit1 RootMinus hen_minus (mkRootTag ChordStart ArcAtStart). Proof. vm_compute. reflexivity. Qed.

(* Reversals: chord reversal keeps the class and flips the named root (oracle I3);
   arc reversal (A,M,C) → (C,M,A) keeps the class and swaps the arc tags (I4). *)
Lemma lv_T01_rev : I_line_arc_q (qp 5 4) (qp (-5) 4) arcU_A arcU_M arcU_C = ILAHit2 hen_plus hen_minus tag_interior tag_interior.
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T02_rev : I_line_arc_q (qp 5 4) (qp 0 4) arcU_A arcU_M arcU_C = ILAHit1 RootMinus hen_minus tag_interior.
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T10_arcrev : I_line_arc_q (qp 0 10) (qp 0 5) arcR_C arcR_M arcR_A = ILAHit1 RootMinus hen_minus (mkRootTag ChordEnd ArcAtEnd).
Proof. vm_compute. reflexivity. Qed.
Lemma lv_T11_arcrev : I_line_arc_q (qp (-5) 4) (qp 5 4) arcMaj_C arcMaj_M arcMaj_A = ILAHit1 RootMinus hen_minus tag_interior.
Proof. vm_compute. reflexivity. Qed.
Lemma lv_Z01_rev : I_line_arc_z (zp 5 4) (zp (-5) 4) zU_A zU_M zU_C = ILAHit2 hen_plus hen_minus tag_interior tag_interior. Proof. vm_compute. reflexivity. Qed.
Lemma lv_Z02_rev : I_line_arc_z (zp 5 4) (zp 0 4) zU_A zU_M zU_C = ILAHit1 RootMinus hen_minus tag_interior. Proof. vm_compute. reflexivity. Qed.
Lemma lv_Z10_arcrev : I_line_arc_z (zp 0 10) (zp 0 5) zR_C zR_M zR_A = ILAHit1 RootMinus hen_minus (mkRootTag ChordEnd ArcAtEnd). Proof. vm_compute. reflexivity. Qed.
Lemma lv_Z11_arcrev : I_line_arc_z (zp (-5) 4) (zp 5 4) zMaj_C zMaj_M zMaj_A = ILAHit1 RootMinus hen_minus tag_interior. Proof. vm_compute. reflexivity. Qed.

Print Assumptions lift_qcross.
Print Assumptions lift_qarc_D.
Print Assumptions lift_qchord_L2.
Print Assumptions lift_decline_iff.
Print Assumptions line_arc_disc_eq_four_L2_h2.
Print Assumptions classify_signs_not_decline.
Print Assumptions classify_signs_hens.
Print Assumptions I_line_arc_z_decline_iff.
Print Assumptions I_line_arc_q_decline_iff.
Print Assumptions I_line_arc_z_hens.
Print Assumptions I_line_arc_q_hens.
Print Assumptions lv_T01.
Print Assumptions lv_T03.
Print Assumptions lv_T08.
Print Assumptions lv_T11.
Print Assumptions lv_T13.
Print Assumptions lv_T18.
Print Assumptions lv_T17q.
Print Assumptions lv_T17z.
Print Assumptions lv_Z01.
Print Assumptions lv_Z08.
Print Assumptions lv_Z13.
Print Assumptions lv_Z16d.
Print Assumptions lv_Z25.
Print Assumptions lv_T10_arcrev.
Print Assumptions lv_Z10_arcrev.
