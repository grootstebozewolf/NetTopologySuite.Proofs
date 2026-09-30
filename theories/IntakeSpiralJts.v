(* ============================================================================
   NetTopologySuite.Proofs.IntakeSpiralJts
   ----------------------------------------------------------------------------
   SPIRALCURVE arm and the JTS clothoid decline taxonomy
   (claimId 0007-intake-spiral, witness 0007-intake-spiral).
   Not a remint of 0007-intake-mkclothoid.

   ISO 13249-3 §4.2.12 SPIRALCURVE is start-placed: LOCATION
   at the start, LENGTH, STARTCURVATURE, ENDCURVATURE. ISO
   CLOTHOID is inflection-placed (A, sd, ed). The mapper is
   IntakeSpiralFront: a clothoid spiral bags norm2 or declines
   by name. cert_of_spiral still returns
   CD_SpiralClothoidNotYet. That is the taxonomy, not the
   mapper result. Every other spiral kind is SpiralOther and
   declines ID_SpiralOther. Not a silent failure.

   JTS CLOTHOID(k0,k1,L) is the same taxonomy. Length is tested
   first: L <= 0 is CD_JtsNonPositiveLength. The example5 triple
   (0, 5/1000, 80) is JC_Example5 and the walker still bags
   locked_clothoid_egg. Every other positive triple is
   CD_JtsTripleNotYet (intake id ID_JtsClothoidNotYet).

   CertDecline is the decline taxonomy later emit can reuse.
   MemberState is the carrier the compound fold will thread
   (end point, tangent, curvature). This letter does not fold
   members, does not discharge JTS G1, and does not prove
   parse ∘ emit = id. Those three stay Prop obligations in
   IntakeSpiralJtsMap. Norm2 is ClothoidNorm2, not a marker.

   ADR-0005: this classification is lenient intake. It is not
   isValid. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance IsoClothoidIntake.
Local Open Scope R_scope.

(* ISO 13249-3 §4.2.12 names other than clothoid. Clothoid is
   SpiralOfClothoid, not a nameplate inside SpiralOther. *)
Inductive SpiralOtherKind : Type :=
| SOK_Bloss
| SOK_Biquadratic
| SOK_Sine
| SOK_Cosine
| SOK_Unknown.

(* Start-placed clothoid spiral. Not an IsoClothoid. *)
Record SpiralClothoid : Type := mkSpiralClothoid {
  sc_loc : Point;
  sc_ref1 : Point;
  sc_ref2 : Point;
  sc_len : R;
  sc_k0 : R;
  sc_k1 : R;
  sc_m : option (R * R)
}.

Inductive SpiralInput : Type :=
| SpiralOfClothoid : SpiralClothoid -> SpiralInput
| SpiralOther : SpiralOtherKind -> SpiralInput.

Inductive JtsClass : Type :=
| JC_Example5
| JC_NonPositiveLength
| JC_TripleNotYet.

(* One taxonomy. Emit round-trip can match these constructors. *)
Inductive CertDecline : Type :=
| CD_SpiralOther : SpiralOtherKind -> CertDecline
| CD_SpiralClothoidNotYet : SpiralClothoid -> CertDecline
| CD_JtsNonPositiveLength : R -> R -> R -> CertDecline
| CD_JtsTripleNotYet : R -> R -> R -> CertDecline.

Definition cert_of_spiral (sp : SpiralInput) : CertDecline :=
  match sp with
  | SpiralOfClothoid sc => CD_SpiralClothoidNotYet sc
  | SpiralOther k => CD_SpiralOther k
  end.

(* Example5 numbers on a start-placed spiral. Still not the
   inflection-placed locked ISO egg. *)
Definition sample_spiral_clothoid : SpiralClothoid :=
  mkSpiralClothoid (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    example5_jts_L example5_jts_k0 example5_jts_k1 None.

(* Length before the example5 match, so a non-positive copy of
   the example5 curvatures cannot hit. *)
Definition classify_jts (k0 k1 len : R) : JtsClass :=
  match Rle_dec len 0 with
  | left _ => JC_NonPositiveLength
  | right _ =>
      if jts_is_example5 k0 k1 len then JC_Example5 else JC_TripleNotYet
  end.

(* Compound-member carrier for the next letter. Not consulted
   by classify_jts. Bare example5 still hits with no predecessor. *)
Record MemberState : Type := mkMemberState {
  mst_end : Point;
  mst_dir : Point;
  mst_curvature : R
}.

Lemma classify_example5 :
  classify_jts example5_jts_k0 example5_jts_k1 example5_jts_L = JC_Example5.
Proof.
  unfold classify_jts.
  destruct (Rle_dec example5_jts_L 0) as [Hle|Hgt].
  - unfold example5_jts_L in Hle. lra.
  - rewrite jts_is_example5_yes. reflexivity.
Qed.

Lemma classify_jts_nonpos :
  classify_jts 0 0 0 = JC_NonPositiveLength.
Proof.
  unfold classify_jts.
  destruct (Rle_dec 0 0) as [_|H].
  - reflexivity.
  - exfalso. apply H. apply Rle_refl.
Qed.

Lemma classify_length_first :
  classify_jts example5_jts_k0 example5_jts_k1 0 = JC_NonPositiveLength.
Proof.
  unfold classify_jts.
  destruct (Rle_dec 0 0) as [_|H].
  - reflexivity.
  - exfalso. apply H. apply Rle_refl.
Qed.

Lemma classify_jts_other :
  classify_jts 0 0 1 = JC_TripleNotYet.
Proof.
  unfold classify_jts.
  destruct (Rle_dec 1 0) as [Hle|Hgt].
  - lra.
  - rewrite jts_is_example5_other. reflexivity.
Qed.

Lemma cert_spiral_clothoid : forall sc,
  cert_of_spiral (SpiralOfClothoid sc) = CD_SpiralClothoidNotYet sc.
Proof. intros sc. reflexivity. Qed.

Lemma cert_spiral_other : forall k,
  cert_of_spiral (SpiralOther k) = CD_SpiralOther k.
Proof. intros k. reflexivity. Qed.

Lemma member_state_proj : forall p d k,
  mst_end (mkMemberState p d k) = p /\
  mst_dir (mkMemberState p d k) = d /\
  mst_curvature (mkMemberState p d k) = k.
Proof. intros p d k. repeat split; reflexivity. Qed.

Print Assumptions classify_example5.
Print Assumptions classify_jts_nonpos.
Print Assumptions classify_length_first.
Print Assumptions classify_jts_other.
Print Assumptions cert_spiral_clothoid.
Print Assumptions cert_spiral_other.
Print Assumptions member_state_proj.
