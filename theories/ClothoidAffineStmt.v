(* ============================================================================
   NetTopologySuite.Proofs.ClothoidAffineStmt
   ----------------------------------------------------------------------------
   STATEMENTS ONLY (no Lemma / Theorem / Proof here).  The statement half of
   the placed-clothoid affine-closure claim (claimId `cloth-affine-closure`);
   the proof half is ClothoidAffine.v, which must prove exactly `claim`,
   `supporting` and `witness` below.  The code of this file (comments
   excluded) is pinned by sha256 in docs/claim-statements.json and checked by
   scripts/check_claim_statements.py.

   Objects.  A placed clothoid is a host clothoid `ClothoidEgg` (the
   Fresnel eval of SheetHenClothoidCore, rigid or reflected host frame)
   read through an external placement o + M p (ClothoidPlacement.placed,
   M any 2x2 `Lin2`).  This is the ISO / GEOS frame o + [u v] c(t) with the
   host frame folded into c.  An affine map is f(p) = b + L p, L a `Lin2`;
   it acts on placements by (o, M) |-> (f(o), L M).  Split, reverse and the
   chord demote act on the host egg only (split / rev) or read the ends.

   Shear is the case det L <> 0 with L not a similarity: this file states
   that the representation is closed under it.  The geometry of the image
   (curvature not linear in placed arc length) is the sibling claim
   `cloth-linear-law-iff-similarity` (ClothoidShearLawStmt.v).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending
   (review.status in docs/claim-statements.json).
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance SignedCurvature SheetHenClothoidCore
  ClothoidLinearize ClothoidTraversal ClothoidPlacement.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Linear and affine maps of the plane.                                   *)
(* -------------------------------------------------------------------------- *)

Definition lin_id : Lin2 := mkLin2 1 0 0 1.

Definition lin_mul (L M : Lin2) : Lin2 :=
  mkLin2 (l11 L * l11 M + l12 L * l21 M) (l11 L * l12 M + l12 L * l22 M)
         (l21 L * l11 M + l22 L * l21 M) (l21 L * l12 M + l22 L * l22 M).

Definition lin_inv (L : Lin2) : Lin2 :=
  mkLin2 (l22 L / lin_det L) (- l12 L / lin_det L)
         (- l21 L / lin_det L) (l11 L / lin_det L).

Record Aff2 : Type := mkAff2 { af_b : Point; af_L : Lin2 }.

Definition aff_ap (f : Aff2) (p : Point) : Point := placed (af_b f) (af_L f) p.

Definition aff_id : Aff2 := mkAff2 (mkPoint 0 0) lin_id.

(* g after f *)
Definition aff_comp (g f : Aff2) : Aff2 :=
  mkAff2 (aff_ap g (af_b f)) (lin_mul (af_L g) (af_L f)).

Definition aff_inv (f : Aff2) : Aff2 :=
  mkAff2 (lin_ap (lin_inv (af_L f))
                 (mkPoint (- px (af_b f)) (- py (af_b f))))
         (lin_inv (af_L f)).

(* -------------------------------------------------------------------------- *)
(* §2  Placed clothoids and the action.                                       *)
(* -------------------------------------------------------------------------- *)

Record PCloth : Type := mkPCloth { pc_o : Point; pc_M : Lin2; pc_c : ClothoidEgg }.

Definition pc_eval (pc : PCloth) (t : R) : Point :=
  placed (pc_o pc) (pc_M pc) (cloth_eval (pc_c pc) t).

(* Arc-length reading: point and tangent at host arc length s. *)
Definition pc_arc (pc : PCloth) (s : R) : Point :=
  placed (pc_o pc) (pc_M pc) (cloth_arc (pc_c pc) s).

Definition pc_tangent (pc : PCloth) (s : R) : Point :=
  lin_ap (pc_M pc) (cloth_arc_v (pc_c pc) s).

Definition pc_act (f : Aff2) (pc : PCloth) : PCloth :=
  mkPCloth (aff_ap f (pc_o pc)) (lin_mul (af_L f) (pc_M pc)) (pc_c pc).

Definition pc_split (pc : PCloth) (t : R) : PCloth * PCloth :=
  (mkPCloth (pc_o pc) (pc_M pc) (fst (cloth_split (pc_c pc) t)),
   mkPCloth (pc_o pc) (pc_M pc) (snd (cloth_split (pc_c pc) t))).

Definition pc_rev (pc : PCloth) : PCloth :=
  mkPCloth (pc_o pc) (pc_M pc) (cloth_rev (pc_c pc)).

(* Chord demote: the segment between the two ends. *)
Definition pc_chord (pc : PCloth) : Point * Point :=
  (pc_eval pc 0, pc_eval pc 1).

(* -------------------------------------------------------------------------- *)
(* §3  The statements.                                                        *)
(* -------------------------------------------------------------------------- *)

Definition act_eval_stmt : Prop :=
  forall f pc t, pc_eval (pc_act f pc) t = aff_ap f (pc_eval pc t).

Definition act_id_stmt : Prop :=
  forall pc, pc_act aff_id pc = pc.

Definition act_comp_stmt : Prop :=
  forall g f pc, pc_act g (pc_act f pc) = pc_act (aff_comp g f) pc.

Definition act_det_stmt : Prop :=
  forall f pc,
    lin_det (pc_M (pc_act f pc)) = lin_det (af_L f) * lin_det (pc_M pc).

Definition act_split_stmt : Prop :=
  forall f pc t,
    pc_split (pc_act f pc) t
      = (pc_act f (fst (pc_split pc t)), pc_act f (snd (pc_split pc t))).

Definition act_rev_stmt : Prop :=
  forall f pc, pc_rev (pc_act f pc) = pc_act f (pc_rev pc).

Definition act_chord_stmt : Prop :=
  forall f pc,
    pc_chord (pc_act f pc)
      = (aff_ap f (fst (pc_chord pc)), aff_ap f (snd (pc_chord pc))).

(* main: placed clothoids are closed under the affine group, the action is a
   left action (identity, composition), it multiplies det M by det L, and it
   commutes with split, reverse and the chord demote. *)
Definition claim : Prop :=
  act_eval_stmt /\ act_id_stmt /\ act_comp_stmt /\ act_det_stmt
  /\ act_split_stmt /\ act_rev_stmt /\ act_chord_stmt.

(* supporting: every affine map with det L <> 0 is invertible in the group
   (so the action is by a group, and invertible maps keep det M <> 0); the
   image's arc-length point and tangent are f of the point and L of the
   tangent, the tangent is the derivative of the image, and
   cross products of tangents scale by det L, so parallel tangents (touching)
   stay parallel exactly when det L <> 0. *)
Definition supporting : Prop :=
  (forall f, lin_det (af_L f) <> 0 ->
     aff_comp (aff_inv f) f = aff_id /\ aff_comp f (aff_inv f) = aff_id)
  /\ (forall f pc s,
        pc_arc (pc_act f pc) s = aff_ap f (pc_arc pc s) /\
        pc_tangent (pc_act f pc) s = lin_ap (af_L f) (pc_tangent pc s))
  /\ (forall pc s,
        derivable_pt_lim (fun u => px (pc_arc pc u)) s (px (pc_tangent pc s)) /\
        derivable_pt_lim (fun u => py (pc_arc pc u)) s (py (pc_tangent pc s)))
  /\ (forall f pc s pc' s',
        curv_cross (pc_tangent (pc_act f pc) s) (pc_tangent (pc_act f pc') s')
          = lin_det (af_L f) * curv_cross (pc_tangent pc s) (pc_tangent pc' s')).

(* witness: the GEOS #1566 shear (u, v) = ((2, 0), (1/2, 1)) is reached from
   the identity placement of the unit-frame egg geos_shear_egg by one linear
   map that is not a similarity (columns of unequal length), det 2 <> 0. *)
Definition witness : Prop :=
  exists f, lin_det (af_L f) <> 0 /\
    l11 (af_L f) * l11 (af_L f) + l21 (af_L f) * l21 (af_L f)
      <> l12 (af_L f) * l12 (af_L f) + l22 (af_L f) * l22 (af_L f) /\
    pc_act f (mkPCloth (mkPoint 0 0) lin_id geos_shear_egg)
      = mkPCloth (mkPoint 0 0) geos_shear geos_shear_egg.
