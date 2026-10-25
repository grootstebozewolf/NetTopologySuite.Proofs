(* ============================================================================
   NetTopologySuite.Proofs.ClothoidSheetStmt
   ----------------------------------------------------------------------------
   STATEMENTS ONLY (no Lemma / Theorem / Proof here).  The statement half of
   claimId `cloth-sheet-transport` (statement C of the shear plan); the proof
   half is ClothoidSheet.v, which must prove exactly `claim`, `supporting`
   and `witness` below.  The code of this file (comments excluded) is pinned
   by sha256 in docs/claim-statements.json and checked by
   scripts/check_claim_statements.py.

   ADR-0007 fixes one sheet S per constructor.  A shear is a change of sheet
   S = (O; e1, e2) -> S' = (f O; L e1, L e2).  This file states that the
   clothoid x clothoid oracle transports along it: pull a pair placed on a
   common invertible frame (o, M) back to the host sheet, run any host
   result that meets I_ok there, push the result forward by the frame.
   Hit keeps its parameters and moves its point by f, Empty stays Empty,
   Decline stays Decline (res_push), and the pushed result meets the placed
   spec on S' (I_sheet_ok).  A pair on two different frames, or a frame
   with det M = 0, is out of scope and declines: pulling one input back
   leaves the other sheared, which needs a clothoid x sheared-clothoid
   oracle that does not exist yet.

   Objects.  Placed clothoids PCloth / pc_act / Aff2 of ClothoidAffineStmt
   (claim cloth-affine-closure); the oracle results IResult and the host
   spec I_ok of SheetHenCookCore; Orientation.cross (orientation of three
   points); RingArea979.signed_area2 (cyclic shoelace of a vertex ring).

   Point location by the canonical ray parity (JCTHalfOpenParity) is NOT
   stated: its east ray and half-open y test are tied to the axes of S, so
   on S' it needs direction-independence of parity (JCT level).  Only the
   on-boundary part of point location is stated here.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending
   (review.status in docs/claim-statements.json).
   ========================================================================== *)

From Stdlib Require Import Reals List.
From NTS.Proofs Require Import Distance Orientation RingArea979 SignedCurvature
  SheetHenClothoidCore SheetHenCookCore ClothoidTraversal ClothoidPlacement
  ClothoidAffineStmt ClothoidShearLawStmt ClothoidCookMkClothoid.
Import ListNotations.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The host sheet, the placed spec and the pushed result.                 *)
(* -------------------------------------------------------------------------- *)

Definition host_pc (c : ClothoidEgg) : PCloth := mkPCloth (mkPoint 0 0) lin_id c.

Definition pc_frame (pc : PCloth) : Aff2 := mkAff2 (pc_o pc) (pc_M pc).

Definition on_pc (pc : PCloth) (t : R) (p : Point) : Prop :=
  0 <= t <= 1 /\ p = pc_eval pc t.

(* The clothoid arm of I_ok, read on placed clothoids. *)
Definition I_placed_ok (pc1 pc2 : PCloth) (o : IResult) : Prop :=
  match o with
  | IHit p ti tj => on_pc pc1 ti p /\ on_pc pc2 tj p
  | IEmpty => ~ exists X t1 t2, on_pc pc1 t1 X /\ on_pc pc2 t2 X
  | IDecline => False
  end.

Definition res_push (f : Aff2) (o : IResult) : IResult :=
  match o with
  | IHit p ti tj => IHit (aff_ap f p) ti tj
  | IEmpty => IEmpty
  | IDecline => IDecline
  end.

(* -------------------------------------------------------------------------- *)
(* §2  The cook on a sheared sheet: one common invertible frame, or Decline.  *)
(* -------------------------------------------------------------------------- *)

Definition pc_scope (pc1 pc2 : PCloth) : Prop :=
  pc_o pc1 = pc_o pc2 /\ pc_M pc1 = pc_M pc2 /\ lin_det (pc_M pc1) <> 0.

Definition req_b (a b : R) : bool := if Req_EM_T a b then true else false.

Definition pc_scope_b (pc1 pc2 : PCloth) : bool :=
  req_b (px (pc_o pc1)) (px (pc_o pc2)) && req_b (py (pc_o pc1)) (py (pc_o pc2))
  && req_b (l11 (pc_M pc1)) (l11 (pc_M pc2)) && req_b (l12 (pc_M pc1)) (l12 (pc_M pc2))
  && req_b (l21 (pc_M pc1)) (l21 (pc_M pc2)) && req_b (l22 (pc_M pc1)) (l22 (pc_M pc2))
  && negb (req_b (lin_det (pc_M pc1)) 0).

(* Pull back to the host sheet, cook there, push forward by the frame. *)
Definition sheet_cook (cook : Egg -> Egg -> IResult) (pc1 pc2 : PCloth) : IResult :=
  if pc_scope_b pc1 pc2
  then res_push (pc_frame pc1) (cook (MkClothoid (pc_c pc1)) (MkClothoid (pc_c pc2)))
  else IDecline.

(* The spec on S': in scope, the placed spec; out of scope, Decline. *)
Definition I_sheet_ok (pc1 pc2 : PCloth) (o : IResult) : Prop :=
  match o with
  | IDecline => ~ pc_scope pc1 pc2
  | _ => pc_scope pc1 pc2 /\ I_placed_ok pc1 pc2 o
  end.

Definition sheet_act (f : Aff2) (S : Sheet) : Sheet :=
  mkSheet (aff_ap f (sheet_origin S)) (lin_ap (af_L f) (sheet_e1 S))
          (lin_ap (af_L f) (sheet_e2 S)) (sheet_has_lattice S).

(* -------------------------------------------------------------------------- *)
(* §3  The statements.                                                        *)
(* -------------------------------------------------------------------------- *)

(* Hit keeps its parameters and moves its point; Empty and Decline stay. *)
Definition push_shape_stmt : Prop :=
  forall f o,
    (res_push f o = IDecline <-> o = IDecline) /\
    (res_push f o = IEmpty <-> o = IEmpty) /\
    (forall p ti tj, o = IHit p ti tj -> res_push f o = IHit (aff_ap f p) ti tj).

(* On the host sheet the placed spec is the clothoid arm of I_ok. *)
Definition host_spec_stmt : Prop :=
  forall c1 c2 o,
    I_ok (MkClothoid c1) (MkClothoid c2) o <-> I_placed_ok (host_pc c1) (host_pc c2) o.

(* Equivariance: an invertible affine map moves a correct result to a
   correct result, both ways. *)
Definition transport_stmt : Prop :=
  forall f pc1 pc2 o, lin_det (af_L f) <> 0 ->
    (I_placed_ok pc1 pc2 o
     <-> I_placed_ok (pc_act f pc1) (pc_act f pc2) (res_push f o)).

(* The sheet cook meets the sheet spec, pair by pair: in scope whenever the
   host result for the pulled-back pair meets I_ok, out of scope always. *)
Definition sheet_cook_stmt : Prop :=
  forall cook pc1 pc2,
    (pc_scope pc1 pc2 ->
       I_ok (MkClothoid (pc_c pc1)) (MkClothoid (pc_c pc2))
            (cook (MkClothoid (pc_c pc1)) (MkClothoid (pc_c pc2)))) ->
    I_sheet_ok pc1 pc2 (sheet_cook cook pc1 pc2).

(* main: the clothoid x clothoid oracle is equivariant under invertible
   affine maps, and pull-back / host cook / push-forward is a correct oracle
   on a sheared sheet. *)
Definition claim : Prop :=
  push_shape_stmt /\ host_spec_stmt /\ transport_stmt /\ sheet_cook_stmt.

(* supporting: the scope test decides pc_scope; sheets compose and their
   frame orientation scales by det L; noding (a list of pairwise results)
   transports; tangency, split vertices and on-boundary location transport;
   orientation of three points and of a vertex ring scale by det L, so they
   flip exactly when det L < 0. *)
Definition supporting : Prop :=
  (forall pc1 pc2, pc_scope_b pc1 pc2 = true <-> pc_scope pc1 pc2)
  /\ (forall g f S, sheet_act (aff_comp g f) S = sheet_act g (sheet_act f S))
  /\ (forall f S,
        curv_cross (sheet_e1 (sheet_act f S)) (sheet_e2 (sheet_act f S))
          = lin_det (af_L f) * curv_cross (sheet_e1 S) (sheet_e2 S))
  /\ (forall f (G : list (PCloth * PCloth * IResult)), lin_det (af_L f) <> 0 ->
        Forall (fun r => I_placed_ok (fst (fst r)) (snd (fst r)) (snd r)) G ->
        Forall (fun r => I_placed_ok (fst (fst r)) (snd (fst r)) (snd r))
          (map (fun r => (pc_act f (fst (fst r)), pc_act f (snd (fst r)),
                          res_push f (snd r))) G))
  /\ (forall f pc1 pc2 s1 s2, lin_det (af_L f) <> 0 ->
        (curv_cross (pc_tangent pc1 s1) (pc_tangent pc2 s2) = 0
         <-> curv_cross (pc_tangent (pc_act f pc1) s1)
                        (pc_tangent (pc_act f pc2) s2) = 0))
  /\ (forall f pc t,
        pc_eval (fst (pc_split (pc_act f pc) t)) 1 = aff_ap f (pc_eval pc t) /\
        pc_eval (snd (pc_split (pc_act f pc) t)) 0 = aff_ap f (pc_eval pc t))
  /\ (forall f pc p, lin_det (af_L f) <> 0 ->
        ((exists t, on_pc pc t p) <-> (exists t, on_pc (pc_act f pc) t (aff_ap f p))))
  /\ (forall f P Q X,
        Orientation.cross (aff_ap f P) (aff_ap f Q) (aff_ap f X)
          = lin_det (af_L f) * Orientation.cross P Q X)
  /\ (forall f l,
        RingArea979.signed_area2 (map (aff_ap f) l)
          = lin_det (af_L f) * RingArea979.signed_area2 l).

(* witness: the locked clothoid Hit of ClothoidCookMkClothoid, both eggs
   placed on the GEOS #1566 shear frame, is a correct sheared Hit at the
   sheared point with the host parameters; and the limit: the host egg
   against the sheared GEOS egg is out of scope, the sheet cook declines,
   and the second input, pulled back by the first's (identity) frame, stays
   sheared with no window of curvature linear in arc length. *)
Definition witness : Prop :=
  I_sheet_ok (mkPCloth (mkPoint 0 0) geos_shear locked_cloth_A)
             (mkPCloth (mkPoint 0 0) geos_shear locked_cloth_B)
             (IHit (lin_ap geos_shear locked_cloth_hit_pt) locked_cloth_ti locked_cloth_tj)
  /\ (forall cook,
        sheet_cook cook (host_pc locked_cloth_A)
                        (mkPCloth (mkPoint 0 0) geos_shear geos_shear_egg) = IDecline)
  /\ (forall s1 s2, s1 < s2 ->
        ~ linear_law_on geos_shear_egg
            (lin_mul (lin_inv (pc_M (host_pc locked_cloth_A))) geos_shear) s1 s2).
