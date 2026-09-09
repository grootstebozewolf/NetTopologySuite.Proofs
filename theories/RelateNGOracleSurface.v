(* ============================================================================
   NetTopologySuite.Proofs.RelateNGOracleSurface
   ----------------------------------------------------------------------------
   Issue #575 / #522 claimId 522-f: oracle wire surface — an explicit
   UNSUPPORTED result token, structurally distinct from any 9-cell matrix,
   plus pins of the triangle regime fills as they stand today.

   A decline cannot travel over the oracle wire as a DE-9IM string:
   `im_unsupported` carries EI=BE=`Some 3`, so it fails `matrix_ok` and
   is not a legal F/0/1/2 nine-char.  This module names the wire cells
   (`WireCell` / `WireMatrix`), encodes a well-formed matrix or declines
   (`RelateWireResult`), and proves the triangle classifier's fills
   land on the right side of that cut. Leftover `Ⅰ`
   (`TPR_TouchPartialEdge`), leftover `Ⅲ`
   (`TPR_TouchOnesided`), and leftover `Ⅱ`
   (`TPR_TouchObtuse` / `TPR_MixedCone` / `TPR_SameCone`) stay
   on the token side.

   Green (Qed):
     - `encode_matrix m <> None` iff `matrix_ok m`
     - `RWR_Unsupported <> RWR_Matrix w` for every wire matrix
     - `triangle_pair_wire TPR_Unsupported = RWR_Unsupported`
     - classified regimes encode as the current designated fills
       (FFFFFFFFF / 2FFF1FFF2 / 2FFFFFFF2 / FFFF1FFF2)
     - `relate` of the leftover T-junction encodes as `RWR_Unsupported`

   Finding (Qex):
     - the #575 ticket witness "#530 declined pair returns UNSUPPORTED"
       is false.  That pair classifies disjoint (#571) and encodes as
       `RWR_Matrix wm_disjoint`.  The decline pin is the T-junction
       (`#577` / 522-j).

   Not claimed:
     - remint of `aa_matrix_disjoint` or `triangle_pair_fill TPR_Disjoint`
       (still FFFFFFFFF; OGC FF2FF1212 stays in RelateNGDisjointCells)
     - harness updates (GeosOracleBugHunt / CurveOracleBugHunt)
     - leftover certificates, classifier-order changes, ADR-0004

   Token spelling on the oracle wire is `UNSUPPORTED` (result position
   only, never a catalog matrix key).  Coq has no String/Ascii here;
   the token is the constructor `RWR_Unsupported`.

   Frozen anchors untouched.  Not an ADR-0004 remint.  `522-f` is the
   existing #575 ticket id.

   WITNESS topic: relate · claimId: 522-f · witness: 522-f-unsupported-token
   macro: relate
   lane: proofs
   issue: #575 / #522
   ADR-0004: not a remint. 522-f is the existing #575 ticket id.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Agent
   ========================================================================== *)

(* WITNESS {"claimId":"522-f","topic":"relate","lemma":"triangle_unsupported_token","title":"Triangle decline is the UNSUPPORTED wire token, not a matrix","file":"theories/RelateNGOracleSurface.v","witness":"522-f-unsupported-token","board":"#575"} *)

From Stdlib Require Import Reals Lia List.
From NTS.Proofs Require Import DE9IM RelateMatrixTriangle
  RelateNGCore RelateNGDisjoint.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Wire cells.  Legal DE-9IM characters only; `Some n` with n > 2 is not a    *)
(* cell and cannot be written as a 9-char.                                    *)
(* -------------------------------------------------------------------------- *)

Inductive WireCell : Type :=
| WC_F
| WC_0
| WC_1
| WC_2.

Record WireMatrix : Type := mkWM {
  wm_ii : WireCell; wm_ib : WireCell; wm_ie : WireCell;
  wm_bi : WireCell; wm_bb : WireCell; wm_be : WireCell;
  wm_ei : WireCell; wm_eb : WireCell; wm_ee : WireCell
}.

Definition encode_dim (d : DimValue) : option WireCell :=
  match d with
  | None => Some WC_F
  | Some 0 => Some WC_0
  | Some 1 => Some WC_1
  | Some 2 => Some WC_2
  | Some _ => None
  end.

Definition encode_nine
    (ii ib ie bi bb be ei eb ee : DimValue) : option WireMatrix :=
  match encode_dim ii with
  | None => None
  | Some wii =>
    match encode_dim ib with
    | None => None
    | Some wib =>
      match encode_dim ie with
      | None => None
      | Some wie =>
        match encode_dim bi with
        | None => None
        | Some wbi =>
          match encode_dim bb with
          | None => None
          | Some wbb =>
            match encode_dim be with
            | None => None
            | Some wbe =>
              match encode_dim ei with
              | None => None
              | Some wei =>
                match encode_dim eb with
                | None => None
                | Some web =>
                  match encode_dim ee with
                  | None => None
                  | Some wee =>
                      Some {| wm_ii := wii; wm_ib := wib; wm_ie := wie;
                              wm_bi := wbi; wm_bb := wbb; wm_be := wbe;
                              wm_ei := wei; wm_eb := web; wm_ee := wee |}
                  end
                end
              end
            end
          end
        end
      end
    end
  end.

Definition encode_matrix (m : IntersectionMatrix) : option WireMatrix :=
  encode_nine (im_ii m) (im_ib m) (im_ie m)
              (im_bi m) (im_bb m) (im_be m)
              (im_ei m) (im_eb m) (im_ee m).

Lemma encode_dim_some_ok : forall d w,
  encode_dim d = Some w -> dim_value_ok d.
Proof.
  intros d w H.
  destruct d as [n|]; [|exact I].
  destruct n as [|[|[|n]]]; simpl in H; try discriminate;
    unfold dim_value_ok; lia.
Qed.

Lemma encode_dim_ok_some : forall d,
  dim_value_ok d -> exists w, encode_dim d = Some w.
Proof.
  intros d H.
  destruct d as [n|].
  - destruct n as [|[|[|n]]].
    + exists WC_0; reflexivity.
    + exists WC_1; reflexivity.
    + exists WC_2; reflexivity.
    + unfold dim_value_ok in H; lia.
  - exists WC_F; reflexivity.
Qed.

Lemma encode_nine_ok :
  forall ii ib ie bi bb be ei eb ee,
    dim_value_ok ii /\ dim_value_ok ib /\ dim_value_ok ie /\
    dim_value_ok bi /\ dim_value_ok bb /\ dim_value_ok be /\
    dim_value_ok ei /\ dim_value_ok eb /\ dim_value_ok ee ->
    exists w, encode_nine ii ib ie bi bb be ei eb ee = Some w.
Proof.
  intros ii ib ie bi bb be ei eb ee
    (Hii & Hib & Hie & Hbi & Hbb & Hbe & Hei & Heb & Hee).
  destruct (encode_dim_ok_some ii Hii) as [wii Eii].
  destruct (encode_dim_ok_some ib Hib) as [wib Eib].
  destruct (encode_dim_ok_some ie Hie) as [wie Eie].
  destruct (encode_dim_ok_some bi Hbi) as [wbi Ebi].
  destruct (encode_dim_ok_some bb Hbb) as [wbb Ebb].
  destruct (encode_dim_ok_some be Hbe) as [wbe Ebe].
  destruct (encode_dim_ok_some ei Hei) as [wei Eei].
  destruct (encode_dim_ok_some eb Heb) as [web Eeb].
  destruct (encode_dim_ok_some ee Hee) as [wee Eee].
  unfold encode_nine.
  rewrite Eii, Eib, Eie, Ebi, Ebb, Ebe, Eei, Eeb, Eee.
  eexists; reflexivity.
Qed.

Lemma encode_nine_some_ok :
  forall ii ib ie bi bb be ei eb ee w,
    encode_nine ii ib ie bi bb be ei eb ee = Some w ->
    dim_value_ok ii /\ dim_value_ok ib /\ dim_value_ok ie /\
    dim_value_ok bi /\ dim_value_ok bb /\ dim_value_ok be /\
    dim_value_ok ei /\ dim_value_ok eb /\ dim_value_ok ee.
Proof.
  intros ii ib ie bi bb be ei eb ee w H.
  unfold encode_nine in H.
  destruct (encode_dim ii) as [wii|] eqn:Eii; [|discriminate].
  destruct (encode_dim ib) as [wib|] eqn:Eib; [|discriminate].
  destruct (encode_dim ie) as [wie|] eqn:Eie; [|discriminate].
  destruct (encode_dim bi) as [wbi|] eqn:Ebi; [|discriminate].
  destruct (encode_dim bb) as [wbb|] eqn:Ebb; [|discriminate].
  destruct (encode_dim be) as [wbe|] eqn:Ebe; [|discriminate].
  destruct (encode_dim ei) as [wei|] eqn:Eei; [|discriminate].
  destruct (encode_dim eb) as [web|] eqn:Eeb; [|discriminate].
  destruct (encode_dim ee) as [wee|] eqn:Eee; [|discriminate].
  repeat split; eapply encode_dim_some_ok; eassumption.
Qed.

Theorem encode_matrix_iff_ok : forall m,
  (exists w, encode_matrix m = Some w) <-> matrix_ok m.
Proof.
  intros m; split.
  - intros [w Hw]. unfold encode_matrix, matrix_ok in *.
    exact (encode_nine_some_ok _ _ _ _ _ _ _ _ _ _ Hw).
  - intros Hok. unfold encode_matrix, matrix_ok in *.
    exact (encode_nine_ok _ _ _ _ _ _ _ _ _ Hok).
Qed.

Lemma encode_matrix_unsupported :
  encode_matrix im_unsupported = None.
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Result token.  Legal in result position only; never a matrix key.          *)
(* Oracle spelling: UNSUPPORTED.                                              *)
(* -------------------------------------------------------------------------- *)

Inductive RelateWireResult : Type :=
| RWR_Matrix (w : WireMatrix)
| RWR_Unsupported.

Definition encode_wire (m : IntersectionMatrix) : RelateWireResult :=
  match encode_matrix m with
  | Some w => RWR_Matrix w
  | None => RWR_Unsupported
  end.

Theorem wire_unsupported_neq_matrix : forall w,
  RWR_Unsupported <> RWR_Matrix w.
Proof. discriminate. Qed.

Lemma encode_wire_ok : forall m,
  matrix_ok m -> exists w, encode_wire m = RWR_Matrix w.
Proof.
  intros m Hok.
  apply encode_matrix_iff_ok in Hok.
  destruct Hok as [w Hw].
  exists w. unfold encode_wire. rewrite Hw. reflexivity.
Qed.

Lemma encode_wire_not_ok : forall m,
  ~ matrix_ok m -> encode_wire m = RWR_Unsupported.
Proof.
  intros m Hnok.
  unfold encode_wire.
  destruct (encode_matrix m) as [w|] eqn:Em; [|reflexivity].
  exfalso. apply Hnok. apply encode_matrix_iff_ok. exists w. exact Em.
Qed.

Lemma encode_wire_unsupported :
  encode_wire im_unsupported = RWR_Unsupported.
Proof.
  apply encode_wire_not_ok. exact im_unsupported_not_ok.
Qed.

(* -------------------------------------------------------------------------- *)
(* Designated 9-cell pins (current fills; not reminted).                      *)
(* -------------------------------------------------------------------------- *)

Definition wm_disjoint : WireMatrix :=
  {| wm_ii := WC_F; wm_ib := WC_F; wm_ie := WC_F;
     wm_bi := WC_F; wm_bb := WC_F; wm_be := WC_F;
     wm_ei := WC_F; wm_eb := WC_F; wm_ee := WC_F |}.

Definition wm_overlap : WireMatrix :=
  {| wm_ii := WC_2; wm_ib := WC_F; wm_ie := WC_F;
     wm_bi := WC_F; wm_bb := WC_1; wm_be := WC_F;
     wm_ei := WC_F; wm_eb := WC_F; wm_ee := WC_2 |}.

Definition wm_contains : WireMatrix :=
  {| wm_ii := WC_2; wm_ib := WC_F; wm_ie := WC_F;
     wm_bi := WC_F; wm_bb := WC_F; wm_be := WC_F;
     wm_ei := WC_F; wm_eb := WC_F; wm_ee := WC_2 |}.

Definition wm_touch : WireMatrix :=
  {| wm_ii := WC_F; wm_ib := WC_F; wm_ie := WC_F;
     wm_bi := WC_F; wm_bb := WC_1; wm_be := WC_F;
     wm_ei := WC_F; wm_eb := WC_F; wm_ee := WC_2 |}.

Definition triangle_pair_wire (r : TrianglePairRegime) : RelateWireResult :=
  encode_wire (triangle_pair_fill r).

(* WITNESS topic: relate · claimId: 522-f · witness: 522-f-unsupported-token *)
Theorem triangle_unsupported_token :
  triangle_pair_wire TPR_Unsupported = RWR_Unsupported.
Proof.
  unfold triangle_pair_wire.
  rewrite triangle_pair_fill_unsupported_eq.
  exact encode_wire_unsupported.
Qed.

Theorem triangle_disjoint_wire :
  triangle_pair_wire TPR_Disjoint = RWR_Matrix wm_disjoint.
Proof. reflexivity. Qed.

Theorem triangle_overlap_wire :
  triangle_pair_wire TPR_Overlap = RWR_Matrix wm_overlap.
Proof. reflexivity. Qed.

Theorem triangle_contains_wire :
  triangle_pair_wire TPR_Contains = RWR_Matrix wm_contains.
Proof. reflexivity. Qed.

Theorem triangle_touch_edge_wire :
  triangle_pair_wire TPR_TouchEdge = RWR_Matrix wm_touch.
Proof. reflexivity. Qed.

Theorem triangle_touch_vertex_wire :
  triangle_pair_wire TPR_TouchVertex = RWR_Matrix wm_touch.
Proof. reflexivity. Qed.

Theorem triangle_touch_partial_wire :
  triangle_pair_wire TPR_TouchPartialEdge = RWR_Unsupported.
Proof.
  unfold triangle_pair_wire.
  rewrite triangle_pair_fill_touch_partial_eq.
  exact encode_wire_unsupported.
Qed.

Theorem triangle_touch_onesided_wire :
  triangle_pair_wire TPR_TouchOnesided = RWR_Unsupported.
Proof.
  unfold triangle_pair_wire.
  rewrite triangle_pair_fill_touch_onesided_eq.
  exact encode_wire_unsupported.
Qed.

Theorem triangle_touch_obtuse_wire :
  triangle_pair_wire TPR_TouchObtuse = RWR_Unsupported.
Proof.
  unfold triangle_pair_wire.
  rewrite triangle_pair_fill_touch_obtuse_eq.
  exact encode_wire_unsupported.
Qed.

Theorem triangle_touch_mixed_wire :
  triangle_pair_wire TPR_MixedCone = RWR_Unsupported.
Proof.
  unfold triangle_pair_wire.
  rewrite triangle_pair_fill_touch_mixed_eq.
  exact encode_wire_unsupported.
Qed.

Theorem triangle_touch_samecone_wire :
  triangle_pair_wire TPR_SameCone = RWR_Unsupported.
Proof.
  unfold triangle_pair_wire.
  rewrite triangle_pair_fill_touch_samecone_eq.
  exact encode_wire_unsupported.
Qed.

(* TPR_TouchPartialEdge / TPR_TouchOnesided / TPR_TouchObtuse /
   TPR_MixedCone / TPR_SameCone are classified but fill is still
   the token. Keep them excluded so a matrix decode cannot swallow
   leftover Ⅰ / leftover Ⅲ / leftover Ⅱ / leftover Ⅴ /
   leftover Ⅵ. *)
Theorem classified_triangle_is_matrix : forall r,
  r <> TPR_Unsupported ->
  r <> TPR_TouchPartialEdge ->
  r <> TPR_TouchOnesided ->
  r <> TPR_TouchObtuse ->
  r <> TPR_MixedCone ->
  r <> TPR_SameCone ->
  exists w, triangle_pair_wire r = RWR_Matrix w.
Proof.
  intros r H Hu Ho Hob Hm Hs.
  destruct r.
  - exists wm_disjoint; exact triangle_disjoint_wire.
  - exists wm_overlap; exact triangle_overlap_wire.
  - exists wm_contains; exact triangle_contains_wire.
  - exists wm_touch; exact triangle_touch_edge_wire.
  - exists wm_touch; exact triangle_touch_vertex_wire.
  - contradiction Hu; reflexivity.
  - contradiction Ho; reflexivity.
  - contradiction Hob; reflexivity.
  - contradiction Hm; reflexivity.
  - contradiction Hs; reflexivity.
  - contradiction H; reflexivity.
Qed.

Theorem triangle_unsupported_not_a_matrix : forall w,
  triangle_pair_wire TPR_Unsupported <> RWR_Matrix w.
Proof.
  intros w. rewrite triangle_unsupported_token. apply wire_unsupported_neq_matrix.
Qed.

(* -------------------------------------------------------------------------- *)
(* `relate` on the wire.  Empty-pair and leftover-decline are tokens; the     *)
(* #530 / #571 sentinel is a matrix (ticket witness is stale).                *)
(* -------------------------------------------------------------------------- *)

Theorem relate_unsupported_pair_wire :
  encode_wire (relate [] []) = RWR_Unsupported.
Proof.
  rewrite relate_unsupported_pair. exact encode_wire_unsupported.
Qed.

(* WITNESS {"claimId":"522-f","topic":"relate","lemma":"relate_tjunction_wire_unsupported","title":"relate of the leftover T-junction is UNSUPPORTED on the wire","file":"theories/RelateNGOracleSurface.v","witness":"522-f-unsupported-token","board":"#575"} *)
Theorem relate_tjunction_wire_unsupported :
  encode_wire (relate (triangle_geometry 0 0 2 0 0 1)
                      (triangle_geometry 1 0 3 0 2 1))
  = RWR_Unsupported.
Proof.
  rewrite relate_on_triangles_dispatches.
  unfold tris_relate.
  rewrite tjunction_pair_unsupported.
  exact encode_wire_unsupported.
Qed.

Theorem relate_tjunction_not_a_matrix : forall w,
  encode_wire (relate (triangle_geometry 0 0 2 0 0 1)
                      (triangle_geometry 1 0 3 0 2 1))
  <> RWR_Matrix w.
Proof.
  intros w. rewrite relate_tjunction_wire_unsupported.
  apply wire_unsupported_neq_matrix.
Qed.

Theorem relate_sentinel_wire_disjoint :
  encode_wire (relate (triangle_geometry 0 0 1 0 0 1)
                      (triangle_geometry 2 0 3 0 2 1))
  = RWR_Matrix wm_disjoint.
Proof.
  rewrite relate_triangle_dispatch_ex.
  unfold tris_relate.
  exact triangle_disjoint_wire.
Qed.

(* Qex: #575 ticket witness "#530 declined pair returns UNSUPPORTED" is
   false.  That pair classifies disjoint (#571) and is a 9-cell on the
   wire.  The decline pin is the T-junction above. *)
Theorem relate_sentinel_not_unsupported :
  encode_wire (relate (triangle_geometry 0 0 1 0 0 1)
                      (triangle_geometry 2 0 3 0 2 1))
  <> RWR_Unsupported.
Proof.
  rewrite relate_sentinel_wire_disjoint. discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions triangle_unsupported_token.
Print Assumptions encode_matrix_iff_ok.
Print Assumptions classified_triangle_is_matrix.
Print Assumptions relate_tjunction_wire_unsupported.
Print Assumptions relate_sentinel_not_unsupported.
