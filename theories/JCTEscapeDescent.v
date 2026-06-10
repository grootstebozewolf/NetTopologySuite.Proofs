(* ============================================================================
   NetTopologySuite.Proofs.JCTEscapeDescent
   ----------------------------------------------------------------------------
   H1 PROPER, part 6: the ESCAPE half decomposed -- the base case is Qed and
   the residual shrinks from "construct a path to infinity" to ONE DESCENT
   STEP (one detour, one fewer crossing).

   The half-open crossings are counted by a nat-valued function `ho_count`
   (the per-edge test is decidable).  Two Qed pieces close everything except
   the descent:

     - BASE CASE (`escape_east_of_zero_count`): if NO edge crosses at p,
       the open eastward ray is literally SKELETON-FREE -- a strict straddle
       east of p would be a counted crossing; an edge point at p's height is
       otherwise a vertex or on a horizontal level edge, and the
       `ray_avoids_vertices` guard banishes both east of p (a horizontal
       level edge with a west-east endpoint split would contain p).  The
       straight eastward ray escapes every radius.

     - INDUCTION (`escape_of_descent`): strong induction on `ho_count`,
       riding the Qed component invariance
       (`in_bounded_component_cont_invariant`): a descent step hands the
       boundedness to a smaller-count point, and count zero escapes.

   THE FINAL RESIDUAL (`escape_descent`): from an even-parity guarded
   complement point with at least one crossing, reach -- through the
   complement -- a guarded point with strictly fewer crossings.  One detour
   around the first blocking edge; simplicity of the ring lives here and
   only here.  `parity_seam_offring_of_descent` then yields the FULL
   corrected H1 seam from the descent step alone.

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Arith Lia Wf_nat.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam.
From NTS.Proofs Require Import PointInRingCorrect JCT JCT_OnEdgeCounterexample.
From NTS.Proofs Require Import ConvexOffringSeam JCTParityTransport.
From NTS.Proofs Require Import JCTHalfOpenParity JCTGenericStability JCTLevelJump.
From NTS.Proofs Require Import JCTTrappedHalf JCTSeamAssembly.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §1  The crossing count and its parity bridge.
   --------------------------------------------------------------------------- *)

Fixpoint ho_count (p : Point) (es : list Edge) : nat :=
  match es with
  | [] => 0%nat
  | e :: es' =>
      ((if edge_crosses_ray_ho_dec p e then 1 else 0) + ho_count p es')%nat
  end.

Lemma ho_count_parity : forall (p : Point) (es : list Edge),
  (Nat.Even (ho_count p es) <-> ho_parity_even p es)
  /\ (Nat.Odd (ho_count p es) <-> ho_parity_odd p es).
Proof.
  intros p; induction es as [| e es' IH]; cbn [ho_count].
  - split.
    + split; intros _; [ constructor | exists 0%nat; lia ].
    + split; intro H; [ destruct H; lia | inversion H ].
  - destruct IH as [IHe IHo].
    destruct (edge_crosses_ray_ho_dec p e) as [Hc | Hn].
    + split.
      * cbn [Nat.add]. rewrite Nat.Even_succ. rewrite IHo.
        rewrite (ho_even_cons_cross _ _ _ Hc). tauto.
      * cbn [Nat.add]. rewrite Nat.Odd_succ. rewrite IHe.
        rewrite (ho_odd_cons_cross _ _ _ Hc). tauto.
    + cbn [Nat.add]. split.
      * rewrite IHe. rewrite (ho_even_cons_skip _ _ _ Hn). tauto.
      * rewrite IHo. rewrite (ho_odd_cons_skip _ _ _ Hn). tauto.
Qed.

Lemma ho_count_zero_no_cross : forall (p : Point) (es : list Edge),
  ho_count p es = 0%nat ->
  forall e, In e es -> ~ edge_crosses_ray_ho p e.
Proof.
  intros p; induction es as [| e0 es' IH]; intros Hz e Hin; [ contradiction | ].
  cbn [ho_count] in Hz.
  destruct (edge_crosses_ray_ho_dec p e0) as [Hc | Hn]; [ lia | ].
  destruct Hin as [He | Hin].
  - subst e0. exact Hn.
  - exact (IH ltac:(lia) e Hin).
Qed.

(* ---------------------------------------------------------------------------
   §2  Base case: zero crossings means the eastward ray is skeleton-free.
   --------------------------------------------------------------------------- *)

Lemma ho_no_cross_east_free : forall (a b q : Point),
  ~ edge_crosses_ray_ho q (a, b) ->
  ~ (py a = py q /\ px q <= px a) ->
  ~ (py b = py q /\ px q <= px b) ->
  (~ exists t : R, 0 <= t <= 1 /\
       px q = (1 - t) * px a + t * px b /\
       py q = (1 - t) * py a + t * py b) ->
  forall x', px q <= x' ->
    ~ (exists t : R, 0 <= t <= 1 /\
         x' = (1 - t) * px a + t * px b /\
         py q = (1 - t) * py a + t * py b).
Proof.
  intros a b q Hnc Hga Hgb Hoff x' Hx' [t [[Ht0 Ht1] [Hx Hy]]].
  destruct (Req_dec (py a) (py b)) as [Hflat | Hne].
  - (* horizontal edge: it lies at q's height, so both endpoints are at the
       level; the guards force both strictly west, but x' is a convex
       combination of their x's *)
    assert (Hh : py a = py q) by nra.
    assert (Hhb : py b = py q) by lra.
    assert (Hwa : px a < px q) by (destruct (Rle_or_lt (px q) (px a));
      [ exfalso; apply Hga; split; assumption | assumption ]).
    assert (Hwb : px b < px q) by (destruct (Rle_or_lt (px q) (px b));
      [ exfalso; apply Hgb; split; assumption | assumption ]).
    destruct (Rle_or_lt t 0) as [Hcase | Hcase]; nra.
  - destruct (Rtotal_order t 0) as [Hlt | [Hz | Hgt]]; [ lra | | ].
    + (* t = 0 : the point is vertex a, east on the ray *)
      subst t. apply Hga. split.
      * nra.
      * nra.
    + destruct (Rtotal_order t 1) as [Hlt1 | [Ho | Hgt1]]; [ | | lra ].
      * (* 0 < t < 1 : strict interior point of the edge at q's height --
           a counted crossing unless it sits at or west of q; combined with
           px q <= x' it must BE q, contradicting off-edge *)
        assert (Hq : x' = px q).
        { destruct (Rtotal_order (py a) (py b)) as [Hab | [Hab | Hab]];
            [ | lra | ].
          - (* ascending *)
            assert (Hband : py a <= py q < py b) by nra.
            assert (Hray : ~ (px q < px a + (px b - px a) * (py q - py a)
                                            / (py b - py a))).
            { intro Hr. apply Hnc. left. split; [ exact Hband | exact Hr ]. }
            assert (Hxf : px a + (px b - px a) * (py q - py a) / (py b - py a)
                            = x').
            { apply Rmult_eq_reg_r with (py b - py a); [ | lra ].
              replace ((px a + (px b - px a) * (py q - py a) / (py b - py a))
                         * (py b - py a))
                with (px a * (py b - py a) + (px b - px a) * (py q - py a))
                by (field; lra).
              nra. }
            lra.
          - (* descending *)
            assert (Hband : py b <= py q < py a) by nra.
            assert (Hray : ~ (px q < px b + (px a - px b) * (py q - py b)
                                            / (py a - py b))).
            { intro Hr. apply Hnc. right. split; [ exact Hband | exact Hr ]. }
            assert (Hxf : px b + (px a - px b) * (py q - py b) / (py a - py b)
                            = x').
            { apply Rmult_eq_reg_r with (py a - py b); [ | lra ].
              replace ((px b + (px a - px b) * (py q - py b) / (py a - py b))
                         * (py a - py b))
                with (px b * (py a - py b) + (px a - px b) * (py q - py b))
                by (field; lra).
              nra. }
            lra. }
        apply Hoff. exists t. split; [ lra | split ].
        { rewrite <- Hq. exact Hx. }
        { exact Hy. }
      * (* t = 1 : the point is vertex b, east on the ray *)
        subst t. apply Hgb. split.
        { nra. }
        { nra. }
Qed.

Lemma ho_zero_count_ray_free : forall (r : Ring) (q : Point),
  ring_complement r q ->
  ray_avoids_vertices q r ->
  ho_count q (ring_edges r) = 0%nat ->
  forall x', px q <= x' -> ~ ring_image r (mkPoint x' (py q)).
Proof.
  intros r q Hcompl Hrav Hz x' Hx' [e [t [Hin [Ht [Hx Hy]]]]].
  destruct e as [a b].
  destruct (ring_edges_endpoints_in r _ Hin) as [Ha Hb].
  cbn [fst snd] in *.
  refine (ho_no_cross_east_free a b q
            (ho_count_zero_no_cross q _ Hz _ Hin) _ _ _ x' Hx'
            (ex_intro _ t (conj Ht (conj _ _)))).
  - intros [He Hle]. exact (Hrav a Ha (conj He Hle)).
  - intros [He Hle]. exact (Hrav b Hb (conj He Hle)).
  - intro Hex. apply Hcompl.
    destruct Hex as [t' [Ht' [Hx2 Hy2]]].
    exists (a, b), t'. cbn [fst snd]. repeat split; try assumption; lra.
  - cbn [px] in Hx. exact Hx.
  - cbn [py] in Hy. exact Hy.
Qed.

(* The straight eastward escape. *)
Lemma escape_east_ray_free : forall (r : Ring) (q : Point),
  (forall x', px q <= x' -> ~ ring_image r (mkPoint x' (py q))) ->
  ~ in_bounded_component_cont r q.
Proof.
  intros r q Hfree; destruct q as [u v]; cbn [px py] in *.
  intros [M [HM Hb]].
  set (X := u + (M + Rabs u + 1)).
  assert (HXge : M + 1 <= X)
    by (unfold X; pose proof (Rle_abs (- u)); rewrite Rabs_Ropp in *; lra).
  assert (HXgt : u <= X) by (unfold X; pose proof (Rabs_pos u); lra).
  assert (Hq : connected_in_complement_cont r (mkPoint u v) (mkPoint X v)).
  { exists (fun t => mkPoint ((1 - t) * u + t * X) ((1 - t) * v + t * v)).
    split; [ apply straight_path_continuous | ]. split; [ | split ].
    - cbn [px py]; f_equal; lra.
    - cbn [px py]; f_equal; lra.
    - intros t Ht Himg.
      assert (Hco : (1 - t) * v + t * v = v) by ring.
      rewrite Hco in Himg.
      refine (Hfree ((1 - t) * u + t * X) _ Himg). nra. }
  specialize (Hb _ Hq). cbn [px py] in Hb. nra.
Qed.

Theorem escape_east_of_zero_count : forall (r : Ring) (q : Point),
  ring_complement r q ->
  ray_avoids_vertices q r ->
  ho_count q (ring_edges r) = 0%nat ->
  ~ in_bounded_component_cont r q.
Proof.
  intros r q Hcompl Hrav Hz.
  apply escape_east_ray_free.
  exact (ho_zero_count_ray_free r q Hcompl Hrav Hz).
Qed.

(* ---------------------------------------------------------------------------
   §3  THE FINAL RESIDUAL, and the strong induction that consumes it.
   --------------------------------------------------------------------------- *)

(* One detour, one fewer crossing.  Simplicity of the ring lives here and
   only here. *)
Definition escape_descent (r : Ring) : Prop :=
  forall p : Point,
    ring_complement r p ->
    ray_avoids_vertices p r ->
    ho_parity_even p (ring_edges r) ->
    (0 < ho_count p (ring_edges r))%nat ->
    exists q : Point,
      connected_in_complement_cont r p q /\
      ray_avoids_vertices q r /\
      ho_parity_even q (ring_edges r) /\
      (ho_count q (ring_edges r) < ho_count p (ring_edges r))%nat.

Theorem escape_of_descent : forall (r : Ring),
  escape_descent r ->
  forall p : Point,
    ring_complement r p ->
    ray_avoids_vertices p r ->
    ho_parity_even p (ring_edges r) ->
    ~ in_bounded_component_cont r p.
Proof.
  intros r Hdesc.
  assert (Hind : forall n (p : Point),
            ho_count p (ring_edges r) = n ->
            ring_complement r p ->
            ray_avoids_vertices p r ->
            ho_parity_even p (ring_edges r) ->
            ~ in_bounded_component_cont r p).
  { induction n as [n IH] using lt_wf_ind.
    intros p Hn Hcompl Hrav Heven Hbnd.
    destruct n as [| n'].
    - exact (escape_east_of_zero_count r p Hcompl Hrav Hn Hbnd).
    - destruct (Hdesc p Hcompl Hrav Heven ltac:(lia))
        as [q [Hconn [Hravq [Hevq Hlt]]]].
      assert (Hcomplq : ring_complement r q).
      { destruct Hconn as [g [_ [_ [Hg1 Hin]]]].
        rewrite <- Hg1. apply Hin. lra. }
      refine (IH (ho_count q (ring_edges r)) ltac:(lia) q eq_refl
                 Hcomplq Hravq Hevq _).
      exact (in_bounded_component_cont_invariant r p q Hconn Hbnd). }
  intros p Hcompl Hrav Heven.
  exact (Hind (ho_count p (ring_edges r)) p eq_refl Hcompl Hrav Heven).
Qed.

(* ---------------------------------------------------------------------------
   §4  Wiring into the seam: H1 from the descent step alone.
   --------------------------------------------------------------------------- *)

Theorem even_parity_escapes_of_descent : forall (r : Ring) (p : Point),
  escape_descent r ->
  ring_complement r p ->
  ray_avoids_vertices p r ->
  even_parity_escapes r p.
Proof.
  intros r p Hdesc Hcompl Hrav Hnin.
  assert (Heven : ho_parity_even p (ring_edges r)).
  { destruct (ho_parity_dec p (ring_edges r)) as [Ho | He]; [ | exact He ].
    exfalso. apply Hnin.
    apply (point_in_ring_ho_agrees p r Hrav). exact Ho. }
  exact (escape_of_descent r Hdesc p Hcompl Hrav Heven).
Qed.

(* THE H1 SEAM FROM THE DESCENT STEP: everything else is Qed. *)
Theorem parity_seam_offring_of_descent : forall (r : Ring) (p : Point),
  escape_descent r ->
  parity_characterises_interior_cont_offring p r.
Proof.
  intros r p Hdesc.
  unfold parity_characterises_interior_cont_offring.
  intros Hs Hc Hm Hcompl Hnh Hrav.
  exact (parity_seam_offring_of_escape r p
           (even_parity_escapes_of_descent r p Hdesc Hcompl Hrav)
           Hs Hc Hm Hcompl Hnh Hrav).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions escape_east_of_zero_count.
Print Assumptions escape_of_descent.
Print Assumptions parity_seam_offring_of_descent.
