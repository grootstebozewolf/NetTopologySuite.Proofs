(* ============================================================================
   NetTopologySuite.Proofs.JCTCornerSector
   ----------------------------------------------------------------------------
   ESCAPE DESCENT, rung 4b-3: THE CORNER SECTOR.  The wall theorem (rung
   4b-2) clears the corridor only strictly INSIDE the wall edge's vertical
   span; to descend past the wall's bottom vertex v the walk must round the
   corner.  This file proves the corner passable: a short VERTICAL DROP just
   west of v, from height py v + eps down to py v - eps, stays in the
   complement for every sufficiently small delta and then eps (eps shrinks
   AFTER delta: the band must be thin relative to the westward offset, so
   the edges incident to v -- whose points in the band stay within
   slope*eps of v -- cannot reach delta west of v).

   Tautness enters exactly once more: an edge meeting v must have v as a
   SHARED ENDPOINT (`taut_vertex_endpoint`), so the obstacle edges split
   into the two-or-more edges AT v (cleared by the slope bound) and the
   edges missing v (cleared by explicit positive margins at v's level, in
   the style of level_gap).  Every clearance is an affine endpoint
   evaluation; the two-stage Rmin fold `corner_fold` produces the uniform
   delta0, then eps0(delta).

   One honest residual hypothesis: NO HORIZONTAL EDGE EXTENDS WEST FROM v
   (`px v <= px` of both endpoints of any horizontal edge at v).  Such an
   edge genuinely blocks every westward drop -- rounding it requires
   walking under its far end, deferred with the recursion to rung 5.

   `corner_sector_guarded` packages the rung: from the corridor point at
   height py v + eps the walk reaches an off-ring, ray-guarded point
   strictly BELOW the corner level -- the destination the descent recursion
   (rung 5) restarts from.  `corridor_offset_jog` glues corridors of
   different offsets at a shared height (the wall theorem's all-delta
   quantifier is exactly what it consumes).

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Arith Lia.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam.
From NTS.Proofs Require Import PointInRingCorrect JCT JCT_OnEdgeCounterexample.
From NTS.Proofs Require Import ConvexOffringSeam JCTParityTransport.
From NTS.Proofs Require Import JCTHalfOpenParity JCTGenericStability JCTLevelJump.
From NTS.Proofs Require Import JCTTrappedHalf JCTSeamAssembly JCTEscapeDescent.
From NTS.Proofs Require Import JCTEastApproach JCTCorridor JCTWalkKit JCTWalkStep.
From NTS.Proofs Require Import JCTTautClearance.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §0  Small kit: coordinate equality, division caps.
   --------------------------------------------------------------------------- *)

Lemma point_eq_of_coords : forall p q : Point,
  px p = px q -> py p = py q -> p = q.
Proof.
  intros [x1 y1] [x2 y2]; cbn; intros Hx Hy; subst; reflexivity.
Qed.

Lemma coord_point_dec : forall p q : Point, {p = q} + {p <> q}.
Proof.
  intros p q.
  destruct (Req_EM_T (px p) (px q)) as [Hx | Hx].
  - destruct (Req_EM_T (py p) (py q)) as [Hy | Hy].
    + left; exact (point_eq_of_coords p q Hx Hy).
    + right; intro He; apply Hy; rewrite He; reflexivity.
  - right; intro He; apply Hx; rewrite He; reflexivity.
Qed.

(* eps < A / B (B positive) gives the product form the clearances consume. *)
Lemma cap_mult : forall (x A B : R), 0 < B -> x < A / B -> x * B < A.
Proof.
  intros x A B HB Hx.
  replace A with (A / B * B) by (field; lra).
  apply Rmult_lt_compat_r; lra.
Qed.

(* The carrier abscissa does not depend on the edge's orientation. *)
Lemma edge_x_at_swap : forall (a b : Point) (y : R),
  py a <> py b ->
  edge_x_at (a, b) y = edge_x_at (b, a) y.
Proof.
  intros a b y Hnh. unfold edge_x_at. field. lra.
Qed.

(* ---------------------------------------------------------------------------
   §1  Tautness at a vertex: any edge through v has v as an endpoint.
   --------------------------------------------------------------------------- *)

Lemma taut_vertex_endpoint : forall (r : Ring) (e1 g : Edge) (v w : Point),
  ring_taut r ->
  In e1 (ring_edges r) -> In g (ring_edges r) ->
  e1 = (v, w) \/ e1 = (w, v) ->
  forall u : R,
    0 <= u <= 1 ->
    (1 - u) * px (fst g) + u * px (snd g) = px v ->
    (1 - u) * py (fst g) + u * py (snd g) = py v ->
    fst g = v \/ snd g = v.
Proof.
  intros r e1 g v w Htaut Hin1 Hing Hor u Hu Hxu Hyu.
  destruct Hor as [He | He]; subst e1.
  - (* v = fst e1, parameter 0 *)
    destruct (Htaut g (v, w) Hing Hin1 u 0 Hu ltac:(lra)
                ltac:(cbn [fst snd]; lra) ltac:(cbn [fst snd]; lra))
      as [[H0 | H1] | [Hf _]].
    + left. subst u. apply point_eq_of_coords; lra.
    + right. subst u. apply point_eq_of_coords; lra.
    + left. rewrite Hf. reflexivity.
  - (* v = snd e1, parameter 1 *)
    destruct (Htaut g (w, v) Hing Hin1 u 1 Hu ltac:(lra)
                ltac:(cbn [fst snd]; lra) ltac:(cbn [fst snd]; lra))
      as [[H0 | H1] | [_ Hs]].
    + left. subst u. apply point_eq_of_coords; lra.
    + right. subst u. apply point_eq_of_coords; lra.
    + right. rewrite Hs. reflexivity.
Qed.

(* ---------------------------------------------------------------------------
   §2  The two-stage Rmin fold: delta first, then eps.
   --------------------------------------------------------------------------- *)

Lemma corner_fold : forall (P : Edge -> R -> R -> Prop) (es : list Edge),
  (forall g, In g es ->
     exists dg, 0 < dg /\ forall delta, 0 < delta < dg ->
       exists eg, 0 < eg /\ forall eps, 0 < eps < eg -> P g delta eps) ->
  exists d0, 0 < d0 /\ forall delta, 0 < delta < d0 ->
    exists e0, 0 < e0 /\ forall eps, 0 < eps < e0 ->
      forall g, In g es -> P g delta eps.
Proof.
  intros P; induction es as [| e es' IH]; intros Hall.
  - exists 1. split; [ lra | ]. intros delta Hd.
    exists 1. split; [ lra | ]. intros eps He g [].
  - destruct (Hall e (or_introl eq_refl)) as [d1 [Hd1 Hb1]].
    destruct (IH (fun g Hg => Hall g (or_intror Hg))) as [d2 [Hd2 Hb2]].
    exists (Rmin d1 d2). split; [ apply Rmin_glb_lt; lra | ].
    intros delta Hd.
    pose proof (Rmin_l d1 d2). pose proof (Rmin_r d1 d2).
    destruct (Hb1 delta ltac:(lra)) as [e1c [He1c Hc1]].
    destruct (Hb2 delta ltac:(lra)) as [e2c [He2c Hc2]].
    exists (Rmin e1c e2c). split; [ apply Rmin_glb_lt; lra | ].
    intros eps He g Hin.
    pose proof (Rmin_l e1c e2c). pose proof (Rmin_r e1c e2c).
    destruct Hin as [He' | Hin].
    + subst g. apply Hc1. lra.
    + apply Hc2; [ lra | exact Hin ].
Qed.

(* ---------------------------------------------------------------------------
   §3  Drop clearance primitives.  The drop segment sits at abscissa xd with
       px v - 2*delta <= xd <= px v - delta/2, heights in [py v - eps,
       py v + eps].  Each primitive kills one obstacle position.
   --------------------------------------------------------------------------- *)

(* Both endpoints at or east of v: the segment never reaches delta/2 west. *)
Lemma drop_avoid_east_of : forall (a b v : Point) (delta xd y : R),
  0 < delta ->
  px v <= px a -> px v <= px b ->
  xd <= px v - delta / 2 ->
  ~ (exists s : R, 0 <= s <= 1 /\
       xd = (1 - s) * px a + s * px b /\
       y = (1 - s) * py a + s * py b).
Proof.
  intros a b v delta xd y Hd Ha Hb Hxd [s [Hs [Hx _]]].
  assert (T1 : (1 - s) * px a >= (1 - s) * px v) by nra.
  assert (T2 : s * px b >= s * px v) by nra.
  nra.
Qed.

(* Both endpoints strictly west of the drop abscissa. *)
Lemma drop_avoid_west_of : forall (a b : Point) (xd y : R),
  px a < xd -> px b < xd ->
  ~ (exists s : R, 0 <= s <= 1 /\
       xd = (1 - s) * px a + s * px b /\
       y = (1 - s) * py a + s * py b).
Proof.
  intros a b xd y Ha Hb [s [Hs [Hx _]]].
  destruct (Rle_or_lt s (1 / 2)) as [Hh | Hh].
  - assert (T1 : (1 - s) * (xd - px a) >= (1 / 2) * (xd - px a)) by nra.
    assert (T2 : 0 <= s * (xd - px b)) by nra.
    nra.
  - assert (T1 : s * (xd - px b) >= (1 / 2) * (xd - px b)) by nra.
    assert (T2 : 0 <= (1 - s) * (xd - px a)) by nra.
    nra.
Qed.

(* Both endpoints strictly above the band's top. *)
Lemma drop_avoid_above_band : forall (a b : Point) (c xd y : R),
  y <= c -> c < py a -> c < py b ->
  ~ (exists s : R, 0 <= s <= 1 /\
       xd = (1 - s) * px a + s * px b /\
       y = (1 - s) * py a + s * py b).
Proof.
  intros a b c xd y Hyc Ha Hb [s [Hs [_ Hy]]].
  destruct (Rle_or_lt s (1 / 2)) as [Hh | Hh].
  - assert (T1 : (1 - s) * (py a - c) >= (1 / 2) * (py a - c)) by nra.
    assert (T2 : 0 <= s * (py b - c)) by nra.
    nra.
  - assert (T1 : s * (py b - c) >= (1 / 2) * (py b - c)) by nra.
    assert (T2 : 0 <= (1 - s) * (py a - c)) by nra.
    nra.
Qed.

(* Both endpoints strictly below the band's bottom. *)
Lemma drop_avoid_below_band : forall (a b : Point) (c xd y : R),
  c <= y -> py a < c -> py b < c ->
  ~ (exists s : R, 0 <= s <= 1 /\
       xd = (1 - s) * px a + s * px b /\
       y = (1 - s) * py a + s * py b).
Proof.
  intros a b c xd y Hyc Ha Hb [s [Hs [_ Hy]]].
  destruct (Rle_or_lt s (1 / 2)) as [Hh | Hh].
  - assert (T1 : (1 - s) * (c - py a) >= (1 / 2) * (c - py a)) by nra.
    assert (T2 : 0 <= s * (c - py b)) by nra.
    nra.
  - assert (T1 : s * (c - py b) >= (1 / 2) * (c - py b)) by nra.
    assert (T2 : 0 <= (1 - s) * (c - py a)) by nra.
    nra.
Qed.

(* An edge leaving FROM v (fst = v), non-horizontal: inside the thin band
   its points stay within slope*eps of v, short of delta/2 west. *)
Lemma drop_avoid_from_vertex : forall (b v : Point) (delta eps xd y : R),
  py b <> py v ->
  0 < delta -> 0 < eps ->
  2 * eps * (Rabs (px b - px v) + 1) < delta * Rabs (py b - py v) ->
  xd <= px v - delta / 2 ->
  py v - eps <= y <= py v + eps ->
  ~ (exists s : R, 0 <= s <= 1 /\
       xd = (1 - s) * px v + s * px b /\
       y = (1 - s) * py v + s * py b).
Proof.
  intros b v delta eps xd y Hnh Hd He Hcap Hxd Hband [s [Hs [Hx Hy]]].
  assert (Hsx : s * (px v - px b) >= delta / 2) by nra.
  assert (Hsy : - eps <= s * (py b - py v) <= eps) by nra.
  assert (Hbx : px b < px v) by nra.
  rewrite (Rabs_left (px b - px v) ltac:(lra)) in Hcap.
  destruct (Rcase_abs (py b - py v)) as [Hby | Hby].
  - rewrite (Rabs_left (py b - py v) Hby) in Hcap.
    assert (T1 : s * (py v - py b) * (px v - px b)
                   >= (delta / 2) * (py v - py b)) by nra.
    assert (T2 : s * (py v - py b) <= eps) by nra.
    assert (T3 : s * (py v - py b) * (px v - px b)
                   <= eps * (px v - px b)) by nra.
    nra.
  - assert (Hby' : 0 < py b - py v) by lra.
    rewrite (Rabs_right (py b - py v) ltac:(lra)) in Hcap.
    assert (T1 : s * (py b - py v) * (px v - px b)
                   >= (delta / 2) * (py b - py v)) by nra.
    assert (T2 : s * (py b - py v) <= eps) by lra.
    assert (T3 : s * (py b - py v) * (px v - px b)
                   <= eps * (px v - px b)) by nra.
    nra.
Qed.

(* Mirror: an edge arriving AT v (snd = v), non-horizontal. *)
Lemma drop_avoid_to_vertex : forall (a v : Point) (delta eps xd y : R),
  py a <> py v ->
  0 < delta -> 0 < eps ->
  2 * eps * (Rabs (px a - px v) + 1) < delta * Rabs (py a - py v) ->
  xd <= px v - delta / 2 ->
  py v - eps <= y <= py v + eps ->
  ~ (exists s : R, 0 <= s <= 1 /\
       xd = (1 - s) * px a + s * px v /\
       y = (1 - s) * py a + s * py v).
Proof.
  intros a v delta eps xd y Hnh Hd He Hcap Hxd Hband [s [Hs [Hx Hy]]].
  assert (Hsx : (1 - s) * (px v - px a) >= delta / 2) by nra.
  assert (Hsy : - eps <= (1 - s) * (py a - py v) <= eps) by nra.
  assert (Hax : px a < px v) by nra.
  rewrite (Rabs_left (px a - px v) ltac:(lra)) in Hcap.
  destruct (Rcase_abs (py a - py v)) as [Hay | Hay].
  - rewrite (Rabs_left (py a - py v) Hay) in Hcap.
    assert (T1 : (1 - s) * (py v - py a) * (px v - px a)
                   >= (delta / 2) * (py v - py a)) by nra.
    assert (T2 : (1 - s) * (py v - py a) <= eps) by nra.
    assert (T3 : (1 - s) * (py v - py a) * (px v - px a)
                   <= eps * (px v - px a)) by nra.
    nra.
  - assert (Hay' : 0 < py a - py v) by lra.
    rewrite (Rabs_right (py a - py v) ltac:(lra)) in Hcap.
    assert (T1 : (1 - s) * (py a - py v) * (px v - px a)
                   >= (delta / 2) * (py a - py v)) by nra.
    assert (T2 : (1 - s) * (py a - py v) <= eps) by lra.
    assert (T3 : (1 - s) * (py a - py v) * (px v - px a)
                   <= eps * (px v - px a)) by nra.
    nra.
Qed.

(* An edge missing v whose carrier crosses v's level at abscissa X with
   |X - px v| = m > 0: for 4*delta < m and a thin band the drop segment
   stays m/2 away from the carrier's band points. *)
Lemma drop_avoid_level_crossing : forall (a b v : Point) (delta eps xd y X : R),
  py a <> py b ->
  (X - px a) * (py b - py a) = (py v - py a) * (px b - px a) ->
  0 < delta -> 0 < eps ->
  4 * delta < Rabs (X - px v) ->
  4 * eps * (Rabs (px b - px a) + 1)
    < Rabs (X - px v) * Rabs (py b - py a) ->
  px v - 2 * delta <= xd <= px v - delta / 2 ->
  py v - eps <= y <= py v + eps ->
  ~ (exists s : R, 0 <= s <= 1 /\
       xd = (1 - s) * px a + s * px b /\
       y = (1 - s) * py a + s * py b).
Proof.
  intros a b v delta eps xd y X Hnh HX Hd He Hdcap Hecap Hxd Hband
    [s [Hs [Hx Hy]]].
  assert (Hx2 : xd - px a = s * (px b - px a)) by nra.
  assert (Hy2 : y - py a = s * (py b - py a)) by nra.
  apply (Rmult_eq_compat_r (py b - py a)) in Hx2.
  apply (Rmult_eq_compat_r (px b - px a)) in Hy2.
  assert (Hkey : (xd - X) * (py b - py a) = (y - py v) * (px b - px a)) by nra.
  (* |xd - X| >= m/2 *)
  assert (Habs1 : Rabs (X - px v) / 2 <= Rabs (xd - X)).
  { destruct (Rcase_abs (X - px v)) as [Hc | Hc].
    - rewrite (Rabs_left (X - px v) Hc) in *.
      rewrite (Rabs_right (xd - X) ltac:(lra)). lra.
    - rewrite (Rabs_right (X - px v) Hc) in *.
      rewrite (Rabs_left (xd - X) ltac:(lra)). lra. }
  assert (Hay : Rabs (y - py v) <= eps)
    by (unfold Rabs; destruct (Rcase_abs (y - py v)); lra).
  assert (Hprod : Rabs (xd - X) * Rabs (py b - py a)
                    = Rabs (y - py v) * Rabs (px b - px a))
    by (rewrite <- !Rabs_mult; rewrite Hkey; reflexivity).
  pose proof (Rabs_pos (px b - px a)) as HDx.
  pose proof (Rabs_pos_lt (py b - py a) ltac:(lra)) as HDy.
  pose proof (Rabs_pos (xd - X)) as HxdX.
  assert (T1 : (Rabs (X - px v) / 2) * Rabs (py b - py a)
                 <= Rabs (xd - X) * Rabs (py b - py a)) by nra.
  assert (T2 : Rabs (y - py v) * Rabs (px b - px a)
                 <= eps * Rabs (px b - px a)) by nra.
  nra.
Qed.

(* ---------------------------------------------------------------------------
   §4  The per-edge dispatch and the corner drop.
   --------------------------------------------------------------------------- *)

Lemma corner_edge_clear : forall (r : Ring) (e1 g : Edge) (v w : Point),
  ring_taut r ->
  In e1 (ring_edges r) -> In g (ring_edges r) ->
  e1 = (v, w) \/ e1 = (w, v) ->
  py v < py w ->
  (py (fst g) = py (snd g) -> fst g = v \/ snd g = v ->
     px v <= px (fst g) /\ px v <= px (snd g)) ->
  exists dg, 0 < dg /\ forall delta, 0 < delta < dg ->
  exists eg, 0 < eg /\ forall eps, 0 < eps < eg ->
    forall xd y,
      px v - 2 * delta <= xd <= px v - delta / 2 ->
      py v - eps <= y <= py v + eps ->
      ~ (exists s : R, 0 <= s <= 1 /\
           xd = (1 - s) * px (fst g) + s * px (snd g) /\
           y = (1 - s) * py (fst g) + s * py (snd g)).
Proof.
  intros r e1 g v w Htaut Hin1 Hing Hor Hvw Hez.
  destruct g as [a b]; cbn [fst snd] in *.
  (* CASE A: an endpoint of g IS v. *)
  destruct (coord_point_dec a v) as [Hav | Hav].
  { subst a.
    destruct (Req_EM_T (py b) (py v)) as [Hh | Hh].
    - (* horizontal at v: extends east by hypothesis *)
      destruct (Hez ltac:(cbn; lra) ltac:(left; reflexivity)) as [_ Hbe].
      exists 1. split; [ lra | ]. intros delta Hd.
      exists 1. split; [ lra | ]. intros eps He xd y Hxd Hband.
      apply (drop_avoid_east_of v b v delta xd y); try lra.
    - (* non-horizontal from v *)
      exists 1. split; [ lra | ]. intros delta Hd.
      exists (delta * Rabs (py b - py v) / (2 * (Rabs (px b - px v) + 1))).
      pose proof (Rabs_pos_lt (py b - py v) ltac:(lra)) as HB.
      pose proof (Rabs_pos (px b - px v)) as HA.
      split; [ apply Rdiv_lt_0_compat; nra | ].
      intros eps He xd y Hxd Hband.
      assert (Hcap : 2 * eps * (Rabs (px b - px v) + 1)
                       < delta * Rabs (py b - py v)).
      { destruct He as [He1 He2].
        apply (cap_mult eps _ (2 * (Rabs (px b - px v) + 1))
                 ltac:(nra)) in He2.
        lra. }
      apply (drop_avoid_from_vertex b v delta eps xd y Hh
               ltac:(lra) ltac:(lra) Hcap ltac:(lra) Hband). }
  destruct (coord_point_dec b v) as [Hbv | Hbv].
  { subst b.
    destruct (Req_EM_T (py a) (py v)) as [Hh | Hh].
    - destruct (Hez ltac:(cbn; lra) ltac:(right; reflexivity)) as [Hae _].
      exists 1. split; [ lra | ]. intros delta Hd.
      exists 1. split; [ lra | ]. intros eps He xd y Hxd Hband.
      apply (drop_avoid_east_of a v v delta xd y); try lra.
    - exists 1. split; [ lra | ]. intros delta Hd.
      exists (delta * Rabs (py a - py v) / (2 * (Rabs (px a - px v) + 1))).
      pose proof (Rabs_pos_lt (py a - py v) ltac:(lra)) as HB.
      pose proof (Rabs_pos (px a - px v)) as HA.
      split; [ apply Rdiv_lt_0_compat; nra | ].
      intros eps He xd y Hxd Hband.
      assert (Hcap : 2 * eps * (Rabs (px a - px v) + 1)
                       < delta * Rabs (py a - py v)).
      { destruct He as [He1 He2].
        apply (cap_mult eps _ (2 * (Rabs (px a - px v) + 1))
                 ltac:(nra)) in He2.
        lra. }
      apply (drop_avoid_to_vertex a v delta eps xd y Hh
               ltac:(lra) ltac:(lra) Hcap ltac:(lra) Hband). }
  (* CASE B: g misses v -- any contact contradicts tautness. *)
  assert (Hnotong : forall u : R, 0 <= u <= 1 ->
            ~ ((1 - u) * px a + u * px b = px v /\
               (1 - u) * py a + u * py b = py v)).
  { intros u Hu [Hxu Hyu].
    destruct (taut_vertex_endpoint r e1 (a, b) v w Htaut Hin1 Hing Hor
                u Hu ltac:(cbn [fst snd]; exact Hxu)
                ltac:(cbn [fst snd]; exact Hyu)) as [Hfa | Hfb];
      cbn [fst snd] in *; [ exact (Hav Hfa) | exact (Hbv Hfb) ]. }
  destruct (Rlt_le_dec (py v) (py a)) as [Haab | Hale];
  destruct (Rlt_le_dec (py v) (py b)) as [Hbab | Hble].
  - (* both strictly above the level *)
    exists 1. split; [ lra | ]. intros delta Hd.
    exists (Rmin (py a - py v) (py b - py v)).
    split; [ apply Rmin_glb_lt; lra | ].
    intros eps He xd y Hxd Hband.
    pose proof (Rmin_l (py a - py v) (py b - py v)).
    pose proof (Rmin_r (py a - py v) (py b - py v)).
    apply (drop_avoid_above_band a b (py v + eps) xd y); lra.
  - (* a above, b at-or-below: the carrier crosses the level; X <> px v *)
    assert (Hnh : py a <> py b) by lra.
    set (X := edge_x_at (a, b) (py v)).
    assert (HX : (X - px a) * (py b - py a) = (py v - py a) * (px b - px a))
      by (unfold X, edge_x_at; field; lra).
    assert (Hm : X <> px v).
    { intro Heq.
      set (u := (py a - py v) / (py a - py b)).
      assert (Hu1 : u * (py a - py b) = py a - py v)
        by (unfold u; field; lra).
      assert (Hub : 0 <= u <= 1) by nra.
      apply (Hnotong u Hub).
      split.
      - unfold u. unfold X, edge_x_at in Heq. rewrite <- Heq. field. lra.
      - nra. }
    pose proof (Rabs_pos_lt (X - px v) ltac:(lra)) as Hmpos.
    exists (Rabs (X - px v) / 4). split; [ lra | ]. intros delta Hd.
    pose proof (Rabs_pos_lt (py b - py a) ltac:(lra)) as HDy.
    pose proof (Rabs_pos (px b - px a)) as HDx.
    exists (Rabs (X - px v) * Rabs (py b - py a)
              / (4 * (Rabs (px b - px a) + 1))).
    split; [ apply Rdiv_lt_0_compat; nra | ].
    intros eps He xd y Hxd Hband.
    assert (Hcap : 4 * eps * (Rabs (px b - px a) + 1)
                     < Rabs (X - px v) * Rabs (py b - py a)).
    { destruct He as [He1 He2].
      apply (cap_mult eps _ (4 * (Rabs (px b - px a) + 1))
               ltac:(nra)) in He2.
      lra. }
    apply (drop_avoid_level_crossing a b v delta eps xd y X Hnh HX
             ltac:(lra) ltac:(lra) ltac:(lra) Hcap Hxd Hband).
  - (* a at-or-below, b above: mirror *)
    assert (Hnh : py a <> py b) by lra.
    set (X := edge_x_at (a, b) (py v)).
    assert (HX : (X - px a) * (py b - py a) = (py v - py a) * (px b - px a))
      by (unfold X, edge_x_at; field; lra).
    assert (Hm : X <> px v).
    { intro Heq.
      set (u := (py v - py a) / (py b - py a)).
      assert (Hu1 : u * (py b - py a) = py v - py a)
        by (unfold u; field; lra).
      assert (Hub : 0 <= u <= 1) by nra.
      apply (Hnotong u Hub).
      split.
      - unfold u. unfold X, edge_x_at in Heq. rewrite <- Heq. field. lra.
      - nra. }
    pose proof (Rabs_pos_lt (X - px v) ltac:(lra)) as Hmpos.
    exists (Rabs (X - px v) / 4). split; [ lra | ]. intros delta Hd.
    pose proof (Rabs_pos_lt (py b - py a) ltac:(lra)) as HDy.
    pose proof (Rabs_pos (px b - px a)) as HDx.
    exists (Rabs (X - px v) * Rabs (py b - py a)
              / (4 * (Rabs (px b - px a) + 1))).
    split; [ apply Rdiv_lt_0_compat; nra | ].
    intros eps He xd y Hxd Hband.
    assert (Hcap : 4 * eps * (Rabs (px b - px a) + 1)
                     < Rabs (X - px v) * Rabs (py b - py a)).
    { destruct He as [He1 He2].
      apply (cap_mult eps _ (4 * (Rabs (px b - px a) + 1))
               ltac:(nra)) in He2.
      lra. }
    apply (drop_avoid_level_crossing a b v delta eps xd y X Hnh HX
             ltac:(lra) ltac:(lra) ltac:(lra) Hcap Hxd Hband).
  - (* both at or below the level *)
    destruct (Req_EM_T (py a) (py v)) as [Hae | Hae];
    destruct (Req_EM_T (py b) (py v)) as [Hbe | Hbe].
    + (* horizontal AT the level, missing v: one side of v *)
      assert (Hax : px a <> px v)
        by (intro Hx; apply Hav, point_eq_of_coords; lra).
      assert (Hbx : px b <> px v)
        by (intro Hx; apply Hbv, point_eq_of_coords; lra).
      destruct (Rlt_le_dec (px a) (px v)) as [Haw | Haw].
      * (* a west: b must be west too, else contact between *)
        destruct (Rlt_le_dec (px b) (px v)) as [Hbw | Hbw].
        -- exists (Rmin (px v - px a) (px v - px b) / 4).
           pose proof (Rmin_glb_lt (px v - px a) (px v - px b) 0
                         ltac:(lra) ltac:(lra)).
           split; [ lra | ]. intros delta Hd.
           exists 1. split; [ lra | ]. intros eps He xd y Hxd Hband.
           pose proof (Rmin_l (px v - px a) (px v - px b)).
           pose proof (Rmin_r (px v - px a) (px v - px b)).
           apply (drop_avoid_west_of a b xd y); lra.
        -- exfalso.
           set (u := (px v - px a) / (px b - px a)).
           assert (Hu1 : u * (px b - px a) = px v - px a)
             by (unfold u; field; lra).
           assert (Hub : 0 <= u <= 1) by nra.
           apply (Hnotong u Hub). split; nra.
      * (* a east (strictly): b must be east too *)
        destruct (Rlt_le_dec (px b) (px v)) as [Hbw | Hbw].
        -- exfalso.
           set (u := (px v - px a) / (px b - px a)).
           assert (Hu1 : u * (px b - px a) = px v - px a)
             by (unfold u; field; lra).
           assert (Hub : 0 <= u <= 1) by nra.
           apply (Hnotong u Hub). split; nra.
        -- exists 1. split; [ lra | ]. intros delta Hd.
           exists 1. split; [ lra | ]. intros eps He xd y Hxd Hband.
           apply (drop_avoid_east_of a b v delta xd y); lra.
    + (* a at the level, b strictly below: carrier crosses; X = px a <> px v *)
      assert (Hnh : py a <> py b) by lra.
      set (X := edge_x_at (a, b) (py v)).
      assert (HX : (X - px a) * (py b - py a) = (py v - py a) * (px b - px a))
        by (unfold X, edge_x_at; field; lra).
      assert (Hm : X <> px v).
      { intro Heq.
        apply (Hnotong 0 ltac:(lra)).
        assert (HX0 : X = px a) by nra.
        split; lra. }
      pose proof (Rabs_pos_lt (X - px v) ltac:(lra)) as Hmpos.
      exists (Rabs (X - px v) / 4). split; [ lra | ]. intros delta Hd.
      pose proof (Rabs_pos_lt (py b - py a) ltac:(lra)) as HDy.
      pose proof (Rabs_pos (px b - px a)) as HDx.
      exists (Rabs (X - px v) * Rabs (py b - py a)
                / (4 * (Rabs (px b - px a) + 1))).
      split; [ apply Rdiv_lt_0_compat; nra | ].
      intros eps He xd y Hxd Hband.
      assert (Hcap : 4 * eps * (Rabs (px b - px a) + 1)
                       < Rabs (X - px v) * Rabs (py b - py a)).
      { destruct He as [He1 He2].
        apply (cap_mult eps _ (4 * (Rabs (px b - px a) + 1))
                 ltac:(nra)) in He2.
        lra. }
      apply (drop_avoid_level_crossing a b v delta eps xd y X Hnh HX
               ltac:(lra) ltac:(lra) ltac:(lra) Hcap Hxd Hband).
    + (* b at the level, a strictly below: X = px b <> px v *)
      assert (Hnh : py a <> py b) by lra.
      set (X := edge_x_at (a, b) (py v)).
      assert (HX : (X - px a) * (py b - py a) = (py v - py a) * (px b - px a))
        by (unfold X, edge_x_at; field; lra).
      assert (Hm : X <> px v).
      { intro Heq.
        apply (Hnotong 1 ltac:(lra)).
        assert (HX1 : X = px b) by nra.
        split; lra. }
      pose proof (Rabs_pos_lt (X - px v) ltac:(lra)) as Hmpos.
      exists (Rabs (X - px v) / 4). split; [ lra | ]. intros delta Hd.
      pose proof (Rabs_pos_lt (py b - py a) ltac:(lra)) as HDy.
      pose proof (Rabs_pos (px b - px a)) as HDx.
      exists (Rabs (X - px v) * Rabs (py b - py a)
                / (4 * (Rabs (px b - px a) + 1))).
      split; [ apply Rdiv_lt_0_compat; nra | ].
      intros eps He xd y Hxd Hband.
      assert (Hcap : 4 * eps * (Rabs (px b - px a) + 1)
                       < Rabs (X - px v) * Rabs (py b - py a)).
      { destruct He as [He1 He2].
        apply (cap_mult eps _ (4 * (Rabs (px b - px a) + 1))
                 ltac:(nra)) in He2.
        lra. }
      apply (drop_avoid_level_crossing a b v delta eps xd y X Hnh HX
               ltac:(lra) ltac:(lra) ltac:(lra) Hcap Hxd Hband).
    + (* both strictly below *)
      exists 1. split; [ lra | ]. intros delta Hd.
      exists (Rmin (py v - py a) (py v - py b)).
      split; [ apply Rmin_glb_lt; lra | ].
      intros eps He xd y Hxd Hband.
      pose proof (Rmin_l (py v - py a) (py v - py b)).
      pose proof (Rmin_r (py v - py a) (py v - py b)).
      apply (drop_avoid_below_band a b (py v - eps) xd y); lra.
Qed.

(* The drop abscissa tracks the corridor: for a thin band it sits between
   delta/2 and 2*delta west of the corner. *)
Lemma drop_abscissa_bound : forall (v w : Point) (delta eps : R),
  py v < py w -> 0 < delta -> 0 < eps ->
  2 * eps * (Rabs (px w - px v) + 1) < delta * (py w - py v) ->
  px v - 2 * delta <= edge_x_at (v, w) (py v + eps) - delta
    <= px v - delta / 2.
Proof.
  intros v w delta eps Hvw Hd He Hcap.
  unfold edge_x_at.
  set (q := (px w - px v) * (py v + eps - py v) / (py w - py v)).
  assert (Hq : q * (py w - py v) = (px w - px v) * eps)
    by (unfold q; field; lra).
  destruct (Rcase_abs (px w - px v)) as [Hc | Hc].
  - rewrite (Rabs_left (px w - px v) Hc) in Hcap.
    assert (Hb1 : - (delta / 2) * (py w - py v) <= q * (py w - py v)) by nra.
    assert (Hb2 : q * (py w - py v) <= 0) by nra.
    split; nra.
  - rewrite (Rabs_right (px w - px v) Hc) in Hcap.
    assert (Hb1 : 0 <= q * (py w - py v)) by nra.
    assert (Hb2 : q * (py w - py v) <= (delta / 2) * (py w - py v)) by nra.
    split; nra.
Qed.

(* THE CORNER DROP: the vertical segment just west of the wall's bottom
   vertex is skeleton-free, for all small delta and then all small eps. *)
Theorem corner_drop : forall (r : Ring) (e1 : Edge) (v w : Point),
  ring_taut r ->
  In e1 (ring_edges r) ->
  e1 = (v, w) \/ e1 = (w, v) ->
  py v < py w ->
  (forall g, In g (ring_edges r) ->
     py (fst g) = py (snd g) -> fst g = v \/ snd g = v ->
     px v <= px (fst g) /\ px v <= px (snd g)) ->
  exists delta0, 0 < delta0 /\
  forall delta, 0 < delta < delta0 ->
  exists eps0, 0 < eps0 /\
  forall eps, 0 < eps < eps0 ->
    forall y, py v - eps <= y <= py v + eps ->
      ~ ring_image r (mkPoint (edge_x_at e1 (py v + eps) - delta) y).
Proof.
  intros r e1 v w Htaut Hin1 Hor Hvw Hez.
  destruct (corner_fold
              (fun g delta eps =>
                 forall xd y,
                   px v - 2 * delta <= xd <= px v - delta / 2 ->
                   py v - eps <= y <= py v + eps ->
                   ~ (exists s : R, 0 <= s <= 1 /\
                        xd = (1 - s) * px (fst g) + s * px (snd g) /\
                        y = (1 - s) * py (fst g) + s * py (snd g)))
              (ring_edges r)) as [d0 [Hd0 Hstage]].
  { intros g Hing.
    exact (corner_edge_clear r e1 g v w Htaut Hin1 Hing Hor Hvw
             (Hez g Hing)). }
  exists d0. split; [ exact Hd0 | ].
  intros delta Hd.
  destruct (Hstage delta Hd) as [e0 [He0 Hball]].
  pose proof (Rabs_pos (px w - px v)) as HA.
  exists (Rmin e0 (delta * (py w - py v) / (2 * (Rabs (px w - px v) + 1)))).
  split.
  { apply Rmin_glb_lt; [ exact He0 | apply Rdiv_lt_0_compat; nra ]. }
  intros eps He y Hband Himg.
  pose proof (Rmin_l e0
                (delta * (py w - py v) / (2 * (Rabs (px w - px v) + 1)))).
  pose proof (Rmin_r e0
                (delta * (py w - py v) / (2 * (Rabs (px w - px v) + 1)))).
  assert (Hcap : 2 * eps * (Rabs (px w - px v) + 1) < delta * (py w - py v)).
  { destruct He as [He1 He2].
    assert (He3 : eps < delta * (py w - py v)
                          / (2 * (Rabs (px w - px v) + 1))) by lra.
    apply (cap_mult eps _ (2 * (Rabs (px w - px v) + 1)) ltac:(nra)) in He3.
    lra. }
  assert (Hxb : px v - 2 * delta <= edge_x_at e1 (py v + eps) - delta
                  <= px v - delta / 2).
  { destruct Hor as [He' | He']; subst e1.
    - apply (drop_abscissa_bound v w delta eps Hvw ltac:(lra) ltac:(lra) Hcap).
    - rewrite <- (edge_x_at_swap v w (py v + eps) ltac:(lra)).
      apply (drop_abscissa_bound v w delta eps Hvw ltac:(lra) ltac:(lra) Hcap). }
  destruct Himg as [g [s [Hing [Hs [Hx Hy]]]]].
  cbn [px py] in Hx, Hy.
  apply (Hball eps ltac:(lra) g Hing
           (edge_x_at e1 (py v + eps) - delta) y Hxb Hband).
  exists s. repeat split; try assumption; lra.
Qed.

(* ---------------------------------------------------------------------------
   §5  Connectors: offset jog, parking BELOW a level, the guarded sector.
   --------------------------------------------------------------------------- *)

(* Corridors of two offsets at one height connect horizontally; the wall
   theorem's all-delta freedom is exactly the hypothesis. *)
Lemma corridor_offset_jog : forall (r : Ring) (e1 : Edge) (y d1 d2 : R),
  d1 <= d2 ->
  (forall delta, d1 <= delta <= d2 -> ~ ring_image r (corridor e1 delta y)) ->
  connected_in_complement_cont r (corridor e1 d1 y) (corridor e1 d2 y).
Proof.
  intros r e1 y d1 d2 Hle Hfree.
  unfold corridor.
  apply horizontal_connected.
  intros x Hx.
  assert (Hx1 : edge_x_at e1 y - d2 <= x <= edge_x_at e1 y - d1).
  { unfold Rmin, Rmax in Hx.
    destruct (Rle_dec (edge_x_at e1 y - d1) (edge_x_at e1 y - d2)); lra. }
  intro Himg.
  apply (Hfree (edge_x_at e1 y - x) ltac:(lra)).
  unfold corridor.
  replace (edge_x_at e1 y - (edge_x_at e1 y - x)) with x by ring.
  exact Himg.
Qed.

(* Mirror of level_gap: an explicit vertex-level-free gap BELOW a height. *)
Fixpoint depth_gap (y0 : R) (l : list Point) : R :=
  match l with
  | [] => 1
  | v :: l' =>
      if Rle_dec y0 (py v) then depth_gap y0 l'
      else Rmin (y0 - py v) (depth_gap y0 l')
  end.

Lemma depth_gap_pos : forall (y0 : R) (l : list Point), 0 < depth_gap y0 l.
Proof.
  intros y0; induction l as [| v l' IH]; cbn [depth_gap]; [ lra | ].
  destruct (Rle_dec y0 (py v)); [ exact IH | apply Rmin_glb_lt; lra ].
Qed.

Lemma depth_gap_spec : forall (y0 : R) (l : list Point) (v : Point),
  In v l -> y0 <= py v \/ py v <= y0 - depth_gap y0 l.
Proof.
  intros y0; induction l as [| w l' IH]; intros v Hin; [ contradiction | ].
  cbn [depth_gap].
  destruct Hin as [He | Hin].
  - subst w. destruct (Rle_dec y0 (py v)) as [Hle | Hgt].
    + left; exact Hle.
    + right. pose proof (Rmin_l (y0 - py v) (depth_gap y0 l')). lra.
  - destruct (Rle_dec y0 (py w)) as [Hle | Hgt].
    + exact (IH v Hin).
    + destruct (IH v Hin) as [H | H]; [ left; exact H | right ].
      pose proof (Rmin_r (y0 - py w) (depth_gap y0 l')). lra.
Qed.

Lemma guard_of_fresh_depth : forall (r : Ring) (q : Point) (y0 : R),
  y0 - depth_gap y0 r < py q -> py q < y0 ->
  ray_avoids_vertices q r.
Proof.
  intros r q y0 H1 H2 v Hv [Heq _].
  destruct (depth_gap_spec y0 r v Hv) as [H | H]; lra.
Qed.

(* THE RUNG THEOREM: from the wall's corridor at height py v + eps the walk
   rounds the bottom corner to an off-ring, ray-guarded point strictly
   below the corner level -- one vertical complement segment. *)
Theorem corner_sector_guarded : forall (r : Ring) (e1 : Edge) (v w : Point),
  ring_taut r ->
  In e1 (ring_edges r) ->
  e1 = (v, w) \/ e1 = (w, v) ->
  py v < py w ->
  (forall g, In g (ring_edges r) ->
     py (fst g) = py (snd g) -> fst g = v \/ snd g = v ->
     px v <= px (fst g) /\ px v <= px (snd g)) ->
  exists delta0, 0 < delta0 /\
  forall delta, 0 < delta < delta0 ->
  exists eps0, 0 < eps0 /\
  forall eps, 0 < eps < eps0 ->
    connected_in_complement_cont r
      (corridor e1 delta (py v + eps))
      (mkPoint (edge_x_at e1 (py v + eps) - delta) (py v - eps)) /\
    ring_complement r
      (mkPoint (edge_x_at e1 (py v + eps) - delta) (py v - eps)) /\
    ray_avoids_vertices
      (mkPoint (edge_x_at e1 (py v + eps) - delta) (py v - eps)) r.
Proof.
  intros r e1 v w Htaut Hin1 Hor Hvw Hez.
  destruct (corner_drop r e1 v w Htaut Hin1 Hor Hvw Hez)
    as [delta0 [Hd0 Hstage]].
  exists delta0. split; [ exact Hd0 | ].
  intros delta Hd.
  destruct (Hstage delta Hd) as [eps0 [He0 Hfree]].
  exists (Rmin eps0 (depth_gap (py v) r)).
  pose proof (depth_gap_pos (py v) r) as Hgp.
  split; [ apply Rmin_glb_lt; lra | ].
  intros eps He.
  pose proof (Rmin_l eps0 (depth_gap (py v) r)).
  pose proof (Rmin_r eps0 (depth_gap (py v) r)).
  assert (Hfree' : forall y, py v - eps <= y <= py v + eps ->
            ~ ring_image r
                (mkPoint (edge_x_at e1 (py v + eps) - delta) y))
    by (intros y Hy; apply Hfree; lra).
  split; [ | split ].
  - unfold corridor.
    apply (vertical_connected r (edge_x_at e1 (py v + eps) - delta)
             (py v + eps) (py v - eps)).
    intros y Hy.
    apply Hfree'.
    unfold Rmin, Rmax in Hy.
    destruct (Rle_dec (py v + eps) (py v - eps)); lra.
  - apply Hfree'. lra.
  - apply (guard_of_fresh_depth r _ (py v)); cbn [py]; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions taut_vertex_endpoint.
Print Assumptions corner_edge_clear.
Print Assumptions corner_drop.
Print Assumptions corner_sector_guarded.
