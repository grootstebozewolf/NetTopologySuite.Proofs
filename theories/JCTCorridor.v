(* ============================================================================
   NetTopologySuite.Proofs.JCTCorridor
   ----------------------------------------------------------------------------
   ESCAPE DESCENT, rung 2: the corridor toolkit -- travel ALONG an edge at a
   westward offset, with explicit affine clearance margins.

   The corridor along a non-horizontal carrier edge e at offset delta is the
   set of points (edge_x_at e y - delta, y) for y in a height window.  Two
   structural facts make it formalisable in the corpus's style:

     1. `edge_x_at e` -- the carrier LINE's abscissa -- is AFFINE in y, so
        the corridor is itself a STRAIGHT SEGMENT (`edge_x_at_affine`), and
        `straight_path_continuous` carries it (`corridor_connected`).
     2. Clearance against any other edge f reduces to the sign of the
        affine function  phi(s) = edge_x_at e (y_f s) - x_f s  along f.  An
        affine function lies between its endpoint values
        (`affine_between`), so if f's endpoints are strictly west by more
        than delta, or strictly east, or strictly outside the height
        window, the whole of f misses the corridor -- EXPLICIT margins,
        no compactness, no square roots (`corridor_avoid_*`).  The carrier
        itself is missed for every positive offset
        (`corridor_avoid_carrier`).

   Plus `level_gap`: above any height there is an explicit vertex-level-free
   gap (finite Rmin), so a corridor endpoint can be parked at a height with
   NO vertex level at all -- `guard_of_fresh_level` then gives the ray guard
   for free.  These are the pieces rung 3's boundary walk composes; the
   mixed case (an edge only partially inside the window) is handled there by
   window clipping, and the touch-freedom needed to orient phi comes from
   `ring_simple` via `crossings_distinct`-style arguments.

   A worked instance closes the file: a concrete corridor inside the unit
   square, every clearance discharged by the helpers.

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
From NTS.Proofs Require Import JCTEastApproach.
From NTS.Proofs Require Import RectangleJCT.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §1  The carrier line and its affineness.
   --------------------------------------------------------------------------- *)

Definition edge_x_at (e : Edge) (y : R) : R :=
  let (a, b) := e in
  px a + (px b - px a) * (y - py a) / (py b - py a).

Lemma edge_x_at_affine : forall (e : Edge) (u v t : R),
  py (fst e) <> py (snd e) ->
  edge_x_at e ((1 - t) * u + t * v)
    = (1 - t) * edge_x_at e u + t * edge_x_at e v.
Proof.
  intros [a b] u v t Hnh. cbn [fst snd] in Hnh. unfold edge_x_at.
  field. lra.
Qed.

Lemma edge_x_at_endpoint_a : forall (e : Edge),
  py (fst e) <> py (snd e) ->
  edge_x_at e (py (fst e)) = px (fst e).
Proof.
  intros [a b] Hnh. cbn [fst snd] in *. unfold edge_x_at. field. lra.
Qed.

Lemma edge_x_at_endpoint_b : forall (e : Edge),
  py (fst e) <> py (snd e) ->
  edge_x_at e (py (snd e)) = px (snd e).
Proof.
  intros [a b] Hnh. cbn [fst snd] in *. unfold edge_x_at. field. lra.
Qed.

(* Points ON the carrier sit exactly on the line. *)
Lemma on_carrier_x : forall (e : Edge) (s : R),
  py (fst e) <> py (snd e) ->
  edge_x_at e ((1 - s) * py (fst e) + s * py (snd e))
    = (1 - s) * px (fst e) + s * px (snd e).
Proof.
  intros e s Hnh.
  rewrite (edge_x_at_affine e (py (fst e)) (py (snd e)) s Hnh).
  rewrite (edge_x_at_endpoint_a e Hnh), (edge_x_at_endpoint_b e Hnh).
  reflexivity.
Qed.

(* An affine function lies between its endpoint values. *)
Lemma affine_between : forall (al be u v s : R),
  0 <= s <= 1 ->
  Rmin (al * u + be) (al * v + be)
    <= al * ((1 - s) * u + s * v) + be
  /\ al * ((1 - s) * u + s * v) + be
    <= Rmax (al * u + be) (al * v + be).
Proof.
  intros al be u v s Hs.
  unfold Rmin, Rmax; destruct (Rle_dec (al * u + be) (al * v + be)); split; nra.
Qed.

(* ---------------------------------------------------------------------------
   §2  The corridor is a straight complement path.
   --------------------------------------------------------------------------- *)

Definition corridor (e : Edge) (delta y : R) : Point :=
  mkPoint (edge_x_at e y - delta) y.

Lemma corridor_connected : forall (r : Ring) (e : Edge) (ylo yhi delta : R),
  py (fst e) <> py (snd e) ->
  ylo <= yhi ->
  (forall y, ylo <= y <= yhi -> ~ ring_image r (corridor e delta y)) ->
  connected_in_complement_cont r
    (corridor e delta yhi) (corridor e delta ylo).
Proof.
  intros r e ylo yhi delta Hnh Hle Hfree.
  exists (fun t => mkPoint
            ((1 - t) * (edge_x_at e yhi - delta)
               + t * (edge_x_at e ylo - delta))
            ((1 - t) * yhi + t * ylo)).
  split; [ apply straight_path_continuous | ]. split; [ | split ].
  - unfold corridor; cbn [px py]; f_equal; lra.
  - unfold corridor; cbn [px py]; f_equal; lra.
  - intros t Ht Himg.
    set (y := (1 - t) * yhi + t * ylo).
    assert (Hw : ylo <= y <= yhi) by (unfold y; nra).
    assert (Hco : (1 - t) * (edge_x_at e yhi - delta)
                    + t * (edge_x_at e ylo - delta)
                  = edge_x_at e y - delta).
    { unfold y. rewrite (edge_x_at_affine e yhi ylo t Hnh). lra. }
    rewrite Hco in Himg.
    exact (Hfree y Hw Himg).
Qed.

(* Per-edge freedom assembles into skeleton freedom. *)
Lemma corridor_free_of_edges : forall (r : Ring) (e : Edge) (ylo yhi delta : R),
  (forall f, In f (ring_edges r) ->
     forall y, ylo <= y <= yhi ->
       ~ (exists s : R, 0 <= s <= 1 /\
            edge_x_at e y - delta = (1 - s) * px (fst f) + s * px (snd f) /\
            y = (1 - s) * py (fst f) + s * py (snd f))) ->
  forall y, ylo <= y <= yhi -> ~ ring_image r (corridor e delta y).
Proof.
  intros r e ylo yhi delta Havoid y Hw [f [s [Hin [[Hs1 Hs2] [Hx Hy]]]]].
  apply (Havoid f Hin y Hw).
  exists s. unfold corridor in *; cbn [px py] in *.
  repeat split; assumption.
Qed.

(* ---------------------------------------------------------------------------
   §3  Explicit clearances.
   --------------------------------------------------------------------------- *)

(* The carrier itself: any positive offset misses it. *)
Lemma corridor_avoid_carrier : forall (e : Edge) (delta : R) (y : R),
  py (fst e) <> py (snd e) ->
  0 < delta ->
  ~ (exists s : R, 0 <= s <= 1 /\
       edge_x_at e y - delta = (1 - s) * px (fst e) + s * px (snd e) /\
       y = (1 - s) * py (fst e) + s * py (snd e)).
Proof.
  intros e delta y Hnh Hd [s [Hs [Hx Hy]]].
  rewrite <- (on_carrier_x e s Hnh) in Hx.
  rewrite <- Hy in Hx. lra.
Qed.

(* An edge whose endpoints are both strictly WEST of the carrier line by more
   than delta misses the corridor (affine sign propagation). *)
Lemma corridor_avoid_west : forall (e f : Edge) (delta : R) (y : R),
  py (fst e) <> py (snd e) ->
  px (fst f) + delta < edge_x_at e (py (fst f)) ->
  px (snd f) + delta < edge_x_at e (py (snd f)) ->
  ~ (exists s : R, 0 <= s <= 1 /\
       edge_x_at e y - delta = (1 - s) * px (fst f) + s * px (snd f) /\
       y = (1 - s) * py (fst f) + s * py (snd f)).
Proof.
  intros e f delta y Hnh Hwa Hwb [s [Hs [Hx Hy]]].
  destruct e as [a b]; cbn [fst snd] in *.
  unfold edge_x_at in *.
  set (al := (px b - px a) / (py b - py a)) in *.
  assert (Hlin : forall z : R,
            px a + (px b - px a) * (z - py a) / (py b - py a)
              = al * z + (px a - al * py a))
    by (intro z; unfold al; field; lra).
  rewrite Hlin in Hx, Hwa, Hwb.
  rewrite Hy in Hx.
  destruct (Rle_or_lt 1 s) as [Hs1 | Hs1].
  - nra.
  - assert (H1 : (1 - s) * (px (fst f) + delta)
                   < (1 - s) * (al * py (fst f) + (px a - al * py a))) by nra.
    assert (H2 : s * (px (snd f) + delta)
                   <= s * (al * py (snd f) + (px a - al * py a))) by nra.
    nra.
Qed.

(* An edge whose endpoints are both strictly EAST of the carrier line misses
   every westward corridor. *)
Lemma corridor_avoid_east : forall (e f : Edge) (delta : R) (y : R),
  py (fst e) <> py (snd e) ->
  0 < delta ->
  edge_x_at e (py (fst f)) < px (fst f) ->
  edge_x_at e (py (snd f)) < px (snd f) ->
  ~ (exists s : R, 0 <= s <= 1 /\
       edge_x_at e y - delta = (1 - s) * px (fst f) + s * px (snd f) /\
       y = (1 - s) * py (fst f) + s * py (snd f)).
Proof.
  intros e f delta y Hnh Hd Hea Heb [s [Hs [Hx Hy]]].
  destruct e as [a b]; cbn [fst snd] in *.
  unfold edge_x_at in *.
  set (al := (px b - px a) / (py b - py a)) in *.
  assert (Hlin : forall z : R,
            px a + (px b - px a) * (z - py a) / (py b - py a)
              = al * z + (px a - al * py a))
    by (intro z; unfold al; field; lra).
  rewrite Hlin in Hx, Hea, Heb.
  rewrite Hy in Hx.
  assert (H1 : (1 - s) * (al * py (fst f) + (px a - al * py a))
                 <= (1 - s) * px (fst f)) by nra.
  assert (H2 : s * (al * py (snd f) + (px a - al * py a))
                 <= s * px (snd f)) by nra.
  nra.
Qed.

(* Edges entirely below or above the height window are missed. *)
Lemma corridor_avoid_below : forall (e f : Edge) (delta ylo yhi y : R),
  ylo <= y <= yhi ->
  py (fst f) < ylo -> py (snd f) < ylo ->
  ~ (exists s : R, 0 <= s <= 1 /\
       edge_x_at e y - delta = (1 - s) * px (fst f) + s * px (snd f) /\
       y = (1 - s) * py (fst f) + s * py (snd f)).
Proof.
  intros e f delta ylo yhi y Hw Ha Hb [s [[Hs1 Hs2] [Hx Hy]]].
  assert (T1 : 0 <= (1 - s) * (ylo - py (fst f))) by nra.
  assert (T2 : 0 <= s * (ylo - py (snd f))) by nra.
  destruct (Rle_or_lt 1 s); nra.
Qed.

Lemma corridor_avoid_above : forall (e f : Edge) (delta ylo yhi y : R),
  ylo <= y <= yhi ->
  yhi < py (fst f) -> yhi < py (snd f) ->
  ~ (exists s : R, 0 <= s <= 1 /\
       edge_x_at e y - delta = (1 - s) * px (fst f) + s * px (snd f) /\
       y = (1 - s) * py (fst f) + s * py (snd f)).
Proof.
  intros e f delta ylo yhi y Hw Ha Hb [s [[Hs1 Hs2] [Hx Hy]]].
  assert (T1 : 0 <= (1 - s) * (py (fst f) - yhi)) by nra.
  assert (T2 : 0 <= s * (py (snd f) - yhi)) by nra.
  destruct (Rle_or_lt 1 s); nra.
Qed.

(* ---------------------------------------------------------------------------
   §4  Parking heights: an explicit vertex-level-free gap above any height.
   --------------------------------------------------------------------------- *)

Fixpoint level_gap (y0 : R) (l : list Point) : R :=
  match l with
  | [] => 1
  | v :: l' =>
      if Rle_dec (py v) y0 then level_gap y0 l'
      else Rmin (py v - y0) (level_gap y0 l')
  end.

Lemma level_gap_pos : forall (y0 : R) (l : list Point), 0 < level_gap y0 l.
Proof.
  intros y0; induction l as [| v l' IH]; cbn [level_gap]; [ lra | ].
  destruct (Rle_dec (py v) y0); [ exact IH | apply Rmin_glb_lt; lra ].
Qed.

Lemma level_gap_spec : forall (y0 : R) (l : list Point) (v : Point),
  In v l -> py v <= y0 \/ y0 + level_gap y0 l <= py v.
Proof.
  intros y0; induction l as [| w l' IH]; intros v Hin; [ contradiction | ].
  cbn [level_gap].
  destruct Hin as [He | Hin].
  - subst w. destruct (Rle_dec (py v) y0) as [Hle | Hgt].
    + left; exact Hle.
    + right. pose proof (Rmin_l (py v - y0) (level_gap y0 l')). lra.
  - destruct (Rle_dec (py w) y0) as [Hle | Hgt].
    + exact (IH v Hin).
    + destruct (IH v Hin) as [H | H]; [ left; exact H | right ].
      pose proof (Rmin_r (py w - y0) (level_gap y0 l')). lra.
Qed.

(* A height inside the gap carries no vertex level at all, hence the guard. *)
Lemma guard_of_fresh_level : forall (r : Ring) (q : Point) (y0 : R),
  y0 < py q -> py q < y0 + level_gap y0 r ->
  ray_avoids_vertices q r.
Proof.
  intros r q y0 H1 H2 v Hv [Heq _].
  destruct (level_gap_spec y0 r v Hv) as [H | H]; lra.
Qed.

(* ---------------------------------------------------------------------------
   §5  Worked instance: a corridor inside the unit square.
   --------------------------------------------------------------------------- *)

Example square_corridor :
  connected_in_complement_cont (rect_ring 0 0 1 1)
    (mkPoint (1 / 2) (3 / 4)) (mkPoint (1 / 2) (1 / 4)).
Proof.
  set (e1 := (mkPoint 1 0, mkPoint 1 1)).
  assert (Hnh : py (fst e1) <> py (snd e1)) by (cbn; lra).
  assert (Hx1 : forall y : R, edge_x_at e1 y = 1)
    by (intro y; unfold e1, edge_x_at; cbn [px py fst snd]; field; lra).
  assert (Hc34 : corridor e1 (1 / 2) (3 / 4) = mkPoint (1 / 2) (3 / 4))
    by (unfold corridor; rewrite Hx1; f_equal; lra).
  assert (Hc14 : corridor e1 (1 / 2) (1 / 4) = mkPoint (1 / 2) (1 / 4))
    by (unfold corridor; rewrite Hx1; f_equal; lra).
  rewrite <- Hc34, <- Hc14.
  apply (corridor_connected (rect_ring 0 0 1 1) e1 (1 / 4) (3 / 4) (1 / 2));
    [ exact Hnh | lra | ].
  apply corridor_free_of_edges.
  intros f Hin y Hw.
  rewrite ring_edges_rect in Hin. cbn [In] in Hin.
  destruct Hin as [Hf | [Hf | [Hf | [Hf | []]]]]; subst f.
  - (* bottom edge, entirely below the window *)
    apply (corridor_avoid_below e1 _ (1 / 2) (1 / 4) (3 / 4) y Hw);
      cbn [px py fst snd]; lra.
  - (* right edge: the carrier itself *)
    apply (corridor_avoid_carrier e1 (1 / 2) y Hnh). lra.
  - (* top edge, entirely above the window *)
    apply (corridor_avoid_above e1 _ (1 / 2) (1 / 4) (3 / 4) y Hw);
      cbn [px py fst snd]; lra.
  - (* left edge, strictly west of the carrier line by more than delta *)
    apply (corridor_avoid_west e1 _ (1 / 2) y Hnh);
      cbn [px py fst snd]; rewrite Hx1; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions corridor_connected.
Print Assumptions corridor_avoid_west.
Print Assumptions guard_of_fresh_level.
Print Assumptions square_corridor.
