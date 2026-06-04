(* ============================================================================
   NetTopologySuite.Proofs.RingArea979
   ----------------------------------------------------------------------------
   Mathematical grounding for JTS#979 ("Geometry.buffer with a fixed
   PrecisionModel removes a hole"): the precision-collapse mechanism, certified.

   The root cause of #979 is NOT the buffer distance and NOT the noder -- it is
   precision reduction.  Snapping a hole-ring's vertices to a fixed grid of
   spacing `1/scale` (JTS `PrecisionModel.makePrecise`) collapses any hole that
   is small relative to the grid: its signed area degenerates to exactly zero,
   so the hole vanishes and buffer drops it.

   The oracle's `HOLE_PRECISION_AUDIT` / `HOLES_SURVIVE_PRECISION` modes
   (oracle/driver.ml) compute the EXACT (zarith Q) signed area of a ring before
   and after precision reduction and flag a #979 collapse when the area drops to
   zero.  That hand-rolled criterion was asserted as "exact ground truth"; this
   file supplies the Coq theorem behind it.

   The headline is a QUANTIZATION fact: after snapping to a grid of spacing
   `1/scale`, twice the signed area of the ring is an integer multiple of
   `1/scale^2`.  Two consequences follow immediately:

     - (`snap_area_zero_or_large`) the snapped area is either exactly zero or at
       least `1/scale^2` in magnitude -- there is no continuum of "small" snapped
       holes; and

     - (`hole_below_grid_resolution_collapses`) any ring whose snapped twice-area
       has magnitude below one grid cell (`< 1/scale^2`) has area EXACTLY zero.
       So a sub-grid hole is removed outright, never merely shrunk -- exactly the
       #979 mechanism, and the soundness witness the oracle's "REMOVED" verdict
       relies on.

   The development is rounding-mode agnostic: the snap is parameterised by an
   arbitrary `rnd : R -> Z`, so it covers both Coq's round-half-to-even
   (`snap_round_coord` in HotPixel_b64.v, `rnd := round_mode mode_NE`) and the
   oracle's round-half-up.  It builds on the existing orientation theory: the
   triangle case reduces to `Orientation.cross` (so #979 collapse for a
   triangular hole is exactly the snapped vertices going collinear).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.8)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import ZArith.
Import ListNotations.
From NTS.Proofs Require Import Distance Orientation Triangle.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Shoelace signed area of a ring given as a list of vertices.                *)
(*                                                                            *)
(* `edge_cross p q` is the cross term `px p * py q - px q * py p` for the     *)
(* directed edge p -> q (twice the signed area swept from the origin).        *)
(* `shoelace_open` sums it over consecutive pairs WITHOUT wrap-around;        *)
(* `signed_area2` closes the ring by appending the first vertex, matching the *)
(* oracle's `ring_area2` (which uses the cyclic successor `(i+1) mod n`).     *)
(* -------------------------------------------------------------------------- *)

Definition edge_cross (p q : Point) : R := px p * py q - px q * py p.

Fixpoint shoelace_open (l : list Point) : R :=
  match l with
  | p :: ((q :: _) as t) => edge_cross p q + shoelace_open t
  | _ => 0
  end.

Definition signed_area2 (l : list Point) : R :=
  match l with
  | [] => 0
  | p0 :: _ => shoelace_open (l ++ [p0])
  end.

(* Definitional stepping lemmas (control reduction without fragile `simpl`). *)
Lemma shoelace_open_cons2 : forall p q r,
  shoelace_open (p :: q :: r) = edge_cross p q + shoelace_open (q :: r).
Proof. reflexivity. Qed.

Lemma shoelace_open_nil : shoelace_open [] = 0.
Proof. reflexivity. Qed.

Lemma shoelace_open_single : forall p, shoelace_open [p] = 0.
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Triangle bridge: the closed three-vertex ring's signed twice-area is the   *)
(* orientation cross product.  Ties #979 collapse to the existing orientation *)
(* theory -- a triangular hole collapses exactly when its (snapped) vertices  *)
(* go collinear (`cross = 0`).                                                 *)
(* -------------------------------------------------------------------------- *)

Lemma signed_area2_triangle : forall A B C : Point,
  signed_area2 [A; B; C] = cross A B C.
Proof.
  intros A B C. unfold signed_area2, cross, edge_cross. cbn [app].
  rewrite !shoelace_open_cons2, shoelace_open_single.
  unfold edge_cross. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Grid snap (precision reduction).  `snap_coord rnd scale x = rnd(x*scale)/  *)
(* scale` sends a coordinate to the grid of spacing `1/scale`; `snap_pt`      *)
(* snaps both coordinates of a point.  Parameterised by `rnd : R -> Z` so it  *)
(* models any rounding mode (round-half-even, round-half-up, truncate, ...).  *)
(* -------------------------------------------------------------------------- *)

Definition snap_coord (rnd : R -> Z) (scale : R) (x : R) : R :=
  IZR (rnd (x * scale)) / scale.

Definition snap_pt (rnd : R -> Z) (scale : R) (P : Point) : Point :=
  mkPoint (snap_coord rnd scale (px P)) (snap_coord rnd scale (py P)).

(* Each snapped edge term is an integer over `scale^2`. *)
Lemma edge_cross_snap_IZR :
  forall (rnd : R -> Z) (scale : R) (p q : Point), scale <> 0 ->
    edge_cross (snap_pt rnd scale p) (snap_pt rnd scale q)
    = IZR (rnd (px p * scale) * rnd (py q * scale)
           - rnd (px q * scale) * rnd (py p * scale))
      / (scale * scale).
Proof.
  intros rnd scale p q Hs.
  unfold edge_cross, snap_pt, snap_coord, px, py.
  rewrite minus_IZR, !mult_IZR. field. exact Hs.
Qed.

(* -------------------------------------------------------------------------- *)
(* Headline quantization (open shoelace): a snapped vertex list's shoelace    *)
(* sum is an integer multiple of `1/scale^2`.                                  *)
(* -------------------------------------------------------------------------- *)

Lemma shoelace_open_snap_quantized :
  forall (rnd : R -> Z) (scale : R), scale <> 0 ->
  forall l : list Point,
    exists K : Z,
      shoelace_open (map (snap_pt rnd scale) l) = IZR K / (scale * scale).
Proof.
  intros rnd scale Hs.
  induction l as [| p l' IH].
  - exists 0%Z. cbn [map]. rewrite shoelace_open_nil. simpl IZR.
    unfold Rdiv. rewrite Rmult_0_l. reflexivity.
  - destruct l' as [| q t].
    + exists 0%Z. cbn [map]. rewrite shoelace_open_single. simpl IZR.
      unfold Rdiv. rewrite Rmult_0_l. reflexivity.
    + (* l = p :: q :: t.  map distributes; step the shoelace once. *)
      destruct IH as [K' HK'].
      cbn [map]. rewrite shoelace_open_cons2.
      change (snap_pt rnd scale q :: map (snap_pt rnd scale) t)
        with (map (snap_pt rnd scale) (q :: t)).
      rewrite HK'.
      rewrite edge_cross_snap_IZR by exact Hs.
      set (e := (rnd (px p * scale)%R * rnd (py q * scale)%R
                 - rnd (px q * scale)%R * rnd (py p * scale)%R)%Z).
      exists (e + K')%Z.
      rewrite plus_IZR. field; exact Hs.
Qed.

(* -------------------------------------------------------------------------- *)
(* Quantization for the closed ring.                                           *)
(* -------------------------------------------------------------------------- *)

Theorem signed_area2_snap_quantized :
  forall (rnd : R -> Z) (scale : R), scale <> 0 ->
  forall l : list Point,
    exists K : Z,
      signed_area2 (map (snap_pt rnd scale) l) = IZR K / (scale * scale).
Proof.
  intros rnd scale Hs [| p0 l].
  - exists 0%Z. unfold signed_area2. simpl IZR.
    unfold Rdiv. rewrite Rmult_0_l. reflexivity.
  - unfold signed_area2. cbn [map].
    rewrite <- (map_cons (snap_pt rnd scale) p0 l).
    change [snap_pt rnd scale p0] with (map (snap_pt rnd scale) [p0]).
    rewrite <- map_app.
    apply shoelace_open_snap_quantized. exact Hs.
Qed.

(* -------------------------------------------------------------------------- *)
(* Consequence 1: the snapped twice-area is zero or at least one grid cell.    *)
(* No snapped ring has area strictly between 0 and `1/scale^2`.                *)
(* -------------------------------------------------------------------------- *)

Theorem snap_area_zero_or_large :
  forall (rnd : R -> Z) (scale : R), 0 < scale ->
  forall l : list Point,
    signed_area2 (map (snap_pt rnd scale) l) = 0
    \/ 1 / (scale * scale) <= Rabs (signed_area2 (map (snap_pt rnd scale) l)).
Proof.
  intros rnd scale Hpos l.
  assert (Hs : scale <> 0) by lra.
  assert (Hsc2 : 0 < scale * scale) by (apply Rmult_lt_0_compat; lra).
  destruct (signed_area2_snap_quantized rnd scale Hs l) as [K HK].
  rewrite HK.
  destruct (Z.eq_dec K 0) as [-> | Hnz].
  - left. simpl IZR. field. lra.
  - right.
    assert (H1 : 1 <= Rabs (IZR K)).
    { rewrite <- abs_IZR.
      replace 1 with (IZR 1) by (simpl; reflexivity).
      apply IZR_le. lia. }
    unfold Rdiv. rewrite Rabs_mult.
    rewrite (Rabs_pos_eq (/ (scale * scale)))
      by (apply Rlt_le, Rinv_0_lt_compat; exact Hsc2).
    apply (Rmult_le_compat_r (/ (scale * scale))) in H1;
      [| apply Rlt_le, Rinv_0_lt_compat; exact Hsc2].
    rewrite Rmult_1_l in H1. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Consequence 2 (the certified #979 mechanism): any snapped ring whose        *)
(* twice-area has magnitude below one grid cell is EXACTLY zero.  A hole       *)
(* smaller than the grid resolution is removed outright, not shrunk -- this is *)
(* the soundness witness behind the oracle's "REMOVED" verdict.                *)
(* -------------------------------------------------------------------------- *)

Theorem hole_below_grid_resolution_collapses :
  forall (rnd : R -> Z) (scale : R), 0 < scale ->
  forall l : list Point,
    Rabs (signed_area2 (map (snap_pt rnd scale) l)) < 1 / (scale * scale) ->
    signed_area2 (map (snap_pt rnd scale) l) = 0.
Proof.
  intros rnd scale Hpos l Hlt.
  destruct (snap_area_zero_or_large rnd scale Hpos l) as [Hz | Hge].
  - exact Hz.
  - exfalso. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Triangle corollary: a snapped triangular hole's collapse is exactly its     *)
(* snapped vertices going collinear (`cross = 0`).  Connects the #979          *)
(* mechanism to the orientation predicate, as #66 anticipates.                 *)
(* -------------------------------------------------------------------------- *)

Corollary snapped_triangle_area_is_cross :
  forall (rnd : R -> Z) (scale : R) (A B C : Point),
    signed_area2 (map (snap_pt rnd scale) [A; B; C])
    = cross (snap_pt rnd scale A) (snap_pt rnd scale B) (snap_pt rnd scale C).
Proof.
  intros rnd scale A B C. cbn [map]. apply signed_area2_triangle.
Qed.

(* ============================================================================
   Multi-ring hole-count layer (oracle `HOLES_SURVIVE_PRECISION`).
   ----------------------------------------------------------------------------
   A polygon carries a list of interior rings (holes).  The oracle's
   `HOLES_SURVIVE_PRECISION` mode reports "survived s of k": how many of the k
   input holes still have nonzero snapped area.  The #979 count signature is
   `s < k` -- precision reduction dropped at least one hole.

   This layer certifies that signature.  A ring `survives` iff its snapped
   twice-area is nonzero; it is `subgrid` iff that area sits below one grid
   cell.  Single-ring `hole_below_grid_resolution_collapses` lifts to:
     - every hole sub-grid  =>  ALL holes removed (`all_subgrid_holes_removed`);
     - some hole sub-grid   =>  some hole removed (`some_subgrid_hole_removed`);
     - and at the count level, one sub-grid hole forces `survived < k`
       (`survived_count_lt_of_subgrid`).
   ========================================================================== *)

Definition hole_survives (rnd : R -> Z) (scale : R) (ring : list Point) : Prop :=
  signed_area2 (map (snap_pt rnd scale) ring) <> 0.

Definition subgrid_ring (rnd : R -> Z) (scale : R) (ring : list Point) : Prop :=
  Rabs (signed_area2 (map (snap_pt rnd scale) ring)) < 1 / (scale * scale).

(* A sub-grid hole does not survive precision reduction. *)
Lemma subgrid_ring_removed :
  forall (rnd : R -> Z) (scale : R), 0 < scale ->
  forall ring : list Point,
    subgrid_ring rnd scale ring -> ~ hole_survives rnd scale ring.
Proof.
  intros rnd scale Hpos ring Hsub Hsurv.
  apply Hsurv. apply hole_below_grid_resolution_collapses; assumption.
Qed.

(* Every hole sub-grid => the polygon loses ALL its holes. *)
Theorem all_subgrid_holes_removed :
  forall (rnd : R -> Z) (scale : R), 0 < scale ->
  forall holes : list (list Point),
    Forall (subgrid_ring rnd scale) holes ->
    Forall (fun r => ~ hole_survives rnd scale r) holes.
Proof.
  intros rnd scale Hpos holes.
  apply Forall_impl. intros ring. apply subgrid_ring_removed. exact Hpos.
Qed.

(* The #979 signature, qualitative form: at least one sub-grid hole means at
   least one hole is removed. *)
Theorem some_subgrid_hole_removed :
  forall (rnd : R -> Z) (scale : R), 0 < scale ->
  forall holes : list (list Point),
    Exists (subgrid_ring rnd scale) holes ->
    Exists (fun r => ~ hole_survives rnd scale r) holes.
Proof.
  intros rnd scale Hpos holes HEx.
  apply Exists_exists in HEx. destruct HEx as [ring [Hin Hsub]].
  apply Exists_exists. exists ring. split; [exact Hin |].
  apply subgrid_ring_removed; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Count form.  Decide survival via the reals' total order (`Req_EM_T`), count *)
(* the survivors, and show one sub-grid hole forces `survived < length holes`. *)
(* -------------------------------------------------------------------------- *)

Definition survives_b (rnd : R -> Z) (scale : R) (ring : list Point) : bool :=
  if Req_EM_T (signed_area2 (map (snap_pt rnd scale) ring)) 0 then false else true.

Lemma survives_b_true_iff :
  forall (rnd : R -> Z) (scale : R) (ring : list Point),
    survives_b rnd scale ring = true <-> hole_survives rnd scale ring.
Proof.
  intros rnd scale ring. unfold survives_b, hole_survives.
  destruct (Req_EM_T (signed_area2 (map (snap_pt rnd scale) ring)) 0) as [He | Hne].
  - split; [discriminate | intro H; contradiction].
  - split; [intros _; exact Hne | reflexivity].
Qed.

Definition survived_count (rnd : R -> Z) (scale : R)
    (holes : list (list Point)) : nat :=
  length (filter (survives_b rnd scale) holes).

(* Generic list facts about filter length. *)
Lemma length_filter_le :
  forall (A : Type) (f : A -> bool) (l : list A),
    (length (filter f l) <= length l)%nat.
Proof.
  intros A f l. induction l as [| a l IH]; simpl; [lia |].
  destruct (f a); simpl; lia.
Qed.

Lemma length_filter_lt :
  forall (A : Type) (f : A -> bool) (l : list A) (x : A),
    In x l -> f x = false -> (length (filter f l) < length l)%nat.
Proof.
  intros A f l x. induction l as [| a l IH]; simpl; [contradiction |].
  intros Hin Hfx. destruct (f a) eqn:Hfa; simpl.
  - destruct Hin as [Heq | Hin].
    + subst a. congruence.
    + specialize (IH Hin Hfx). lia.
  - pose proof (length_filter_le _ f l). lia.
Qed.

Theorem survived_count_le :
  forall (rnd : R -> Z) (scale : R) (holes : list (list Point)),
    (survived_count rnd scale holes <= length holes)%nat.
Proof.
  intros. unfold survived_count. apply length_filter_le.
Qed.

(* The #979 count signature: a single sub-grid hole forces fewer survivors than
   input holes (`survived < k`). *)
Theorem survived_count_lt_of_subgrid :
  forall (rnd : R -> Z) (scale : R), 0 < scale ->
  forall (holes : list (list Point)) (ring : list Point),
    In ring holes -> subgrid_ring rnd scale ring ->
    (survived_count rnd scale holes < length holes)%nat.
Proof.
  intros rnd scale Hpos holes ring Hin Hsub.
  assert (Hf : survives_b rnd scale ring = false).
  { destruct (survives_b rnd scale ring) eqn:E; [| reflexivity].
    exfalso. apply (subgrid_ring_removed rnd scale Hpos ring Hsub).
    apply survives_b_true_iff. exact E. }
  unfold survived_count.
  apply (length_filter_lt _ (survives_b rnd scale) holes ring Hin Hf).
Qed.

(* ============================================================================
   True-area layer: the snapping error bound and the collapse reduction.
   ----------------------------------------------------------------------------
   The collapse theorems above are stated on the SNAPPED twice-area (what the
   oracle actually computes).  To connect them to the TRUE hole -- a hole that
   was real before precision reduction -- we need to know how far snapping can
   move things.  For a round-to-nearest `rnd` the answer is the classic bound:
   each coordinate moves by at most half a grid cell, `1/(2*scale)`.

   `collapse_of_small_true_area` then reduces #979 to an area-perturbation
   bound: if the true twice-area plus the area perturbation introduced by
   snapping together stay below one grid cell, the hole collapses to exactly
   zero.  Bounding that perturbation by the per-coordinate error
   `snap_coord_close` and the vertex magnitudes (an O(n * M / scale) estimate)
   is the next slice; this slice supplies the per-coordinate bound and the
   reduction it feeds.

   `rounds_to_nearest` is satisfied by both rounding modes that matter here:
   Coq/Flocq's round-half-to-even (`round_mode mode_NE`, the `snap_round_coord`
   used across the binary64 layer) and the oracle's round-half-up.
   ========================================================================== *)

Definition rounds_to_nearest (rnd : R -> Z) : Prop :=
  forall y : R, Rabs (IZR (rnd y) - y) <= / 2.

(* Each snapped coordinate is within half a grid cell of the original. *)
Lemma snap_coord_close :
  forall (rnd : R -> Z) (scale : R),
    rounds_to_nearest rnd -> 0 < scale ->
    forall x : R, Rabs (snap_coord rnd scale x - x) <= / (2 * scale).
Proof.
  intros rnd scale Hrn Hpos x. unfold snap_coord.
  assert (Hs : scale <> 0) by lra.
  replace (IZR (rnd (x * scale)) / scale - x)
    with ((IZR (rnd (x * scale)) - x * scale) * / scale) by (field; exact Hs).
  rewrite Rabs_mult.
  rewrite (Rabs_pos_eq (/ scale)) by (apply Rlt_le, Rinv_0_lt_compat; lra).
  replace (/ (2 * scale)) with (/ 2 * / scale) by (field; exact Hs).
  apply Rmult_le_compat_r.
  - apply Rlt_le, Rinv_0_lt_compat; lra.
  - apply Hrn.
Qed.

(* Point-level: snapping moves each axis of a vertex by at most 1/(2*scale). *)
Lemma snap_pt_close_x :
  forall (rnd : R -> Z) (scale : R),
    rounds_to_nearest rnd -> 0 < scale ->
    forall P : Point,
      Rabs (px (snap_pt rnd scale P) - px P) <= / (2 * scale).
Proof.
  intros rnd scale Hrn Hpos P. unfold snap_pt, px.
  apply snap_coord_close; assumption.
Qed.

Lemma snap_pt_close_y :
  forall (rnd : R -> Z) (scale : R),
    rounds_to_nearest rnd -> 0 < scale ->
    forall P : Point,
      Rabs (py (snap_pt rnd scale P) - py P) <= / (2 * scale).
Proof.
  intros rnd scale Hrn Hpos P. unfold snap_pt, py.
  apply snap_coord_close; assumption.
Qed.

(* Reduction: if the true twice-area plus the snapping-induced area            *)
(* perturbation stay below one grid cell, the snapped hole is exactly zero --  *)
(* removed, not shrunk.  This is the true-area form of the #979 mechanism; it  *)
(* turns any area-perturbation bound into a guaranteed-collapse criterion.     *)
Theorem collapse_of_small_true_area :
  forall (rnd : R -> Z) (scale : R), 0 < scale ->
  forall l : list Point,
    Rabs (signed_area2 (map (snap_pt rnd scale) l) - signed_area2 l)
      + Rabs (signed_area2 l) < 1 / (scale * scale) ->
    signed_area2 (map (snap_pt rnd scale) l) = 0.
Proof.
  intros rnd scale Hpos l Hsum.
  apply (hole_below_grid_resolution_collapses rnd scale Hpos l).
  pose proof (Rabs_triang_inv (signed_area2 (map (snap_pt rnd scale) l))
                              (signed_area2 l)) as Hti.
  lra.
Qed.

(* ============================================================================
   Area-perturbation bound: from per-coordinate snap error to a guaranteed
   true-hole collapse.
   ----------------------------------------------------------------------------
   `collapse_of_small_true_area` reduces #979 to bounding how much snapping
   perturbs the ring area.  This section proves that bound for a general ring:
   if every vertex has magnitude <= M, snapping (each coordinate moved by
   <= delta) changes twice the signed area by at most
   `INR (n+1) * 2*(2M+delta)*delta` for an n-vertex ring.  Composing with the
   half-cell coordinate bound `snap_coord_close` (delta = 1/(2*scale)) yields a
   closed criterion `hole_collapses_of_small_true_ring`: a bounded ring whose
   TRUE area is small enough relative to the grid collapses to exactly zero.
   ========================================================================== *)

(* |x * y| <= a * b from coordinate bounds. *)
Lemma Rabs_mult_le :
  forall x y a b : R, Rabs x <= a -> Rabs y <= b -> Rabs (x * y) <= a * b.
Proof.
  intros x y a b Hx Hy. rewrite Rabs_mult.
  apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hx | exact Hy].
Qed.

(* Four-term triangle inequality. *)
Lemma Rabs_sum4 :
  forall a b c d : R, Rabs (a + b + c + d) <= Rabs a + Rabs b + Rabs c + Rabs d.
Proof.
  intros a b c d.
  eapply Rle_trans; [apply Rabs_triang|].
  apply Rplus_le_compat; [| apply Rle_refl].
  eapply Rle_trans; [apply Rabs_triang|].
  apply Rplus_le_compat; [| apply Rle_refl].
  apply Rabs_triang.
Qed.

(* Per-edge perturbation: snapping the two endpoints (each coordinate within   *)
(* delta) changes one shoelace edge term by at most 2*(2M+delta)*delta.        *)
Lemma edge_cross_perturb_bound :
  forall (M delta : R) (p q p' q' : Point),
    0 <= M -> 0 <= delta ->
    Rabs (px p) <= M -> Rabs (py p) <= M ->
    Rabs (px q) <= M -> Rabs (py q) <= M ->
    Rabs (px p' - px p) <= delta -> Rabs (py p' - py p) <= delta ->
    Rabs (px q' - px q) <= delta -> Rabs (py q' - py q) <= delta ->
    Rabs (edge_cross p' q' - edge_cross p q) <= 2 * (2 * M + delta) * delta.
Proof.
  intros M delta p q p' q' HM Hd Hpx Hpy Hqx Hqy Hp'x Hp'y Hq'x Hq'y.
  assert (Hp'xM : Rabs (px p') <= M + delta).
  { replace (px p') with (px p + (px p' - px p)) by ring.
    eapply Rle_trans; [apply Rabs_triang|]. lra. }
  assert (Hq'xM : Rabs (px q') <= M + delta).
  { replace (px q') with (px q + (px q' - px q)) by ring.
    eapply Rle_trans; [apply Rabs_triang|]. lra. }
  assert (Hsplit : edge_cross p' q' - edge_cross p q
    = px p' * (py q' - py q) + py q * (px p' - px p)
      + (- (px q' * (py p' - py p))) + (- (py p * (px q' - px q)))).
  { unfold edge_cross. ring. }
  rewrite Hsplit.
  eapply Rle_trans; [apply Rabs_sum4|].
  rewrite !Rabs_Ropp.
  assert (Hb1a : Rabs (px p' * (py q' - py q)) <= (M + delta) * delta)
    by (apply Rabs_mult_le; assumption).
  assert (Hb1b : Rabs (py q * (px p' - px p)) <= M * delta)
    by (apply Rabs_mult_le; assumption).
  assert (Hb2a : Rabs (px q' * (py p' - py p)) <= (M + delta) * delta)
    by (apply Rabs_mult_le; assumption).
  assert (Hb2b : Rabs (py p * (px q' - px q)) <= M * delta)
    by (apply Rabs_mult_le; assumption).
  assert (Harith :
    (M + delta) * delta + M * delta + (M + delta) * delta + M * delta
    = 2 * (2 * M + delta) * delta) by ring.
  lra.
Qed.

(* Assembly over the shoelace list: bound by (number of vertices) edge bounds.  *)
Lemma shoelace_open_perturb_bound :
  forall (rnd : R -> Z) (scale M delta : R),
    0 <= M -> 0 <= delta ->
    (forall P, Rabs (px (snap_pt rnd scale P) - px P) <= delta) ->
    (forall P, Rabs (py (snap_pt rnd scale P) - py P) <= delta) ->
    forall L : list Point,
      Forall (fun P => Rabs (px P) <= M /\ Rabs (py P) <= M) L ->
      Rabs (shoelace_open (map (snap_pt rnd scale) L) - shoelace_open L)
        <= INR (length L) * (2 * (2 * M + delta) * delta).
Proof.
  intros rnd scale M delta HM Hd Hcx Hcy.
  set (B := 2 * (2 * M + delta) * delta).
  assert (HB : 0 <= B) by (unfold B; nra).
  intros L. induction L as [| p L' IH]; intros HF.
  - cbn [map length]. rewrite shoelace_open_nil.
    replace (0 - 0) with 0 by ring. rewrite Rabs_R0.
    simpl INR. rewrite Rmult_0_l. lra.
  - destruct L' as [| q t].
    + cbn [map length]. rewrite !shoelace_open_single.
      replace (0 - 0) with 0 by ring. rewrite Rabs_R0.
      simpl INR. rewrite Rmult_1_l. exact HB.
    + pose proof (Forall_inv HF) as HFp.
      pose proof (Forall_inv_tail HF) as HFt.
      pose proof (Forall_inv HFt) as HFq.
      specialize (IH HFt).
      cbn [map].
      rewrite (shoelace_open_cons2 (snap_pt rnd scale p) (snap_pt rnd scale q)
                 (map (snap_pt rnd scale) t)).
      rewrite (shoelace_open_cons2 p q t).
      change (snap_pt rnd scale q :: map (snap_pt rnd scale) t)
        with (map (snap_pt rnd scale) (q :: t)).
      set (ed := edge_cross (snap_pt rnd scale p) (snap_pt rnd scale q)
                 - edge_cross p q).
      set (re := shoelace_open (map (snap_pt rnd scale) (q :: t))
                 - shoelace_open (q :: t)).
      replace (edge_cross (snap_pt rnd scale p) (snap_pt rnd scale q)
                + shoelace_open (map (snap_pt rnd scale) (q :: t))
               - (edge_cross p q + shoelace_open (q :: t)))
        with (ed + re) by (unfold ed, re; ring).
      eapply Rle_trans; [apply Rabs_triang|].
      assert (He : Rabs ed <= B).
      { unfold ed, B. apply edge_cross_perturb_bound.
        - exact HM.
        - exact Hd.
        - exact (proj1 HFp).
        - exact (proj2 HFp).
        - exact (proj1 HFq).
        - exact (proj2 HFq).
        - apply Hcx.
        - apply Hcy.
        - apply Hcx.
        - apply Hcy. }
      set (m := length (q :: t)).
      apply Rle_trans with (B + INR m * B).
      * apply Rplus_le_compat; [exact He | exact IH].
      * change (length (p :: q :: t)) with (S m). rewrite S_INR.
        apply Req_le; ring.
Qed.

(* Closed ring: bound by INR (n+1) edge bounds (n = vertex count). *)
Theorem signed_area2_perturb_bound :
  forall (rnd : R -> Z) (scale M delta : R),
    0 <= M -> 0 <= delta ->
    (forall P, Rabs (px (snap_pt rnd scale P) - px P) <= delta) ->
    (forall P, Rabs (py (snap_pt rnd scale P) - py P) <= delta) ->
    forall l : list Point,
      Forall (fun P => Rabs (px P) <= M /\ Rabs (py P) <= M) l ->
      Rabs (signed_area2 (map (snap_pt rnd scale) l) - signed_area2 l)
        <= INR (length l + 1) * (2 * (2 * M + delta) * delta).
Proof.
  intros rnd scale M delta HM Hd Hcx Hcy l HF.
  destruct l as [| p0 l'].
  - cbn [map signed_area2].
    replace (0 - 0) with 0 by ring. rewrite Rabs_R0.
    apply Rmult_le_pos; [apply pos_INR | nra].
  - set (L := (p0 :: l') ++ [p0]).
    assert (Harea_snap : signed_area2 (map (snap_pt rnd scale) (p0 :: l'))
                         = shoelace_open (map (snap_pt rnd scale) L)).
    { unfold signed_area2, L. cbn [map].
      rewrite <- (map_cons (snap_pt rnd scale) p0 l').
      change [snap_pt rnd scale p0] with (map (snap_pt rnd scale) [p0]).
      rewrite <- map_app. reflexivity. }
    assert (Harea : signed_area2 (p0 :: l') = shoelace_open L).
    { unfold signed_area2, L. reflexivity. }
    rewrite Harea_snap, Harea.
    replace (length (p0 :: l') + 1)%nat with (length L)
      by (unfold L; rewrite length_app; simpl; lia).
    apply shoelace_open_perturb_bound; try assumption.
    unfold L. rewrite Forall_app. split.
    + exact HF.
    + constructor; [exact (Forall_inv HF) | constructor].
Qed.

(* -------------------------------------------------------------------------- *)
(* Capstone: a bounded ring whose TRUE twice-area is small enough relative to  *)
(* the grid is removed outright by precision reduction.  Round-to-nearest      *)
(* snapping moves each coordinate by <= 1/(2*scale); the area then moves by at *)
(* most the perturbation bound, and `collapse_of_small_true_area` forces the   *)
(* snapped hole to exactly zero.  This is the closed, true-hole form of #979.  *)
(* -------------------------------------------------------------------------- *)

Theorem hole_collapses_of_small_true_ring :
  forall (rnd : R -> Z) (scale M : R),
    rounds_to_nearest rnd -> 0 < scale -> 0 <= M ->
  forall l : list Point,
    Forall (fun P => Rabs (px P) <= M /\ Rabs (py P) <= M) l ->
    INR (length l + 1) * (2 * (2 * M + / (2 * scale)) * / (2 * scale))
      + Rabs (signed_area2 l) < 1 / (scale * scale) ->
    signed_area2 (map (snap_pt rnd scale) l) = 0.
Proof.
  intros rnd scale M Hrn Hpos HM l HF Hbnd.
  apply (collapse_of_small_true_area rnd scale Hpos l).
  assert (Hdelta : 0 <= / (2 * scale))
    by (apply Rlt_le, Rinv_0_lt_compat; lra).
  assert (Hpert :
    Rabs (signed_area2 (map (snap_pt rnd scale) l) - signed_area2 l)
    <= INR (length l + 1) * (2 * (2 * M + / (2 * scale)) * / (2 * scale))).
  { apply signed_area2_perturb_bound; try assumption.
    - intro P. apply snap_pt_close_x; assumption.
    - intro P. apply snap_pt_close_y; assumption. }
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions signed_area2_snap_quantized.
Print Assumptions hole_below_grid_resolution_collapses.
Print Assumptions snapped_triangle_area_is_cross.
Print Assumptions some_subgrid_hole_removed.
Print Assumptions survived_count_lt_of_subgrid.
Print Assumptions snap_coord_close.
Print Assumptions collapse_of_small_true_area.
Print Assumptions signed_area2_perturb_bound.
Print Assumptions hole_collapses_of_small_true_ring.
