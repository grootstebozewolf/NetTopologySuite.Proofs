(* ============================================================================
   NetTopologySuite.Proofs.JCTLevelJump
   ----------------------------------------------------------------------------
   H1 PROPER, part 4: UPPER half-ball constancy of the half-open parity at
   EVERY complement point, Qed -- and the kernel shrinks once more, to the
   pure downward LEVEL JUMP.

   The half-open band `vy <= h < wy` is BOTTOM-INCLUSIVE, so each edge's
   band membership is stable UPWARD at every height: if `h` is in the band
   so is every `h' in [h, h + eps)` below the top, and if `h` is at-or-above
   the band top the band stays dead upward.  Concretely, for any edge there
   are only four upper-regimes:

     A. ya <= h and yb <= h : both disjuncts dead for all h' >= h (eps = 1);
     B. h < ya and h < yb   : both bands unreached, margin min(ya-h, yb-h);
     C. ya <= h < yb        : ascending band LIVE including its bottom edge
                              -- the ray atom PA is nonzero (PA = 0 in the
                              closed-bottom band puts q ON the edge, with
                              t = 0 allowed), so its sign is stable;
     D. yb <= h < ya        : descending mirror.

   No genericity, no vertex pairing: `ho_upper_stable` holds at EVERY
   complement point.  Consequently the remaining kernel is only

     ho_level_jump r  --  at a vertex-level complement point, the parity
                          JUST BELOW the level equals the parity AT it

   (`ho_level_stable_of_jump`), and H1's trapped half follows from that
   single downward-jump statement (`odd_parity_trapped_of_level_jump`).
   The jump is the honest residue: crossing a level downward, the east
   level-vertices hand their half-open bands between their incident edges
   (pass-through: one-for-one; extremum: two-at-once) -- the vertex-pairing
   count, now isolated on one side of one line.

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam.
From NTS.Proofs Require Import PointInRingCorrect JCT JCT_OnEdgeCounterexample.
From NTS.Proofs Require Import ConvexOffringSeam JCTParityTransport.
From NTS.Proofs Require Import JCTHalfOpenParity JCTGenericStability.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §1  Per-edge upper stability at any off-edge point.
   --------------------------------------------------------------------------- *)

Lemma ho_cross_stable_upper : forall (a b q : Point),
  (~ exists t : R, 0 <= t <= 1 /\
        px q = (1 - t) * px a + t * px b /\
        py q = (1 - t) * py a + t * py b) ->
  exists eps, 0 < eps /\
    forall q' : Point,
      Rabs (px q' - px q) < eps ->
      py q <= py q' < py q + eps ->
      (edge_crosses_ray_ho q' (a, b) <-> edge_crosses_ray_ho q (a, b)).
Proof.
  intros a b q Hoff.
  destruct (Rle_dec (py a) (py q)) as [HA | HA];
  destruct (Rle_dec (py b) (py q)) as [HB | HB].
  - (* A: both at-or-below the level: dead upward *)
    exists 1. split; [ lra | ].
    intros q' Hx Hh. unfold edge_crosses_ray_ho.
    split; intros [[[Hu1 Hu2] _] | [[Hu1 Hu2] _]]; lra.
  - (* C: ya <= h < yb : ascending band live, bottom included *)
    set (PA := (py b - py a) * (px a - px q) + (px b - px a) * (py q - py a)).
    assert (Hab : py a < py b) by lra.
    assert (HPA : PA <> 0).
    { intro Hz. apply Hoff.
      exists ((py q - py a) / (py b - py a)).
      assert (Hd : py b - py a <> 0) by lra.
      split; [ split | split ].
      - apply Rmult_le_reg_r with (py b - py a); [ lra | ].
        replace ((py q - py a) / (py b - py a) * (py b - py a))
          with (py q - py a) by (field; lra). lra.
      - apply Rmult_le_reg_r with (py b - py a); [ lra | ].
        replace ((py q - py a) / (py b - py a) * (py b - py a))
          with (py q - py a) by (field; lra). lra.
      - apply Rmult_eq_reg_r with (py b - py a); [ | lra ].
        replace (((1 - (py q - py a) / (py b - py a)) * px a +
                  (py q - py a) / (py b - py a) * px b) * (py b - py a))
          with (px a * (py b - py q) + px b * (py q - py a)) by (field; lra).
        unfold PA in Hz. nra.
      - apply Rmult_eq_reg_r with (py b - py a); [ | lra ].
        replace (((1 - (py q - py a) / (py b - py a)) * py a +
                  (py q - py a) / (py b - py a) * py b) * (py b - py a))
          with (py a * (py b - py q) + py b * (py q - py a)) by (field; lra).
        nra. }
    destruct (Rtotal_order 0 PA) as [HPAp | [HPAz | HPAn]];
      [ | exfalso; exact (HPA (eq_sym HPAz)) | ].
    + (* crossing TRUE at q, stably on the upper half-ball *)
      destruct (affine_sign_stable
                  (- (py b - py a)) (px b - px a)
                  ((py b - py a) * px a - (px b - px a) * py a)
                  (px q) (py q) ltac:(unfold PA in HPAp; nra))
        as [e3 [He3 Hb3]].
      exists (Rmin e3 (py b - py q)). split.
      * apply Rmin_glb_lt; lra.
      * intros q' Hx Hh.
        assert (Hx3 : Rabs (px q' - px q) < e3)
          by (eapply Rlt_le_trans; [ exact Hx | apply Rmin_l ]).
        assert (Hh3 : Rabs (py q' - py q) < e3).
        { pose proof (Rmin_l e3 (py b - py q)).
          unfold Rabs; destruct (Rcase_abs (py q' - py q)); lra. }
        assert (Hhb : py q' < py b)
          by (pose proof (Rmin_r e3 (py b - py q)); lra).
        pose proof (Hb3 (px q') (py q') Hx3 Hh3) as S3.
        rewrite (ho_asc_iff a b q' Hab), (ho_asc_iff a b q Hab).
        split; intros _; (split; [ lra | unfold PA in *; nra ]).
    + (* crossing FALSE at q, stably *)
      destruct (affine_sign_stable
                  (py b - py a) (- (px b - px a))
                  (- ((py b - py a) * px a - (px b - px a) * py a))
                  (px q) (py q) ltac:(unfold PA in HPAn; nra))
        as [e3 [He3 Hb3]].
      exists e3. split; [ lra | ].
      intros q' Hx Hh.
      assert (Hh3 : Rabs (py q' - py q) < e3)
        by (unfold Rabs; destruct (Rcase_abs (py q' - py q)); lra).
      pose proof (Hb3 (px q') (py q') Hx Hh3) as S3.
      rewrite (ho_asc_iff a b q' Hab), (ho_asc_iff a b q Hab).
      split; intros [Hu HP]; exfalso; unfold PA in *; nra.
  - (* D: yb <= h < ya : descending band live, bottom included *)
    set (PD := (py a - py b) * (px b - px q) + (px a - px b) * (py q - py b)).
    assert (Hab : py b < py a) by lra.
    assert (HPD : PD <> 0).
    { intro Hz. apply Hoff.
      exists ((py a - py q) / (py a - py b)).
      assert (Hd : py a - py b <> 0) by lra.
      split; [ split | split ].
      - apply Rmult_le_reg_r with (py a - py b); [ lra | ].
        replace ((py a - py q) / (py a - py b) * (py a - py b))
          with (py a - py q) by (field; lra). lra.
      - apply Rmult_le_reg_r with (py a - py b); [ lra | ].
        replace ((py a - py q) / (py a - py b) * (py a - py b))
          with (py a - py q) by (field; lra). lra.
      - apply Rmult_eq_reg_r with (py a - py b); [ | lra ].
        replace (((1 - (py a - py q) / (py a - py b)) * px a +
                  (py a - py q) / (py a - py b) * px b) * (py a - py b))
          with (px a * (py q - py b) + px b * (py a - py q)) by (field; lra).
        unfold PD in Hz. nra.
      - apply Rmult_eq_reg_r with (py a - py b); [ | lra ].
        replace (((1 - (py a - py q) / (py a - py b)) * py a +
                  (py a - py q) / (py a - py b) * py b) * (py a - py b))
          with (py a * (py q - py b) + py b * (py a - py q)) by (field; lra).
        nra. }
    destruct (Rtotal_order 0 PD) as [HPDp | [HPDz | HPDn]];
      [ | exfalso; exact (HPD (eq_sym HPDz)) | ].
    + destruct (affine_sign_stable
                  (- (py a - py b)) (px a - px b)
                  ((py a - py b) * px b - (px a - px b) * py b)
                  (px q) (py q) ltac:(unfold PD in HPDp; nra))
        as [e3 [He3 Hb3]].
      exists (Rmin e3 (py a - py q)). split.
      * apply Rmin_glb_lt; lra.
      * intros q' Hx Hh.
        assert (Hx3 : Rabs (px q' - px q) < e3)
          by (eapply Rlt_le_trans; [ exact Hx | apply Rmin_l ]).
        assert (Hh3 : Rabs (py q' - py q) < e3).
        { pose proof (Rmin_l e3 (py a - py q)).
          unfold Rabs; destruct (Rcase_abs (py q' - py q)); lra. }
        assert (Hha : py q' < py a)
          by (pose proof (Rmin_r e3 (py a - py q)); lra).
        pose proof (Hb3 (px q') (py q') Hx3 Hh3) as S3.
        rewrite (ho_desc_iff a b q' Hab), (ho_desc_iff a b q Hab).
        split; intros _; (split; [ lra | unfold PD in *; nra ]).
    + destruct (affine_sign_stable
                  (py a - py b) (- (px a - px b))
                  (- ((py a - py b) * px b - (px a - px b) * py b))
                  (px q) (py q) ltac:(unfold PD in HPDn; nra))
        as [e3 [He3 Hb3]].
      exists e3. split; [ lra | ].
      intros q' Hx Hh.
      assert (Hh3 : Rabs (py q' - py q) < e3)
        by (unfold Rabs; destruct (Rcase_abs (py q' - py q)); lra).
      pose proof (Hb3 (px q') (py q') Hx Hh3) as S3.
      rewrite (ho_desc_iff a b q' Hab), (ho_desc_iff a b q Hab).
      split; intros [Hu HP]; exfalso; unfold PD in *; nra.
  - (* B: both strictly above the level: bands unreached, with margin *)
    exists (Rmin (py a - py q) (py b - py q)). split.
    + apply Rmin_glb_lt; lra.
    + intros q' Hx Hh.
      pose proof (Rmin_l (py a - py q) (py b - py q)).
      pose proof (Rmin_r (py a - py q) (py b - py q)).
      unfold edge_crosses_ray_ho.
      split; intros [[[Hu1 Hu2] _] | [[Hu1 Hu2] _]]; lra.
Qed.

(* ---------------------------------------------------------------------------
   §2  Finite assembly over the edge list, upper half-ball version.
   --------------------------------------------------------------------------- *)

Lemma ho_parity_ball_upper : forall (q : Point) (es : list Edge),
  (forall e, In e es ->
     exists eps, 0 < eps /\
       forall q' : Point,
         Rabs (px q' - px q) < eps -> py q <= py q' < py q + eps ->
         (edge_crosses_ray_ho q' e <-> edge_crosses_ray_ho q e)) ->
  exists eps, 0 < eps /\
    forall q' : Point,
      Rabs (px q' - px q) < eps -> py q <= py q' < py q + eps ->
      (ho_parity_odd q' es <-> ho_parity_odd q es)
      /\ (ho_parity_even q' es <-> ho_parity_even q es).
Proof.
  intros q; induction es as [| e es' IH]; intros Hst.
  - exists 1. split; [ lra | ].
    intros q' _ _. split; split; intro H; try (inversion H; fail); constructor.
  - destruct (Hst e (or_introl eq_refl)) as [e1 [He1 Hb1]].
    destruct (IH (fun e' He' => Hst e' (or_intror He'))) as [e2 [He2 Hb2]].
    exists (Rmin e1 e2). split; [ apply Rmin_glb_lt; lra | ].
    intros q' Hx Hh.
    pose proof (Rmin_l e1 e2). pose proof (Rmin_r e1 e2).
    assert (Hx1 : Rabs (px q' - px q) < e1) by lra.
    assert (Hh1 : py q <= py q' < py q + e1) by lra.
    assert (Hx2 : Rabs (px q' - px q) < e2) by lra.
    assert (Hh2 : py q <= py q' < py q + e2) by lra.
    pose proof (Hb1 q' Hx1 Hh1) as Hiff.
    destruct (Hb2 q' Hx2 Hh2) as [IHo IHe].
    destruct (edge_crosses_ray_ho_dec q e) as [Hc | Hn].
    + assert (Hc' : edge_crosses_ray_ho q' e) by tauto.
      rewrite (ho_odd_cons_cross _ _ _ Hc), (ho_odd_cons_cross _ _ _ Hc'),
              (ho_even_cons_cross _ _ _ Hc), (ho_even_cons_cross _ _ _ Hc').
      tauto.
    + assert (Hn' : ~ edge_crosses_ray_ho q' e) by tauto.
      rewrite (ho_odd_cons_skip _ _ _ Hn), (ho_odd_cons_skip _ _ _ Hn'),
              (ho_even_cons_skip _ _ _ Hn), (ho_even_cons_skip _ _ _ Hn').
      tauto.
Qed.

(* Upper stability at EVERY complement point -- no genericity, no pairing. *)
Theorem ho_upper_stable : forall (r : Ring) (q : Point),
  ring_complement r q ->
  exists eps, 0 < eps /\
    forall q' : Point,
      Rabs (px q' - px q) < eps -> py q <= py q' < py q + eps ->
      (point_in_ring_ho q' r <-> point_in_ring_ho q r).
Proof.
  intros r q Hcompl.
  destruct (ho_parity_ball_upper q (ring_edges r)) as [eps [Heps Hball]].
  { intros [a b] Hin.
    apply ho_cross_stable_upper.
    intro Hex. apply Hcompl.
    destruct Hex as [t [[Ht1 Ht2] [Hx Hy]]].
    exists (a, b), t. cbn [fst snd]. repeat split; assumption. }
  exists eps. split; [ exact Heps | ].
  intros q' Hx Hh. exact (proj1 (Hball q' Hx Hh)).
Qed.

(* ---------------------------------------------------------------------------
   §3  The kernel shrinks to the downward level jump.
   --------------------------------------------------------------------------- *)

(* THE REMAINING KERNEL: at a vertex-level complement point, the parity just
   BELOW the level equals the parity AT it.  This is the vertex-pairing count
   isolated on one side of one line: crossing the level downward, each east
   level-vertex hands its half-open band between its two incident edges. *)
Definition ho_level_jump (r : Ring) : Prop :=
  forall q : Point,
    ring_complement r q ->
    (exists v, In v r /\ py v = py q) ->
    exists eps, 0 < eps /\
      forall q' : Point,
        Rabs (px q' - px q) < eps -> py q - eps < py q' < py q ->
        ring_complement r q' ->
        (point_in_ring_ho q' r <-> point_in_ring_ho q r).

Theorem ho_level_stable_of_jump : forall (r : Ring),
  ho_level_jump r -> ho_level_stable r.
Proof.
  intros r Hjump q Hcompl Hat.
  destruct (Hjump q Hcompl Hat) as [e1 [He1 Hb1]].
  destruct (ho_upper_stable r q Hcompl) as [e2 [He2 Hb2]].
  exists (Rmin e1 e2). split; [ apply Rmin_glb_lt; lra | ].
  intros q' Hx Hh Hcompl'.
  pose proof (Rmin_l e1 e2). pose proof (Rmin_r e1 e2).
  destruct (Rle_or_lt (py q) (py q')) as [Hup | Hdown].
  - apply Hb2.
    + lra.
    + split; [ exact Hup | ].
      unfold Rabs in Hh; destruct (Rcase_abs (py q' - py q)); lra.
  - apply Hb1; try assumption.
    + lra.
    + split; [ | exact Hdown ].
      unfold Rabs in Hh; destruct (Rcase_abs (py q' - py q)); lra.
Qed.

(* THE CAPSTONE: H1's trapped half needs only the downward level jump. *)
Theorem odd_parity_trapped_of_level_jump : forall (r : Ring) (p : Point),
  ring_closed r ->
  ho_level_jump r ->
  ray_avoids_vertices p r ->
  point_in_ring p r ->
  in_bounded_component_cont r p.
Proof.
  intros r p Hclosed Hjump Hrav Hpir.
  apply (odd_parity_trapped_of_level_stable r p Hclosed); try assumption.
  apply ho_level_stable_of_jump. exact Hjump.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions ho_cross_stable_upper.
Print Assumptions ho_upper_stable.
Print Assumptions ho_level_stable_of_jump.
Print Assumptions odd_parity_trapped_of_level_jump.
