(* ============================================================================
   NetTopologySuite.Proofs.JCTEastApproach
   ----------------------------------------------------------------------------
   ESCAPE DESCENT, rung 1: the east approach.  From an even-parity guarded
   complement point, walk east along the ray up to (but not onto) the FIRST
   crossing -- the launchpad every detour starts from.

   Contents, all Qed:

     - `cross_x` : the height-(py p) crossing abscissa of an edge (asc/desc
       by the endpoint order; garbage off-crossing, never used there);
     - `ho_cross_strict_of_guard` : under `ray_avoids_vertices`, every
       half-open crossing is a STRICT straddle (a bottom-endpoint-level
       crossing would put that vertex on the ray, east);
     - `cross_x_east` / `cross_pt_on_edge` : a crossing's abscissa lies
       strictly east of p and is the edge's unique height-(py p) point;
     - `min_cross_x` : the first wall.  `min_cross_x_spec`: when the count
       is positive it exists, is achieved by a crossing edge, and bounds
       every crossing from below;
     - `east_segment_free` : the half-open segment [px p, X1) at p's height
       is SKELETON-FREE (non-crossing edges by the part-6 ray lemma,
       crossing edges because their unique height point sits at or beyond
       the wall);
     - `east_walk` : therefore p connects to every m on that segment, and m
       keeps p's guard and EXACT crossing count (`ho_count`) -- the descent
       invariants survive the approach;
     - `crossings_distinct` : THE FIRST GENUINE USE OF `ring_simple` in the
       H1 campaign -- two distinct crossing edges cross the ray at distinct
       abscissae, because a shared crossing point is interior to both
       (strict straddles!) and would be a proper intersection.

   Next rungs (docs/jct-escape-descent-plan.md): the corner corridor around
   the first edge's nearer endpoint, the recursive boundary walk, and the
   assembly `escape_descent_holds` closing H1.

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
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §1  The crossing abscissa.
   --------------------------------------------------------------------------- *)

Definition cross_x (p : Point) (e : Edge) : R :=
  let (a, b) := e in
  if Rle_dec (py a) (py b)
  then px a + (px b - px a) * (py p - py a) / (py b - py a)
  else px b + (px a - px b) * (py p - py b) / (py a - py b).

(* Under the ray guard, every half-open crossing is a STRICT straddle. *)
Lemma ho_cross_strict_of_guard : forall (r : Ring) (p : Point) (a b : Point),
  ray_avoids_vertices p r ->
  In (a, b) (ring_edges r) ->
  edge_crosses_ray_ho p (a, b) ->
  (py a < py p < py b \/ py b < py p < py a).
Proof.
  intros r p a b Hrav Hin Hc.
  destruct (ring_edges_endpoints_in r _ Hin) as [Ha Hb]; cbn [fst snd] in *.
  destruct Hc as [[Hy Hx] | [Hy Hx]].
  - left. destruct (Req_dec (py a) (py p)) as [He | Hne]; [ | lra ].
    exfalso.
    replace (px a + (px b - px a) * (py p - py a) / (py b - py a))
      with (px a) in Hx by (rewrite <- He; field; lra).
    apply (Hrav a Ha). split; [ exact He | lra ].
  - right. destruct (Req_dec (py b) (py p)) as [He | Hne]; [ | lra ].
    exfalso.
    replace (px b + (px a - px b) * (py p - py b) / (py a - py b))
      with (px b) in Hx by (rewrite <- He; field; lra).
    apply (Hrav b Hb). split; [ exact He | lra ].
Qed.

(* The crossing abscissa lies strictly east of p. *)
Lemma cross_x_east : forall (p : Point) (a b : Point),
  edge_crosses_ray_ho p (a, b) ->
  px p < cross_x p (a, b).
Proof.
  intros p a b Hc. unfold cross_x.
  destruct Hc as [[Hy Hx] | [Hy Hx]];
    destruct (Rle_dec (py a) (py b)) as [Hle | Hle]; try lra.
Qed.

(* The crossing abscissa is ON the edge at p's height. *)
Lemma cross_pt_on_edge : forall (p : Point) (a b : Point),
  edge_crosses_ray_ho p (a, b) ->
  exists t : R, 0 <= t <= 1 /\
    cross_x p (a, b) = (1 - t) * px a + t * px b /\
    py p = (1 - t) * py a + t * py b.
Proof.
  intros p a b Hc.
  destruct Hc as [[Hy Hx] | [Hy Hx]].
  - assert (Hd : py a < py b) by lra.
    exists ((py p - py a) / (py b - py a)).
    assert (Hd0 : py b - py a <> 0) by lra.
    split; [ split | split ].
    + apply Rmult_le_reg_r with (py b - py a); [ lra | ].
      replace ((py p - py a) / (py b - py a) * (py b - py a))
        with (py p - py a) by (field; lra). lra.
    + apply Rmult_le_reg_r with (py b - py a); [ lra | ].
      replace ((py p - py a) / (py b - py a) * (py b - py a))
        with (py p - py a) by (field; lra). lra.
    + unfold cross_x. destruct (Rle_dec (py a) (py b)) as [Hle | Hle]; [ | lra ].
      apply Rmult_eq_reg_r with (py b - py a); [ | lra ].
      replace (((1 - (py p - py a) / (py b - py a)) * px a +
                (py p - py a) / (py b - py a) * px b) * (py b - py a))
        with (px a * (py b - py p) + px b * (py p - py a)) by (field; lra).
      replace ((px a + (px b - px a) * (py p - py a) / (py b - py a))
                 * (py b - py a))
        with (px a * (py b - py a) + (px b - px a) * (py p - py a))
        by (field; lra).
      ring.
    + apply Rmult_eq_reg_r with (py b - py a); [ | lra ].
      replace (((1 - (py p - py a) / (py b - py a)) * py a +
                (py p - py a) / (py b - py a) * py b) * (py b - py a))
        with (py a * (py b - py p) + py b * (py p - py a)) by (field; lra).
      ring.
  - assert (Hd : py b < py a) by lra.
    exists ((py a - py p) / (py a - py b)).
    assert (Hd0 : py a - py b <> 0) by lra.
    split; [ split | split ].
    + apply Rmult_le_reg_r with (py a - py b); [ lra | ].
      replace ((py a - py p) / (py a - py b) * (py a - py b))
        with (py a - py p) by (field; lra). lra.
    + apply Rmult_le_reg_r with (py a - py b); [ lra | ].
      replace ((py a - py p) / (py a - py b) * (py a - py b))
        with (py a - py p) by (field; lra). lra.
    + unfold cross_x. destruct (Rle_dec (py a) (py b)) as [Hle | Hle]; [ lra | ].
      apply Rmult_eq_reg_r with (py a - py b); [ | lra ].
      replace (((1 - (py a - py p) / (py a - py b)) * px a +
                (py a - py p) / (py a - py b) * px b) * (py a - py b))
        with (px a * (py p - py b) + px b * (py a - py p)) by (field; lra).
      replace ((px b + (px a - px b) * (py p - py b) / (py a - py b))
                 * (py a - py b))
        with (px b * (py a - py b) + (px a - px b) * (py p - py b))
        by (field; lra).
      ring.
    + apply Rmult_eq_reg_r with (py a - py b); [ | lra ].
      replace (((1 - (py a - py p) / (py a - py b)) * py a +
                (py a - py p) / (py a - py b) * py b) * (py a - py b))
        with (py a * (py p - py b) + py b * (py a - py p)) by (field; lra).
      ring.
Qed.

(* Conversely: any on-edge point at p's height of a crossing edge IS the
   crossing point. *)
Lemma height_pt_unique : forall (p : Point) (a b : Point) (t : R),
  edge_crosses_ray_ho p (a, b) ->
  0 <= t <= 1 ->
  py p = (1 - t) * py a + t * py b ->
  (1 - t) * px a + t * px b = cross_x p (a, b).
Proof.
  intros p a b t Hc Ht Hy.
  destruct Hc as [[Hband Hx] | [Hband Hx]].
  - assert (Hd : py a < py b) by lra.
    unfold cross_x. destruct (Rle_dec (py a) (py b)) as [Hle | Hle]; [ | lra ].
    apply Rmult_eq_reg_r with (py b - py a); [ | lra ].
    replace ((px a + (px b - px a) * (py p - py a) / (py b - py a))
               * (py b - py a))
      with (px a * (py b - py a) + (px b - px a) * (py p - py a))
      by (field; lra).
    nra.
  - assert (Hd : py b < py a) by lra.
    unfold cross_x. destruct (Rle_dec (py a) (py b)) as [Hle | Hle]; [ lra | ].
    apply Rmult_eq_reg_r with (py a - py b); [ | lra ].
    replace ((px b + (px a - px b) * (py p - py b) / (py a - py b))
               * (py a - py b))
      with (px b * (py a - py b) + (px a - px b) * (py p - py b))
      by (field; lra).
    nra.
Qed.

(* ---------------------------------------------------------------------------
   §2  The first wall: the minimum crossing abscissa.
   --------------------------------------------------------------------------- *)

Fixpoint min_cross_x (p : Point) (es : list Edge) : option R :=
  match es with
  | [] => None
  | e :: es' =>
      let rest := min_cross_x p es' in
      if edge_crosses_ray_ho_dec p e
      then match rest with
           | None => Some (cross_x p e)
           | Some m => Some (Rmin (cross_x p e) m)
           end
      else rest
  end.

Lemma ho_count_pos_ex : forall (p : Point) (es : list Edge),
  (0 < ho_count p es)%nat ->
  exists e, In e es /\ edge_crosses_ray_ho p e.
Proof.
  intros p; induction es as [| e es' IH]; intros Hpos; cbn [ho_count] in Hpos.
  - lia.
  - destruct (edge_crosses_ray_ho_dec p e) as [Hc | Hn].
    + exists e. split; [ left; reflexivity | exact Hc ].
    + destruct (IH ltac:(lia)) as [e' [Hin' Hc']].
      exists e'. split; [ right; exact Hin' | exact Hc' ].
Qed.

Lemma min_cross_x_none : forall (p : Point) (es : list Edge),
  min_cross_x p es = None ->
  forall e, In e es -> ~ edge_crosses_ray_ho p e.
Proof.
  intros p; induction es as [| e0 es' IH]; intros Hn e Hin; [ contradiction | ].
  cbn [min_cross_x] in Hn.
  destruct (edge_crosses_ray_ho_dec p e0) as [Hc0 | Hn0].
  - destruct (min_cross_x p es'); discriminate.
  - destruct Hin as [He | Hin]; [ subst e0; exact Hn0 | exact (IH Hn e Hin) ].
Qed.

Lemma min_cross_x_some_of_cross : forall (p : Point) (es : list Edge) (e : Edge),
  In e es -> edge_crosses_ray_ho p e ->
  exists X1, min_cross_x p es = Some X1.
Proof.
  intros p; induction es as [| e0 es' IH]; intros e Hin Hc; [ contradiction | ].
  cbn [min_cross_x].
  destruct (edge_crosses_ray_ho_dec p e0) as [Hc0 | Hn0].
  - destruct (min_cross_x p es') as [m |].
    + eexists; reflexivity.
    + eexists; reflexivity.
  - destruct Hin as [He | Hin].
    + subst e0. exact (False_ind _ (Hn0 Hc)).
    + exact (IH e Hin Hc).
Qed.

Lemma min_cross_x_achieved : forall (p : Point) (es : list Edge) (X1 : R),
  min_cross_x p es = Some X1 ->
  exists e, In e es /\ edge_crosses_ray_ho p e /\ cross_x p e = X1.
Proof.
  intros p; induction es as [| e0 es' IH]; intros X1 Hm; [ discriminate | ].
  cbn [min_cross_x] in Hm.
  destruct (edge_crosses_ray_ho_dec p e0) as [Hc0 | Hn0].
  - destruct (min_cross_x p es') as [m |] eqn:Hrest.
    + injection Hm as Hm. unfold Rmin in Hm.
      destruct (Rle_dec (cross_x p e0) m) as [Hle | Hle].
      * exists e0. split; [ left; reflexivity | split; [ exact Hc0 | exact Hm ] ].
      * destruct (IH m eq_refl) as [e' [Hin' [Hc' Hx']]].
        exists e'. split; [ right; exact Hin' | split; [ exact Hc' | ] ].
        rewrite Hx'. exact Hm.
    + injection Hm as Hm.
      exists e0. split; [ left; reflexivity | split; [ exact Hc0 | exact Hm ] ].
  - destruct (IH X1 Hm) as [e' [Hin' [Hc' Hx']]].
    exists e'. split; [ right; exact Hin' | split; assumption ].
Qed.

Lemma min_cross_x_lb : forall (p : Point) (es : list Edge) (X1 : R),
  min_cross_x p es = Some X1 ->
  forall e, In e es -> edge_crosses_ray_ho p e -> X1 <= cross_x p e.
Proof.
  intros p; induction es as [| e0 es' IH]; intros X1 Hm e Hin Hc;
    [ contradiction | ].
  cbn [min_cross_x] in Hm.
  destruct (edge_crosses_ray_ho_dec p e0) as [Hc0 | Hn0].
  - destruct (min_cross_x p es') as [m |] eqn:Hrest.
    + injection Hm as Hm.
      destruct Hin as [He | Hin].
      * subst e0. rewrite <- Hm. apply Rmin_l.
      * pose proof (IH m eq_refl e Hin Hc).
        rewrite <- Hm. eapply Rle_trans; [ apply Rmin_r | assumption ].
    + injection Hm as Hm.
      destruct Hin as [He | Hin].
      * subst e0. lra.
      * exfalso. exact (min_cross_x_none p es' Hrest e Hin Hc).
  - destruct Hin as [He | Hin].
    + subst e0. exact (False_ind _ (Hn0 Hc)).
    + exact (IH X1 Hm e Hin Hc).
Qed.

(* ---------------------------------------------------------------------------
   §3  The east segment up to the wall is skeleton-free.
   --------------------------------------------------------------------------- *)

Lemma east_segment_free : forall (r : Ring) (p : Point) (X1 : R),
  ring_complement r p ->
  ray_avoids_vertices p r ->
  min_cross_x p (ring_edges r) = Some X1 ->
  forall x', px p <= x' -> x' < X1 ->
    ~ ring_image r (mkPoint x' (py p)).
Proof.
  intros r p X1 Hcompl Hrav Hmin x' Hge Hlt [e [t [Hin [Ht [Hx Hy]]]]].
  destruct e as [a b].
  destruct (ring_edges_endpoints_in r _ Hin) as [Ha Hb]; cbn [fst snd] in *.
  cbn [px py] in Hx, Hy.
  destruct (edge_crosses_ray_ho_dec p (a, b)) as [Hc | Hn].
  - (* crossing edge: its unique height point is at cross_x >= X1 > x' *)
    pose proof (height_pt_unique p a b t Hc Ht Hy) as Hu.
    pose proof (min_cross_x_lb p (ring_edges r) X1 Hmin (a, b) Hin Hc).
    lra.
  - (* non-crossing edge: the part-6 ray-freedom lemma *)
    refine (ho_no_cross_east_free a b p Hn _ _ _ x' Hge
              (ex_intro _ t (conj Ht (conj Hx Hy)))).
    + intros [He Hle]. exact (Hrav a Ha (conj He Hle)).
    + intros [He Hle]. exact (Hrav b Hb (conj He Hle)).
    + intro Hex. apply Hcompl.
      destruct Hex as [t' [[Ht1' Ht2'] [Hx2 Hy2]]].
      exists (a, b), t'. cbn [fst snd]. repeat split; assumption.
Qed.

(* ---------------------------------------------------------------------------
   §4  The east walk: connectivity + invariance of guard and count.
   --------------------------------------------------------------------------- *)

Lemma east_walk_connected : forall (r : Ring) (p : Point) (X1 x' : R),
  ring_complement r p ->
  ray_avoids_vertices p r ->
  min_cross_x p (ring_edges r) = Some X1 ->
  px p <= x' -> x' < X1 ->
  connected_in_complement_cont r p (mkPoint x' (py p)).
Proof.
  intros r p X1 x' Hcompl Hrav Hmin Hge Hlt.
  destruct p as [u v]; cbn [px py] in *.
  exists (fun t => mkPoint ((1 - t) * u + t * x') ((1 - t) * v + t * v)).
  split; [ apply straight_path_continuous | ]. split; [ | split ].
  - cbn [px py]; f_equal; lra.
  - cbn [px py]; f_equal; lra.
  - intros t Ht Himg.
    assert (Hco : (1 - t) * v + t * v = v) by ring.
    rewrite Hco in Himg.
    refine (east_segment_free r (mkPoint u v) X1 Hcompl Hrav Hmin
              ((1 - t) * u + t * x') _ _ Himg); cbn [px py]; nra.
Qed.

(* Per-edge: crossing is invariant under an eastward shift that stays west of
   the edge's own crossing abscissa. *)
Lemma cross_iff_shift_east : forall (p m : Point) (e : Edge),
  py m = py p ->
  px p <= px m ->
  (edge_crosses_ray_ho p e -> px m < cross_x p e) ->
  (edge_crosses_ray_ho m e <-> edge_crosses_ray_ho p e).
Proof.
  intros p m [a b] Hy Hx Hwest.
  unfold edge_crosses_ray_ho. rewrite Hy.
  split.
  - intros [[Hband Hray] | [Hband Hray]].
    + left. split; [ exact Hband | lra ].
    + right. split; [ exact Hband | lra ].
  - intro Hc.
    pose proof (Hwest Hc) as Hm. unfold cross_x in Hm.
    destruct Hc as [[Hband Hray] | [Hband Hray]].
    + assert (Hd : py a < py b) by lra.
      destruct (Rle_dec (py a) (py b)) as [Hle | Hle]; [ | lra ].
      left. split; [ exact Hband | exact Hm ].
    + assert (Hd : py b < py a) by lra.
      destruct (Rle_dec (py a) (py b)) as [Hle | Hle]; [ lra | ].
      right. split; [ exact Hband | exact Hm ].
Qed.

Lemma ho_count_ext : forall (p m : Point) (es : list Edge),
  (forall e, In e es ->
     (edge_crosses_ray_ho m e <-> edge_crosses_ray_ho p e)) ->
  ho_count m es = ho_count p es.
Proof.
  intros p m; induction es as [| e es' IH]; intros Hiff; [ reflexivity | ].
  cbn [ho_count].
  rewrite (IH (fun e' He' => Hiff e' (or_intror He'))).
  pose proof (Hiff e (or_introl eq_refl)) as He.
  destruct (edge_crosses_ray_ho_dec m e) as [Hcm | Hnm];
  destruct (edge_crosses_ray_ho_dec p e) as [Hcp | Hnp];
    try reflexivity; tauto.
Qed.

(* THE RUNG THEOREM: the east approach.  Every point on the half-open
   segment up to the first wall is reachable, guarded, and carries the same
   crossing count. *)
Theorem east_approach : forall (r : Ring) (p : Point),
  ring_complement r p ->
  ray_avoids_vertices p r ->
  (0 < ho_count p (ring_edges r))%nat ->
  exists X1 : R,
    px p < X1 /\
    min_cross_x p (ring_edges r) = Some X1 /\
    (exists e, In e (ring_edges r) /\ edge_crosses_ray_ho p e /\
               cross_x p e = X1) /\
    forall x', px p <= x' -> x' < X1 ->
      let m := mkPoint x' (py p) in
      connected_in_complement_cont r p m /\
      ring_complement r m /\
      ray_avoids_vertices m r /\
      ho_count m (ring_edges r) = ho_count p (ring_edges r).
Proof.
  intros r p Hcompl Hrav Hpos.
  destruct (ho_count_pos_ex p (ring_edges r) Hpos) as [e0 [Hin0 Hc0]].
  destruct (min_cross_x_some_of_cross p (ring_edges r) e0 Hin0 Hc0)
    as [X1 Hmin].
  destruct (min_cross_x_achieved p (ring_edges r) X1 Hmin)
    as [e1 [Hin1 [Hc1 Hx1]]].
  exists X1.
  assert (HpX : px p < X1).
  { rewrite <- Hx1. destruct e1 as [a b]. apply cross_x_east. exact Hc1. }
  split; [ exact HpX | ].
  split; [ exact Hmin | ].
  split; [ exists e1; auto | ].
  intros x' Hge Hlt m.
  assert (Hconn : connected_in_complement_cont r p m)
    by (apply (east_walk_connected r p X1 x' Hcompl Hrav Hmin Hge Hlt)).
  assert (Hcomplm : ring_complement r m).
  { intro Himg.
    exact (east_segment_free r p X1 Hcompl Hrav Hmin x' Hge Hlt Himg). }
  assert (Hravm : ray_avoids_vertices m r).
  { intros v Hv [Heq Hle]. unfold m in *; cbn [px py] in *.
    apply (Hrav v Hv). split; [ rewrite Heq; reflexivity | lra ]. }
  split; [ exact Hconn | ]. split; [ exact Hcomplm | ].
  split; [ exact Hravm | ].
  apply ho_count_ext.
  intros e He. apply cross_iff_shift_east; unfold m; cbn [px py].
  - reflexivity.
  - lra.
  - intro Hc. pose proof (min_cross_x_lb p (ring_edges r) X1 Hmin e He Hc). lra.
Qed.

(* ---------------------------------------------------------------------------
   §5  Simplicity enters: distinct crossing edges cross at distinct points.
   --------------------------------------------------------------------------- *)

Theorem crossings_distinct : forall (r : Ring) (p : Point) (e1 e2 : Edge),
  ring_simple r ->
  ray_avoids_vertices p r ->
  In e1 (ring_edges r) -> In e2 (ring_edges r) -> e1 <> e2 ->
  edge_crosses_ray_ho p e1 -> edge_crosses_ray_ho p e2 ->
  cross_x p e1 <> cross_x p e2.
Proof.
  intros r p [a1 b1] [a2 b2] Hs Hrav Hin1 Hin2 Hne Hc1 Hc2 Heq.
  (* both crossings are STRICT straddles, so the shared point is interior *)
  pose proof (ho_cross_strict_of_guard r p a1 b1 Hrav Hin1 Hc1) as Hstr1.
  pose proof (ho_cross_strict_of_guard r p a2 b2 Hrav Hin2 Hc2) as Hstr2.
  destruct (cross_pt_on_edge p a1 b1 Hc1) as [t [Ht [Hx1 Hy1]]].
  destruct (cross_pt_on_edge p a2 b2 Hc2) as [s [Hs' [Hx2 Hy2]]].
  (* interiority of the parameters from the strict straddles *)
  assert (Ht' : 0 < t < 1).
  { destruct Hstr1 as [Hb | Hb]; split.
    - destruct (Rle_or_lt t 0) as [Hle | ]; [ exfalso; nra | assumption ].
    - destruct (Rle_or_lt 1 t) as [Hle | ]; [ exfalso; nra | assumption ].
    - destruct (Rle_or_lt t 0) as [Hle | ]; [ exfalso; nra | assumption ].
    - destruct (Rle_or_lt 1 t) as [Hle | ]; [ exfalso; nra | assumption ]. }
  assert (Hs'' : 0 < s < 1).
  { destruct Hstr2 as [Hb | Hb]; split.
    - destruct (Rle_or_lt s 0) as [Hle | ]; [ exfalso; nra | assumption ].
    - destruct (Rle_or_lt 1 s) as [Hle | ]; [ exfalso; nra | assumption ].
    - destruct (Rle_or_lt s 0) as [Hle | ]; [ exfalso; nra | assumption ].
    - destruct (Rle_or_lt 1 s) as [Hle | ]; [ exfalso; nra | assumption ]. }
  (* the shared crossing point is a proper intersection: ring_simple refutes *)
  apply (Hs (a1, b1) (a2, b2) Hin1 Hin2 Hne).
  unfold segments_intersect_properly. cbn [fst snd].
  exists t, s.
  split; [ exact Ht' | ]. split; [ exact Hs'' | ].
  split; [ | lra ].
  rewrite <- Hx1, <- Hx2. exact Heq.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions east_approach.
Print Assumptions crossings_distinct.
