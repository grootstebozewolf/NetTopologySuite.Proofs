(* ============================================================================
   NetTopologySuite.Proofs.CrvTouchKiss
   ----------------------------------------------------------------------------
   CRV-TOUCH acceptance module (docs/scout/spec-crv-touch.md, #1038).

   A tangency oracle over rational input eggs, decided exactly in Q:

     * circle–circle tangency  (d² − r₁² − r₂²)² = 4 r₁² r₂²   (discq = 0)
     * circle–line tangency    h² = r² − |o − F|² = 0
     * certificate             σ = Ext iff d² − r₁² − r₂² > 0, else Int;
                               an arc–line tangency is always Ext
     * kiss                    a tangency with σ = Ext (TOUCH); σ = Int is a
                               pinch (covers, not TOUCH)
     * identity                a tangency hen reuses an existing hen iff the
                               two points are equal in Q; else it is minted
     * span                    every span test is the sign of a + b·√D with
                               a, b, D rational (`surd_nonneg`), so crossings
                               are span-checked without leaving Q
     * Decline                 cooked input, segment–segment, zero-length
                               segment, collinear (non-)arc, and coincident
                               circles (d² = 0, r₁² = r₂²) — the last one
                               BEFORE the tangency point divides by d²

   Arc eggs are three rational WKT points; the circle is their circumcentre.
   Only the two end points are hens; the mid control point is egg data.

   ℝ bridge (`cc_ext_disks_touch`, `cc_int_disk_covers`): on two discs with
   positive rational r², a σ = Ext tangency gives OverlayTouchRow.disks_touch
   and a σ = Int tangency gives disk_covers one way or the other.  The
   oracle lemma `oracle_disc_touch_class` ties the oracle's Touch output to
   that classification.

   Witnesses A1–A9 of the spec, plus span-checked Hit / Empty, are closed
   computations (vm_compute).  They say nothing about other inputs; the
   general statements are the bridge theorems and `oracle_coincident_decline`.

   Not a noder, not a cook step, not an ADR-0006 keyword, not
   OverlayNGCurve.TOUCH.  Does not expand ADR-0007's first cook scope: this
   is the decision the spec names, not a cook for chord–arc eggs.

   claimId: crv-touch-kiss · witness: crv-touch-A1-A9 · board: CRV-TOUCH
   ========================================================================== *)

From Stdlib Require Import QArith Qreals Reals Lra List Bool.
From NTS.Proofs Require Import Distance Disk OverlayTouchRow.
Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  Rational eggs.                                                          *)
(* -------------------------------------------------------------------------- *)

Local Open Scope Q_scope.

Record QPt := mkQPt { qx : Q; qy : Q }.
Record QCirc := mkQCirc { ccx : Q; ccy : Q; cr2 : Q }.

Inductive Egg :=
  | EArc (p0 p1 p2 : QPt)      (* CIRCULARSTRING segment; p1 = control point *)
  | EDisc (c : QCirc)          (* a full circle (disc boundary) *)
  | ESeg (p0 p1 : QPt)         (* a chord egg *)
  | ECooked.                   (* already split at a √ hen: not decided *)

Inductive Sigma := Ext | Int.
Inductive Hen := Reuse (i : nat) | Mint.
Inductive Outcome :=
  | Touch (p : QPt) (s : Sigma) (h : Hen)
  | Hit | Empty | Decline.

Definition is_kiss (o : Outcome) : bool :=
  match o with Touch _ Ext _ => true | _ => false end.

Definition qpos (x : Q) : bool := negb (Qle_bool x 0).
Definition qneg (x : Q) : bool := negb (Qle_bool 0 x).
Definition qzero (x : Q) : bool := Qeq_bool x 0.
Definition qnonneg (x : Q) : bool := Qle_bool 0 x.
Definition sq (x : Q) : Q := x * x.

Definition peq (p q : QPt) : bool := Qeq_bool (qx p) (qx q) && Qeq_bool (qy p) (qy q).

Fixpoint find_hen (hs : list QPt) (p : QPt) (i : nat) : Hen :=
  match hs with
  | [] => Mint
  | h :: t => if peq h p then Reuse i else find_hen t p (S i)
  end.

Definition orient (a b c : QPt) : Q :=
  (qx b - qx a) * (qy c - qy a) - (qy b - qy a) * (qx c - qx a).

(** Linear part of [orient a b] along direction (vx, vy). *)
Definition orient_dir (a b : QPt) (vx vy : Q) : Q :=
  (qx b - qx a) * vy - (qy b - qy a) * vx.

(** a + b·√D ≥ 0, for D ≥ 0, decided in Q. *)
Definition surd_nonneg (a b D : Q) : bool :=
  if qnonneg a then qnonneg b || Qle_bool (sq b * D) (sq a)
  else qpos b && Qle_bool (sq a) (sq b * D).

(** Circumcircle of three points; None when they are collinear. *)
Definition circum (a b c : QPt) : option QCirc :=
  let den := 2 * (qx a * (qy b - qy c) + qx b * (qy c - qy a) + qx c * (qy a - qy b)) in
  if qzero den then None
  else
    let na := sq (qx a) + sq (qy a) in
    let nb := sq (qx b) + sq (qy b) in
    let nc := sq (qx c) + sq (qy c) in
    let ux := (na * (qy b - qy c) + nb * (qy c - qy a) + nc * (qy a - qy b)) / den in
    let uy := (na * (qx c - qx b) + nb * (qx a - qx c) + nc * (qx b - qx a)) / den in
    Some (mkQCirc ux uy (sq (qx a - ux) + sq (qy a - uy))).

Definition circ_of (e : Egg) : option QCirc :=
  match e with
  | EArc a b c => circum a b c
  | EDisc c => Some c
  | _ => None
  end.

(** Span of a curve egg at the point M + g·√D·(vx, vy) (on its circle).
    For an arc p0→p1→p2: the point is on p1's side of chord p0p2, closed;
    on the circle the chord line meets only p0 and p2, so the closed test
    is "endpoint or strictly on p1's side". *)
Definition span_surd (e : Egg) (M : QPt) (vx vy D g : Q) : bool :=
  match e with
  | EArc p0 p1 p2 =>
      let s := orient p0 p2 p1 in
      surd_nonneg (s * orient p0 p2 M) (s * g * orient_dir p0 p2 vx vy) D
  | _ => true
  end.

Definition span_q (e : Egg) (p : QPt) : bool := span_surd e p 0 0 0 1.

(* -------------------------------------------------------------------------- *)
(* §2  Circle × circle.                                                        *)
(* -------------------------------------------------------------------------- *)

Definition d2 (c1 c2 : QCirc) : Q := sq (ccx c2 - ccx c1) + sq (ccy c2 - ccy c1).
Definition sgap (c1 c2 : QCirc) : Q := d2 c1 c2 - cr2 c1 - cr2 c2.
Definition discq (c1 c2 : QCirc) : Q := sq (sgap c1 c2) - 4 * cr2 c1 * cr2 c2.

Inductive CC := CCoincident | CTangent (s : Sigma) | CCross | CMiss.

(** Coincident circles are caught FIRST (A9): they pass discq = 0. *)
Definition cc_class (c1 c2 : QCirc) : CC :=
  if qzero (d2 c1 c2) && Qeq_bool (cr2 c1) (cr2 c2) then CCoincident
  else if qzero (discq c1 c2) then CTangent (if qpos (sgap c1 c2) then Ext else Int)
  else if qneg (discq c1 c2) then CCross
  else CMiss.

(** Radical foot M = c1 + k·e, e = c2 − c1; tangency point when h² = 0. *)
Definition cc_k (c1 c2 : QCirc) : Q := (d2 c1 c2 + cr2 c1 - cr2 c2) / (2 * d2 c1 c2).
Definition cc_foot (c1 c2 : QCirc) : QPt :=
  mkQPt (ccx c1 + cc_k c1 c2 * (ccx c2 - ccx c1)) (ccy c1 + cc_k c1 c2 * (ccy c2 - ccy c1)).
(** Crossings: M ± √D·perp(e), D = (r1² − k²·d²) / d². *)
Definition cc_D (c1 c2 : QCirc) : Q := (cr2 c1 - sq (cc_k c1 c2) * d2 c1 c2) / d2 c1 c2.

Definition cc_hit_at (e1 e2 : Egg) (c1 c2 : QCirc) (g : Q) : bool :=
  let M := cc_foot c1 c2 in
  let vx := - (ccy c2 - ccy c1) in let vy := ccx c2 - ccx c1 in
  span_surd e1 M vx vy (cc_D c1 c2) g && span_surd e2 M vx vy (cc_D c1 c2) g.

Definition cc_branch (hs : list QPt) (e1 e2 : Egg) (c1 c2 : QCirc) : Outcome :=
  match cc_class c1 c2 with
  | CCoincident => Decline
  | CTangent s =>
      let p := cc_foot c1 c2 in
      if span_q e1 p && span_q e2 p then Touch p s (find_hen hs p 0) else Empty
  | CCross => if cc_hit_at e1 e2 c1 c2 1 || cc_hit_at e1 e2 c1 c2 (-1) then Hit else Empty
  | CMiss => Empty
  end.

(* -------------------------------------------------------------------------- *)
(* §3  Circle × segment.                                                       *)
(* -------------------------------------------------------------------------- *)

Definition seg_l2 (p0 p1 : QPt) : Q := sq (qx p1 - qx p0) + sq (qy p1 - qy p0).
Definition seg_t (c : QCirc) (p0 p1 : QPt) : Q :=
  ((ccx c - qx p0) * (qx p1 - qx p0) + (ccy c - qy p0) * (qy p1 - qy p0)) / seg_l2 p0 p1.
Definition seg_foot (c : QCirc) (p0 p1 : QPt) : QPt :=
  mkQPt (qx p0 + seg_t c p0 p1 * (qx p1 - qx p0)) (qy p0 + seg_t c p0 p1 * (qy p1 - qy p0)).
Definition seg_h2 (c : QCirc) (p0 p1 : QPt) : Q :=
  let f := seg_foot c p0 p1 in cr2 c - (sq (ccx c - qx f) + sq (ccy c - qy f)).

Definition cs_hit_at (e : Egg) (c : QCirc) (p0 p1 : QPt) (g : Q) : bool :=
  let D := seg_h2 c p0 p1 / seg_l2 p0 p1 in
  let s := seg_t c p0 p1 in
  surd_nonneg s g D && surd_nonneg (1 - s) (- g) D &&
  span_surd e (seg_foot c p0 p1) (qx p1 - qx p0) (qy p1 - qy p0) D g.

Definition cs_branch (hs : list QPt) (e : Egg) (c : QCirc) (p0 p1 : QPt) : Outcome :=
  if qzero (seg_l2 p0 p1) then Decline
  else
    let h := seg_h2 c p0 p1 in
    if qneg h then Empty
    else if qzero h then
      let t := seg_t c p0 p1 in let p := seg_foot c p0 p1 in
      if qnonneg t && Qle_bool t 1 && span_q e p then Touch p Ext (find_hen hs p 0)
      else Empty
    else if cs_hit_at e c p0 p1 1 || cs_hit_at e c p0 p1 (-1) then Hit else Empty.

(* -------------------------------------------------------------------------- *)
(* §4  The oracle.  [hs] = hens already on the sheet.                          *)
(* -------------------------------------------------------------------------- *)

Definition is_seg (e : Egg) : bool := match e with ESeg _ _ => true | _ => false end.

Definition kiss_oracle (hs : list QPt) (e1 e2 : Egg) : Outcome :=
  match e1, e2 with
  | ECooked, _ | _, ECooked => Decline
  | ESeg _ _, ESeg _ _ => Decline
  | ESeg p0 p1, e | e, ESeg p0 p1 =>
      match circ_of e with
      | Some c => cs_branch hs e c p0 p1
      | None => Decline
      end
  | _, _ =>
      match circ_of e1, circ_of e2 with
      | Some c1, Some c2 => cc_branch hs e1 e2 c1 c2
      | _, _ => Decline
      end
  end.

(* -------------------------------------------------------------------------- *)
(* §5  General facts about the oracle.                                         *)
(* -------------------------------------------------------------------------- *)

Lemma oracle_disc_disc : forall hs c1 c2,
  kiss_oracle hs (EDisc c1) (EDisc c2) = cc_branch hs (EDisc c1) (EDisc c2) c1 c2.
Proof. reflexivity. Qed.

(** A9, generally: coincident circles Decline, whatever the hens. *)
Theorem oracle_coincident_decline : forall hs e1 e2 c1 c2,
  cc_class c1 c2 = CCoincident ->
  cc_branch hs e1 e2 c1 c2 = Decline.
Proof. intros hs e1 e2 c1 c2 H. unfold cc_branch. rewrite H. reflexivity. Qed.

Lemma cc_class_coincident : forall c1 c2,
  d2 c1 c2 == 0 -> cr2 c1 == cr2 c2 -> cc_class c1 c2 = CCoincident.
Proof.
  intros c1 c2 Hd Hr. unfold cc_class, qzero.
  apply Qeq_bool_iff in Hd. apply Qeq_bool_iff in Hr.
  rewrite Hd, Hr. reflexivity.
Qed.

(** A Touch on two discs comes only from a CTangent classification. *)
Lemma oracle_disc_touch_class : forall hs c1 c2 p s h,
  kiss_oracle hs (EDisc c1) (EDisc c2) = Touch p s h ->
  cc_class c1 c2 = CTangent s.
Proof.
  intros hs c1 c2 p s h H.
  rewrite oracle_disc_disc in H. unfold cc_branch in H.
  destruct (cc_class c1 c2) as [| s' | |]; try discriminate.
  destruct (span_q (EDisc c1) (cc_foot c1 c2) && span_q (EDisc c2) (cc_foot c1 c2));
    [| discriminate].
  injection H as _ Hs _. subst. reflexivity.
Qed.

Close Scope Q_scope.

(* -------------------------------------------------------------------------- *)
(* §6  ℝ bridge: σ = Ext is disks_touch, σ = Int is covers.                    *)
(* -------------------------------------------------------------------------- *)

Local Open Scope R_scope.

Definition disk_of (c : QCirc) : Disk :=
  mkDisk (mkPoint (Q2R (ccx c)) (Q2R (ccy c))) (sqrt (Q2R (cr2 c))).

Lemma ctk_Q2R_zero : Q2R 0 = 0.
Proof. unfold Q2R. cbn. lra. Qed.

Lemma ctk_Q2R_four : Q2R 4 = 4.
Proof. unfold Q2R. cbn. lra. Qed.

Lemma d2_R : forall c1 c2,
  dist_sq (dcentre (disk_of c1)) (dcentre (disk_of c2)) = Q2R (d2 c1 c2).
Proof.
  intros c1 c2. unfold dist_sq, disk_of, d2, sq. cbn [dcentre px py].
  rewrite !Q2R_plus, !Q2R_mult, !Q2R_minus. ring.
Qed.

(** The two facts the classifier hands over, in ℝ. *)
Lemma cc_tangent_R : forall c1 c2 s,
  cc_class c1 c2 = CTangent s ->
  let D := Q2R (d2 c1 c2) in let x := Q2R (cr2 c1) in let y := Q2R (cr2 c2) in
  (D - x - y) * (D - x - y) = 4 * x * y /\
  (s = Ext -> 0 < D - x - y) /\ (s = Int -> D - x - y <= 0).
Proof.
  intros c1 c2 s H D x y. unfold cc_class in H.
  destruct (qzero (d2 c1 c2) && Qeq_bool (cr2 c1) (cr2 c2)); [discriminate |].
  destruct (qzero (discq c1 c2)) eqn:Hz; [| destruct (qneg (discq c1 c2)); discriminate].
  injection H as Hs.
  unfold qzero in Hz. apply Qeq_bool_eq, Qeq_eqR in Hz.
  unfold discq, sgap, sq in Hz.
  rewrite Q2R_minus, !Q2R_mult, !Q2R_minus, ctk_Q2R_four, ctk_Q2R_zero in Hz.
  split; [fold D x y in Hz; lra |].
  unfold qpos in Hs.
  destruct (Qle_bool (sgap c1 c2) 0) eqn:Hle; cbn in Hs; subst s.
  - split; [discriminate |]. intros _.
    apply Qle_bool_iff, Qle_Rle in Hle.
    unfold sgap in Hle. rewrite !Q2R_minus, ctk_Q2R_zero in Hle. exact Hle.
  - split; [| discriminate]. intros _.
    assert (Hlt : (0 < sgap c1 c2)%Q).
    { apply Qnot_le_lt. intro Hc. apply Qle_bool_iff in Hc. congruence. }
    apply Qlt_Rlt in Hlt. unfold sgap in Hlt.
    rewrite !Q2R_minus, ctk_Q2R_zero in Hlt. exact Hlt.
Qed.

(** External tangency of discs from the distance identity (the TOUCH branch
    of OverlayTouchRow.disc_relations_complete_with_touch, stated alone). *)
Lemma disks_touch_of_sum : forall A B : Disk,
  0 < dradius A -> 0 < dradius B ->
  dist (dcentre A) (dcentre B) = dradius A + dradius B ->
  disks_touch A B.
Proof.
  intros [cA r1] [cB r2] HrA HrB Heq. cbn [dcentre dradius] in *.
  assert (Hdne : dist cA cB <> 0) by lra.
  pose proof (dist_mul_self cA cB) as Hd2.
  split.
  - set (K := mkPoint (px cA + (r1 / dist cA cB) * (px cB - px cA))
                      (py cA + (r1 / dist cA cB) * (py cB - py cA))).
    assert (HKA : dist_sq cA K = (r1 / dist cA cB) * (r1 / dist cA cB) * dist_sq cA cB)
      by (unfold K, dist_sq; cbn [px py]; ring).
    assert (HKB : dist_sq cB K
                  = (1 - r1 / dist cA cB) * (1 - r1 / dist cA cB) * dist_sq cA cB)
      by (unfold K, dist_sq; cbn [px py]; ring).
    assert (HKA2 : dist_sq cA K = r1 * r1) by (rewrite HKA, <- Hd2; field; exact Hdne).
    assert (HKB2 : dist_sq cB K = r2 * r2).
    { rewrite HKB, <- Hd2. replace r2 with (dist cA cB - r1) by lra.
      field. exact Hdne. }
    exists K. unfold in_disk. cbn [dcentre dradius]. rewrite HKA2, HKB2. lra.
  - intros p [HiA HiB].
    apply in_disk_int_dist in HiA; cbn [dcentre dradius] in HiA; [| cbn; lra].
    apply in_disk_int_dist in HiB; cbn [dcentre dradius] in HiB; [| cbn; lra].
    pose proof (dist_triangle cA p cB) as Ht.
    rewrite (dist_sym p cB) in Ht. lra.
Qed.

(** HEADLINE (Ext): a σ = Ext tangency of two positive discs is TOUCH. *)
Theorem cc_ext_disks_touch : forall c1 c2,
  (0 < cr2 c1)%Q -> (0 < cr2 c2)%Q ->
  cc_class c1 c2 = CTangent Ext ->
  disks_touch (disk_of c1) (disk_of c2).
Proof.
  intros c1 c2 Ha Hb H.
  destruct (cc_tangent_R c1 c2 Ext H) as (Hsq & Hext & _).
  specialize (Hext eq_refl).
  apply Qlt_Rlt in Ha, Hb. rewrite ctk_Q2R_zero in Ha, Hb.
  set (x := Q2R (cr2 c1)) in *. set (y := Q2R (cr2 c2)) in *.
  set (D := Q2R (d2 c1 c2)) in *.
  pose proof (sqrt_lt_R0 x Ha) as Hu. pose proof (sqrt_lt_R0 y Hb) as Hv.
  pose proof (sqrt_sqrt x (Rlt_le _ _ Ha)) as Hux.
  pose proof (sqrt_sqrt y (Rlt_le _ _ Hb)) as Hvy.
  set (u := sqrt x) in *. set (v := sqrt y) in *.
  assert (HS : D - x - y = 2 * u * v).
  { assert (Hf : (D - x - y - 2 * u * v) * (D - x - y + 2 * u * v) = 0).
    { replace ((D - x - y - 2 * u * v) * (D - x - y + 2 * u * v))
        with ((D - x - y) * (D - x - y) - 4 * (u * u) * (v * v)) by ring.
      rewrite Hux, Hvy. lra. }
    assert (Huv : 0 < u * v) by (apply Rmult_lt_0_compat; assumption).
    destruct (Rmult_integral _ _ Hf); lra. }
  assert (HD : dist_sq (dcentre (disk_of c1)) (dcentre (disk_of c2))
               = (u + v) * (u + v)).
  { rewrite d2_R. fold D.
    replace ((u + v) * (u + v)) with (u * u + v * v + 2 * u * v) by ring.
    rewrite Hux, Hvy. lra. }
  apply disks_touch_of_sum;
    change (dradius (disk_of c1)) with u; change (dradius (disk_of c2)) with v;
    [exact Hu | exact Hv |].
  apply dist_eq_of_sq; [lra | exact HD].
Qed.

(** HEADLINE (Int): a σ = Int tangency of two positive discs is covers
    (one way or the other) — a pinch, not TOUCH. *)
Theorem cc_int_disk_covers : forall c1 c2,
  (0 < cr2 c1)%Q -> (0 < cr2 c2)%Q ->
  cc_class c1 c2 = CTangent Int ->
  disk_covers (disk_of c1) (disk_of c2) \/ disk_covers (disk_of c2) (disk_of c1).
Proof.
  intros c1 c2 Ha Hb H.
  destruct (cc_tangent_R c1 c2 Int H) as (Hsq & _ & Hint).
  specialize (Hint eq_refl).
  apply Qlt_Rlt in Ha, Hb. rewrite ctk_Q2R_zero in Ha, Hb.
  set (x := Q2R (cr2 c1)) in *. set (y := Q2R (cr2 c2)) in *.
  set (D := Q2R (d2 c1 c2)) in *.
  pose proof (sqrt_lt_R0 x Ha) as Hu. pose proof (sqrt_lt_R0 y Hb) as Hv.
  pose proof (sqrt_sqrt x (Rlt_le _ _ Ha)) as Hux.
  pose proof (sqrt_sqrt y (Rlt_le _ _ Hb)) as Hvy.
  set (u := sqrt x) in *. set (v := sqrt y) in *.
  assert (HS : D - x - y = - (2 * u * v)).
  { assert (Hf : (D - x - y - 2 * u * v) * (D - x - y + 2 * u * v) = 0).
    { replace ((D - x - y - 2 * u * v) * (D - x - y + 2 * u * v))
        with ((D - x - y) * (D - x - y) - 4 * (u * u) * (v * v)) by ring.
      rewrite Hux, Hvy. lra. }
    assert (Huv : 0 < u * v) by (apply Rmult_lt_0_compat; assumption).
    destruct (Rmult_integral _ _ Hf); lra. }
  assert (HD : dist_sq (dcentre (disk_of c1)) (dcentre (disk_of c2))
               = (u - v) * (u - v)).
  { rewrite d2_R. fold D.
    replace ((u - v) * (u - v)) with (u * u + v * v - 2 * u * v) by ring.
    rewrite Hux, Hvy. lra. }
  destruct (Rle_dec v u) as [Hvu | Huv].
  - left. apply covers_of_reach;
      change (dradius (disk_of c1)) with u; change (dradius (disk_of c2)) with v;
      [lra |].
    rewrite (dist_eq_of_sq _ _ (u - v)); [lra | lra | exact HD].
  - right. apply covers_of_reach;
      change (dradius (disk_of c1)) with u; change (dradius (disk_of c2)) with v;
      [lra |].
    rewrite dist_sym.
    rewrite (dist_eq_of_sq _ _ (v - u)); [lra | lra |].
    rewrite HD. ring.
Qed.

(** The oracle's disc Touch, read through σ. *)
Corollary oracle_disc_kiss_is_touch : forall hs c1 c2 p h,
  (0 < cr2 c1)%Q -> (0 < cr2 c2)%Q ->
  kiss_oracle hs (EDisc c1) (EDisc c2) = Touch p Ext h ->
  disks_touch (disk_of c1) (disk_of c2).
Proof.
  intros hs c1 c2 p h Ha Hb H.
  apply cc_ext_disks_touch; [exact Ha | exact Hb |].
  exact (oracle_disc_touch_class _ _ _ _ _ _ H).
Qed.

Corollary oracle_disc_pinch_is_covers : forall hs c1 c2 p h,
  (0 < cr2 c1)%Q -> (0 < cr2 c2)%Q ->
  kiss_oracle hs (EDisc c1) (EDisc c2) = Touch p Int h ->
  disk_covers (disk_of c1) (disk_of c2) \/ disk_covers (disk_of c2) (disk_of c1).
Proof.
  intros hs c1 c2 p h Ha Hb H.
  apply cc_int_disk_covers; [exact Ha | exact Hb |].
  exact (oracle_disc_touch_class _ _ _ _ _ _ H).
Qed.

Close Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §7  Acceptance witnesses A1–A9 (+ span-checked Hit).  Closed computations.  *)
(* -------------------------------------------------------------------------- *)

Local Open Scope Q_scope.

Definition P (x y : Z) : QPt := mkQPt (inject_Z x) (inject_Z y).
Definition Cq (x y rr : Z) : QCirc := mkQCirc (inject_Z x) (inject_Z y) (inject_Z rr).

Definition touch_is (o : Outcome) (p : QPt) (s : Sigma) (h : Hen) : bool :=
  match o with
  | Touch q s' h' =>
      peq p q &&
      match s, s' with Ext, Ext | Int, Int => true | _, _ => false end &&
      match h, h' with
      | Mint, Mint => true
      | Reuse i, Reuse j => Nat.eqb i j
      | _, _ => false
      end
  | _ => false
  end.

Definition is_hit (o : Outcome) : bool := match o with Hit => true | _ => false end.
Definition is_empty (o : Outcome) : bool := match o with Empty => true | _ => false end.
Definition is_decline (o : Outcome) : bool := match o with Decline => true | _ => false end.

(* WITNESS {"claimId":"crv-touch-kiss","topic":"overlay","lemma":"w_A1_ext_kiss","title":"A1: T-ext discs (ext_A/ext_B) are a kiss at (1,0), sigma Ext","witness":"crv-touch-A1-A9","board":"CRV-TOUCH"} *)
Example w_A1_ext_kiss :
  let o := kiss_oracle [] (EDisc (Cq 0 0 1)) (EDisc (Cq 2 0 1)) in
  touch_is o (P 1 0) Ext Mint && is_kiss o = true.
Proof. vm_compute. reflexivity. Qed.

(** A1 read in ℝ: the oracle's kiss is OverlayTouchRow's TOUCH. *)
Lemma w_A1_touch_R : disks_touch (disk_of (Cq 0 0 1)) (disk_of (Cq 2 0 1)).
Proof.
  apply (oracle_disc_kiss_is_touch [] _ _ (cc_foot (Cq 0 0 1) (Cq 2 0 1)) Mint);
    [reflexivity | reflexivity | vm_compute; reflexivity].
Qed.

(* WITNESS {"claimId":"crv-touch-kiss","topic":"overlay","lemma":"w_A2_int_pinch","title":"A2: T-int discs (int_A/int_B) touch at (2,0) with sigma Int, a pinch, not a kiss","witness":"crv-touch-A1-A9","board":"CRV-TOUCH"} *)
Example w_A2_int_pinch :
  let o := kiss_oracle [] (EDisc (Cq 0 0 4)) (EDisc (Cq 1 0 1)) in
  touch_is o (P 2 0) Int Mint && negb (is_kiss o) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma w_A2_covers_R :
  disk_covers (disk_of (Cq 0 0 4)) (disk_of (Cq 1 0 1)) \/
  disk_covers (disk_of (Cq 1 0 1)) (disk_of (Cq 0 0 4)).
Proof.
  apply (oracle_disc_pinch_is_covers [] _ _ (cc_foot (Cq 0 0 4) (Cq 1 0 1)) Mint);
    [reflexivity | reflexivity | vm_compute; reflexivity].
Qed.

(** CIRCULARSTRING (-5 0, 0 5, 5 0, 0 -5, -5 0): two arcs, two join hens. *)
Definition arc1 : Egg := EArc (P (-5) 0) (P 0 5) (P 5 0).
Definition arc2 : Egg := EArc (P 5 0) (P 0 (-5)) (P (-5) 0).
Definition joins : list QPt := [P (-5) 0; P 5 0].

(* WITNESS {"claimId":"crv-touch-kiss","topic":"overlay","lemma":"w_A3_control_point_mints","title":"A3: y=5 kisses arc 1 at its control point (0,5); a fresh hen is minted","witness":"crv-touch-A1-A9","board":"CRV-TOUCH"} *)
Example w_A3_control_point_mints :
  touch_is (kiss_oracle joins arc1 (ESeg (P (-10) 5) (P 10 5))) (P 0 5) Ext Mint = true.
Proof. vm_compute. reflexivity. Qed.

(* WITNESS {"claimId":"crv-touch-kiss","topic":"overlay","lemma":"w_A4_join_reuses","title":"A4: x=5 kisses arc 1 at the join (5,0); the join hen is reused","witness":"crv-touch-A1-A9","board":"CRV-TOUCH"} *)
Example w_A4_join_reuses :
  touch_is (kiss_oracle joins arc1 (ESeg (P 5 (-10)) (P 5 10))) (P 5 0) Ext (Reuse 1) = true.
Proof. vm_compute. reflexivity. Qed.

Example w_A5_join_same_hen :
  touch_is (kiss_oracle joins arc2 (ESeg (P 5 (-10)) (P 5 10))) (P 5 0) Ext (Reuse 1) = true.
Proof. vm_compute. reflexivity. Qed.

Example w_A6_tangent_off_span :
  is_empty (kiss_oracle joins arc1 (ESeg (P (-10) (-5)) (P 10 (-5)))) = true.
Proof. vm_compute. reflexivity. Qed.

Example w_A7_crossing_hit :
  is_hit (kiss_oracle [] (EDisc (Cq 0 0 1)) (EDisc (Cq 1 0 1))) = true.
Proof. vm_compute. reflexivity. Qed.

Example w_A8_cooked_decline :
  is_decline (kiss_oracle [] ECooked (EDisc (Cq 0 0 1))) = true.
Proof. vm_compute. reflexivity. Qed.

(* WITNESS {"claimId":"crv-touch-kiss","topic":"overlay","lemma":"w_A9_coincident_decline","title":"A9: coincident discs Decline before the tangency point; never Touch","witness":"crv-touch-A1-A9","board":"CRV-TOUCH"} *)
Example w_A9_coincident_decline :
  is_decline (kiss_oracle [] (EDisc (Cq 0 0 1)) (EDisc (Cq 0 0 1))) = true.
Proof. vm_compute. reflexivity. Qed.

(** Co-circular arcs (arc 1 and arc 2 share their circle) also Decline. *)
Example w_cocircular_decline : is_decline (kiss_oracle joins arc1 arc2) = true.
Proof. vm_compute. reflexivity. Qed.

Example w_zero_length_segment_decline :
  is_decline (kiss_oracle [] (EDisc (Cq 0 0 1)) (ESeg (P 3 3) (P 3 3))) = true.
Proof. vm_compute. reflexivity. Qed.

(** Span-checked Hit: y = 3 crosses arc 1 at (±4, 3), inside the span ... *)
Example w_secant_in_span_hit :
  is_hit (kiss_oracle joins arc1 (ESeg (P (-10) 3) (P 10 3))) = true.
Proof. vm_compute. reflexivity. Qed.

(** ... y = −3 crosses the circle at (±4, −3), outside arc 1: Empty. *)
Example w_secant_off_span_empty :
  is_empty (kiss_oracle joins arc1 (ESeg (P (-10) (-3)) (P 10 (-3)))) = true.
Proof. vm_compute. reflexivity. Qed.

(** Circle × arc with irrational crossings (y = −5/2, x = ±√(75)/2):
    the span test runs on a + b·√D and finds both below arc 1. *)
Example w_cc_surd_off_span_empty :
  is_empty (kiss_oracle [] arc1 (EDisc (Cq 0 (-5) 25))) = true.
Proof. vm_compute. reflexivity. Qed.

Example w_cc_surd_in_span_hit :
  is_hit (kiss_oracle [] arc1 (EDisc (Cq 0 5 25))) = true.
Proof. vm_compute. reflexivity. Qed.

Close Scope Q_scope.

Print Assumptions cc_ext_disks_touch.
Print Assumptions cc_int_disk_covers.
