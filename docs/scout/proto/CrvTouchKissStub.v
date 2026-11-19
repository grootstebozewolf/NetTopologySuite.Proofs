(* ============================================================================
   CRV-TOUCH · kiss oracle stub on the rational plane — THROWAWAY PROTOTYPE
   ----------------------------------------------------------------------------
   Board: "CRV-TOUCH · Stub the kiss oracle on R² for the three witnesses".
   Something to react to, not a proof.  Not in _CoqProject; never merged into
   theories/.  Every check below is a closed computation (vm_compute), so it
   says nothing about any input not listed here.

   Encodes the Architect grill of 2026-11-19 (Notion CRV-TOUCH map):
     Q1  decide by exact-Q discq = 0 (here: (d²−r₁²−r₂²)² = 4 r₁² r₂²)
     Q2  only uncooked input eggs; cooked / irrational input → Decline
     Q3  outcome shape unchanged: Touch | Empty | Decline | Hit
     Q4  certificate σ = sign(d² − r₁² − r₂²) ∈ {Ext, Int}; arc–line → Ext
     Q5  hen point is rational; rounding to binary64 is output-only (absent)
     Q6  reuse an existing hen iff Q-equal; control points are never hens
     Q7  "kiss" = σ = Ext; an Int tangency is a pinch (covers, not TOUCH)
   ========================================================================== *)

From Stdlib Require Import QArith List Bool.
Import ListNotations.
Open Scope Q_scope.

Record Pt := mkPt { px : Q; py : Q }.
Record Circ := mkCirc { cx : Q; cy : Q; r2 : Q }.

(* An arc egg: three rational WKT points on its circle.  Only [a0]/[a2] are
   hens; [a1] is the mid control point — egg data (Q6). *)
Record Arc := mkArc { acirc : Circ; a0 : Pt; a1 : Pt; a2 : Pt }.
Record Seg := mkSeg { s0 : Pt; s1 : Pt }.

Inductive Egg := EArc (a : Arc) | EDisc (c : Circ) | ESeg (s : Seg)
               | ECooked.             (* already split at a √ hen (Q2) *)

Inductive Sigma := Ext | Int.
Inductive Hen := Reuse (i : nat) | Mint.
Inductive Outcome :=
  | Touch (p : Pt) (s : Sigma) (h : Hen)  (* tangency hen; kiss iff s = Ext *)
  | Hit | Empty | Decline.

Definition peq (p q : Pt) : bool := Qeq_bool (px p) (px q) && Qeq_bool (py p) (py q).
Definition qpos x := negb (Qle_bool x 0).
Definition qneg x := negb (Qle_bool 0 x).
Definition qzero x := Qeq_bool x 0.

Definition sq x := x * x.
Definition orient (a b c : Pt) : Q :=
  (px b - px a) * (py c - py a) - (py b - py a) * (px c - px a).

(* p (known on the circle) lies in arc a0→a1→a2: an endpoint, or strictly
   on a1's side of chord a0a2.  Exact Q, no angle. *)
Definition in_arc (a : Arc) (p : Pt) : bool :=
  peq p (a0 a) || peq p (a2 a) ||
  (let s := orient (a0 a) (a2 a) (a1 a) * orient (a0 a) (a2 a) p in qpos s).

(* Q6: rational equality against the existing hen list. *)
Fixpoint find_hen (hs : list Pt) (p : Pt) (i : nat) : Hen :=
  match hs with
  | [] => Mint
  | h :: t => if peq h p then Reuse i else find_hen t p (S i)
  end.

(* ---- circle × circle ----------------------------------------------------- *)
Definition d2 (c1 c2 : Circ) := sq (cx c2 - cx c1) + sq (cy c2 - cy c1).
Definition sgap (c1 c2 : Circ) := d2 c1 c2 - r2 c1 - r2 c2.          (* Q4 *)
Definition discq0 (c1 c2 : Circ) := qzero (sq (sgap c1 c2) - 4 * r2 c1 * r2 c2).
Definition crosses (c1 c2 : Circ) := qneg (sq (sgap c1 c2) - 4 * r2 c1 * r2 c2).
Definition cc_point (c1 c2 : Circ) : Pt :=
  let k := (d2 c1 c2 + r2 c1 - r2 c2) / (2 * d2 c1 c2) in
  mkPt (cx c1 + k * (cx c2 - cx c1)) (cy c1 + k * (cy c2 - cy c1)).

(* ---- circle × segment ---------------------------------------------------- *)
Definition foot (c : Circ) (s : Seg) : Q * Pt :=
  let dx := px (s1 s) - px (s0 s) in let dy := py (s1 s) - py (s0 s) in
  let t := ((cx c - px (s0 s)) * dx + (cy c - py (s0 s)) * dy) / (sq dx + sq dy) in
  (t, mkPt (px (s0 s) + t * dx) (py (s0 s) + t * dy)).
Definition h2 (c : Circ) (s : Seg) :=
  let f := snd (foot c s) in r2 c - (sq (cx c - px f) + sq (cy c - py f)).
Definition in_seg (s : Seg) (t : Q) := Qle_bool 0 t && Qle_bool t 1.

Definition circ_of (e : Egg) : option Circ :=
  match e with EArc a => Some (acirc a) | EDisc c => Some c | _ => None end.
Definition span_ok (e : Egg) (p : Pt) : bool :=
  match e with EArc a => in_arc a p | _ => true end.

(* The oracle.  [hs] = hens already on the sheet (input endpoints / joins). *)
Definition kiss_oracle (hs : list Pt) (e1 e2 : Egg) : Outcome :=
  match e1, e2 with
  | ECooked, _ | _, ECooked => Decline
  | ESeg _, ESeg _ => Decline                    (* not this oracle's case *)
  | ESeg s, e | e, ESeg s =>
      match circ_of e with
      | None => Decline
      | Some c =>
          let h := h2 c s in
          if qneg h then Empty
          else if qpos h then Hit                (* secant; spans not checked *)
          else let '(t, p) := foot c s in
               if in_seg s t && span_ok e p then Touch p Ext (find_hen hs p 0)
               else Empty
      end
  | _, _ =>
      match circ_of e1, circ_of e2 with
      | Some c1, Some c2 =>
          if crosses c1 c2 then Hit
          else if negb (discq0 c1 c2) then Empty
          else let p := cc_point c1 c2 in
               if span_ok e1 p && span_ok e2 p then
                 Touch p (if qpos (sgap c1 c2) then Ext else Int) (find_hen hs p 0)
               else Empty
      | _, _ => Decline
      end
  end.

Definition is_kiss (o : Outcome) : bool :=
  match o with Touch _ Ext _ => true | _ => false end.            (* Q7 *)

(* ============================================================================
   Witnesses
   ========================================================================== *)
Definition P x y := mkPt (inject_Z x) (inject_Z y).
Definition C x y rr := mkCirc (inject_Z x) (inject_Z y) (inject_Z rr).

Definition touch_at (o : Outcome) (p : Pt) (s : Sigma) (h : Hen) : bool :=
  match o, s, h with
  | Touch q Ext (Reuse i), Ext, Reuse j => peq p q && Nat.eqb i j
  | Touch q Ext Mint, Ext, Mint => peq p q
  | Touch q Int Mint, Int, Mint => peq p q
  | Touch q Int (Reuse i), Int, Reuse j => peq p q && Nat.eqb i j
  | _, _, _ => false
  end.

(* 1. T-ext — OverlayTouchRow.ext_A / ext_B: kiss at (1,0), σ = Ext. *)
Example w_ext :
  let o := kiss_oracle [] (EDisc (C 0 0 1)) (EDisc (C 2 0 1)) in
  touch_at o (P 1 0) Ext Mint = true /\ is_kiss o = true.
Proof. split; vm_compute; reflexivity. Qed.

(* 2. T-int — OverlayTouchRow.int_A / int_B: tangency at (2,0), σ = Int —
      a pinch, NOT a kiss (t_int_is_covers_not_kiss). *)
Example w_int :
  let o := kiss_oracle [] (EDisc (C 0 0 4)) (EDisc (C 1 0 1)) in
  touch_at o (P 2 0) Int Mint = true /\ is_kiss o = false.
Proof. split; vm_compute; reflexivity. Qed.

(* 3. Arc–line on CIRCULARSTRING (-5 0, 0 5, 5 0, 0 -5, -5 0), r = 5.
      Hens on the sheet: the two joins (-5,0) [0] and (5,0) [1]. *)
Definition c5 := C 0 0 25.
Definition arc1 := mkArc c5 (P (-5) 0) (P 0 5) (P 5 0).
Definition arc2 := mkArc c5 (P 5 0) (P 0 (-5)) (P (-5) 0).
Definition joins := [P (-5) 0; P 5 0].

(* 3a. y = 5, chord (−10,5)→(10,5): kiss at the mid CONTROL point (0,5),
       which is egg data, so a fresh hen is minted (Q6). *)
Example w_line_top :
  touch_at (kiss_oracle joins (EArc arc1) (ESeg (mkSeg (P (-10) 5) (P 10 5))))
           (P 0 5) Ext Mint = true.
Proof. vm_compute; reflexivity. Qed.

(* 3b. x = 5, chord (5,−10)→(5,10): kiss at the join (5,0) → reuse hen [1]. *)
Example w_line_join :
  touch_at (kiss_oracle joins (EArc arc1) (ESeg (mkSeg (P 5 (-10)) (P 5 10))))
           (P 5 0) Ext (Reuse 1) = true.
Proof. vm_compute; reflexivity. Qed.

(* 3c. Same circle, other arc, same join: one hen, the same index (Q6). *)
Example w_line_join_arc2 :
  touch_at (kiss_oracle joins (EArc arc2) (ESeg (mkSeg (P 5 (-10)) (P 5 10))))
           (P 5 0) Ext (Reuse 1) = true.
Proof. vm_compute; reflexivity. Qed.

(* ---- the other outcomes (Q3 shape) ---------------------------------------- *)
Example w_empty_span :   (* y = −5 kisses the circle at (0,−5), outside arc1 *)
  kiss_oracle joins (EArc arc1) (ESeg (mkSeg (P (-10) (-5)) (P 10 (-5)))) = Empty.
Proof. vm_compute; reflexivity. Qed.

Example w_hit :          (* crossing discs: Hit, never Touch *)
  kiss_oracle [] (EDisc (C 0 0 1)) (EDisc (C 1 0 1)) = Hit.
Proof. vm_compute; reflexivity. Qed.

Example w_decline :      (* cooked input: Decline, not decided (Q2) *)
  kiss_oracle [] ECooked (EDisc (C 0 0 1)) = Decline.
Proof. vm_compute; reflexivity. Qed.

(* Known stub gaps (deliberate; for the spec, not this file):
   - Hit does not check spans; a secant outside both spans should be Empty.
   - Overlapping co-circular arcs (Q6 → Decline) are not detected.
   - No ℝ statement: nothing here relates kiss_oracle to Disk.in_disk. *)
