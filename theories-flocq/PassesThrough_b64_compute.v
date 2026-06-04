(* ============================================================================
   NetTopologySuite.Proofs.Flocq.PassesThrough_b64_compute
   ----------------------------------------------------------------------------
   COMPUTATIONAL (extractable) binary64 Liang-Barsky hot-pixel passes-through
   predicates -- the oracle compute path for the RocqRefRunner PASSES_THROUGH_*
   modes.

   Why this file exists.  `HotPixel_b64.b64_liang_barsky_touches` (and the
   half-open analog in `PassesThroughHalfopen_b64.v`) are SPECIFICATIONS: they
   read coordinates through `Binary.B2R ... : R` and decide with exact real
   arithmetic (`Rmax`/`Rmin`/`Rle_bool`/`Req_dec_T`).  Coq's `R` is
   non-computational, so those functions cannot be extracted to runnable OCaml.
   Before this file, `oracle/driver.ml` hand-rolled the native-float predicate
   directly (the credibility gap tracked in
   docs/oracle-handroll-migration.md).

   These definitions compute on the `binary64` layer (`b64_minus`/`b64_div`/
   `b64_le`/...), so they extract to native float code and are bit-exact with
   the C# differential reference.  They mirror, operation for operation, the
   native `lb_*` / `passes_through_*` kernels that previously lived in
   driver.ml, so the extracted oracle reproduces the established differential
   corpus.

   SOUNDNESS STATUS.  Because `b64_div` rounds (it is not exact even in the
   integer regime, Validate_binary64.v:142), these rounded predicates are NOT
   provably equal to the exact R-specs above; the bridge to
   `b64_segment_touches_hot_pixel_closed_spec` is a forward-error / integer-
   regime result, deferred (docs/oracle-handroll-migration.md item 1).  This
   file makes NO soundness claim -- it is the de-hand-rolled compute path, with
   the algorithm now single-sourced in Coq instead of transcribed into OCaml.

   Extraction overrides live in `Validate_binary64_extract.v`:
     - b64_min / b64_max  -> Float.min / Float.max
     - b64_one/two/half   -> native literals (their binary_normalize bodies
                             would otherwise hit the B754_finite ctor stub)
     - b64_snap_coord     -> native round-half-to-even (matches Bnearbyint NE)
   ========================================================================== *)

From Flocq Require Import IEEE754.Binary.
From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import HotPixel_b64.

(* Positive zero, matching the native `0.0`.  Defined via the constructor so
   extraction emits 0.0 directly (no binary_normalize / B754_finite stub). *)
Definition b64_zero : binary64 := Binary.B754_zero prec emax false.

(* Boolean IEEE equality (Some Eq).  Matches native polymorphic `=` on the
   finite coordinates reached here. *)
Definition b64_eqb (x y : binary64) : bool :=
  match b64_compare x y with Some Eq => true | _ => false end.

(* Operand-selecting min/max.  On the finite t-bounds reached here these
   coincide with OCaml's Float.min / Float.max (to which they are extracted). *)
Definition b64_min (x y : binary64) : binary64 := if b64_le x y then x else y.
Definition b64_max (x y : binary64) : binary64 := if b64_le x y then y else x.

(* Per-axis degenerate-slab guards.  Closed (FILTER) and half-open variants,
   mirroring driver.ml's lb_inslab_closed / lb_inslab_halfopen. *)
Definition b64_lb_inslab_closed (c0 c1 lo hi : binary64) : bool :=
  if b64_eqb c1 c0 then andb (b64_le lo c0) (b64_le c0 hi) else true.

Definition b64_lb_inslab_halfopen (c0 c1 lo hi : binary64) : bool :=
  if b64_eqb c1 c0 then andb (b64_le lo c0) (b64_lt c0 hi) else true.

(* Per-axis t-bounds; degenerate axis clipped to [0,1]. *)
Definition b64_lb_tlo (c0 c1 lo hi : binary64) : binary64 :=
  if b64_eqb c1 c0 then b64_zero
  else b64_min (b64_div (b64_minus lo c0) (b64_minus c1 c0))
               (b64_div (b64_minus hi c0) (b64_minus c1 c0)).

Definition b64_lb_thi (c0 c1 lo hi : binary64) : binary64 :=
  if b64_eqb c1 c0 then b64_one
  else b64_max (b64_div (b64_minus lo c0) (b64_minus c1 c0))
               (b64_div (b64_minus hi c0) (b64_minus c1 c0)).

(* Closed-filter Liang-Barsky touch (mirror of driver.ml lb_touches). *)
Definition b64_liang_barsky_touches_compute (P0 P1 C : BPoint) : bool :=
  let x0 := bx P0 in let y0 := by_ P0 in
  let x1 := bx P1 in let y1 := by_ P1 in
  let cx := bx C  in let cy := by_ C  in
  let xlo := b64_minus cx b64_half in let xhi := b64_plus cx b64_half in
  let ylo := b64_minus cy b64_half in let yhi := b64_plus cy b64_half in
  andb (andb (b64_lb_inslab_closed x0 x1 xlo xhi)
             (b64_lb_inslab_closed y0 y1 ylo yhi))
       (b64_le (b64_max b64_zero
                  (b64_max (b64_lb_tlo x0 x1 xlo xhi) (b64_lb_tlo y0 y1 ylo yhi)))
               (b64_min b64_one
                  (b64_min (b64_lb_thi x0 x1 xlo xhi) (b64_lb_thi y0 y1 ylo yhi)))).

(* Half-open-filter Liang-Barsky touch (mirror of driver.ml
   lb_touches_halfopen): closed slab guards + non-empty clipped interval +
   strict-upper midpoint witness on both axes. *)
Definition b64_liang_barsky_touches_halfopen_compute (P0 P1 C : BPoint) : bool :=
  let x0 := bx P0 in let y0 := by_ P0 in
  let x1 := bx P1 in let y1 := by_ P1 in
  let cx := bx C  in let cy := by_ C  in
  let xlo := b64_minus cx b64_half in let xhi := b64_plus cx b64_half in
  let ylo := b64_minus cy b64_half in let yhi := b64_plus cy b64_half in
  let tmin := b64_max b64_zero
                (b64_max (b64_lb_tlo x0 x1 xlo xhi) (b64_lb_tlo y0 y1 ylo yhi)) in
  let tmax := b64_min b64_one
                (b64_min (b64_lb_thi x0 x1 xlo xhi) (b64_lb_thi y0 y1 ylo yhi)) in
  let tmid := b64_div (b64_plus tmin tmax) b64_two in
  let xmid := b64_plus (b64_mult (b64_minus b64_one tmid) x0) (b64_mult tmid x1) in
  let ymid := b64_plus (b64_mult (b64_minus b64_one tmid) y0) (b64_mult tmid y1) in
  andb (andb (andb (b64_lb_inslab_halfopen x0 x1 xlo xhi)
                   (b64_lb_inslab_halfopen y0 y1 ylo yhi))
             (b64_le tmin tmax))
       (andb (b64_lt xmid xhi) (b64_lt ymid yhi)).

(* Passes-through: touch on the original AND the snapped segment.  Reuses the
   computational b64_snap (= b64_snap_coord on each axis) from HotPixel_b64. *)
Definition b64_passes_through_hot_pixel_compute (P0 P1 C : BPoint) : bool :=
  andb (b64_liang_barsky_touches_compute P0 P1 C)
       (b64_liang_barsky_touches_compute (b64_snap P0) (b64_snap P1) C).

Definition b64_passes_through_hot_pixel_halfopen_compute (P0 P1 C : BPoint) : bool :=
  andb (b64_liang_barsky_touches_halfopen_compute P0 P1 C)
       (b64_liang_barsky_touches_halfopen_compute (b64_snap P0) (b64_snap P1) C).
