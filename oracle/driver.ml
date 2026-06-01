(* =============================================================================
   oracle/driver.ml
   -----------------------------------------------------------------------------
   Stdin/stdout adapter around the Coq-extracted functions in `extracted.ml`.
   This is the RocqRefRunner binary used by the differential test harness in
   NetTopologySuite.Curve.

   Protocol (text, ASCII).  The first non-blank line is the mode:

     SIMPLIFY        -- greedy perpendicular-distance polyline simplifier.
        line 2:       <eps>
        lines 3..N:   <x> <y>
        EOF           terminates the polyline.
        output:       one "<x> <y>" hex-float line per kept point.

     ORIENT          -- 2D orientation predicate, naive layer.
        line 2:       <x0> <y0>
        line 3:       <x1> <y1>
        line 4:       <x2> <y2>
        EOF.
        output:       single line "<sign> <signed_area_hex>".
                      sign is one of: POS / NEG / ZERO / NAN.

     ORIENT_FILTERED -- 2D orientation with Shewchuk Stage A filter.
        line 2..4:    points as above.
        output:       single line "<sign> <signed_area_hex>".
                      sign is one of: POS / NEG / ZERO / NAN / UNCERTAIN.

     INTERSECT_FILTERED -- segment-pair intersection predicate, Stage A.
        line 2:       <x0> <y0>     -- P0
        line 3:       <x1> <y1>     -- P1
        line 4:       <xq0> <yq0>   -- Q0
        line 5:       <xq1> <yq1>   -- Q1
        EOF.
        output:       single token "<sign>".
                      sign is one of: NONE / POINT / COLLINEAR / NAN / UNCERTAIN.

     INTERSECT_POINT_FILTERED -- intersection point coordinates.
        line 2..5:    four points as above.
        EOF.
        output:       single line, one of:
                        "NONE"                 (no intersection or non-Point result)
                        "POINT <x_hex> <y_hex>" (rounded intersection coordinates)

     INTERSECT_POINT_XY -- intersection point coordinates via verified
                           total projections (Phase 1 Scope C.2-tight).
        line 2..5:    four points as above.
        EOF.
        output:       single line "XY <x_hex> <y_hex>" -- unconditional
                      output of `b64_intersect_point_x` / `_y` from
                      `Intersect_b64_exact.v`.  No option layer and no
                      filter pre-check: callers responsible for first
                      consulting `INTERSECT_FILTERED` (or holding the
                      `intersect_point_inputs_int_safe` precondition
                      externally) to determine whether the returned
                      coordinates are meaningful.  Outside that regime
                      the totals still return a binary64, but its
                      relation to the geometric intersection is not
                      formally guaranteed -- see
                      `b64_intersect_point_x_forward_error_vs_intersect_x_R`
                      for the verified soundness statement.

     PASSES_THROUGH_FILTER -- hot-pixel passes-through, closed-pixel filter.
        line 2:       <x0> <y0>     -- P0   (segment endpoint)
        line 3:       <x1> <y1>     -- P1   (segment endpoint)
        line 4:       <cx> <cy>     -- C    (hot pixel center, unit grid)
        output:       single token "TRUE" or "FALSE".
        Coq mirror:   `b64_passes_through_hot_pixel` (HotPixel_b64.v:2374).
                      Sound vs the CLOSED hot pixel, complete vs the
                      HALF-OPEN hot pixel.

     PASSES_THROUGH_HALFOPEN -- hot-pixel passes-through, half-open filter.
        line 2:       <x0> <y0>     -- P0
        line 3:       <x1> <y1>     -- P1
        line 4:       <cx> <cy>     -- C    (hot pixel center)
        output:       single token "TRUE" or "FALSE".
        Coq mirror:   `b64_passes_through_hot_pixel_halfopen`
                      (PassesThroughHalfopen_b64.v).  Sound AND complete
                      vs the HALF-OPEN hot pixel.

   Option-layer pin (oracle-level, mirrors the Coq bracket lemma):
       HALFOPEN = TRUE  =>  FILTER = TRUE.
   Divergence cases (closed accepts, half-open rejects) characterise the
   boundary category -- segments grazing the closed upper boundary x=xhi
   (or y=yhi) of the unit-grid pixel.

     EDGE_IN_RESULT  -- boolean overlay-result membership for an edge.
        line 2:       <op>         UNION | INTERSECTION | DIFFERENCE | SYMDIFF
        line 3:       <in_left>    true | false
        line 4:       <in_right>   true | false
        output:       single token "TRUE" or "FALSE".
        Coq mirror:   `edge_in_result` (OverlayGraph.v:375), DIRECTLY
                      extracted -- no native mirror.  Pure bool
                      computation over BooleanOp + EdgeLabel.

     INCIRCLE_SIGN   -- 4-point in-circle determinant sign.
        line 2..5:    A, B, C, P (four BPoints, one per line)
        output:       single line "<sign> <det_hex>".
                      sign is one of: POS / NEG / ZERO / NAN.
        Coq mirror:   `inCircle_R` (ArcOrient.v:88), HAND-ROLLED native
                      arithmetic (Phase 4 R-side; no b64 bridge yet).
                      POS iff (A,B,C) is CCW AND P strictly inside the
                      circumscribed circle.  CW flips the sign.

     ARC_CHORD_CROSSES_CIRCLE -- bool sufficient condition for an arc's
                                 circumcircle being crossed by a chord.
        line 2..6:    arc_start, arc_mid, arc_end, chord_P, chord_Q
                      (five BPoints, one per line)
        output:       single token "TRUE" or "FALSE".
        Coq mirror:   `chord_crosses_arc_circle` (ArcIntersect.v:129) +
                      IVT-witnessed `chord_crosses_arc_circle_implies_
                      circle_intersection` (ArcIntersectIVT.v).
                      HAND-ROLLED: sign-product of inCircle_R at the two
                      chord endpoints.  SUFFICIENT only -- TRUE => chord
                      crosses circumcircle; FALSE does NOT imply
                      non-crossing (both endpoints same side may still
                      cross twice).

     ARC_PASSES_THROUGH_PIXEL -- bool sufficient condition for an arc
                                 passing through a hot pixel.
        line 2..5:    arc_start, arc_mid, arc_end, pixel_center (four
                      BPoints)
        line 6:       <scale>   pixel-side length as a float (e.g. 1.0
                                for unit-grid pixels)
        output:       single token "TRUE" or "FALSE".
        Coq mirror:   `arc_passes_through_hot_pixel` (ArcHotPixel.v:95)
                      six-way disjunction: 4 edge-crossing sign tests +
                      2 endpoint-in-pixel tests.  Endpoint tests use the
                      half-open convention (bottom + left CLOSED, top +
                      right OPEN).  SUFFICIENT only.

     CLOTHOID_INTERSECT -- chord-length parameter L of a clothoid (Euler
                           spiral) segment via Halley iteration on the
                           G^1 Hermite L-form residual.  TOLERANCE oracle
                           (see the mode comment): there is no Flocq-side
                           `b64_clothoid_intersect` yet, so this realises
                           the R-side mathematics numerically rather than
                           bit-exactly.
        line 2:       <kappa_0>    curvature at tau=0
        line 3:       <kappa_1>    curvature at tau=1
        line 4:       <d>          target chord length (>= 0)
        line 5:       <L0>         initial guess for L (> 0)
        line 6:       <max_iters>  iteration cap (decimal integer)
        output:       single line "<status> <L_hex> <iters>".
                      status is one of: CONV / MAXITER / NAN.
        Reference:    `HasClothoidIntersect` aspirational block in
                      `theories-flocq/Intersect_b64_exact.v` +
                      `docs/audit-phase4-curves.md` 6.1.  R-side
                      derivative identities proved (and CITED, not
                      imported) in the companion proprietary corpus
                      `clothoid-halley-coq` (Merkator Group, 2026).

   Numeric tokens go through OCaml `float_of_string`, so any IEEE 754
   binary64 spelling works -- decimal ("0.5"), hex ("0x1p-1"),
   "infinity", "neg_infinity", "nan".  Output uses "%h" (hex-float) so
   consumers can round-trip bits exactly.

   Persistent-mode dispatch.  All modes except SIMPLIFY return after
   emitting their reply and loop back to read the next mode line.  This
   lets a long-running C# differential test process keep a single
   oracle_bin instance alive across many calls.  SIMPLIFY exits the
   process (it reads its input until EOF, so a subsequent mode line
   would be misinterpreted).  EOF on the mode-reading branch shuts
   down cleanly.
   ========================================================================== *)

open Extracted

(* ----- Common: point parsing + hex output. ------------------------------- *)

let parse_point line =
  match String.split_on_char ' ' (String.trim line) with
  | [x; y] -> { bx = float_of_string x; by_ = float_of_string y }
  | _ -> failwith (Printf.sprintf "oracle: bad point line: %s" line)

let print_point bp =
  Printf.printf "%h %h\n" bp.bx bp.by_

(* ----- SIMPLIFY mode. ----------------------------------------------------- *)

let read_simplify_input () =
  let eps = float_of_string (String.trim (input_line stdin)) in
  let rec loop acc =
    match try Some (input_line stdin) with End_of_file -> None with
    | None -> List.rev acc
    | Some raw ->
      let line = String.trim raw in
      if line = "" then loop acc
      else loop (parse_point line :: acc)
  in
  (eps, loop [])

let run_simplify () =
  let (eps, pts) = read_simplify_input () in
  let result = greedy_simplify_perp_b64 eps pts in
  List.iter print_point result

(* ----- ORIENT mode. ------------------------------------------------------- *)

let sign_string = function
  | OrientPos  -> "POS"
  | OrientNeg  -> "NEG"
  | OrientZero -> "ZERO"
  | OrientNan  -> "NAN"

let run_orient () =
  let p0 = parse_point (input_line stdin) in
  let p1 = parse_point (input_line stdin) in
  let q  = parse_point (input_line stdin) in
  let s = b64_orient_sign_naive p0 p1 q in
  let v = b64_orient2d p0 p1 q in
  Printf.printf "%s %h\n" (sign_string s) v

let sign_robust_string = function
  | OrientRPos       -> "POS"
  | OrientRNeg       -> "NEG"
  | OrientRZero      -> "ZERO"
  | OrientRNan       -> "NAN"
  | OrientRUncertain -> "UNCERTAIN"

let run_orient_filtered () =
  let p0 = parse_point (input_line stdin) in
  let p1 = parse_point (input_line stdin) in
  let q  = parse_point (input_line stdin) in
  let s = b64_orient_sign_filtered p0 p1 q in
  let v = b64_orient2d p0 p1 q in
  Printf.printf "%s %h\n" (sign_robust_string s) v

(* ----- INTERSECT_FILTERED mode. ------------------------------------------ *)

let intersect_sign_string = function
  | IntersectNone      -> "NONE"
  | IntersectPoint     -> "POINT"
  | IntersectCollinear -> "COLLINEAR"
  | IntersectNan       -> "NAN"
  | IntersectUncertain -> "UNCERTAIN"

let run_intersect_filtered () =
  let p0 = parse_point (input_line stdin) in
  let p1 = parse_point (input_line stdin) in
  let q0 = parse_point (input_line stdin) in
  let q1 = parse_point (input_line stdin) in
  let s = b64_intersect_sign_filtered p0 p1 q0 q1 in
  Printf.printf "%s\n" (intersect_sign_string s)

(* ----- INTERSECT_POINT_FILTERED mode. ------------------------------------ *)

let run_intersect_point_filtered () =
  let p0 = parse_point (input_line stdin) in
  let p1 = parse_point (input_line stdin) in
  let q0 = parse_point (input_line stdin) in
  let q1 = parse_point (input_line stdin) in
  match b64_intersect_point p0 p1 q0 q1 with
  | None    -> print_endline "NONE"
  | Some bp -> Printf.printf "POINT %h %h\n" bp.bx bp.by_

(* ----- INTERSECT_POINT_XY mode. ------------------------------------------ *)

(* Calls the verified total projections b64_intersect_point_x / _y from
   `theories-flocq/Intersect_b64_exact.v` (Phase 1 Scope C.2-tight) directly,
   without the option-wrapping or pre-filter check.  Useful for the .Curve
   C# differential corpus when comparing bit-for-bit against a C# port that
   pattern-matches on the predicate first and then computes coordinates
   unconditionally on the IntersectPoint branch. *)
let run_intersect_point_xy () =
  let p0 = parse_point (input_line stdin) in
  let p1 = parse_point (input_line stdin) in
  let q0 = parse_point (input_line stdin) in
  let q1 = parse_point (input_line stdin) in
  let x = b64_intersect_point_x p0 p1 q0 q1 in
  let y = b64_intersect_point_y p0 p1 q0 q1 in
  Printf.printf "XY %h %h\n" x y

(* ----- PASSES_THROUGH_FILTER / PASSES_THROUGH_HALFOPEN modes. ------------ *)

(* Native OCaml mirrors of the corpus's hot-pixel predicates.  Equivalent
   to extracting `b64_passes_through_hot_pixel` and `_halfopen` from
   `HotPixel_b64.v` / `PassesThroughHalfopen_b64.v`, with the same trust
   pattern as the existing `Bplus -> ( +. )` extracts: on IEEE 754
   binary64 hardware in round-to-nearest-even mode (the OCaml default
   under SSE2/NEON, which is what oracle_bin runs on), native float ops
   realise Flocq's R semantics for the operations used in the LB filter.

   Implemented directly here -- not via Coq's `Extract Constant` -- to
   sidestep the R-module hierarchy that Coq's stdlib emits for
   `Reals.Rdefinitions.RbaseSymbolsImpl` (abstract `coq_R` type via a
   module signature, distinct from the toplevel `Rplus` symbol that
   `Extract Inlined Constant` reaches).  The corpus's bracket lemma
   `b64_passes_through_hot_pixel_halfopen_implies_closed` is the
   formally-proved option-layer pin; this code is the runtime mirror. *)

(* Round to nearest integer with ties to even (IEEE 754 default, the
   semantics of `Bnearbyint mode_NE` from HotPixel_b64.v's b64_snap_coord).
   OCaml 4.14 stdlib's `Float.round` is half-away-from-zero, so we
   implement half-to-even via floor + parity-of-remainder. *)
let round_half_to_even (x : float) : float =
  if x <> x then x                                  (* NaN passthrough *)
  else if x = infinity || x = neg_infinity then x   (* infinities pass *)
  else
    let f = Float.floor x in
    let d = x -. f in
    if d < 0.5 then f
    else if d > 0.5 then f +. 1.0
    else if Float.rem f 2.0 = 0.0 then f else f +. 1.0

let snap_coord_native (x : float) : float = round_half_to_even x

let snap_native (p : bPoint) : bPoint =
  { bx = snap_coord_native p.bx; by_ = snap_coord_native p.by_ }

(* Per-axis slab membership for the degenerate (axis-parallel) case.
   Non-degenerate axes pass through unconditionally (the t-bounds carry
   the constraint).  Closed variant for the FILTER mode. *)
let lb_inslab_closed c0 c1 lo hi : bool =
  if c1 = c0 then lo <= c0 && c0 <= hi else true

(* Half-open variant: strict upper, matching `in_hot_pixel`'s `< xhi`
   on the upper bound. *)
let lb_inslab_halfopen c0 c1 lo hi : bool =
  if c1 = c0 then lo <= c0 && c0 < hi else true

(* Per-axis t-bounds.  For non-degenerate axes the two t-values
   (lo - c0)/(c1 - c0) and (hi - c0)/(c1 - c0) sit at the slab boundaries;
   `lb_tlo` is the smaller and `lb_thi` is the larger, regardless of
   orientation.  Degenerate case returns [0, 1] (the segment parameter
   range itself) so the t-overlap check below reduces to "non-empty
   segment". *)
let lb_tlo c0 c1 lo hi : float =
  if c1 = c0 then 0.0
  else Float.min ((lo -. c0) /. (c1 -. c0)) ((hi -. c0) /. (c1 -. c0))

let lb_thi c0 c1 lo hi : float =
  if c1 = c0 then 1.0
  else Float.max ((lo -. c0) /. (c1 -. c0)) ((hi -. c0) /. (c1 -. c0))

(* Closed-filter Liang-Barsky touch: `b64_liang_barsky_touches`. *)
let lb_touches p0 p1 c : bool =
  let x0 = p0.bx and y0 = p0.by_
  and x1 = p1.bx and y1 = p1.by_
  and cx = c.bx  and cy = c.by_ in
  let xlo = cx -. 0.5 and xhi = cx +. 0.5
  and ylo = cy -. 0.5 and yhi = cy +. 0.5 in
  lb_inslab_closed x0 x1 xlo xhi
  && lb_inslab_closed y0 y1 ylo yhi
  && Float.max 0.0 (Float.max (lb_tlo x0 x1 xlo xhi)
                              (lb_tlo y0 y1 ylo yhi))
     <= Float.min 1.0 (Float.min (lb_thi x0 x1 xlo xhi)
                                 (lb_thi y0 y1 ylo yhi))

(* Half-open-filter Liang-Barsky touch: `b64_liang_barsky_touches_halfopen`.
   Closed conditions PLUS explicit strict-upper midpoint checks
   `x(tmid) < xhi`, `y(tmid) < yhi` -- the corpus's midpoint-witness
   characterisation that captures half-open across both orientations
   of (c0, c1). *)
let lb_touches_halfopen p0 p1 c : bool =
  let x0 = p0.bx and y0 = p0.by_
  and x1 = p1.bx and y1 = p1.by_
  and cx = c.bx  and cy = c.by_ in
  let xlo = cx -. 0.5 and xhi = cx +. 0.5
  and ylo = cy -. 0.5 and yhi = cy +. 0.5 in
  let tmin = Float.max 0.0 (Float.max (lb_tlo x0 x1 xlo xhi)
                                      (lb_tlo y0 y1 ylo yhi))
  and tmax = Float.min 1.0 (Float.min (lb_thi x0 x1 xlo xhi)
                                      (lb_thi y0 y1 ylo yhi)) in
  let tmid = (tmin +. tmax) /. 2.0 in
  let xmid = (1.0 -. tmid) *. x0 +. tmid *. x1
  and ymid = (1.0 -. tmid) *. y0 +. tmid *. y1 in
  lb_inslab_halfopen x0 x1 xlo xhi
  && lb_inslab_halfopen y0 y1 ylo yhi
  && tmin <= tmax
  && xmid < xhi
  && ymid < yhi

(* `b64_passes_through_hot_pixel`: closed-filter conjunction on the
   original AND snapped segment. *)
let passes_through_filter p0 p1 c : bool =
  lb_touches p0 p1 c
  && lb_touches (snap_native p0) (snap_native p1) c

(* `b64_passes_through_hot_pixel_halfopen`: half-open conjunction. *)
let passes_through_halfopen p0 p1 c : bool =
  lb_touches_halfopen p0 p1 c
  && lb_touches_halfopen (snap_native p0) (snap_native p1) c

let bool_string b = if b then "TRUE" else "FALSE"

let run_passes_through_filter () =
  let p0 = parse_point (input_line stdin) in
  let p1 = parse_point (input_line stdin) in
  let c  = parse_point (input_line stdin) in
  print_endline (bool_string (passes_through_filter p0 p1 c))

let run_passes_through_halfopen () =
  let p0 = parse_point (input_line stdin) in
  let p1 = parse_point (input_line stdin) in
  let c  = parse_point (input_line stdin) in
  print_endline (bool_string (passes_through_halfopen p0 p1 c))

(* ----- EDGE_IN_RESULT mode (Phase 3, extracted). ------------------------- *)

(* Direct extract of `edge_in_result` from `theories/OverlayGraph.v:375`.
   BooleanOp constructors come through as-is from `Inductive BooleanOp`
   (Overlay.v:212).  EdgeLabel extracts to an OCaml record with `in_left`
   / `in_right : bool` fields. *)

let parse_op s = match String.uppercase_ascii (String.trim s) with
  | "UNION"        -> Union
  | "INTERSECTION" -> Intersection
  | "DIFFERENCE"   -> Difference
  | "SYMDIFF"      -> SymDiff
  | other -> failwith (Printf.sprintf "oracle: unknown BooleanOp: %s" other)

let parse_bool s = match String.lowercase_ascii (String.trim s) with
  | "true"  -> true
  | "false" -> false
  | other -> failwith (Printf.sprintf "oracle: unknown bool: %s" other)

let run_edge_in_result () =
  let op       = parse_op   (input_line stdin) in
  let in_left  = parse_bool (input_line stdin) in
  let in_right = parse_bool (input_line stdin) in
  let label    = { in_left; in_right } in
  print_endline (bool_string (edge_in_result op label))

(* ----- INCIRCLE_SIGN mode (Phase 4, hand-rolled). ------------------------ *)

(* Native OCaml mirror of `inCircle_R` (theories/ArcOrient.v:88).  Cofactor
   expansion along the first column of the 3x3 lifted determinant.  This is
   a HAND-ROLLED implementation, parallel to the Phase 2 hot-pixel modes:
   the Coq predicate is R-side (not yet bridged to BPoint / binary64), so
   extraction is structurally not possible without first adding a b64-side
   parallel `b64_inCircle_R` to theories-flocq/.  The native float
   arithmetic realises Flocq's R semantics under IEEE 754 binary64
   round-to-nearest-even (same trust pattern as the existing
   PASSES_THROUGH_* modes).

   Pin: `inCircle_R A B C P` at ArcOrient.v:88.
     ax := px A - px P;  ay := py A - py P;
     bx := px B - px P;  by := py B - py P;
     cx := px C - px P;  cy := py C - py P;
     na := ax*ax + ay*ay;
     nb := bx*bx + by*by;
     nc := cx*cx + cy*cy;
     ax * (by * nc - cy * nb)
     - ay * (bx * nc - cx * nb)
     + na * (bx * cy - cx * by).

   Sign convention: positive iff (A, B, C) is CCW AND P is strictly inside
   the circumscribed circle.  For CW (A, B, C) the sign flips. *)

let incircle_r_native
    (a : bPoint) (b : bPoint) (c : bPoint) (p : bPoint) : float =
  let ax = a.bx -. p.bx and ay = a.by_ -. p.by_ in
  let bx = b.bx -. p.bx and by_ = b.by_ -. p.by_ in
  let cx = c.bx -. p.bx and cy = c.by_ -. p.by_ in
  let na = ax *. ax +. ay *. ay in
  let nb = bx *. bx +. by_ *. by_ in
  let nc = cx *. cx +. cy *. cy in
  ax *. (by_ *. nc -. cy *. nb)
  -. ay *. (bx *. nc -. cx *. nb)
  +. na *. (bx *. cy -. cx *. by_)

let incircle_sign_string (v : float) : string =
  if v <> v then "NAN"
  else if v > 0.0 then "POS"
  else if v < 0.0 then "NEG"
  else "ZERO"

let run_incircle_sign () =
  let a = parse_point (input_line stdin) in
  let b = parse_point (input_line stdin) in
  let c = parse_point (input_line stdin) in
  let p = parse_point (input_line stdin) in
  let v = incircle_r_native a b c p in
  Printf.printf "%s %h\n" (incircle_sign_string v) v

(* ----- ARC_CHORD_CROSSES_CIRCLE mode (Phase 4, hand-rolled). ------------- *)

(* Sufficient condition for `arc_chord_intersects` (theories/ArcIntersect.v:90)
   via the sign-product test on `inCircle_R`.

   Pin: `chord_crosses_arc_circle a P Q` at ArcIntersect.v:129 -- the
   sP * sQ < 0 form where sP, sQ are the inCircle signs at the chord
   endpoints relative to (arc_start, arc_mid, arc_end).

   Soundness: `chord_crosses_arc_circle_implies_circle_intersection`
   (theories/ArcIntersectIVT.v) -- the IVT-witnessed circle crossing
   theorem.

   This is a SUFFICIENT condition only.  When TRUE, the chord crosses
   the arc's circumcircle.  When FALSE, the chord may still cross
   (both endpoints on the same side, with the chord passing through
   the circle in between), so callers must not interpret FALSE as
   non-crossing. *)

let run_arc_chord_crosses_circle () =
  let arc_start = parse_point (input_line stdin) in
  let arc_mid   = parse_point (input_line stdin) in
  let arc_end   = parse_point (input_line stdin) in
  let chord_p   = parse_point (input_line stdin) in
  let chord_q   = parse_point (input_line stdin) in
  let sp = incircle_r_native arc_start arc_mid arc_end chord_p in
  let sq = incircle_r_native arc_start arc_mid arc_end chord_q in
  print_endline (bool_string (sp *. sq < 0.0))

(* ----- ARC_PASSES_THROUGH_PIXEL mode (Phase 4, hand-rolled). ------------- *)

(* Sufficient condition for `arc_passes_through_hot_pixel`
   (theories/ArcHotPixel.v:95): the six-way disjunction over the four pixel
   edges plus the two arc endpoints.

   Each edge crossing test uses the inCircle sign-product form
   (matching `chord_crosses_arc_circle`).  Each endpoint test uses the
   half-open hot-pixel membership predicate (matching Phase 2's
   in_hot_pixel half-open convention: bottom + left CLOSED, top + right
   OPEN).

   Pixel layout at center C, scale s (radius r = s/2):
     bottom-left  = (cx - r, cy - r)
     bottom-right = (cx + r, cy - r)
     top-right    = (cx + r, cy + r)
     top-left     = (cx - r, cy + r)

   Pin: arc_passes_through_hot_pixel a C scale at ArcHotPixel.v:95
   (six-way disjunction: 4 edge crossings + start_in + end_in).

   Sufficient condition only.  TRUE => arc passes through pixel.
   FALSE => unclear (the disjunction covers the typical case but is
   sufficient, not necessary). *)

let in_hot_pixel_halfopen
    (p : bPoint) (c : bPoint) (scale : float) : bool =
  let r = scale *. 0.5 in
  p.bx >= c.bx -. r && p.bx < c.bx +. r &&
  p.by_ >= c.by_ -. r && p.by_ < c.by_ +. r

let run_arc_passes_through_pixel () =
  let arc_start = parse_point (input_line stdin) in
  let arc_mid   = parse_point (input_line stdin) in
  let arc_end   = parse_point (input_line stdin) in
  let center    = parse_point (input_line stdin) in
  let scale     = float_of_string (String.trim (input_line stdin)) in
  let r = scale *. 0.5 in
  let bl = { bx = center.bx -. r; by_ = center.by_ -. r } in
  let br = { bx = center.bx +. r; by_ = center.by_ -. r } in
  let tr = { bx = center.bx +. r; by_ = center.by_ +. r } in
  let tl = { bx = center.bx -. r; by_ = center.by_ +. r } in
  let crosses p q =
    let sp = incircle_r_native arc_start arc_mid arc_end p in
    let sq = incircle_r_native arc_start arc_mid arc_end q in
    sp *. sq < 0.0
  in
  let result =
    crosses bl br || crosses br tr || crosses tr tl || crosses tl bl
    || in_hot_pixel_halfopen arc_start center scale
    || in_hot_pixel_halfopen arc_end   center scale
  in
  print_endline (bool_string result)

(* ----- CLOTHOID_INTERSECT mode (Phase 4, hand-rolled, TOLERANCE oracle). -- *)

(* Numeric reference for the chord-length parameter L of a clothoid (Euler
   spiral) segment under the G^1 Hermite L-form residual

       f(L) = L^2 * (P(L)^2 + Q(L)^2) - d^2

   solved by Halley iteration.  This is the deferred "future hook" sketched
   in `theories-flocq/Intersect_b64_exact.v`'s `HasClothoidIntersect`
   aspirational block and `docs/audit-phase4-curves.md` 6.1: the R-side
   mathematics is discharged in the companion proprietary corpus
   `clothoid-halley-coq` (Merkator Group, 2026, Coquelicot 3.x), CITED here
   per its academic-citation licence, not imported.

   There is no Flocq-side `b64_clothoid_intersect` yet, so -- unlike every
   bit-exact mode above -- this is a TOLERANCE oracle: it realises the
   R-side L-form numerically (composite-Simpson quadrature for the
   Fresnel-type integrals + Halley iteration) for differential comparison
   against clothoid-halley-coq's 9,058-record `golden_vectors.json` within
   the corpus's stated 1e-9 m chord-length agreement.  It is NOT a verified
   reference; callers must not treat its output as bit-exact, and the
   reported iteration count matches the upstream corpus only insofar as the
   stopping rule below mirrors it.

   Arc-length-normalised tangent angle (tau in [0,1], s = L*tau):

       psi(tau) = kappa_0 * tau + (kappa_1 - kappa_0) * tau^2 / 2.

   Fresnel-type integrals at parameter L (P' = -T, Q' = R, R' = -S2s,
   T' = S2c -- the six identities proved in clothoid-halley-coq):

       P(L)   = int_0^1 cos(L*psi) dtau
       Q(L)   = int_0^1 sin(L*psi) dtau
       R(L)   = int_0^1 psi*cos(L*psi) dtau
       T(L)   = int_0^1 psi*sin(L*psi) dtau
       S2c(L) = int_0^1 psi^2*cos(L*psi) dtau
       S2s(L) = int_0^1 psi^2*sin(L*psi) dtau

   give the residual and its first two derivatives:

       f(L)   = L^2 (P^2 + Q^2) - d^2
       f'(L)  = 2 L (P^2 + Q^2) + 2 L^2 (Q R - P T)
       f''(L) = 2 (P^2 + Q^2) + 8 L (Q R - P T)
                + 2 L^2 (R^2 + T^2 - P S2c - Q S2s)

   and the Halley step is  L <- L - 2 f f' / (2 f'^2 - f f''). *)

(* Composite-Simpson panel count (even).  The rail-transition regime keeps
   |kappa_i * L| <= pi (clothoid-halley-coq monotone branch), so the
   integrands oscillate over at most ~half a period; 1024 panels put the
   quadrature error well below the 1e-9 m differential tolerance. *)
let clothoid_simpson_panels = 1024

let clothoid_psi kappa0 kappa1 tau =
  kappa0 *. tau +. (kappa1 -. kappa0) *. tau *. tau *. 0.5

(* One composite-Simpson pass returning all six integrals at parameter L,
   sharing the psi / cos / sin evaluations across the integrand family. *)
let clothoid_integrals kappa0 kappa1 l =
  let n = clothoid_simpson_panels in
  let h = 1.0 /. float_of_int n in
  let p = ref 0.0 and q = ref 0.0 and r = ref 0.0
  and t = ref 0.0 and s2c = ref 0.0 and s2s = ref 0.0 in
  for i = 0 to n do
    let tau = float_of_int i *. h in
    let psi = clothoid_psi kappa0 kappa1 tau in
    let a = l *. psi in
    let c = cos a and s = sin a in
    (* Simpson weights: 1 at the endpoints, 4 at odd nodes, 2 at even
       interior nodes. *)
    let w =
      if i = 0 || i = n then 1.0
      else if i land 1 = 1 then 4.0
      else 2.0
    in
    p   := !p   +. w *. c;
    q   := !q   +. w *. s;
    r   := !r   +. w *. (psi *. c);
    t   := !t   +. w *. (psi *. s);
    s2c := !s2c +. w *. (psi *. psi *. c);
    s2s := !s2s +. w *. (psi *. psi *. s)
  done;
  let k = h /. 3.0 in
  (k *. !p, k *. !q, k *. !r, k *. !t, k *. !s2c, k *. !s2s)

(* Relative stopping tolerances.  Convergence is declared on either a small
   relative residual or a small relative Halley step; cubic convergence of
   Halley drops the step below `clothoid_step_tol` in a handful of
   iterations within the monotone branch. *)
let clothoid_res_tol  = 1e-12
let clothoid_step_tol = 1e-14

let run_clothoid_intersect () =
  let kappa0 = float_of_string (String.trim (input_line stdin)) in
  let kappa1 = float_of_string (String.trim (input_line stdin)) in
  let d      = float_of_string (String.trim (input_line stdin)) in
  let l0     = float_of_string (String.trim (input_line stdin)) in
  let max_it = int_of_string   (String.trim (input_line stdin)) in
  let d2 = d *. d in
  let rec iterate l iters =
    if not (Float.is_finite l) then
      Printf.printf "NAN %h %d\n" l iters
    else
      let (p, q, r, t, s2c, s2s) = clothoid_integrals kappa0 kappa1 l in
      let pq   = p *. p +. q *. q in
      let qrpt = q *. r -. p *. t in
      let f    = l *. l *. pq -. d2 in
      if Float.abs f <= clothoid_res_tol *. (1.0 +. d2) then
        Printf.printf "CONV %h %d\n" l iters
      else if iters >= max_it then
        Printf.printf "MAXITER %h %d\n" l iters
      else
        let f'  = 2.0 *. l *. pq +. 2.0 *. l *. l *. qrpt in
        let f'' = 2.0 *. pq +. 8.0 *. l *. qrpt
                  +. 2.0 *. l *. l
                     *. (r *. r +. t *. t -. p *. s2c -. q *. s2s) in
        let denom = 2.0 *. f' *. f' -. f *. f'' in
        if denom = 0.0 then
          Printf.printf "MAXITER %h %d\n" l iters
        else
          let l_next = l -. (2.0 *. f *. f') /. denom in
          if Float.abs (l_next -. l)
             <= clothoid_step_tol *. (1.0 +. Float.abs l_next) then
            Printf.printf "CONV %h %d\n" l_next (iters + 1)
          else
            iterate l_next (iters + 1)
  in
  iterate l0 0

(* ----- Mode dispatch. ----------------------------------------------------- *)

(* Persistent loop: SIMPLIFY exits after one call (it reads its input
   until EOF); every other mode emits its reply, flushes stdout, and
   loops back to read the next mode line.  EOF on the mode line exits
   cleanly. *)
let () =
  let rec read_mode () =
    match try Some (input_line stdin) with End_of_file -> None with
    | None -> None
    | Some raw ->
      let line = String.trim raw in
      if line = "" then read_mode () else Some line
  in
  let rec loop () =
    match read_mode () with
    | None -> ()
    | Some mode ->
      (match mode with
       | "SIMPLIFY"                 -> run_simplify (); exit 0
       | "ORIENT"                   -> run_orient ()
       | "ORIENT_FILTERED"          -> run_orient_filtered ()
       | "INTERSECT_FILTERED"       -> run_intersect_filtered ()
       | "INTERSECT_POINT_FILTERED" -> run_intersect_point_filtered ()
       | "INTERSECT_POINT_XY"       -> run_intersect_point_xy ()
       | "PASSES_THROUGH_FILTER"    -> run_passes_through_filter ()
       | "PASSES_THROUGH_HALFOPEN"  -> run_passes_through_halfopen ()
       | "EDGE_IN_RESULT"           -> run_edge_in_result ()
       | "INCIRCLE_SIGN"            -> run_incircle_sign ()
       | "ARC_CHORD_CROSSES_CIRCLE" -> run_arc_chord_crosses_circle ()
       | "ARC_PASSES_THROUGH_PIXEL" -> run_arc_passes_through_pixel ()
       | "CLOTHOID_INTERSECT"       -> run_clothoid_intersect ()
       | other -> failwith (Printf.sprintf "oracle: unknown mode: %s" other));
      flush stdout;
      loop ()
  in
  loop ()
