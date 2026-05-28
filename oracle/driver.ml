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
       | other -> failwith (Printf.sprintf "oracle: unknown mode: %s" other));
      flush stdout;
      loop ()
  in
  loop ()
