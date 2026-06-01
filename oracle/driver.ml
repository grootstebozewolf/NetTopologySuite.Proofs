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

     ORIENT_EXACT    -- EXACT orientation over arbitrary binary64 (the
                        ground-truth reference for the JTS #1106 differential
                        test).  Dyadic-rational/bignum determinant; sign is
                        exact for ALL finite inputs (no |coord| <= 2^25
                        restriction).  Mirrors the Qed-proven `b64_orient2d_exact`
                        (theories-flocq/Orient_b64_exact_full.v).
        line 2..4:    points as above.
        output:       single token "<sign>": POS / NEG / ZERO / NAN.

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

(* zarith's bignum module, captured before `open Extracted` shadows `Z`
   with the Coq-extracted `Z` inductive.  Used by the ORIENT_EXACT mode. *)
module BigZ = Z

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

(* ----- ORIENT_EXACT mode. ------------------------------------------------ *)

(* EXACT ground-truth orientation over arbitrary binary64 coordinates -- the
   reference for the JTS #1106 differential test (exact vs the double-double
   `Orientation.index`).

   Every finite binary64 is a dyadic rational m * 2^e, so the orientation
   determinant is computed EXACTLY with bignums (zarith).  This mirrors the
   Qed-proven algorithm `b64_orient2d_exact` and its full-double soundness
   theorem `b64_orient2d_exact_sound` (theories-flocq/Orient_b64_exact_full.v):
   for all finite inputs the sign returned here equals the true real
   orientation sign -- no |coord| <= 2^25 restriction.

   It is a faithful re-implementation rather than an extraction: the oracle's
   native-float extraction maps Flocq's `binary_float` to OCaml `float` and
   stubs the `B754_finite` decode, so the Coq decode cannot be extracted; the
   theorem certifies this algorithm.  (Oracle code is not the trusted base.) *)

(* value = m * 2^e, m a bignum *)
let dyad_of_float (d : float) : BigZ.t * int =
  if d = 0.0 then (BigZ.zero, 0)
  else
    let (f, k) = Float.frexp d in          (* d = f * 2^k, 0.5 <= |f| < 1 *)
    (BigZ.of_int64 (Int64.of_float (Float.ldexp f 53)), k - 53)

let dyad_sub (m1, e1) (m2, e2) =           (* align to the smaller exponent *)
  let e = min e1 e2 in
  (BigZ.sub (BigZ.shift_left m1 (e1 - e)) (BigZ.shift_left m2 (e2 - e)), e)

let dyad_mul (m1, e1) (m2, e2) = (BigZ.mul m1 m2, e1 + e2)

let orient_exact_sign (p0 : bPoint) (p1 : bPoint) (q : bPoint) : int =
  let f = dyad_of_float in
  let t1 = dyad_mul (dyad_sub (f p1.bx) (f p0.bx)) (dyad_sub (f q.by_) (f p0.by_)) in
  let t2 = dyad_mul (dyad_sub (f q.bx) (f p0.bx)) (dyad_sub (f p1.by_) (f p0.by_)) in
  BigZ.sign (fst (dyad_sub t1 t2))

let run_orient_exact () =
  let p0 = parse_point (input_line stdin) in
  let p1 = parse_point (input_line stdin) in
  let q  = parse_point (input_line stdin) in
  let finite p = Float.is_finite p.bx && Float.is_finite p.by_ in
  if not (finite p0 && finite p1 && finite q) then print_endline "NAN"
  else
    let s = orient_exact_sign p0 p1 q in
    print_endline (if s > 0 then "POS" else if s < 0 then "NEG" else "ZERO")

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

(* Extracted from Coq: `b64_passes_through_hot_pixel_compute` and
   `_halfopen_compute` (theories-flocq/PassesThrough_b64_compute.v) -- the
   computational binary64 Liang-Barsky predicates.  The R-spec versions in
   HotPixel_b64 / PassesThroughHalfopen_b64 read coordinates through `B2R`
   and decide with exact-real arithmetic, so they are not extractable; the
   `_compute` versions mirror them on the b64 layer and extract to native
   float code.  They are bit-exact with the previous hand-rolled kernels
   (2,000,000-case differential check, oracle/test_pt.ml), via the usual
   `Bplus -> ( +. )` / `Float.min` / round-half-even extraction overrides in
   Validate_binary64_extract.v.

   Soundness of the rounded predicate to the geometric hot-pixel relation is
   the forward-error / integer-regime obligation tracked in
   docs/oracle-handroll-migration.md item 1 (the R-spec carries the exact
   soundness; bridging the rounded compute to it is deferred). *)

let bool_string b = if b then "TRUE" else "FALSE"

let run_passes_through_filter () =
  let p0 = parse_point (input_line stdin) in
  let p1 = parse_point (input_line stdin) in
  let c  = parse_point (input_line stdin) in
  print_endline (bool_string (b64_passes_through_hot_pixel_compute p0 p1 c))

let run_passes_through_halfopen () =
  let p0 = parse_point (input_line stdin) in
  let p1 = parse_point (input_line stdin) in
  let c  = parse_point (input_line stdin) in
  print_endline
    (bool_string (b64_passes_through_hot_pixel_halfopen_compute p0 p1 c))

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

(* The in-circle determinant is the extracted `b64_inCircle`
   (theories-flocq/InCircle_b64_compute.v), which mirrors `inCircle_R`
   (theories/ArcOrient.v:88) on the b64 layer.  `inCircle_R` is R-side, hence
   not extractable; `b64_inCircle` is its binary64 evaluator and is bit-exact
   with the previous hand-rolled `incircle_r_native` (2,000,000-case
   differential check, oracle/test_ic.ml).  Used by INCIRCLE_SIGN and by the
   ARC_* sign-products below.

   Sign convention: positive iff (A, B, C) is CCW AND P is strictly inside
   the circumscribed circle.  For CW (A, B, C) the sign flips.

   Soundness of the b64 sign to inCircle_R's sign (clean integer-regime
   exactness, |coord| <= 2^12, since the determinant has no division) is
   deferred -- docs/oracle-handroll-migration.md item 2. *)

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
  let v = b64_inCircle a b c p in
  Printf.printf "%s %h\n" (incircle_sign_string v) v

(* ----- ARC_CHORD_CROSSES_CIRCLE mode (Phase 4, extracted). --------------- *)

(* The extracted `b64_chord_crosses_arc_circle`
   (theories-flocq/ArcCircle_b64_compute.v): the sign-product test
   `b64_inCircle(S,M,E,P) * b64_inCircle(S,M,E,Q) < 0` on the b64 layer,
   bit-exact with the previous hand-rolled glue (2,000,000-case check,
   oracle/test_arc.ml).

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
  print_endline
    (bool_string
       (b64_chord_crosses_arc_circle arc_start arc_mid arc_end chord_p chord_q))

(* ----- ARC_PASSES_THROUGH_PIXEL mode (Phase 4, extracted). -------------- *)

(* The extracted `b64_arc_passes_through_hot_pixel`
   (theories-flocq/ArcPixel_b64_compute.v): the six-way disjunction over the
   four pixel edges (inCircle sign-products via `b64_chord_crosses_arc_circle`)
   plus the two arc-endpoint half-open membership tests.  Bit-exact with the
   previous hand-rolled kernels (2,000,000-case check, oracle/test_pixel.ml).

   Pin: `arc_passes_through_hot_pixel a C scale` at ArcHotPixel.v:95.
   Sufficient condition only: TRUE => arc passes through pixel; FALSE
   inconclusive. *)

let run_arc_passes_through_pixel () =
  let arc_start = parse_point (input_line stdin) in
  let arc_mid   = parse_point (input_line stdin) in
  let arc_end   = parse_point (input_line stdin) in
  let center    = parse_point (input_line stdin) in
  let scale     = float_of_string (String.trim (input_line stdin)) in
  print_endline
    (bool_string
       (b64_arc_passes_through_hot_pixel
          arc_start arc_mid arc_end center scale))

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
       | "ORIENT_EXACT"             -> run_orient_exact ()
       | "INTERSECT_FILTERED"       -> run_intersect_filtered ()
       | "INTERSECT_POINT_FILTERED" -> run_intersect_point_filtered ()
       | "INTERSECT_POINT_XY"       -> run_intersect_point_xy ()
       | "PASSES_THROUGH_FILTER"    -> run_passes_through_filter ()
       | "PASSES_THROUGH_HALFOPEN"  -> run_passes_through_halfopen ()
       | "EDGE_IN_RESULT"           -> run_edge_in_result ()
       | "INCIRCLE_SIGN"            -> run_incircle_sign ()
       | "ARC_CHORD_CROSSES_CIRCLE" -> run_arc_chord_crosses_circle ()
       | "ARC_PASSES_THROUGH_PIXEL" -> run_arc_passes_through_pixel ()
       | other -> failwith (Printf.sprintf "oracle: unknown mode: %s" other));
      flush stdout;
      loop ()
  in
  loop ()
