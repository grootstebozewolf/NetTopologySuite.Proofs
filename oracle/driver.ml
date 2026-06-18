(* =============================================================================
   oracle/driver.ml
   -----------------------------------------------------------------------------
   Stdin/stdout adapter around the Coq-extracted functions in `extracted.ml`.
   This is the RocqRefRunner binary used by the differential test harness in
   NetTopologySuite.Curve.

   For Consumer Connie / NTS-Upstream Norm: see docs/HELP.md + docs/READING-GUIDE.md
   (Consumer Connie path) + the phase completion/audit docs for the mapping of
   oracle modes to verified Coq theorems.

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

     PASSES_THROUGH_EXACT -- EXACT-rational hot-pixel passes-through (closed).
        line 2..4:    P0, P1, C (three BPoints, one per line).
        output:       single token "TRUE" / "FALSE" / "NAN".
        Ground truth (zarith Q, no rounding) for the rounded
        PASSES_THROUGH_FILTER.  The rounded filter over-accepts within
        O(ulp) of tangency (machine-checked unsound:
        PassesThrough_b64_compute_unsound.v); diff FILTER vs EXACT to
        surface that sub-ulp boundary band -- the JTS noder hardening set.

     PASSES_THROUGH_HALFOPEN_EXACT -- EXACT-rational half-open analogue, the
        ground truth for PASSES_THROUGH_HALFOPEN (unsoundness machine-checked
        in PassesThroughHalfopen_b64_compute_unsound.v).
        line 2..4:    P0, P1, C.   output: "TRUE" / "FALSE" / "NAN".

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

     INCIRCLE_EXACT  -- EXACT 4-point in-circle sign over arbitrary binary64
                        (Delaunay ground truth; inCircle analogue of
                        ORIENT_EXACT).  Dyadic/bignum determinant, exact for
                        ALL finite inputs (no overflow/underflow band limit).
        line 2..5:    A, B, C, P (four BPoints).
        output:       single token: POS / NEG / ZERO / NAN.
                      Sign convention proven in ArcOrient.v
                      (inCircle_R_swap_* / _cyclic / _scaling).

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

     ARC_LENGTH_INVARIANTS_EXACT -- EXACT arc-length invariants for a circular arc
                         through 3 control points (issue #64, Option-A).
        line 2..4:    arc_start, arc_mid, arc_end (three BPoints).
        output:       "<r2> <cos> <0|1>" -- squared circumradius r2 and
                      cos Theta0 = (vA.vC)/r2 as exact rationals "num/den",
                      and a major-arc flag.  "DEGENERATE" if collinear.
                      The arc length is s = sqrt r2 * Theta with
                      Theta = (if major then 2*pi - acos cos else acos cos),
                      the single transcendental step done consumer-side.
                      Coq mirror: theories/ArcLength.v (chord_subtended_sq)
                      + theories/AngleBetween.v (cos_angle_between).  All
                      exact zarith Q -- NOT a hand-rolled float kernel.

     ARC_LENGTH -- the literal float arc length s = r * Theta (issue #64),
                   the value the JTS/NTS curve implementation computes.
        line 2..4:    arc_start, arc_mid, arc_end (three BPoints).
        output:       single "%h" double = sqrt r2 * Theta (Theta from the
                      ARC_LENGTH_INVARIANTS_EXACT invariants via one acos); "DEGENERATE"
                      if collinear; "NAN" if non-finite.
        INTERFACE-BOUNDARY mode: arc length is transcendental, so it has no
                      Coq-extractable form; the hand-rolled sqrt/acos is the
                      sanctioned exception (docs/oracle-handrolled-allowlist.txt).
                      For the certifiable invariants use ARC_LENGTH_INVARIANTS_EXACT.

     ARC_SHORTER -- EXACT decision of which of two arcs is shorter (issue #64).
        line 2..7:    arc1 (start,mid,end), arc2 (start,mid,end).
        output:       verdict for arc1 vs arc2 -- SHORTER | EQUAL | LONGER
                      (exact, equal radii) | TRANSCENDENTAL (radii differ, no
                      exact rational verdict) | DEGENERATE | NAN.
                      Exact zarith Q: comparing arc lengths is rational when
                      radii match (order of Theta from cos Theta0 + major
                      flag); declines, rather than rounds, otherwise.

     ARC_AREA_INVARIANTS_EXACT -- EXACT-rational invariants of an arc's
                      circular-SEGMENT area (issue #64, M-AREA-CP).
        line 2..4:    arc_start, arc_mid, arc_end.
        output:       "<r2> <cos> <sin2> <0|1>" -- r2, cos Theta0, sin^2 Theta0
                      (= 1 - cos^2), major-arc flag, all exact rationals;
                      "DEGENERATE" / "NAN".  Pure zarith Q.

     ARC_AREA -- the float circular-segment area A_seg = (r2/2)(Theta - sin
                      Theta) (issue #64), the value the JTS/NTS curve area
                      computes; one rounding (acos + sin) past the exact
                      invariants above.  Interface-boundary float (sanctioned,
                      docs/oracle-handrolled-allowlist.txt).
        line 2..4:    arc_start, arc_mid, arc_end.
        output:       single "%h" double; "DEGENERATE" / "NAN".

     CURVE_SNAP_DECISION -- EXACT curve-snap grid-friendly decision (PRC-SN,
                      JTS#1195, proofs#66).  Snap the 3 arc controls to a
                      1/scale grid (exact Q) and decide keep-vs-densify.
        line 2:       <scale>   (integer grid factor)
        line 3..5:    arc_start, arc_mid, arc_end.
        output:       PRESERVE (snapped circumcentre lands on the grid) |
                      DENSIFY (it does not) | DEGEN (snapped controls collinear)
                      | NAN.  Pure zarith Q -- ratchet-clean.

     CURVE_SNAP_INVARIANTS_EXACT -- same input; output the exact snapped
                      circumcentre + radius "<ox> <oy> <r2> <0|1>" (last =
                      centre-on-grid flag), or DEGEN / NAN.

     RELATE_MATRIX -- pinned DE-9IM matrix lookup (issue #67 S11).
        line 2:       <key>  -- COQ witness name, FILL alias, or raw 9-char
                      matrix (II IB IE / BI BB BE / EI EB EE row-major).
        output:       single 9-char matrix string (F/0/1/2 cells).
        Coq mirror:   witness matrices in RelateLineLine.v, RelateAreaArea.v,
                      RelateAreaLine.v, RelateBoundary.v, RelateArcChord.v,
                      RelateClothoid.v, RelateCurveAreaPoint.v; predicate
                      algebra in DE9IM.v.
                      HAND-ROLLED catalog in oracle/relate_matrix.ml (not
                      geometry computation — full RelateNG noding is S13+).

     RELATE_PREDICATE -- DE-9IM predicate test on a pinned matrix (S11).
        line 2:       <matrix_key>  (same key vocabulary as RELATE_MATRIX)
        line 3:       <predicate>   Disjoint | Intersects | Contains | Within |
                      Covers | CoveredBy | Equals | Touches | Crosses | Overlaps
                      (R-prefix aliases accepted, e.g. RIntersects).
        output:       single token "TRUE" or "FALSE".
        Coq mirror:   `predicate_holds` / `im_*` in theories/DE9IM.v.

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

(* Finiteness guard for the EXACT ground-truth modes.  Uses `classify_float`
   (a validity predicate, not arithmetic) rather than `Float.is_finite` so it
   reads as I/O validation, not a hand-rolled numeric kernel. *)
let finite_float (x : float) : bool =
  match classify_float x with FP_nan | FP_infinite -> false | _ -> true

let finite_bpoint (p : bPoint) : bool = finite_float p.bx && finite_float p.by_

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

let dyad_add (m1, e1) (m2, e2) =           (* align to the smaller exponent *)
  let e = min e1 e2 in
  (BigZ.add (BigZ.shift_left m1 (e1 - e)) (BigZ.shift_left m2 (e2 - e)), e)

let orient_exact_sign (p0 : bPoint) (p1 : bPoint) (q : bPoint) : int =
  let f = dyad_of_float in
  let t1 = dyad_mul (dyad_sub (f p1.bx) (f p0.bx)) (dyad_sub (f q.by_) (f p0.by_)) in
  let t2 = dyad_mul (dyad_sub (f q.bx) (f p0.bx)) (dyad_sub (f p1.by_) (f p0.by_)) in
  BigZ.sign (fst (dyad_sub t1 t2))

let run_orient_exact () =
  let p0 = parse_point (input_line stdin) in
  let p1 = parse_point (input_line stdin) in
  let q  = parse_point (input_line stdin) in
  if not (finite_bpoint p0 && finite_bpoint p1 && finite_bpoint q) then print_endline "NAN"
  else
    let s = orient_exact_sign p0 p1 q in
    print_endline (if s > 0 then "POS" else if s < 0 then "NEG" else "ZERO")

(* ----- INCIRCLE_EXACT mode. ---------------------------------------------- *)

(* EXACT 4-point in-circle determinant sign over arbitrary binary64 -- the
   Delaunay-robustness ground truth, the inCircle analogue of ORIENT_EXACT.
   inCircle_R A B C P = det[ax ay na; bx by nb; cx cy nc] with offsets
   (X - P) and lifted norms na = ax^2 + ay^2.  Computed exactly with bignums
   (no overflow/underflow band limit, unlike float DD).  Sign convention is
   the one proven in theories/ArcOrient.v (inCircle_R_swap_* / _cyclic /
   _scaling): POS iff P is inside the circumcircle of a CCW triangle A,B,C;
   ZERO iff the four points are cocircular (or degenerate). *)
let incircle_exact_sign (a : bPoint) (b : bPoint) (c : bPoint) (p : bPoint) : int =
  let f = dyad_of_float in
  let ax = dyad_sub (f a.bx) (f p.bx) and ay = dyad_sub (f a.by_) (f p.by_) in
  let bx = dyad_sub (f b.bx) (f p.bx) and by_ = dyad_sub (f b.by_) (f p.by_) in
  let cx = dyad_sub (f c.bx) (f p.bx) and cy = dyad_sub (f c.by_) (f p.by_) in
  let na = dyad_add (dyad_mul ax ax) (dyad_mul ay ay) in
  let nb = dyad_add (dyad_mul bx bx) (dyad_mul by_ by_) in
  let nc = dyad_add (dyad_mul cx cx) (dyad_mul cy cy) in
  let t1 = dyad_mul ax (dyad_sub (dyad_mul by_ nc) (dyad_mul cy nb)) in
  let t2 = dyad_mul ay (dyad_sub (dyad_mul bx nc) (dyad_mul cx nb)) in
  let t3 = dyad_mul na (dyad_sub (dyad_mul bx cy) (dyad_mul cx by_)) in
  BigZ.sign (fst (dyad_add (dyad_sub t1 t2) t3))

let run_incircle_exact () =
  let a = parse_point (input_line stdin) in
  let b = parse_point (input_line stdin) in
  let c = parse_point (input_line stdin) in
  let p = parse_point (input_line stdin) in
  if not (finite_bpoint a && finite_bpoint b && finite_bpoint c && finite_bpoint p) then print_endline "NAN"
  else
    let s = incircle_exact_sign a b c p in
    print_endline (if s > 0 then "POS" else if s < 0 then "NEG" else "ZERO")

(* ----- TWOSUM / GROW_EXPANSION modes. ------------------------------------ *)

(* Introspection on the Shewchuk fast-expansion-sum cascade, for validating
   counterexamples about its magnitude behaviour in seconds (rather than
   constructing binary64 literals inside Coq).  TWOSUM runs Knuth/Dekker
   b64_TwoSum; GROW_EXPANSION runs the whole b64_grow_expansion_aux cascade
   and reports the final carry + the settled error chain. *)

let rec read_floats acc =
  match (try Some (input_line stdin) with End_of_file -> None) with
  | None -> List.rev acc
  | Some line ->
      let t = String.trim line in
      if t = "" then read_floats acc
      else read_floats (float_of_string t :: acc)

(* b64_TwoSum x y = (sum, err): sum = round(x+y), err = x+y-sum exactly. *)
let run_twosum () =
  let x = float_of_string (String.trim (input_line stdin)) in
  let y = float_of_string (String.trim (input_line stdin)) in
  let (s, e) = b64_TwoSum x y in
  Printf.printf "SUM %h ERR %h\n" s e

(* GROW_EXPANSION: line 1 = q (initial carry), remaining lines = xs.
   Output: "QFINAL <hex>" then one "H <hex>" per settled error. *)
let run_grow_expansion () =
  let q = float_of_string (String.trim (input_line stdin)) in
  let xs = read_floats [] in
  let (hs, qfinal) = b64_grow_expansion_aux q xs in
  Printf.printf "QFINAL %h\n" qfinal;
  List.iter (fun h -> Printf.printf "H %h\n" h) hs

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

(* ----- PASSES_THROUGH_EXACT / _HALFOPEN_EXACT modes. --------------------- *)

(* EXACT-rational ground truth for the hot-pixel passes-through test -- the
   reference JTS's snap-rounding noder diffs its rounded filter against.  Every
   finite binary64 is a dyadic rational, so `Q.of_float` is exact; the
   Liang-Barsky t-interval decision is evaluated in exact rationals (zarith Q),
   no rounding.  The rounded computational filter (PASSES_THROUGH_FILTER) is a
   conservative over-approximation: it over-accepts within O(ulp) of tangency,
   machine-checked in theories-flocq/PassesThrough_b64_compute_unsound.v
   (closed) and PassesThroughHalfopen_b64_compute_unsound.v (half-open).
   Diffing FILTER/HALFOPEN against the EXACT mode surfaces exactly that
   sub-ulp boundary band -- the adversarial set JTS hardens its noder on.

   Not hand-rolled mirror arithmetic: the snap step reuses the EXTRACTED
   `b64_snap` (round-half-to-even), and the decision is exact rationals, not a
   transcription of the rounded float algorithm.  The exact R-spec it realises
   is `b64_passes_through_hot_pixel` (HotPixel_b64.v) / `_halfopen`
   (PassesThroughHalfopen_b64.v), which are non-computational (`R`-valued) and
   so cannot themselves be extracted. *)

let qle = Q.leq
let qlt = Q.lt
let qeq = Q.equal
let qmin a b = if Q.leq a b then a else b
let qmax a b = if Q.leq a b then b else a
let q0 = Q.zero
let q1 = Q.one
let qhalf = Q.of_ints 1 2
let qf = Q.of_float

let lb_inslab_q c0 c1 lo hi =
  if qeq c1 c0 then (qle lo c0 && qle c0 hi) else true
let lb_inslab_halfopen_q c0 c1 lo hi =
  if qeq c1 c0 then (qle lo c0 && qlt c0 hi) else true
let lb_tlo_q c0 c1 lo hi =
  if qeq c1 c0 then q0
  else qmin (Q.div (Q.sub lo c0) (Q.sub c1 c0)) (Q.div (Q.sub hi c0) (Q.sub c1 c0))
let lb_thi_q c0 c1 lo hi =
  if qeq c1 c0 then q1
  else qmax (Q.div (Q.sub lo c0) (Q.sub c1 c0)) (Q.div (Q.sub hi c0) (Q.sub c1 c0))

(* exact closed-pixel touch on one segment *)
let touch_exact_q x0 y0 x1 y1 cx cy =
  let xlo = Q.sub cx qhalf and xhi = Q.add cx qhalf in
  let ylo = Q.sub cy qhalf and yhi = Q.add cy qhalf in
  lb_inslab_q x0 x1 xlo xhi && lb_inslab_q y0 y1 ylo yhi
  && qle (qmax q0 (qmax (lb_tlo_q x0 x1 xlo xhi) (lb_tlo_q y0 y1 ylo yhi)))
         (qmin q1 (qmin (lb_thi_q x0 x1 xlo xhi) (lb_thi_q y0 y1 ylo yhi)))

(* exact half-open touch: strict upper slab guard + strict-upper midpoint
   witness on both axes (mirrors b64_liang_barsky_touches_halfopen). *)
let touch_exact_halfopen_q x0 y0 x1 y1 cx cy =
  let xlo = Q.sub cx qhalf and xhi = Q.add cx qhalf in
  let ylo = Q.sub cy qhalf and yhi = Q.add cy qhalf in
  let tmin = qmax q0 (qmax (lb_tlo_q x0 x1 xlo xhi) (lb_tlo_q y0 y1 ylo yhi)) in
  let tmax = qmin q1 (qmin (lb_thi_q x0 x1 xlo xhi) (lb_thi_q y0 y1 ylo yhi)) in
  let tmid = Q.div (Q.add tmin tmax) (Q.of_int 2) in
  let xmid = Q.add (Q.mul (Q.sub q1 tmid) x0) (Q.mul tmid x1) in
  let ymid = Q.add (Q.mul (Q.sub q1 tmid) y0) (Q.mul tmid y1) in
  lb_inslab_halfopen_q x0 x1 xlo xhi && lb_inslab_halfopen_q y0 y1 ylo yhi
  && qle tmin tmax && qlt xmid xhi && qlt ymid yhi

let q_touch_of_bpoints touch p0 p1 (c : bPoint) =
  touch (qf p0.bx) (qf p0.by_) (qf p1.bx) (qf p1.by_) (qf c.bx) (qf c.by_)

(* exact passes-through = exact touch on the original AND on the unit-grid
   snap; the snap uses the extracted `b64_snap`. *)
let passes_through_exact_q touch p0 p1 c =
  let s0 = b64_snap p0 and s1 = b64_snap p1 in
  q_touch_of_bpoints touch p0 p1 c && q_touch_of_bpoints touch s0 s1 c

let run_passes_through_exact () =
  let p0 = parse_point (input_line stdin) in
  let p1 = parse_point (input_line stdin) in
  let c  = parse_point (input_line stdin) in
  if not (finite_bpoint p0 && finite_bpoint p1 && finite_bpoint c)
  then print_endline "NAN"
  else print_endline (bool_string (passes_through_exact_q touch_exact_q p0 p1 c))

let run_passes_through_halfopen_exact () =
  let p0 = parse_point (input_line stdin) in
  let p1 = parse_point (input_line stdin) in
  let c  = parse_point (input_line stdin) in
  if not (finite_bpoint p0 && finite_bpoint p1 && finite_bpoint c)
  then print_endline "NAN"
  else print_endline (bool_string (passes_through_exact_q touch_exact_halfopen_q p0 p1 c))

(* ----- ARC_LENGTH_INVARIANTS_EXACT mode (issue #64, Option-A arc length). ---------- *)

(* EXACT arc-length invariants for a circular arc through 3 control points
   A=start, B=mid, C=end.  Arc length s = r * Theta is transcendental (Theta an
   angle, r a square root), hence NOT Coq-extractable (Flocq has no Batan2) and
   -- per the oracle credibility ratchet -- must not be hand-rolled in float.
   This mode instead emits the EXACT RATIONAL invariants from which the length
   follows by a single consumer-side acos/sqrt, mirroring the certified Coq
   relations:
     - r2    = squared circumradius
     - cos   = cos Theta0 = (vA . vC) / r2, with vA = A-O, vC = C-O and
               |vA| = |vC| = r  (theories/AngleBetween.cos_angle_between)
     - major = 1 iff the arc through B is the MAJOR arc (Theta = 2*pi - Theta0),
               decided exactly by whether B and the centre O lie on the SAME
               side of chord AC (orientation signs).
   Consumer reconstructs:  r = sqrt r2;  Theta = if major then 2*pi - acos cos
   else acos cos;  length = r * Theta.  The half-angle identity
   chord^2 = 2*r2*(1 - cos) is theories/ArcLength.chord_subtended_sq.  All
   arithmetic here is exact zarith Q (every binary64 is dyadic) -- no float, no
   hand-rolled numeric kernel.

   Input:  lines 2..4 = arc_start, arc_mid, arc_end (three BPoints "x y").
   Output: "<r2> <cos> <0|1>" (r2, cos as exact rationals "num/den");
           "DEGENERATE" if the three control points are collinear (no circle);
           "NAN" if any coordinate is non-finite. *)
type arc_inv = ArcDegenerate | ArcInv of Q.t * Q.t * int

(* Exact (zarith Q) circular-arc invariants from 3 control points A, B, C:
   squared circumradius r2, cos Theta0 = (vA.vC)/r2 (vA = A-O, vC = C-O), and a
   major-arc flag (1 iff B and the centre O are on the SAME side of chord AC).
   Pure Q -- no float, no hand-rolled numeric kernel.  Shared by
   ARC_LENGTH_INVARIANTS_EXACT (prints the rationals) and ARC_LENGTH (one float step). *)
let arc_invariants_q (a : bPoint) (b : bPoint) (c : bPoint) : arc_inv =
  let ax = qf a.bx and ay = qf a.by_ in
  let bx = qf b.bx and by_ = qf b.by_ in
  let cx = qf c.bx and cy = qf c.by_ in
  (* d = 2 (ax(by-cy) + bx(cy-ay) + cx(ay-by)); zero iff the points are collinear *)
  let d = Q.mul (Q.of_int 2)
    (Q.add (Q.add (Q.mul ax (Q.sub by_ cy)) (Q.mul bx (Q.sub cy ay)))
           (Q.mul cx (Q.sub ay by_))) in
  if qeq d q0 then ArcDegenerate
  else begin
    let na = Q.add (Q.mul ax ax) (Q.mul ay ay) in
    let nb = Q.add (Q.mul bx bx) (Q.mul by_ by_) in
    let nc = Q.add (Q.mul cx cx) (Q.mul cy cy) in
    let ox = Q.div
      (Q.add (Q.add (Q.mul na (Q.sub by_ cy)) (Q.mul nb (Q.sub cy ay)))
             (Q.mul nc (Q.sub ay by_))) d in
    let oy = Q.div
      (Q.add (Q.add (Q.mul na (Q.sub cx bx)) (Q.mul nb (Q.sub ax cx)))
             (Q.mul nc (Q.sub bx ax))) d in
    let vax = Q.sub ax ox and vay = Q.sub ay oy in
    let vcx = Q.sub cx ox and vcy = Q.sub cy oy in
    let r2 = Q.add (Q.mul vax vax) (Q.mul vay vay) in
    let dot_ac = Q.add (Q.mul vax vcx) (Q.mul vay vcy) in
    let cos_full = Q.div dot_ac r2 in
    (* orientation of (A, C, X) = (cx-ax)(Xy-ay) - (cy-ay)(Xx-ax) *)
    let orient_acx xx xy =
      Q.sub (Q.mul (Q.sub cx ax) (Q.sub xy ay))
            (Q.mul (Q.sub cy ay) (Q.sub xx ax)) in
    let sb = Q.sign (orient_acx bx by_) in
    let so = Q.sign (orient_acx ox oy) in
    let major = if so <> 0 && sb = so then 1 else 0 in
    ArcInv (r2, cos_full, major)
  end

let run_arc_length_invariants_exact () =
  let a = parse_point (input_line stdin) in
  let b = parse_point (input_line stdin) in
  let c = parse_point (input_line stdin) in
  if not (finite_bpoint a && finite_bpoint b && finite_bpoint c)
  then print_endline "NAN"
  else match arc_invariants_q a b c with
    | ArcDegenerate -> print_endline "DEGENERATE"
    | ArcInv (r2, cos_full, major) ->
        Printf.printf "%s %s %d\n" (Q.to_string r2) (Q.to_string cos_full) major

(* ARC_LENGTH: the literal float arc length s = r * Theta -- the value the
   JTS/NTS curve implementation itself computes (Math.sqrt + Math.acos).  This
   is an INTERFACE-BOUNDARY mode: arc length is transcendental, so it has NO
   Coq-extractable form, and the differential test needs the same primitive
   double the port emits.  The hand-rolled float step here is the sanctioned
   exception in docs/oracle-handrolled-allowlist.txt (interface-boundary
   category).  It applies r = sqrt r2 and Theta0 = acos cos to the EXACT
   rational invariants (arc_invariants_q), so it rounds only ONCE past the
   certified algebra; the certifiable form is ARC_LENGTH_INVARIANTS_EXACT. *)
let run_arc_length () =
  let a = parse_point (input_line stdin) in
  let b = parse_point (input_line stdin) in
  let c = parse_point (input_line stdin) in
  if not (finite_bpoint a && finite_bpoint b && finite_bpoint c)
  then print_endline "NAN"
  else match arc_invariants_q a b c with
    | ArcDegenerate -> print_endline "DEGENERATE"
    | ArcInv (r2, cos_full, major) ->
        let r = sqrt (Q.to_float r2) in
        (* Central half-angle via the EXACT sin^2(θ/2) = (1 − cos)/2 in Q, then
           asin -- robust for near-flat arcs.  The old acos(to_float cos_full)
           lost all precision once cos≈1 (large-r / tiny-θ): to_float rounds the
           tiny 1−cos away and acos near 1 amplifies it, so r·θ dipped BELOW the
           chord -- violating the proven chord_le_arc_length.  Forming (1−cos)/2
           in exact Q first (no float cancellation) keeps it sound, and
           asin(s) ≥ s gives arc = 2r·asin(s) ≥ 2r·s = chord.  Mirrors
           theories/ArcLength.chord_subtended_sq. *)
        let s = sqrt (Q.to_float (Q.mul (Q.sub q1 cos_full) (Q.of_ints 1 2))) in
        let t0 = 2.0 *. asin s in
        let theta = if major = 1 then 2.0 *. Float.pi -. t0 else t0 in
        Printf.printf "%h\n" (r *. theta)

(* ----- ARC_SHORTER mode (issue #64) -- EXACT arc-length comparison. ------ *)

(* Which of two arcs is shorter?  Arc length r*Theta is transcendental, but
   COMPARING two arc lengths is EXACTLY decidable when the radii are equal:
   shorter <=> smaller Theta, and Theta's order is a rational decision on
   (cos Theta0, major-arc flag) from arc_invariants_q -- a minor arc (Theta<=pi)
   is shorter than any major arc (Theta>=pi), and within one class the order is
   a sign-compare of cos Theta0 (acos is monotone decreasing: minor Theta grows
   as cos falls; major Theta = 2pi - acos grows as cos rises).  The two classes
   meet only at Theta=pi (cos=-1), the single equality bridge.

   When the radii differ, r1*Theta1 vs r2*Theta2 is genuinely transcendental
   (no exact rational verdict), so the mode honestly reports TRANSCENDENTAL --
   exactly the point of an honest EXACT oracle: it decides the comparison where
   the polynomial layer suffices and declines (rather than rounds) where it does
   not.  All arithmetic is exact zarith Q -- no float, no hand-rolled kernel.

   Input:  lines 2..7 = arc1 (start, mid, end), arc2 (start, mid, end).
   Output: verdict for arc1 vs arc2 -- SHORTER | EQUAL | LONGER |
           TRANSCENDENTAL (radii differ) | DEGENERATE (collinear) | NAN. *)
let run_arc_shorter () =
  let a1 = parse_point (input_line stdin) in
  let b1 = parse_point (input_line stdin) in
  let c1 = parse_point (input_line stdin) in
  let a2 = parse_point (input_line stdin) in
  let b2 = parse_point (input_line stdin) in
  let c2 = parse_point (input_line stdin) in
  if not (List.for_all finite_bpoint [a1; b1; c1; a2; b2; c2])
  then print_endline "NAN"
  else match arc_invariants_q a1 b1 c1, arc_invariants_q a2 b2 c2 with
    | ArcDegenerate, _ | _, ArcDegenerate -> print_endline "DEGENERATE"
    | ArcInv (r2a, ca, ma), ArcInv (r2b, cb, mb) ->
        if not (qeq r2a r2b) then print_endline "TRANSCENDENTAL"
        else begin
          let qm1 = Q.of_int (-1) in
          (* Theta-order key: <0 iff arc1 is shorter (equal radius). *)
          let cmp =
            if ma = mb then
              (if ma = 0 then Q.compare cb ca   (* minor: Theta ~ -cos *)
               else Q.compare ca cb)            (* major: Theta ~ +cos *)
            else if qeq ca qm1 && qeq cb qm1 then 0  (* both Theta=pi *)
            else compare ma mb                  (* minor (0) shorter than major (1) *)
          in
          print_endline
            (if cmp < 0 then "SHORTER" else if cmp > 0 then "LONGER" else "EQUAL")
        end

(* ----- HOLE_PRECISION_AUDIT mode (JTS#979 hunter oracle). ---------------- *)

(* JTS#979: `Geometry.buffer` with a fixed PrecisionModel REMOVES a hole.  The
   root mechanism is precision reduction: snapping the hole-ring's vertices to
   the fixed grid (makePrecise: x |-> round(x*scale)/scale) collapses the hole
   -- its signed area degenerates to zero (or flips), so the hole vanishes and
   buffer drops it.  This oracle is the EXACT ground truth for that collapse:
   the signed-area sign of the ring computed in zarith Q (shoelace; every
   binary64 is dyadic, so exact, no rounding), BEFORE and AFTER precision
   reduction.  A hunter flags a #979 hole-collapse when the exact ring has
   nonzero area but the precision-reduced ring has zero area.

   PROOF-BACKED.  `ring_area2` is the shoelace signed area `signed_area2` and
   `q_make_precise` is the grid snap `snap_pt`, both formalised in
   `theories/RingArea979.v`.  The collapse this oracle reports is certified
   there: `signed_area2_snap_quantized` shows the snapped twice-area is an
   integer multiple of `1/scale^2`, and `hole_below_grid_resolution_collapses`
   shows any ring whose snapped twice-area is below one grid cell is EXACTLY
   zero -- so a "ZERO" precise verdict is a sound witness of hole removal, not
   a rounding artefact.  (The proof is rounding-mode agnostic; this oracle
   instantiates the round-half-up `rnd`.)

   Input:  line 2   = scale  (positive integer = fixed PrecisionModel scale)
           line 3   = n       (vertex count, >= 3)
           lines 4.. = the n ring vertices "x y"
   Output: "<exact_sign> <precise_sign>"  (each POS / NEG / ZERO);
           "POS ZERO" / "NEG ZERO" is a hole that the precision model removes. *)

let qsign (q : Q.t) : string =
  let s = Q.sign q in if s > 0 then "POS" else if s < 0 then "NEG" else "ZERO"

(* round q to the nearest multiple of 1/scale: floor(q*scale + 1/2) / scale. *)
let q_make_precise (scale : int) (q : Q.t) : Q.t =
  let s = Q.add (Q.mul q (Q.of_int scale)) (Q.of_ints 1 2) in
  Q.div (Q.of_bigint (BigZ.fdiv (Q.num s) (Q.den s))) (Q.of_int scale)

(* Exact circumcentre (ox, oy) and squared radius r2 of three points given as
   exact rationals; None when the three are collinear (d = 0).  Same algebra as
   arc_invariants_q's centre step, on raw Q tuples, for the CURVE_SNAP_* modes. *)
let circumcentre_q (ax, ay) (bx, by) (cx, cy) =
  let d = Q.mul (Q.of_int 2)
    (Q.add (Q.add (Q.mul ax (Q.sub by cy)) (Q.mul bx (Q.sub cy ay)))
           (Q.mul cx (Q.sub ay by))) in
  if qeq d q0 then None
  else begin
    let na = Q.add (Q.mul ax ax) (Q.mul ay ay) in
    let nb = Q.add (Q.mul bx bx) (Q.mul by by) in
    let nc = Q.add (Q.mul cx cx) (Q.mul cy cy) in
    let ox = Q.div
      (Q.add (Q.add (Q.mul na (Q.sub by cy)) (Q.mul nb (Q.sub cy ay)))
             (Q.mul nc (Q.sub ay by))) d in
    let oy = Q.div
      (Q.add (Q.add (Q.mul na (Q.sub cx bx)) (Q.mul nb (Q.sub ax cx)))
             (Q.mul nc (Q.sub bx ax))) d in
    let r2 = Q.add (Q.mul (Q.sub ax ox) (Q.sub ax ox))
                   (Q.mul (Q.sub ay oy) (Q.sub ay oy)) in
    Some (ox, oy, r2)
  end

(* twice the signed area of the ring (shoelace); only its sign is used. *)
let ring_area2 (xs : Q.t array) (ys : Q.t array) : Q.t =
  let n = Array.length xs in
  let acc = ref Q.zero in
  for i = 0 to n - 1 do
    let j = (i + 1) mod n in
    acc := Q.add !acc (Q.sub (Q.mul xs.(i) ys.(j)) (Q.mul xs.(j) ys.(i)))
  done;
  !acc

let run_hole_precision_audit () =
  let scale = int_of_string (String.trim (input_line stdin)) in
  let n = int_of_string (String.trim (input_line stdin)) in
  let pts = Array.init n (fun _ -> parse_point (input_line stdin)) in
  let xs = Array.map (fun p -> qf p.bx) pts in
  let ys = Array.map (fun p -> qf p.by_) pts in
  let xsp = Array.map (q_make_precise scale) xs in
  let ysp = Array.map (q_make_precise scale) ys in
  Printf.printf "%s %s\n" (qsign (ring_area2 xs ys)) (qsign (ring_area2 xsp ysp))

(* ----- HOLES_SURVIVE_PRECISION mode (JTS#979 hole-COUNT oracle). ---------- *)

(* The direct hole-COUNT metric for #979: given a polygon's k hole-rings and a
   fixed PrecisionModel scale, report how many holes SURVIVE precision
   reduction -- i.e. whose precision-reduced ring still has nonzero (exact,
   zarith Q) signed area.  The #979 signature is survived < k (the precision
   model dropped a hole).  This is the multi-ring count version of
   HOLE_PRECISION_AUDIT; distance d is irrelevant and not taken.

   Input:  line 2   = scale  (positive integer = fixed PrecisionModel scale)
           line 3   = k       (number of hole rings)
           then for each hole:  a line "n_i" (its vertex count), then n_i
                                vertices "x y".
   Output: "survived <s> of <k>"  [+ "  collapsed=[i;j;...]" of the dropped
            hole indices, 0-based]. *)

let run_holes_survive_precision () =
  let scale = int_of_string (String.trim (input_line stdin)) in
  let k = int_of_string (String.trim (input_line stdin)) in
  let survived = ref 0 in
  let collapsed = ref [] in
  for h = 0 to k - 1 do
    let n = int_of_string (String.trim (input_line stdin)) in
    let pts = Array.init n (fun _ -> parse_point (input_line stdin)) in
    let xsp = Array.map (fun p -> q_make_precise scale (qf p.bx)) pts in
    let ysp = Array.map (fun p -> q_make_precise scale (qf p.by_)) pts in
    if Q.sign (ring_area2 xsp ysp) <> 0 then incr survived
    else collapsed := h :: !collapsed
  done;
  Printf.printf "survived %d of %d" !survived k;
  (match List.rev !collapsed with
   | [] -> ()
   | l -> Printf.printf "  collapsed=[%s]" (String.concat ";" (List.map string_of_int l)));
  print_newline ()

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

(* ----- ARC_LINE_XY mode (Phase 4 Scope C, extracted). ------------------- *)

(* NOTE: this is a SINGLE-point projection (Cramer's rule, one root); it is not
   an enumerator and emits -inf/-nan on a two-crossing line (issue #224).  For
   arc-line/segment intersection enumeration (0/1/2 points, sweep- and
   segment-clamped) use ARC_SEGMENT_XY below. *)

(* Calls the verified total projections b64_arc_line_intersect_point_x / _y
   from `theories-flocq/ArcLineIntersect_b64_exact.v` directly.  Reads the arc
   (start, mid, end) defining the circumcircle, then the chord endpoints P, Q,
   and emits the binary64 coordinates of the parameterised circle-chord
   intersection point (Cramer's rule with inCircle determinants).  The same
   `Bplus/Bminus/Bmult/Bdiv -> ( +. )/( -. )/( *. )/( /. )` extraction overrides
   that back the other arc modes make these bit-equal with .NET `double`.

   Backed by: the round-chain identity `b64_arc_line_intersect_point_{x,y}_
   round_chain` and the forward-error headlines
   `b64_arc_line_point_{x,y}_forward_error` (<= bpow 13) and the tighter
   data-dependent `..._forward_error_ulp` (ulp-of-output form).  Differential
   evidence vs a native-float reference: oracle/test_arc.ml. *)

let run_arc_line_xy () =
  let arc_start = parse_point (input_line stdin) in
  let arc_mid   = parse_point (input_line stdin) in
  let arc_end   = parse_point (input_line stdin) in
  let chord_p   = parse_point (input_line stdin) in
  let chord_q   = parse_point (input_line stdin) in
  let x = b64_arc_line_intersect_point_x arc_start arc_mid arc_end chord_p chord_q in
  let y = b64_arc_line_intersect_point_y arc_start arc_mid arc_end chord_p chord_q in
  Printf.printf "XY %h %h\n" x y

(* ----- ARC_AREA / ARC_AREA_INVARIANTS_EXACT (issue #64, M-AREA-CP). ------ *)

(* Circular-SEGMENT area of one arc (A=start, B=mid, C=end): the signed region
   between chord AC and the arc through B -- the per-arc correction a curve-
   polygon area (M-AREA-CP) adds to the straight-edge shoelace.

     A_seg = (r^2 / 2) * (Theta - sin Theta),   Theta = swept central angle.

   Refactored to mirror ARC_LENGTH (replacing the earlier hand-rolled shoelace
   stub that bypassed the ratchet): A_seg is transcendental (Theta), so the
   honest oracle splits into an EXACT-rational invariants mode and an
   interface-boundary float, both built on the shared exact arc_invariants_q
   (r2, cos Theta0, major flag).  cos Theta = cos Theta0 on either arc; sin Theta
   = +sqrt(1 - cos^2) on the minor arc, -sqrt(1 - cos^2) on the major.

   ARC_AREA_INVARIANTS_EXACT: lines 2..4 = A, B, C; output the exact rationals
     "<r2> <cos> <sin2> <0|1>" (sin2 = 1 - cos^2 = sin^2 Theta0), "DEGENERATE",
     or "NAN".  Pure zarith Q -- ratchet-clean.
   ARC_AREA: same input; output the float A_seg ("%h") -- one rounding past the
     exact invariants (acos + sin), the value the JTS/NTS curve area computes;
     the sanctioned interface-boundary float. *)

let run_arc_area_invariants_exact () =
  let a = parse_point (input_line stdin) in
  let b = parse_point (input_line stdin) in
  let c = parse_point (input_line stdin) in
  if not (finite_bpoint a && finite_bpoint b && finite_bpoint c)
  then print_endline "NAN"
  else match arc_invariants_q a b c with
    | ArcDegenerate -> print_endline "DEGENERATE"
    | ArcInv (r2, cos_full, major) ->
        let sin2 = Q.sub q1 (Q.mul cos_full cos_full) in
        Printf.printf "%s %s %s %d\n"
          (Q.to_string r2) (Q.to_string cos_full) (Q.to_string sin2) major

let run_arc_area () =
  let a = parse_point (input_line stdin) in
  let b = parse_point (input_line stdin) in
  let c = parse_point (input_line stdin) in
  if not (finite_bpoint a && finite_bpoint b && finite_bpoint c)
  then print_endline "NAN"
  else match arc_invariants_q a b c with
    | ArcDegenerate -> print_endline "DEGENERATE"
    | ArcInv (r2, cos_full, major) ->
        let r2f = Q.to_float r2 in
        (* Robust central angle: half-angle via exact sin^2(θ/2)=(1−cos)/2 in Q,
           same acos-near-1 fix as run_arc_length. *)
        let s = sqrt (Q.to_float (Q.mul (Q.sub q1 cos_full) (Q.of_ints 1 2))) in
        let t0 = 2.0 *. asin s in
        let theta = if major = 1 then 2.0 *. Float.pi -. t0 else t0 in
        (* Segment area = (r²/2)(θ − sin θ).  For small θ (near-flat minor arcs)
           θ − sin θ ≈ θ³/6 is catastrophic cancellation in float, so sum the
           Taylor series Σ_{k≥1} (−1)^{k+1} θ^{2k+1}/(2k+1)! instead (term
           recurrence  t_{k+1} = −t_k·θ²/((2k+2)(2k+3)) ).  θ ≥ 1 (all major
           arcs, and minor arcs where the subtraction is well-conditioned) takes
           the direct path. *)
        let g =
          if theta >= 1.0 then theta -. sin theta
          else begin
            let t2 = theta *. theta in
            let term = ref (theta *. t2 /. 6.0) in   (* k=1: θ³/3! *)
            let sum  = ref !term in
            let k = ref 1 in
            while abs_float !term > abs_float !sum *. 1e-17 && !k < 30 do
              let kk = float_of_int !k in
              term := -. !term *. t2 /. ((2.0 *. kk +. 2.0) *. (2.0 *. kk +. 3.0));
              sum  := !sum +. !term;
              incr k
            done;
            !sum
          end
        in
        Printf.printf "%h\n" (r2f /. 2.0 *. g)

(* ----- ARC_CENTROID (issue #64/#69 C-LIN): centre of mass of one circular ARC.
   ---------------------------------------------------------------------------
   The 1-D arc (curve) centroid, emitted as a POINT.  It lies on the arc's
   ANGULAR BISECTOR at centroid = O + (2*r*sin(theta/2)/theta) * m, where O is the
   exact circumcentre, m = arc_bisector_unit (toward the arc midpoint), and theta
   the (minor or major) sweep.  NOTE: the offset is along m, NOT along the mid
   control point B -- B is an arbitrary point on the arc, not necessarily the
   angular midpoint, so O->B misplaces the centroid for non-canonical
   CircularStrings (B is used only to disambiguate the semicircle bisector side).
   This is the per-arc position CircularString.getCentroid() weights by ARC_LENGTH
   (M-LEN-CS).

   INTERFACE-BOUNDARY float, exactly like ARC_LENGTH: the offset 2*r*sin(theta/2)
   /theta is transcendental (asin), so it hand-rolls float off the EXACT
   arc_invariants_q / circumcentre_q rational kernel, rounding only ONCE past the
   certified algebra.  s = sin(theta/2) = sqrt((1 - cos)/2) reuses ARC_LENGTH's
   acos-near-1 fix.  Spec proven in theories/ArcCentroid.v: offset = 2*r*sin(theta/2)
   /theta, semicircle -> 2r/PI, full turn -> 0, 0 <= offset <= r.

   Input:  lines 2..4 = arc_start, arc_mid, arc_end ("x y").
   Output: "XY <cx> <cy>" (centroid coords, %h); "DEGENERATE" (collinear); "NAN". *)
(* Unit angular BISECTOR of the arc A->B->C about centre (ox,oy), pointing toward
   the arc's angular midpoint (its bulge / B side).  An arc's centroid and a
   circular segment's centroid both lie along THIS direction -- NOT along O->B:
   the SQL/MM mid control point B is an arbitrary point on the arc, not
   necessarily the angular midpoint, so projecting the offset along (B-O)
   misplaces the centroid for non-canonical CircularStrings.
   m = sgn * (uA + uC)/|uA + uC|, uA = A-O, uC = C-O, sgn = -1 if major else +1
   (uA + uC bisects the minor arc; the major arc's midpoint is the opposite ray).
   Semicircle (uA + uC ~ 0): the bisector is perpendicular to chord AC, oriented
   toward B (B disambiguates the side). *)
let arc_bisector_unit (ox, oy) (a : bPoint) (b : bPoint) (c : bPoint) (major : int) =
  let uax = a.bx -. ox and uay = a.by_ -. oy in
  let ucx = c.bx -. ox and ucy = c.by_ -. oy in
  let sx = uax +. ucx and sy = uay +. ucy in
  let n = sqrt (sx *. sx +. sy *. sy) in
  let r = sqrt (uax *. uax +. uay *. uay) in
  if n > 1e-9 *. r then
    let g = if major = 1 then -1.0 else 1.0 in
    (g *. sx /. n, g *. sy /. n)
  else begin
    (* semicircle: perpendicular to chord AC, oriented toward B *)
    let px = -. (c.by_ -. a.by_) and py = c.bx -. a.bx in
    let pn = sqrt (px *. px +. py *. py) in
    let s = if px *. (b.bx -. ox) +. py *. (b.by_ -. oy) < 0.0 then -1.0 else 1.0 in
    (s *. px /. pn, s *. py /. pn)
  end

let run_arc_centroid () =
  let a = parse_point (input_line stdin) in
  let b = parse_point (input_line stdin) in
  let c = parse_point (input_line stdin) in
  if not (finite_bpoint a && finite_bpoint b && finite_bpoint c)
  then print_endline "NAN"
  else match arc_invariants_q a b c with
    | ArcDegenerate -> print_endline "DEGENERATE"
    | ArcInv (r2, cos_full, major) ->
        (match circumcentre_q (qf a.bx, qf a.by_) (qf b.bx, qf b.by_)
                 (qf c.bx, qf c.by_) with
         | None -> print_endline "DEGENERATE"
         | Some (ox, oy, _r2c) ->
             let r = sqrt (Q.to_float r2) in
             let s = sqrt (Q.to_float (Q.mul (Q.sub q1 cos_full) (Q.of_ints 1 2))) in
             let t0 = 2.0 *. asin s in
             let theta = if major = 1 then 2.0 *. Float.pi -. t0 else t0 in
             let oxf = Q.to_float ox and oyf = Q.to_float oy in
             (* offset = 2 r sin(theta/2) / theta, along the angular bisector m *)
             let offset = 2.0 *. r *. s /. theta in
             let (mx, my) = arc_bisector_unit (oxf, oyf) a b c major in
             let cx = oxf +. offset *. mx in
             let cy = oyf +. offset *. my in
             Printf.printf "XY %h %h\n" cx cy)

(* ----- ARC_AREA_CENTROID (issue #64/#69 C-AREA): centre of mass of one circular
   SEGMENT (the 2-D region between an arc and its chord), as a POINT.
   ---------------------------------------------------------------------------
   centroid = O + (4*r*sin^3(theta/2)/(3*(theta - sin theta))) * m, with O the
   exact circumcentre, m = arc_bisector_unit (the arc's ANGULAR bisector, toward
   the midpoint -- NOT along the mid control point B), theta the (minor/major)
   sweep.  Companion to ARC_AREA (same r2/cos/major kernel + the SAME theta - sin
   theta Taylor series for small theta) and to ARC_CENTROID (same bisector m).

   INTERFACE-BOUNDARY float, like ARC_AREA/ARC_CENTROID: the offset
   4*r*sin^3(theta/2)/(3*(theta - sin theta)) is transcendental (asin/sin), no
   Coq-extractable form; rounds only ONCE past the exact arc_invariants_q /
   circumcentre_q rational kernel.  Spec proven in theories/ArcAreaCentroid.v
   (offset = 4r*sin^3(theta/2)/(3(theta-sin theta)); semicircle -> 4r/(3*PI);
   full turn -> 0).

   Input:  lines 2..4 = arc_start, arc_mid, arc_end ("x y").
   Output: "XY <cx> <cy>" (segment-centroid coords, %h); "DEGENERATE"; "NAN". *)
let run_arc_area_centroid () =
  let a = parse_point (input_line stdin) in
  let b = parse_point (input_line stdin) in
  let c = parse_point (input_line stdin) in
  if not (finite_bpoint a && finite_bpoint b && finite_bpoint c)
  then print_endline "NAN"
  else match arc_invariants_q a b c with
    | ArcDegenerate -> print_endline "DEGENERATE"
    | ArcInv (r2, cos_full, major) ->
        (match circumcentre_q (qf a.bx, qf a.by_) (qf b.bx, qf b.by_)
                 (qf c.bx, qf c.by_) with
         | None -> print_endline "DEGENERATE"
         | Some (ox, oy, _r2c) ->
             let r = sqrt (Q.to_float r2) in
             let s = sqrt (Q.to_float (Q.mul (Q.sub q1 cos_full) (Q.of_ints 1 2))) in
             let t0 = 2.0 *. asin s in
             let theta = if major = 1 then 2.0 *. Float.pi -. t0 else t0 in
             (* g = theta - sin theta (twice the segment area / r^2); same Taylor
                small-angle path as ARC_AREA to avoid catastrophic cancellation. *)
             let g =
               if theta >= 1.0 then theta -. sin theta
               else begin
                 let t2 = theta *. theta in
                 let term = ref (theta *. t2 /. 6.0) in
                 let sum  = ref !term in
                 let k = ref 1 in
                 while abs_float !term > abs_float !sum *. 1e-17 && !k < 30 do
                   let kk = float_of_int !k in
                   term := -. !term *. t2 /. ((2.0 *. kk +. 2.0) *. (2.0 *. kk +. 3.0));
                   sum  := !sum +. !term;
                   incr k
                 done;
                 !sum
               end
             in
             let oxf = Q.to_float ox and oyf = Q.to_float oy in
             (* offset = 4 r sin^3(theta/2) / (3 (theta - sin theta)), along the
                angular bisector m (NOT along the mid control point B) *)
             let offset = 4.0 /. 3.0 *. r *. (s *. s *. s) /. g in
             let (mx, my) = arc_bisector_unit (oxf, oyf) a b c major in
             let cx = oxf +. offset *. mx in
             let cy = oyf +. offset *. my in
             Printf.printf "XY %h %h\n" cx cy)

(* ----- ARC_DISTANCE (issue #64/#69 D-PT): shortest distance from a point to one
   circular ARC.
   ---------------------------------------------------------------------------
   The nearest point on the FULL circle to P is the radial foot O + r*(P-O)/|P-O|,
   at distance ||P-O| - r|.  If that foot lies on the arc A->B->C the answer is
   that radial distance; otherwise the nearest arc point is an endpoint, so the
   answer is min(|P-A|, |P-C|).  We always take the min with the endpoint
   distances (radial foot is the global circle-nearest, so when it is on the arc
   it already dominates; gating it on arc membership is what makes off-arc feet
   fall back to the endpoints).

   The on-arc-sector membership is the only genuinely new geometry; the rest is
   sqrt of an exact rational.  Membership uses atan2 (CCW angle interval from A
   through B to C) -> INTERFACE-BOUNDARY float (atan2/sqrt, no Coq-extractable
   form), off the exact circumcentre_q centre.

   Input:  lines 2..5 = arc_start, arc_mid, arc_end, query point P ("x y").
   Output: "<dist>" (%h); "DEGENERATE" (collinear arc); "NAN" (non-finite). *)
let run_arc_distance () =
  let a = parse_point (input_line stdin) in
  let b = parse_point (input_line stdin) in
  let c = parse_point (input_line stdin) in
  let p = parse_point (input_line stdin) in
  if not (finite_bpoint a && finite_bpoint b && finite_bpoint c && finite_bpoint p)
  then print_endline "NAN"
  else match circumcentre_q (qf a.bx, qf a.by_) (qf b.bx, qf b.by_)
               (qf c.bx, qf c.by_) with
    | None -> print_endline "DEGENERATE"
    | Some (ox, oy, r2) ->
        let oxf = Q.to_float ox and oyf = Q.to_float oy in
        let r = sqrt (Q.to_float r2) in
        let hypot2 dx dy = sqrt (dx *. dx +. dy *. dy) in
        let dpA = hypot2 (p.bx -. a.bx) (p.by_ -. a.by_) in
        let dpC = hypot2 (p.bx -. c.bx) (p.by_ -. c.by_) in
        let cand = ref (if dpA <= dpC then dpA else dpC) in
        let d = hypot2 (p.bx -. oxf) (p.by_ -. oyf) in
        if d > 0.0 then begin
          let twopi = 2.0 *. Float.pi in
          let ccw f t = let x = mod_float (t -. f) twopi in if x < 0.0 then x +. twopi else x in
          let ang qx qy = atan2 (qy -. oyf) (qx -. oxf) in
          let angA = ang a.bx a.by_ in
          let dAB = ccw angA (ang b.bx b.by_) in
          let dAC = ccw angA (ang c.bx c.by_) in
          let dAP = ccw angA (ang p.bx p.by_) in
          let on_arc = if dAB <= dAC then dAP <= dAC else dAP >= dAC in
          if on_arc then begin
            let radial = abs_float (d -. r) in
            if radial < !cand then cand := radial
          end
        end;
        Printf.printf "%h\n" !cand

(* Is the circle point (qx,qy) -- assumed ON the circumcircle of arc A->B->C
   about centre (ox,oy) -- within the arc's angular span?  CCW angle-interval
   test from A through B to C (the same membership ARC_DISTANCE uses inline);
   inclusive at the endpoints.  atan2 (transcendental) -> interface-boundary. *)
let point_on_arc_sector (ox, oy) (a : bPoint) (b : bPoint) (c : bPoint) (qx, qy) =
  let twopi = 2.0 *. Float.pi in
  let ccw f t = let x = mod_float (t -. f) twopi in if x < 0.0 then x +. twopi else x in
  let ang px py = atan2 (py -. oy) (px -. ox) in
  let angA = ang a.bx a.by_ in
  let dAB = ccw angA (ang b.bx b.by_) in
  let dAC = ccw angA (ang c.bx c.by_) in
  let dAQ = ccw angA (ang qx qy) in
  (* Inclusive at BOTH endpoints.  In the clockwise-swept branch (dAB > dAC)
     the in-span set is {A} U [dAC, 2pi): the start A wraps to dAQ = 0, so a
     bare `dAQ >= dAC` would drop A (orientation-dependent endpoint loss --
     e.g. a tangency or shared vertex exactly at A).  Re-include dAQ = 0. *)
  if dAB <= dAC then dAQ <= dAC else (dAQ >= dAC || dAQ = 0.0)

(* ----- ARC_ARC_XY (issue #64 #5b / N-AA): arc-arc intersection coordinates.
   ---------------------------------------------------------------------------
   The intersection POINTS of two circular arcs, enumerated.  Two circumcircles
   (centres O1,O2, squared radii r1^2,r2^2 -- all EXACT via circumcentre_q) meet
   on the radical line: with d = |O1 O2|, a = (d^2 + r1^2 - r2^2)/(2 d) the signed
   distance from O1 to the radical foot M = O1 + (a/d)(O2-O1), and h = sqrt(r1^2 -
   a^2) the half-chord, the circle intersections are M +/- h * perp(O2-O1)/d.
   Each is then kept only if it lies in BOTH arc spans (point_on_arc_sector).

   INTERFACE-BOUNDARY float: the coordinates carry an irrational sqrt(discriminant)
   (no Coq-extractable form, like ARC_LINE_XY), computed off the EXACT
   circumcentre_q centres/radii so the only rounding is the final sqrt/atan2.
   This is the oracle pin for N-AA; the unconditional coordinate SOUNDNESS proof
   stays the deferred #5b frontier (theories/ArcArcSound.v has the shared-vertex
   + conditional-floor slice).

   Input:  lines 2..7 = arc1 (start,mid,end), arc2 (start,mid,end) ("x y").
   Output: "<n>" then n*(" <x> <y>") on one line, n in {0,1,2} = arc-arc
           intersection points (the +h point first); "DEGENERATE" (either arc
           collinear); "COINCIDENT" (identical circumcircles); "NAN". *)
let run_arc_arc_xy () =
  let a1 = parse_point (input_line stdin) in
  let b1 = parse_point (input_line stdin) in
  let c1 = parse_point (input_line stdin) in
  let a2 = parse_point (input_line stdin) in
  let b2 = parse_point (input_line stdin) in
  let c2 = parse_point (input_line stdin) in
  if not (finite_bpoint a1 && finite_bpoint b1 && finite_bpoint c1 &&
          finite_bpoint a2 && finite_bpoint b2 && finite_bpoint c2)
  then print_endline "NAN"
  else match circumcentre_q (qf a1.bx, qf a1.by_) (qf b1.bx, qf b1.by_)
                 (qf c1.bx, qf c1.by_),
             circumcentre_q (qf a2.bx, qf a2.by_) (qf b2.bx, qf b2.by_)
                 (qf c2.bx, qf c2.by_) with
    | None, _ | _, None -> print_endline "DEGENERATE"
    | Some (o1x, o1y, r1sq), Some (o2x, o2y, r2sq) ->
        (* exact squared centre distance *)
        let dq = Q.add (Q.mul (Q.sub o2x o1x) (Q.sub o2x o1x))
                       (Q.mul (Q.sub o2y o1y) (Q.sub o2y o1y)) in
        if qeq dq q0 then
          (if qeq r1sq r2sq then print_endline "COINCIDENT"
           else print_endline "0")            (* concentric, distinct radii: no meet *)
        else begin
          let o1xf = Q.to_float o1x and o1yf = Q.to_float o1y in
          let o2xf = Q.to_float o2x and o2yf = Q.to_float o2y in
          let r1f = Q.to_float r1sq and r2f = Q.to_float r2sq in
          let d2 = Q.to_float dq in
          let d = sqrt d2 in
          let a = (d2 +. r1f -. r2f) /. (2.0 *. d) in
          let h2 = r1f -. a *. a in
          if h2 < 0.0 then print_endline "0"   (* circles do not meet *)
          else begin
            let h = sqrt (if h2 < 0.0 then 0.0 else h2) in
            let ux = (o2xf -. o1xf) /. d and uy = (o2yf -. o1yf) /. d in
            let mx = o1xf +. a *. ux and my = o1yf +. a *. uy in
            (* M +/- h * perp(u), perp(ux,uy) = (-uy, ux) *)
            let p_plus  = (mx -. h *. uy, my +. h *. ux) in
            let p_minus = (mx +. h *. uy, my -. h *. ux) in
            let cands = if h = 0.0 then [p_plus] else [p_plus; p_minus] in
            let keep (qx, qy) =
              point_on_arc_sector (o1xf, o1yf) a1 b1 c1 (qx, qy) &&
              point_on_arc_sector (o2xf, o2yf) a2 b2 c2 (qx, qy) in
            let pts = List.filter keep cands in
            Printf.printf "%d" (List.length pts);
            List.iter (fun (x, y) -> Printf.printf " %h %h" x y) pts;
            print_newline ()
          end
        end

(* ----- ARC_SEGMENT_XY (issue #224 W1 / N-AL): arc-SEGMENT intersection coords.
   ---------------------------------------------------------------------------
   Intersection POINTS of a circular arc with a line SEGMENT, enumerated -- the
   segment analogue of ARC_ARC_XY, and the usable replacement for the
   single-point ARC_LINE_XY (which returns -inf/-nan on a 2-crossing line).

   The arc's circumcircle (centre O, squared radius r^2 -- EXACT via
   circumcentre_q) meets the segment's supporting line where, with u the unit
   direction P->Q, F = P + s(Q-P) the perpendicular foot (s = (O-P).(Q-P)/|PQ|^2),
   d = |O F| and h = sqrt(r^2 - d^2): the circle intersections are F +- h u, at
   line parameters t = s +- h/|PQ|.  Each is kept iff it lies in the arc's sweep
   (point_on_arc_sector) AND on the segment (0 <= t <= 1).  The count decision
   r^2 - d^2 >/=/< 0 and the foot are EXACT Q (no float-tangency sign flip);
   only the final sqrt and the emitted coordinates round.

   Backed by theories/ArcSegmentCircles.v: line_circle_radical_point (F +- h u
   lie on the circle) and arc_line_circle_intersect (the witness has
   inCircle_R = 0 and lies on the line).

   Input:  lines 2..4 = arc (start,mid,end), lines 5..6 = segment P, Q ("x y").
   Output: "<n>" then n*(" <x> <y>"), n in {0,1,2} (the t = s+h/|PQ| point
           first); "DEGENERATE" (arc collinear OR zero-length segment); "NAN". *)
let run_arc_segment_xy () =
  let a1 = parse_point (input_line stdin) in
  let b1 = parse_point (input_line stdin) in
  let c1 = parse_point (input_line stdin) in
  let p  = parse_point (input_line stdin) in
  let q  = parse_point (input_line stdin) in
  if not (finite_bpoint a1 && finite_bpoint b1 && finite_bpoint c1 &&
          finite_bpoint p && finite_bpoint q)
  then print_endline "NAN"
  else match circumcentre_q (qf a1.bx, qf a1.by_) (qf b1.bx, qf b1.by_)
                 (qf c1.bx, qf c1.by_) with
    | None -> print_endline "DEGENERATE"
    | Some (ox, oy, r2) ->
        (* exact segment vector and squared length *)
        let dxq = Q.sub (qf q.bx) (qf p.bx)
        and dyq = Q.sub (qf q.by_) (qf p.by_) in
        let l2q = Q.add (Q.mul dxq dxq) (Q.mul dyq dyq) in
        if qeq l2q q0 then print_endline "DEGENERATE"  (* zero-length segment *)
        else begin
          (* exact perpendicular foot F = P + s(Q-P), s = (O-P).(Q-P)/|PQ|^2 *)
          let projn = Q.add (Q.mul (Q.sub ox (qf p.bx)) dxq)
                            (Q.mul (Q.sub oy (qf p.by_)) dyq) in
          let s   = Q.div projn l2q in
          let fxq = Q.add (qf p.bx)  (Q.mul s dxq)
          and fyq = Q.add (qf p.by_) (Q.mul s dyq) in
          (* exact squared perpendicular distance and discriminant *)
          let d2q = Q.add (Q.mul (Q.sub ox fxq) (Q.sub ox fxq))
                          (Q.mul (Q.sub oy fyq) (Q.sub oy fyq)) in
          let h2q = Q.sub r2 d2q in
          if qlt h2q q0 then print_endline "0"        (* line misses the circle *)
          else begin
            let oxf = Q.to_float ox and oyf = Q.to_float oy in
            let lf  = sqrt (Q.to_float l2q) in
            let uxf = (q.bx -. p.bx) /. lf and uyf = (q.by_ -. p.by_) /. lf in
            let fxf = Q.to_float fxq and fyf = Q.to_float fyq in
            let sf  = Q.to_float s in
            let hf  = sqrt (Q.to_float h2q) in
            let hl  = hf /. lf in
            (* F +- h u, at line parameters t = s +- h/|PQ| *)
            let p_plus  = (fxf +. hf *. uxf, fyf +. hf *. uyf, sf +. hl) in
            let p_minus = (fxf -. hf *. uxf, fyf -. hf *. uyf, sf -. hl) in
            let cands = if hf = 0.0 then [p_plus] else [p_plus; p_minus] in
            let keep (qx, qy, t) =
              t >= 0.0 && t <= 1.0 &&
              point_on_arc_sector (oxf, oyf) a1 b1 c1 (qx, qy) in
            let pts = List.filter keep cands in
            Printf.printf "%d" (List.length pts);
            List.iter (fun (x, y, _) -> Printf.printf " %h %h" x y) pts;
            print_newline ()
          end
        end

(* ----- ARC_ARC_DISTANCE (D-AA, JTS #1195 §7): arc-to-arc shortest distance.
   ---------------------------------------------------------------------------
   The minimum distance between two circular arcs.  By the critical-pair
   analysis the minimiser is one of: (a) the two interior radial feet on the
   line O1 O2 when the circumcircles are DISJOINT (external d >= r1+r2, gap
   d-r1-r2; internal d < |r1-r2|, gap |r1-r2|-d) AND both feet lie in their
   sweeps; (b) 0, when the circumcircles intersect and a real intersection lies
   in BOTH sweeps; or (c) an endpoint of one arc against the other arc (the
   point-to-arc distance, reusing the ARC_DISTANCE radial-foot/endpoint shape).
   We take the min over all that apply -- each candidate is a genuine
   arc1-point/arc2-point pair, and the analysis guarantees the true minimiser
   is among them.

   Centres / radii² / squared centre distance are EXACT (circumcentre_q); only
   the final sqrt / atan2 (sector membership) round -- INTERFACE-BOUNDARY float,
   off the certified rational kernel.  Proof companion: theories/ArcArcDistance.v
   (two_circles_dist_lower + circle_feet_dist => two_circles_dist_radial /
   arc_arc_dist_external) certifies the disjoint circle-to-circle core; the
   sweep clamp stays the deferred atan2 layer (as for ARC_DISTANCE).

   Input:  lines 2..4 = arc1 (start,mid,end), lines 5..7 = arc2 (start,mid,end).
   Output: "<dist>" (%h); "DEGENERATE" (either arc collinear); "NAN". *)
let run_arc_arc_distance () =
  let a1 = parse_point (input_line stdin) in
  let b1 = parse_point (input_line stdin) in
  let c1 = parse_point (input_line stdin) in
  let a2 = parse_point (input_line stdin) in
  let b2 = parse_point (input_line stdin) in
  let c2 = parse_point (input_line stdin) in
  if not (finite_bpoint a1 && finite_bpoint b1 && finite_bpoint c1 &&
          finite_bpoint a2 && finite_bpoint b2 && finite_bpoint c2)
  then print_endline "NAN"
  else match circumcentre_q (qf a1.bx, qf a1.by_) (qf b1.bx, qf b1.by_)
                 (qf c1.bx, qf c1.by_),
             circumcentre_q (qf a2.bx, qf a2.by_) (qf b2.bx, qf b2.by_)
                 (qf c2.bx, qf c2.by_) with
    | None, _ | _, None -> print_endline "DEGENERATE"
    | Some (o1x, o1y, r1sq), Some (o2x, o2y, r2sq) ->
        let o1xf = Q.to_float o1x and o1yf = Q.to_float o1y in
        let o2xf = Q.to_float o2x and o2yf = Q.to_float o2y in
        let r1 = sqrt (Q.to_float r1sq) and r2 = sqrt (Q.to_float r2sq) in
        let dq = Q.add (Q.mul (Q.sub o2x o1x) (Q.sub o2x o1x))
                       (Q.mul (Q.sub o2y o1y) (Q.sub o2y o1y)) in
        let d = sqrt (Q.to_float dq) in
        let hypot2 dx dy = sqrt (dx *. dx +. dy *. dy) in
        (* point-to-arc distance: radial foot when the point's ray hits the
           sweep, else the nearer chord endpoint (the ARC_DISTANCE kernel). *)
        let point_arc_dist (oxf, oyf, r) (a : bPoint) (b : bPoint) (c : bPoint)
                           (px, py) =
          let dpA = hypot2 (px -. a.bx) (py -. a.by_) in
          let dpC = hypot2 (px -. c.bx) (py -. c.by_) in
          let best = ref (if dpA <= dpC then dpA else dpC) in
          let dp = hypot2 (px -. oxf) (py -. oyf) in
          if dp > 0.0 && point_on_arc_sector (oxf, oyf) a b c (px, py) then begin
            let radial = abs_float (dp -. r) in
            if radial < !best then best := radial
          end;
          !best in
        let cand = ref infinity in
        let upd v = if v < !cand then cand := v in
        (* (c) the four endpoint-vs-other-arc distances *)
        upd (point_arc_dist (o2xf, o2yf, r2) a2 b2 c2 (a1.bx, a1.by_));
        upd (point_arc_dist (o2xf, o2yf, r2) a2 b2 c2 (c1.bx, c1.by_));
        upd (point_arc_dist (o1xf, o1yf, r1) a1 b1 c1 (a2.bx, a2.by_));
        upd (point_arc_dist (o1xf, o1yf, r1) a1 b1 c1 (c2.bx, c2.by_));
        if d > 0.0 then begin
          let ux = (o2xf -. o1xf) /. d and uy = (o2yf -. o1yf) /. d in
          (* (a) interior radial feet when the circumcircles are DISJOINT *)
          if d >= r1 +. r2 then begin
            (* external: feet face each other along the line O1 O2 *)
            let f1 = (o1xf +. r1 *. ux, o1yf +. r1 *. uy) in
            let f2 = (o2xf -. r2 *. ux, o2yf -. r2 *. uy) in
            if point_on_arc_sector (o1xf, o1yf) a1 b1 c1 f1
               && point_on_arc_sector (o2xf, o2yf) a2 b2 c2 f2
            then upd (d -. r1 -. r2)
          end else if d < abs_float (r1 -. r2) then begin
            (* internal (nested): both feet on the larger-radius side *)
            let s = if r1 >= r2 then 1.0 else -1.0 in
            let f1 = (o1xf +. s *. r1 *. ux, o1yf +. s *. r1 *. uy) in
            let f2 = (o2xf +. s *. r2 *. ux, o2yf +. s *. r2 *. uy) in
            if point_on_arc_sector (o1xf, o1yf) a1 b1 c1 f1
               && point_on_arc_sector (o2xf, o2yf) a2 b2 c2 f2
            then upd (abs_float (r1 -. r2) -. d)
          end;
          (* (b) 0 when the circumcircles intersect in both sweeps *)
          if d <= r1 +. r2 && d >= abs_float (r1 -. r2) then begin
            let aa = (Q.to_float dq +. Q.to_float r1sq -. Q.to_float r2sq)
                     /. (2.0 *. d) in
            let h2 = Q.to_float r1sq -. aa *. aa in
            if h2 >= 0.0 then begin
              let h = sqrt h2 in
              let mx = o1xf +. aa *. ux and my = o1yf +. aa *. uy in
              let both (qx, qy) =
                point_on_arc_sector (o1xf, o1yf) a1 b1 c1 (qx, qy)
                && point_on_arc_sector (o2xf, o2yf) a2 b2 c2 (qx, qy) in
              if both (mx -. h *. uy, my +. h *. ux)
                 || both (mx +. h *. uy, my -. h *. ux)
              then upd 0.0
            end
          end
        end;
        Printf.printf "%h\n" !cand

(* ----- CURVE_SNAP_DECISION / CURVE_SNAP_INVARIANTS_EXACT (PRC-SN, JTS#1195,
   proofs#66). ---------------------------------------------------------------

   Reduce the precision of a circular arc by snapping its 3 control points to a
   1/scale grid (exact Q via q_make_precise), then decide whether the snapped
   arc can be kept (PRESERVE) or must be DENSIFYd to a polyline.  JTS's
   isGridFriendly keeps the arc iff the circumcentre of the SNAPPED controls is
   itself on the grid; doing it in exact Q catches the double-rounding loss that
   JTS's binary64 centre computation hides on large / sub-grid coordinates.
   No transcendentals and no float -- a single EXACT mode, ratchet-clean (no
   interface-boundary float needed, unlike ARC_LENGTH/ARC_AREA).  (Replaces the
   main 9235847 stub that always emitted PRESERVE.)

   Input (both modes):  line 2 = <scale> (int), lines 3..5 = A, B, C.
   CURVE_SNAP_DECISION         -> PRESERVE | DENSIFY | DEGEN | NAN.
   CURVE_SNAP_INVARIANTS_EXACT -> "<ox> <oy> <r2> <centre_on_grid 0|1>" (exact
     rationals of the snapped circumcentre + flag), or DEGEN / NAN.  r2 is
     emitted so a consumer can apply its own grid-radius test (r is a grid
     multiple iff r2*scale^2 is a perfect square) without that test gating the
     verdict here -- parity with the JTS reference, which keys on the centre. *)

let snap_controls scale a b c =
  let snap p = (q_make_precise scale (qf p.bx), q_make_precise scale (qf p.by_)) in
  (snap a, snap b, snap c)

let centre_on_grid scale ox oy =
  qeq (q_make_precise scale ox) ox && qeq (q_make_precise scale oy) oy

let run_curve_snap_decision () =
  let scale = int_of_string (String.trim (input_line stdin)) in
  let a = parse_point (input_line stdin) in
  let b = parse_point (input_line stdin) in
  let c = parse_point (input_line stdin) in
  if not (finite_bpoint a && finite_bpoint b && finite_bpoint c)
  then print_endline "NAN"
  else
    let (sa, sb, sc) = snap_controls scale a b c in
    match circumcentre_q sa sb sc with
    | None -> print_endline "DEGEN"
    | Some (ox, oy, _r2) ->
        print_endline (if centre_on_grid scale ox oy then "PRESERVE" else "DENSIFY")

let run_curve_snap_invariants_exact () =
  let scale = int_of_string (String.trim (input_line stdin)) in
  let a = parse_point (input_line stdin) in
  let b = parse_point (input_line stdin) in
  let c = parse_point (input_line stdin) in
  if not (finite_bpoint a && finite_bpoint b && finite_bpoint c)
  then print_endline "NAN"
  else
    let (sa, sb, sc) = snap_controls scale a b c in
    match circumcentre_q sa sb sc with
    | None -> print_endline "DEGEN"
    | Some (ox, oy, r2) ->
        Printf.printf "%s %s %s %d\n"
          (Q.to_string ox) (Q.to_string oy) (Q.to_string r2)
          (if centre_on_grid scale ox oy then 1 else 0)

(* ----- SNAP_SCALED mode (extracted, exactness-backed). ------------------- *)

(* Direct extract of `b64_snap_coord_scaled` from SnapRoundingScale_b64.v:
   snap to the grid of spacing 1/scale via round(x*scale)/scale.  Proven
   (`b64_snap_coord_scaled_B2R`) to compute the R-side `snap_round_coord`
   EXACTLY when scale is a power of two -- the C1 power-of-two generalisation
   of the unit-grid `b64_snap_coord`.  Input: the scale (binary64), then a
   point P; output the snapped point. *)
let run_snap_scaled () =
  let scale = float_of_string (String.trim (input_line stdin)) in
  let p     = parse_point (input_line stdin) in
  print_point { bx  = b64_snap_coord_scaled p.bx  scale;
                by_ = b64_snap_coord_scaled p.by_ scale }

(* ----- RELATE_MATRIX / RELATE_PREDICATE (issue #67 S11). ----------------- *)

let run_relate_matrix () =
  let key = String.trim (input_line stdin) in
  print_endline (Relate_matrix.resolve_matrix_input key)

let run_relate_predicate () =
  let matrix_key = String.trim (input_line stdin) in
  let predicate  = String.trim (input_line stdin) in
  let holds = Relate_matrix.check_predicate matrix_key predicate in
  print_endline (if holds then "TRUE" else "FALSE")

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
       | "TWOSUM"                   -> run_twosum ()
       | "GROW_EXPANSION"           -> run_grow_expansion ()
       | "INTERSECT_FILTERED"       -> run_intersect_filtered ()
       | "INTERSECT_POINT_FILTERED" -> run_intersect_point_filtered ()
       | "INTERSECT_POINT_XY"       -> run_intersect_point_xy ()
       | "PASSES_THROUGH_FILTER"    -> run_passes_through_filter ()
       | "PASSES_THROUGH_HALFOPEN"  -> run_passes_through_halfopen ()
       | "HOLE_PRECISION_AUDIT"          -> run_hole_precision_audit ()
       | "HOLES_SURVIVE_PRECISION"       -> run_holes_survive_precision ()
       | "PASSES_THROUGH_EXACT"          -> run_passes_through_exact ()
       | "PASSES_THROUGH_HALFOPEN_EXACT" -> run_passes_through_halfopen_exact ()
       | "ARC_LENGTH_INVARIANTS_EXACT"              -> run_arc_length_invariants_exact ()
       | "ARC_LENGTH"                    -> run_arc_length ()
       | "ARC_SHORTER"                   -> run_arc_shorter ()
       | "EDGE_IN_RESULT"           -> run_edge_in_result ()
       | "INCIRCLE_SIGN"            -> run_incircle_sign ()
       | "INCIRCLE_EXACT"           -> run_incircle_exact ()
       | "ARC_CHORD_CROSSES_CIRCLE" -> run_arc_chord_crosses_circle ()
       | "ARC_LINE_XY"              -> run_arc_line_xy ()
       | "ARC_PASSES_THROUGH_PIXEL" -> run_arc_passes_through_pixel ()
       | "ARC_AREA_INVARIANTS_EXACT"    -> run_arc_area_invariants_exact ()
       | "ARC_AREA"                 -> run_arc_area ()
       | "ARC_CENTROID"             -> run_arc_centroid ()
       | "ARC_AREA_CENTROID"        -> run_arc_area_centroid ()
       | "ARC_DISTANCE"             -> run_arc_distance ()
       | "ARC_ARC_XY"               -> run_arc_arc_xy ()
       | "ARC_SEGMENT_XY"           -> run_arc_segment_xy ()
       | "ARC_ARC_DISTANCE"         -> run_arc_arc_distance ()
       | "CURVE_SNAP_DECISION"          -> run_curve_snap_decision ()
       | "CURVE_SNAP_INVARIANTS_EXACT"  -> run_curve_snap_invariants_exact ()
       | "SNAP_SCALED"                  -> run_snap_scaled ()
       | "RELATE_MATRIX"                -> run_relate_matrix ()
       | "RELATE_PREDICATE"             -> run_relate_predicate ()
       | other -> failwith (Printf.sprintf "oracle: unknown mode: %s" other));
      flush stdout;
      loop ()
  in
  loop ()
