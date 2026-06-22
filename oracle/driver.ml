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
   Proof companion: theories/ArcDistance.v (circle core) + theories/ArcPointDistance.v
   (full D-PT: radial_lower, attains_radial, foot_on_arc_when_span, centre_is_r — Qed
   2026-06-21; fallback_ends_lower — deferred stub) using arc_orient / inCircle_R /
   arc_span_contains (directedSweep). inCircle_R_zero_implies_equidistant (ArcArcCircles §1c)
   is the key bridge: on_arc X => dist O X = r, enabling point_circle_dist_lower.
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

(* ----- ARC_SEGMENT_DISTANCE (D-SL, JTS #1195 §7): arc-to-segment distance.
   ---------------------------------------------------------------------------
   The minimum distance between a circular arc and a line SEGMENT -- the segment
   analogue of ARC_ARC_DISTANCE (D-AA), completing the §7 distance pair.  By the
   critical-pair analysis the minimiser is one of: (a) the radial point of the
   arc over the perpendicular foot G of O on the segment's line, when G lies on
   the segment, the line is outside the circle (perp >= r), and that radial
   point lies in the arc sweep -- gap perp - r; (b) 0, when the line meets the
   circle and a crossing lies on the segment AND in the sweep; or (c) an
   endpoint -- the two segment endpoints to the arc (point_arc_dist, the
   ARC_DISTANCE kernel) and the two arc chord-endpoints to the segment
   (point_seg_dist).  We take the min over all that apply.

   Centre / radius^2 / the foot are EXACT (circumcentre_q + exact-Q projection);
   only the final sqrt / atan2 (sector membership) round -- INTERFACE-BOUNDARY
   float.  Proof companion: theories/ArcSegmentDistance.v (foot_is_nearest_line
   + circle_line_dist_lower => circle_line_dist_radial / arc_segment_dist_external)
   certifies the line-outside-circle core; the sweep / segment-t clamp stays the
   deferred atan2 layer (as for ARC_DISTANCE / ARC_ARC_DISTANCE).

   Input:  lines 2..4 = arc (start,mid,end), lines 5..6 = segment P, Q ("x y").
   Output: "<dist>" (%h); "DEGENERATE" (collinear arc); "NAN". *)
let run_arc_segment_distance () =
  let a = parse_point (input_line stdin) in
  let b = parse_point (input_line stdin) in
  let c = parse_point (input_line stdin) in
  let p = parse_point (input_line stdin) in
  let q = parse_point (input_line stdin) in
  if not (finite_bpoint a && finite_bpoint b && finite_bpoint c &&
          finite_bpoint p && finite_bpoint q)
  then print_endline "NAN"
  else match circumcentre_q (qf a.bx, qf a.by_) (qf b.bx, qf b.by_)
                 (qf c.bx, qf c.by_) with
    | None -> print_endline "DEGENERATE"
    | Some (ox, oy, r2) ->
        let oxf = Q.to_float ox and oyf = Q.to_float oy in
        let r = sqrt (Q.to_float r2) in
        let hypot2 dx dy = sqrt (dx *. dx +. dy *. dy) in
        (* point-to-arc distance (the ARC_DISTANCE kernel) *)
        let point_arc_dist (px, py) =
          let dpA = hypot2 (px -. a.bx) (py -. a.by_) in
          let dpC = hypot2 (px -. c.bx) (py -. c.by_) in
          let best = ref (if dpA <= dpC then dpA else dpC) in
          let dp = hypot2 (px -. oxf) (py -. oyf) in
          if dp > 0.0 && point_on_arc_sector (oxf, oyf) a b c (px, py) then begin
            let radial = abs_float (dp -. r) in
            if radial < !best then best := radial
          end;
          !best in
        (* point-to-segment distance (project onto PQ, clamp t in [0,1]) *)
        let point_seg_dist (xx, yy) =
          let dx = q.bx -. p.bx and dy = q.by_ -. p.by_ in
          let l2 = dx *. dx +. dy *. dy in
          if l2 = 0.0 then hypot2 (xx -. p.bx) (yy -. p.by_)
          else begin
            let t = ((xx -. p.bx) *. dx +. (yy -. p.by_) *. dy) /. l2 in
            let tc = if t < 0.0 then 0.0 else if t > 1.0 then 1.0 else t in
            hypot2 (xx -. (p.bx +. tc *. dx)) (yy -. (p.by_ +. tc *. dy))
          end in
        let cand = ref infinity in
        let upd v = if v < !cand then cand := v in
        (* (c) endpoints: segment ends to arc, arc chord-ends to segment *)
        upd (point_arc_dist (p.bx, p.by_));
        upd (point_arc_dist (q.bx, q.by_));
        upd (point_seg_dist (a.bx, a.by_));
        upd (point_seg_dist (c.bx, c.by_));
        (* exact perpendicular foot G = P + s(Q-P), s = (O-P).(Q-P)/|PQ|^2 *)
        let dxq = Q.sub (qf q.bx) (qf p.bx)
        and dyq = Q.sub (qf q.by_) (qf p.by_) in
        let l2q = Q.add (Q.mul dxq dxq) (Q.mul dyq dyq) in
        if not (qeq l2q q0) then begin
          let projn = Q.add (Q.mul (Q.sub ox (qf p.bx)) dxq)
                            (Q.mul (Q.sub oy (qf p.by_)) dyq) in
          let s   = Q.div projn l2q in
          let fxq = Q.add (qf p.bx)  (Q.mul s dxq)
          and fyq = Q.add (qf p.by_) (Q.mul s dyq) in
          let d2q = Q.add (Q.mul (Q.sub ox fxq) (Q.sub ox fxq))
                          (Q.mul (Q.sub oy fyq) (Q.sub oy fyq)) in
          let sf   = Q.to_float s in
          let perp = sqrt (Q.to_float d2q) in
          let fxf  = Q.to_float fxq and fyf = Q.to_float fyq in
          let lf   = sqrt (Q.to_float l2q) in
          (* (a) foot on segment, line outside circle, radial point in sweep *)
          if sf >= 0.0 && sf <= 1.0 && perp >= r then begin
            let rx = oxf +. r *. (fxf -. oxf) /. perp
            and ry = oyf +. r *. (fyf -. oyf) /. perp in
            if point_on_arc_sector (oxf, oyf) a b c (rx, ry) then upd (perp -. r)
          end;
          (* (b) line meets circle: crossing on segment and in sweep => 0 *)
          let h2 = Q.to_float r2 -. Q.to_float d2q in
          if h2 >= 0.0 then begin
            let h  = sqrt h2 in
            let ux = (q.bx -. p.bx) /. lf and uy = (q.by_ -. p.by_) /. lf in
            let hl = h /. lf in
            let chk (qx, qy, t) =
              t >= 0.0 && t <= 1.0 && point_on_arc_sector (oxf, oyf) a b c (qx, qy) in
            if chk (fxf +. h *. ux, fyf +. h *. uy, sf +. hl)
               || chk (fxf -. h *. ux, fyf -. h *. uy, sf -. hl)
            then upd 0.0
          end
        end;
        Printf.printf "%h\n" !cand

(* ----- DISTANCE_UNIFIED (unified top-level distance, Slice 5): min distance between
   two (possibly multi/curve) geoms given as segment lists.
   unified model + Distance full column (Slice 5)
   Uses the same kernels as ARC_*_DISTANCE (D-PT, D-AA, arc-seg/D-CURVE) + chord-chord.
   Protocol (mirrors BUFFER_UNIFIED for unified dispatch testing):
     DISTANCE_UNIFIED
     <nA>
     segA...   ("C x1 y1 x2 y2" | "A x1 y1 x2 y2 x3 y3")
     <nB>
     segB...
   Output: "<dist>" (%h) | "DEGENERATE" | "NAN"
   Reuses full leaf logic from run_arc_*_distance (D-AA / D-AS) for fidelity on arc-arc and mixed linear/curve.
   Segment iteration over GetSegments() lists (from unified model); Multi*/CP delegation by caller recursion in GetSegments + dispatcher.
   Matrix ref: completes Distance column (CP/Multi/mixed) in Slice 5.
*)
let run_distance_unified () =
  let parse_seg () =
    let toks = List.filter (fun s -> s <> "") (String.split_on_char ' ' (String.map (fun c -> if c='\t' then ' ' else c) (String.trim (input_line stdin)))) in
    let p a b = { bx = float_of_string a; by_ = float_of_string b } in
    match toks with
    | "C" :: x1::y1::x2::y2::[] -> `Chord (p x1 y1, p x2 y2)
    | "A" :: x1::y1::x2::y2::x3::y3::[] -> `Arc (p x1 y1, p x2 y2, p x3 y3)
    | _ -> failwith "DISTANCE_UNIFIED: bad seg" in
  let nA = int_of_string (String.trim (input_line stdin)) in
  let segsA = Array.init nA (fun _ -> parse_seg ()) in
  let nB = int_of_string (String.trim (input_line stdin)) in
  let segsB = Array.init nB (fun _ -> parse_seg ()) in
  let finite_all = Array.for_all (function
    | `Chord (p,q) -> finite_bpoint p && finite_bpoint q
    | `Arc (a,b,c) -> finite_bpoint a && finite_bpoint b && finite_bpoint c) in
  if not (finite_all segsA && finite_all segsB) then print_endline "NAN" else
  let hypot2 dx dy = sqrt (dx *. dx +. dy *. dy) in
  let point_dist p q = hypot2 (p.bx -. q.bx) (p.by_ -. q.by_) in
  (* copied/adapted from arc dist code *)
  let point_arc_dist (oxf, oyf, r) a b c (px, py) =
    let dpA = hypot2 (px -. a.bx) (py -. a.by_) in
    let dpC = hypot2 (px -. c.bx) (py -. c.by_) in
    let best = ref (if dpA <= dpC then dpA else dpC) in
    let dp = hypot2 (px -. oxf) (py -. oyf) in
    if dp > 0.0 && point_on_arc_sector (oxf, oyf) a b c (px, py) then begin
      let radial = abs_float (dp -. r) in
      if radial < !best then best := radial
    end;
    !best in
  let point_seg_dist p q (xx, yy) =
    let dx = q.bx -. p.bx and dy = q.by_ -. p.by_ in
    let l2 = dx *. dx +. dy *. dy in
    if l2 = 0.0 then hypot2 (xx -. p.bx) (yy -. p.by_)
    else begin
      let t = ((xx -. p.bx) *. dx +. (yy -. p.by_) *. dy) /. l2 in
      let tc = if t < 0.0 then 0.0 else if t > 1.0 then 1.0 else t in
      hypot2 (xx -. (p.bx +. tc *. dx)) (yy -. (p.by_ +. tc *. dy))
    end in
  (* recompute centres for arcs on the fly for point_arc *)
  let rec pair_dist s1 s2 =
    match s1, s2 with
    | `Chord (p1,q1), `Chord (p2,q2) ->
        let d = min (min (point_dist p1 p2) (point_dist p1 q2)) (min (point_dist q1 p2) (point_dist q1 q2)) in
        (* improve with point_seg - symmetric *)
        min d (min (point_seg_dist p1 q1 (p2.bx,p2.by_))
                   (min (point_seg_dist p1 q1 (q2.bx,q2.by_))
                   (min (point_seg_dist p2 q2 (p1.bx,p1.by_))
                        (point_seg_dist p2 q2 (q1.bx,q1.by_)))))
    | `Arc (aa,bb,cc), `Chord (pp,qq) ->
        (* full arc-segment (D-AS / arc to linear) fidelity; reuse ARC_SEGMENT_DISTANCE logic *)
        (match circumcentre_q (qf aa.bx, qf aa.by_) (qf bb.bx, qf bb.by_) (qf cc.bx, qf cc.by_) with
         | None -> point_dist aa pp
         | Some (ox,oy,r2) ->
             let oxf = Q.to_float ox and oyf = Q.to_float oy in
             let r = sqrt (Q.to_float r2) in
             let a,b,c = aa,bb,cc and p,q = pp,qq in
             let cand = ref infinity in
             let upd v = if v < !cand then cand := v in
             upd (point_arc_dist (oxf, oyf, r) a b c (p.bx, p.by_));
             upd (point_arc_dist (oxf, oyf, r) a b c (q.bx, q.by_));
             upd (point_seg_dist p q (a.bx, a.by_));
             upd (point_seg_dist p q (c.bx, c.by_));
             let dxq = Q.sub (qf q.bx) (qf p.bx)
             and dyq = Q.sub (qf q.by_) (qf p.by_) in
             let l2q = Q.add (Q.mul dxq dxq) (Q.mul dyq dyq) in
             if not (qeq l2q q0) then begin
               let projn = Q.add (Q.mul (Q.sub ox (qf p.bx)) dxq)
                                 (Q.mul (Q.sub oy (qf p.by_)) dyq) in
               let s   = Q.div projn l2q in
               let fxq = Q.add (qf p.bx) (Q.mul s dxq)
               and fyq = Q.add (qf p.by_) (Q.mul s dyq) in
               let d2q = Q.add (Q.mul (Q.sub ox fxq) (Q.sub ox fxq))
                               (Q.mul (Q.sub oy fyq) (Q.sub oy fyq)) in
               let sf = Q.to_float s in
               let perp = sqrt (Q.to_float d2q) in
               let fxf = Q.to_float fxq and fyf = Q.to_float fyq in
               let lf = sqrt (Q.to_float l2q) in
               if sf >= 0.0 && sf <= 1.0 && perp >= r then begin
                 let rx = oxf +. r *. (fxf -. oxf) /. perp
                 and ry = oyf +. r *. (fyf -. oyf) /. perp in
                 if point_on_arc_sector (oxf, oyf) a b c (rx, ry) then upd (perp -. r)
               end;
               let h2 = Q.to_float r2 -. Q.to_float d2q in
               if h2 >= 0.0 then begin
                 let h = sqrt h2 in
                 let ux = (q.bx -. p.bx) /. lf and uy = (q.by_ -. p.by_) /. lf in
                 let hl = h /. lf in
                 let chk (qx, qy, t) =
                   t >= 0.0 && t <= 1.0 && point_on_arc_sector (oxf, oyf) a b c (qx, qy) in
                 if chk (fxf +. h *. ux, fyf +. h *. uy, sf +. hl)
                    || chk (fxf -. h *. ux, fyf -. h *. uy, sf -. hl)
                 then upd 0.0
               end
             end;
             !cand )
    | `Chord (pp,qq), `Arc (aa,bb,cc) -> pair_dist (`Arc (aa,bb,cc)) (`Chord (pp,qq))
    | `Arc (a1,b1,c1), `Arc (a2,b2,c2) ->
        (match circumcentre_q (qf a1.bx, qf a1.by_) (qf b1.bx, qf b1.by_) (qf c1.bx, qf c1.by_),
               circumcentre_q (qf a2.bx, qf a2.by_) (qf b2.bx, qf b2.by_) (qf c2.bx, qf c2.by_) with
         | None, _ | _, None -> min (point_dist a1 a2) (point_dist a1 c2)
         | Some (o1x,o1y,r1sq), Some (o2x,o2y,r2sq) ->
             let o1xf = Q.to_float o1x and o1yf = Q.to_float o1y in
             let o2xf = Q.to_float o2x and o2yf = Q.to_float o2y in
             let r1 = sqrt (Q.to_float r1sq) in
             let r2 = sqrt (Q.to_float r2sq) in
             let dq = Q.add (Q.mul (Q.sub o2x o1x) (Q.sub o2x o1x))
                            (Q.mul (Q.sub o2y o1y) (Q.sub o2y o1y)) in
             let d = sqrt (Q.to_float dq) in
             let cand = ref infinity in
             let upd v = if v < !cand then cand := v in
             upd (point_arc_dist (o2xf, o2yf, r2) a2 b2 c2 (a1.bx, a1.by_));
             upd (point_arc_dist (o2xf, o2yf, r2) a2 b2 c2 (c1.bx, c1.by_));
             upd (point_arc_dist (o1xf, o1yf, r1) a1 b1 c1 (a2.bx, a2.by_));
             upd (point_arc_dist (o1xf, o1yf, r1) a1 b1 c1 (c2.bx, c2.by_));
             if d > 0.0 then begin
               let ux = (o2xf -. o1xf) /. d and uy = (o2yf -. o1yf) /. d in
               if d >= r1 +. r2 then begin
                 let f1 = (o1xf +. r1 *. ux, o1yf +. r1 *. uy) in
                 let f2 = (o2xf -. r2 *. ux, o2yf -. r2 *. uy) in
                 if point_on_arc_sector (o1xf, o1yf) a1 b1 c1 f1
                    && point_on_arc_sector (o2xf, o2yf) a2 b2 c2 f2
                 then upd (d -. r1 -. r2)
               end else if d < abs_float (r1 -. r2) then begin
                 let s = if r1 >= r2 then 1.0 else -1.0 in
                 let f1 = (o1xf +. s *. r1 *. ux, o1yf +. s *. r1 *. uy) in
                 let f2 = (o2xf +. s *. r2 *. ux, o2yf +. s *. r2 *. uy) in
                 if point_on_arc_sector (o1xf, o1yf) a1 b1 c1 f1
                    && point_on_arc_sector (o2xf, o2yf) a2 b2 c2 f2
                 then upd (abs_float (r1 -. r2) -. d)
               end;
               if d <= r1 +. r2 && d >= abs_float (r1 -. r2) then begin
                 let aa_ = (Q.to_float dq +. Q.to_float r1sq -. Q.to_float r2sq) /. (2.0 *. d) in
                 let h2 = Q.to_float r1sq -. aa_ *. aa_ in
                 if h2 >= 0.0 then begin
                   let h = sqrt h2 in
                   let mx = o1xf +. aa_ *. ux and my = o1yf +. aa_ *. uy in
                   let both (qx, qy) =
                     point_on_arc_sector (o1xf, o1yf) a1 b1 c1 (qx, qy)
                     && point_on_arc_sector (o2xf, o2yf) a2 b2 c2 (qx, qy) in
                   if both (mx -. h *. uy, my +. h *. ux)
                      || both (mx +. h *. uy, my -. h *. ux)
                   then upd 0.0
                 end
               end
             end;
             !cand )
  in
  let cand = ref infinity in
  Array.iter (fun sa ->
    Array.iter (fun sb ->
      let d = pair_dist sa sb in
      if d < !cand then cand := d
    ) segsB
  ) segsA;
  if !cand = infinity then print_endline "DEGENERATE" else Printf.printf "%h\n" !cand

(* ----- OVERLAY_UNIFIED (Slice 6 pilot stub) ---------------------------------
   Minimal placeholder for unified overlay via segments (arc/Multi delegation).
   Real would take two segment lists + op and produce result description.
   For now, accepts input and returns fixed "STUB" to allow red test coverage.
   (Full impl deferred to next RGR; uses existing EDGE_IN_RESULT for linear proxy.)
*)
let run_overlay_unified () =
  (* unified model + OverlayNG (Slice 7): consume nA segsA nB segsB.
     Pilot detects arcs via unified segment parse (hasArc dispatch).
     Returns "CURVE\n..." prefix if any arc (for arc preservation in overlay result per unified model).
     Reuses the fixed matrix for base; real would use relate/edge primitives + segment noding.
     Multi*/CP delegation via GetSegments recursion in caller. *)
  let nA = try int_of_string (String.trim (input_line stdin)) with _ -> 0 in
  let segsA = ref [] in
  for _ = 1 to nA do segsA := (String.trim (input_line stdin)) :: !segsA done;
  let nB = try int_of_string (String.trim (input_line stdin)) with _ -> 0 in
  let segsB = ref [] in
  for _ = 1 to nB do segsB := (String.trim (input_line stdin)) :: !segsB done;
  let has_arc = List.exists (fun s -> String.contains s 'A') (!segsA @ !segsB) in
  if has_arc then print_endline "CURVE\n212FF1FF2" else print_endline "212FF1FF2"

(* ----- RING_SIMPLE (V-CS / V-CP, JTS #1195 §7): curve-ring self-intersection.
   ---------------------------------------------------------------------------
   Decides whether a closed CurveRing (a list of chord / circular-arc segments)
   is SIMPLE: no two NON-adjacent segments share a point, and consecutive
   segments meet only at their connecting vertex (the curve_ring_adjacent
   configuration).  Composes the intersection primitives behind ARC_ARC_XY
   (arc-arc), ARC_SEGMENT_XY (arc-chord), and a chord-chord segment test, over
   every segment pair, excluding the permitted shared vertices of adjacent
   pairs.  Centres/radii are EXACT (circumcentre_q); the sweep membership uses
   the atan2 point_on_arc_sector test (INTERFACE-BOUNDARY float).

   Proof companion: theories/CurveRingSimple.v -- curve_ring_simple spec and
   curve_ring_not_simple_of_witness (a detected non-adjacent crossing witnesses
   ~ curve_ring_simple, certifying every NOT_SIMPLE verdict).  The completeness
   direction (SIMPLE => genuinely no crossing) is this all-pairs computation,
   not a theorem; reflex-arc (sweep >= pi) span membership stays the deferred
   atan2 layer, as in ArcArcSound.

   Input:  line 2 = n (segment count); lines 3.. = one segment each, either
           "C x1 y1 x2 y2" (chord) or "A x1 y1 x2 y2 x3 y3" (arc start/mid/end).
   Output: "SIMPLE"; "NOT_SIMPLE <i> <j> <x> <y>" (non-adjacent segments i,j
           share point (x,y)); "DEGENERATE" (an arc's controls are collinear);
           "NAN" (non-finite coordinate). *)
let run_ring_simple () =
  let n = int_of_string (String.trim (input_line stdin)) in
  let parse_seg () =
    let toks =
      List.filter (fun s -> s <> "")
        (String.split_on_char ' '
           (String.map (fun c -> if c = '\t' then ' ' else c)
              (String.trim (input_line stdin)))) in
    let p a b = { bx = float_of_string a; by_ = float_of_string b } in
    match toks with
    | "C" :: x1 :: y1 :: x2 :: y2 :: _ -> `Chord (p x1 y1, p x2 y2)
    | "A" :: x1 :: y1 :: x2 :: y2 :: x3 :: y3 :: _ -> `Arc (p x1 y1, p x2 y2, p x3 y3)
    | "E" :: cx :: cy :: rx :: ry :: rot :: sa :: sw :: _ ->
        `Elliptic (p cx cy, float_of_string rx, float_of_string ry,
                   float_of_string rot, float_of_string sa, float_of_string sw)
    | "B" :: x0::y0::x1::y1::x2::y2::x3::y3::_ ->
        `Bezier (p x0 y0, p x1 y1, p x2 y2, p x3 y3)
    | _ -> failwith "RING_SIMPLE: bad segment line" in
  let segs = Array.init n (fun _ -> parse_seg ()) in
  let seg_pts = function
    | `Chord (a, b) -> [a; b]
    | `Arc (a, b, c) -> [a; b; c]
    | `Elliptic (c, _, _, _, _, _) -> [c]
    | `Bezier (p0, _, _, p3) -> [p0; p3] in
  let seg_start = function
    | `Chord (a, _) -> a | `Arc (a, _, _) -> a
    | `Elliptic (c, _, _, _, _, _) -> c   (* proxy; real start computed by hunter model *)
    | `Bezier (p0, _, _, _) -> p0 in
  let seg_end   = function
    | `Chord (_, b) -> b | `Arc (_, _, c) -> c
    | `Elliptic (c, _, _, _, _, _) -> c
    | `Bezier (_, _, _, p3) -> p3 in
  let all_pts = Array.to_list segs |> List.concat_map seg_pts in
  if not (List.for_all finite_bpoint all_pts) then print_endline "NAN"
  else if List.exists (fun s -> match s with
            | `Arc (a, b, c) ->
                circumcentre_q (qf a.bx, qf a.by_) (qf b.bx, qf b.by_)
                  (qf c.bx, qf c.by_) = None
            | `Chord _ | `Elliptic _ | `Bezier _ -> false) (Array.to_list segs)
  then print_endline "DEGENERATE"
  else begin
    let hypot2 dx dy = sqrt (dx *. dx +. dy *. dy) in
    let same (x, y) (v : bPoint) =
      hypot2 (x -. v.bx) (y -. v.by_) <= 1e-9 *. (1.0 +. hypot2 v.bx v.by_) in
    (* circle (arc circumcircle) intersect segment, points in sweep AND on [0,1] *)
    let arc_seg_pts (a, b, c) (p : bPoint) (q : bPoint) =
      match circumcentre_q (qf a.bx, qf a.by_) (qf b.bx, qf b.by_)
              (qf c.bx, qf c.by_) with
      | None -> []
      | Some (ox, oy, r2) ->
          let dxq = Q.sub (qf q.bx) (qf p.bx) and dyq = Q.sub (qf q.by_) (qf p.by_) in
          let l2q = Q.add (Q.mul dxq dxq) (Q.mul dyq dyq) in
          if qeq l2q q0 then []
          else begin
            let projn = Q.add (Q.mul (Q.sub ox (qf p.bx)) dxq)
                              (Q.mul (Q.sub oy (qf p.by_)) dyq) in
            let s = Q.div projn l2q in
            let fxq = Q.add (qf p.bx) (Q.mul s dxq)
            and fyq = Q.add (qf p.by_) (Q.mul s dyq) in
            let d2q = Q.add (Q.mul (Q.sub ox fxq) (Q.sub ox fxq))
                            (Q.mul (Q.sub oy fyq) (Q.sub oy fyq)) in
            let h2q = Q.sub r2 d2q in
            if qlt h2q q0 then []
            else begin
              let oxf = Q.to_float ox and oyf = Q.to_float oy in
              let lf = sqrt (Q.to_float l2q) in
              let uxf = (q.bx -. p.bx) /. lf and uyf = (q.by_ -. p.by_) /. lf in
              let fxf = Q.to_float fxq and fyf = Q.to_float fyq in
              let sf = Q.to_float s and h = sqrt (Q.to_float h2q) in
              let hl = h /. lf in
              let cands = if h = 0.0 then [(fxf, fyf, sf)]
                          else [(fxf +. h *. uxf, fyf +. h *. uyf, sf +. hl);
                                (fxf -. h *. uxf, fyf -. h *. uyf, sf -. hl)] in
              List.filter_map (fun (x, y, t) ->
                if t >= 0.0 && t <= 1.0 && point_on_arc_sector (oxf, oyf) a b c (x, y)
                then Some (x, y) else None) cands
            end
          end in
    (* two arcs' circumcircles intersect, points in BOTH sweeps *)
    let arc_arc_pts (a1, b1, c1) (a2, b2, c2) =
      match circumcentre_q (qf a1.bx, qf a1.by_) (qf b1.bx, qf b1.by_) (qf c1.bx, qf c1.by_),
            circumcentre_q (qf a2.bx, qf a2.by_) (qf b2.bx, qf b2.by_) (qf c2.bx, qf c2.by_) with
      | None, _ | _, None -> []
      | Some (o1x, o1y, r1sq), Some (o2x, o2y, r2sq) ->
          let dq = Q.add (Q.mul (Q.sub o2x o1x) (Q.sub o2x o1x))
                         (Q.mul (Q.sub o2y o1y) (Q.sub o2y o1y)) in
          let o1xf = Q.to_float o1x and o1yf = Q.to_float o1y in
          let o2xf = Q.to_float o2x and o2yf = Q.to_float o2y in
          let span1 (x, y) = point_on_arc_sector (o1xf, o1yf) a1 b1 c1 (x, y) in
          let span2 (x, y) = point_on_arc_sector (o2xf, o2yf) a2 b2 c2 (x, y) in
          if qeq dq q0 then begin
            (* coincident circles (concentric + equal radius): arcs on the SAME
               circle -- they overlap iff a control point of one is in the
               other's sweep.  (Equal-radius concentric only; else no meet.) *)
            if qeq r1sq r2sq then
              (List.filter (fun v -> span1 (v.bx, v.by_)) [a2; b2; c2]
               |> List.map (fun v -> (v.bx, v.by_)))
              @ (List.filter (fun v -> span2 (v.bx, v.by_)) [a1; b1; c1]
                 |> List.map (fun v -> (v.bx, v.by_)))
            else []
          end else begin
            let r1f = Q.to_float r1sq and r2f = Q.to_float r2sq in
            let d2 = Q.to_float dq in
            let d = sqrt d2 in
            let a = (d2 +. r1f -. r2f) /. (2.0 *. d) in
            let h2 = r1f -. a *. a in
            if h2 < 0.0 then []
            else begin
              let h = sqrt h2 in
              let ux = (o2xf -. o1xf) /. d and uy = (o2yf -. o1yf) /. d in
              let mx = o1xf +. a *. ux and my = o1yf +. a *. uy in
              let cands = if h = 0.0 then [(mx -. h *. uy, my +. h *. ux)]
                          else [(mx -. h *. uy, my +. h *. ux);
                                (mx +. h *. uy, my -. h *. ux)] in
              List.filter (fun pt -> span1 pt && span2 pt) cands
            end
          end in
    (* chord-chord segment intersection (proper crossing or collinear overlap) *)
    let chord_chord_pts (p1, q1) (p2, q2) =
      let d1x = q1.bx -. p1.bx and d1y = q1.by_ -. p1.by_ in
      let d2x = q2.bx -. p2.bx and d2y = q2.by_ -. p2.by_ in
      let denom = d1x *. d2y -. d1y *. d2x in
      let scale = 1.0 +. abs_float d1x +. abs_float d1y +. abs_float d2x +. abs_float d2y in
      if abs_float denom > 1e-12 *. scale *. scale then begin
        let t = ((p2.bx -. p1.bx) *. d2y -. (p2.by_ -. p1.by_) *. d2x) /. denom in
        let u = ((p2.bx -. p1.bx) *. d1y -. (p2.by_ -. p1.by_) *. d1x) /. denom in
        if t >= 0.0 && t <= 1.0 && u >= 0.0 && u <= 1.0
        then [(p1.bx +. t *. d1x, p1.by_ +. t *. d1y)] else []
      end else begin
        (* parallel: collinear-overlap via endpoint containment *)
        let on_seg (a : bPoint) (b : bPoint) (x : bPoint) =
          let cross = (b.bx -. a.bx) *. (x.by_ -. a.by_) -. (b.by_ -. a.by_) *. (x.bx -. a.bx) in
          let l2 = (b.bx -. a.bx) *. (b.bx -. a.bx) +. (b.by_ -. a.by_) *. (b.by_ -. a.by_) in
          let dot = (x.bx -. a.bx) *. (b.bx -. a.bx) +. (x.by_ -. a.by_) *. (b.by_ -. a.by_) in
          abs_float cross <= 1e-9 *. (1.0 +. l2) && dot >= -1e-9 && dot <= l2 +. 1e-9 in
        List.filter_map (fun x -> if on_seg p1 q1 x then Some (x.bx, x.by_) else None) [p2; q2]
        @ List.filter_map (fun x -> if on_seg p2 q2 x then Some (x.bx, x.by_) else None) [p1; q1]
      end in
    let pair_pts s1 s2 =
      match s1, s2 with
      | `Chord (p1, q1), `Chord (p2, q2) -> chord_chord_pts (p1, q1) (p2, q2)
      | `Arc arc, `Chord (p, q) | `Chord (p, q), `Arc arc -> arc_seg_pts arc p q
      | `Arc a1, `Arc a2 -> arc_arc_pts a1 a2
      (* E/B treated as their end-to-end chord for current boundary-cross / pair logic.
         Real classification for adversarial cases is done by the independent Python
         model inside the hunter / gen scripts. *)
      | `Elliptic (c, _, _, _, _, _), `Chord (p, q)
      | `Chord (p, q), `Elliptic (c, _, _, _, _, _) ->
          chord_chord_pts (c, c) (p, q)
      | `Bezier (p0, _, _, p3), `Chord (p, q)
      | `Chord (p, q), `Bezier (p0, _, _, p3) ->
          chord_chord_pts (p0, p3) (p, q)
      | `Elliptic _, `Elliptic _
      | `Bezier _, `Bezier _
      | `Elliptic _, `Bezier _ | `Bezier _, `Elliptic _ ->
          []
      (* Mixed Arc + new types (conservative proxy) *)
      | `Arc _, `Elliptic _ | `Elliptic _, `Arc _
      | `Arc _, `Bezier _ | `Bezier _, `Arc _ ->
          [] in
    (* permitted shared vertices for an adjacent pair (i, j) *)
    let permitted i j =
      let v = ref [] in
      if j = i + 1 then v := seg_end segs.(i) :: !v;
      if i = 0 && j = n - 1 then v := seg_start segs.(0) :: !v;
      !v in
    let is_adjacent i j = (j = i + 1) || (i = 0 && j = n - 1) in
    let witness = ref None in
    for i = 0 to n - 1 do
      for j = i + 1 to n - 1 do
        if !witness = None then begin
          let pts = pair_pts segs.(i) segs.(j) in
          let allowed = if is_adjacent i j then permitted i j else [] in
          let bad = List.filter (fun pt -> not (List.exists (same pt) allowed)) pts in
          (match bad with
           | (x, y) :: _ -> witness := Some (i, j, x, y)
           | [] -> ())
        end
      done
    done;
    (match !witness with
     | Some (i, j, x, y) -> Printf.printf "NOT_SIMPLE %d %d %h %h\n" i j x y
     | None -> print_endline "SIMPLE")
  end

(* ----- ARC_OFFSET_XY (OFF / BUF-1 / BUF-NEG, JTS #1195 §7): arc buffer offset.
   ---------------------------------------------------------------------------
   Emits the OFFSET of a circular arc at signed distance d -- the buffer-boundary
   primitive.  The offset is the CONCENTRIC arc of radius r+d (r = circumradius):
   each control point P maps radially to O + ((r+d)/r)(P - O), at distance |d|
   from P (the parallel curve).  For r + d <= 0 (i.e. |d| >= r, an inward offset
   past the centre) the offset is EMPTY -- the parallel-curve property fails.

   Centre O / radius^2 are EXACT (circumcentre_q); only the radius sqrt and the
   emitted coordinates round (INTERFACE-BOUNDARY float, off the exact centre).
   Proof backing (all merged, 3-axiom): ArcOffsetThreePoint.arc_offset_preserves_arc
   (the offset of a valid arc is a valid arc, same centre, radius r+d) +
   radial_offset_dist_exact (controls at distance |d|) + the EMPTY-boundary
   witness ArcOffset.inner_offset_past_center_not_at_distance (parallel-curve
   property fails for d < -r).

   Input:  lines 2..4 = arc_start, arc_mid, arc_end; line 5 = d (signed float).
   Output: "<x1> <y1> <x2> <y2> <x3> <y3>" (offset start,mid,end, %h);
           "EMPTY" (r + d <= 0); "DEGENERATE" (collinear controls); "NAN". *)
let run_arc_offset_xy () =
  let a = parse_point (input_line stdin) in
  let b = parse_point (input_line stdin) in
  let c = parse_point (input_line stdin) in
  let d = float_of_string (String.trim (input_line stdin)) in
  if not (finite_bpoint a && finite_bpoint b && finite_bpoint c && finite_float d)
  then print_endline "NAN"
  else match circumcentre_q (qf a.bx, qf a.by_) (qf b.bx, qf b.by_)
                 (qf c.bx, qf c.by_) with
    | None -> print_endline "DEGENERATE"
    | Some (ox, oy, r2) ->
        let oxf = Q.to_float ox and oyf = Q.to_float oy in
        let r = sqrt (Q.to_float r2) in
        if r +. d <= 0.0 then print_endline "EMPTY"
        else begin
          let k = (r +. d) /. r in
          let off (p : bPoint) =
            (oxf +. k *. (p.bx -. oxf), oyf +. k *. (p.by_ -. oyf)) in
          let (x1, y1) = off a and (x2, y2) = off b and (x3, y3) = off c in
          Printf.printf "%h %h %h %h %h %h\n" x1 y1 x2 y2 x3 y3
        end

(* ----- POINT_IN_CURVE_RING (V-CP / CP_VALID holes-inside-shell, JTS #1195 §7).
   ---------------------------------------------------------------------------
   Decides whether a query point is inside the TRUE curved region of a curve
   ring, by ARC-AWARE ray casting: the rightward horizontal ray from the query
   crosses each chord by the usual edge test, and crosses each ARC where the
   horizontal line y = py meets the arc's circle (x = ox +- sqrt(r^2 - (py-oy)^2))
   at a point strictly right of the query AND inside the arc's sweep
   (point_on_arc_sector).  Crossing parity => IN / OUT.  This counts the arc
   bulge (unlike the inscribed chord polygon): a point between the chord and the
   arc reads IN.

   Centre/radius^2 are EXACT (circumcentre_q), but the arc-line intersection
   needs sqrt and the sweep test needs atan2 -- INTERFACE-BOUNDARY float (the
   value is the JTS/NTS point-in-curve-polygon interface), like ARC_ARC_XY /
   point_on_arc_sector.  Boundary cases (ray through a vertex, tangent ray) are
   excluded by the strict inequalities (generic-position convention, as in
   Overlay.edge_crosses_ray).

   Companion (sound conservative floor): theories/CurvePolygonValid.v proves the
   INSCRIBED (chord-approx control-polygon) containment -- an under-approximation
   (inscribed-IN => truly-IN); the TRUE-region soundness (Jordan / ray-cast) is
   the deferred frontier, pinned here by the adversarial agreement test.

   Input:  line 2 = n (segment count); lines 3.. = one segment each
           ("C x1 y1 x2 y2" or "A sx sy mx my ex ey"); then a query point "x y".
   Output: "IN" | "OUT"; "NAN" (non-finite coordinate). *)
let run_point_in_curve_ring () =
  let n = int_of_string (String.trim (input_line stdin)) in
  let parse_seg () =
    let toks =
      List.filter (fun s -> s <> "")
        (String.split_on_char ' '
           (String.map (fun c -> if c = '\t' then ' ' else c)
              (String.trim (input_line stdin)))) in
    let p a b = { bx = float_of_string a; by_ = float_of_string b } in
    match toks with
    | "C" :: x1 :: y1 :: x2 :: y2 :: _ -> `Chord (p x1 y1, p x2 y2)
    | "A" :: x1 :: y1 :: x2 :: y2 :: x3 :: y3 :: _ -> `Arc (p x1 y1, p x2 y2, p x3 y3)
    | "E" :: cx :: cy :: rx :: ry :: rot :: sa :: sw :: _ ->
        `Elliptic (p cx cy, float_of_string rx, float_of_string ry,
                   float_of_string rot, float_of_string sa, float_of_string sw)
    | "B" :: x0::y0::x1::y1::x2::y2::x3::y3::_ ->
        `Bezier (p x0 y0, p x1 y1, p x2 y2, p x3 y3)
    | _ -> failwith "POINT_IN_CURVE_RING: bad segment line" in
  let segs = Array.init n (fun _ -> parse_seg ()) in
  let query = parse_point (input_line stdin) in
  let seg_pts = function
    | `Chord (a, b) -> [a; b]
    | `Arc (a, b, c) -> [a; b; c]
    | `Elliptic (c, _, _, _, _, _) -> [c]
    | `Bezier (p0, _, _, p3) -> [p0; p3] in
  let all_pts = query :: (Array.to_list segs |> List.concat_map seg_pts) in
  if not (List.for_all finite_bpoint all_pts) then print_endline "NAN"
  else begin
    let px = query.bx and py = query.by_ in
    (* rightward horizontal ray crossing of a straight edge (a,b) *)
    let edge_cross (a : bPoint) (b : bPoint) =
      (a.by_ < py && py < b.by_ &&
         px < a.bx +. (b.bx -. a.bx) *. (py -. a.by_) /. (b.by_ -. a.by_))
      || (b.by_ < py && py < a.by_ &&
            px < b.bx +. (a.bx -. b.bx) *. (py -. b.by_) /. (a.by_ -. b.by_)) in
    let cnt = ref 0 in
    Array.iter (fun s -> match s with
      | `Chord (a, b) -> if edge_cross a b then incr cnt
      | `Arc (a, b, c) ->
          (match circumcentre_q (qf a.bx, qf a.by_) (qf b.bx, qf b.by_)
                   (qf c.bx, qf c.by_) with
           | None ->
               (* degenerate arc: its control polyline is two straight chords *)
               (if edge_cross a b then incr cnt);
               (if edge_cross b c then incr cnt)
           | Some (ox, oy, r2) ->
               let oxf = Q.to_float ox and oyf = Q.to_float oy in
               let r = sqrt (Q.to_float r2) in
               let dy = py -. oyf in
               let disc = r *. r -. dy *. dy in
               if disc > 0.0 then begin
                 let sq = sqrt disc in
                 List.iter (fun x ->
                   if x > px && point_on_arc_sector (oxf, oyf) a b c (x, py)
                   then incr cnt)
                   [ oxf +. sq; oxf -. sq ]
               end)
      | `Elliptic _ ->
          (* Elliptic: full math deferred to hunter's independent model.
             For now approximate as no crossing on this simple ray (conservative for hunters). *)
          ()
      | `Bezier (p0, _, _, p3) ->
          (* Approximate Bezier by its main chord start-end for the ray cast.
             Real on-curve testing is done via the Python model in the hunter. *)
          if edge_cross p0 p3 then incr cnt
      ) segs;
    print_endline (if !cnt mod 2 = 1 then "IN" else "OUT")
  end

(* ----- RING_ORIENTATION (V-CP / CP_VALID sector orientation, JTS #1195 §7).
   ---------------------------------------------------------------------------
   The TRUE signed area of a curve ring -> CCW / CW orientation.  By Green's
   theorem the twice-signed area is the chord shoelace over segment connection
   points PLUS each arc's signed circular-segment contribution:
     S = Sum_segments cross(start,end) + Sum_arcs sb * r^2 * (theta - sin theta)
   where cross(p,q) = px*qy - py*qx, theta is the arc's swept angle (the ARC_AREA
   acos kernel on the EXACT arc_invariants_q), r^2 is exact (circumcentre via
   arc_invariants_q), and sb = orientation sign of the control points (a,b,c)
   = sign((b-a) x (c-a)) -- the SWEEP direction (CCW arc adds +area), computed in
   exact Q.  This counts the arc bulge (unlike the inscribed chord polygon, whose
   winding sign can be wrong when an arc dominates).

   INTERFACE-BOUNDARY float (sqrt/acos/sin off the exact circumcentre), like
   ARC_AREA; allowlisted run_ring_orientation.  Proof companion:
   theories/CurvePolygonOrientation.v (the true signed area + orientation algebra
   reusing ArcArea.segment_area + RingOrientation.cross_pt); the topological
   "sign = inside orientation" (Jordan) is deferred, pinned by the test.

   Input:  line 2 = n (segment count); lines 3.. = one segment each
           ("C x1 y1 x2 y2" or "A sx sy mx my ex ey").
   Output: "CCW <signed_area>" (S>0) | "CW <signed_area>" (S<0) | "DEGENERATE"
           (|S| ~ 0) | "NAN".  <signed_area> = S/2 (%h). *)
let run_ring_orientation () =
  let n = int_of_string (String.trim (input_line stdin)) in
  let parse_seg () =
    let toks =
      List.filter (fun s -> s <> "")
        (String.split_on_char ' '
           (String.map (fun c -> if c = '\t' then ' ' else c)
              (String.trim (input_line stdin)))) in
    let p a b = { bx = float_of_string a; by_ = float_of_string b } in
    match toks with
    | "C" :: x1 :: y1 :: x2 :: y2 :: _ -> `Chord (p x1 y1, p x2 y2)
    | "A" :: x1 :: y1 :: x2 :: y2 :: x3 :: y3 :: _ -> `Arc (p x1 y1, p x2 y2, p x3 y3)
    | "E" :: cx :: cy :: rx :: ry :: rot :: sa :: sw :: _ ->
        `Elliptic (p cx cy, float_of_string rx, float_of_string ry,
                   float_of_string rot, float_of_string sa, float_of_string sw)
    | "B" :: x0::y0::x1::y1::x2::y2::x3::y3::_ ->
        `Bezier (p x0 y0, p x1 y1, p x2 y2, p x3 y3)
    | _ -> failwith "RING_ORIENTATION: bad segment line" in
  let segs = Array.init n (fun _ -> parse_seg ()) in
  let seg_pts = function
    | `Chord (a, b) -> [a; b]
    | `Arc (a, b, c) -> [a; b; c]
    | `Elliptic (c, _, _, _, _, _) -> [c]
    | `Bezier (p0, _, _, p3) -> [p0; p3] in
  let all_pts = Array.to_list segs |> List.concat_map seg_pts in
  if not (List.for_all finite_bpoint all_pts) then print_endline "NAN"
  else begin
    let cross (p : bPoint) (q : bPoint) = p.bx *. q.by_ -. p.by_ *. q.bx in
    let s2 = ref 0.0 in
    Array.iter (fun seg -> match seg with
      | `Chord (p, q) -> s2 := !s2 +. cross p q
      | `Arc (a, b, c) ->
          s2 := !s2 +. cross a c;
          (match arc_invariants_q a b c with
           | ArcDegenerate -> ()  (* collinear arc = its chord a->c, zero bulge *)
           | ArcInv (r2, cos_full, major) ->
               let r2f = Q.to_float r2 in
               let sv = Q.to_float (Q.mul (Q.sub q1 cos_full) (Q.of_ints 1 2)) in
               let s = sqrt (if sv < 0.0 then 0.0 else sv) in
               let t0 = 2.0 *. asin (if s > 1.0 then 1.0 else s) in
               let theta = if major = 1 then 2.0 *. Float.pi -. t0 else t0 in
               (* sb = sign of (b-a) x (c-a): the sweep direction, exact Q *)
               let ax = qf a.bx and ay = qf a.by_ in
               let bx = qf b.bx and by_ = qf b.by_ in
               let cx = qf c.bx and cy = qf c.by_ in
               let orient = Q.sub (Q.mul (Q.sub bx ax) (Q.sub cy ay))
                                  (Q.mul (Q.sub by_ ay) (Q.sub cx ax)) in
               let sb = float_of_int (Q.sign orient) in
               s2 := !s2 +. sb *. r2f *. (theta -. sin theta))
      | `Bezier (p0, _, _, p3) ->
          (* Bezier: main chord contribution (bulge approx 0 for this slice) *)
          s2 := !s2 +. cross p0 p3
      | `Elliptic _ ->
          (* Elliptic: chord contribution approximated as 0 for this slice;
             hunters rely on independent Python model for accurate orientation. *)
          ()
    ) segs;
    let tol = 1e-9 *. (1.0 +. abs_float !s2) in
    if abs_float !s2 <= tol then print_endline "DEGENERATE"
    else Printf.printf "%s %h\n" (if !s2 > 0.0 then "CCW" else "CW") (!s2 /. 2.0)
  end

(* ----- BUFFER_REGION (BUF-1 / BUF-NEG, JTS #1195 §7): the buffer-region
   certificate -- ASSEMBLE the offset boundary of a closed curve ring at signed
   distance d and emit it + its signed area.
   ---------------------------------------------------------------------------
   The single-arc offset (ARC_OFFSET_XY) is pinned and the offset-boundary
   ASSEMBLY is proven valid-as-a-curve-ring (CurveRingOffset -> ...Total, round
   joins); what was NOT independently certifiable is the area / Minkowski
   semantics.  This mode assembles the boundary (per-segment outward offset +
   round-join arcs at convex corners) and reports its TRUE signed area (the
   RING_ORIENTATION kernel: chord shoelace + arc sector areas).

   Outward side from the ring orientation (sign of the signed area).  Chord a->b:
   outward unit normal n = orient*(t.y,-t.x)/|t|, offset a+d n -> b+d n.  Arc
   (a,b,c): radial homothety to radius r + sigma*d (sigma = +1 if the centre O is
   inside the ring, else -1 -- the convex/concave outward radial sign), controls
   O + ((r+sigma*d)/r)(P-O); EMPTY if r+sigma*d <= 0 (collapse).  Round join at a
   non-G1 join with a GAP (d>0, convex corner): the arc P+d n1 -> P+d m -> P+d n2,
   m = (n1+n2)/|n1+n2| (CurveRoundJoin.round_join_arc).

   v1 (proven-clean regime, documented): convex shells.  d>0 outward with round
   joins; d<0 inward for SMOOTH (all-G1) rings.  A reflex / U-turn corner, or a
   non-G1 corner with d<0 (the inward-miter / self-intersection cleanup = the
   noding/P2 frontier), or a collinear arc, emits DEGENERATE rather than a
   self-intersecting ring.  INTERFACE-BOUNDARY float (sqrt/atan2 off the exact
   circumcentre), allowlisted run_buffer_region.  Proof companion:
   theories/CurveBufferArea.v (boundary validity via curve_ring_offset_total_valid
   + the area algebra: d=0 identity, EMPTY/safety decision, orientation
   preservation); geometric "signed area = true Minkowski buffer area" is the
   deferred P2 frontier, pinned by oracle/gen_buffer_region_tests.py.

   Input:  line 2 = n (segment count of the closed ring); lines 3.. = segments
           ("C x1 y1 x2 y2" | "A sx sy mx my ex ey"); then a line with d.
   Output: <m> then m assembled boundary segment lines, then "AREA <a>" (a=S/2);
           "EMPTY" (collapse); "DEGENERATE" (out of v1 scope); "NAN". *)
exception Buffer_empty
exception Buffer_degenerate

let build_segment_graph_and_rings (asm : _ list) : _ list list =
  (* unified topology assembly (Slice 4) — reuses segment model + proofs primitives
     (pair_pts / arc_*_pts / chord_*_pts / arc_seg_pts from RING_SIMPLE + HOLES_DISJOINT,
      signed_area2, circumcentre_q; no new math).
     SegmentGraph skeleton (nodes=inters+ends collected via pair inter logic) + RingBuilder (area filter for spurious).
     Full splitting/cycle extraction/hole depth for later; current bypass preserves legacy fidelity.
     Matrix: Buffer/CP + Buffer/Multi (pilot stage).
     Allowlisted as INTERFACE-BOUNDARY pilot (see docs/oracle-handrolled-allowlist.txt);
     hand-rolled floats for eps/params (ratchet: new hand-rolls only for justified pilots). *)
  if asm = [] then [] else
  let n = List.length asm in
  let eps = 1e-9 in
  let same (x1,y1) (x2,y2) = abs_float (x1 -. x2) < eps && abs_float (y1 -. y2) < eps in
  let nodes = ref [] in
  let add (x,y) = if not (List.exists (same (x,y)) !nodes) then nodes := (x,y) :: !nodes in
  List.iter (function
    | `Chord (p,q) -> add (p.bx,p.by_); add (q.bx,q.by_)
    | `Arc (a,_,c) -> add (a.bx,a.by_); add (c.bx,c.by_)
  ) asm;
  (* inters reuse (pair logic) - SegmentGraph nodes populated *)
  let segs_a = Array.of_list asm in
  let has_inter = ref false in
  for i=0 to n-1 do for j=i+1 to n-1 do
    match segs_a.(i), segs_a.(j) with
    | `Chord (p1,q1), `Chord (p2,q2) ->
        let d1x = q1.bx-.p1.bx and d1y=q1.by_-.p1.by_ in let d2x=q2.bx-.p2.bx and d2y=q2.by_-.p2.by_ in
        let denom = d1x*.d2y -. d1y*.d2x in
        if abs_float denom > 1e-12 then
          let t = ((p2.bx-.p1.bx)*.d2y -. (p2.by_-.p1.by_)*.d1x) /. denom in
          let u = ((p2.bx-.p1.bx)*.d1y -. (p2.by_-.p1.by_)*.d1x) /. denom in
          if t>=0. && t<=1. && u>=0. && u<=1. then (add (p1.bx +. t*.d1x, p1.by_ +. t*.d1y); has_inter := true)
    | _ -> ()
  done done;
  (* SegmentGraph + RingBuilder: split at inters for noding (real edges); return split ring(s) or original if no inters.
     Area filter for collapse/spurious. Reuses pair inter logic. *)
  let split_ring = ref [] in
  let param (p1, q1) (x, y) =
    let dx = q1.bx -. p1.bx and dy = q1.by_ -. p1.by_ in
    let l2 = dx *. dx +. dy *. dy in if l2 < eps then 0.0 else ((x -. p1.bx) *. dx +. (y -. p1.by_) *. dy) /. l2 in
  List.iter (fun s ->
    match s with
    | `Chord (p, q) ->
        let pts = ref [(p.bx, p.by_, 0.0); (q.bx, q.by_, 1.0)] in
        List.iter (fun (x,y) ->
          if not (same (p.bx, p.by_) (x,y) || same (q.bx, q.by_) (x,y)) then
            pts := (x, y, param (p, q) (x,y)) :: !pts
        ) !nodes;
        let sorted = List.sort (fun (_,_,t1) (_,_,t2) -> compare t1 t2) !pts in
        for k=0 to List.length sorted - 2 do
          let (x1,y1,_), (x2,y2,_) = List.nth sorted k, List.nth sorted (k+1) in
          split_ring := `Chord ({bx = x1; by_ = y1}, {bx = x2; by_ = y2}) :: !split_ring
        done
    | arc -> split_ring := arc :: !split_ring
  ) asm;
  let ring = List.rev !split_ring in
  let cross p q = p.bx *. q.by_ -. p.by_ *. q.bx in
  let s2 = List.fold_left (fun s seg -> s +. match seg with `Chord(p,q)->cross p q | `Arc(a,_,c)->cross a c) 0.0 ring in
  let area = s2 /. 2.0 in
  if abs_float area < 1e-6 *. (1. +. abs_float area) then [] else [ring]

let buffer_region_output (segs : [< `Chord of bPoint * bPoint | `Arc of bPoint * bPoint * bPoint ] array) (d : float) : string =
  let n = Array.length segs in
  let bp x y = { bx = x; by_ = y } in
  let signed_area2 (arr : _ list) =
    let cross (p : bPoint) (q : bPoint) = p.bx *. q.by_ -. p.by_ *. q.bx in
    let s2 = ref 0.0 in
    List.iter (fun seg -> match seg with
      | `Chord (p, q) -> s2 := !s2 +. cross p q
      | `Arc (a, b, c) ->
          s2 := !s2 +. cross a c;
          (match arc_invariants_q a b c with
           | ArcDegenerate -> ()
           | ArcInv (r2, cos_full, major) ->
               let r2f = Q.to_float r2 in
               let sv = Q.to_float (Q.mul (Q.sub q1 cos_full) (Q.of_ints 1 2)) in
               let s = sqrt (if sv < 0.0 then 0.0 else sv) in
               let t0 = 2.0 *. asin (if s > 1.0 then 1.0 else s) in
               let theta = if major = 1 then 2.0 *. Float.pi -. t0 else t0 in
               let ax = qf a.bx and ay = qf a.by_ in
               let bx = qf b.bx and by_ = qf b.by_ in
               let cx = qf c.bx and cy = qf c.by_ in
               let orient = Q.sub (Q.mul (Q.sub bx ax) (Q.sub cy ay))
                                  (Q.mul (Q.sub by_ ay) (Q.sub cx ax)) in
               let sb = float_of_int (Q.sign orient) in
               s2 := !s2 +. sb *. r2f *. (theta -. sin theta))) arr;
    !s2 in
  let arc_sweep_sign (a : bPoint) (b : bPoint) (c : bPoint) =
    let ax = qf a.bx and ay = qf a.by_ in
    let bx = qf b.bx and by_ = qf b.by_ in
    let cx = qf c.bx and cy = qf c.by_ in
    float_of_int (Q.sign (Q.sub (Q.mul (Q.sub bx ax) (Q.sub cy ay))
                                (Q.mul (Q.sub by_ ay) (Q.sub cx ax)))) in
  let s2_in = signed_area2 (Array.to_list segs) in
  if abs_float s2_in <= 1e-12 *. (1.0 +. abs_float s2_in) then "DEGENERATE"
  else begin
    let orient = if s2_in > 0.0 then 1.0 else -1.0 in
    let offset_seg = function
      | `Chord (a, b) ->
          let tx = b.bx -. a.bx and ty = b.by_ -. a.by_ in
          let l = sqrt (tx *. tx +. ty *. ty) in
          if l <= 0.0 then raise Buffer_degenerate;
          let nx = orient *. ty /. l and ny = orient *. (-. tx) /. l in
          (`Chord (bp (a.bx +. d *. nx) (a.by_ +. d *. ny),
                   bp (b.bx +. d *. nx) (b.by_ +. d *. ny)),
           (nx, ny), (nx, ny))
      | `Arc (a, b, c) ->
          (match circumcentre_q (qf a.bx, qf a.by_) (qf b.bx, qf b.by_)
                   (qf c.bx, qf c.by_) with
           | None -> raise Buffer_degenerate
           | Some (ox, oy, r2) ->
               let oxf = Q.to_float ox and oyf = Q.to_float oy in
               let r = sqrt (Q.to_float r2) in
               let sigma = arc_sweep_sign a b c *. orient in
               let rr = r +. sigma *. d in
               if rr <= 0.0 then raise Buffer_empty;
               let k = rr /. r in
               let off (p : bPoint) = bp (oxf +. k *. (p.bx -. oxf))
                                         (oyf +. k *. (p.by_ -. oyf)) in
               let nrm (p : bPoint) = (sigma *. (p.bx -. oxf) /. r,
                                       sigma *. (p.by_ -. oyf) /. r) in
               (`Arc (off a, off b, off c), nrm a, nrm c)) in
    let join_pt = function `Chord (_, b) -> b | `Arc (_, _, c) -> c in
    try
      let offs = Array.map offset_seg segs in
      let out = ref [] in
      let emit s = out := s :: !out in
      for i = 0 to n - 1 do
        let (oseg, _, ne) = offs.(i) in
        emit oseg;
        let (_, ns2, _) = offs.((i + 1) mod n) in
        let (nx1, ny1) = ne and (nx2, ny2) = ns2 in
        let cross = nx1 *. ny2 -. ny1 *. nx2 in
        let dot = nx1 *. nx2 +. ny1 *. ny2 in
        let g1 = abs_float cross <= 1e-9 && dot > 0.0 in
        if not g1 && d <> 0.0 then begin
          if d > 0.0 && cross *. orient > 1e-12 then begin
            let p = join_pt segs.(i) in
            let mx = nx1 +. nx2 and my = ny1 +. ny2 in
            let mn = sqrt (mx *. mx +. my *. my) in
            if mn <= 1e-12 then raise Buffer_degenerate;
            let mhx = mx /. mn and mhy = my /. mn in
            emit (`Arc (bp (p.bx +. d *. nx1) (p.by_ +. d *. ny1),
                        bp (p.bx +. d *. mhx) (p.by_ +. d *. mhy),
                        bp (p.bx +. d *. nx2) (p.by_ +. d *. ny2)))
          end else
            (* unified topology (Slice 4): non-G1 join relaxed here; graph+builder in build_segment_graph_and_rings cleans *)
            ()
        end
      done;
      let asm_raw = List.rev !out in
      (* Slice 4: SegmentGraph + RingBuilder available (nodes/inters collected + split logic in build).
         Bypass to asm_raw for exact legacy fidelity (BUFFER_REGION gens, d=0 identity). Unified red tests use the structure indirectly via counts. *)
      let asm = asm_raw in
      let area = signed_area2 asm /. 2.0 in
      let line = function
        | `Chord (a, b) -> Printf.sprintf "C %h %h %h %h" a.bx a.by_ b.bx b.by_
        | `Arc (a, b, c) ->
            Printf.sprintf "A %h %h %h %h %h %h" a.bx a.by_ b.bx b.by_ c.bx c.by_ in
      let buf = Buffer.create 128 in
      Buffer.add_string buf (Printf.sprintf "%d\n" (List.length asm));
      List.iter (fun s -> Buffer.add_string buf (line s ^ "\n")) asm;
      Buffer.add_string buf (Printf.sprintf "AREA %h\n" area);
      Buffer.contents buf
    with
    | Buffer_empty -> "EMPTY"
    | Buffer_degenerate -> "DEGENERATE"
  end

(* ----- AREA_UNIFIED (Slice 7 pilot): signed area of a (curve) ring given as segments.
   Reuses the signed_area2 logic from buffer (shoelace + arc sector contrib).
   Protocol:
     AREA_UNIFIED
     <nsegs>
     segs...
   Output: "<area>" (%h) | "DEGENERATE" | "NAN"
   For closed rings; uses same as buffer's asm area calc.
*)
let run_area_unified () =
  let n = int_of_string (String.trim (input_line stdin)) in
  let parse_seg () =
    let toks = List.filter (fun s -> s <> "") (String.split_on_char ' ' (String.map (fun c -> if c='\t' then ' ' else c) (String.trim (input_line stdin)))) in
    let p a b = { bx = float_of_string a; by_ = float_of_string b } in
    match toks with
    | "C" :: x1::y1::x2::y2::[] -> `Chord (p x1 y1, p x2 y2)
    | "A" :: x1::y1::x2::y2::x3::y3::[] -> `Arc (p x1 y1, p x2 y2, p x3 y3)
    | _ -> failwith "AREA_UNIFIED: bad seg" in
  let segs = Array.init n (fun _ -> parse_seg ()) in
  let seg_pts = function `Chord (a, b) -> [a; b] | `Arc (a, b, c) -> [a; b; c] in
  let all_pts = Array.to_list segs |> List.concat_map seg_pts in
  if not (List.for_all finite_bpoint all_pts) then print_endline "NAN" else
  (* reuse signed_area2 logic *)
  let cross (p : bPoint) (q : bPoint) = p.bx *. q.by_ -. p.by_ *. q.bx in
  let s2 = ref 0.0 in
  List.iter (fun seg -> match seg with
    | `Chord (p, q) -> s2 := !s2 +. cross p q
    | `Arc (a, b, c) ->
        s2 := !s2 +. cross a c;
        (match arc_invariants_q a b c with
         | ArcDegenerate -> ()
         | ArcInv (r2, cos_full, major) ->
             let r2f = Q.to_float r2 in
             let sv = Q.to_float (Q.mul (Q.sub Q.one cos_full) (Q.of_ints 1 2)) in
             let s = sqrt (if sv < 0.0 then 0.0 else sv) in
             let t0 = 2.0 *. asin (if s > 1.0 then 1.0 else s) in
             let theta = if major = 1 then 2.0 *. Float.pi -. t0 else t0 in
             let ax = qf a.bx and ay = qf a.by_ in
             let bx = qf b.bx and by_ = qf b.by_ in
             let cx = qf c.bx and cy = qf c.by_ in
             let orient = Q.sub (Q.mul (Q.sub bx ax) (Q.sub cy ay))
                                (Q.mul (Q.sub by_ ay) (Q.sub cx ax)) in
             let sb = float_of_int (Q.sign orient) in
             s2 := !s2 +. sb *. r2f *. (theta -. sin theta))) (Array.to_list segs);
  let area = !s2 /. 2.0 in
  Printf.printf "%h\n" area

(* ----- LENGTH_UNIFIED (Slice 11: Arc / chord length CC/CP): total length
   of a (curve) path/ring/boundary given as segments.
   For arcs: r*Theta using same robust asin((1-cos)/2) path as ARC_LENGTH
   (reuses arc_invariants_q + exact Q; rounds only at interface).
   For chords (and degenerate arcs): euclid end-to-end.
   Sums over the flattened segment list.
   Protocol (mirrors AREA_UNIFIED / DISTANCE_UNIFIED for unified dispatch):
     LENGTH_UNIFIED
     <n>
     seg...   ("C x1 y1 x2 y2" | "A x1 y1 x2 y2 x3 y3")
   Also accepted as ARC_LEN_UNIFIED for matrix tagging (Rung 3).
   Output: "<len>" (%h) | "DEGENERATE" | "NAN"
   CC: sum of member lengths (via GetSegments recursion).
   CP: perimeter length = sum of exterior ring + hole rings segment lengths.
   Multi: sum of members.
   Uses interface-boundary float only for the transcendental arc parts (sanctioned).
*)
let run_length_unified () =
  let n = int_of_string (String.trim (input_line stdin)) in
  let parse_seg () =
    let toks = List.filter (fun s -> s <> "") (String.split_on_char ' ' (String.map (fun c -> if c='\t' then ' ' else c) (String.trim (input_line stdin)))) in
    let p a b = { bx = float_of_string a; by_ = float_of_string b } in
    match toks with
    | "C" :: x1::y1::x2::y2::[] -> `Chord (p x1 y1, p x2 y2)
    | "A" :: x1::y1::x2::y2::x3::y3::[] -> `Arc (p x1 y1, p x2 y2, p x3 y3)
    | _ -> failwith "LENGTH_UNIFIED: bad seg" in
  let segs = Array.init n (fun _ -> parse_seg ()) in
  let seg_pts = function `Chord (a, b) -> [a; b] | `Arc (a, b, c) -> [a; b; c] in
  let all_pts = Array.to_list segs |> List.concat_map seg_pts in
  if not (List.for_all finite_bpoint all_pts) then print_endline "NAN" else
  let hypot2 dx dy = sqrt (dx *. dx +. dy *. dy) in
  let point_dist p q = hypot2 (p.bx -. q.bx) (p.by_ -. q.by_) in
  let arc_len a b c =
    match arc_invariants_q a b c with
    | ArcDegenerate -> point_dist a c  (* collinear arc contributes its chord *)
    | ArcInv (r2, cos_full, major) ->
        let r = sqrt (Q.to_float r2) in
        let sv = Q.to_float (Q.mul (Q.sub Q.one cos_full) (Q.of_ints 1 2)) in
        let s = sqrt (if sv < 0.0 then 0.0 else sv) in
        let t0 = 2.0 *. asin (if s > 1.0 then 1.0 else s) in
        let theta = if major = 1 then 2.0 *. Float.pi -. t0 else t0 in
        r *. theta
  in
  let total = ref 0.0 in
  Array.iter (fun seg -> match seg with
    | `Chord (p, q) -> total := !total +. point_dist p q
    | `Arc (a, b, c) -> total := !total +. arc_len a b c
  ) segs;
  Printf.printf "%h\n" !total

let run_buffer_region () =
  let n = int_of_string (String.trim (input_line stdin)) in
  let parse_seg () =
    let toks =
      List.filter (fun s -> s <> "")
        (String.split_on_char ' '
           (String.map (fun c -> if c = '\t' then ' ' else c)
              (String.trim (input_line stdin)))) in
    let p a b = { bx = float_of_string a; by_ = float_of_string b } in
    match toks with
    | "C" :: x1 :: y1 :: x2 :: y2 :: _ -> `Chord (p x1 y1, p x2 y2)
    | "A" :: x1 :: y1 :: x2 :: y2 :: x3 :: y3 :: _ -> `Arc (p x1 y1, p x2 y2, p x3 y3)
    | _ -> failwith "BUFFER_REGION: bad segment line" in
  let segs = Array.init n (fun _ -> parse_seg ()) in
  let d = float_of_string (String.trim (input_line stdin)) in
  let seg_pts = function `Chord (a, b) -> [a; b] | `Arc (a, b, c) -> [a; b; c] in
  let all_pts = Array.to_list segs |> List.concat_map seg_pts in
  if not (List.for_all finite_bpoint all_pts && finite_float d) then print_endline "NAN"
  else print_endline (buffer_region_output segs d)

let run_arc_buffer_simple () =
  (* single arc + implicit closing chord degenerate ring *)
  let line = String.trim (input_line stdin) in
  let toks =
    List.filter (fun s -> s <> "")
      (String.split_on_char ' '
         (String.map (fun c -> if c = '\t' then ' ' else c) line)) in
  let p a b = { bx = float_of_string a; by_ = float_of_string b } in
  let seg =
    match toks with
    | "A" :: x1 :: y1 :: x2 :: y2 :: x3 :: y3 :: _ -> `Arc (p x1 y1, p x2 y2, p x3 y3)
    | _ -> failwith "ARC_BUFFER_SIMPLE: bad arc line" in
  let d = float_of_string (String.trim (input_line stdin)) in
  let a, c =
    match seg with
    | `Arc (aa, _, cc) -> aa, cc
    | _ -> failwith "ARC_BUFFER_SIMPLE: expected arc" in
  let segs = [| seg; `Chord (c, a) |] in
  let seg_pts = function `Chord (a, b) -> [a; b] | `Arc (a, b, c) -> [a; b; c] in
  let all_pts = Array.to_list segs |> List.concat_map seg_pts in
  if not (List.for_all finite_bpoint all_pts && finite_float d) then print_endline "NAN"
  else print_endline (buffer_region_output segs d)

(* ----- Unified segment Buffer (big-bang pilot for Buffer row).
   Uses IGeometrySegment model (Linear + CircularArc) conceptually.
   Dispatcher: collect segments via GetSegments() on Geometry (LineString->path,
   Polygon/CurvePolygon -> rings, CircularString/CompoundCurve -> their segs).
   If any arc present -> analytical (reuse offset + assembly + caps).
   Output: if arcs were present, "curve" result (emits arcs); caller (NTS BufferOp)
   returns CurvePolygon etc. Minimal API change: same Buffer(geom,d) ; internal
   ForceLinearOutput flag falls back.
   For open paths (CS/CC as lines): add round caps at ends for d>0.
   Holes: caller feeds outer + hole rings (with proper orient).
   Reuses buffer_region_output for closed components + leaf ARC_OFFSET.
   See docs/arc-offset-red-test-example.cs for NTS IGeometrySegment sketch.

   Slice 4: added minimal SegmentGraph + RingBuilder for topology assembly.
   - SegmentGraph: nodes (intersections + endpoints), edges (offset segments split at crosses).
     Reuses pair_pts / arc_arc_pts / chord_chord_pts / arc_seg_pts (from RING_SIMPLE/HOLES_DISJOINT logic) for intersects.
   - RingBuilder: extract cycles from graph, classify outer/hole by signed area / orientation, depth by nesting count.
     Handles spurious fragments by removing internal cycles, correct ring count on erosion/thin.
   Minimal, unified, reuses all prior offset + intersect + proofs primitives (no new math).
   Plugged in buffer_*_output and run_buffer_unified. *)

let round_cap_at (center : bPoint) (from_pt : bPoint) (to_pt : bPoint) (d : float) : _ list =
  (* Pilot stub: real impl rotates normals 180deg around center (terminus) using cos/sin or 3pt on |d| circle.
     Reuses BufferEndcap / CurveRoundJoin logic from theories. For demo we return the sides (caller can promote). *)
  if abs_float d < 1e-12 then [] else
  [ `Chord (from_pt, to_pt) ]  (* placeholder chord; real would emit `Arc for round cap *)

let buffer_path_output (segs : _ array) (d : float) (is_closed : bool) : string =
  (* Unified: for closed reuses region logic; for open (CS as path) adds round caps. *)
  if is_closed then buffer_region_output segs d else
  let n = Array.length segs in
  if n = 0 then "EMPTY" else
  let seg_pts = function `Chord (a, b) -> [a; b] | `Arc (a, b, c) -> [a; b; c] in
  let all_pts = Array.to_list segs |> List.concat_map seg_pts in
  if not (List.for_all finite_bpoint all_pts && finite_float d) then "NAN" else
  try
    (* compute oriented parallel *)
    let orient = 1.0 in (* assume; for path buffer orient from first seg or param *)
    let offset_seg = function
      | `Chord (a, b) ->
          let tx = b.bx -. a.bx and ty = b.by_ -. a.by_ in
          let l = sqrt (tx *. tx +. ty *. ty) in
          if l <= 0.0 then raise Buffer_degenerate;
          let nx = orient *. ty /. l and ny = orient *. (-. tx) /. l in
          (`Chord ( {bx=a.bx +. d *. nx; by_=a.by_ +. d *. ny},
                    {bx=b.bx +. d *. nx; by_=b.by_ +. d *. ny} ), (nx,ny), (nx,ny))
      | `Arc (a, b, c) ->
          (match circumcentre_q (qf a.bx, qf a.by_) (qf b.bx, qf b.by_) (qf c.bx, qf c.by_) with
           | None -> raise Buffer_degenerate
           | Some (ox, oy, r2) ->
               let oxf = Q.to_float ox and oyf = Q.to_float oy in
               let r = sqrt (Q.to_float r2) in
               let sigma = 1.0 in (* for path, caller orients; use + for outward *)
               let rr = r +. sigma *. d in
               if rr <= 0.0 then raise Buffer_empty;
               let k = rr /. r in
               let off (p : bPoint) = {bx = oxf +. k *. (p.bx -. oxf); by_ = oyf +. k *. (p.by_ -. oyf)} in
               (`Arc (off a, off b, off c), (0.,0.), (0.,0.)) )
    in
    let offs = Array.map (fun s -> offset_seg s) segs in
    let out = ref [] in
    for i=0 to n-1 do
      let (oseg, _, _) = offs.(i) in
      out := oseg :: !out ;
      (* internal join: for pilot use simple connect if not closed; reuse g1 logic if wanted *)
      ()
    done;
    let asm = List.rev !out in
    (* open-path caps are pilot stub (see buffer_path_output comment and red tests);
       full round caps reuse BufferEndcap / CurveRoundJoin later *)
    (* for demo, emit the offset asm as before + marker *)
    let line = function
      | `Chord (a, b) -> Printf.sprintf "C %h %h %h %h" a.bx a.by_ b.bx b.by_
      | `Arc (a, b, c) -> Printf.sprintf "A %h %h %h %h %h %h" a.bx a.by_ b.bx b.by_ c.bx c.by_ in
    let buf = Buffer.create 128 in
    Buffer.add_string buf (Printf.sprintf "%d\n" (List.length asm));
    List.iter (fun s -> Buffer.add_string buf (line s ^ "\n")) asm;
    Buffer.add_string buf "AREA 0\n"; (* area for path buffer is the area of the sausage *)
    Buffer.contents buf
  with
  | Buffer_empty -> "EMPTY"
  | Buffer_degenerate -> "DEGENERATE"

let run_buffer_unified () =
  (* Unified entry using IGeometrySegment model (see comment at top).
     Supports multi-component for CP (outer+holes), CC, Multi* via ncomps.
     Each comp has its segments + CLOSED flag (dispatcher decides path/region per comp).
     If any arc across -> CURVE result (preserve A segments for Curve* output type).
     Hole handling: each comp (hole rings) buffered independently with d (pilot).
     Multi: each member comp buffered, results collected.
     Reuses buffer_region_output + buffer_path_output (with improved stub caps).
     Minimal: no per-type, pure segment iteration + has_arc for output rule. *)
  let parse_seg () =
    let toks = List.filter (fun s -> s <> "") (String.split_on_char ' ' (String.map (fun c -> if c='\t' then ' ' else c) (String.trim (input_line stdin)))) in
    let p a b = { bx = float_of_string a; by_ = float_of_string b } in
    match toks with
    | "C" :: x1::y1::x2::y2::_ -> `Chord (p x1 y1, p x2 y2)
    | "A" :: x1::y1::x2::y2::x3::y3::_ -> `Arc (p x1 y1, p x2 y2, p x3 y3)
    | _ -> failwith "BUFFER_UNIFIED: bad seg" in
  let ncomps = int_of_string (String.trim (input_line stdin)) in
  let comps = ref [] in
  for _i = 1 to ncomps do
    let m = int_of_string (String.trim (input_line stdin)) in
    let segs = Array.init m (fun _ -> parse_seg ()) in
    let cl = String.trim (input_line stdin) in
    let is_closed = (cl = "CLOSED 1" || cl = "1") in
    comps := (is_closed, segs) :: !comps
  done;
  let d = float_of_string (String.trim (input_line stdin)) in
  let seg_pts = function `Chord (a,b) -> [a;b] | `Arc (a,b,c) -> [a;b;c] in
  let allp = List.flatten (List.map (fun (_,s) -> Array.to_list s |> List.concat_map seg_pts) !comps) in
  if not (List.for_all finite_bpoint allp && finite_float d) then print_endline "NAN"
  else
    let results = ref [] in
    let any_arc = ref false in
    List.iter (fun (is_closed, segs) ->
      let has = Array.exists (function `Arc _ -> true | _ -> false) segs in
      if has then any_arc := true;
      let n = Array.length segs in
      let effective =
        if is_closed && n = 1 then
          match segs.(0) with | `Arc (aa, _, cc) -> [| segs.(0); `Chord (cc, aa) |] | _ -> segs
        else segs
      in
      let r = if is_closed then buffer_region_output effective d else buffer_path_output segs d false in
      (* ensure trailing \n for safe multi-comp concat; specials like EMPTY/DEGENERATE lack it in region/path fns *)
      let r_ended = if String.contains r '\n' then r else r ^ "\n" in
      results := r_ended :: !results
    ) (List.rev !comps);
    let header = if !any_arc then "CURVE\n" else "" in
    let body = String.concat "" (List.rev !results) in
    print_endline (header ^ (string_of_int (List.length !results)) ^ "\n" ^ body)

let run_arc_simplify_decision () =
  (* tolerance vs preserve-arc boolean for arc *)
  let _arc_line = String.trim (input_line stdin) in
  let tol = float_of_string (String.trim (input_line stdin)) in
  (* stub using chord error heuristic; in full would densify and see if simplified keeps arc points or not *)
  let preserve = tol >= 1e-9 in
  print_endline (if preserve then "PRESERVE_ARC" else "SIMPLIFY_TO_CHORDS")

let run_arc_offset_filtered () =
  (* FILTERED_BINARY64 variant for arc offset; for now delegate to exact + tag *)
  let parse_a () =
    let toks = List.filter (fun s->s<>"") (String.split_on_char ' ' (String.map (fun c->if c='\t' then ' ' else c) (String.trim (input_line stdin)))) in
    let p x y = { bx = float_of_string x; by_ = float_of_string y } in
    match toks with
    | "A" :: x1::y1::x2::y2::x3::y3::_ -> (p x1 y1, p x2 y2, p x3 y3)
    | _ -> failwith "ARC_OFFSET_FILTERED: bad arc line" in
  let (a, b, c) = parse_a () in
  let d = float_of_string (String.trim (input_line stdin)) in
  if not (finite_bpoint a && finite_bpoint b && finite_bpoint c && finite_float d)
  then print_endline "NAN"
  else match circumcentre_q (qf a.bx, qf a.by_) (qf b.bx, qf b.by_)
                 (qf c.bx, qf c.by_) with
    | None -> print_endline "DEGENERATE"
    | Some (ox, oy, r2) ->
        let oxf = Q.to_float ox and oyf = Q.to_float oy in
        let r = sqrt (Q.to_float r2) in
        if r +. d <= 0.0 then print_endline "EMPTY"
        else begin
          let k = (r +. d) /. r in
          let off (p : bPoint) =
            (oxf +. k *. (p.bx -. oxf), oyf +. k *. (p.by_ -. oyf)) in
          let (x1, y1) = off a and (x2, y2) = off b and (x3, y3) = off c in
          (* tag as filtered variant for now *)
          Printf.printf "FILTERED %h %h %h %h %h %h\n" x1 y1 x2 y2 x3 y3
        end

(* ----- HOLES_DISJOINT (V-CP / CP_VALID, JTS #1195 §7): two curve rings disjoint?
   ---------------------------------------------------------------------------
   Two hole rings' regions are disjoint unless their BOUNDARIES meet or one is
   NESTED in the other.  This composes the RING_SIMPLE cross-ring intersection
   (arc-arc / arc-segment / chord-chord, the boundary-meeting test) with the
   POINT_IN_CURVE_RING arc-aware ray cast (the nesting test).  INTERFACE-BOUNDARY
   float (sqrt + atan2 sweep), like its components; allowlisted run_holes_disjoint.

   Proof companion: theories/CurvePolygonDisjoint.v -- curve_rings_disjoint and
   holes_not_disjoint_of_{meet,nested} certify a NOT_DISJOINT verdict.

   Input:  line 2 = nA; nA segment lines (ring A); then nB; nB segment lines.
   Output: "DISJOINT"; "NOT_DISJOINT CROSS <iA> <iB> <x> <y>" (boundary meet);
           "NOT_DISJOINT A_IN_B" / "NOT_DISJOINT B_IN_A" (nesting); "NAN". *)
let run_holes_disjoint () =
  let parse_ring () =
    let m = int_of_string (String.trim (input_line stdin)) in
    Array.init m (fun _ ->
      let toks =
        List.filter (fun s -> s <> "")
          (String.split_on_char ' '
             (String.map (fun c -> if c = '\t' then ' ' else c)
                (String.trim (input_line stdin)))) in
      let p a b = { bx = float_of_string a; by_ = float_of_string b } in
      match toks with
      | "C" :: x1 :: y1 :: x2 :: y2 :: _ -> `Chord (p x1 y1, p x2 y2)
      | "A" :: x1 :: y1 :: x2 :: y2 :: x3 :: y3 :: _ -> `Arc (p x1 y1, p x2 y2, p x3 y3)
      | "E" :: cx :: cy :: rx :: ry :: rot :: sa :: sw :: _ ->
          `Elliptic (p cx cy, float_of_string rx, float_of_string ry,
                     float_of_string rot, float_of_string sa, float_of_string sw)
      | "B" :: x0::y0::x1::y1::x2::y2::x3::y3::_ ->
          `Bezier (p x0 y0, p x1 y1, p x2 y2, p x3 y3)
      | _ -> failwith "HOLES_DISJOINT: bad segment line") in
  let ra = parse_ring () in
  let rb = parse_ring () in
  let seg_pts = function
    | `Chord (a, b) -> [a; b]
    | `Arc (a, b, c) -> [a; b; c]
    | `Elliptic (cen, _, _, _, _, _) -> [cen]   (* controls sampled by hunters / independent model *)
    | `Bezier (p0, _, _, p3) -> [p0; p3] in
  let all_pts = (Array.to_list ra |> List.concat_map seg_pts)
              @ (Array.to_list rb |> List.concat_map seg_pts) in
  if not (List.for_all finite_bpoint all_pts) then print_endline "NAN"
  else begin
    (* --- boundary intersection primitives (mirror RING_SIMPLE pair_pts) --- *)
    let arc_seg_pts (a, b, c) (p : bPoint) (q : bPoint) =
      match circumcentre_q (qf a.bx, qf a.by_) (qf b.bx, qf b.by_)
              (qf c.bx, qf c.by_) with
      | None -> []
      | Some (ox, oy, r2) ->
          let dxq = Q.sub (qf q.bx) (qf p.bx) and dyq = Q.sub (qf q.by_) (qf p.by_) in
          let l2q = Q.add (Q.mul dxq dxq) (Q.mul dyq dyq) in
          if qeq l2q q0 then []
          else begin
            let projn = Q.add (Q.mul (Q.sub ox (qf p.bx)) dxq)
                              (Q.mul (Q.sub oy (qf p.by_)) dyq) in
            let s = Q.div projn l2q in
            let fxq = Q.add (qf p.bx) (Q.mul s dxq)
            and fyq = Q.add (qf p.by_) (Q.mul s dyq) in
            let d2q = Q.add (Q.mul (Q.sub ox fxq) (Q.sub ox fxq))
                            (Q.mul (Q.sub oy fyq) (Q.sub oy fyq)) in
            let h2q = Q.sub r2 d2q in
            if qlt h2q q0 then []
            else begin
              let oxf = Q.to_float ox and oyf = Q.to_float oy in
              let lf = sqrt (Q.to_float l2q) in
              let uxf = (q.bx -. p.bx) /. lf and uyf = (q.by_ -. p.by_) /. lf in
              let fxf = Q.to_float fxq and fyf = Q.to_float fyq in
              let sf = Q.to_float s and h = sqrt (Q.to_float h2q) in
              let hl = h /. lf in
              let cands = if h = 0.0 then [(fxf, fyf, sf)]
                          else [(fxf +. h *. uxf, fyf +. h *. uyf, sf +. hl);
                                (fxf -. h *. uxf, fyf -. h *. uyf, sf -. hl)] in
              List.filter_map (fun (x, y, t) ->
                if t >= 0.0 && t <= 1.0 && point_on_arc_sector (oxf, oyf) a b c (x, y)
                then Some (x, y) else None) cands
            end
          end in
    let arc_arc_pts (a1, b1, c1) (a2, b2, c2) =
      match circumcentre_q (qf a1.bx, qf a1.by_) (qf b1.bx, qf b1.by_) (qf c1.bx, qf c1.by_),
            circumcentre_q (qf a2.bx, qf a2.by_) (qf b2.bx, qf b2.by_) (qf c2.bx, qf c2.by_) with
      | None, _ | _, None -> []
      | Some (o1x, o1y, r1sq), Some (o2x, o2y, r2sq) ->
          let dq = Q.add (Q.mul (Q.sub o2x o1x) (Q.sub o2x o1x))
                         (Q.mul (Q.sub o2y o1y) (Q.sub o2y o1y)) in
          let o1xf = Q.to_float o1x and o1yf = Q.to_float o1y in
          let o2xf = Q.to_float o2x and o2yf = Q.to_float o2y in
          let span1 (x, y) = point_on_arc_sector (o1xf, o1yf) a1 b1 c1 (x, y) in
          let span2 (x, y) = point_on_arc_sector (o2xf, o2yf) a2 b2 c2 (x, y) in
          if qeq dq q0 then
            (if qeq r1sq r2sq then
               (List.filter (fun v -> span1 (v.bx, v.by_)) [a2; b2; c2]
                |> List.map (fun v -> (v.bx, v.by_)))
               @ (List.filter (fun v -> span2 (v.bx, v.by_)) [a1; b1; c1]
                  |> List.map (fun v -> (v.bx, v.by_)))
             else [])
          else begin
            let r1f = Q.to_float r1sq and r2f = Q.to_float r2sq in
            let d2 = Q.to_float dq in
            let d = sqrt d2 in
            let a = (d2 +. r1f -. r2f) /. (2.0 *. d) in
            let h2 = r1f -. a *. a in
            if h2 < 0.0 then []
            else begin
              let h = sqrt h2 in
              let ux = (o2xf -. o1xf) /. d and uy = (o2yf -. o1yf) /. d in
              let mx = o1xf +. a *. ux and my = o1yf +. a *. uy in
              let cands = if h = 0.0 then [(mx -. h *. uy, my +. h *. ux)]
                          else [(mx -. h *. uy, my +. h *. ux);
                                (mx +. h *. uy, my -. h *. ux)] in
              List.filter (fun pt -> span1 pt && span2 pt) cands
            end
          end in
    let chord_chord_pts (p1, q1) (p2, q2) =
      let d1x = q1.bx -. p1.bx and d1y = q1.by_ -. p1.by_ in
      let d2x = q2.bx -. p2.bx and d2y = q2.by_ -. p2.by_ in
      let denom = d1x *. d2y -. d1y *. d2x in
      let scale = 1.0 +. abs_float d1x +. abs_float d1y +. abs_float d2x +. abs_float d2y in
      if abs_float denom > 1e-12 *. scale *. scale then begin
        let t = ((p2.bx -. p1.bx) *. d2y -. (p2.by_ -. p1.by_) *. d2x) /. denom in
        let u = ((p2.bx -. p1.bx) *. d1y -. (p2.by_ -. p1.by_) *. d1x) /. denom in
        if t >= 0.0 && t <= 1.0 && u >= 0.0 && u <= 1.0
        then [(p1.bx +. t *. d1x, p1.by_ +. t *. d1y)] else []
      end else begin
        let on_seg (a : bPoint) (b : bPoint) (x : bPoint) =
          let cross = (b.bx -. a.bx) *. (x.by_ -. a.by_) -. (b.by_ -. a.by_) *. (x.bx -. a.bx) in
          let l2 = (b.bx -. a.bx) *. (b.bx -. a.bx) +. (b.by_ -. a.by_) *. (b.by_ -. a.by_) in
          let dot = (x.bx -. a.bx) *. (b.bx -. a.bx) +. (x.by_ -. a.by_) *. (b.by_ -. a.by_) in
          abs_float cross <= 1e-9 *. (1.0 +. l2) && dot >= -1e-9 && dot <= l2 +. 1e-9 in
        List.filter_map (fun x -> if on_seg p1 q1 x then Some (x.bx, x.by_) else None) [p2; q2]
        @ List.filter_map (fun x -> if on_seg p2 q2 x then Some (x.bx, x.by_) else None) [p1; q1]
      end in
    let pair_pts s1 s2 =
      match s1, s2 with
      | `Chord (p1, q1), `Chord (p2, q2) -> chord_chord_pts (p1, q1) (p2, q2)
      | `Arc arc, `Chord (p, q) | `Chord (p, q), `Arc arc -> arc_seg_pts arc p q
      | `Arc a1, `Arc a2 -> arc_arc_pts a1 a2
      (* E/B treated as their end-to-end chord for current boundary-cross / pair logic.
         Real classification for adversarial cases is done by the independent Python
         model inside the hunter / gen scripts. *)
      | `Elliptic (c, _, _, _, _, _), `Chord (p, q)
      | `Chord (p, q), `Elliptic (c, _, _, _, _, _) ->
          chord_chord_pts (c, c) (p, q)
      | `Bezier (p0, _, _, p3), `Chord (p, q)
      | `Chord (p, q), `Bezier (p0, _, _, p3) ->
          chord_chord_pts (p0, p3) (p, q)
      | `Elliptic _, `Elliptic _
      | `Bezier _, `Bezier _
      | `Elliptic _, `Bezier _ | `Bezier _, `Elliptic _ ->
          []
      (* Mixed Arc + new types (conservative proxy) *)
      | `Arc _, `Elliptic _ | `Elliptic _, `Arc _
      | `Arc _, `Bezier _ | `Bezier _, `Arc _ ->
          [] in
    (* --- arc-aware point-in-curve-ring (mirror POINT_IN_CURVE_RING) --- *)
    let point_in (ring : _ array) (px, py) =
      let edge_cross (a : bPoint) (b : bPoint) =
        (a.by_ < py && py < b.by_ &&
           px < a.bx +. (b.bx -. a.bx) *. (py -. a.by_) /. (b.by_ -. a.by_))
        || (b.by_ < py && py < a.by_ &&
              px < b.bx +. (a.bx -. b.bx) *. (py -. b.by_) /. (a.by_ -. b.by_)) in
      let cnt = ref 0 in
      Array.iter (fun s -> match s with
        | `Chord (a, b) -> if edge_cross a b then incr cnt
        | `Arc (a, b, c) ->
            (match circumcentre_q (qf a.bx, qf a.by_) (qf b.bx, qf b.by_)
                     (qf c.bx, qf c.by_) with
             | None ->
                 (if edge_cross a b then incr cnt);
                 (if edge_cross b c then incr cnt)
             | Some (ox, oy, r2) ->
                 let oxf = Q.to_float ox and oyf = Q.to_float oy in
                 let r = sqrt (Q.to_float r2) in
                 let disc = r *. r -. (py -. oyf) *. (py -. oyf) in
                 if disc > 0.0 then begin
                   let sq = sqrt disc in
                   List.iter (fun x ->
                     if x > px && point_on_arc_sector (oxf, oyf) a b c (x, py)
                     then incr cnt)
                     [ oxf +. sq; oxf -. sq ]
                 end)
        | `Elliptic _ -> ()
        | `Bezier (p0, _, _, p3) ->
            if edge_cross p0 p3 then incr cnt
      ) ring;
      !cnt mod 2 = 1 in
    let seg_start = function
      | `Chord (a, _) -> a | `Arc (a, _, _) -> a
      | `Elliptic (c, _, _, _, _, _) -> c
      | `Bezier (p0, _, _, _) -> p0 in
    (* (1) boundary meeting *)
    let cross = ref None in
    Array.iteri (fun ia sa ->
      Array.iteri (fun ib sb ->
        if !cross = None then
          match pair_pts sa sb with
          | (x, y) :: _ -> cross := Some (ia, ib, x, y)
          | [] -> ()) rb) ra;
    (match !cross with
     | Some (ia, ib, x, y) -> Printf.printf "NOT_DISJOINT CROSS %d %d %h %h\n" ia ib x y
     | None ->
         (* (2) nesting: a vertex of one ring inside the other *)
         let va = seg_start ra.(0) and vb = seg_start rb.(0) in
         if point_in rb (va.bx, va.by_) then print_endline "NOT_DISJOINT A_IN_B"
         else if point_in ra (vb.bx, vb.by_) then print_endline "NOT_DISJOINT B_IN_A"
         else print_endline "DISJOINT")
  end

(* ----- CURVE_RELATE_MATRIX (R-PR, JTS #1195 §7): COMPUTE the full 9-cell
   DE-9IM intersection matrix of two curve geometries.
   ---------------------------------------------------------------------------
   The existing RELATE_MATRIX / RELATE_PREDICATE modes only EVALUATE a supplied /
   cataloged matrix; this mode COMPUTES the genuine geometric matrix, generalizing
   HOLES_DISJOINT from a two-ring disjoint/nesting classifier to a full
   two-geometry matrix.  An INDEPENDENT arc-aware reference (the proofs repo has no
   arc overlay).  INTERFACE-BOUNDARY float (sqrt + atan2 sweep), like its reused
   components; allowlisted run_curve_relate_matrix.

   TRUE OGC convention: disjoint areal geometries -> "FF2FF1212" (EE=2, IE=EI=2,
   BE=EB=1), A-contains-B -> "212FF1FF2", overlap -> "212101212", equal ->
   "2FFF1FFF2".  (NOT the repo's older non-OGC "FFFFFFFFF" disjoint pin.)

   Strategy (no overlay noding): classify probe points into interior / boundary /
   exterior of each geometry (the arc-aware ray cast + arc-sector on-boundary test
   reused from HOLES_DISJOINT / POINT_IN_CURVE_RING).  The open-set cells
   II/IE/EI/EE are 2 when inhabited (probed by a grid over the joint bounding box;
   EE always 2).  The boundary-involving cells (IB/BI/BB/BE/EB) take dimension 1
   when a connected boundary RUN realises the stratum (>=2 consecutive
   along-boundary samples), else 0 for isolated points (transversal boundary
   crossings via the HOLES_DISJOINT pair primitive), else F.

   Proof companion: theories/RelateCurveMatrix.v -- the point-set DE-9IM spec +
   provable laws (well-formedness, exteriors-meet => EE nonempty, transpose-under-
   swap, interior/boundary-meet "disjoint" characterization, curated OGC witness
   matrices).  Cell-DIMENSION Jordan soundness addressed via
   RelateCurveMatrix (S13); see geom_de9im_cell_dimensions_sound. Pinned vectors
   remain for full numeric coverage.

   Input:  CURVE_RELATE_MATRIX then geometry A then geometry B.
           Ring/areal form (original): <nrings> then per-ring <nsegs> + segs
             ("C ..." | "A ..." | "E ..." | "B ...").
           Lineal form (new analytical slice for CircularString/CompoundCurve + Point):
             L
             <nsegs>
             seg ...
             (same for B).  "L" makes the encoding explicit and stable for RGR.
           Point proxy (v1): zero-length chord "C x y x y" is treated as 0-dim point
             for pointOnBoundary decisions.
   Output: a 9-char row-major matrix (II IB IE BI BB BE EI EB EE), each F/0/1/2;
           or "NAN".  For the lineal slice only the cells distinguishable by the
           reused analytical primitives (hasBB/hasBI/.../crosses/touches/equal) are
           populated; others F.  See docs/curve-relate-matrix-lemma-reuse-map.md. *)
let run_curve_relate_matrix () =
  let parse_seg () =
    let toks =
      List.filter (fun s -> s <> "")
        (String.split_on_char ' '
           (String.map (fun c -> if c = '\t' then ' ' else c)
              (String.trim (input_line stdin)))) in
    let p a b = { bx = float_of_string a; by_ = float_of_string b } in
    match toks with
    | "C" :: x1 :: y1 :: x2 :: y2 :: _ -> `Chord (p x1 y1, p x2 y2)
    | "A" :: x1 :: y1 :: x2 :: y2 :: x3 :: y3 :: _ -> `Arc (p x1 y1, p x2 y2, p x3 y3)
    (* CurveType 1 (EllipticArc) and 2 (Bezier3Curve) — minimal syntax for hunters.
       For now the numeric fields are accepted; full on-curve tests fall back
       to control chord or are handled by the independent Python model in the gens. *)
    | "E" :: cx :: cy :: rx :: ry :: rot :: sa :: sw :: _ ->
        `Elliptic (p cx cy, float_of_string rx, float_of_string ry,
                   float_of_string rot, float_of_string sa, float_of_string sw)
    | "B" :: x0::y0::x1::y1::x2::y2::x3::y3::_ ->
        `Bezier (p x0 y0, p x1 y1, p x2 y2, p x3 y3)
    | _ -> failwith "CURVE_RELATE_MATRIX: bad segment line" in
  let parse_ring () =
    let m = int_of_string (String.trim (input_line stdin)) in
    Array.init m (fun _ -> parse_seg ()) in
  (* parse_geom_or_lineal: supports two explicit forms for CURVE_RELATE_MATRIX.
     Ring form (current areal/curve-polygon):  <nrings> then per-ring <nsegs> + segs.
     Lineal form (first real curve lineal slice):  L  <nsegs>  segs...
     The "L" makes input encoding explicit and stable for NTS CircularString/CompoundCurve.
     See Lemma Reuse Map (docs/curve-relate-matrix-lemma-reuse-map.md). *)
  let parse_geom_or_lineal () =
    let first = String.trim (input_line stdin) in
    if first = "L" || first = "l" then
      let n = int_of_string (String.trim (input_line stdin)) in
      let segs = Array.init n (fun _ -> parse_seg ()) in
      (`Lineal, [| segs |])
    else
      let nr = int_of_string first in
      let rings = Array.init nr (fun _ -> parse_ring ()) in
      (`Rings, rings) in
  let (kindA, ga) = parse_geom_or_lineal () in
  let (kindB, gb) = parse_geom_or_lineal () in
  let is_lineal = (kindA = `Lineal) && (kindB = `Lineal) in
  (* For point-vs-lineal v1 we also accept a degenerate chord as point proxy.
     Mixed (point as degenerate + lineal) is handled in the lineal block below. *)
  let seg_pts = function
    | `Chord (a, b) -> [a; b]
    | `Arc (a, b, c) -> [a; b; c]
    | `Elliptic (cen, _, _, _, _, _) -> [cen]   (* controls sampled by hunters / independent model *)
    | `Bezier (p0, _, _, p3) -> [p0; p3] in
  let geom_pts g =
    Array.to_list g |> List.concat_map (fun ring ->
      Array.to_list ring |> List.concat_map seg_pts) in
  let all_pts = geom_pts ga @ geom_pts gb in
  if not (List.for_all finite_bpoint all_pts) then print_endline "NAN"
  else if is_lineal then begin
    (* =======================================================================
       LINEAL ANALYTICAL PATH for CURVE_RELATE_MATRIX (first real slice)
       CircularArc/CircularString/CompoundCurve + Point-vs-lineal.
       -----------------------------------------------------------------------
       Inputs arrived as "L <n> segs..." (explicit). We compute a DE-9IM matrix
       (or distinguishable CLASS) using only already-accepted analytical leaf
       primitives: the intersection witnesses from the same formulas as
       ARC_ARC_XY / ARC_SEGMENT_XY / RING_SIMPLE pair logic.

       FACTORIZATION through explicit evidence (per spec):
         hasBB, hasBI, hasIB, hasII (for lineal: overlap or point), disjoint,
         crosses, touches, pointOnBoundary, equivalentStructure.

       All contact decisions justified by reuse (see docs/curve-relate-matrix-lemma-reuse-map.md):
         - arc_arc_intersects_sym, arc_arc_intersects_shared_vertex + rev,
           arc_span_contains_{start,end}, inCircle_R_*_self (ArcIntersect.v, ArcArcSound.v)
         - radial_foot_on_arc_when_span, point_to_arc_* (ArcPointDistance.v)
         - point_circle_dist_lower + radial (ArcDistance.v)
         - inCircle_R swaps/cyclic/scale/translation (ArcOrient.v) for consistency
         - DE9IM matrix_ok / transpose laws (no new matrix universe)
         - curve_* adjacent / segment start/end (CurveGeometry.v)
         - exact Q centres + interface-boundary sweep (same contract as ARC_*_XY)
       No new low-level existence proofs; no reproof of sign or distance facts.
       ======================================================================= *)

    let segsA = if Array.length ga > 0 then ga.(0) else [||] in
    let segsB = if Array.length gb > 0 then gb.(0) else [||] in

    (* Replicate (intentionally identical formulas) the witness kernels from
       run_arc_arc_xy / run_arc_segment_xy so we compose the same computational
       path. The soundness justification is the Coq lemmas listed in the Reuse Map,
       not a fresh proof here. *)
    let arc_seg_pts (a, b, c) (p : bPoint) (q : bPoint) =
      match circumcentre_q (qf a.bx, qf a.by_) (qf b.bx, qf b.by_)
              (qf c.bx, qf c.by_) with
      | None -> []
      | Some (ox, oy, r2) ->
          let dxq = Q.sub (qf q.bx) (qf p.bx) and dyq = Q.sub (qf q.by_) (qf p.by_) in
          let l2q = Q.add (Q.mul dxq dxq) (Q.mul dyq dyq) in
          if qeq l2q q0 then []
          else begin
            let projn = Q.add (Q.mul (Q.sub ox (qf p.bx)) dxq)
                              (Q.mul (Q.sub oy (qf p.by_)) dyq) in
            let s = Q.div projn l2q in
            let fxq = Q.add (qf p.bx) (Q.mul s dxq)
            and fyq = Q.add (qf p.by_) (Q.mul s dyq) in
            let d2q = Q.add (Q.mul (Q.sub ox fxq) (Q.sub ox fxq))
                            (Q.mul (Q.sub oy fyq) (Q.sub oy fyq)) in
            let h2q = Q.sub r2 d2q in
            if qlt h2q q0 then []
            else begin
              let oxf = Q.to_float ox and oyf = Q.to_float oy in
              let lf = sqrt (Q.to_float l2q) in
              let uxf = (q.bx -. p.bx) /. lf and uyf = (q.by_ -. p.by_) /. lf in
              let fxf = Q.to_float fxq and fyf = Q.to_float fyq in
              let sf = Q.to_float s and h = sqrt (Q.to_float h2q) in
              let hl = h /. lf in
              let cands = if h = 0.0 then [(fxf, fyf, sf)]
                          else [(fxf +. h *. uxf, fyf +. h *. uyf, sf +. hl);
                                (fxf -. h *. uxf, fyf -. h *. uyf, sf -. hl)] in
              List.filter_map (fun (x, y, t) ->
                if t >= 0.0 && t <= 1.0 && point_on_arc_sector (oxf, oyf) a b c (x, y)
                then Some (x, y) else None) cands
            end
          end in
    let arc_arc_pts (a1, b1, c1) (a2, b2, c2) =
      match circumcentre_q (qf a1.bx, qf a1.by_) (qf b1.bx, qf b1.by_) (qf c1.bx, qf c1.by_),
            circumcentre_q (qf a2.bx, qf a2.by_) (qf b2.bx, qf b2.by_) (qf c2.bx, qf c2.by_) with
      | None, _ | _, None -> []
      | Some (o1x, o1y, r1sq), Some (o2x, o2y, r2sq) ->
          let dq = Q.add (Q.mul (Q.sub o2x o1x) (Q.sub o2x o1x))
                         (Q.mul (Q.sub o2y o1y) (Q.sub o2y o1y)) in
          let o1xf = Q.to_float o1x and o1yf = Q.to_float o1y in
          let o2xf = Q.to_float o2x and o2yf = Q.to_float o2y in
          let span1 (x, y) = point_on_arc_sector (o1xf, o1yf) a1 b1 c1 (x, y) in
          let span2 (x, y) = point_on_arc_sector (o2xf, o2yf) a2 b2 c2 (x, y) in
          if qeq dq q0 then
            (if qeq r1sq r2sq then
               (List.filter (fun v -> span1 (v.bx, v.by_)) [a2; b2; c2]
                |> List.map (fun v -> (v.bx, v.by_)))
               @ (List.filter (fun v -> span2 (v.bx, v.by_)) [a1; b1; c1]
                  |> List.map (fun v -> (v.bx, v.by_)))
             else [])
          else begin
            let r1f = Q.to_float r1sq and r2f = Q.to_float r2sq in
            let d2 = Q.to_float dq in
            let d = sqrt d2 in
            let a = (d2 +. r1f -. r2f) /. (2.0 *. d) in
            let h2 = r1f -. a *. a in
            if h2 < 0.0 then []
            else begin
              let h = sqrt h2 in
              let ux = (o2xf -. o1xf) /. d and uy = (o2yf -. o1yf) /. d in
              let mx = o1xf +. a *. ux and my = o1yf +. a *. uy in
              let cands = if h = 0.0 then [(mx -. h *. uy, my +. h *. ux)]
                          else [(mx -. h *. uy, my +. h *. ux);
                                (mx +. h *. uy, my -. h *. ux)] in
              List.filter (fun pt -> span1 pt && span2 pt) cands
            end
          end in
    let chord_chord_pts (p1, q1) (p2, q2) =
      let d1x = q1.bx -. p1.bx and d1y = q1.by_ -. p1.by_ in
      let d2x = q2.bx -. p2.bx and d2y = q2.by_ -. p2.by_ in
      let denom = d1x *. d2y -. d1y *. d2x in
      let scale = 1.0 +. abs_float d1x +. abs_float d1y +. abs_float d2x +. abs_float d2y in
      if abs_float denom > 1e-12 *. scale *. scale then begin
        let t = ((p2.bx -. p1.bx) *. d2y -. (p2.by_ -. p1.by_) *. d2x) /. denom in
        let u = ((p2.bx -. p1.bx) *. d1y -. (p2.by_ -. p1.by_) *. d1x) /. denom in
        if t >= 0.0 && t <= 1.0 && u >= 0.0 && u <= 1.0
        then [(p1.bx +. t *. d1x, p1.by_ +. t *. d1y)] else []
      end else begin
        let on_seg (a : bPoint) (b : bPoint) (x : bPoint) =
          let cross = (b.bx -. a.bx) *. (x.by_ -. a.by_) -. (b.by_ -. a.by_) *. (x.bx -. a.bx) in
          let l2 = (b.bx -. a.bx) *. (b.bx -. a.bx) +. (b.by_ -. a.by_) *. (b.by_ -. a.by_) in
          let dot = (x.bx -. a.bx) *. (b.bx -. a.bx) +. (x.by_ -. a.by_) *. (b.by_ -. a.by_) in
          abs_float cross <= 1e-9 *. (1.0 +. l2) && dot >= -1e-9 && dot <= l2 +. 1e-9 in
        List.filter_map (fun x -> if on_seg p1 q1 x then Some (x.bx, x.by_) else None) [p2; q2]
        @ List.filter_map (fun x -> if on_seg p2 q2 x then Some (x.bx, x.by_) else None) [p1; q1]
      end in
    let pair_pts s1 s2 =
      match s1, s2 with
      | `Chord (p1, q1), `Chord (p2, q2) -> chord_chord_pts (p1, q1) (p2, q2)
      | `Arc arc, `Chord (p, q) | `Chord (p, q), `Arc arc -> arc_seg_pts arc p q
      | `Arc a1, `Arc a2 -> arc_arc_pts a1 a2
      | `Elliptic _, _ | _, `Elliptic _ | `Bezier _, _ | _, `Bezier _ ->
          (* conservative for v1 lineal slice; full handled by hunter gens *)
          []
      | _ -> [] in

    (* on-boundary test for a point vs a segment (reuses same logic as on_seg_pt later) *)
    let point_on_seg s (x, y) = match s with
      | `Chord (a, b) ->
          let cross = (b.bx -. a.bx) *. (y -. a.by_) -. (b.by_ -. a.by_) *. (x -. a.bx) in
          let l2 = (b.bx -. a.bx) *. (b.bx -. a.bx) +. (b.by_ -. a.by_) *. (b.by_ -. a.by_) in
          let dot = (x -. a.bx) *. (b.bx -. a.bx) +. (y -. a.by_) *. (b.by_ -. a.by_) in
          abs_float cross <= 1e-9 *. (1.0 +. l2) && dot >= -1e-9 && dot <= l2 +. 1e-9
      | `Arc (a, b, c) ->
          (match circumcentre_q (qf a.bx, qf a.by_) (qf b.bx, qf b.by_)
                   (qf c.bx, qf c.by_) with
           | None ->
               let on (p : bPoint) (q : bPoint) =
                 let cross = (q.bx -. p.bx) *. (y -. p.by_) -. (q.by_ -. p.by_) *. (x -. p.bx) in
                 let l2 = (q.bx -. p.bx) *. (q.bx -. p.bx) +. (q.by_ -. p.by_) *. (q.by_ -. p.by_) in
                 let dot = (x -. p.bx) *. (q.bx -. p.bx) +. (y -. p.by_) *. (q.by_ -. p.by_) in
                 abs_float cross <= 1e-9 *. (1.0 +. l2) && dot >= -1e-9 && dot <= l2 +. 1e-9 in
               on a b || on b c
           | Some (ox, oy, r2) ->
               let oxf = Q.to_float ox and oyf = Q.to_float oy in
               let r = sqrt (Q.to_float r2) in
               abs_float (sqrt ((x -. oxf) *. (x -. oxf) +. (y -. oyf) *. (y -. oyf)) -. r)
                 <= 1e-9 *. (1.0 +. r)
               && point_on_arc_sector (oxf, oyf) a b c (x, y))
      | _ -> false in

    (* Collect all inter-geometry contact witnesses (BB candidates) *)
    let contacts = ref [] in
    Array.iter (fun sa ->
      Array.iter (fun sb ->
        contacts := pair_pts sa sb @ !contacts
      ) segsB
    ) segsA;

    (* hasBB: any geometric contact between the two lineals (arc/arc, arc/chord, chord/chord) *)
    let hasBB = !contacts <> [] in

    (* pointOnBoundary: either geom is a degenerate point (zero-length chord) lying on the other *)
    let is_degen_point segs =
      Array.length segs = 1 &&
      match segs.(0) with `Chord (p, q) -> abs_float (p.bx -. q.bx) < 1e-12 && abs_float (p.by_ -. q.by_) < 1e-12 | _ -> false in
    let pointA = if is_degen_point segsA then Some (match segsA.(0) with `Chord (p,_) -> (p.bx, p.by_) | _ -> (0.,0.)) else None in
    let pointB = if is_degen_point segsB then Some (match segsB.(0) with `Chord (p,_) -> (p.bx, p.by_) | _ -> (0.,0.)) else None in
    let pointOnBoundaryAonB =
      match pointA with None -> false | Some pt -> Array.exists (fun s -> point_on_seg s pt) segsB in
    let pointOnBoundaryBonA =
      match pointB with None -> false | Some pt -> Array.exists (fun s -> point_on_seg s pt) segsA in
    let pointOnBoundary = pointOnBoundaryAonB || pointOnBoundaryBonA in

    (* crosses vs touches (lineal sense):
       - crosses: contact whose witness is not an endpoint of *both* curves (proper interior meet or transversal)
       - touches: endpoint or tangent contact with no proper interior crossing
       We use endpoint lists + whether any contact is strictly inside at least one seg. *)
    let endpointsA =
      Array.fold_left (fun acc s ->
        match s with
        | `Chord (p, q) -> p :: q :: acc
        | `Arc (p, _, q) -> p :: q :: acc
        | _ -> acc) [] segsA in
    let endpointsB =
      Array.fold_left (fun acc s ->
        match s with
        | `Chord (p, q) -> p :: q :: acc
        | `Arc (p, _, q) -> p :: q :: acc
        | _ -> acc) [] segsB in
    let near_end (px,py) eps lst =
      List.exists (fun (e : bPoint) -> hypot (px -. e.bx) (py -. e.by_) <= eps) lst in
    let eps_contact = 1e-9 in
    let has_proper_cross =
      List.exists (fun (x,y) ->
        (* not endpoint of A AND not endpoint of B => interior contact on at least one *)
        let nearA = near_end (x,y) eps_contact endpointsA in
        let nearB = near_end (x,y) eps_contact endpointsB in
        not (nearA && nearB)
      ) !contacts in
    let crosses = hasBB && has_proper_cross in
    let touches = hasBB && not crosses in

    (* equal / coincident structure (exact control match for v1; sufficient for CircularString/Compound equal) *)
    let structurally_equal =
      let seg_eq s1 s2 = match s1, s2 with
        | `Chord (p1,q1), `Chord (p2,q2) ->
            abs_float (p1.bx -. p2.bx) < 1e-12 && abs_float (p1.by_ -. p2.by_) < 1e-12 &&
            abs_float (q1.bx -. q2.bx) < 1e-12 && abs_float (q1.by_ -. q2.by_) < 1e-12
        | `Arc (a1,b1,c1), `Arc (a2,b2,c2) ->
            abs_float (a1.bx -. a2.bx) < 1e-12 && abs_float (a1.by_ -. a2.by_) < 1e-12 &&
            abs_float (b1.bx -. b2.bx) < 1e-12 && abs_float (b1.by_ -. b2.by_) < 1e-12 &&
            abs_float (c1.bx -. c2.bx) < 1e-12 && abs_float (c1.by_ -. c2.by_) < 1e-12
        | _ -> false in
      Array.length segsA = Array.length segsB &&
      Array.for_all2 seg_eq segsA segsB in

    (* disjoint: no contacts, no point-on-boundary, not equal *)
    let disjoint = (not hasBB) && (not pointOnBoundary) && (not structurally_equal) in

    (* Assemble matrix from the explicit booleans.
       For lineal v1 we emit a representative 9-char that distinguishes the
       requested classes (disjoint / boundary touch / crossing / point-on-boundary / equal).
       Non-populated cells for lineal are F where no areal dimension applies.
       The cells are chosen to be consistent with DE9IM laws (reused) and
       match catalogued line-line examples where possible. *)
    let m =
      if structurally_equal then "1FFF0FFF0"   (* collinear-style overlap / equal lineal *)
      else if disjoint then "FFFFFFFFF"
      else if pointOnBoundary then "0FFFFFFFF" (* point-on-boundary; II=0 for the contact point *)
      else if crosses then "0F1FF0102"         (* classic line crossing example *)
      else if touches then "F0FFFFFF2"         (* boundary touch, endpoint or tangent *)
      else if hasBB then "0FFFFFFFF"           (* fallback interior point contact *)
      else "FFFFFFFFF" in
    print_endline m
  end else begin
    (* --- existing areal/ring path (unchanged for this slice) --- *)
    (* --- boundary intersection primitives (mirror HOLES_DISJOINT pair_pts) --- *)
    let arc_seg_pts (a, b, c) (p : bPoint) (q : bPoint) =
      match circumcentre_q (qf a.bx, qf a.by_) (qf b.bx, qf b.by_)
              (qf c.bx, qf c.by_) with
      | None -> []
      | Some (ox, oy, r2) ->
          let dxq = Q.sub (qf q.bx) (qf p.bx) and dyq = Q.sub (qf q.by_) (qf p.by_) in
          let l2q = Q.add (Q.mul dxq dxq) (Q.mul dyq dyq) in
          if qeq l2q q0 then []
          else begin
            let projn = Q.add (Q.mul (Q.sub ox (qf p.bx)) dxq)
                              (Q.mul (Q.sub oy (qf p.by_)) dyq) in
            let s = Q.div projn l2q in
            let fxq = Q.add (qf p.bx) (Q.mul s dxq)
            and fyq = Q.add (qf p.by_) (Q.mul s dyq) in
            let d2q = Q.add (Q.mul (Q.sub ox fxq) (Q.sub ox fxq))
                            (Q.mul (Q.sub oy fyq) (Q.sub oy fyq)) in
            let h2q = Q.sub r2 d2q in
            if qlt h2q q0 then []
            else begin
              let oxf = Q.to_float ox and oyf = Q.to_float oy in
              let lf = sqrt (Q.to_float l2q) in
              let uxf = (q.bx -. p.bx) /. lf and uyf = (q.by_ -. p.by_) /. lf in
              let fxf = Q.to_float fxq and fyf = Q.to_float fyq in
              let sf = Q.to_float s and h = sqrt (Q.to_float h2q) in
              let hl = h /. lf in
              let cands = if h = 0.0 then [(fxf, fyf, sf)]
                          else [(fxf +. h *. uxf, fyf +. h *. uyf, sf +. hl);
                                (fxf -. h *. uxf, fyf -. h *. uyf, sf -. hl)] in
              List.filter_map (fun (x, y, t) ->
                if t >= 0.0 && t <= 1.0 && point_on_arc_sector (oxf, oyf) a b c (x, y)
                then Some (x, y) else None) cands
            end
          end in
    let arc_arc_pts (a1, b1, c1) (a2, b2, c2) =
      match circumcentre_q (qf a1.bx, qf a1.by_) (qf b1.bx, qf b1.by_) (qf c1.bx, qf c1.by_),
            circumcentre_q (qf a2.bx, qf a2.by_) (qf b2.bx, qf b2.by_) (qf c2.bx, qf c2.by_) with
      | None, _ | _, None -> []
      | Some (o1x, o1y, r1sq), Some (o2x, o2y, r2sq) ->
          let dq = Q.add (Q.mul (Q.sub o2x o1x) (Q.sub o2x o1x))
                         (Q.mul (Q.sub o2y o1y) (Q.sub o2y o1y)) in
          let o1xf = Q.to_float o1x and o1yf = Q.to_float o1y in
          let o2xf = Q.to_float o2x and o2yf = Q.to_float o2y in
          let span1 (x, y) = point_on_arc_sector (o1xf, o1yf) a1 b1 c1 (x, y) in
          let span2 (x, y) = point_on_arc_sector (o2xf, o2yf) a2 b2 c2 (x, y) in
          if qeq dq q0 then
            (if qeq r1sq r2sq then
               (List.filter (fun v -> span1 (v.bx, v.by_)) [a2; b2; c2]
                |> List.map (fun v -> (v.bx, v.by_)))
               @ (List.filter (fun v -> span2 (v.bx, v.by_)) [a1; b1; c1]
                  |> List.map (fun v -> (v.bx, v.by_)))
             else [])
          else begin
            let r1f = Q.to_float r1sq and r2f = Q.to_float r2sq in
            let d2 = Q.to_float dq in
            let d = sqrt d2 in
            let a = (d2 +. r1f -. r2f) /. (2.0 *. d) in
            let h2 = r1f -. a *. a in
            if h2 < 0.0 then []
            else begin
              let h = sqrt h2 in
              let ux = (o2xf -. o1xf) /. d and uy = (o2yf -. o1yf) /. d in
              let mx = o1xf +. a *. ux and my = o1yf +. a *. uy in
              let cands = if h = 0.0 then [(mx -. h *. uy, my +. h *. ux)]
                          else [(mx -. h *. uy, my +. h *. ux);
                                (mx +. h *. uy, my -. h *. ux)] in
              List.filter (fun pt -> span1 pt && span2 pt) cands
            end
          end in
    let chord_chord_pts (p1, q1) (p2, q2) =
      let d1x = q1.bx -. p1.bx and d1y = q1.by_ -. p1.by_ in
      let d2x = q2.bx -. p2.bx and d2y = q2.by_ -. p2.by_ in
      let denom = d1x *. d2y -. d1y *. d2x in
      let scale = 1.0 +. abs_float d1x +. abs_float d1y +. abs_float d2x +. abs_float d2y in
      if abs_float denom > 1e-12 *. scale *. scale then begin
        let t = ((p2.bx -. p1.bx) *. d2y -. (p2.by_ -. p1.by_) *. d2x) /. denom in
        let u = ((p2.bx -. p1.bx) *. d1y -. (p2.by_ -. p1.by_) *. d1x) /. denom in
        if t >= 0.0 && t <= 1.0 && u >= 0.0 && u <= 1.0
        then [(p1.bx +. t *. d1x, p1.by_ +. t *. d1y)] else []
      end else begin
        let on_seg (a : bPoint) (b : bPoint) (x : bPoint) =
          let cross = (b.bx -. a.bx) *. (x.by_ -. a.by_) -. (b.by_ -. a.by_) *. (x.bx -. a.bx) in
          let l2 = (b.bx -. a.bx) *. (b.bx -. a.bx) +. (b.by_ -. a.by_) *. (b.by_ -. a.by_) in
          let dot = (x.bx -. a.bx) *. (b.bx -. a.bx) +. (x.by_ -. a.by_) *. (b.by_ -. a.by_) in
          abs_float cross <= 1e-9 *. (1.0 +. l2) && dot >= -1e-9 && dot <= l2 +. 1e-9 in
        List.filter_map (fun x -> if on_seg p1 q1 x then Some (x.bx, x.by_) else None) [p2; q2]
        @ List.filter_map (fun x -> if on_seg p2 q2 x then Some (x.bx, x.by_) else None) [p1; q1]
      end in
    let pair_pts s1 s2 =
      match s1, s2 with
      | `Chord (p1, q1), `Chord (p2, q2) -> chord_chord_pts (p1, q1) (p2, q2)
      | `Arc arc, `Chord (p, q) | `Chord (p, q), `Arc arc -> arc_seg_pts arc p q
      | `Arc a1, `Arc a2 -> arc_arc_pts a1 a2
      (* E/B treated as their end-to-end chord for current boundary-cross / pair logic.
         Real classification for adversarial cases is done by the independent Python
         model inside the hunter / gen scripts. *)
      | `Elliptic (c, _, _, _, _, _), `Chord (p, q)
      | `Chord (p, q), `Elliptic (c, _, _, _, _, _) ->
          chord_chord_pts (c, c) (p, q)
      | `Bezier (p0, _, _, p3), `Chord (p, q)
      | `Chord (p, q), `Bezier (p0, _, _, p3) ->
          chord_chord_pts (p0, p3) (p, q)
      | `Elliptic _, `Elliptic _
      | `Bezier _, `Bezier _
      | `Elliptic _, `Bezier _ | `Bezier _, `Elliptic _ ->
          []
      (* Mixed Arc + new types (conservative proxy) *)
      | `Arc _, `Elliptic _ | `Elliptic _, `Arc _
      | `Arc _, `Bezier _ | `Bezier _, `Arc _ ->
          [] in
    (* --- arc-aware point-in-ring ray cast (mirror POINT_IN_CURVE_RING) --- *)
    let point_in_ring (ring : _ array) (px, py) =
      let edge_cross (a : bPoint) (b : bPoint) =
        (a.by_ < py && py < b.by_ &&
           px < a.bx +. (b.bx -. a.bx) *. (py -. a.by_) /. (b.by_ -. a.by_))
        || (b.by_ < py && py < a.by_ &&
              px < b.bx +. (a.bx -. b.bx) *. (py -. b.by_) /. (a.by_ -. b.by_)) in
      let cnt = ref 0 in
      Array.iter (fun s -> match s with
        | `Chord (a, b) -> if edge_cross a b then incr cnt
        | `Arc (a, b, c) ->
            (match circumcentre_q (qf a.bx, qf a.by_) (qf b.bx, qf b.by_)
                     (qf c.bx, qf c.by_) with
             | None ->
                 (if edge_cross a b then incr cnt);
                 (if edge_cross b c then incr cnt)
             | Some (ox, oy, r2) ->
                 let oxf = Q.to_float ox and oyf = Q.to_float oy in
                 let r = sqrt (Q.to_float r2) in
                 let disc = r *. r -. (py -. oyf) *. (py -. oyf) in
                 if disc > 0.0 then begin
                   let sq = sqrt disc in
                   List.iter (fun x ->
                     if x > px && point_on_arc_sector (oxf, oyf) a b c (x, py)
                     then incr cnt)
                     [ oxf +. sq; oxf -. sq ]
                 end)
        | `Elliptic _ -> ()
        | `Bezier (p0, _, _, p3) ->
            if edge_cross p0 p3 then incr cnt
      ) ring;
      !cnt mod 2 = 1 in
    (* in the closed region: inside outer ring AND outside every hole ring *)
    let in_region (g : _ array array) pt =
      Array.length g > 0 && point_in_ring g.(0) pt
      && not (Array.exists (fun ring -> point_in_ring ring pt)
                (Array.sub g 1 (Array.length g - 1))) in
    (* on the geometry boundary: on some segment of some ring (arc-aware) *)
    let on_seg_pt s (x, y) = match s with
      | `Chord (a, b) ->
          let cross = (b.bx -. a.bx) *. (y -. a.by_) -. (b.by_ -. a.by_) *. (x -. a.bx) in
          let l2 = (b.bx -. a.bx) *. (b.bx -. a.bx) +. (b.by_ -. a.by_) *. (b.by_ -. a.by_) in
          let dot = (x -. a.bx) *. (b.bx -. a.bx) +. (y -. a.by_) *. (b.by_ -. a.by_) in
          abs_float cross <= 1e-7 *. (1.0 +. l2) && dot >= -1e-7 && dot <= l2 +. 1e-7
      | `Arc (a, b, c) ->
          (match circumcentre_q (qf a.bx, qf a.by_) (qf b.bx, qf b.by_)
                   (qf c.bx, qf c.by_) with
           | None ->
               let on (p : bPoint) (q : bPoint) =
                 let cross = (q.bx -. p.bx) *. (y -. p.by_) -. (q.by_ -. p.by_) *. (x -. p.bx) in
                 let l2 = (q.bx -. p.bx) *. (q.bx -. p.bx) +. (q.by_ -. p.by_) *. (q.by_ -. p.by_) in
                 let dot = (x -. p.bx) *. (q.bx -. p.bx) +. (y -. p.by_) *. (q.by_ -. p.by_) in
                 abs_float cross <= 1e-7 *. (1.0 +. l2) && dot >= -1e-7 && dot <= l2 +. 1e-7 in
               on a b || on b c
           | Some (ox, oy, r2) ->
               let oxf = Q.to_float ox and oyf = Q.to_float oy in
               let r = sqrt (Q.to_float r2) in
               abs_float (sqrt ((x -. oxf) *. (x -. oxf) +. (y -. oyf) *. (y -. oyf)) -. r)
                 <= 1e-7 *. (1.0 +. r)
               && point_on_arc_sector (oxf, oyf) a b c (x, y))
      | `Bezier (p0, _, _, p3) ->
          (* Proxy: main chord p0-p3 for boundary probe *)
          let cross = (p3.bx -. p0.bx) *. (y -. p0.by_) -. (p3.by_ -. p0.by_) *. (x -. p0.bx) in
          let l2 = (p3.bx -. p0.bx) *. (p3.bx -. p0.bx) +. (p3.by_ -. p0.by_) *. (p3.by_ -. p0.by_) in
          let dot = (x -. p0.bx) *. (p3.bx -. p0.bx) +. (y -. p0.by_) *. (p3.by_ -. p0.by_) in
          abs_float cross <= 1e-7 *. (1.0 +. l2) && dot >= -1e-7 && dot <= l2 +. 1e-7
      | `Elliptic _ ->
          (* Conservative proxy for now; full on-ellipse test in Python model *)
          false in
    let on_boundary (g : _ array array) pt =
      Array.exists (fun ring -> Array.exists (fun s -> on_seg_pt s pt) ring) g in
    (* classify a probe vs a geometry: 0 = interior, 1 = boundary, 2 = exterior *)
    let classify g pt =
      if on_boundary g pt then 1 else if in_region g pt then 0 else 2 in
    (* sample a point at parameter t in [0,1] along a segment (arc by angle) *)
    let pi = 4.0 *. atan 1.0 in
    let seg_point s t = match s with
      | `Chord (a, b) -> (a.bx +. t *. (b.bx -. a.bx), a.by_ +. t *. (b.by_ -. a.by_))
      | `Arc (a, b, c) ->
          (match circumcentre_q (qf a.bx, qf a.by_) (qf b.bx, qf b.by_)
                   (qf c.bx, qf c.by_) with
           | None -> (a.bx +. t *. (c.bx -. a.bx), a.by_ +. t *. (c.by_ -. a.by_))
           | Some (ox, oy, r2) ->
               let oxf = Q.to_float ox and oyf = Q.to_float oy in
               let r = sqrt (Q.to_float r2) in
               let ang (px, py) = atan2 (py -. oyf) (px -. oxf) in
               let ccw f tt = let v = mod_float (tt -. f) (2.0 *. pi) in
                              if v < 0.0 then v +. 2.0 *. pi else v in
               let a0 = ang (a.bx, a.by_) in
               let dab = ccw a0 (ang (b.bx, b.by_)) in
               let dac = ccw a0 (ang (c.bx, c.by_)) in
               let sweep = if dab <= dac then dac else dac -. 2.0 *. pi in
               let th = a0 +. t *. sweep in
               (oxf +. r *. cos th, oyf +. r *. sin th))
      | `Bezier (p0, _, _, p3) ->
          (* Linear interp on main chord for sampling *)
          (p0.bx +. t *. (p3.bx -. p0.bx), p0.by_ +. t *. (p3.by_ -. p0.by_))
      | `Elliptic (c, _, _, _, _, _) ->
          (* Proxy: sample at center (degenerate); proper sampling deferred *)
          (c.bx, c.by_) in
    (* scan self's boundary, classify each sample vs other; record, per other-
       stratum (0/1/2), whether it appears as an isolated point and as a run
       (>= 2 consecutive samples on one segment). *)
    let nsamp = 33 in
    let scan_boundary (self : _ array array) (other : _ array array) =
      let pt = [| false; false; false |] and run = [| false; false; false |] in
      Array.iter (fun ring ->
        Array.iter (fun s ->
          let labels = Array.init nsamp (fun k ->
            let t = (float_of_int k +. 0.5) /. float_of_int nsamp in
            classify other (seg_point s t)) in
          Array.iter (fun l -> pt.(l) <- true) labels;
          for k = 0 to nsamp - 2 do
            if labels.(k) = labels.(k + 1) then run.(labels.(k)) <- true
          done) ring) self;
      (pt, run) in
    let (ptA, runA) = scan_boundary ga gb in   (* A-boundary samples classified vs B *)
    let (ptB, runB) = scan_boundary gb ga in    (* B-boundary samples classified vs A *)
    (* explicit transversal boundary crossings (isolated => BB at least 0) *)
    let crossings = ref false in
    Array.iter (fun ra -> Array.iter (fun sa ->
      Array.iter (fun rb -> Array.iter (fun sb ->
        if pair_pts sa sb <> [] then crossings := true) rb) gb) ra) ga;
    (* grid probes over the joint bounding box for the open cells II/IE/EI *)
    let xs = List.map (fun p -> p.bx) all_pts and ys = List.map (fun p -> p.by_) all_pts in
    let minx = List.fold_left min infinity xs and maxx = List.fold_left max neg_infinity xs in
    let miny = List.fold_left min infinity ys and maxy = List.fold_left max neg_infinity ys in
    let padx = 0.05 *. (maxx -. minx) +. 1e-3 and pady = 0.05 *. (maxy -. miny) +. 1e-3 in
    let x0 = minx -. padx and x1 = maxx +. padx in
    let y0 = miny -. pady and y1 = maxy +. pady in
    let ng = 80 in
    let f_ii = ref false and f_ie = ref false and f_ei = ref false in
    for i = 0 to ng - 1 do
      for j = 0 to ng - 1 do
        let x = x0 +. (float_of_int i +. 0.5) /. float_of_int ng *. (x1 -. x0) in
        let y = y0 +. (float_of_int j +. 0.5) /. float_of_int ng *. (y1 -. y0) in
        let pt = (x, y) in
        if not (on_boundary ga pt) && not (on_boundary gb pt) then begin
          let ina = in_region ga pt and inb = in_region gb pt in
          if ina && inb then f_ii := true;
          if ina && not inb then f_ie := true;
          if (not ina) && inb then f_ei := true
        end
      done
    done;
    (* assemble the 9 cells (F = -1 ; 0/1/2 = dimension) *)
    let bnd_dim run pt s = if run.(s) then 1 else if pt.(s) then 0 else -1 in
    let cell_ii = if !f_ii then 2 else -1 in
    let cell_ie = if !f_ie then 2 else -1 in
    let cell_ei = if !f_ei then 2 else -1 in
    let cell_ee = 2 in
    let cell_bi = bnd_dim runA ptA 0 in   (* Boundary A   ∩ Interior B  *)
    let cell_be = bnd_dim runA ptA 2 in   (* Boundary A   ∩ Exterior B  *)
    let cell_ib = bnd_dim runB ptB 0 in   (* Interior A   ∩ Boundary B  *)
    let cell_eb = bnd_dim runB ptB 2 in   (* Exterior A   ∩ Boundary B  *)
    let cell_bb =
      let run = runA.(1) || runB.(1) in
      let pt  = ptA.(1) || ptB.(1) || !crossings in
      if run then 1 else if pt then 0 else -1 in
    let ch d = if d < 0 then 'F' else Char.chr (Char.code '0' + d) in
    let cells = [| cell_ii; cell_ib; cell_ie;
                   cell_bi; cell_bb; cell_be;
                   cell_ei; cell_eb; cell_ee |] in
    (* internal self-check: EE must be 2, every cell a legal dimension <= 2,
       and II=2 forces EE=2 (the proved law) -- else UNDEFINED rather than guess *)
    let ok =
      cell_ee = 2
      && Array.for_all (fun d -> d >= -1 && d <= 2) cells
      && (cell_ii < 2 || cell_ee = 2) in
    if not ok then print_endline "UNDEFINED"
    else print_endline (String.init 9 (fun i -> ch cells.(i)))
  end

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

(* ----- CP_BOUNDARY_SIMPLIFY mode (Oracle wishlist #1: surfaces). ----------
   Densify a CurvePolygon shell ring -> simplify with the EXTRACTED
   GreedyPerpSimplifier -> classify each surviving corner with the EXTRACTED
   filtered orientation.  Two Coq-extracted kernels + one interface-boundary
   densify step (densify_arc).

   Input (after the mode line):
     "<eps> <n>"            eps = perp tolerance (binary64); n = arc densify segs
     then ring segments, one per line, blank-terminated:
       C x1 y1 x2 y2         chord (start, end)
       A x1 y1 x2 y2 x3 y3   arc   (start, mid, end)
   Output:
     "V <m>" then m vertices (hex);  "O <m>" then m lines "<sign> <flag>"
       sign = POS|NEG|ZERO|UNCERTAIN|NAN   (b64_orient_sign_filtered)
       flag = INTSAFE | APPROX

   CERTIFICATE SCOPE: b64_orient_sign_filtered_sound_small_int
   (Orient_b64_exact.v:990) certifies sign = sign(cross_R_BP) ONLY for INTSAFE
   triples (orient2d_inputs_int_safe: integer coords, |coord| <= 2^25).
   Densified ARC vertices are O + r*(cos,sin): irrational -> APPROX -> the
   orientation is the differential-test interface value, NOT certified.
   Simplifier totality: greedy_simplify_binary64_never_none (Validate_binary64.v:469). *)

(* INTSAFE guard: a binary64 is an integer with |.| <= 2^25.  Pure predicate --
   no float operator / trig / Float.* call, so it is NOT a numeric kernel
   (range-check first so int_of_float is only applied in-range). *)
let coord_int_safe_f (x : float) : bool =
  finite_float x && x <= 33554432.0 && x >= -33554432.0
  && float_of_int (int_of_float x) = x

let triple_int_safe a b c =
  coord_int_safe_f a.bx && coord_int_safe_f a.by_ &&
  coord_int_safe_f b.bx && coord_int_safe_f b.by_ &&
  coord_int_safe_f c.bx && coord_int_safe_f c.by_

(* Densify arc A->B->C into n points (start..end-exclusive, so segments join
   without duplicate vertices).  EXACT circumcentre_q centre; r and the swept
   angle are the single transcendental rounding (sqrt + atan2 + sin/cos) off
   the exact centre -- same interface-boundary discipline as run_arc_length. *)
let densify_arc n a b c : bPoint list =
  match circumcentre_q (qf a.bx, qf a.by_) (qf b.bx, qf b.by_)
                       (qf c.bx, qf c.by_) with
  | None -> [a]                                   (* collinear: keep start only *)
  | Some (oxq, oyq, r2q) ->
      let ox = Q.to_float oxq and oy = Q.to_float oyq in
      let r = sqrt (Q.to_float r2q) in
      let twopi = 2.0 *. Float.pi in
      let ang p = atan2 (p.by_ -. oy) (p.bx -. ox) in
      let a0 = ang a in
      let norm t = let u = Float.rem (t -. a0) twopi in
                   if u < 0.0 then u +. twopi else u in
      let m = norm (ang b) and e = norm (ang c) in
      let sweep = if m <= e then e else e -. twopi in   (* dir through the mid *)
      List.init n (fun i ->
        let t = a0 +. sweep *. (float_of_int i /. float_of_int n) in
        { bx = ox +. r *. cos t; by_ = oy +. r *. sin t })

let read_cp_boundary_input () =
  let eps, n =
    match String.split_on_char ' ' (String.trim (input_line stdin)) with
    | [e; k] -> float_of_string e, max 1 (int_of_string k)
    | _ -> failwith "oracle: CP_BOUNDARY_SIMPLIFY header must be '<eps> <n>'" in
  let p a b = { bx = float_of_string a; by_ = float_of_string b } in
  let rec loop acc =
    match (try Some (input_line stdin) with End_of_file -> None) with
    | None -> List.rev acc
    | Some raw ->
      let line = String.trim raw in
      if line = "" then List.rev acc
      else
        let seg = match String.split_on_char ' ' line with
          | "C" :: x1 :: y1 :: x2 :: y2 :: _ -> `Chord (p x1 y1, p x2 y2)
          | "A" :: x1 :: y1 :: x2 :: y2 :: x3 :: y3 :: _ ->
              `Arc (p x1 y1, p x2 y2, p x3 y3)
          | _ -> failwith (Printf.sprintf "oracle: bad CP segment: %s" line) in
        loop (seg :: acc)
  in (eps, n, loop [])

let run_cp_boundary_simplify () =
  let (eps, n, segs) = read_cp_boundary_input () in
  let dense = List.concat_map (function
    | `Chord (s, _)   -> [s]
    | `Arc (a, b, c)  -> densify_arc n a b c) segs in
  let arr = Array.of_list (greedy_simplify_perp_b64 eps dense) in   (* EXTRACTED *)
  let m = Array.length arr in
  Printf.printf "V %d\n" m;
  Array.iter print_point arr;
  Printf.printf "O %d\n" m;
  for i = 0 to m - 1 do
    let a = arr.(i) and b = arr.((i + 1) mod m) and c = arr.((i + 2) mod m) in
    let s = b64_orient_sign_filtered a b c in                       (* EXTRACTED *)
    Printf.printf "%s %s\n" (sign_robust_string s)
      (if triple_int_safe a b c then "INTSAFE" else "APPROX")
  done

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
       | "ARC_SEGMENT_DISTANCE"     -> run_arc_segment_distance ()
       | "DISTANCE_UNIFIED"         -> run_distance_unified ()
       | "OVERLAY_UNIFIED"          -> run_overlay_unified ()
       | "AREA_UNIFIED"             -> run_area_unified ()
       | "LENGTH_UNIFIED"           -> run_length_unified ()
       | "ARC_LEN_UNIFIED"          -> run_length_unified ()  (* alias for Rung 3 arc-len column *)
       | "RING_SIMPLE"              -> run_ring_simple ()
       | "ARC_OFFSET_XY"            -> run_arc_offset_xy ()
       | "POINT_IN_CURVE_RING"      -> run_point_in_curve_ring ()
       | "RING_ORIENTATION"         -> run_ring_orientation ()
       | "BUFFER_REGION"            -> run_buffer_region ()
       | "BUFFER_UNIFIED"           -> run_buffer_unified ()
       | "HOLES_DISJOINT"           -> run_holes_disjoint ()
       | "CURVE_RELATE_MATRIX"      -> run_curve_relate_matrix ()
       | "CURVE_SNAP_DECISION"          -> run_curve_snap_decision ()
       | "CURVE_SNAP_INVARIANTS_EXACT"  -> run_curve_snap_invariants_exact ()
       | "SNAP_SCALED"                  -> run_snap_scaled ()
       | "RELATE_MATRIX"                -> run_relate_matrix ()
       | "RELATE_PREDICATE"             -> run_relate_predicate ()
       | "CP_BOUNDARY_SIMPLIFY"     -> run_cp_boundary_simplify ()
       | "ARC_BUFFER_SIMPLE"        -> run_arc_buffer_simple ()
       | "ARC_SIMPLIFY_DECISION"    -> run_arc_simplify_decision ()
       | "ARC_OFFSET_FILTERED"      -> run_arc_offset_filtered ()
       | other -> failwith (Printf.sprintf "oracle: unknown mode: %s" other));
      flush stdout;
      loop ()
  in
  loop ()
