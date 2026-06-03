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
       | "TWOSUM"                   -> run_twosum ()
       | "GROW_EXPANSION"           -> run_grow_expansion ()
       | "INTERSECT_FILTERED"       -> run_intersect_filtered ()
       | "INTERSECT_POINT_FILTERED" -> run_intersect_point_filtered ()
       | "INTERSECT_POINT_XY"       -> run_intersect_point_xy ()
       | "PASSES_THROUGH_FILTER"    -> run_passes_through_filter ()
       | "PASSES_THROUGH_HALFOPEN"  -> run_passes_through_halfopen ()
       | "HOLE_PRECISION_AUDIT"          -> run_hole_precision_audit ()
       | "PASSES_THROUGH_EXACT"          -> run_passes_through_exact ()
       | "PASSES_THROUGH_HALFOPEN_EXACT" -> run_passes_through_halfopen_exact ()
       | "EDGE_IN_RESULT"           -> run_edge_in_result ()
       | "INCIRCLE_SIGN"            -> run_incircle_sign ()
       | "INCIRCLE_EXACT"           -> run_incircle_exact ()
       | "ARC_CHORD_CROSSES_CIRCLE" -> run_arc_chord_crosses_circle ()
       | "ARC_PASSES_THROUGH_PIXEL" -> run_arc_passes_through_pixel ()
       | other -> failwith (Printf.sprintf "oracle: unknown mode: %s" other));
      flush stdout;
      loop ()
  in
  loop ()
