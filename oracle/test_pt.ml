(* Differential check: extracted b64_passes_through_*_compute  vs  the OLD
   hand-rolled native driver kernels, over random + boundary-stressed inputs.
   Must be 100% bit-identical before the driver swap. *)
open Extracted

(* ---- OLD native kernels (verbatim from origin/main oracle/driver.ml) ---- *)
let round_half_to_even (x : float) : float =
  if x <> x then x
  else if x = infinity || x = neg_infinity then x
  else
    let f = Float.floor x in
    let d = x -. f in
    if d < 0.5 then f
    else if d > 0.5 then f +. 1.0
    else if Float.rem f 2.0 = 0.0 then f else f +. 1.0
let snap_coord_native (x : float) : float = round_half_to_even x
let snap_native (p : bPoint) : bPoint =
  { bx = snap_coord_native p.bx; by_ = snap_coord_native p.by_ }
let lb_inslab_closed c0 c1 lo hi : bool =
  if c1 = c0 then lo <= c0 && c0 <= hi else true
let lb_inslab_halfopen c0 c1 lo hi : bool =
  if c1 = c0 then lo <= c0 && c0 < hi else true
let lb_tlo c0 c1 lo hi : float =
  if c1 = c0 then 0.0
  else Float.min ((lo -. c0) /. (c1 -. c0)) ((hi -. c0) /. (c1 -. c0))
let lb_thi c0 c1 lo hi : float =
  if c1 = c0 then 1.0
  else Float.max ((lo -. c0) /. (c1 -. c0)) ((hi -. c0) /. (c1 -. c0))
let lb_touches p0 p1 c : bool =
  let x0 = p0.bx and y0 = p0.by_ and x1 = p1.bx and y1 = p1.by_
  and cx = c.bx and cy = c.by_ in
  let xlo = cx -. 0.5 and xhi = cx +. 0.5
  and ylo = cy -. 0.5 and yhi = cy +. 0.5 in
  lb_inslab_closed x0 x1 xlo xhi && lb_inslab_closed y0 y1 ylo yhi
  && Float.max 0.0 (Float.max (lb_tlo x0 x1 xlo xhi) (lb_tlo y0 y1 ylo yhi))
     <= Float.min 1.0 (Float.min (lb_thi x0 x1 xlo xhi) (lb_thi y0 y1 ylo yhi))
let lb_touches_halfopen p0 p1 c : bool =
  let x0 = p0.bx and y0 = p0.by_ and x1 = p1.bx and y1 = p1.by_
  and cx = c.bx and cy = c.by_ in
  let xlo = cx -. 0.5 and xhi = cx +. 0.5
  and ylo = cy -. 0.5 and yhi = cy +. 0.5 in
  let tmin = Float.max 0.0 (Float.max (lb_tlo x0 x1 xlo xhi) (lb_tlo y0 y1 ylo yhi))
  and tmax = Float.min 1.0 (Float.min (lb_thi x0 x1 xlo xhi) (lb_thi y0 y1 ylo yhi)) in
  let tmid = (tmin +. tmax) /. 2.0 in
  let xmid = (1.0 -. tmid) *. x0 +. tmid *. x1
  and ymid = (1.0 -. tmid) *. y0 +. tmid *. y1 in
  lb_inslab_halfopen x0 x1 xlo xhi && lb_inslab_halfopen y0 y1 ylo yhi
  && tmin <= tmax && xmid < xhi && ymid < yhi
let old_filter p0 p1 c = lb_touches p0 p1 c && lb_touches (snap_native p0) (snap_native p1) c
let old_halfopen p0 p1 c =
  lb_touches_halfopen p0 p1 c
  && lb_touches_halfopen (snap_native p0) (snap_native p1) c

(* ---- random / boundary-stressed coordinate generator ---- *)
let coords = [| -2.0; -1.5; -1.0; -0.5; 0.0; 0.5; 1.0; 1.5; 2.0; 3.0 |]
let rand_coord () =
  if Random.int 3 = 0 then coords.(Random.int (Array.length coords))  (* grid/boundary *)
  else (Random.float 6.0) -. 3.0                                      (* generic *)
let rand_pt () = { bx = rand_coord (); by_ = rand_coord () }

let () =
  Random.self_init ();
  let n = 2_000_000 in
  let mism_f = ref 0 and mism_h = ref 0 in
  for _ = 1 to n do
    let p0 = rand_pt () and p1 = rand_pt () and c = rand_pt () in
    if old_filter p0 p1 c <> b64_passes_through_hot_pixel_compute p0 p1 c then incr mism_f;
    if old_halfopen p0 p1 c <> b64_passes_through_hot_pixel_halfopen_compute p0 p1 c then incr mism_h
  done;
  Printf.printf "cases=%d  filter_mismatch=%d  halfopen_mismatch=%d\n" n !mism_f !mism_h;
  if !mism_f = 0 && !mism_h = 0 then print_endline "BIT-EXACT: extracted == old native"
  else (print_endline "DIVERGENCE"; exit 1)
