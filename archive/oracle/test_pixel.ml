open Extracted
(* OLD native logic (verbatim) *)
let in_hot_pixel_halfopen (p:bPoint) (c:bPoint) (scale:float) : bool =
  let r = scale *. 0.5 in
  p.bx >= c.bx -. r && p.bx < c.bx +. r &&
  p.by_ >= c.by_ -. r && p.by_ < c.by_ +. r
let old_apt arc_start arc_mid arc_end center scale =
  let r = scale *. 0.5 in
  let bl = { bx = center.bx -. r; by_ = center.by_ -. r } in
  let br = { bx = center.bx +. r; by_ = center.by_ -. r } in
  let tr = { bx = center.bx +. r; by_ = center.by_ +. r } in
  let tl = { bx = center.bx -. r; by_ = center.by_ +. r } in
  let crosses p q =
    let sp = b64_inCircle arc_start arc_mid arc_end p in
    let sq = b64_inCircle arc_start arc_mid arc_end q in
    sp *. sq < 0.0 in
  crosses bl br || crosses br tr || crosses tr tl || crosses tl bl
  || in_hot_pixel_halfopen arc_start center scale
  || in_hot_pixel_halfopen arc_end center scale
let coords = [| -8.;-4.;-2.;-1.;-0.5;0.;0.5;1.;2.;3.;4.;1000.;4096. |]
let rc () = if Random.int 3 = 0 then coords.(Random.int (Array.length coords)) else Random.float 200. -. 100.
let rp () = { bx = rc (); by_ = rc () }
let rscale () = let s=[|0.5;1.0;2.0;0.25;3.0|] in if Random.int 2=0 then s.(Random.int 5) else Random.float 8.
let () =
  Random.self_init ();
  let n = 2_000_000 in let mism = ref 0 in
  for _ = 1 to n do
    let s=rp() and m=rp() and e=rp() and c=rp() and sc=rscale() in
    if old_apt s m e c sc <> b64_arc_passes_through_hot_pixel s m e c sc then incr mism
  done;
  Printf.printf "cases=%d mismatch=%d\n" n !mism;
  if !mism=0 then print_endline "BIT-EXACT: b64_arc_passes_through_hot_pixel == native"
  else (print_endline "DIVERGENCE"; exit 1)
