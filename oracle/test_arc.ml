open Extracted
let coords = [| -8.;-4.;-2.;-1.;-0.5;0.;0.5;1.;2.;3.;4.;1000.;4096. |]
let rc () = if Random.int 3 = 0 then coords.(Random.int (Array.length coords)) else Random.float 200. -. 100.
let rp () = { bx = rc (); by_ = rc () }

(* Bit-level equality so NaN==NaN counts as a match (the extracted projection
   and the native reference produce the SAME NaN on a zero denominator). *)
let bit_eq (a : float) (b : float) = Int64.bits_of_float a = Int64.bits_of_float b

let () =
  Random.self_init ();
  let n = 2_000_000 in

  (* 1. b64_chord_crosses_arc_circle vs the native sign-product glue. *)
  let mism = ref 0 in
  for _ = 1 to n do
    let s=rp() and m=rp() and e=rp() and p=rp() and q=rp() in
    let sp = b64_inCircle s m e p and sq = b64_inCircle s m e q in
    let old = (sp *. sq) < 0.0 in
    let neu = b64_chord_crosses_arc_circle s m e p q in
    if old <> neu then incr mism
  done;
  Printf.printf "cases=%d mismatch=%d\n" n !mism;
  if !mism=0 then print_endline "BIT-EXACT: b64_chord_crosses_arc_circle == native glue"
  else (print_endline "DIVERGENCE"; exit 1);

  (* 2. Arc-line intersection COORDINATES (Scope C): extracted projections
        b64_arc_line_intersect_point_x / _y vs the native Cramer reference,
        bit-for-bit.  Both compute  P + (sP/(sP-sQ)) * (Q - P)  through the
        same IEEE 754 binary64 ops, so they must agree to the bit. *)
  let mism2 = ref 0 and tested = ref 0 in
  for _ = 1 to n do
    let s=rp() and m=rp() and e=rp() and p=rp() and q=rp() in
    let sp = b64_inCircle s m e p and sq = b64_inCircle s m e q in
    let den = sp -. sq in
    if den <> 0.0 then begin
      incr tested;
      let t = sp /. den in
      let refx = p.bx +. t *. (q.bx -. p.bx) in
      let refy = p.by_ +. t *. (q.by_ -. p.by_) in
      let x = b64_arc_line_intersect_point_x s m e p q in
      let y = b64_arc_line_intersect_point_y s m e p q in
      if not (bit_eq x refx && bit_eq y refy) then incr mism2
    end
  done;
  Printf.printf "arc_line cases=%d (den<>0) mismatch=%d\n" !tested !mism2;
  if !mism2=0 then
    print_endline "BIT-EXACT: b64_arc_line_intersect_point_{x,y} == native Cramer reference"
  else (print_endline "DIVERGENCE"; exit 1)
