open Extracted
let coords = [| -8.;-4.;-2.;-1.;-0.5;0.;0.5;1.;2.;3.;4.;1000.;4096. |]
let rc () = if Random.int 3 = 0 then coords.(Random.int (Array.length coords)) else Random.float 200. -. 100.
let rp () = { bx = rc (); by_ = rc () }
let () =
  Random.self_init ();
  let n = 2_000_000 in let mism = ref 0 in
  for _ = 1 to n do
    let s=rp() and m=rp() and e=rp() and p=rp() and q=rp() in
    let sp = b64_inCircle s m e p and sq = b64_inCircle s m e q in
    let old = (sp *. sq) < 0.0 in
    let neu = b64_chord_crosses_arc_circle s m e p q in
    if old <> neu then incr mism
  done;
  Printf.printf "cases=%d mismatch=%d\n" n !mism;
  if !mism=0 then print_endline "BIT-EXACT: b64_chord_crosses_arc_circle == native glue"
  else (print_endline "DIVERGENCE"; exit 1)
