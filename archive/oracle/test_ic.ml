open Extracted
(* OLD native incircle (verbatim from driver) *)
let incircle_r_native (a:bPoint) (b:bPoint) (c:bPoint) (p:bPoint) : float =
  let ax = a.bx -. p.bx and ay = a.by_ -. p.by_ in
  let bx = b.bx -. p.bx and by_ = b.by_ -. p.by_ in
  let cx = c.bx -. p.bx and cy = c.by_ -. p.by_ in
  let na = ax *. ax +. ay *. ay in
  let nb = bx *. bx +. by_ *. by_ in
  let nc = cx *. cx +. cy *. cy in
  ax *. (by_ *. nc -. cy *. nb)
  -. ay *. (bx *. nc -. cx *. nb)
  +. na *. (bx *. cy -. cx *. by_)
let coords = [| -8.;-4.;-2.;-1.;-0.5;0.;0.5;1.;2.;3.;4.;1000.;4096. |]
let rc () = if Random.int 3 = 0 then coords.(Random.int (Array.length coords)) else Random.float 200. -. 100.
let rp () = { bx = rc (); by_ = rc () }
let () =
  Random.self_init ();
  let n = 2_000_000 in let mism = ref 0 in
  for _ = 1 to n do
    let a=rp() and b=rp() and c=rp() and p=rp() in
    let o = incircle_r_native a b c p and e = b64_inCircle a b c p in
    (* bit-for-bit compare (NaN-safe) *)
    if Int64.bits_of_float o <> Int64.bits_of_float e then incr mism
  done;
  Printf.printf "cases=%d bit_mismatch=%d\n" n !mism;
  if !mism=0 then print_endline "BIT-EXACT: b64_inCircle == native" else (print_endline "DIVERGENCE"; exit 1)
