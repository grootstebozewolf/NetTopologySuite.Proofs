(* Definitive bridge test: extracted compute (rounded binary64) vs the EXACT
   real spec, computed with Zarith rationals (Q.of_float is exact: every
   binary64 is a dyadic rational).  Full-range random + boundary-stressed. *)
open Extracted
module Q = Q
let qle a b = Q.leq a b
let qeq a b = Q.equal a b
let qmin a b = if Q.leq a b then a else b
let qmax a b = if Q.leq a b then b else a
let q0 = Q.zero and q1 = Q.one and qhalf = Q.of_ints 1 2
let qf = Q.of_float
let lb_inslab c0 c1 lo hi = if qeq c1 c0 then (qle lo c0 && qle c0 hi) else true
let lb_tlo c0 c1 lo hi = if qeq c1 c0 then q0
  else qmin (Q.div (Q.sub lo c0) (Q.sub c1 c0)) (Q.div (Q.sub hi c0) (Q.sub c1 c0))
let lb_thi c0 c1 lo hi = if qeq c1 c0 then q1
  else qmax (Q.div (Q.sub lo c0) (Q.sub c1 c0)) (Q.div (Q.sub hi c0) (Q.sub c1 c0))
let touch x0 y0 x1 y1 cx cy =
  let xlo=Q.sub cx qhalf and xhi=Q.add cx qhalf and ylo=Q.sub cy qhalf and yhi=Q.add cy qhalf in
  lb_inslab x0 x1 xlo xhi && lb_inslab y0 y1 ylo yhi
  && qle (qmax q0 (qmax (lb_tlo x0 x1 xlo xhi) (lb_tlo y0 y1 ylo yhi)))
         (qmin q1 (qmin (lb_thi x0 x1 xlo xhi) (lb_thi y0 y1 ylo yhi)))
let rhe x = let f=Float.floor x in let dd=x-.f in
  if dd<0.5 then f else if dd>0.5 then f+.1.0 else if Float.rem f 2.0=0.0 then f else f+.1.0
let t a0x a0y a1x a1y cx cy = touch (qf a0x)(qf a0y)(qf a1x)(qf a1y)(qf cx)(qf cy)
let spec_passes (p0:bPoint)(p1:bPoint)(c:bPoint) =
  t p0.bx p0.by_ p1.bx p1.by_ c.bx c.by_
  && t (rhe p0.bx)(rhe p0.by_)(rhe p1.bx)(rhe p1.by_) c.bx c.by_
(* varied generators: generic doubles, near-boundary, integers, half/quarter *)
let g () =
  match Random.int 5 with
  | 0 -> float_of_int (Random.int 21 - 10)              (* integer *)
  | 1 -> float_of_int (Random.int 41 - 20) *. 0.5       (* half *)
  | 2 -> float_of_int (Random.int 81 - 40) *. 0.25      (* quarter *)
  | 3 -> (float_of_int (Random.int 11 - 5)) +. (Random.float 1.0 -. 0.5)  (* near grid+eps *)
  | _ -> Random.float 20.0 -. 10.0                      (* generic dyadic *)
let rp () = { bx=g(); by_=g() }
let () =
  Random.self_init ();
  let n = 5_000_000 in
  let fp=ref 0 and fn=ref 0 and exfp=ref None and exfn=ref None in
  for _=1 to n do
    let p0=rp() and p1=rp() and c=rp() in
    let comp=b64_passes_through_hot_pixel_compute p0 p1 c in
    let spec=spec_passes p0 p1 c in
    if comp && not spec then (incr fp; if !exfp=None then exfp:=Some(p0,p1,c));
    if (not comp) && spec then (incr fn; if !exfn=None then exfn:=Some(p0,p1,c))
  done;
  Printf.printf "cases=%d  soundness_viol=%d  completeness_viol=%d\n" n !fp !fn;
  let pr nm = function None->() | Some(p0,p1,c)->
    Printf.printf "  %s: P0=(%h,%h) P1=(%h,%h) C=(%h,%h)\n" nm p0.bx p0.by_ p1.bx p1.by_ c.bx c.by_ in
  pr "FP(comp&&!spec)" !exfp; pr "FN(!comp&&spec)" !exfn
