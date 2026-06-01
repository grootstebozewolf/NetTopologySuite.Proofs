(* compute (extracted, rounded float) vs EXACT-rational spec, over half-integer
   inputs (where B2R values are exact and the spec is exactly computable).
   Goal: detect whether b64_..._compute can disagree with the exact R-spec. *)
open Extracted

(* exact rationals, den>0, normalized *)
type q = { n:int; d:int }
let rec gcd a b = if b=0 then abs a else gcd b (a mod b)
let mkq n d = let s = if d<0 then -1 else 1 in let n=n*s and d=d*s in
              let g=gcd n d in let g=if g=0 then 1 else g in {n=n/g; d=d/g}
let qadd a b = mkq (a.n*b.d + b.n*a.d) (a.d*b.d)
let qsub a b = mkq (a.n*b.d - b.n*a.d) (a.d*b.d)
let qdiv a b = mkq (a.n*b.d) (a.d*b.n)
let qle a b = a.n*b.d <= b.n*a.d
let qeq a b = a.n*b.d = b.n*a.d
let qmin a b = if qle a b then a else b
let qmax a b = if qle a b then b else a
let q0 = mkq 0 1 and q1 = mkq 1 1 and qhalf = mkq 1 2
let qof_half (v:float) = mkq (int_of_float (Float.round (v *. 2.0))) 2

(* EXACT spec, mirroring b64_liang_barsky_touches (lb_inslab closed, < upper for
   half-open is the OTHER predicate; here we test the CLOSED filter b64_passes_
   through_hot_pixel_compute, whose spec uses lb_inslab with <= ). *)
let lb_inslab c0 c1 lo hi = if qeq c1 c0 then (qle lo c0 && qle c0 hi) else true
let lb_tlo c0 c1 lo hi = if qeq c1 c0 then q0
  else qmin (qdiv (qsub lo c0) (qsub c1 c0)) (qdiv (qsub hi c0) (qsub c1 c0))
let lb_thi c0 c1 lo hi = if qeq c1 c0 then q1
  else qmax (qdiv (qsub lo c0) (qsub c1 c0)) (qdiv (qsub hi c0) (qsub c1 c0))
let touch x0 y0 x1 y1 cx cy =
  let xlo=qsub cx qhalf and xhi=qadd cx qhalf and ylo=qsub cy qhalf and yhi=qadd cy qhalf in
  lb_inslab x0 x1 xlo xhi && lb_inslab y0 y1 ylo yhi
  && qle (qmax q0 (qmax (lb_tlo x0 x1 xlo xhi) (lb_tlo y0 y1 ylo yhi)))
         (qmin q1 (qmin (lb_thi x0 x1 xlo xhi) (lb_thi y0 y1 ylo yhi)))
(* snap: round half to even (exact integer); same on both sides, so use float *)
let rhe x = let f=Float.floor x in let dd=x-.f in
  if dd<0.5 then f else if dd>0.5 then f+.1.0 else if Float.rem f 2.0=0.0 then f else f+.1.0
let spec_passes (p0:bPoint) (p1:bPoint) (c:bPoint) =
  let tq p = touch (qof_half p.bx) (qof_half p.by_) (qof_half p1.bx) (qof_half p1.by_)
                   (qof_half c.bx) (qof_half c.by_) in ignore tq;
  let t a0 a1 = touch (qof_half a0.bx)(qof_half a0.by_)(qof_half a1.bx)(qof_half a1.by_)(qof_half c.bx)(qof_half c.by_) in
  let s p = { bx=rhe p.bx; by_=rhe p.by_ } in
  t p0 p1 && t (s p0) (s p1)
let hv () = float_of_int (Random.int 17 - 8) *. 0.5   (* half-integer in [-4,4] *)
let rp () = { bx=hv(); by_=hv() }
let () =
  Random.self_init ();
  let n = 5_000_000 in
  let fp = ref 0 (* compute=true, spec=false : SOUNDNESS violation *)
  and fn = ref 0 (* compute=false, spec=true : completeness violation *) in
  let ex_fp = ref None and ex_fn = ref None in
  for _=1 to n do
    let p0=rp() and p1=rp() and c=rp() in
    let comp = b64_passes_through_hot_pixel_compute p0 p1 c in
    let spec = spec_passes p0 p1 c in
    if comp && not spec then (incr fp; if !ex_fp=None then ex_fp:=Some(p0,p1,c));
    if (not comp) && spec then (incr fn; if !ex_fn=None then ex_fn:=Some(p0,p1,c))
  done;
  Printf.printf "cases=%d  soundness_viol(comp&&!spec)=%d  completeness_viol(!comp&&spec)=%d\n" n !fp !fn;
  let pr name = function None -> () | Some(p0,p1,c) ->
    Printf.printf "  %s: P0=(%g,%g) P1=(%g,%g) C=(%g,%g)\n" name p0.bx p0.by_ p1.bx p1.by_ c.bx c.by_ in
  pr "first soundness viol" !ex_fp; pr "first completeness viol" !ex_fn
