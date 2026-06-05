(* EXHAUSTIVE half-integer sweep hunting spec=>compute (C2) violations:
   spec=true & compute=false  (a false negative -- oracle drops a real pass).
   exact spec via Zarith Q; compute = extracted. Half-integer grid hits exact
   corner/edge tangencies that random sampling misses. *)
open Extracted
let qle=Q.leq and qeq=Q.equal
let qmin a b=if Q.leq a b then a else b
let qmax a b=if Q.leq a b then b else a
let q0=Q.zero and q1=Q.one and qhalf=Q.of_ints 1 2 and qf=Q.of_float
let lb_inslab c0 c1 lo hi=if qeq c1 c0 then (qle lo c0&&qle c0 hi) else true
let lb_tlo c0 c1 lo hi=if qeq c1 c0 then q0 else qmin (Q.div(Q.sub lo c0)(Q.sub c1 c0))(Q.div(Q.sub hi c0)(Q.sub c1 c0))
let lb_thi c0 c1 lo hi=if qeq c1 c0 then q1 else qmax (Q.div(Q.sub lo c0)(Q.sub c1 c0))(Q.div(Q.sub hi c0)(Q.sub c1 c0))
let touch x0 y0 x1 y1 cx cy=
  let xlo=Q.sub cx qhalf and xhi=Q.add cx qhalf and ylo=Q.sub cy qhalf and yhi=Q.add cy qhalf in
  lb_inslab x0 x1 xlo xhi&&lb_inslab y0 y1 ylo yhi
  &&qle(qmax q0(qmax(lb_tlo x0 x1 xlo xhi)(lb_tlo y0 y1 ylo yhi)))(qmin q1(qmin(lb_thi x0 x1 xlo xhi)(lb_thi y0 y1 ylo yhi)))
let rhe x=let f=Float.floor x in let d=x-.f in if d<0.5 then f else if d>0.5 then f+.1.0 else if Float.rem f 2.0=0.0 then f else f+.1.0
let t a0x a0y a1x a1y cx cy=touch(qf a0x)(qf a0y)(qf a1x)(qf a1y)(qf cx)(qf cy)
let spec p0 p1 (c:bPoint)= t p0.bx p0.by_ p1.bx p1.by_ c.bx c.by_ && t (rhe p0.bx)(rhe p0.by_)(rhe p1.bx)(rhe p1.by_) c.bx c.by_
let grid=[| -1.5;-1.;-0.5;0.;0.5;1.;1.5;2. |]
let () =
  let fn=ref 0 and fp=ref 0 and exfn=ref None and exfp=ref None and total=ref 0 in
  let cs=[| 0.;1.;-1. |] in  (* integer centers (exact corners at +/-0.5) *)
  Array.iter (fun cx-> Array.iter (fun cy->
    let c={bx=cx;by_=cy} in
    Array.iter(fun a-> Array.iter(fun b-> Array.iter(fun d-> Array.iter(fun e->
      let p0={bx=a;by_=b} and p1={bx=d;by_=e} in
      incr total;
      let comp=b64_passes_through_hot_pixel_compute p0 p1 c and sp=spec p0 p1 c in
      if sp && not comp then (incr fn; if !exfn=None then exfn:=Some(p0,p1,c));
      if comp && not sp then (incr fp; if !exfp=None then exfp:=Some(p0,p1,c))
    ) grid) grid) grid) grid) cs) cs;
  Printf.printf "exhaustive cases=%d  C2_viol(spec&&!comp)=%d  (compute&&!spec)=%d\n" !total !fn !fp;
  let pr nm=function None->()|Some(p0,p1,c)->Printf.printf "  %s: P0=(%g,%g) P1=(%g,%g) C=(%g,%g)\n" nm p0.bx p0.by_ p1.bx p1.by_ c.bx c.by_ in
  pr "C2 viol (spec&&!comp)" !exfn; pr "(comp&&!spec)" !exfp
