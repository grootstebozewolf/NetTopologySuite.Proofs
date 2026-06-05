(* Probe the ulp-band around every half-integer config (where tangencies live):
   perturb each coord by +/-k ulp, check spec=>compute (C2: spec&&!comp). *)
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
let rec bump x k = if k=0 then x else if k>0 then bump (Float.succ x) (k-1) else bump (Float.pred x) (k+1)
let grid=[| -1.;-0.5;0.;0.5;1.;1.5 |] and cs=[|0.;1.|]
let ks=[| -3;-2;-1;0;1;2;3 |]
let () =
  let fn=ref 0 and fp=ref 0 and exfn=ref None and tot=ref 0 in
  let base = [ (* (i,which coord 0..5) to perturb *) ] in ignore base;
  Array.iter(fun cx->Array.iter(fun cy->let c={bx=cx;by_=cy} in
   Array.iter(fun a->Array.iter(fun b->Array.iter(fun d->Array.iter(fun e->
     (* perturb each of the 6 coords by each k *)
     for coord=0 to 5 do Array.iter(fun k->
       let a=if coord=0 then bump a k else a and b=if coord=1 then bump b k else b
       and d=if coord=2 then bump d k else d and e=if coord=3 then bump e k else e in
       let cx2=if coord=4 then bump cx k else cx and cy2=if coord=5 then bump cy k else cy in
       let c={bx=cx2;by_=cy2} in
       let p0={bx=a;by_=b} and p1={bx=d;by_=e} in
       incr tot;
       let comp=b64_passes_through_hot_pixel_compute p0 p1 c and sp=spec p0 p1 c in
       if sp && not comp then (incr fn; if !exfn=None then exfn:=Some(p0,p1,c));
       if comp && not sp then incr fp
     ) ks done
   )grid)grid)grid)grid)cs)cs;
  Printf.printf "ulp-band cases=%d  C2_viol(spec&&!comp)=%d  (comp&&!spec)=%d\n" !tot !fn !fp;
  (match !exfn with None->()|Some(p0,p1,c)->Printf.printf "  C2 witness: P0=(%h,%h) P1=(%h,%h) C=(%h,%h)\n" p0.bx p0.by_ p1.bx p1.by_ c.bx c.by_)
