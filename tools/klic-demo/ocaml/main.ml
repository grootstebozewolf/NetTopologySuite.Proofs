(* tools/klic-demo/ocaml/main.ml -- the ONLY hand-written OCaml in the
   verified path.  Text I/O around the extracted Rocq code in hotpixel_q.ml:
   it turns decimal digit strings into extracted Z values (using the extracted
   Z.add / Z.mul / Z.of_nat) and back (using the extracted Z.div_eucl), and
   dispatches one query per stdin line.  No geometry or arithmetic here.

   Protocol (one query per line, rationals as "num/den" or "num"):
     SNAP  x s                    -> "<snap(x,s)> <|snap(x,s) - x|>"
     PASS  x0 y0 x1 y1 cx cy s    -> "1" | "0"   q_passes_through_closed
     TOUCH x0 y0 x1 y1 cx cy s    -> "1" | "0"   q_touches_closed
     INTER ax ay bx by cx cy dx dy -> "NONE" | "<x> <y>"  q_seg_intersection
   License: BSD-3-Clause.  NetTopologySuite.Proofs contributors. *)
open Hotpixel_q

let rec nat_of_int k = if k <= 0 then O else S (nat_of_int (k - 1))
let zdigit = Array.init 10 (fun k -> Z.of_nat (nat_of_int k))
let zten = Z.of_nat (nat_of_int 10)

let z_of_string (s : string) : z =
  let neg = String.length s > 0 && s.[0] = '-' in
  let start = if neg || (String.length s > 0 && s.[0] = '+') then 1 else 0 in
  if start >= String.length s then failwith ("bad integer: " ^ s);
  let acc = ref Z0 in
  for i = start to String.length s - 1 do
    let c = s.[i] in
    if c < '0' || c > '9' then failwith ("bad integer: " ^ s);
    acc := Z.add (Z.mul !acc zten) zdigit.(Char.code c - Char.code '0')
  done;
  if neg then Z.opp !acc else !acc

let rec string_of_nonneg (v : z) : string =
  match v with
  | Z0 -> "0"
  | _ ->
    let (Pair (qt, r)) = Z.div_eucl v zten in
    let d = ref (-1) in
    Array.iteri (fun k zk -> if Z.eqb zk r = True then d := k) zdigit;
    let ch = String.make 1 (Char.chr (Char.code '0' + !d)) in
    (match qt with Z0 -> ch | _ -> string_of_nonneg qt ^ ch)

let string_of_z (v : z) : string =
  match v with
  | Zneg _ -> "-" ^ string_of_nonneg (Z.opp v)
  | _ -> string_of_nonneg v

let q_of_string (s : string) : q =
  match String.index_opt s '/' with
  | None -> inject_Z (z_of_string s)
  | Some i ->
    let n = z_of_string (String.sub s 0 i) in
    let d = z_of_string (String.sub s (i + 1) (String.length s - i - 1)) in
    (match d with
     | Zpos p -> qred { qnum = n; qden = p }
     | _ -> failwith ("denominator must be positive: " ^ s))

let string_of_q (v : q) : string =
  let r = qred v in
  match r.qden with
  | XH -> string_of_z r.qnum
  | p -> string_of_z r.qnum ^ "/" ^ string_of_z (Zpos p)

let pt a b = { qx = q_of_string a; qy = q_of_string b }
let b01 = function True -> "1" | False -> "0"

let answer line =
  match List.filter (fun w -> w <> "") (String.split_on_char ' ' (String.trim line)) with
  | [] -> None
  | ["SNAP"; x; s] ->
    let xq = q_of_string x and sq = q_of_string s in
    Some (string_of_q (q_snap_coord xq sq) ^ " " ^ string_of_q (q_snap_disp xq sq))
  | ["PASS"; x0; y0; x1; y1; cx; cy; s] ->
    Some (b01 (q_passes_through_closed (pt x0 y0) (pt x1 y1) (pt cx cy) (q_of_string s)))
  | ["TOUCH"; x0; y0; x1; y1; cx; cy; s] ->
    Some (b01 (q_touches_closed (pt x0 y0) (pt x1 y1) (pt cx cy) (q_of_string s)))
  | ["INTER"; ax; ay; bx; by_; cx; cy; dx; dy] ->
    (match q_seg_intersection (pt ax ay) (pt bx by_) (pt cx cy) (pt dx dy) with
     | None -> Some "NONE"
     | Some p -> Some (string_of_q p.qx ^ " " ^ string_of_q p.qy))
  | _ -> failwith ("bad query: " ^ line)

let () =
  try
    while true do
      let line = input_line stdin in
      match answer line with
      | None -> ()
      | Some a -> print_string a; print_char '\n'
    done
  with End_of_file -> flush stdout
