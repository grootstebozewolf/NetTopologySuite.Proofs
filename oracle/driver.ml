(* =============================================================================
   oracle/driver.ml
   -----------------------------------------------------------------------------
   Stdin/stdout adapter around the Coq-extracted `greedy_simplify_perp_b64`.
   Used as the oracle binary by the differential test harness in
   NetTopologySuite.Curve.

   Protocol (text, ASCII):

       Line 1:     <eps>
       Lines 2..N: <x> <y>
       EOF         terminates the polyline.

   Each numeric token is parsed by OCaml's `float_of_string`, so any
   IEEE 754 binary64 spelling works -- decimal ("0.5"), hex
   ("0x1p-1"), "infinity", "neg_infinity", "nan".  The output uses
   "%h" (hex-float) so consumers can round-trip the bits exactly.

   Single-shot: reads one polyline, writes the simplified result, exits.
   Wrap in a shell loop or pipe one polyline per process if you want
   batch behaviour -- the harness on the C# side does the latter.
   ========================================================================== *)

open Extracted

let read_input () =
  let eps_line = input_line stdin in
  let eps = float_of_string (String.trim eps_line) in
  let rec loop acc =
    match try Some (input_line stdin) with End_of_file -> None with
    | None -> List.rev acc
    | Some raw ->
      let line = String.trim raw in
      if line = "" then loop acc
      else
        match String.split_on_char ' ' line with
        | [x; y] ->
          let bp = { bx = float_of_string x; by_ = float_of_string y } in
          loop (bp :: acc)
        | _ -> failwith (Printf.sprintf "oracle: bad point line: %s" line)
  in
  let pts = loop [] in
  (eps, pts)

let print_point bp =
  Printf.printf "%h %h\n" bp.bx bp.by_

let () =
  let (eps, pts) = read_input () in
  let result = greedy_simplify_perp_b64 eps pts in
  List.iter print_point result
