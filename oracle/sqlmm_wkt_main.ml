(* Standalone stdin protocol for SQLMM_WKT — used when oracle_bin is not
   rebuilt locally.  Same request/reply as driver.ml mode SQLMM_WKT. *)

let rec loop () =
  match try Some (input_line stdin) with End_of_file -> None with
  | None -> ()
  | Some raw ->
      let line = String.trim raw in
      if line = "" then loop ()
      else if line = "SQLMM_WKT" then begin
        let wkt = input_line stdin in
        print_endline (Sqlmm_wkt.parse_line wkt);
        flush stdout;
        loop ()
      end else begin
        prerr_endline ("sqlmm_wkt_bin: expected SQLMM_WKT, got " ^ line);
        exit 2
      end

let () = loop ()
