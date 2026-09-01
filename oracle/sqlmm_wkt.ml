(* =============================================================================
   oracle/sqlmm_wkt.ml
   -----------------------------------------------------------------------------
   Structural WKT oracle for the ISO/IEC 13249-3 §4.2.1 instantiable ST_Curve
   subtypes that the engines do not yet carry: CLOTHOID, CIRCLE,
   GEODESICSTRING, NURBSCURVE, SPIRALCURVE (plus ELLIPTICALCURVE, also
   instantiable at §4.2.9, so it is not UNKNOWN).

   This is I/O type identity.  It does not evaluate length, does not grow
   CurveSegment, and does not remint 508-*.  Numbers stay decimal tokens;
   there is no binary64 arithmetic here.

   SPIRALTYPE deviation (documented in
   docs/iso13249-3-curve-type-bindings-2026-08.md §8):
     The standard writes <spiraltype text> as free-form <letters>, and
     §5.1.68 length-prefixes the value in WKB, so the value set is open —
     §4.2.12 lists clothoid, bloss, biquadratic, sine and cosine only as
     the *initial* set.  Text has no length prefix, and <letters> admits
     the characters that would end the value, so this lexer reads a spiral
     type up to the comma or parenthesis that terminates it.  Interior
     spaces are preserved (SPIRALTYPE Wiener Bogen parses).  A name
     containing a comma or a parenthesis is the one case this grammar
     cannot represent.

   Protocol (driver mode SQLMM_WKT):
     SQLMM_WKT
     <one WKT line>
   Output: one line
     OK <TYPE> <DIM> ...
     REFUSE <REASON>
     UNKNOWN <TOKEN>
   A successful parse of a lowercase type keyword adds CASEFOLD (the
   spec is silent on keyword case; tolerant-in is the documented
   deviation).  A tagged LINESTRING member inside COMPOUNDCURVE /
   CURVEPOLYGON adds DEVIATION TAGGED_LINESTRING.
   ========================================================================== *)

type dim = XY | Z | M | ZM

exception Parse of string

type cursor = { s : string; mutable i : int }

let slen c = String.length c.s
let eof c = c.i >= slen c
let peek c = if eof c then None else Some c.s.[c.i]

let rec skip_ws c =
  match peek c with
  | Some (' ' | '\t' | '\n' | '\r') -> c.i <- c.i + 1; skip_ws c
  | _ -> ()

let is_digit ch = ch >= '0' && ch <= '9'
let is_letter ch =
  (ch >= 'A' && ch <= 'Z') || (ch >= 'a' && ch <= 'z')

let ieq a b =
  String.uppercase_ascii a = String.uppercase_ascii b

let rtrim s =
  let n = String.length s in
  let rec last i =
    if i < 0 then -1
    else
      match s.[i] with
      | ' ' | '\t' | '\n' | '\r' -> last (i - 1)
      | _ -> i
  in
  let e = last (n - 1) in
  if e < 0 then "" else String.sub s 0 (e + 1)

let dim_string = function
  | XY -> "XY"
  | Z -> "Z"
  | M -> "M"
  | ZM -> "ZM"

let expect_char c ch =
  skip_ws c;
  match peek c with
  | Some x when x = ch -> c.i <- c.i + 1
  | Some x ->
      raise (Parse (Printf.sprintf "expected '%c', got '%c'" ch x))
  | None ->
      raise (Parse (Printf.sprintf "expected '%c', got EOF" ch))

let read_word c =
  skip_ws c;
  match peek c with
  | Some ch when is_letter ch ->
      let start = c.i in
      c.i <- c.i + 1;
      while not (eof c)
            && (is_letter c.s.[c.i] || is_digit c.s.[c.i] || c.s.[c.i] = '_')
      do
        c.i <- c.i + 1
      done;
      String.sub c.s start (c.i - start)
  | _ -> raise (Parse "expected word")

let looks_like_number c =
  skip_ws c;
  match peek c with
  | Some ('+' | '-') ->
      let j = c.i + 1 in
      j < slen c && (is_digit c.s.[j] || c.s.[j] = '.')
  | Some '.' ->
      let j = c.i + 1 in
      j < slen c && is_digit c.s.[j]
  | Some ch -> is_digit ch
  | None -> false

let read_number c =
  skip_ws c;
  let start = c.i in
  (match peek c with
   | Some ('+' | '-') -> c.i <- c.i + 1
   | _ -> ());
  let saw_digit = ref false in
  while not (eof c) && is_digit c.s.[c.i] do
    saw_digit := true;
    c.i <- c.i + 1
  done;
  if not (eof c) && c.s.[c.i] = '.' then begin
    c.i <- c.i + 1;
    while not (eof c) && is_digit c.s.[c.i] do
      saw_digit := true;
      c.i <- c.i + 1
    done
  end;
  if not !saw_digit then raise (Parse "expected number");
  if not (eof c) && (c.s.[c.i] = 'e' || c.s.[c.i] = 'E') then begin
    c.i <- c.i + 1;
    (match peek c with
     | Some ('+' | '-') -> c.i <- c.i + 1
     | _ -> ());
    let exp = ref false in
    while not (eof c) && is_digit c.s.[c.i] do
      exp := true;
      c.i <- c.i + 1
    done;
    if not !exp then raise (Parse "expected exponent")
  end;
  String.sub c.s start (c.i - start)

(* SPIRALTYPE value: anything but comma or parenthesis.  Interior spaces
   stay.  Trailing whitespace before the terminator is not interior. *)
let read_spiraltype_value c =
  skip_ws c;
  let start = c.i in
  let rec scan () =
    match peek c with
    | Some (',' | '(' | ')') | None -> ()
    | Some _ -> c.i <- c.i + 1; scan ()
  in
  scan ();
  rtrim (String.sub c.s start (c.i - start))

let initial_spiraltype s =
  match String.lowercase_ascii s with
  | "clothoid" | "bloss" | "biquadratic" | "sine" | "cosine" -> true
  | _ -> false

let split_type_and_dim raw =
  let u = String.uppercase_ascii raw in
  let n = String.length u in
  if n >= 2 && String.sub u (n - 2) 2 = "ZM" then
    (String.sub raw 0 (n - 2), Some ZM)
  else if n >= 1 && String.sub u (n - 1) 1 = "Z" then
    (String.sub raw 0 (n - 1), Some Z)
  else if n >= 1 && String.sub u (n - 1) 1 = "M" then
    (String.sub raw 0 (n - 1), Some M)
  else
    (raw, None)

let read_optional_dim c attached =
  match attached with
  | Some d -> d
  | None ->
      skip_ws c;
      match peek c with
      | Some ch when is_letter ch ->
          let save = c.i in
          let w = read_word c in
          begin match String.uppercase_ascii w with
          | "ZM" -> ZM
          | "Z" -> Z
          | "M" -> M
          | _ -> c.i <- save; XY
          end
      | _ -> XY

let at_empty c =
  skip_ws c;
  match peek c with
  | Some ch when is_letter ch ->
      let save = c.i in
      let w = read_word c in
      if ieq w "EMPTY" then true else (c.i <- save; false)
  | _ -> false

let finish c =
  skip_ws c;
  if not (eof c) then raise (Parse "trailing input")

let comma_or_rparen c =
  skip_ws c;
  match peek c with
  | Some ',' -> c.i <- c.i + 1; `Comma
  | Some ')' -> `RParen
  | Some x -> raise (Parse (Printf.sprintf "expected ',' or ')', got '%c'" x))
  | None -> raise (Parse "expected ',' or ')', got EOF")

let expect_word c name =
  let w = read_word c in
  if not (ieq w name) then
    raise (Parse (Printf.sprintf "expected %s, got %s" name w))

let read_point_nums c =
  if not (looks_like_number c) then raise (Parse "expected point");
  let rec more acc =
    if looks_like_number c then more (read_number c :: acc) else List.rev acc
  in
  more [read_number c]

let read_point_list c =
  expect_char c '(';
  skip_ws c;
  if peek c = Some ')' then begin
    c.i <- c.i + 1;
    []
  end else
    let rec rest acc =
      match comma_or_rparen c with
      | `RParen -> expect_char c ')'; List.rev acc
      | `Comma -> rest (read_point_nums c :: acc)
    in
    rest [read_point_nums c]

let expected_ords = function
  | XY -> 2
  | Z | M -> 3
  | ZM -> 4

let check_point_dim dim pts =
  let n = expected_ords dim in
  List.iter
    (fun p -> if List.length p <> n then raise (Parse "POINT_DIM"))
    pts

let read_balanced_group c =
  skip_ws c;
  expect_char c '(';
  let start = c.i in
  let rec walk depth =
    if eof c then raise (Parse "unbalanced parenthesis");
    let ch = c.s.[c.i] in
    c.i <- c.i + 1;
    match ch with
    | '(' -> walk (depth + 1)
    | ')' -> if depth = 1 then () else walk (depth - 1)
    | _ -> walk depth
  in
  walk 1;
  rtrim (String.sub c.s start (c.i - start - 1))

let skip_optional_comma c =
  skip_ws c;
  match peek c with
  | Some ',' -> c.i <- c.i + 1
  | _ -> ()

type field = { name : string; value : string }

let rec read_named_fields c acc =
  skip_ws c;
  match peek c with
  | Some ')' -> List.rev acc
  | Some ch when is_letter ch ->
      let name = read_word c in
      skip_ws c;
      let value =
        match peek c with
        | Some '(' -> read_balanced_group c
        | _ when looks_like_number c -> read_number c
        | Some ch when is_letter ch -> read_word c
        | _ -> raise (Parse (Printf.sprintf "bad field %s" name))
      in
      skip_optional_comma c;
      read_named_fields c ({ name; value } :: acc)
  | Some x ->
      raise (Parse (Printf.sprintf "expected field or ')', got '%c'" x))
  | None -> raise (Parse "unterminated field list")

let field_find fields name =
  try Some (List.find (fun f -> ieq f.name name) fields).value
  with Not_found -> None

let require_field fields name =
  match field_find fields name with
  | Some v -> v
  | None -> raise (Parse (Printf.sprintf "missing %s" name))

let parse_point_body dim c ~arity_min ~arity_exact ~empty_ok =
  if at_empty c then
    if empty_ok then "EMPTY" else raise (Parse "EMPTY_FORBIDDEN")
  else begin
    let pts = read_point_list c in
    check_point_dim dim pts;
    let n = List.length pts in
    (match arity_exact with
     | Some k when n <> k -> raise (Parse "ARITY")
     | _ -> ());
    if n < arity_min then raise (Parse "ARITY");
    Printf.sprintf "POINTS %d" n
  end

let parse_clothoid _dim c =
  if at_empty c then "EMPTY"
  else begin
    expect_char c '(';
    let fields = read_named_fields c [] in
    expect_char c ')';
    ignore (require_field fields "AFFINEPLACEMENT");
    let a = require_field fields "SCALEFACTOR" in
    let sd = require_field fields "STARTDISTANCE" in
    let ed = require_field fields "ENDDISTANCE" in
    Printf.sprintf "SCALEFACTOR %s STARTDISTANCE %s ENDDISTANCE %s" a sd ed
  end

let parse_elliptical _dim c =
  if at_empty c then "EMPTY"
  else begin
    expect_char c '(';
    let fields = read_named_fields c [] in
    expect_char c ')';
    ignore (require_field fields "AFFINEPLACEMENT");
    let rx = require_field fields "UAXISLENGTH" in
    let ry = require_field fields "VAXISLENGTH" in
    Printf.sprintf "UAXISLENGTH %s VAXISLENGTH %s" rx ry
  end

let read_number_list_group c =
  expect_char c '(';
  skip_ws c;
  if peek c = Some ')' then begin
    c.i <- c.i + 1;
    []
  end else
    let rec rest acc =
      match comma_or_rparen c with
      | `RParen -> expect_char c ')'; List.rev acc
      | `Comma -> rest (read_number c :: acc)
    in
    rest [read_number c]

let rec read_control_points c =
  expect_char c '(';
  skip_ws c;
  if peek c = Some ')' then begin
    c.i <- c.i + 1;
    0
  end else
    let rec one n =
      skip_ws c;
      match peek c with
      | Some ')' -> n
      | Some '(' ->
          ignore (read_balanced_group c);
          skip_optional_comma c;
          one (n + 1)
      | _ when looks_like_number c ->
          ignore (read_number c);
          while looks_like_number c do ignore (read_number c) done;
          skip_optional_comma c;
          one (n + 1)
      | Some x -> raise (Parse (Printf.sprintf "bad control point '%c'" x))
      | None -> raise (Parse "unterminated CONTROLPOINTS")
    in
    let n = one 0 in
    expect_char c ')';
    n

let parse_nurbs _dim c =
  if at_empty c then "EMPTY"
  else begin
    expect_char c '(';
    skip_ws c;
    expect_word c "DEGREE";
    skip_optional_comma c;
    let deg = read_number c in
    skip_optional_comma c;
    expect_word c "KNOTS";
    skip_optional_comma c;
    let knots = read_number_list_group c in
    skip_optional_comma c;
    expect_word c "CONTROLPOINTS";
    skip_optional_comma c;
    let ncp = read_control_points c in
    skip_ws c;
    skip_optional_comma c;
    expect_char c ')';
    if ncp < 1 then raise (Parse "NURBSCURVE_CONTROLPOINTS");
    Printf.sprintf "DEGREE %s CONTROLPOINTS %d KNOTS %d" deg ncp (List.length knots)
  end

let parse_spiral _dim c =
  if at_empty c then "EMPTY"
  else begin
    expect_char c '(';
    skip_ws c;
    expect_word c "SPIRALTYPE";
    let typ = read_spiraltype_value c in
    if typ = "" then raise (Parse "EMPTY_SPIRALTYPE");
    skip_optional_comma c;
    let fields = read_named_fields c [] in
    expect_char c ')';
    let kind = if initial_spiraltype typ then "INITIAL" else "EXTENSION" in
    let extra =
      match field_find fields "LENGTH" with
      | Some l -> " LENGTH " ^ l
      | None -> ""
    in
    Printf.sprintf "SPIRALTYPE %s %s%s" typ kind extra
  end

type member_info = { kind : string; deviation : string list }

let rec parse_tagged_body typ dim c =
  match String.uppercase_ascii typ with
  | "CIRCLE" ->
      parse_point_body dim c ~arity_min:3 ~arity_exact:(Some 3) ~empty_ok:true
  | "GEODESICSTRING" ->
      parse_point_body dim c ~arity_min:2 ~arity_exact:None ~empty_ok:true
  | "CIRCULARSTRING" | "LINESTRING" ->
      parse_point_body dim c ~arity_min:1 ~arity_exact:None ~empty_ok:true
  | "CLOTHOID" -> parse_clothoid dim c
  | "NURBSCURVE" -> parse_nurbs dim c
  | "SPIRALCURVE" -> parse_spiral dim c
  | "ELLIPTICALCURVE" -> parse_elliptical dim c
  | "COMPOUNDCURVE" | "CURVEPOLYGON" -> parse_compound dim c
  | other -> raise (Parse ("unsupported member " ^ other))

and parse_one_member dim c =
  skip_ws c;
  match peek c with
  | Some '(' ->
      let pts = read_point_list c in
      check_point_dim dim pts;
      { kind = "LINESTRING_BARE"; deviation = [] }
  | Some ch when is_letter ch ->
      let raw = read_word c in
      let typ0, attached = split_type_and_dim raw in
      let typ = String.uppercase_ascii typ0 in
      let mdim = read_optional_dim c attached in
      if mdim <> XY && mdim <> dim then raise (Parse "DIM_CONFLICT");
      let use_dim = if mdim = XY then dim else mdim in
      ignore (parse_tagged_body typ use_dim c);
      let deviation = if typ = "LINESTRING" then ["TAGGED_LINESTRING"] else [] in
      { kind = typ; deviation }
  | _ -> raise (Parse "expected compound member")

and parse_member_list dim c =
  expect_char c '(';
  skip_ws c;
  if peek c = Some ')' then begin
    c.i <- c.i + 1;
    []
  end else
    let rec rest acc =
      skip_ws c;
      match peek c with
      | Some ')' -> c.i <- c.i + 1; List.rev acc
      | Some ',' ->
          c.i <- c.i + 1;
          rest (parse_one_member dim c :: acc)
      | Some x -> raise (Parse (Printf.sprintf "expected ',' or ')', got '%c'" x))
      | None -> raise (Parse "unterminated member list")
    in
    rest [parse_one_member dim c]

and parse_compound dim c =
  if at_empty c then "EMPTY"
  else
    let ms = parse_member_list dim c in
    let n = List.length ms in
    let devs =
      List.concat (List.map (fun m -> m.deviation) ms)
      |> List.sort_uniq String.compare
    in
    let kinds = String.concat "," (List.map (fun m -> m.kind) ms) in
    let extra =
      if devs = [] then "" else " DEVIATION " ^ String.concat "," devs
    in
    Printf.sprintf "MEMBERS %d [%s]%s" n kinds extra

let recognized = function
  | "POINT" | "LINESTRING" | "POLYGON" | "MULTIPOINT"
  | "MULTILINESTRING" | "MULTIPOLYGON" | "GEOMETRYCOLLECTION"
  | "CIRCULARSTRING" | "COMPOUNDCURVE" | "CURVEPOLYGON"
  | "MULTICURVE" | "MULTISURFACE" | "TRIANGLE" | "TIN"
  | "POLYHEDRALSURFACE" -> true
  | _ -> false

let instantiable_zoo = function
  | "CIRCLE" | "GEODESICSTRING" | "ELLIPTICALCURVE"
  | "NURBSCURVE" | "CLOTHOID" | "SPIRALCURVE" -> true
  | _ -> false

let skip_balanced_or_empty c =
  if at_empty c then ()
  else begin
    skip_ws c;
    match peek c with
    | Some '(' -> ignore (read_balanced_group c)
    | _ -> raise (Parse "expected EMPTY or '('")
  end

let type_letters_casefold raw =
  let buf = Buffer.create 16 in
  String.iter (fun ch -> if is_letter ch then Buffer.add_char buf ch) raw;
  let letters = Buffer.contents buf in
  letters <> "" && letters <> String.uppercase_ascii letters

let parse_line raw =
  try
    let c = { s = raw; i = 0 } in
    skip_ws c;
    if eof c then raise (Parse "empty input");
    let raw_typ = read_word c in
    let typ0, attached = split_type_and_dim raw_typ in
    let typ = String.uppercase_ascii typ0 in
    if typ = "" then raise (Parse ("UNKNOWN " ^ String.uppercase_ascii raw_typ));
    let dim = read_optional_dim c attached in
    let specialized =
      instantiable_zoo typ || typ = "CIRCULARSTRING"
      || typ = "COMPOUNDCURVE" || typ = "CURVEPOLYGON"
    in
    if not specialized && not (recognized typ) then
      "UNKNOWN " ^ typ
    else begin
      let body =
        if specialized then parse_tagged_body typ dim c
        else begin
          skip_balanced_or_empty c;
          "RECOGNIZED"
        end
      in
      finish c;
      let fold = if type_letters_casefold raw_typ then " CASEFOLD" else "" in
      Printf.sprintf "OK %s %s %s%s" typ (dim_string dim) body fold
    end
  with
  | Parse msg ->
      if String.length msg >= 8 && String.sub msg 0 8 = "UNKNOWN " then msg
      else "REFUSE " ^ msg
  | Invalid_argument _ ->
      "REFUSE PARSE"
