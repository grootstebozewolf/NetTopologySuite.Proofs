(* ============================================================================
   oracle/relate_matrix.ml
   ----------------------------------------------------------------------------
   Issue #67 session 11 (S11): pinned DE-9IM matrix catalog + predicate engine.

   Hand-rolled lookup mirroring Coq witness definitions in theories/DE9IM.v and
   RelateMatrix*.v (not geometry computation — full RelateNG noding is S13+).
   Keys match oracle/relate_matrix_fill_vocabulary.txt and de9im_*_vectors.txt.

   Pins: theories/RelateLineLine.v, RelateAreaArea.v, RelateAreaLine.v,
         RelateArcChord.v, RelateClothoid.v, RelateBoundary.v,
         RelateCurveAreaPoint.v.
   ========================================================================== *)

type pat = Wild | PFalse | PTrue | PDim of int

let char_matches c ch =
  match c, ch with
  | Wild, _ -> true
  | PFalse, 'F' -> true
  | PFalse, _ -> false
  | PTrue, 'F' -> false
  | PTrue, _ -> true
  | PDim n, ch when ch >= '0' && ch <= '9' -> Char.code ch - Char.code '0' = n
  | PDim _, _ -> false

let pattern_matches p cells =
  List.length p = List.length cells
  && List.for_all2 char_matches p cells

let matrix_cells s =
  if String.length s <> 9 then invalid_arg "relate_matrix: expected 9-char matrix"
  else List.init 9 (fun i -> s.[i])

let matrix_matches patterns cells =
  List.exists (fun p -> pattern_matches p cells) patterns

(* Standard JTS/OGC patterns — mirror theories/DE9IM.v (row-major 9 cells). *)
let pat_disjoint =
  [PFalse; PFalse; Wild; PFalse; PFalse; Wild; PFalse; PFalse; Wild]

let pat_intersects_0 =
  [PTrue; Wild; Wild; Wild; Wild; Wild; Wild; Wild; Wild]

let pat_intersects_1 =
  [Wild; PTrue; Wild; Wild; Wild; Wild; Wild; Wild; Wild]

let pat_intersects_3 =
  [Wild; Wild; PTrue; Wild; Wild; Wild; Wild; Wild; Wild]

let pat_intersects_4 =
  [Wild; Wild; Wild; Wild; PTrue; Wild; Wild; Wild; Wild]

let pat_contains =
  [PTrue; Wild; Wild; Wild; Wild; Wild; PFalse; PFalse; Wild]

let pat_within =
  [PTrue; Wild; PFalse; Wild; Wild; PFalse; Wild; Wild; Wild]

let pat_covers_0 = pat_contains
let pat_covers_1 =
  [Wild; PTrue; Wild; Wild; Wild; Wild; PFalse; PFalse; Wild]
let pat_covers_3 =
  [Wild; Wild; PTrue; Wild; Wild; Wild; PFalse; PFalse; Wild]
let pat_covers_4 =
  [Wild; Wild; Wild; Wild; PTrue; Wild; PFalse; PFalse; Wild]

let pat_coveredBy_0 = pat_within
let pat_coveredBy_1 =
  [Wild; Wild; PFalse; PTrue; Wild; Wild; Wild; Wild; Wild]
let pat_coveredBy_3 =
  [Wild; Wild; PFalse; Wild; Wild; PTrue; Wild; Wild; Wild]
let pat_coveredBy_4 =
  [Wild; Wild; PFalse; Wild; PTrue; Wild; Wild; Wild; Wild]

let pat_equals_topo =
  [PTrue; Wild; PFalse; Wild; Wild; PFalse; PFalse; PFalse; PFalse]

let pat_touches_0 =
  [PFalse; PTrue; Wild; Wild; Wild; Wild; Wild; Wild; Wild]

let pat_touches_1 =
  [Wild; Wild; Wild; PFalse; PTrue; Wild; Wild; Wild; Wild]

let pat_touches_3 =
  [Wild; Wild; Wild; Wild; Wild; Wild; PFalse; PTrue; Wild]

let pat_crosses_pl_pa_la =
  [PTrue; Wild; Wild; Wild; PFalse; Wild; Wild; Wild; Wild]

let pat_crosses_lp_ap_al =
  [PTrue; Wild; Wild; Wild; Wild; PTrue; Wild; Wild; Wild]

let pat_crosses_ll =
  [PDim 0; Wild; Wild; Wild; Wild; Wild; Wild; Wild; Wild]

let pat_overlaps_pp_aa =
  [PTrue; Wild; Wild; Wild; PTrue; Wild; Wild; Wild; PTrue]

let pat_overlaps_ll =
  [PDim 1; Wild; Wild; Wild; PTrue; Wild; Wild; Wild; PTrue]

let predicate_holds name cells =
  match String.uppercase_ascii (String.trim name) with
  | "DISJOINT" | "RDISJOINT" ->
      matrix_matches [pat_disjoint] cells
  | "INTERSECTS" | "RINTERSECTS" ->
      matrix_matches [pat_intersects_0; pat_intersects_1; pat_intersects_3; pat_intersects_4] cells
  | "CONTAINS" | "RCONTAINS" ->
      matrix_matches [pat_contains] cells
  | "WITHIN" | "RWITHIN" ->
      matrix_matches [pat_within] cells
  | "COVERS" | "RCOVERS" ->
      matrix_matches [pat_covers_0; pat_covers_1; pat_covers_3; pat_covers_4] cells
  | "COVEREDBY" | "RCOVEREDBY" ->
      matrix_matches [pat_coveredBy_0; pat_coveredBy_1; pat_coveredBy_3; pat_coveredBy_4] cells
  | "EQUALS" | "EQUALSTOPO" | "REQUALSTOPO" ->
      matrix_matches [pat_equals_topo] cells
  | "TOUCHES" | "RTOUCHES" ->
      matrix_matches [pat_touches_0; pat_touches_1; pat_touches_3] cells
  | "CROSSES" | "RCROSSES" ->
      matrix_matches [pat_crosses_pl_pa_la; pat_crosses_lp_ap_al; pat_crosses_ll] cells
  | "OVERLAPS" | "ROVERLAPS" ->
      matrix_matches [pat_overlaps_pp_aa; pat_overlaps_ll] cells
  | _ -> invalid_arg ("relate_matrix: unknown predicate: " ^ name)

(* Pinned 9-char matrices — keep in sync with Coq definitions + vector files. *)
let catalog =
  [ (* line-line witnesses (RelateLineLine.v) *)
    "ll_matrix_disjoint", "FFFFFFFFF";
    "ll_matrix_point_ii", "0FFFFFFFF";
    "ll_matrix_overlap_ii", "1FFF0FFF0";
    (* Romanschek paper pins *)
    "ll_matrix_paper_test6", "FF1FF0102";
    "ll_matrix_paper_test7", "1FFF0FFF2";
    "ll_matrix_paper_test8", "101FF0FF2";
    "ll_matrix_paper_test9", "101F00FF2";
    "ll_matrix_paper_test10", "FF10F0102";
    "ll_matrix_paper_test13", "0F1FF0102";
    (* boundary (RelateBoundary.v) *)
    "ll_matrix_touches_endpoint", "F0FFFFFF2";
    "jts1175_separated_not_disjoint_matrix", "FF10F0102";
    (* area-area (RelateAreaArea.v) *)
    "aa_matrix_disjoint", "FFFFFFFFF";
    "aa_matrix_partial_overlap", "2FFF1FFF2";
    "aa_matrix_contains", "2FFFFFFF2";
    "aa_matrix_touch_vertical", "FFFF1FFF2";
    (* area-line (RelateAreaLine.v) *)
    "al_matrix_segment_interior", "1FFFFFFF2";
    "al_matrix_segment_crosses", "1FFFF0FF2";
    "al_matrix_disjoint", "FFFFFFFFF";
    "al_matrix_boundary_touch", "FFFF0FFF2";
    (* arc / clothoid chord path *)
    "ac_matrix_disjoint", "FFFFFFFFF";
    "ac_matrix_point_ii", "0FFFFFFFF";
    "cl_matrix_disjoint", "FFFFFFFFF";
    "cl_matrix_point_ii", "0FFFFFFFF";
    (* fill API aliases (relate_matrix_fill_vocabulary.txt) *)
    "rect_pair_fill RPR_Disjoint", "FFFFFFFFF";
    "rect_pair_fill RPR_Overlap", "2FFF1FFF2";
    "rect_pair_fill RPR_Contains", "2FFFFFFF2";
    "rect_pair_fill RPR_TouchVert", "FFFF1FFF2";
    "line_pair_fill LPR_Disjoint", "FFFFFFFFF";
    "line_pair_fill LPR_ProperCross", "0FFFFFFFF";
    "line_pair_fill LPR_Share", "0FFFFFFFF";
    "line_pair_fill LPR_CollinearOverlap", "1FFF0FFF0";
    "area_line_fill ALR_Interior", "1FFFFFFF2";
    "area_line_fill ALR_Pierce", "1FFFF0FF2";
    "area_line_fill ALR_Disjoint", "FFFFFFFFF";
    "area_line_fill ALR_BoundaryTouch", "FFFF0FFF2";
    "arc_chord_fill ACR_ChordDisjoint", "FFFFFFFFF";
    "arc_chord_fill ACR_ChordProperCross", "0FFFFFFFF";
    "arc_chord_fill ACR_ChordShare", "0FFFFFFFF";
    "arc_chord_fill ACR_CircleCross", "0FFFFFFFF";
    "arc_analytic_fill AAR_AnalyticCross", "0FFFFFFFF";
    "clothoid_fill CLR_ChordDisjoint", "FFFFFFFFF";
    "clothoid_fill CLR_ChordProperCross", "0FFFFFFFF";
    "clothoid_fill CLR_ChordShare", "0FFFFFFFF";
    (* curve-polygon × point (RelateCurveAreaPoint.v, S12) *)
    "cap_matrix_rect_contains_point", "0FFFFFFF0";
    "cap_matrix_rect_touches_boundary", "FFFFFFF0F";
    "curve_point_fill CPR_StrictInterior", "0FFFFFFF0";
    "curve_point_fill CPR_LeftBoundaryTouch", "FFFFFFF0F";
  ]

let strip_prefix prefix s =
  let plen = String.length prefix in
  if String.length s >= plen && String.sub s 0 plen = prefix then
    String.trim (String.sub s plen (String.length s - plen))
  else s

let normalize_key s =
  let t = String.trim s in
  strip_prefix "FILL " (strip_prefix "COQ " t)

let lookup_matrix key =
  let k = normalize_key key in
  if String.length k = 9 && String.for_all (fun c -> c = 'F' || (c >= '0' && c <= '2')) k then
    k
  else
    match List.assoc_opt k catalog with
    | Some m -> m
    | None -> invalid_arg ("relate_matrix: unknown key: " ^ k)

let resolve_matrix_input key =
  lookup_matrix key

let check_predicate matrix_key predicate =
  let m = lookup_matrix matrix_key in
  predicate_holds predicate (matrix_cells m)

let catalog_entries () = catalog