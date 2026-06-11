open Relate_matrix

let assert_eq msg got exp =
  if got <> exp then (
    Printf.eprintf "FAIL %s: got %S exp %S\n" msg got exp;
    exit 1)

let assert_bool msg got exp =
  if got <> exp then (
    Printf.eprintf "FAIL %s: got %b exp %b\n" msg got exp;
    exit 1)

let assert_matrix key exp =
  assert_eq ("lookup " ^ key) (lookup_matrix key) exp

let assert_pred key pred exp =
  assert_bool (Printf.sprintf "predicate %s %s" key pred)
    (check_predicate key pred) exp

let () =
  (* catalog entries resolve to 9-char row-major matrices *)
  List.iter
    (fun (k, m) ->
      if String.length m <> 9 then (
        Printf.eprintf "FAIL catalog %s: length %d\n" k (String.length m);
        exit 1))
    catalog;

  (* Romanschek line-line pins (de9im_line_line_vectors.txt) *)
  assert_matrix "ll_matrix_paper_test6" "FF1FF0102";
  assert_matrix "ll_matrix_paper_test7" "1FFF0FFF2";
  assert_matrix "ll_matrix_paper_test10" "FF10F0102";
  assert_matrix "ll_matrix_paper_test13" "0F1FF0102";
  assert_matrix "COQ ll_matrix_paper_test13" "0F1FF0102";

  (* S2 witnesses + fill aliases *)
  assert_matrix "ll_matrix_disjoint" "FFFFFFFFF";
  assert_matrix "ll_matrix_point_ii" "0FFFFFFFF";
  assert_matrix "line_pair_fill LPR_ProperCross" "0FFFFFFFF";
  assert_matrix "FILL line_pair_fill LPR_CollinearOverlap" "1FFF0FFF0";

  (* area-area / area-line (Coq witness definitions) *)
  assert_matrix "aa_matrix_partial_overlap" "2FFF1FFF2";
  assert_matrix "aa_matrix_contains" "2FFFFFFF2";
  assert_matrix "aa_matrix_touch_vertical" "FFFF1FFF2";
  assert_matrix "rect_pair_fill RPR_Overlap" "2FFF1FFF2";
  assert_matrix "al_matrix_segment_interior" "1FFFFFFF2";
  assert_matrix "area_line_fill ALR_Interior" "1FFFFFFF2";
  assert_matrix "al_matrix_boundary_touch" "FFFF0FFF2";

  (* raw 9-char passthrough *)
  assert_matrix "1FFFF0FF2" "1FFFF0FF2";

  (* predicate pins — Romanschek test 10 / JTS#1175 class *)
  assert_pred "ll_matrix_paper_test10" "Intersects" true;
  assert_pred "ll_matrix_paper_test10" "Disjoint" false;
  assert_pred "jts1175_separated_not_disjoint_matrix" "RIntersects" true;
  assert_pred "jts1175_separated_not_disjoint_matrix" "RDisjoint" false;

  (* test 13 crosses; test 6 intersects but not crosses_ll *)
  assert_pred "ll_matrix_paper_test13" "Crosses" true;
  assert_pred "ll_matrix_paper_test6" "Intersects" true;
  assert_pred "ll_matrix_paper_test6" "Crosses" false;

  (* area-area regimes *)
  assert_pred "aa_matrix_partial_overlap" "Overlaps" true;
  assert_pred "aa_matrix_contains" "Contains" true;
  assert_pred "aa_matrix_touch_vertical" "Touches" true;
  assert_pred "aa_matrix_disjoint" "Disjoint" true;

  (* area-line regimes *)
  assert_pred "al_matrix_segment_crosses" "Crosses" true;
  assert_pred "al_matrix_boundary_touch" "Touches" true;

  (* S12 curve-polygon × point *)
  assert_matrix "cap_matrix_rect_contains_point" "0FFFFFFF0";
  assert_matrix "curve_point_fill CPR_StrictInterior" "0FFFFFFF0";
  assert_matrix "cap_matrix_rect_touches_boundary" "FFFFFFF0F";
  assert_pred "cap_matrix_rect_contains_point" "Contains" true;
  assert_pred "cap_matrix_rect_touches_boundary" "Touches" true;

  print_endline "OK: relate_matrix catalog + predicate pins"