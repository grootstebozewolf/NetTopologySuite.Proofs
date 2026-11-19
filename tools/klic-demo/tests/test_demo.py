"""Pins every number tools/klic-demo/demo.py prints.

A change in Shapely/GEOS behaviour (a fixed future GEOS, say) shows up here as
a failing test with the new numbers, never as a silent pass: the GEOS version
itself is pinned, and so are the stock answers it gives.

Kinds of assertion, kept apart as in the README:
  * stock_*       TESTED observations of a stock tool on the synthetic inputs
  * verified_*    answers of the Rocq-extracted kernel (each answer is backed
                  by a Qed reflection theorem; the bound is a theorem)
"""
from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import demo  # noqa: E402
import verified_hotpixel as vk  # noqa: E402

PINNED_SHAPELY = "2.2.0"
PINNED_GEOS = "3.14.1"


@pytest.fixture(scope="module")
def res():
    return demo.compute()


# --------------------------------------------------------------------------
# Toolchain pin: a GEOS change must surface as a test change.
# --------------------------------------------------------------------------

def test_pinned_shapely_and_geos_versions(res):
    assert res["shapely_version"] == PINNED_SHAPELY
    assert res["geos_version"] == PINNED_GEOS


def test_report_prints_geos_version(res):
    assert f"Shapely {PINNED_SHAPELY} / GEOS {PINNED_GEOS}" in demo.report(res).splitlines()[0]


# --------------------------------------------------------------------------
# Inputs are the committed synthetic files, regenerated bit-for-bit.
# --------------------------------------------------------------------------

INPUT_SHA256 = {
    "cases/caseA_pairs.wkt": "19e425f8fb1afec0b3fa7d6ecee21c613b909fca780cd7cc5d1bdc7f6c011c5f",
    "cases/caseC.wkt": "b3ff5878b18b328c3864b8c36716544a1b2dec08335dd920bc100be0ee4936b4",
    "data/klic_synthetic_mm.wkt": "61e18693ebc137af8dcece86843ba76488b91607de29637ef50bfc49158093d5",
    "tests/fixtures/synthetic_imkl.xml": "4dea720bd914dda30730924cbd06df0873a9428164fe2aea45c02881dcd3bc3e",
}


HANDOVER_SHA256 = {
    "data/klic_handover_mm.wkt": "4880e52ee9b269281f62fb3fda9bf99b4f043162a28dc72b8c148fe239c001b8",
    "data/klic_handover.geojson": "2f80332c875b78dfa5316fe3b5dccd80111f6c1296adfaf58f91ab5cce151ac7",
}


@pytest.mark.parametrize("rel", sorted(HANDOVER_SHA256))
def test_handover_inputs_unchanged(rel):
    assert hashlib.sha256((ROOT / rel).read_bytes()).hexdigest() == HANDOVER_SHA256[rel]


def test_make_handover_data_regenerates_identical_inputs(tmp_path):
    import shutil
    (tmp_path / "data").mkdir()
    shutil.copy(ROOT / "make_handover_data.py", tmp_path / "make_handover_data.py")
    subprocess.run([sys.executable, "make_handover_data.py"], cwd=tmp_path, check=True, capture_output=True)
    for rel, h in HANDOVER_SHA256.items():
        assert hashlib.sha256((tmp_path / rel).read_bytes()).hexdigest() == h, rel


@pytest.mark.parametrize("rel", sorted(INPUT_SHA256))
def test_committed_inputs_unchanged(rel):
    assert hashlib.sha256((ROOT / rel).read_bytes()).hexdigest() == INPUT_SHA256[rel]


def test_make_data_regenerates_identical_inputs(tmp_path):
    import shutil
    for d in ("cases", "data", "tests/fixtures"):
        (tmp_path / d).mkdir(parents=True)
    shutil.copy(ROOT / "make_data.py", tmp_path / "make_data.py")
    subprocess.run([sys.executable, str(tmp_path / "make_data.py")], check=True, capture_output=True)
    for rel, h in INPUT_SHA256.items():
        assert hashlib.sha256((tmp_path / rel).read_bytes()).hexdigest() == h, rel


def test_all_input_coordinates_are_integer_mm():
    for line in (ROOT / "cases" / "caseA_pairs.wkt").read_text().splitlines()[:50]:
        for g in line.split(";"):
            assert all(v.denominator == 1 for p in vk.coords_from_wkt_text(g) for v in p)


# --------------------------------------------------------------------------
# Cases A and B: the first-build handover scenario (GP-0001, LS-0042, MS-0007)
# --------------------------------------------------------------------------

def test_stock_case_a_ls0042(res):
    s = res["caseA"]["stock"]
    assert s["intersects"] is True
    assert s["covers"] is False and s["within"] is False
    assert s["points_on_cable"] == [False, False]
    assert s["points_on_boundary"] == [False, False]
    assert s["sr_wkt"] == "LINESTRING (155000618 463005829, 155013698 463004978)"
    assert s["sr_covers"] is False


def test_stock_case_a_geos_points_are_picometres_off(res):
    assert [round(e, 1) for e in res["caseA"]["geos_point_error_pm"]] == [7.8, 11.0]


def test_verified_case_a_nodes(res):
    a = res["caseA"]
    assert a["snapped_nodes"] == [["155013698", "463004978"], ["155000618", "463005829"]]
    assert [[round(float(Fraction(v)), 6) for v in d] for d in a["snap_disp_mm"]] == \
        [[0.137881, 0.436983], [0.242213, 0.295857]]
    assert all(Fraction(v) <= Fraction(1, 2) for d in a["snap_disp_mm"] for v in d)
    assert a["passes_cable_and_edge"] == [[True, True], [True, True]]


def test_tested_case_a_noded_arrangement(res):
    a = res["caseA"]
    assert a["tested_inside_part_wkt"] == "LINESTRING (155000618 463005829, 155013698 463004978)"
    assert a["tested_noded_dig_valid"] is True
    assert a["tested_noded_dig_covers_inside"] is True
    assert a["tested_inside_equals_geos_sr"] is True


def test_stock_case_b_ms0007_three_calls(res):
    s = res["caseB"]["stock"]
    assert s["intersects"] is False
    assert s["intersection_wkt"] == "LINESTRING EMPTY"
    assert round(s["distance_mm"], 6) == 0.3
    assert s["sr_intersection_wkt"] == "POINT (155014211 463008230)"
    assert s["reduced_intersects"] is False


def test_verified_case_b_vertex_pixel(res):
    b = res["caseB"]
    assert b["vertex_passes"] == [False, False, True, False, False]
    assert b["hot_pixel_centre"] == [["155014211", "463008230"]]
    assert all(Fraction(v) <= Fraction(1, 2) for d in b["vertex_snap_disp_mm"] for v in d)
    assert [round(g, 6) for g in b["vertex_gap_mm_float"]] == [0.3]


def test_case_b_metres_at_scale_1000(res):
    mm, m = res["caseB"], res["caseB_metres_s1000"]
    assert m["vertex_passes"] == mm["vertex_passes"]
    assert [[Fraction(v) * 1000 for v in c] for c in m["hot_pixel_centre"]] == \
        [[Fraction(v) for v in c] for c in mm["hot_pixel_centre"]]


# --------------------------------------------------------------------------
# Case A*: 3000 random pairs
# --------------------------------------------------------------------------

def test_stock_random_a_covers_false(res):
    a = res["randomA"]
    assert a["pairs"] == 3000
    assert a["stock_covers_false"] == 2235


def test_stock_random_a_geos_node_error_is_picometres(res):
    pm = res["randomA"]["geos_max_node_error_pm"]
    assert 0 < pm < 100          # off by picometres, not millimetres
    assert round(pm, 1) == 29.8


def test_verified_random_a_nodes_and_bound(res):
    a = res["randomA"]
    assert a["verified_nodes"] == 6000
    assert a["verified_max_disp_mm"] == "57465962/114960375"
    assert Fraction(a["verified_max_disp_mm"]) <= Fraction(1, 2)
    assert a["verified_bound_mm"] == "1/2"
    assert a["verified_bound_holds"] is True


def test_verified_random_a_cable_and_edge_share_every_node_pixel(res):
    assert res["randomA"]["verified_hotpixel_both"] == 6000


# --------------------------------------------------------------------------
# Case C: corner clip
# --------------------------------------------------------------------------

def test_stock_case_c_three_calls_disagree(res):
    s = res["caseC"]["stock"]
    assert s["intersects"] is True
    assert s["relate"] == "1F20F1102"
    assert s["relate_interior_interior"] == "1"
    assert s["covers"] is False
    assert s["intersection_wkt"] == (
        "LINESTRING (155523520.69981417 463287348.8600093, 155523520.7200218 463287349.6004359)")
    assert round(s["intersection_length_mm"], 6) == 0.740702


def test_verified_case_c_corner_pixel(res):
    b = res["caseC"]
    assert b["corner_passes"] == [False, True, False, False]
    assert b["corner_hit_xy"] == [["155523521", "463287349"]]


def test_verified_case_c_nodes_snaps_and_displacements(res):
    b = res["caseC"]
    assert b["exact_nodes"] == [["11217446999321266/72127013", "66831065267922857/144254026"],
                                ["2804061550918826/18029823", "5568659274289987/12019882"]]
    assert b["snapped_nodes"] == [["155523521", "463287349"], ["155523521", "463287350"]]
    assert b["snapped_on_corner"] == [True, False]
    assert b["snap_disp_mm"] == [["21651507/72127013", "20194217/144254026"],
                                 ["5047957/18029823", "4802713/12019882"]]
    assert b["max_disp_mm"] == "4802713/12019882"
    assert Fraction(b["max_disp_mm"]) <= Fraction(1, 2)


def test_case_c_clip_depth_is_0_3_mm():
    """The exact distance of the corner from the cable line (TESTED, Fraction)."""
    d, c = (ROOT / "cases" / "caseC.wkt").read_text().strip().split(";")
    v = vk.coords_from_wkt_text(d)[1]
    (x0, y0), (x1, y1) = vk.coords_from_wkt_text(c)
    cross = (x1 - x0) * (v[1] - y0) - (y1 - y0) * (v[0] - x0)
    d2 = cross * cross / ((x1 - x0) ** 2 + (y1 - y0) ** 2)
    assert Fraction(29, 100) ** 2 <= d2 <= Fraction(31, 100) ** 2


# --------------------------------------------------------------------------
# Unit scale: metres at s = 1000 give the same nodes (exactly /1000)
# --------------------------------------------------------------------------

def test_metres_at_scale_1000_match_millimetres(res):
    mm, m = res["caseC"], res["caseC_metres_s1000"]
    assert m["corner_passes"] == mm["corner_passes"]
    k = Fraction(1, 1000)
    for (a, b), (c, d) in zip(mm["snapped_nodes"], m["snapped_nodes"]):
        assert Fraction(a) * k == Fraction(c) and Fraction(b) * k == Fraction(d)
    for (a, b), (c, d) in zip(mm["exact_nodes"], m["exact_nodes"]):
        assert Fraction(a) * k == Fraction(c) and Fraction(b) * k == Fraction(d)
    assert m["snap_disp_mm"] == mm["snap_disp_mm"]
    assert m["max_disp_mm"] == mm["max_disp_mm"]


def test_metre_text_is_not_a_double(res):
    h = res["metre_float_hazard"]
    assert h["x_m_exact"] == "155523.521"
    assert h["double_exact"] is False
    assert round(h["x_m_double_error_pm"], 3) == 7.916


def test_integer_mm_rd_coordinates_are_doubles():
    """TESTED twin of the Qed lemma rd_mm_grid_representable_b64."""
    for v in (155_523_521, 463_287_349, 629_000_000, 10**9):
        assert Fraction(float(v)) == v


# --------------------------------------------------------------------------
# Recorded stock run (JTS, NTS, PostGIS, Shapely), pinned
# --------------------------------------------------------------------------

EXPECTED_STOCK = {
    # tool: (version, A* covers=False, A covers(∩), C covers(∩))
    "Shapely": ("Shapely 2.2.0 / GEOS 3.14.1", 2235, False, False),
    "JTS": ("jts-core 1.20.0", 559, True, True),
    "NTS": ("NetTopologySuite 2.6.0 (compatible with JTS 1.20.0)", 559, True, True),
    "PostGIS": ("PostGIS 3.5.2 / GEOS 3.9.0-CAPI-1.16.2", 2235, False, False),
}


def test_recorded_stock_results(res):
    st = res["stock_recorded"]
    assert st is not None, "run python tools/klic-demo/stock/run_all.py"
    got = {r["tool"]: r for r in st["results"]}
    assert set(got) == set(EXPECTED_STOCK)
    for tool, (ver, a_false, a_cov, c_cov) in EXPECTED_STOCK.items():
        r = got[tool]
        assert r["status"] == "ok"
        assert r["version"] == ver
        assert r["randomA"] == {"pairs": 3000, "nonempty": 3000, "covers_false": a_false}
        assert r["caseA"] == {"covers": a_cov, "within": a_cov, "points_on_cable": [False, False],
                              "points_on_boundary": [False, False], "sr_covers": False}
        # case B: the three-way split reproduces in every tool
        assert r["caseB"]["intersects"] is False and r["caseB"]["intersection_empty"] is True
        assert r["caseB"]["sr_intersection"].replace("POINT(", "POINT (") == "POINT (155014211 463008230)"
        assert r["caseB"]["reduced_intersects"] is False
        assert (r["caseC"]["intersects"], r["caseC"]["relate"], r["caseC"]["covers"]) == (True, "1F20F1102", c_cov)


def test_live_shapely_matches_recorded(res):
    sys.path.insert(0, str(ROOT / "stock"))
    import stock_shapely
    live = stock_shapely.run(str(ROOT / "cases" / "caseA_pairs.wkt"), str(ROOT / "cases" / "caseC.wkt"),
                             str(ROOT / "data" / "klic_handover_mm.wkt"))
    rec = {r["tool"]: r for r in res["stock_recorded"]["results"]}["Shapely"]
    for k in ("randomA", "caseA", "caseB", "caseC"):
        assert live[k] == rec[k], k


# --------------------------------------------------------------------------
# Real data: 24 public Kadaster example deliveries (recorded run; the data
# itself is not in the repo -- real_data/run_kadaster_examples.py fetches it)
# --------------------------------------------------------------------------

def test_real_data_recorded_summary(res):
    R = res["real"]
    assert R["source"].startswith("github.com/kadaster/klic-win@5e83c0e42bbd6ee50c401cc1ef5759446c8fe147")
    assert (R["deliveries"], R["lines"]) == (24, 43962)
    assert R["geos"] == ["Shapely 2.2.0 / GEOS 3.14.1"]
    assert R["verified_dig_vertex_hotpixel_passes"] == 0
    assert R["verified_exact_nodes"] == 1879
    assert R["verified_max_disp_m"] == "193/386120"
    assert Fraction(R["verified_max_disp_m"]) <= Fraction(1, 2000)
    assert R["verified_bound_holds"] is True
    assert R["stock_covers_false"] == 903
    assert R["deliveries_with_covers_false"] == 24


def test_real_data_recorded_stock_tools(res):
    got = {r["tool"]: (r["version"], r["randomA"]) for r in res["stock_recorded_real"]["results"]}
    assert got == {
        "Shapely": ("Shapely 2.2.0 / GEOS 3.14.1", {"pairs": 43962, "nonempty": 43962, "covers_false": 903}),
        "JTS": ("jts-core 1.20.0", {"pairs": 43962, "nonempty": 43962, "covers_false": 208}),
        "NTS": ("NetTopologySuite 2.6.0 (compatible with JTS 1.20.0)",
                {"pairs": 43962, "nonempty": 43962, "covers_false": 208}),
        "PostGIS": ("PostGIS 3.5.2 / GEOS 3.9.0-CAPI-1.16.2",
                    {"pairs": 43962, "nonempty": 43932, "covers_false": 933}),
    }
