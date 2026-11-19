"""imkl_loader.py on the SYNTHETIC IMKL-shaped fixture (not Kadaster data)."""
from __future__ import annotations

import json
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import imkl_loader  # noqa: E402

FIXTURE = ROOT / "tests" / "fixtures" / "synthetic_imkl.xml"


def test_load_reads_dig_polygon_and_lines_exactly():
    d = imkl_loader.load_imkl(FIXTURE, line_feature_regex="")
    assert d["srs"] == ["urn:ogc:def:crs:EPSG::28992"]
    assert len(d["digs"]) == 1 and len(d["lines"]) == 8
    ring = d["digs"][0]["ring"]
    assert ring[1] == (Fraction("155523.521"), Fraction("463287.349"))  # exact decimal, no float
    assert {ln["feature"] for ln in d["lines"]} == {"ElectricityCable"}


def test_analyse_metres_on_1mm_grid():
    res = imkl_loader.analyse(imkl_loader.load_imkl(FIXTURE, line_feature_regex=""), Fraction(1, 1000), show_locations=True)
    (r,) = res["per_dig"]
    assert r["lines_touching_dig"] == 8
    assert r["hotpixel_vertex_passes"] == 1
    assert r["hotpixel_cases"] == [{"feature": "ElectricityCable",
                                    "vertex_rd_m": ["155523521/1000", "463287349/1000"]}]
    assert r["exact_nodes"] == 16
    assert r["max_snap_disp_m"] == "176643353/359996429000"
    assert r["bound_m"] == "1/2000" and r["bound_holds"] is True
    # TESTED, stock Shapely/GEOS on metre doubles (pinned like demo numbers)
    assert (res["shapely"], res["geos"]) == ("2.2.0", "3.14.1")
    assert r["stock_covers_false"] == 7
    assert r["stock_intersects_relate_covers_disagree"] == 7


def test_cli_default_report_has_no_coordinates():
    out = subprocess.run([sys.executable, str(ROOT / "imkl_loader.py"), str(FIXTURE),
                          "--line-feature-regex", ""],
                         capture_output=True, text=True, check=True).stdout
    rep = json.loads(out)
    assert "hotpixel_cases" not in rep["per_dig"][0]
    assert "155523" not in out


def test_dimension_3_poslist(tmp_path):
    f = tmp_path / "d3.xml"
    f.write_text("""<?xml version="1.0"?>
<gml:FeatureCollection xmlns:gml="http://www.opengis.net/gml/3.2" xmlns:imkl="urn:x">
 <gml:featureMember><imkl:Graafpolygoon><gml:Polygon srsDimension="3"><gml:exterior><gml:LinearRing>
  <gml:posList>0 0 1 10 0 1 10 10 1 0 10 1 0 0 1</gml:posList></gml:LinearRing></gml:exterior></gml:Polygon>
 </imkl:Graafpolygoon></gml:featureMember>
 <gml:featureMember><imkl:Kabel><gml:LineString srsDimension="3">
  <gml:posList>-1 5.0004 0 11 5.0004 0</gml:posList></gml:LineString></imkl:Kabel></gml:featureMember>
</gml:FeatureCollection>""")
    d = imkl_loader.load_imkl(f, line_feature_regex="kabel")
    assert d["digs"][0]["ring"][2] == (10, 10)
    assert d["lines"][0]["pts"] == [(-1, Fraction("5.0004")), (11, Fraction("5.0004"))]
    assert d["lines"][0]["feature"] == "Kabel"
