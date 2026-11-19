"""Live re-runs of the JTS, NTS and PostGIS stock checks, compared with the
recorded run in results/stock_results.json.  Each test skips (with the
reason) when its toolchain is absent; it never fabricates a result.
Set KLIC_LIVE_STOCK=0 to skip all of them."""
from __future__ import annotations

import json
import os
import shutil
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "stock"))
import run_all  # noqa: E402

RECORDED = {r["tool"]: r for r in json.loads((ROOT / "results" / "stock_results.json").read_text())["results"]}
LIVE = os.environ.get("KLIC_LIVE_STOCK", "1") != "0"


def _same(live, tool):
    rec = RECORDED[tool]
    assert live.get("status", "ok") == "ok", live
    assert live["version"] == rec["version"]
    assert live["caseA"] == rec["caseA"]
    for k in ("intersects", "relate", "covers"):
        assert live["caseB"][k] == rec["caseB"][k]


@pytest.mark.skipif(not LIVE or not shutil.which("java"), reason="java not available")
def test_jts_live():
    _same(run_all.run_jts(), "JTS")


@pytest.mark.skipif(not LIVE or not shutil.which("dotnet"), reason="dotnet not available")
def test_nts_live():
    _same(run_all.run_nts(), "NTS")


@pytest.mark.skipif(not LIVE or not shutil.which("docker"), reason="docker not available")
def test_postgis_live():
    r = run_all.run_postgis()
    if r.get("status") == "not run":
        pytest.skip(r["reason"])
    _same(r, "PostGIS")
