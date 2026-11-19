#!/usr/bin/env python3
"""Run the stock-tool predicates on every available tool and record the run.

  python tools/klic-demo/stock/run_all.py [--only shapely,jts,nts,postgis]

Writes tools/klic-demo/results/stock_results.json: one entry per tool with the
version string the tool itself printed, plus the UTC time of the run.  A tool
that cannot run here (no java / dotnet / docker) is recorded as
{"status": "not run", "reason": ...} -- never as a result.

Toolchain pins: JTS jts-core 1.20.0 (stock/jts/pom.xml), NetTopologySuite
2.6.0 (stock/nts/KlicStock.csproj), PostGIS image postgis/postgis:17-3.5
(override with POSTGIS_IMAGE), Shapely 2.2.0 (requirements.txt).
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
A = ROOT / "cases" / "caseA_pairs.wkt"
B = ROOT / "cases" / "caseB.wkt"
OUT = ROOT / "results" / "stock_results.json"
JTS_VERSION = "1.20.0"


def _json_tail(stdout: str) -> dict:
    for line in reversed(stdout.strip().splitlines()):
        line = line.strip()
        if line.startswith("{"):
            return json.loads(line)
    raise RuntimeError("no JSON line in tool output:\n" + stdout[-2000:])


def run_shapely() -> dict:
    p = subprocess.run([sys.executable, str(HERE / "stock_shapely.py"), str(A), str(B)],
                       capture_output=True, text=True, check=True)
    return _json_tail(p.stdout)


def run_jts() -> dict:
    if not shutil.which("java"):
        return {"tool": "JTS", "status": "not run", "reason": "java not found"}
    jar = HERE / "jts" / "lib" / f"jts-core-{JTS_VERSION}.jar"
    if not jar.exists():
        if not shutil.which("mvn"):
            return {"tool": "JTS", "status": "not run", "reason": "mvn not found to fetch jts-core"}
        subprocess.run(["mvn", "-q", "dependency:copy-dependencies", "-DoutputDirectory=lib"],
                       cwd=HERE / "jts", check=True, capture_output=True)
    p = subprocess.run(["java", "-cp", str(jar), str(HERE / "jts" / "KlicStock.java"), str(A), str(B)],
                       capture_output=True, text=True, check=True)
    return _json_tail(p.stdout)


def run_nts() -> dict:
    if not shutil.which("dotnet"):
        return {"tool": "NTS", "status": "not run", "reason": "dotnet not found"}
    p = subprocess.run(["dotnet", "run", "-c", "Release", "--project", str(HERE / "nts"), "--", str(A), str(B)],
                       capture_output=True, text=True, check=True)
    return _json_tail(p.stdout)


def run_postgis() -> dict:
    if not shutil.which("docker"):
        return {"tool": "PostGIS", "status": "not run", "reason": "docker not found"}
    p = subprocess.run(["bash", str(HERE / "postgis" / "run.sh"), str(A), str(B)],
                       capture_output=True, text=True)
    if p.returncode != 0:
        return {"tool": "PostGIS", "status": "not run", "reason": "docker run failed: " + p.stderr.strip()[-300:]}
    r = _json_tail(p.stdout)
    return r


RUNNERS = {"shapely": run_shapely, "jts": run_jts, "nts": run_nts, "postgis": run_postgis}


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", default=",".join(RUNNERS))
    ap.add_argument("--out", default=str(OUT))
    ap.add_argument("--case-a", default=None, help="alternative case-A pairs file (dig;line per row)")
    args = ap.parse_args(argv)
    global A
    if args.case_a:
        A = Path(args.case_a).resolve()
    results = []
    for name in args.only.split(","):
        r = RUNNERS[name]()
        r.setdefault("status", "ok")
        results.append(r)
        print(json.dumps(r), flush=True)
    doc = {"run_utc": dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
           "inputs": {"caseA": A.name, "caseB": B.name},
           "results": results}
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    Path(args.out).write_text(json.dumps(doc, indent=2) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
