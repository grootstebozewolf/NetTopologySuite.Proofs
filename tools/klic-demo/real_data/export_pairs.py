#!/usr/bin/env python3
"""Write (dig polygon; utility line) pairs of the Kadaster example deliveries
as case-A WKT rows, for stock/run_all.py --case-a.  Only lines that
intersect the polygon are written.  The output is derived from third-party
data without a stated licence: keep it out of the repo (default: a temp path).

  python real_data/export_pairs.py <dir with Levering_* subdirs or zips> <out.wkt>
"""
from __future__ import annotations

import io
import sys
import tempfile
import zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import imkl_loader  # noqa: E402
from shapely.geometry import LineString, Polygon  # noqa: E402


def wkt_pts(pts):
    return ", ".join(f"{float(x)!r} {float(y)!r}" for x, y in pts)


def main(src, out):
    n = 0
    with open(out, "w") as f:
        for item in sorted(Path(src).iterdir()):
            with tempfile.TemporaryDirectory() as td:
                if item.suffix == ".zip":
                    with zipfile.ZipFile(item) as z:
                        for m in z.namelist():
                            if m.endswith(".xml") and "GI_gebiedsinformatielevering" in m:
                                z.extract(m, td)
                    d = imkl_loader.load_imkl(td, dig_regex="graafpolygoon|orientatiepolygoon")
                else:
                    d = imkl_loader.load_imkl(item, dig_regex="graafpolygoon|orientatiepolygoon")
            for dig in d["digs"]:
                ring = dig["ring"]
                P = Polygon([(float(x), float(y)) for x, y in ring])
                pw = f"POLYGON (({wkt_pts(ring)}))"
                for ln in d["lines"]:
                    if LineString([(float(x), float(y)) for x, y in ln["pts"]]).intersects(P):
                        f.write(f"{pw};LINESTRING ({wkt_pts(ln['pts'])})\n")
                        n += 1
    print(f"{n} pairs -> {out}")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
