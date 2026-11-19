#!/usr/bin/env python3
"""Run the hot-pixel analysis on Kadaster's PUBLIC example KLIC deliveries.

Source: https://github.com/kadaster/klic-win  (no licence file stated; the
files are not copied into this repo -- this script downloads them).
Pinned commit: KLIC_WIN_COMMIT below; folder "Uitleveren/Voorbeelden IMKL v2.0"
(24 Levering_*.zip, KLIC test requests from 2022, IMKL 2.0).

  python tools/klic-demo/real_data/run_kadaster_examples.py [--src <dir of Levering_*.zip>]

Writes tools/klic-demo/results/kadaster_examples.json.  Graafmelding (G/C)
deliveries carry a imkl:Graafpolygoon; orientation requests (O) an
imkl:Orientatiepolygoon -- both are analysed as the dig polygon.
"""
from __future__ import annotations

import argparse
import io
import json
import sys
import tempfile
import urllib.parse
import urllib.request
import zipfile
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))
import imkl_loader  # noqa: E402

KLIC_WIN_COMMIT = "5e83c0e42bbd6ee50c401cc1ef5759446c8fe147"
FOLDER = "Uitleveren/Voorbeelden IMKL v2.0"
ZIPS = """22C001966_3 22C001967_3 22C001969_3 22C001970_3 22C002011_2 22G003174_1 22G003175_1
22G003176_1 22G003178_1 22G003179_1 22G003180_1 22G003181_1 22G003182_1 22G003246_1 22G003247_1
22O000512_1 22O000513_1 22O000514_1 22O000515_1 22O000517_1 22O000518_1 22O000522_1 22O000525_1
22O000526_1""".split()


def fetch(name: str) -> bytes:
    url = (f"https://raw.githubusercontent.com/kadaster/klic-win/{KLIC_WIN_COMMIT}/"
           + urllib.parse.quote(f"{FOLDER}/Levering_{name}.zip"))
    with urllib.request.urlopen(url, timeout=120) as r:
        return r.read()


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--src", default=None, help="local folder holding Levering_*.zip")
    ap.add_argument("--out", default=str(ROOT / "results" / "kadaster_examples.json"))
    a = ap.parse_args(argv)
    rows = []
    for name in ZIPS:
        data = (Path(a.src) / f"Levering_{name}.zip").read_bytes() if a.src else fetch(name)
        with tempfile.TemporaryDirectory() as td:
            with zipfile.ZipFile(io.BytesIO(data)) as z:
                for m in z.namelist():
                    if m.endswith(".xml") and "GI_gebiedsinformatielevering" in m:
                        z.extract(m, td)
            d = imkl_loader.load_imkl(td, dig_regex="graafpolygoon|orientatiepolygoon")
            res = imkl_loader.analyse(d, Fraction(1, 1000), show_locations=True)
        res["delivery"] = name
        rows.append(res)
        tot = sum(r["hotpixel_vertex_passes"] for r in res["per_dig"])
        cf = sum(r["stock_covers_false"] for r in res["per_dig"])
        print(f"{name}: digs={res['dig_polygons']} lines={res['lines']} "
              f"hotpixel_vertex_passes={tot} stock_covers_false={cf}", flush=True)
    doc = {"source": f"github.com/kadaster/klic-win@{KLIC_WIN_COMMIT}/{FOLDER}",
           "grid": "1 mm (s = 1000 on metres)", "deliveries": rows}
    Path(a.out).write_text(json.dumps(doc, indent=2) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
