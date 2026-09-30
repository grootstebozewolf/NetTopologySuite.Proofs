"""Write the mixed-bulge LWPOLYLINE fixture and its ezdxf flatten reference.

    python3 tools/cad/fixtures/gen_lwpolyline_mixed_bulges.py

R2000. One open LWPOLYLINE (zero, positive, negative bulge) and one closed
LWPOLYLINE. ezdxf's fixed-metadata flag freezes GUIDs and the written-by
timestamp so a second run is the same bytes.
"""

from __future__ import annotations

import io
import json
from pathlib import Path

import ezdxf
from ezdxf.path import make_path

HERE = Path(__file__).resolve().parent
DXF_PATH = HERE / "lwpolyline_mixed_bulges.dxf"
JSON_PATH = HERE / "lwpolyline_mixed_bulges.flatten.json"

# Path.flattening distance: max gap from the curve to a chord midpoint.
DISTANCE = 0.01
SEGMENTS = 4

OPEN = [(0.0, 0.0, 0.0), (4.0, 0.0, 1.0), (4.0, 2.0, -0.5), (0.0, 2.0, 0.0)]
CLOSED = [(0.0, 0.0, 0.0), (3.0, 0.0, 0.4), (3.0, 3.0, -1.0), (0.0, 3.0, 0.0)]


def _drawing() -> ezdxf.document.Drawing:
    doc = ezdxf.new("R2000")
    doc.header["$INSUNITS"] = 6
    doc.header["$AUNITS"] = 0
    doc.header["$ANGDIR"] = 0
    doc.header["$ANGBASE"] = 0.0
    msp = doc.modelspace()
    msp.add_lwpolyline(OPEN, format="xyb")
    msp.add_lwpolyline(CLOSED, format="xyb", close=True)
    return doc


def _flatten_bulge(start: tuple[float, float], end: tuple[float, float], bulge: float) -> list[list[float]]:
    tmp = ezdxf.new("R2000")
    entity = tmp.modelspace().add_lwpolyline(
        [(start[0], start[1], bulge), (end[0], end[1], 0.0)],
        format="xyb",
    )
    return [[float(p.x), float(p.y)] for p in make_path(entity).flattening(DISTANCE, SEGMENTS)]


def _reference(doc: ezdxf.document.Drawing) -> bytes:
    polylines = []
    for entity in doc.modelspace():
        raw = [(float(x), float(y), float(b)) for x, y, b in entity.get_points("xyb")]
        closed = bool(entity.closed)
        span = len(raw) if closed else len(raw) - 1
        arcs = []
        for i in range(span):
            x0, y0, bulge = raw[i]
            x1, y1, _ = raw[(i + 1) % len(raw)]
            if abs(bulge) <= 1e-9:
                continue
            arcs.append(
                {
                    "bulge": bulge,
                    "points": _flatten_bulge((x0, y0), (x1, y1), bulge),
                }
            )
        polylines.append({"closed": closed, "arcs": arcs})
    payload = {
        "ezdxf": ezdxf.__version__,
        "flattening": {"distance": DISTANCE, "segments": SEGMENTS},
        "polylines": polylines,
        "sagitta": DISTANCE,
    }
    text = json.dumps(payload, allow_nan=False, separators=(",", ":"), sort_keys=True)
    return (text + "\n").encode("utf-8")


def render() -> tuple[bytes, bytes]:
    previous = ezdxf.options.write_fixed_meta_data_for_testing
    ezdxf.options.write_fixed_meta_data_for_testing = True
    try:
        stream = io.StringIO()
        _drawing().write(stream)
        dxf = stream.getvalue().encode("utf-8")
    finally:
        ezdxf.options.write_fixed_meta_data_for_testing = previous
    loaded = ezdxf.read(io.StringIO(dxf.decode("utf-8")))
    return dxf, _reference(loaded)


def main() -> None:
    dxf, ref = render()
    DXF_PATH.write_bytes(dxf)
    JSON_PATH.write_bytes(ref)


if __name__ == "__main__":
    main()
