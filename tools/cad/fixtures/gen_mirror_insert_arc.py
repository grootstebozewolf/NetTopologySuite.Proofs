"""Write the mirrored-INSERT arc fixture and its ezdxf flatten reference.

    python3 tools/cad/fixtures/gen_mirror_insert_arc.py

R2000. A block arc inserted with xscale -1 (a reflection). ezdxf's
fixed-metadata flag freezes GUIDs and the written-by timestamp so a
second run is the same bytes.
"""

from __future__ import annotations

import io
import json
from pathlib import Path

import ezdxf
from ezdxf.math import ConstructionArc, Vec3

HERE = Path(__file__).resolve().parent
DXF_PATH = HERE / "mirror_insert_arc.dxf"
JSON_PATH = HERE / "mirror_insert_arc.flatten.json"

BLOCK = "ARCBLK"
DISTANCE = 0.01
CENTER = (1.0, 0.0)
RADIUS = 2.0
START = 10.0
END = 100.0
INSERT = (4.0, 2.0)
XSCALE = -1.0
YSCALE = 1.0


def _drawing() -> ezdxf.document.Drawing:
    doc = ezdxf.new("R2000")
    doc.header["$INSUNITS"] = 6
    doc.header["$AUNITS"] = 0
    doc.header["$ANGDIR"] = 0
    doc.header["$ANGBASE"] = 0.0
    block = doc.blocks.new(BLOCK)
    block.add_arc(CENTER, radius=RADIUS, start_angle=START, end_angle=END)
    doc.modelspace().add_blockref(
        BLOCK,
        INSERT,
        dxfattribs={"xscale": XSCALE, "yscale": YSCALE, "rotation": 0.0},
    )
    return doc


def _placed_points(doc: ezdxf.document.Drawing) -> list[list[float]]:
    """WCS points of the inserted arc. Flattening is in the arc OCS."""
    insert = next(entity for entity in doc.modelspace() if entity.dxftype() == "INSERT")
    arc = next(entity for entity in insert.virtual_entities() if entity.dxftype() == "ARC")
    ocs = arc.ocs()
    tool = ConstructionArc(
        (arc.dxf.center.x, arc.dxf.center.y),
        arc.dxf.radius,
        arc.dxf.start_angle,
        arc.dxf.end_angle,
    )
    points = []
    for point in tool.flattening(DISTANCE):
        world = ocs.to_wcs(Vec3(point.x, point.y, 0.0))
        points.append([float(world.x), float(world.y)])
    return points


def _reference(doc: ezdxf.document.Drawing) -> bytes:
    payload = {
        "block": BLOCK,
        "center": [CENTER[0], CENTER[1]],
        "endAngle": END,
        "ezdxf": ezdxf.__version__,
        "flattening": {"distance": DISTANCE},
        "insert": [INSERT[0], INSERT[1]],
        "points": _placed_points(doc),
        "radius": RADIUS,
        "sagitta": DISTANCE,
        "startAngle": START,
        "xscale": XSCALE,
        "yscale": YSCALE,
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
