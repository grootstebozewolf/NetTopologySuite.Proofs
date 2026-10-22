"""Locked IFC4.3 clothoid alignment segment.

IfcOpenShell reads the file as a reference oracle. It is not vendored.
The bytes below are the fixture; two writes match.
"""

from __future__ import annotations

import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
IFC_PATH = HERE / "ifc_clothoid.ifc"
JSON_PATH = HERE / "ifc_clothoid.json"

# A^2 = R*L = 100*25, so the clothoid constant is 50.
IFC_TEXT = """ISO-10303-21;
HEADER;
FILE_DESCRIPTION(('clothoid alignment segment'),'2;1');
FILE_NAME('ifc_clothoid.ifc','2000-01-01T00:00:00',(''),(''),'IfcOpenShell 0.8.5','carrier-fixture','none');
FILE_SCHEMA(('IFC4X3_ADD2'));
ENDSEC;
DATA;
#1=IFCCARTESIANPOINT((0.,0.));
#2=IFCALIGNMENTHORIZONTALSEGMENT($,$,#1,0.,$,100.,25.,$,.CLOTHOID.);
#3=IFCCARTESIANPOINT((0.,0.));
#4=IFCDIRECTION((1.,0.));
#5=IFCAXIS2PLACEMENT2D(#3,#4);
#6=IFCCLOTHOID(#5,50.);
#7=IFCALIGNMENTSEGMENT('0000000010080000000001',$,'clothoid',$,$,$,$,#2);
#8=IFCALIGNMENTHORIZONTAL('0000000010080000000002',$,'horizontal',$,$,$,$);
#9=IFCALIGNMENT('0000000010080000000003',$,'alignment',$,$,$,$,$);
#10=IFCRELNESTS('0000000010080000000004',$,'alignment-horizontal',$,#9,(#8));
#11=IFCRELNESTS('0000000010080000000005',$,'horizontal-segment',$,#8,(#7));
ENDSEC;
END-ISO-10303-21;
"""


def ifc_bytes() -> bytes:
    return IFC_TEXT.encode("ascii")


def carrier_record() -> dict:
    return {
        "record": "entity",
        "kind": "Spiral",
        "placement": {"links": [], "s": 1},
        "params": {
            "family": "clothoid",
            "source": {
                "predefinedType": "CLOTHOID",
                "startPoint": [0.0, 0.0],
                "startDirection": 0.0,
                "startRadiusOfCurvature": None,
                "endRadiusOfCurvature": 100.0,
                "segmentLength": 25.0,
                "clothoidConstant": 50.0,
                "note": "The segment is IfcAlignmentHorizontalSegment PredefinedType CLOTHOID (buildingSMART IFC4X3, IfcAlignmentHorizontalSegment).",
            },
        },
        "units": {"linear": "unitless", "angle": "radian", "angdir": 0, "angbase": 0.0},
        "tolerance": {"kind": "sourceDefault"},
        "dimension": {"space": "2d"},
        "provenance": {
            "format": "IFC",
            "version": "IFC4X3_ADD2",
            "handle": "0000000010080000000001",
            "layer": "",
            "blockPath": [],
            "fileId": "ifc-clothoid",
        },
    }


def json_bytes() -> bytes:
    return (json.dumps(carrier_record(), allow_nan=False, indent=2) + "\n").encode("utf-8")


def render() -> tuple[bytes, bytes]:
    return ifc_bytes(), json_bytes()


def write() -> None:
    ifc, payload = render()
    IFC_PATH.write_bytes(ifc)
    JSON_PATH.write_bytes(payload)


if __name__ == "__main__":
    write()
