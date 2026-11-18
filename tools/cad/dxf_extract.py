#!/usr/bin/env python3
"""DXF reader that writes CAD carrier JSON lines.

Reads a DXF with ezdxf (MIT) and writes one JSON object per considered
entity, valid under ``carrier.schema.json``. ezdxf is a dev/test
dependency and is not vendored. Nothing from a GPL or LGPL CAD library
is ported.

A considered entity is a modelspace entity, except a similarity INSERT,
which is replaced by the entities of its block (nested inserts compose).
A non-similarity INSERT is one considered entity and declines as a whole.
``len(records) + len(declines) == len(considered)``. Nothing is dropped.

Placement links are applied local-to-world: the entity OCS link, then
the inner block insert, then the outer block insert. ``s`` is -1 when an
odd number of links have ``reflect`` true. A DXF extrusion of -Z is one
such link, for the entities whose coordinates are in their OCS
(``OCS_TYPES``: arcs, circles, polylines, hatches, text, attributes,
inserts). LINE and SPLINE store world coordinates, so their extrusion
moves nothing and is ignored. MTEXT and ELLIPSE store world coordinates
but are drawn in their normal's plane: with a -Z normal they would be
mirrored about their own anchor, so they decline as ID_TiltedPlacement.

Elevation is world z: an INSERT maps its block's z through its own z,
``zscale`` and, under a -Z extrusion, a sign flip; an OCS entity under a
-Z extrusion turns its own z around. Scale is the shared absolute value of xscale and yscale.
Both negative is a half-turn (``reflect`` stays false and 180 degrees are
added to the source rotation) so two reflections are not stored as one.

Modes (ADR-0005):

* ``strict`` declines every named case below.
* ``lenient`` also turns ellipse ratio 1 into an Arc and a closed
  polyline into a Ring (winding rule ``nonzero``, because a polyline
  states no hatch rule). A non-finite bulge (NaN or infinity) is
  ``ID_DegenerateEntity`` in both modes. ``b = 0`` is a Chord in both
  modes; the bulge value is kept. An invisible entity (group 60) is
  not drawn and declines as ``ID_UnsupportedEntity``. A curve-fit or
  spline-fit 2D polyline declines the same way: its vertex list mixes
  the fitted curve with the vertices it was fitted to. A polyline with a constant or
  per-segment width is drawn as a filled band, so it declines as
  ``ID_UnsupportedEntity`` with that reason, in both modes. Any entity
  with a nonzero thickness is extruded along Z and declines as
  ``ID_ThreeDNotYet``. A closed polyline whose last vertex
  repeats its first exactly, with bulge 0, drops that vertex in both
  modes: the closing segment it makes has no length and draws nothing.
  With a nonzero bulge there, or a repeat anywhere else, the zero-length
  segment is still ``ID_DegenerateEntity``.

A Ring records ``orientation`` (``cw`` or ``ccw``) from the source
contour sign, one entry per contour. Vertices are copied in source
order and are not reversed. A hatch with boundary paths is a Ring in
both modes: group 75 odd parity is ``evenodd``. Entire area (style 2)
fills inside the outer boundary whatever the islands' direction, which
``nonzero`` over the stored paths does not say, so it declines as
``ID_HatchRegion``. An empty hatch, outermost style, or an ellipse or spline
edge stays ``ID_HatchRegion``. A 2D POLYLINE is a Compound of chord and
one-segment bulge members in vertex order. A 3D or mesh POLYLINE stays
``ID_ThreeDNotYet``.

Stored ARC angles (group codes 50 and 51, degrees) are always CCW from
the OCS x-axis. ELLIPSE start and end params are always CCW about the
major axis. Both record ``direction`` ``ccw-ocs``. ``$ANGDIR`` and
``$ANGBASE`` stay on ``units`` as display and input provenance, whatever
integer and number the header holds, and are not copied into those
params or into an angleStep. They never decline an entity. An arc whose
end is less than its start is copied raw; 360 is not added.

Named declines: ID_NotSimilarityPlacement, ID_TiltedPlacement,
ID_ThreeDNotYet, ID_HatchRegion, ID_TextEntity, ID_DimensionEntity,
ID_EllipseNotYet, ID_FitPointSpline, ID_UnclampedKnots,
ID_PeriodicSpline, ID_UnknownUnit, ID_ToleranceNonPositive,
ID_ToleranceKindUnsupported,
ID_DegenerateEntity, ID_UnsupportedEntity (with the source name).
DXF does not emit ID_AngleConventionUnknown. ``$ANGDIR`` and
``$ANGBASE`` are display provenance, not a decline. Another format may
emit that id.

An arrayed INSERT (MINSERT) is one INSERT per grid cell, as ezdxf's
``multi_insert()`` gives them; each copy's block path entry is the block
name with ``#`` and the copy's index.

An INSERT's attached ATTRIBs are considered entities too, placed by the
links outside that INSERT (their coordinates are already in its space).
An invisible ATTRIB declines; a non-constant ATTDEF in a block is a
template the INSERT does not draw and declines; a constant ATTDEF is drawn.

A TEXT, MTEXT, ATTRIB or constant ATTDEF declines as ``ID_TextEntity``.

ID_NonzeroOverlapNotYet is in the schema for overlapping nonzero-winding
contours. Year 0 does not detect overlap, so this extractor never emits
that id.

Assisted-by: Cursor Grok 4.7
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from pathlib import Path
from typing import Any, Iterable, Iterator

# Year 0 does not look for overlapping nonzero-winding contours.
OVERLAP_DETECTED = False

SCHEMA_PATH = Path(__file__).with_name("carrier.schema.json")

INSUNITS = {
    0: "unitless",
    1: "inch",
    2: "foot",
    3: "mile",
    4: "millimeter",
    5: "centimeter",
    6: "meter",
    7: "kilometer",
    8: "microinch",
    9: "mil",
    10: "yard",
    11: "angstrom",
    12: "nanometer",
    13: "micron",
    14: "decimeter",
    15: "dekameter",
    16: "hectometer",
    17: "gigameter",
    18: "astronomical-unit",
    19: "light-year",
    20: "parsec",
}

AUNITS = {
    0: "degree",
    1: "dms",
    2: "grad",
    3: "radian",
    4: "surveyor",
}

TEXT_TYPES = {"TEXT", "MTEXT", "ATTRIB", "ATTDEF", "ARCALIGNEDTEXT"}
DIMENSION_TYPES = {"DIMENSION", "LEADER", "MULTILEADER", "MLEADER"}
HATCH_TYPES = {"HATCH", "MPOLYGON"}
THREED_TYPES = {
    "3DFACE",
    "3DSOLID",
    "BODY",
    "MESH",
    "SURFACE",
    "REGION",
    "SOLID",
}
# Entities whose coordinates are in their Object Coordinate System, set by the extrusion.
# Every other entity (LINE, SPLINE, ELLIPSE, MTEXT, POINT, ...) stores world coordinates;
# its extrusion only orients thickness or the plane normal.
OCS_TYPES = frozenset(
    {"ARC", "CIRCLE", "LWPOLYLINE", "POLYLINE", "HATCH", "MPOLYGON", "TEXT", "ATTRIB", "ATTDEF", "SOLID", "TRACE", "INSERT"}
)
# World-coordinate entities whose drawing still depends on the plane normal.
NORMAL_TYPES = frozenset({"MTEXT", "ELLIPSE"})
CIRCULAR_KINDS = {"Arc", "Circle", "BulgePolyline", "Ring"}
# Spiral uses the clothoid Linearizes bound on these tolerances.
STEPPED_KINDS = CIRCULAR_KINDS | {"Spiral"}
# Segment count also passes a Bezier count through as Wang's n.
SEGMENT_COUNT_KINDS = STEPPED_KINDS | {"Bezier"}
GEOMETRY_TYPES = frozenset(
    {"LINE", "LWPOLYLINE", "ARC", "CIRCLE", "ELLIPSE", "SPLINE", "INSERT", "POLYLINE"}
)
HANDLED_ENTITIES = frozenset(
    TEXT_TYPES | DIMENSION_TYPES | HATCH_TYPES | THREED_TYPES | GEOMETRY_TYPES
)
READ_HEADERS = frozenset({"$INSUNITS", "$AUNITS", "$ANGDIR", "$ANGBASE"})
IGNORED_HEADERS = frozenset()
_EPS = 1e-9


def _num(value: Any) -> float:
    return float(value)


def _finite(value: float) -> bool:
    return math.isfinite(value)


def _xy(x: Any, y: Any) -> list[float] | None:
    fx, fy = _num(x), _num(y)
    if not (_finite(fx) and _finite(fy)):
        return None
    return [fx, fy]


def _dist(a: list[float], b: list[float]) -> float:
    return math.hypot(b[0] - a[0], b[1] - a[1])


def det_sign(links: list[dict[str, Any]]) -> int:
    """Determinant sign of a similarity chain. -1 iff reflect is odd."""
    sign = 1
    for link in links:
        if link["reflect"]:
            sign = -sign
    return sign


def knot_clamped(knots: list[float], degree: int, count: int) -> bool:
    """True when the knot vector is clamped: p+1 equal knots at each end."""
    need = count + degree + 1
    if degree < 1 or count < degree + 1 or len(knots) != need:
        return False
    head = knots[: degree + 1]
    tail = knots[-(degree + 1) :]
    return all(math.isclose(k, head[0], abs_tol=_EPS) for k in head) and all(
        math.isclose(k, tail[0], abs_tol=_EPS) for k in tail
    )


def _decl(
    decline_id: str,
    reason: str,
    provenance: dict[str, Any],
    name: str | None = None,
) -> dict[str, Any]:
    row: dict[str, Any] = {
        "record": "decline",
        "id": decline_id,
        "provenance": provenance,
        "reason": reason,
    }
    if name is not None:
        row["name"] = name
    return row


def _provenance(
    entity: Any,
    version: str,
    file_id: str,
    block_path: list[str],
) -> dict[str, Any]:
    layer = getattr(entity.dxf, "layer", "0") or "0"
    handle = str(getattr(entity.dxf, "handle", "") or "")
    origin = getattr(entity, "origin_of_copy", None)
    if not handle and origin is not None:
        # A virtual copy (an attribute copied into a MINSERT cell) reports its source entity.
        handle = str(origin.dxf.get("handle", "") or "")
    return {
        "format": "DXF",
        "version": version,
        "handle": handle,
        "layer": str(layer),
        "blockPath": list(block_path),
        "fileId": file_id,
    }


def _header_units(doc: Any) -> dict[str, Any] | str:
    ins = int(doc.header.get("$INSUNITS", 0))
    if ins not in INSUNITS:
        return "ID_UnknownUnit"
    aunits = int(doc.header.get("$AUNITS", 0))
    # $ANGDIR (integer) and $ANGBASE (degrees) are display/input provenance.
    # Any value is kept. They do not decline the entity.
    angdir = int(doc.header.get("$ANGDIR", 0))
    angbase = _num(doc.header.get("$ANGBASE", 0.0))
    if not _finite(angbase):
        angbase = None
    return {
        "linear": INSUNITS[ins],
        "linearCode": ins,
        "angle": AUNITS.get(aunits, str(aunits)),
        "angleCode": aunits,
        "angdir": angdir,
        "angbase": angbase,
    }


def parse_tolerance(spec: str) -> dict[str, Any] | str:
    """Parse ``source``, ``sagitta:d``, ``count:n``, or ``angle:alpha``.

    A bad number is ``ID_ToleranceNonPositive``. An unknown form is
    ``ID_ToleranceKindUnsupported``.
    """
    text = spec.strip()
    if text in ("", "source", "sourceDefault"):
        return {"kind": "sourceDefault"}
    if ":" not in text:
        return "ID_ToleranceKindUnsupported"
    kind, raw = text.split(":", 1)
    kind = kind.strip().lower()
    try:
        value = float(raw)
    except ValueError:
        return "ID_ToleranceNonPositive"
    if kind in ("sagitta", "d"):
        if not _finite(value) or value <= 0:
            return "ID_ToleranceNonPositive"
        return {"kind": "sagitta", "d": value}
    if kind in ("count", "n", "segmentcount"):
        if not _finite(value) or value < 1 or not float(value).is_integer():
            return "ID_ToleranceNonPositive"
        return {"kind": "segmentCount", "n": int(value)}
    if kind in ("angle", "alpha", "anglestep"):
        if not _finite(value) or value <= 0:
            return "ID_ToleranceNonPositive"
        return {
            "kind": "angleStep",
            "alpha": value,
            "angleUnit": "degree",
            "direction": "ccw-ocs",
        }
    return "ID_ToleranceKindUnsupported"


def _extrusion_link(entity: Any) -> dict[str, Any] | str | None:
    """None is +Z identity. A dict is a -Z reflection. A string is a decline id."""
    extr = getattr(entity.dxf, "extrusion", None)
    if extr is None:
        return None
    x, y, z = _num(extr[0]), _num(extr[1]), _num(extr[2])
    if not (_finite(x) and _finite(y) and _finite(z)):
        return "ID_DegenerateEntity"
    if abs(x) > _EPS or abs(y) > _EPS or abs(z) <= _EPS:
        return "ID_TiltedPlacement"
    if z < 0:
        return {
            "translate": [0.0, 0.0],
            "rotate": 0.0,
            "scale": 1.0,
            "reflect": True,
        }
    return None


def _insert_link(entity: Any) -> dict[str, Any] | str:
    sx = _num(getattr(entity.dxf, "xscale", 1.0))
    sy = _num(getattr(entity.dxf, "yscale", 1.0))
    rotation = _num(getattr(entity.dxf, "rotation", 0.0))
    ins = entity.dxf.insert
    xy = _xy(ins[0], ins[1])
    if xy is None or not (_finite(sx) and _finite(sy) and _finite(rotation)):
        return "ID_DegenerateEntity"
    if abs(sx) <= _EPS or abs(sy) <= _EPS:
        return "ID_DegenerateEntity"
    if not math.isclose(abs(sx), abs(sy), rel_tol=1e-9, abs_tol=_EPS):
        return "ID_NotSimilarityPlacement"
    reflect = (sx < 0) != (sy < 0)
    if sx < 0 and sy < 0:
        rotation += 180.0
    return {
        "translate": xy,
        "rotate": rotation,
        "scale": abs(sx),
        "reflect": reflect,
    }


def _insert_z(entity: Any) -> float | str:
    z = _num(entity.dxf.insert[2])
    if not _finite(z):
        return "ID_DegenerateEntity"
    return z


def _dimension(elevation: float) -> dict[str, Any]:
    if abs(elevation) <= _EPS:
        return {"space": "2d"}
    return {"space": "2d+elevation", "elevation": elevation}


def _entity(
    kind: str,
    params: dict[str, Any],
    links: list[dict[str, Any]],
    units: dict[str, Any],
    tolerance: dict[str, Any],
    elevation: float,
    provenance: dict[str, Any],
    source_name: str | None = None,
) -> dict[str, Any]:
    row: dict[str, Any] = {
        "record": "entity",
        "kind": kind,
        "placement": {"links": links, "s": det_sign(links)},
        "params": params,
        "units": units,
        "tolerance": tolerance,
        "dimension": _dimension(elevation),
        "provenance": provenance,
    }
    if source_name is not None:
        row["sourceName"] = source_name
    return row


def _stamp_tolerance(tolerance: dict[str, Any]) -> dict[str, Any]:
    """Angle steps are the stored CCW OCS convention, never ``$ANGDIR``."""
    if tolerance.get("kind") != "angleStep":
        return tolerance
    stamped = dict(tolerance)
    stamped["direction"] = "ccw-ocs"
    return stamped


def _tolerance_ok(kind: str, tolerance: dict[str, Any]) -> str | None:
    if tolerance["kind"] == "segmentCount" and kind not in SEGMENT_COUNT_KINDS:
        return "ID_ToleranceKindUnsupported"
    if tolerance["kind"] == "angleStep" and kind not in STEPPED_KINDS:
        return "ID_ToleranceKindUnsupported"
    return None


def _segment(start: list[float], end: list[float], bulge: float) -> dict[str, Any] | str:
    if not _finite(bulge):
        return "ID_DegenerateEntity"
    if _dist(start, end) <= _EPS:
        return "ID_DegenerateEntity"
    if abs(bulge) <= _EPS:
        return {"kind": "Chord", "start": start, "end": end, "bulge": 0.0}
    return {"kind": "Arc", "start": start, "end": end, "bulge": bulge}


def _bulge_segments(points: list[tuple[float, float, float]], closed: bool) -> list[dict[str, Any]] | str:
    if closed and len(points) > 1 and points[-1][:2] == points[0][:2] and points[-1][2] == 0:
        # A closed polyline that repeats its first vertex at the end has a zero-length
        # closing segment. With no bulge on it, it draws nothing, so it is dropped.
        points = points[:-1]
    if len(points) < 2:
        return "ID_DegenerateEntity"
    span = len(points) if closed else len(points) - 1
    if closed and len(points) < 3:
        return "ID_DegenerateEntity"
    segments: list[dict[str, Any]] = []
    for i in range(span):
        x0, y0, bulge = points[i]
        x1, y1, _ = points[(i + 1) % len(points)]
        start = _xy(x0, y0)
        end = _xy(x1, y1)
        if start is None or end is None:
            return "ID_DegenerateEntity"
        seg = _segment(start, end, _num(bulge))
        if isinstance(seg, str):
            return seg
        segments.append(seg)
    return segments


def _const_zs(values: Iterable[float]) -> float | str:
    zs = [_num(z) for z in values]
    if not zs:
        return 0.0
    if not all(_finite(z) for z in zs):
        return "ID_DegenerateEntity"
    if max(zs) - min(zs) > _EPS:
        return "ID_ThreeDNotYet"
    return zs[0]


def _spline_weights(spline: Any, count: int) -> list[float] | str:
    raw = list(spline.weights)
    if not raw:
        return [1.0] * count
    weights = [_num(w) for w in raw]
    if len(weights) != count or not all(_finite(w) and w > 0 for w in weights):
        return "ID_DegenerateEntity"
    return weights


def _map_spline(entity: Any) -> dict[str, Any] | str:
    if bool(entity.get_flag_state(entity.PERIODIC)):
        return "ID_PeriodicSpline"
    controls = list(entity.control_points)
    fits = list(entity.fit_points)
    if not controls:
        if fits:
            return "ID_FitPointSpline"
        return "ID_DegenerateEntity"
    zs = _const_zs(p[2] for p in controls)
    if isinstance(zs, str):
        return zs
    degree = int(entity.dxf.degree)
    knots = [_num(k) for k in entity.knots]
    if not all(_finite(k) for k in knots):
        return "ID_DegenerateEntity"
    if not knot_clamped(knots, degree, len(controls)):
        return "ID_UnclampedKnots"
    weights = _spline_weights(entity, len(controls))
    if isinstance(weights, str):
        return weights
    points = []
    for p in controls:
        xy = _xy(p[0], p[1])
        if xy is None:
            return "ID_DegenerateEntity"
        points.append(xy)
    unit = all(math.isclose(w, 1.0, abs_tol=_EPS) for w in weights)
    if unit and degree in (2, 3) and len(points) == degree + 1:
        canonical = [0.0] * (degree + 1) + [1.0] * (degree + 1)
        if all(math.isclose(a, b, abs_tol=_EPS) for a, b in zip(knots, canonical)):
            return {
                "kind": "Bezier",
                "elevation": zs,
                "params": {
                    "degree": degree,
                    "controlPoints": points,
                    "weights": [1] * len(points),
                    "knots": [0] * (degree + 1) + [1] * (degree + 1),
                },
            }
    return {
        "kind": "BSpline",
        "elevation": zs,
        "params": {
            "degree": degree,
            "controlPoints": points,
            "weights": weights,
            "knots": knots,
            "clamped": True,
        },
    }


def _signed_area(segments: list[dict[str, Any]]) -> float:
    area = 0.0
    for seg in segments:
        x1, y1 = seg["start"]
        x2, y2 = seg["end"]
        area += x1 * y2 - x2 * y1
    return area


def _orientation(segments: list[dict[str, Any]]) -> str | None:
    """Source contour sign. None when the polygon area is degenerate."""
    area = _signed_area(segments)
    if abs(area) <= _EPS:
        return None
    return "ccw" if area > 0 else "cw"


def _ring(contours: list[list[dict[str, Any]]], rule: str, elevation: float) -> dict[str, Any] | str:
    orientations: list[str] = []
    for contour in contours:
        sign = _orientation(contour)
        if sign is None:
            return "ID_DegenerateEntity"
        orientations.append(sign)
    return {
        "kind": "Ring",
        "elevation": elevation,
        "params": {"windingRule": rule, "contours": contours, "orientation": orientations},
    }


def _chain_member(segment: dict[str, Any]) -> dict[str, Any]:
    """One source segment, in its own direction. A bulge is not rewritten as a reversed arc."""
    if segment["kind"] == "Chord":
        return {"kind": "Chord", "params": {"start": segment["start"], "end": segment["end"]}}
    return {"kind": "BulgePolyline", "params": {"closed": False, "segments": [segment]}}


# A polyline with width is drawn as a filled band, not as its centre line.
_WIDTH_DECLINE = ("ID_UnsupportedEntity", "polyline width: drawn as a filled band, not a curve")


def _invisible(entity: Any) -> bool:
    """Group code 60: the entity is not drawn."""
    try:
        return bool(int(entity.dxf.get("invisible", 0)))
    except Exception:  # an entity type without the attribute
        return False


def _thickness(entity: Any) -> float:
    """The entity's extrusion thickness, 0 when it has none."""
    try:
        return _num(entity.dxf.get("thickness", 0.0))
    except Exception:  # an entity type without a thickness attribute
        return 0.0


def _map_polyline(entity: Any) -> dict[str, Any] | str | tuple[str, str]:
    if entity.is_3d_polyline or entity.is_polygon_mesh or entity.is_poly_face_mesh or not entity.is_2d_polyline:
        return "ID_ThreeDNotYet"
    if int(entity.dxf.get("flags", 0)) & 6:
        # Curve-fit (2) or spline-fit (4): the vertex list mixes the fitted curve with the
        # vertices it was fitted to, and which of them are drawn is not settled here.
        return ("ID_UnsupportedEntity", "curve-fit or spline-fit polyline: its drawn vertices are not read")
    widths = [_num(entity.dxf.get(key, 0.0)) for key in ("default_start_width", "default_end_width")]
    widths += [_num(v.dxf.get(key, 0.0)) for v in entity.vertices for key in ("start_width", "end_width")]
    if any(w != 0 for w in widths):
        return _WIDTH_DECLINE
    points: list[tuple[float, float, float]] = []
    for vertex in entity.vertices:
        loc = vertex.dxf.location
        z = _num(loc[2])
        if not _finite(z) or abs(z) > _EPS:
            return "ID_ThreeDNotYet"
        points.append((_num(loc[0]), _num(loc[1]), _num(getattr(vertex.dxf, "bulge", 0.0))))
    segments = _bulge_segments(points, bool(entity.is_closed))
    if isinstance(segments, str):
        return segments
    return {
        "kind": "Compound",
        "elevation": 0.0,
        "params": {"members": [_chain_member(segment) for segment in segments]},
    }


def _hatch_rule(entity: Any) -> str | None:
    """Group 75. 0 (odd parity) is ``evenodd``; 1 (outermost) and 2 (entire area) decline.

    Entire area fills everything inside the outer boundary, islands included. ``nonzero``
    over the paths as stored is not that: an island wound against the outer path comes out
    as a hole. Saying it would need the contours reoriented, and the carrier keeps their
    source orientation, so the hatch declines instead.
    """
    style = int(getattr(entity.dxf, "hatch_style", 0))
    if style == 0:
        return "evenodd"
    return None


def _arc_edge_segment(edge: Any) -> dict[str, Any] | str:
    radius = _num(edge.radius)
    start = _num(edge.start_angle)
    end = _num(edge.end_angle)
    center = edge.center
    if not (_finite(radius) and _finite(start) and _finite(end)) or radius <= _EPS:
        return "ID_DegenerateEntity"
    cx, cy = _num(center[0]), _num(center[1])
    if not (_finite(cx) and _finite(cy)):
        return "ID_DegenerateEntity"

    def at(degrees: float) -> list[float] | None:
        radians = math.radians(degrees)
        return _xy(cx + radius * math.cos(radians), cy + radius * math.sin(radians))

    # Travel follows the edge flag. Endpoints stay on the stated angles.
    sweep = (end - start) % 360.0 if edge.ccw else (start - end) % 360.0
    if sweep <= _EPS or abs(sweep - 360.0) <= _EPS:
        return "ID_DegenerateEntity"
    bulge = math.tan(math.radians(sweep) / 4.0) * (1.0 if edge.ccw else -1.0)
    a = at(start)
    b = at(end)
    if a is None or b is None:
        return "ID_DegenerateEntity"
    return _segment(a, b, bulge)


def _edge_segment(edge: Any) -> dict[str, Any] | str:
    name = type(edge).__name__
    if name == "LineEdge":
        start = _xy(edge.start[0], edge.start[1])
        end = _xy(edge.end[0], edge.end[1])
        if start is None or end is None:
            return "ID_DegenerateEntity"
        return _segment(start, end, 0.0)
    if name == "ArcEdge":
        return _arc_edge_segment(edge)
    return "ID_HatchRegion"


def _path_contour(path: Any) -> list[dict[str, Any]] | str:
    if type(path).__name__ == "PolylinePath":
        if not path.is_closed:
            return "ID_HatchRegion"
        points = [(_num(x), _num(y), _num(b)) for x, y, b in path.vertices]
        return _bulge_segments(points, True)
    if type(path).__name__ != "EdgePath":
        return "ID_HatchRegion"
    segments: list[dict[str, Any]] = []
    for edge in path.edges:
        segment = _edge_segment(edge)
        if isinstance(segment, str):
            return segment
        segments.append(segment)
    if len(segments) < 3:
        return "ID_HatchRegion"
    if _dist(segments[0]["start"], segments[-1]["end"]) > _EPS:
        return "ID_HatchRegion"
    return segments


def _hatch_elevation(entity: Any) -> float | str:
    elev = getattr(entity.dxf, "elevation", None)
    if elev is None:
        return 0.0
    z = _num(elev[2]) if len(elev) > 2 else 0.0
    if not _finite(z):
        return "ID_DegenerateEntity"
    return z


def _map_hatch(entity: Any) -> dict[str, Any] | str:
    if entity.dxftype() == "MPOLYGON":
        offset = entity.dxf.get("offset_vector", (0.0, 0.0, 0.0))
        if any(abs(_num(v)) > _EPS for v in offset):
            # Group 11 of an MPOLYGON; what it moves is not settled here.
            return "ID_HatchRegion"
    rule = _hatch_rule(entity)
    if rule is None:
        return "ID_HatchRegion"
    paths = list(entity.paths)
    if not paths:
        return "ID_HatchRegion"
    contours: list[list[dict[str, Any]]] = []
    for path in paths:
        contour = _path_contour(path)
        if isinstance(contour, str):
            return contour
        contours.append(contour)
    elevation = _hatch_elevation(entity)
    if isinstance(elevation, str):
        return elevation
    return _ring(contours, rule, elevation)


def _materialize(
    kind: str,
    params: dict[str, Any],
    links: list[dict[str, Any]],
    units: dict[str, Any],
    tolerance: dict[str, Any],
    elevation: float,
    provenance: dict[str, Any],
) -> dict[str, Any]:
    """Compound members are carrier entities, still in source order."""
    if kind != "Compound":
        return params
    members = []
    for spec in params["members"]:
        child = _materialize(spec["kind"], spec["params"], links, units, tolerance, elevation, provenance)
        members.append(_entity(spec["kind"], child, links, units, tolerance, elevation, provenance))
    return {"members": members}


def _map_geometry(entity: Any, mode: str) -> dict[str, Any] | str | tuple[str, str]:
    """Return a mapping dict or a decline id.

    The dict has kind, params, and elevation. Decline ids are strings.
    """
    dxftype = entity.dxftype()
    if dxftype in TEXT_TYPES:
        return "ID_TextEntity"
    if dxftype in DIMENSION_TYPES:
        return "ID_DimensionEntity"
    if dxftype in HATCH_TYPES:
        return _map_hatch(entity)
    if dxftype == "POLYLINE":
        return _map_polyline(entity)
    if dxftype in THREED_TYPES:
        return "ID_ThreeDNotYet"
    if dxftype == "LINE":
        start = entity.dxf.start
        end = entity.dxf.end
        zs = _const_zs((start[2], end[2]))
        if isinstance(zs, str):
            return zs
        a = _xy(start[0], start[1])
        b = _xy(end[0], end[1])
        if a is None or b is None or _dist(a, b) <= _EPS:
            return "ID_DegenerateEntity"
        return {"kind": "Chord", "elevation": zs, "params": {"start": a, "end": b}}
    if dxftype == "LWPOLYLINE":
        widths = [_num(entity.dxf.get("const_width", 0.0))]
        widths += [_num(w) for _x, _y, start, end in entity.get_points("xyse") for w in (start, end)]
        if any(w != 0 for w in widths):
            return _WIDTH_DECLINE
        raw = [(_num(x), _num(y), _num(b)) for x, y, b in entity.get_points("xyb")]
        closed = bool(entity.closed)
        segments = _bulge_segments(raw, closed)
        if isinstance(segments, str):
            return segments
        elevation = _num(getattr(entity.dxf, "elevation", 0.0))
        if not _finite(elevation):
            return "ID_DegenerateEntity"
        if mode == "lenient" and closed:
            return _ring([segments], "nonzero", elevation)
        return {
            "kind": "BulgePolyline",
            "elevation": elevation,
            "params": {"closed": closed, "segments": segments},
        }
    if dxftype == "ARC":
        center = entity.dxf.center
        zs = _const_zs((center[2],))
        if isinstance(zs, str):
            return zs
        c = _xy(center[0], center[1])
        radius = _num(entity.dxf.radius)
        start = _num(entity.dxf.start_angle)
        end = _num(entity.dxf.end_angle)
        if c is None or not (_finite(radius) and _finite(start) and _finite(end)):
            return "ID_DegenerateEntity"
        if radius <= _EPS or math.isclose(start, end, abs_tol=_EPS):
            return "ID_DegenerateEntity"
        return {
            "kind": "Arc",
            "elevation": zs,
            "params": {
                "center": c,
                "radius": radius,
                "startAngle": start,
                "endAngle": end,
                "angleUnit": "degree",
                "direction": "ccw-ocs",
            },
        }
    if dxftype == "CIRCLE":
        center = entity.dxf.center
        zs = _const_zs((center[2],))
        if isinstance(zs, str):
            return zs
        c = _xy(center[0], center[1])
        radius = _num(entity.dxf.radius)
        if c is None or not _finite(radius):
            return "ID_DegenerateEntity"
        if radius <= _EPS:
            return "ID_DegenerateEntity"
        return {"kind": "Circle", "elevation": zs, "params": {"center": c, "radius": radius}}
    if dxftype == "ELLIPSE":
        if mode != "lenient":
            return "ID_EllipseNotYet"
        ratio = _num(entity.dxf.ratio)
        if not _finite(ratio):
            return "ID_DegenerateEntity"
        if not math.isclose(ratio, 1.0, abs_tol=_EPS):
            return "ID_EllipseNotYet"
        center = entity.dxf.center
        major = entity.dxf.major_axis
        zs = _const_zs((center[2], major[2]))
        if isinstance(zs, str):
            return zs
        c = _xy(center[0], center[1])
        radius = math.hypot(_num(major[0]), _num(major[1]))
        start = _num(entity.dxf.start_param)
        end = _num(entity.dxf.end_param)
        if (
            c is None
            or not (_finite(radius) and _finite(start) and _finite(end) and _finite(_num(major[0])) and _finite(_num(major[1])))
        ):
            return "ID_DegenerateEntity"
        if radius <= _EPS or math.isclose(start, end, abs_tol=_EPS):
            return "ID_DegenerateEntity"
        return {
            "kind": "Arc",
            "elevation": zs,
            "params": {
                "center": c,
                "radius": radius,
                "startAngle": start,
                "endAngle": end,
                "angleUnit": "radian",
                "direction": "ccw-ocs",
                "frameAngle": math.atan2(_num(major[1]), _num(major[0])),
            },
        }
    if dxftype == "SPLINE":
        return _map_spline(entity)
    return "ID_UnsupportedEntity"


def _iter_block(doc: Any, name: str) -> Iterator[Any]:
    for entity in doc.blocks.get(name):
        if entity.dxftype() != "ENDBLK":
            yield entity


def extract_document(
    doc: Any,
    *,
    mode: str = "strict",
    tolerance: dict[str, Any] | None = None,
    file_id: str = "unnamed",
    on_considered: Any = None,
) -> list[dict[str, Any]]:
    """Extract carrier records and declines from an ezdxf document.

    ``mode`` is ``strict`` or ``lenient``. ``tolerance`` is a schema
    tolerance object; the default is sourceDefault.
    ``on_considered``, when given, is called with the DXF type of each
    considered entity, once per row, in row order.
    """
    if mode not in ("strict", "lenient"):
        raise ValueError("mode must be strict or lenient")
    if OVERLAP_DETECTED:
        raise RuntimeError("year 0 does not detect nonzero contour overlap")
    tol = _stamp_tolerance(tolerance if tolerance is not None else {"kind": "sourceDefault"})
    version = str(doc.dxfversion)
    units = _header_units(doc)
    rows: list[dict[str, Any]] = []

    def emit(
        entity: Any,
        prefix: list[dict[str, Any]],
        block_path: list[str],
        z_offset: float,
        stack: tuple[str, ...],
        label: str | None = None,
        z_factor: float = 1.0,
    ) -> None:
        """Emit one considered entity. A local z maps to world z as ``z_offset + z_factor * z``."""

        def add(row: dict[str, Any]) -> None:
            # Every row is one considered entity: this one.
            rows.append(row)
            if on_considered is not None:
                on_considered(entity.dxftype())

        prov = _provenance(entity, version, file_id, block_path)
        if isinstance(units, str):
            add(_decl(units, f"header convention {units}", prov))
            return
        kind = entity.dxftype()
        if _invisible(entity):
            add(_decl("ID_UnsupportedEntity", "invisible: not drawn", prov, name=kind))
            return
        if kind == "INSERT":
            name = str(entity.dxf.name)
            count = int(getattr(entity, "mcount", 1) or 1)
            if count > 1:
                # An arrayed INSERT (MINSERT) draws its block once per grid cell. ezdxf's
                # multi_insert() gives each copy as a plain INSERT, attributes included.
                for index, copy in enumerate(entity.multi_insert()):
                    copy.dxf.handle = entity.dxf.get("handle")
                    emit(copy, prefix, block_path, z_offset, stack, label=f"{name}#{index}", z_factor=z_factor)
                return
            if name in stack:
                add(_decl("ID_DegenerateEntity", f"cyclic block {name}", prov))
                return
            extr = _extrusion_link(entity)
            if isinstance(extr, str):
                add(_decl(extr, "INSERT extrusion is not +/- Z", prov))
                return
            link = _insert_link(entity)
            if isinstance(link, str):
                reason = (
                    "xscale != yscale"
                    if link == "ID_NotSimilarityPlacement"
                    else link
                )
                add(_decl(link, reason, prov))
                return
            iz = _insert_z(entity)
            zscale = _num(entity.dxf.get("zscale", 1.0))
            if isinstance(iz, str) or not _finite(zscale):
                add(_decl("ID_DegenerateEntity", "non-finite INSERT z or zscale", prov))
                return
            children = list(_iter_block(doc, name))
            if not children:
                add(_decl("ID_DegenerateEntity", f"empty block {name}", prov))
                return
            child_prefix = [link] + prefix
            # Under a -Z extrusion the INSERT's OCS z runs along world -z.
            flip = -1.0 if extr is not None else 1.0
            if extr is not None:
                child_prefix = [extr] + child_prefix
            child_offset = z_offset + z_factor * flip * iz
            child_factor = z_factor * flip * zscale
            for child in children:
                emit(child, child_prefix, block_path + [label or name], child_offset, stack + (name,), z_factor=child_factor)
            # Attached attributes are placed in the space the INSERT sits in, not in the block.
            for attrib in entity.attribs:
                emit(attrib, prefix, block_path + [label or name], z_offset, stack + (name,), z_factor=z_factor)
            return
        extr = _extrusion_link(entity)
        if kind in OCS_TYPES:
            if isinstance(extr, str):
                add(_decl(extr, "extrusion is not +/- Z", prov))
                return
        elif kind in NORMAL_TYPES and extr is not None:
            # World coordinates, but drawn in the plane the normal sets: a -Z normal mirrors
            # it about its own anchor, which no link here expresses.
            reason = "extrusion is not +/- Z" if isinstance(extr, str) else f"{kind} with a -Z extrusion is drawn mirrored; not read"
            add(_decl("ID_TiltedPlacement", reason, prov))
            return
        else:
            extr = None  # world coordinates: the extrusion does not move them
        thickness = _thickness(entity)
        if thickness != 0:
            # Thickness extrudes the entity along Z: it spans more than one elevation.
            reason = "thickness extrudes the entity in Z" if _finite(thickness) else "non-finite thickness"
            add(_decl("ID_ThreeDNotYet" if _finite(thickness) else "ID_DegenerateEntity", reason, prov))
            return
        # A -Z OCS also turns its z around.
        z_sign = -1.0 if extr is not None else 1.0
        mapped = _map_geometry(entity, mode)
        if isinstance(mapped, tuple):
            # A decline id with its own reason.
            add(_decl(mapped[0], mapped[1], prov, name=kind if mapped[0] == "ID_UnsupportedEntity" else None))
            return
        if isinstance(mapped, str):
            if mapped == "ID_UnsupportedEntity":
                add(_decl(mapped, f"unsupported {kind}", prov, name=kind))
            else:
                add(_decl(mapped, mapped, prov))
            return
        bad = _tolerance_ok(mapped["kind"], tol)
        if bad:
            add(_decl(bad, f"{tol['kind']} on {mapped['kind']}", prov))
            return
        links = ([extr] + prefix) if extr else list(prefix)
        elevation = z_offset + z_factor * z_sign * _num(mapped["elevation"])
        if not _finite(elevation):
            add(_decl("ID_DegenerateEntity", "non-finite elevation", prov))
            return
        params = _materialize(mapped["kind"], mapped["params"], links, units, tol, elevation, prov)
        add(_entity(mapped["kind"], params, links, units, tol, elevation, prov))

    for entity in doc.modelspace():
        emit(entity, [], [], 0.0, ())
    return rows


def file_identity(path: Path) -> str:
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    return digest


def extract_path(
    path: Path,
    *,
    mode: str = "strict",
    tolerance: dict[str, Any] | None = None,
    file_id: str | None = None,
) -> list[dict[str, Any]]:
    import ezdxf

    doc = ezdxf.readfile(path)
    return extract_document(
        doc,
        mode=mode,
        tolerance=tolerance,
        file_id=file_id if file_id is not None else file_identity(path),
    )


def write_jsonl(rows: Iterable[dict[str, Any]], dest: Any) -> None:
    for row in rows:
        dest.write(json.dumps(row, allow_nan=False, separators=(",", ":")))
        dest.write("\n")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Extract a DXF into CAD carrier JSON lines.")
    parser.add_argument("dxf", type=Path)
    parser.add_argument("output", type=Path, nargs="?", help="JSON lines path, or stdout if omitted")
    parser.add_argument("--mode", choices=("strict", "lenient"), default="strict")
    parser.add_argument(
        "--tolerance",
        default="source",
        help="source | sagitta:d | count:n | angle:alpha",
    )
    parser.add_argument("--file-id", default=None)
    args = parser.parse_args(argv)
    tol = parse_tolerance(args.tolerance)
    if isinstance(tol, str):
        print(f"bad tolerance: {tol}", file=sys.stderr)
        return 2
    if not args.dxf.is_file():
        print(f"not a file: {args.dxf}", file=sys.stderr)
        return 2
    rows = extract_path(args.dxf, mode=args.mode, tolerance=tol, file_id=args.file_id)
    if args.output is None:
        write_jsonl(rows, sys.stdout)
    else:
        with args.output.open("w", encoding="utf-8") as fh:
            write_jsonl(rows, fh)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
