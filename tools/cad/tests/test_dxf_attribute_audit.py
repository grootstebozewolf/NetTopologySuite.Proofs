"""Every DXF attribute of every entity the extractor handles is classified.

A DXF property that changes what an entity draws must be read or must
make the entity decline; ignoring it silently turns a record into a
confident falsehood (polyline width did, and thickness, and invisible).
``AUDIT`` classifies every attribute ezdxf defines for the handled entity
types, so a new or overlooked attribute fails ``test_every_attribute_is_classified``
until someone decides. The ``declines`` entries are then checked by
behaviour: set to a non-default value, the entity declines.

Classes:
* read: the extractor uses it.
* ignored: it does not change the 2D geometry drawn (appearance, data,
  structure), or only matters where the entity already declines.
* declines: a non-default value makes the entity decline.
"""

from __future__ import annotations

from pathlib import Path

import ezdxf
import pytest
from ezdxf.entities import factory

import dxf_extract

_COMMON = {
    "handle": "read",  # provenance
    "layer": "read",  # provenance
    "extrusion": "read",
    "invisible": "declines",
    "owner": "ignored",
    "paperspace": "ignored",  # the extractor walks modelspace
    **{name: "ignored" for name in (
        "color", "color_name", "true_color", "transparency", "linetype", "lineweight", "ltscale",
        "material_handle", "plotstyle_enum", "plotstyle_handle", "shadow_mode", "visualstyle_handle",
    )},
}
# R11/R12 group 38. ezdxf's loader moves it into the point's z when that z is 0 and then
# discards the attribute (``elevation_to_z_axis``), so the extractor reads it through the
# point; fixtures/r12_group38.dxf checks that no height is lost.
_LEGACY_ELEVATION = "read"

AUDIT: dict[str, dict[str, str]] = {
    "LINE": {"start": "read", "end": "read", "thickness": "declines"},
    "ARC": {"center": "read", "radius": "read", "start_angle": "read", "end_angle": "read",
            "thickness": "declines", "elevation": _LEGACY_ELEVATION},
    "CIRCLE": {"center": "read", "radius": "read", "thickness": "declines", "elevation": _LEGACY_ELEVATION},
    "ELLIPSE": {"center": "read", "major_axis": "read", "ratio": "read", "start_param": "read", "end_param": "read"},
    "SPLINE": {
        "degree": "read", "flags": "read",  # periodic
        "n_control_points": "ignored", "n_fit_points": "ignored", "n_knots": "ignored",  # counts
        "control_point_tolerance": "ignored", "knot_tolerance": "ignored", "fit_tolerance": "ignored",
        "start_tangent": "ignored", "end_tangent": "ignored",  # fit-point splines decline
    },
    "LWPOLYLINE": {"const_width": "declines", "count": "ignored", "elevation": "read", "flags": "read",
                   "thickness": "declines"},
    "POLYLINE": {
        "default_start_width": "declines", "default_end_width": "declines", "elevation": "read",
        "flags": "read", "thickness": "declines",
        # Meshes and fitted polylines decline, so these never shape a record.
        "m_count": "ignored", "n_count": "ignored", "m_smooth_density": "ignored",
        "n_smooth_density": "ignored", "smooth_type": "ignored",
    },
    "VERTEX": {
        "location": "read", "bulge": "read", "start_width": "declines", "end_width": "declines",
        "flags": "ignored", "tangent": "ignored",  # fit and mesh vertices: their polylines decline
        "vtx0": "ignored", "vtx1": "ignored", "vtx2": "ignored", "vtx3": "ignored", "vertex_identifier": "ignored",
        "invisible": "ignored",  # a vertex is never drawn on its own
    },
    "HATCH": {
        "elevation": "read", "hatch_style": "read",
        # The region is the same whatever fills it.
        "associative": "ignored", "n_seed_points": "ignored", "pattern_angle": "ignored",
        "pattern_double": "ignored", "pattern_name": "ignored", "pattern_scale": "ignored",
        "pattern_type": "ignored", "pixel_size": "ignored", "solid_fill": "ignored",
    },
    "MPOLYGON": {
        "elevation": "read", "hatch_style": "read", "offset_vector": "declines",
        "annotated_boundary": "ignored", "degenerated_loops": "ignored", "fill_color": "ignored",
        "n_seed_points": "ignored", "pattern_angle": "ignored", "pattern_double": "ignored",
        "pattern_name": "ignored", "pattern_scale": "ignored", "pattern_type": "ignored",
        "pixel_size": "ignored", "solid_fill": "ignored", "version": "ignored",
    },
    "INSERT": {
        "name": "read", "insert": "read", "rotation": "read", "xscale": "read", "yscale": "read",
        "zscale": "read", "row_count": "read", "column_count": "read", "row_spacing": "read",
        "column_spacing": "read", "attribs_follow": "ignored", "elevation": _LEGACY_ELEVATION,
    },
    "TEXT": {
        "text": "read", "insert": "read", "align_point": "read", "halign": "read", "valign": "read",
        "height": "read", "rotation": "read", "oblique": "read", "width": "read", "style": "read",
        "text_generation_flag": "read", "thickness": "declines", "elevation": _LEGACY_ELEVATION,
    },
    "MTEXT": {
        "text": "read", "insert": "read", "char_height": "read", "width": "read", "rotation": "read",
        "text_direction": "read", "attachment_point": "read", "flow_direction": "read",
        "line_spacing_factor": "read", "line_spacing_style": "read", "style": "read",
        "defined_height": "read",  # columns
        # The background mask and the frame box are drawn behind the text, not as it.
        "bg_fill": "ignored", "bg_fill_color": "ignored", "bg_fill_color_name": "ignored",
        "bg_fill_transparency": "ignored", "bg_fill_true_color": "ignored", "box_fill_scale": "ignored",
        "rect_height": "ignored", "rect_width": "ignored",
    },
}
_TEXT_ATTRIBUTE = {
    **AUDIT["TEXT"], "flags": "read", "attribute_type": "read",  # invisible, constant; multiline
    "tag": "ignored", "field_length": "ignored", "lock_position": "ignored",
}
AUDIT["ATTRIB"] = _TEXT_ATTRIBUTE
AUDIT["ATTDEF"] = {**_TEXT_ATTRIBUTE, "prompt": "ignored"}

_HANDLED = (dxf_extract.GEOMETRY_TYPES | dxf_extract.TEXT_TYPES | dxf_extract.HATCH_TYPES) - {"ARCALIGNEDTEXT"}


def _attributes(kind: str) -> set[str]:
    return set(factory.ENTITY_CLASSES[kind].DXFATTRIBS._attribs)


@pytest.mark.parametrize("kind", sorted(_HANDLED | {"VERTEX"}))
def test_every_attribute_is_classified(kind: str) -> None:
    classified = {**_COMMON, **AUDIT[kind]}
    missing = _attributes(kind) - set(classified)
    stale = set(AUDIT[kind]) - _attributes(kind)
    assert not missing, f"{kind}: decide whether these change the drawn geometry: {sorted(missing)}"
    assert not stale, f"{kind}: no longer ezdxf attributes: {sorted(stale)}"
    assert set(classified.values()) <= {"read", "ignored", "declines"}


def test_arcalignedtext_has_no_ezdxf_class_and_declines() -> None:
    assert "ARCALIGNEDTEXT" not in factory.ENTITY_CLASSES
    assert "ARCALIGNEDTEXT" in dxf_extract.TEXT_TYPES


def _attrib(doc):
    """An ATTRIB on an INSERT of a block holding only a template ATTDEF (which declines)."""
    doc.blocks.new("TAGGED").add_attdef("T", (0, 0))
    insert = doc.modelspace().add_blockref("TAGGED", (0, 0))
    return insert.add_attrib("T", "l", (0, 0), dxfattribs={"style": "GLYPH", "height": 7})


def _drawing(kind: str, attribute: str | None):
    """A drawing whose one drawn entity is a ``kind``, with ``attribute`` set away from its default.

    With ``attribute`` None the entity is left as made: the baseline, which must be a record.
    """
    doc = ezdxf.new("R2018")
    doc.styles.add("GLYPH", font="carriertext.ttf")
    msp = doc.modelspace()
    doc.blocks.new("B").add_line((0, 0), (1, 0))
    text = {"style": "GLYPH", "height": 7}
    makers = {
        "LINE": lambda: msp.add_line((0, 0), (1, 0)),
        "ARC": lambda: msp.add_arc((0, 0), 1, 0, 90),
        "CIRCLE": lambda: msp.add_circle((0, 0), 1),
        "LWPOLYLINE": lambda: msp.add_lwpolyline([(0, 0), (1, 0), (1, 1)]),
        "POLYLINE": lambda: msp.add_polyline2d([(0, 0), (1, 0), (1, 1)]),
        "VERTEX": lambda: msp.add_polyline2d([(0, 0), (1, 0), (1, 1)]),
        "TEXT": lambda: msp.add_text("l", dxfattribs=text),
        "ATTDEF": lambda: msp.add_attdef("T", (0, 0), text="l", dxfattribs={**text, "flags": 2}),
        "ATTRIB": lambda: _attrib(doc),
        "MTEXT": lambda: msp.add_mtext("l", dxfattribs={"style": "GLYPH", "char_height": 7}),
        "INSERT": lambda: msp.add_blockref("B", (0, 0)),
        "MPOLYGON": lambda: msp.add_mpolygon(),
        "HATCH": lambda: msp.add_hatch(),
        "ELLIPSE": lambda: msp.add_ellipse((0, 0), (2, 0), 1.0),  # ratio 1: an Arc in lenient mode
        "SPLINE": lambda: msp.add_open_spline([(0, 0), (1, 1), (2, 0), (3, 1)]),
    }
    entity = makers[kind]()
    if kind in ("MPOLYGON", "HATCH"):
        entity.paths.add_polyline_path([(0, 0), (4, 0), (4, 3)], is_closed=True)
    if attribute is not None:
        target = entity.vertices[1].dxf if kind == "VERTEX" else entity.dxf
        value = {"invisible": 1, "offset_vector": (1, 2, 0)}.get(attribute, 0.5)
        setattr(target, attribute, value)
    return doc


# Text kinds only become records once a font map turns them into glyphs, so their
# declining attributes have no record to compare with here.
_TEXT_KINDS = {"TEXT", "MTEXT", "ATTRIB", "ATTDEF"}
_DECLINING = sorted(
    (kind, attribute)
    for kind in sorted((_HANDLED | {"VERTEX"}) - _TEXT_KINDS)
    for attribute, verdict in {**_COMMON, **AUDIT[kind]}.items()
    if verdict == "declines" and attribute in _attributes(kind)
)


@pytest.mark.parametrize(("kind", "attribute"), _DECLINING)
def test_declining_attributes_decline(kind: str, attribute: str) -> None:
    drawn = lambda rows: [row for row in rows if row["record"] == "entity"]
    baseline = dxf_extract.extract_document(_drawing(kind, None), mode="lenient", file_id="audit")
    assert drawn(baseline), (kind, "the baseline must be a record, or the check proves nothing", baseline)
    rows = dxf_extract.extract_document(_drawing(kind, attribute), mode="lenient", file_id="audit")
    assert not drawn(rows), (kind, attribute, rows)


_R12 = Path(__file__).resolve().parents[1] / "fixtures" / "r12_group38.dxf"


def test_r12_fixture_stores_z_only_in_group_38() -> None:
    """Guards the fixture: handles A1 to A4 carry group 38 and no group 30."""
    text = _R12.read_text(encoding="utf-8")
    entities = text.split(" 0\nCIRCLE\n", 1)[1]
    for handle in ("A1", "A2", "A3", "A4"):
        record = entities.split(f" 5\n{handle}\n", 1)[1].split("  0\n", 1)[0]
        assert " 38\n5.0\n" in record and " 30\n" not in record, handle
    assert "AC1009" in text


def test_r12_group_38_height_is_read_never_dropped() -> None:
    rows = dxf_extract.extract_path(_R12, file_id="r12")
    by_handle = {row["provenance"]["handle"]: row for row in rows}
    # Group 38 alone: the height is the elevation.
    for handle in ("A1", "A2"):
        assert by_handle[handle]["dimension"] == {"space": "2d+elevation", "elevation": 5.0}
    # An INSERT's group 38 lifts its block.
    (inside,) = [row for row in rows if row["provenance"]["blockPath"] == ["B"]]
    assert inside["dimension"] == {"space": "2d+elevation", "elevation": 5.0}
    # An explicit z wins over group 38, as AutoCAD reads R12.
    assert by_handle["A5"]["dimension"] == {"space": "2d+elevation", "elevation": 2.5}
    # TEXT declines without a font map; its height is checked with glyphs.
    assert by_handle["A3"]["id"] == "ID_TextEntity"
