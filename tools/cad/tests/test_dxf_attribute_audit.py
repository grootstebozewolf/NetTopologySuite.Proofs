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
* lenient: a non-default value makes the entity decline in strict mode; lenient
  keeps it and names what it left out in the record's ``lenient`` field.
"""

from __future__ import annotations

from pathlib import Path

import ezdxf
import pytest
from ezdxf.entities import factory

import dxf_extract
from test_text_glyphs import ttf  # noqa: F401

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
    "LINE": {"start": "read", "end": "read", "thickness": "lenient"},
    "ARC": {"center": "read", "radius": "read", "start_angle": "read", "end_angle": "read",
            "thickness": "lenient", "elevation": _LEGACY_ELEVATION},
    "CIRCLE": {"center": "read", "radius": "read", "thickness": "lenient", "elevation": _LEGACY_ELEVATION},
    "ELLIPSE": {"center": "read", "major_axis": "read", "ratio": "read", "start_param": "read", "end_param": "read"},
    "SPLINE": {
        "degree": "read", "flags": "read",  # periodic
        "n_control_points": "ignored", "n_fit_points": "ignored", "n_knots": "ignored",  # counts
        "control_point_tolerance": "ignored", "knot_tolerance": "ignored", "fit_tolerance": "ignored",
        "start_tangent": "ignored", "end_tangent": "ignored",  # fit-point splines decline
    },
    "LWPOLYLINE": {"const_width": "lenient", "count": "ignored", "elevation": "read", "flags": "read",
                   "thickness": "lenient"},
    "POLYLINE": {
        "default_start_width": "lenient", "default_end_width": "lenient", "elevation": "read",
        "flags": "read", "thickness": "lenient",
        # Meshes and fitted polylines decline, so these never shape a record.
        "m_count": "ignored", "n_count": "ignored", "m_smooth_density": "ignored",
        "n_smooth_density": "ignored", "smooth_type": "ignored",
    },
    "VERTEX": {
        "location": "read", "bulge": "read", "start_width": "lenient", "end_width": "lenient",
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
        "text_generation_flag": "read", "thickness": "lenient", "elevation": _LEGACY_ELEVATION,
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
    assert set(classified.values()) <= {"read", "ignored", "declines", "lenient"}


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


def _classified(wanted: str) -> list[tuple[str, str]]:
    return sorted(
        (kind, attribute)
        for kind in sorted(_HANDLED | {"VERTEX"})
        for attribute, verdict in {**_COMMON, **AUDIT[kind]}.items()
        if verdict == wanted and attribute in _attributes(kind)
    )


_DECLINING = _classified("declines")
_LENIENT = _classified("lenient")
_drawn = lambda rows: [row for row in rows if row["record"] == "entity"]


def _extract(kind: str, attribute: str | None, mode: str, ttf: str) -> list[dict]:
    fonts = {"carriertext.ttf": ttf}
    return dxf_extract.extract_document(_drawing(kind, attribute), mode=mode, file_id="audit", fonts=fonts)


# A "lenient" attribute declines in strict mode only; lenient is test_lenient_attributes_are_named.
@pytest.mark.parametrize(
    ("kind", "attribute", "mode"),
    [(*case, mode) for case in _DECLINING for mode in ("strict", "lenient")] + [(*case, "strict") for case in _LENIENT],
)
def test_declining_attributes_decline(kind: str, attribute: str, mode: str, ttf) -> None:
    baseline = _extract(kind, None, "lenient", ttf)
    assert _drawn(baseline), (kind, "the baseline must be a record, or the check proves nothing", baseline)
    # Strict declines more, so the lenient baseline being a record is not enough there.
    if mode == "strict" and not _drawn(_extract(kind, None, "strict", ttf)):
        pytest.skip(f"{kind} is no strict record even without {attribute}")
    rows = _extract(kind, attribute, mode, ttf)
    assert not _drawn(rows), (kind, attribute, rows)


@pytest.mark.parametrize(("kind", "attribute"), _LENIENT)
def test_lenient_attributes_are_named(kind: str, attribute: str, ttf) -> None:
    """Lenient keeps the record, unchanged but for a note naming what it left out."""
    (baseline,) = _drawn(_extract(kind, None, "lenient", ttf))
    (row,) = _drawn(_extract(kind, attribute, "lenient", ttf))
    ignored = "thickness" if attribute == "thickness" else "width"
    assert row.pop("lenient") == [{"ignored": ignored, "value": 0.5}]
    row["provenance"]["handle"] = baseline["provenance"]["handle"]
    assert row == baseline
    assert "lenient" not in baseline


_R12 = Path(__file__).resolve().parents[1] / "fixtures" / "r12_group38.dxf"


def test_r12_fixture_stores_z_only_in_group_38() -> None:
    """Guards the fixture: handles A1 to A4 carry group 38 and no group 30."""
    text = _R12.read_text(encoding="utf-8")
    entities = text.split(" 0\nCIRCLE\n", 1)[1]
    for handle in ("A1", "A2", "A3", "A4"):
        record = entities.split(f" 5\n{handle}\n", 1)[1].split("  0\n", 1)[0]
        assert " 38\n5.0\n" in record and " 30\n" not in record, handle
    assert "AC1009" in text


def test_r12_group_38_height_is_read_never_dropped(ttf) -> None:
    # The file has no STYLE table, so TEXT uses the default style and its "txt" font.
    rows = dxf_extract.extract_path(_R12, file_id="r12", fonts={"txt.shx": ttf})
    by_handle = {row["provenance"]["handle"]: row for row in rows}
    # Group 38 alone: the height is the elevation.
    for handle in ("A1", "A2"):
        assert by_handle[handle]["dimension"] == {"space": "2d+elevation", "elevation": 5.0}
    # An INSERT's group 38 lifts its block.
    (inside,) = [row for row in rows if row["provenance"]["blockPath"] == ["B"]]
    assert inside["dimension"] == {"space": "2d+elevation", "elevation": 5.0}
    # An explicit z wins over group 38, as AutoCAD reads R12.
    assert by_handle["A5"]["dimension"] == {"space": "2d+elevation", "elevation": 2.5}
    # TEXT: its glyph outlines sit at the group 38 height.
    assert by_handle["A3"]["kind"] == "Compound"
    assert by_handle["A3"]["dimension"] == {"space": "2d+elevation", "elevation": 5.0}
