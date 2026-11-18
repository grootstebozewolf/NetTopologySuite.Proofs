"""Totality: the extractor considers exactly the entities a drawing draws.

The extractor yields one row (a record or a named decline) per considered
entity. Two relations are checked on random drawings:

* Counts: the types of the considered entities equal every block
  instance's content from ezdxf's block table (MINSERT cells through
  ``multi_insert()``). Where nothing is restored, that walk is checked to
  equal ezdxf's ``recursive_decompose``.
* Instances: each record's source entity and placed geometry match one
  drawn instance, placed by composing ezdxf's insert matrices. Geometry
  is compared for lines, circles, arcs, polylines, 2D polylines and hatch
  paths (vertices, and the midpoint of every bulged segment, which pins
  the arc's direction under a mirror) and spline control points; other
  kinds are matched by source entity.

Where the extractor counts differently on purpose, the oracle restores the
difference by name (``_RESTORED``) instead of leaving it out of the check:

* ATTDEF: ezdxf skips every one; the extractor considers them (a constant
  one is drawn, any other declines as a template).
* INSERT that is not a similarity (unequal scales, or extrusion not +/-Z),
  of an empty block, or of a block that contains itself: one considered
  INSERT that declines, plus its attached ATTRIBs, which do not depend on
  the INSERT's link; ezdxf expands it, yields nothing, or recurses
  without end, respectively (the last reported upstream:
  https://github.com/mozman/ezdxf/issues/1475).
* DIMENSION, LEADER: one considered entity that declines; ezdxf expands
  them into their lines, solids and text.
"""

from __future__ import annotations

import math
import random
from collections import Counter

import ezdxf
import pytest
from ezdxf.disassemble import recursive_decompose
from ezdxf.math import Matrix44

import dxf_extract

# Kept whole: the extractor considers each of these once and declines it.
_KEPT_WHOLE = ("DIMENSION", "LEADER")
_RESTORED = ("ATTDEF", "non-similarity INSERT", "empty-block INSERT", "cyclic INSERT", *_KEPT_WHOLE)


def _whole_insert(doc, insert, stack: tuple[str, ...]) -> bool:
    """An INSERT the extractor considers as one entity instead of entering its block."""
    name = insert.dxf.name
    if name in stack:
        return True  # cyclic
    ex, ey, ez = insert.dxf.extrusion
    if abs(ex) > 1e-9 or abs(ey) > 1e-9:
        return True  # tilted
    if not math.isclose(abs(insert.dxf.xscale), abs(insert.dxf.yscale), rel_tol=1e-9):
        return True  # not a similarity
    return not any(entity.dxftype() != "ENDBLK" for entity in doc.blocks.get(name))  # empty


def _grid(insert):
    return list(insert.multi_insert()) if int(getattr(insert, "mcount", 1) or 1) > 1 else [insert]


def _drawn_types(doc, entities, stack: tuple[str, ...] = ()) -> Counter:
    """The count oracle: every block instance's content, from ezdxf's block table, with
    MINSERT cells from ``multi_insert()`` and the named restorations.

    It walks the block definitions, not ezdxf's placed ``virtual_entities()``: inside a
    block inserted with x and y scaled but z not, ezdxf cannot keep a tilted INSERT as an
    INSERT (its frame is sheared out of the plane) and explodes it early, while the
    extractor judges every INSERT by its own scales and extrusion. Mirroring alone, or a
    uniform x, y and z scale, keeps it an INSERT.
    """
    found: Counter = Counter()
    for entity in entities:
        kind = entity.dxftype()
        if kind == "ENDBLK":
            continue
        if kind != "INSERT":
            found[kind] += 1
            continue
        for copy in _grid(entity):
            # Attached attributes are drawn whether or not the INSERT's block is entered.
            found["ATTRIB"] += len(copy.attribs)
            if _whole_insert(doc, copy, stack):
                found["INSERT"] += 1
                continue
            found += _drawn_types(doc, doc.blocks.get(copy.dxf.name), stack + (copy.dxf.name,))
    return found


def _random_doc(rng: random.Random, *, wide: bool = False):
    """A random drawing. ``wide`` adds the entity kinds and inserts the restorations cover."""
    doc = ezdxf.new("R2018", setup=wide)
    names: list[str] = []

    def fill(layout, depth: int) -> None:
        for _ in range(rng.randint(1, 5)):
            pick = rng.random()
            x, y = rng.uniform(-20, 20), rng.uniform(-20, 20)
            if wide and rng.random() < 0.35:
                extra = rng.randrange(9)
                if extra == 0:
                    layout.add_ellipse((x, y), (3, 1), 0.5)
                elif extra == 1:
                    layout.add_open_spline([(x, y), (x + 1, y + 2), (x + 3, y + 1), (x + 4, y)])
                elif extra == 2:
                    layout.add_polyline2d(
                        [(x, y, 0.5), (x + 2, y, 0.0), (x + 2, y + 1, -0.3)], format="xyb", close=rng.random() < 0.5
                    )
                elif extra == 3:
                    layout.add_hatch().paths.add_polyline_path(
                        [(x, y, 0.0), (x + 4, y, 0.6), (x + 4, y + 3, 0.0)], is_closed=True
                    )
                elif extra == 4:
                    layout.add_mtext("m", dxfattribs={"insert": (x, y)})
                elif extra == 5:
                    layout.add_solid([(x, y), (x + 1, y), (x, y + 1)])
                elif extra == 6:
                    layout.add_leader([(x, y), (x + 2, y + 2), (x + 4, y + 2)])
                elif extra == 7 and depth == 0:
                    layout.add_linear_dim(base=(x, y + 3), p1=(x, y), p2=(x + 5, y)).render()
                elif names:
                    # A stretched or tilted INSERT: one considered entity.
                    target = rng.choice(names)
                    if rng.random() < 0.5:
                        whole = layout.add_blockref(target, (x, y), dxfattribs={"xscale": 2, "yscale": 1})
                    else:
                        whole = layout.add_blockref(target, (x, y), dxfattribs={"extrusion": (0, 1, 1)})
                    # Its attributes are still considered, each on its own.
                    for k in range(rng.randint(0, 2)):
                        whole.add_attrib(f"W{k}", "v", (x, y + k))
                continue
            if pick < 0.2:
                layout.add_line((x, y), (x + 1, y + 2))
            elif pick < 0.3:
                layout.add_circle((x, y), 1 + rng.random())
            elif pick < 0.4:
                layout.add_arc((x, y), 2, 10, 200)
            elif pick < 0.5:
                bulge = rng.choice([0.0, 0.0, 0.4, -0.7])
                layout.add_lwpolyline(
                    [(x, y, bulge), (x + 3, y, 0.0), (x + 3, y + 2, -bulge)], format="xyb", close=rng.random() < 0.5
                )
            elif pick < 0.6:
                layout.add_text("t", dxfattribs={"insert": (x, y)})
            elif pick < 0.65:
                layout.add_point((x, y))
            elif pick < 0.75 and depth > 0:
                flags = rng.choice([0, 1, 2])  # plain, invisible, constant
                layout.add_attdef(f"T{rng.randint(0, 3)}", (x, y), text="c", dxfattribs={"flags": flags})
            elif names:
                scale = rng.choice([1.0, 2.5]) * rng.choice([1, -1])
                insert = layout.add_blockref(
                    rng.choice(names), (x, y),
                    dxfattribs={"rotation": rng.uniform(0, 360), "xscale": scale, "yscale": abs(scale)},
                )
                if rng.random() < 0.3:
                    insert.grid(size=(rng.randint(1, 3), rng.randint(1, 3)), spacing=(4, 5))
                for k in range(rng.randint(0, 2)):
                    insert.add_attrib(f"A{k}", "v", (x, y + k), dxfattribs={"flags": rng.choice([0, 0, 1])})
            else:
                layout.add_line((x, y), (x, y + 1))

    for index in range(rng.randint(1, 4)):
        name = f"B{index}"
        fill(doc.blocks.new(name), depth=1)  # inserts only blocks made before it: no cycles here
        names.append(name)
    if wide:
        doc.blocks.new("EMPTY")
        cyclic = doc.blocks.new("LOOP")
        cyclic.add_line((0, 0), (1, 1))
        cyclic.add_blockref("LOOP", (2, 2))
        names += ["EMPTY", "LOOP"]
    fill(doc.modelspace(), depth=0)
    return doc


@pytest.mark.slow
@pytest.mark.parametrize("wide", [False, True])
@pytest.mark.parametrize("seed", range(80))
def test_considered_entities_match_ezdxfs_expansion(seed: int, wide: bool) -> None:
    doc = _random_doc(random.Random(seed), wide=wide)
    seen: list[str] = []
    rows = dxf_extract.extract_document(doc, file_id="total", on_considered=seen.append)
    assert len(seen) == len(rows)
    assert Counter(seen) == _drawn_types(doc, doc.modelspace())


@pytest.mark.slow
@pytest.mark.parametrize("seed", range(80))
def test_count_oracle_agrees_with_recursive_decompose(seed: int) -> None:
    """Without the restored cases, the one-level walk is exactly ezdxf's recursive_decompose."""
    doc = _random_doc(random.Random(seed))
    drawn = _drawn_types(doc, doc.modelspace())
    drawn["ATTDEF"] = 0
    assert +drawn == Counter(entity.dxftype() for entity in recursive_decompose(doc.modelspace()))


def test_minsert_grid_is_one_copy_per_cell() -> None:
    doc = ezdxf.new("R2018")
    doc.blocks.new("B").add_line((0, 0), (1, 0))
    insert = doc.modelspace().add_blockref("B", (0, 0), dxfattribs={"rotation": 30})
    insert.grid(size=(2, 3), spacing=(5, 7))  # 2 rows 5 apart, 3 columns 7 apart
    rows = dxf_extract.extract_document(doc, file_id="grid")
    assert [row["provenance"]["blockPath"] for row in rows] == [[f"B#{k}"] for k in range(6)]
    offsets = sorted(
        (round(row["placement"]["links"][0]["translate"][0], 9), round(row["placement"]["links"][0]["translate"][1], 9))
        for row in rows
    )
    c, s = math.cos(math.radians(30)), math.sin(math.radians(30))
    expected = sorted(
        (round(col * 7 * c - row * 5 * s, 9), round(col * 7 * s + row * 5 * c, 9)) for row in range(2) for col in range(3)
    )
    assert offsets == pytest.approx(expected)


# --- instance level: the same source entities, in the same places -----------------------

def _place(point, links) -> tuple[float, float]:
    x, y = point
    for link in links:
        if link["reflect"]:
            x = -x
        x, y = x * link["scale"], y * link["scale"]
        angle = math.radians(link["rotate"])
        x, y = math.cos(angle) * x - math.sin(angle) * y, math.sin(angle) * x + math.cos(angle) * y
        x, y = x + link["translate"][0], y + link["translate"][1]
    return (x, y)


def _ours(row: dict) -> list[float] | None:
    """Placed geometry of a record, flattened; None for a decline."""
    if row["record"] != "entity":
        return None
    links, params = row["placement"]["links"], row["params"]
    scale = math.prod(link["scale"] for link in links)
    if row["kind"] == "Chord":
        return [*_place(params["start"], links), *_place(params["end"], links)]
    if row["kind"] in ("Circle", "Arc"):
        return [*_place(params["center"], links), params["radius"] * scale]
    if row["kind"] == "BulgePolyline":
        return _chain(params["segments"], not params["closed"], links)
    if row["kind"] == "Compound":
        segments = []
        for member in params["members"]:
            if member["kind"] == "Chord":
                segments.append({**member["params"], "bulge": 0.0})
            else:
                segments.extend(member["params"]["segments"])
        closed = segments[-1]["end"] == segments[0]["start"]
        return _chain(segments, not closed, links)
    if row["kind"] == "Ring":
        return [v for contour in params["contours"] for v in _chain(contour, False, links)]
    if row["kind"] in ("Bezier", "BSpline"):
        return [v for point in params["controlPoints"] for v in _place(point, links)]
    return None  # other kinds are matched by source entity only


def _bulge_mid(a, b, bulge: float) -> tuple[float, float]:
    """Midpoint of a bulge arc from ``a`` to ``b``: off the chord midpoint by the sagitta, to its right."""
    dx, dy = b[0] - a[0], b[1] - a[1]
    return ((a[0] + b[0]) / 2 + bulge * dy / 2, (a[1] + b[1]) / 2 - bulge * dx / 2)


def _chain(segments, open_end: bool, links) -> list[float]:
    """Each segment's start, its arc midpoint when it bulges, and the last end when open; all placed."""
    points = []
    for segment in segments:
        points.append(segment["start"])
        if segment["bulge"]:
            points.append(_bulge_mid(segment["start"], segment["end"], segment["bulge"]))
    if open_end:
        points.append(segments[-1]["end"])
    return [v for point in points for v in _place(point, links)]


def _geometry(entity, m) -> list[float] | None:
    """Placed geometry of a drawn entity under matrix ``m``; None for what the extractor declines."""
    kind = entity.dxftype()
    if kind == "LINE":
        start, end = m.transform_vertices([entity.dxf.start, entity.dxf.end])
        return [start.x, start.y, end.x, end.y]
    if kind in ("CIRCLE", "ARC"):
        (centre,) = m.transform_vertices([entity.ocs().to_wcs(entity.dxf.center)])
        return [centre.x, centre.y, entity.dxf.radius * m.transform_direction((1, 0, 0)).magnitude]
    if kind == "LWPOLYLINE":
        vertices = [(x, y, b) for x, y, b in entity.get_points("xyb")]
        return _their_chain(vertices, bool(entity.closed), entity.ocs(), entity.dxf.elevation, m)
    if kind == "POLYLINE":
        vertices = [(v.dxf.location.x, v.dxf.location.y, v.dxf.get("bulge", 0.0)) for v in entity.vertices]
        return _their_chain(vertices, bool(entity.is_closed), entity.ocs(), entity.dxf.elevation.z, m)
    if kind == "HATCH":
        out = []
        for path in entity.paths:
            out += _their_chain(list(path.vertices), True, entity.ocs(), entity.dxf.elevation.z, m)
        return out
    if kind == "SPLINE":
        points = m.transform_vertices(entity.control_points)
        return [v for point in points for v in (point.x, point.y)]
    return None


def _their_chain(vertices, closed: bool, ocs, z: float, m) -> list[float]:
    """The same points from ezdxf's entity: vertices and bulge midpoints in its OCS, then to WCS."""
    count = len(vertices)
    points = []
    for index in range(count if closed else count - 1):
        (x0, y0, bulge), (x1, y1, _b) = vertices[index], vertices[(index + 1) % count]
        points.append((x0, y0))
        if bulge:
            points.append(_bulge_mid((x0, y0), (x1, y1), bulge))
    if not closed:
        points.append(vertices[-1][:2])
    placed = m.transform_vertices([ocs.to_wcs((x, y, z)) for x, y in points])
    return [v for point in placed for v in (point.x, point.y)]


def _source(entity) -> str:
    origin = getattr(entity, "origin_of_copy", None)
    return str((origin or entity).dxf.get("handle", ""))


def _instances(doc, entities, m, out: list, stack: tuple[str, ...] = ()) -> None:
    """The position oracle: every drawn instance as (type, source handle, geometry).

    Each INSERT and each MINSERT cell (ezdxf's ``multi_insert``) contributes ezdxf's own
    ``matrix44()``, composed by matrix product with the matrices above it. This avoids
    ``recursive_decompose``, which folds a nested INSERT into one through
    ``Insert.transform``: ezdxf 1.4.4 then keeps a nested grid's spacing unscaled and its
    rows unmirrored (pinned below). ATTDEFs are drawn instances too; ezdxf skips them.
    """
    for entity in entities:
        if entity.dxftype() == "ENDBLK":
            continue
        if entity.dxftype() != "INSERT":
            out.append((entity.dxftype(), _source(entity), _geometry(entity, m)))
            continue
        for copy in _grid(entity):
            # Attached attributes are already in the space the INSERT sits in, and are
            # drawn whether or not the INSERT's block is entered.
            for attrib in copy.attribs:
                out.append(("ATTRIB", _source(attrib), None))
            if _whole_insert(doc, copy, stack):
                out.append(("INSERT", _source(copy), None))
                continue
            _instances(doc, doc.blocks.get(copy.dxf.name), copy.matrix44() @ m, out, stack + (copy.dxf.name,))


@pytest.mark.parametrize(
    ("outer", "theirs_agree"),
    [({"xscale": 2, "yscale": 2}, False), ({"xscale": -1, "rotation": 30}, False), ({"rotation": 30}, True)],
)
def test_recursive_decompose_misplaces_a_nested_grid(outer: dict, theirs_agree: bool) -> None:
    """Pins two ezdxf 1.4.4 defects the position oracle avoids. In a scaled block a nested
    grid keeps its unscaled spacing; in a mirrored one its rows run the wrong way. The
    extractor matches the matrix composition; if ezdxf fixes this, this goes red.
    Reported upstream: https://github.com/mozman/ezdxf/issues/1474"""
    doc = ezdxf.new("R2018")
    doc.blocks.new("B").add_line((0, 0), (1, 0))
    doc.blocks.new("O").add_blockref("B", (3, 4), dxfattribs={"rotation": 20}).grid(size=(2, 2), spacing=(4, 5))
    doc.modelspace().add_blockref("O", (100, 0), dxfattribs=outer)
    drawn: list = []
    _instances(doc, doc.modelspace(), Matrix44(), drawn)
    rows = dxf_extract.extract_document(doc, file_id="pin")
    ours = sorted(round(v, 6) for row in rows for v in _place(row["params"]["start"], row["placement"]["links"]))
    oracle = sorted(round(v, 6) for _kind, _src, geometry in drawn for v in geometry[:2])
    theirs = sorted(
        round(v, 6) for e in recursive_decompose(doc.modelspace()) for v in (e.dxf.start.x, e.dxf.start.y)
    )
    assert ours == pytest.approx(oracle)
    assert (theirs == pytest.approx(oracle)) is theirs_agree


@pytest.mark.slow
@pytest.mark.parametrize("wide", [False, True])
@pytest.mark.parametrize("seed", range(80))
def test_records_are_the_drawn_instances_in_their_places(seed: int, wide: bool) -> None:
    doc = _random_doc(random.Random(seed), wide=wide)
    seen: list[str] = []
    rows = dxf_extract.extract_document(doc, file_id="total", on_considered=seen.append)

    drawn: list = []
    _instances(doc, doc.modelspace(), Matrix44(), drawn)
    theirs: dict[tuple[str, str], list] = {}
    for kind, source, geometry in drawn:
        theirs.setdefault((kind, source), []).append(geometry)

    for kind, row in zip(seen, rows):
        key = (kind, row["provenance"]["handle"])
        mine = _ours(row)
        candidates = theirs.get(key, [])
        match = next(
            (
                index
                for index, other in enumerate(candidates)
                if (mine is None) == (other is None)
                and (mine is None or (len(mine) == len(other) and mine == pytest.approx(other, abs=1e-6)))
            ),
            None,
        )
        assert match is not None, (key, mine, candidates)
        candidates.pop(match)
    assert all(not left for left in theirs.values()), {k: v for k, v in theirs.items() if v}
