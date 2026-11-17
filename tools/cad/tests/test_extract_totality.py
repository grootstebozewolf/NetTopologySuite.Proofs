"""Totality: the extractor considers exactly the entities a drawing draws.

The extractor yields one row (a record or a named decline) per considered
entity. Here the considered set is checked against an independent
enumeration: ezdxf's ``recursive_decompose``, which expands every INSERT,
including MINSERT grids and attached ATTRIBs. ezdxf skips every ATTDEF, so
the ATTDEFs of each drawn block instance are added back: the extractor
considers them too (a constant one is drawn, any other declines by name).
"""

from __future__ import annotations

import random
from collections import Counter

import ezdxf
import pytest
from ezdxf.disassemble import recursive_decompose

import dxf_extract


def _attdefs(doc, entity) -> Counter:
    """ATTDEFs drawn under one INSERT, once per grid copy, nested blocks included."""
    found: Counter = Counter()
    if entity.dxftype() != "INSERT":
        return found
    copies = int(getattr(entity, "mcount", 1) or 1)
    for child in doc.blocks.get(entity.dxf.name):
        if child.dxftype() == "ATTDEF":
            found["ATTDEF"] += copies
        elif child.dxftype() == "INSERT":
            for kind, number in _attdefs(doc, child).items():
                found[kind] += copies * number
    return found


def _random_doc(rng: random.Random):
    doc = ezdxf.new("R2018")
    names: list[str] = []

    def fill(layout, depth: int) -> None:
        for _ in range(rng.randint(1, 5)):
            pick = rng.random()
            x, y = rng.uniform(-20, 20), rng.uniform(-20, 20)
            if pick < 0.2:
                layout.add_line((x, y), (x + 1, y + 2))
            elif pick < 0.3:
                layout.add_circle((x, y), 1 + rng.random())
            elif pick < 0.4:
                layout.add_arc((x, y), 2, 10, 200)
            elif pick < 0.5:
                layout.add_lwpolyline([(x, y), (x + 3, y), (x + 3, y + 2)], close=rng.random() < 0.5)
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
        fill(doc.blocks.new(name), depth=1)  # may insert only blocks made before it: no cycles
        names.append(name)
    fill(doc.modelspace(), depth=0)
    return doc


@pytest.mark.parametrize("seed", range(80))
def test_considered_entities_match_ezdxfs_decomposition(seed: int) -> None:
    doc = _random_doc(random.Random(seed))
    seen: list[str] = []
    rows = dxf_extract.extract_document(doc, file_id="total", on_considered=seen.append)
    assert len(seen) == len(rows)

    drawn = Counter(entity.dxftype() for entity in recursive_decompose(doc.modelspace()))
    for entity in doc.modelspace():
        drawn += _attdefs(doc, entity)
    assert Counter(seen) == drawn


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
    import math

    c, s = math.cos(math.radians(30)), math.sin(math.radians(30))
    expected = sorted(
        (round(col * 7 * c - row * 5 * s, 9), round(col * 7 * s + row * 5 * c, 9)) for row in range(2) for col in range(3)
    )
    assert offsets == pytest.approx(expected)
