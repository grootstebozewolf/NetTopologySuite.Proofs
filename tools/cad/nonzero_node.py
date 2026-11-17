#!/usr/bin/env python3
"""Nonzero-winding fill of closed polylines that cross, touch or overlap.

Input is a list of rings (vertex lists, closed implicitly) in any
orientation. Output is the region where the summed winding number is not
zero, as polygons: a counter-clockwise shell with clockwise holes.

Every decision is exact rational arithmetic on the input numbers:

1. Node. Each edge is split at every crossing with another edge and at
   every endpoint of another edge that lies on it, so two sub-edges share
   either nothing, an endpoint, or their whole length.
2. Label. For each distinct sub-edge the winding number is taken just to
   its left and just to its right: at the midpoint moved by a symbolic
   infinitesimal along the normal, so the probe never sits on an edge.
3. Keep. A sub-edge is boundary when exactly one side is zero. It is
   directed with the filled side on its left.
4. Stitch. At a vertex the boundary continues along the first outgoing
   edge clockwise from the way it came, which closes the filled wedge it
   was following. A walk that returns to a vertex is cut there, so a hole
   touching its shell is its own ring. Rings may meet at a vertex and do
   not cross.
5. Assemble. Counter-clockwise rings are shells and clockwise rings are
   holes. A hole goes to the smallest shell around the fill next to it.

Vertices made by noding are kept, also where the boundary runs straight
through them: another ring may touch there. Output vertices that are
crossing points are rational; the caller rounds them.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Iterable

QPoint = tuple[Fraction, Fraction]
QEdge = tuple[QPoint, QPoint]
Polygon = tuple[list[QPoint], list[list[QPoint]]]


def _cross(ax: Fraction, ay: Fraction, bx: Fraction, by: Fraction) -> Fraction:
    return ax * by - ay * bx


def _orient(a: QPoint, b: QPoint, c: QPoint) -> Fraction:
    return _cross(b[0] - a[0], b[1] - a[1], c[0] - a[0], c[1] - a[1])


def _sign(value: Fraction) -> int:
    return (value > 0) - (value < 0)


def _within(a: QPoint, b: QPoint, p: QPoint) -> bool:
    return min(a[0], b[0]) <= p[0] <= max(a[0], b[0]) and min(a[1], b[1]) <= p[1] <= max(a[1], b[1])


def _ring_edges(ring: list[QPoint]) -> list[QEdge]:
    return [(a, b) for a, b in zip(ring, ring[1:] + ring[:1]) if a != b]


def _float_box(edge: QEdge) -> tuple[float, float, float, float]:
    (ax, ay), (bx, by) = edge
    return (float(min(ax, bx)), float(min(ay, by)), float(max(ax, bx)), float(max(ay, by)))


def node(edges: list[QEdge]) -> list[QEdge]:
    """Split every edge at its contacts with the others. Direction is kept."""
    cuts: list[list[QPoint]] = [[] for _ in edges]
    boxes = [_float_box(edge) for edge in edges]
    order = sorted(range(len(edges)), key=lambda i: boxes[i][0])
    for position, i in enumerate(order):
        a, b = edges[i]
        box = boxes[i]
        # A float box is the exact box rounded, so widen the reject test by a relative margin.
        margin = 1e-9 * (abs(box[0]) + abs(box[2]) + abs(box[1]) + abs(box[3]) + 1e-300)
        for j in order[position + 1 :]:
            other = boxes[j]
            if other[0] > box[2] + margin:
                break
            if other[1] > box[3] + margin or other[3] < box[1] - margin:
                continue
            c, d = edges[j]
            o1, o2 = _sign(_orient(a, b, c)), _sign(_orient(a, b, d))
            o3, o4 = _sign(_orient(c, d, a)), _sign(_orient(c, d, b))
            if o1 * o2 < 0 and o3 * o4 < 0:
                t = _cross(c[0] - a[0], c[1] - a[1], d[0] - c[0], d[1] - c[1]) / _cross(
                    b[0] - a[0], b[1] - a[1], d[0] - c[0], d[1] - c[1]
                )
                point = (a[0] + t * (b[0] - a[0]), a[1] + t * (b[1] - a[1]))
                cuts[i].append(point)
                cuts[j].append(point)
                continue
            if o1 == 0 and _within(a, b, c):
                cuts[i].append(c)
            if o2 == 0 and _within(a, b, d):
                cuts[i].append(d)
            if o3 == 0 and _within(c, d, a):
                cuts[j].append(a)
            if o4 == 0 and _within(c, d, b):
                cuts[j].append(b)
    pieces: list[QEdge] = []
    for (a, b), points in zip(edges, cuts):
        dx, dy = b[0] - a[0], b[1] - a[1]
        along = sorted({a, b, *points}, key=lambda p: (p[0] - a[0]) * dx + (p[1] - a[1]) * dy)
        pieces.extend(zip(along, along[1:]))
    return pieces


class _Winding:
    """Winding number of a fixed edge set about symbolically displaced points."""

    def __init__(self, edges: Iterable[QEdge]) -> None:
        self.edges = list(edges)
        self.spans = [(float(min(a[1], b[1])), float(max(a[1], b[1]))) for a, b in self.edges]

    def beside(self, m: QPoint, n: QPoint) -> int:
        """Winding number at ``m + eps * n`` for an infinitesimal ``eps > 0``."""
        my = float(m[1])
        margin = 1e-9 * (abs(my) + 1e-300)
        total = 0
        for (a, b), (low, high) in zip(self.edges, self.spans):
            if high < my - margin or low > my + margin:
                continue
            a_low = a[1] < m[1] or (a[1] == m[1] and n[1] >= 0)
            b_low = b[1] < m[1] or (b[1] == m[1] and n[1] >= 0)
            if a_low == b_low:
                continue
            side = _sign(_orient(a, b, m)) or _sign(_cross(b[0] - a[0], b[1] - a[1], n[0], n[1]))
            if a_low and side > 0:
                total += 1
            elif b_low and side < 0:
                total -= 1
        return total


def _left_normal(p: QPoint, q: QPoint) -> QPoint:
    return (p[1] - q[1], q[0] - p[0])


def _mid(p: QPoint, q: QPoint) -> QPoint:
    return ((p[0] + q[0]) / 2, (p[1] + q[1]) / 2)


def boundary_edges(edges: list[QEdge]) -> list[QEdge]:
    """Sub-edges between zero and nonzero winding, filled side on the left."""
    winding = _Winding(edges)
    kept: list[QEdge] = []
    for p, q in sorted({(min(a, b), max(a, b)) for a, b in node(edges)}):
        m = _mid(p, q)
        n = _left_normal(p, q)
        left = winding.beside(m, n) != 0
        right = winding.beside(m, (-n[0], -n[1])) != 0
        if left != right:
            kept.append((p, q) if left else (q, p))
    return kept


def _turn_rank(back: QPoint, direction: QPoint) -> tuple[int, QPoint]:
    cross = _cross(back[0], back[1], direction[0], direction[1])
    dot = back[0] * direction[0] + back[1] * direction[1]
    return (1 if cross < 0 or (cross == 0 and dot < 0) else 0, direction)


def _first_clockwise(back: QPoint, directions: list[QPoint]) -> int:
    """Index of the direction reached first turning clockwise from ``back``."""
    best = 0
    best_rank = _turn_rank(back, directions[0])
    for index, direction in enumerate(directions[1:], start=1):
        rank = _turn_rank(back, direction)
        later = rank[0] > best_rank[0] or (
            rank[0] == best_rank[0] and _cross(best_rank[1][0], best_rank[1][1], direction[0], direction[1]) > 0
        )
        if later:
            best, best_rank = index, rank
    return best


def stitch(edges: list[QEdge]) -> list[list[QPoint]]:
    """Closed rings from directed boundary edges."""
    outgoing: dict[QPoint, list[int]] = {}
    for index, (p, _q) in enumerate(edges):
        outgoing.setdefault(p, []).append(index)
    follow: list[int] = []
    for p, q in edges:
        options = outgoing.get(q)
        if not options:
            raise ValueError("boundary does not close")
        directions = [(edges[k][1][0] - q[0], edges[k][1][1] - q[1]) for k in options]
        follow.append(options[_first_clockwise((p[0] - q[0], p[1] - q[1]), directions)])
    if sorted(follow) != list(range(len(edges))):
        raise ValueError("boundary does not pair up")
    rings: list[list[QPoint]] = []
    seen = [False] * len(edges)
    for start in range(len(edges)):
        if seen[start]:
            continue
        ring = []
        index = start
        while not seen[index]:
            seen[index] = True
            ring.append(edges[index][0])
            index = follow[index]
        # The walk keeps a filled wedge on its left, so a hole that touches
        # its shell comes out as one ring through the shared vertex. Cut it
        # there: each closed loop between two visits is a ring of its own.
        open_path: list[QPoint] = []
        loops: list[list[QPoint]] = []
        for vertex in ring:
            if vertex in open_path:
                at = open_path.index(vertex)
                loops.append(open_path[at:])
                del open_path[at + 1 :]
            else:
                open_path.append(vertex)
        loops.append(open_path)
        rings.extend(loops)
    return rings


def _area2(ring: list[QPoint]) -> Fraction:
    return sum((_cross(a[0], a[1], b[0], b[1]) for a, b in zip(ring, ring[1:] + ring[:1])), Fraction(0))


def nonzero_polygons(rings: list[list[tuple[float, float]]]) -> list[Polygon]:
    """Polygons of the nonzero-winding fill. Empty when nothing is filled."""
    exact = [[(Fraction(x), Fraction(y)) for x, y in ring] for ring in rings]
    edges = [edge for ring in exact for edge in _ring_edges(ring)]
    closed = stitch(boundary_edges(edges))
    shells = [ring for ring in closed if _area2(ring) > 0]
    holes = [ring for ring in closed if _area2(ring) < 0]
    probes = [_Winding(_ring_edges(shell)) for shell in shells]
    held: list[list[list[QPoint]]] = [[] for _ in shells]
    for hole in holes:
        p, q = hole[0], hole[1]
        around = [i for i, probe in enumerate(probes) if probe.beside(_mid(p, q), _left_normal(p, q)) != 0]
        if not around:
            raise ValueError("hole has no shell")
        held[min(around, key=lambda i: _area2(shells[i]))].append(hole)
    return list(zip(shells, held))
