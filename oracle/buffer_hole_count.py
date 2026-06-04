#!/usr/bin/env python3
"""Heuristic hole-COUNT oracle/hunter for buffer topology (JTS#979 family, #66).

Why heuristic, why count.  Buffer hole bugs (#979 "buffer with fixed precision
removes a hole", and the dual "buffer spuriously keeps/creates a hole") are
TOPOLOGICAL: what matters is the number of holes, not the exact offset distance.
An exact buffer-topology oracle needs the medial axis / distance transform; this
tool instead rasterises the d-neighbourhood on a grid and counts bounded
components of its complement.  It is a HEURISTIC (grid resolution `res`) but a
faithful one: refine `res` to converge.  It is `d`-AWARE only because buffer
topology genuinely depends on `d` -- and the dependence is NON-MONOTONIC.

Key fact this encodes (see the C-shape self-test): a hole-free C-shaped polygon
buffered by `d` has hole count 0 -> 1 -> 0 as `d` grows -- the mouth seals
(creating a real hole) before the pocket fills (removing it again).  So:
  * "high tolerance => 0 holes" is correct (large d fills the pocket); and
  * "0-hole input => always 0-hole output" is FALSE at intermediate d.
A buffer implementation must reproduce this, not flatten it.

Usage:
  buffer_hole_count(poly, d, res=...) -> int            # holes of buffer(poly,d)
  python3 oracle/buffer_hole_count.py                   # runs the C-shape self-test
"""
import math
import sys
from collections import deque

def _pip(p, poly):                      # point strictly inside polygon (ray cast)
    x, y = p; n = len(poly); inside = False; j = n - 1
    for i in range(n):
        xi, yi = poly[i]; xj, yj = poly[j]
        if ((yi > y) != (yj > y)) and (x < (xj - xi) * (y - yi) / (yj - yi) + xi):
            inside = not inside
        j = i
    return inside

def _d_seg(p, a, b):                    # distance point->segment
    (px, py), (ax, ay), (bx, by) = p, a, b
    dx, dy = bx - ax, by - ay; L2 = dx * dx + dy * dy
    t = 0.0 if L2 == 0 else max(0.0, min(1.0, ((px - ax) * dx + (py - ay) * dy) / L2))
    return math.hypot(px - (ax + t * dx), py - (ay + t * dy))

def _in_buffer(p, poly, d):             # within distance d of the solid polygon
    if _pip(p, poly):
        return True
    n = len(poly)
    return min(_d_seg(p, poly[i], poly[(i + 1) % n]) for i in range(n)) <= d

def buffer_hole_count(poly, d, res=0.2, margin=2.0):
    """Number of holes (bounded complement components) of buffer(poly, d)."""
    xs = [v[0] for v in poly]; ys = [v[1] for v in poly]
    x0, x1 = min(xs) - d - margin, max(xs) + d + margin
    y0, y1 = min(ys) - d - margin, max(ys) + d + margin
    nx = int((x1 - x0) / res) + 1; ny = int((y1 - y0) / res) + 1
    out = [[not _in_buffer((x0 + i * res, y0 + j * res), poly, d)
            for j in range(ny)] for i in range(nx)]
    seen = [[False] * ny for _ in range(nx)]
    holes = 0
    for i in range(nx):
        for j in range(ny):
            if out[i][j] and not seen[i][j]:
                q = deque([(i, j)]); seen[i][j] = True; border = False
                while q:
                    a, b = q.popleft()
                    if a in (0, nx - 1) or b in (0, ny - 1):
                        border = True
                    for da, db in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                        na, nb = a + da, b + db
                        if 0 <= na < nx and 0 <= nb < ny and out[na][nb] and not seen[na][nb]:
                            seen[na][nb] = True; q.append((na, nb))
                if not border:
                    holes += 1
    return holes

# C-shaped polygon, single ring, 0 holes: outer 10x10 square with a deep central
# pocket [2,8]^2 opened to the right through a thin mouth at y in [4.5, 5.5].
C_SHAPE = [(0, 0), (10, 0), (10, 4.5), (8, 4.5), (8, 2), (2, 2),
           (2, 8), (8, 8), (8, 5.5), (10, 5.5), (10, 10), (0, 10)]

def _self_test():
    print("# Heuristic buffer hole-count -- C-shape (0 holes), varying tolerance d:")
    table = {d: buffer_hole_count(C_SHAPE, d) for d in (0.0, 0.3, 1.0, 2.0, 3.0, 5.0, 8.0)}
    for d, h in table.items():
        tag = ""
        if h == 0 and d >= 3.0: tag = "  <- high tolerance: pocket filled, 0 holes"
        if h == 1: tag = "  <- mouth sealed, pocket not yet filled (a REAL hole)"
        print(f"  d={d:>4}: holes={h}{tag}")
    ok = True
    # Invariant 1 (the user's case): high tolerance => 0 holes.
    for d in (3.0, 5.0, 8.0):
        if table[d] != 0:
            print(f"FAIL: high-tolerance d={d} gave {table[d]} holes, expected 0"); ok = False
    # Invariant 2: the topology is genuinely non-monotonic (intermediate d has a hole).
    if table[1.0] != 1 or table[2.0] != 1:
        print("FAIL: expected a real hole at intermediate d (1 and 2)"); ok = False
    print("OK: high-tolerance buffer of the C-shape has 0 holes; "
          "intermediate d correctly shows 1 (non-monotonic)." if ok else "SELF-TEST FAILED")
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(_self_test())
