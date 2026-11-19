"""Python handle on the EXTRACTED Rocq hot-pixel kernel.

Every geometric answer this module returns is computed by OCaml code that Rocq
extracted from theories-flocq/HotPixel_Q_exec.v (tools/klic-demo/ocaml/
hotpixel_q.ml, no extraction overrides).  This module only formats exact
rationals as text, pipes them to the kernel, and parses the reply.

What each call means, by Qed theorem (HotPixel_Q_exec.v):

  snap(x, s)            q_snap_coord          = snap_round_coord x s
                        (q_snap_coord_correct; round-half-to-even onto the
                        grid of spacing 1/s)
  snap -> displacement  q_snap_disp           <= 1 / (2 s)
                        (q_snap_disp_bound)
  passes(P0,P1,C,s)     q_passes_through_closed
                        <-> passes_through_hot_pixel_closed P0 P1 C s
                        (q_passes_through_closed_reflect)
  touches(P0,P1,C,s)    q_touches_closed
                        <-> segment_touches_hot_pixel_closed P0 P1 C s
                        (q_touches_closed_reflect)
  intersection(...)     q_seg_intersection = Some X
                        -> X is on both closed segments
                        (q_seg_intersection_sound)

Inputs are exact rationals (fractions.Fraction).  Parse coordinates from the
WKT / GML TEXT with Fraction(str) -- never via float -- so a delivery's
decimal metres are used exactly.
"""
from __future__ import annotations

import os
import subprocess
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Optional, Sequence, Tuple

HERE = Path(__file__).resolve().parent
KERNEL = Path(os.environ.get("KLIC_KERNEL", HERE / "ocaml" / "hotpixel_q"))

Pt = Tuple[Fraction, Fraction]


def ensure_kernel() -> Path:
    """Build the kernel with the stock OCaml compiler if it is missing."""
    if not KERNEL.exists():
        subprocess.run(["bash", str(HERE / "ocaml" / "build.sh")], check=True,
                       stdout=subprocess.DEVNULL)
    return KERNEL


def _q(v) -> str:
    f = Fraction(v)
    return str(f.numerator) if f.denominator == 1 else f"{f.numerator}/{f.denominator}"


def _parse_q(s: str) -> Fraction:
    return Fraction(s)


def run_batch(queries: Sequence[str]) -> list[str]:
    """Send queries (one per line) to the kernel; return one reply per query."""
    if not queries:
        return []
    proc = subprocess.run([str(ensure_kernel())], input="\n".join(queries) + "\n",
                          capture_output=True, text=True, check=True)
    out = proc.stdout.splitlines()
    if len(out) != len(queries):
        raise RuntimeError(f"kernel returned {len(out)} lines for {len(queries)} queries")
    return out


def q_snap(x, s) -> str:
    return f"SNAP {_q(x)} {_q(s)}"


def q_pass(p0: Pt, p1: Pt, c: Pt, s) -> str:
    return "PASS " + " ".join(_q(v) for v in (*p0, *p1, *c, s))


def q_touch(p0: Pt, p1: Pt, c: Pt, s) -> str:
    return "TOUCH " + " ".join(_q(v) for v in (*p0, *p1, *c, s))


def q_inter(a: Pt, b: Pt, c: Pt, d: Pt) -> str:
    return "INTER " + " ".join(_q(v) for v in (*a, *b, *c, *d))


def snap_many(xs: Iterable, s) -> list[Tuple[Fraction, Fraction]]:
    """[(snapped, |snapped - x|)] for each x, by the extracted kernel."""
    rep = run_batch([q_snap(x, s) for x in xs])
    out = []
    for r in rep:
        a, b = r.split()
        out.append((_parse_q(a), _parse_q(b)))
    return out


def passes_many(items: Iterable[Tuple[Pt, Pt, Pt]], s) -> list[bool]:
    rep = run_batch([q_pass(p0, p1, c, s) for p0, p1, c in items])
    return [r == "1" for r in rep]


def intersections_many(items: Iterable[Tuple[Pt, Pt, Pt, Pt]]) -> list[Optional[Pt]]:
    rep = run_batch([q_inter(a, b, c, d) for a, b, c, d in items])
    out: list[Optional[Pt]] = []
    for r in rep:
        if r == "NONE":
            out.append(None)
        else:
            x, y = r.split()
            out.append((_parse_q(x), _parse_q(y)))
    return out


# --------------------------------------------------------------------------
# Exact WKT coordinate parsing (text -> Fraction, no float on the way).
# --------------------------------------------------------------------------

def coords_from_wkt_text(wkt: str) -> list[Pt]:
    """Coordinates of a single-ring POLYGON or a LINESTRING, exactly."""
    inner = wkt[wkt.index("(") :].replace("(", " ").replace(")", " ")
    pts = []
    for pair in inner.split(","):
        xs, ys = pair.split()[:2]
        pts.append((Fraction(xs), Fraction(ys)))
    return pts
