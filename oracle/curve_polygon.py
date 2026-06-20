#!/usr/bin/env python3
# =============================================================================
# oracle/curve_polygon.py
# -----------------------------------------------------------------------------
# Minimal CurvePolygon reference model (F-CP Option A, issue #849), the in-scope
# (Proofs repo) Python counterpart of the NTS C# CurvePolygon.  It deliberately
# does NOT re-implement any geometry numerics: GetExteriorRing (Option A,
# densified) DELEGATES densification + simplification to the verified-interface
# oracle mode CP_BOUNDARY_SIMPLIFY (densify_arc -> EXTRACTED
# greedy_simplify_perp_b64 -> EXTRACTED b64_orient_sign_filtered).  The only
# numeric kernels in play are therefore the Coq-extracted / allowlisted oracle
# ones -- never a parallel, unverified Python copy.
#
# A ring segment is one of:
#   ("C", (x1, y1), (x2, y2))            chord  (start, end)
#   ("A", (x1, y1), (x2, y2), (x3, y3))  arc    (start, mid, end)
# =============================================================================
import os
import subprocess

BIN = os.environ.get("ORACLE_BIN", "oracle/oracle_bin")


def _seg_line(s):
    if s[0] == "C":
        return f"C {s[1][0]} {s[1][1]} {s[2][0]} {s[2][1]}"
    return f"A {s[1][0]} {s[1][1]} {s[2][0]} {s[2][1]} {s[3][0]} {s[3][1]}"


class CurvePolygon:
    """A CurvePolygon whose exterior is a single closed curve ring."""

    def __init__(self, shell):
        self.shell = list(shell)  # list of ring segments

    def get_exterior_curve(self):
        """The exterior ring as its raw curve segments (chords + arcs)."""
        return list(self.shell)

    def _oracle_input(self, eps, n):
        body = "\n".join(_seg_line(s) for s in self.shell)
        return f"CP_BOUNDARY_SIMPLIFY\n{eps} {n}\n{body}\n\n"

    def run_boundary(self, eps=0.0, n=8, oracle_bin=None):
        """Drive CP_BOUNDARY_SIMPLIFY; return (verts, corners).
        verts   : list of (x, y) floats (the densified + simplified ring)
        corners : list of (sign, flag) with flag in {INTSAFE, APPROX}
        """
        out = subprocess.run(
            [oracle_bin or BIN], input=self._oracle_input(eps, n),
            capture_output=True, text=True,
        ).stdout
        lines = [ln for ln in out.splitlines() if ln.strip() != ""]
        m = int(lines[0].split()[1])              # "V <m>"
        verts = []
        for ln in lines[1 : 1 + m]:
            xs, ys = ln.split()
            verts.append((float.fromhex(xs), float.fromhex(ys)))
        corners = [tuple(ln.split()) for ln in lines[2 + m : 2 + 2 * m]]
        return verts, corners

    def get_exterior_ring(self, eps=0.0, n=8, oracle_bin=None):
        """Option A: the densified + simplified exterior ring as a point list,
        densified by the verified-interface oracle kernel (not a Python copy)."""
        verts, _ = self.run_boundary(eps, n, oracle_bin)
        return verts
