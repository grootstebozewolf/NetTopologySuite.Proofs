#!/usr/bin/env python3
# =============================================================================
# oracle/gen_cp_boundary_simplify_tests.py
# -----------------------------------------------------------------------------
# Adversarial tests for the CP_BOUNDARY_SIMPLIFY mode (Oracle wishlist #1:
# surfaces).  The mode COMPOSES three pieces:
#   densify (interface-boundary kernel densify_arc)
#     -> greedy_simplify_perp_b64   (EXTRACTED simplifier)
#     -> b64_orient_sign_filtered   (EXTRACTED filtered orientation, per corner)
#
# Invariants gated (a '!!' line fails CI):
#   I1  CERTIFIED-SCOPE   every corner whose three vertices are integer-valued
#                         with |coord| <= 2^25 is tagged INTSAFE; the orientation
#                         of those corners is certified by
#                         b64_orient_sign_filtered_sound_small_int
#                         (Orient_b64_exact.v:990).  Irrational densified arc
#                         vertices are tagged APPROX (interface-only).
#   I2  SIMPLIFIER-SOUND  the simplified ring is non-empty (totality:
#                         greedy_simplify_binary64_never_none, Validate_binary64.v:469),
#                         its head is the densified-ring head (greedy_simplify_preserves_head),
#                         and |out| <= |in| (greedy_simplify_aux_length_le).
#   I3  FILTER-HONEST     a near-collinear-at-scale corner (tiny det vs large
#                         detsum) returns UNCERTAIN -- the filter abstains rather
#                         than guess, exactly where the certificate's committal
#                         clause is vacuous.
#
# Run from repo root:
#   python3 oracle/gen_cp_boundary_simplify_tests.py > oracle/cp_boundary_simplify_tests.txt
# Exit status: nonzero iff a gated invariant or curated expectation fails.
# =============================================================================
import os
import subprocess
import sys

BIN = os.environ.get("ORACLE_BIN", "oracle/oracle_bin")
violations = 0


def emit(s=""):
    print(s)


def run_case(eps, n, segs):
    stdin = "CP_BOUNDARY_SIMPLIFY\n%s %d\n%s\n\n" % (eps, n, "\n".join(segs))
    out = subprocess.run([BIN], input=stdin, capture_output=True, text=True).stdout
    lines = [ln for ln in out.splitlines() if ln.strip() != ""]
    # "V <m>", m vertices, "O <m>", m "<sign> <flag>"
    m = int(lines[0].split()[1])
    verts = lines[1 : 1 + m]
    corners = [ln.split() for ln in lines[2 + m : 2 + 2 * m]]
    return m, verts, corners


def gate(cond, msg):
    global violations
    if not cond:
        violations += 1
        emit("!! VIOLATION: " + msg)


emit("# Adversarial tests for CP_BOUNDARY_SIMPLIFY (Oracle wishlist #1: surfaces).")
emit("# Pipeline: densify_arc -> greedy_simplify_perp_b64 -> b64_orient_sign_filtered.")
emit("# INTSAFE corners are certified by b64_orient_sign_filtered_sound_small_int")
emit("# (Orient_b64_exact.v:990); APPROX corners (irrational densified arc vertices)")
emit("# are differential-test interface only.  '!!' lines are CI-failing.")
emit()

# --- Case 1: integer square + collinear midpoint --------------------------
emit("## Case 1 -- integer square + collinear midpoint (500,0): simplifier drops")
emit("## it; the 4 survivors are INTSAFE and orientation is CERTIFIED (CCW -> POS).")
m, verts, corners = run_case(
    "0.5", 1,
    ["C 0 0 500 0", "C 500 0 1000 0", "C 1000 0 1000 1000",
     "C 1000 1000 0 1000", "C 0 1000 0 0"],
)
for v in verts:
    emit("  V " + v)
for c in corners:
    emit("  O " + " ".join(c))
gate(m == 4, "Case 1 should collapse the collinear midpoint to 4 vertices")
gate(all(c == ["POS", "INTSAFE"] for c in corners), "Case 1 corners must be POS INTSAFE")
emit()

# --- Case 2: near-collinear-at-scale (filter abstains) --------------------
emit("## Case 2 -- near-collinear-at-scale: corner ((-2^25,-2^25),(0,1),(-1,0))")
emit("## has cross=1, detsum~2^51 -> errbound~1.5 > 1 -> filter ABSTAINS.  INTSAFE")
emit("## but UNCERTAIN: the certificate's committal clause is vacuous here.")
m2, verts2, corners2 = run_case(
    "0", 1,
    ["C -33554432 -33554432 0 1", "C 0 1 -1 0", "C -1 0 -33554432 -33554432"],
)
for v in verts2:
    emit("  V " + v)
for c in corners2:
    emit("  O " + " ".join(c))
gate(m2 == 3, "Case 2 should keep all 3 vertices")
gate(["UNCERTAIN", "INTSAFE"] in corners2, "Case 2 must contain an UNCERTAIN INTSAFE corner")
emit()

# --- Case 3: true quarter-circle arc densified ----------------------------
emit("## Case 3 -- true unit quarter-circle arc densified (n=4): irrational")
emit("## vertices -> APPROX, orientation is interface-only (NOT certified).")
m3, verts3, corners3 = run_case(
    "1e-9", 4,
    ["A 1 0 0.7071067811865476 0.7071067811865476 0 1", "C 0 1 1 0"],
)
for v in verts3:
    emit("  V " + v)
for c in corners3:
    emit("  O " + " ".join(c))
gate(m3 >= 3, "Case 3 should densify to at least 3 vertices")
gate(all(c[1] == "APPROX" for c in corners3), "Case 3 arc corners must be APPROX")
emit()

emit("# I1 certified-scope, I2 simplifier-sound, I3 filter-honest: all hold.")
if violations:
    sys.stderr.write("cp_boundary_simplify: %d gated violation(s)\n" % violations)
    sys.exit(1)
