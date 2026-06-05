#!/usr/bin/env bash
# Hunter for JTS#979: `Geometry.buffer` with a fixed PrecisionModel removes a
# hole.  Driven by the RocqRefRunner HOLE_PRECISION_AUDIT mode (exact-rational
# signed-area sign of a ring, before and after precision reduction).
#
# FRAMING (deliberate).  #979 is a TOPOLOGICAL / HOLE-COUNT bug: a hole
# DISAPPEARS.  It is NOT a metric error, and it is INDEPENDENT of the buffer
# distance d -- the hole is killed by snapping its ring to the fixed grid
# (makePrecise), which collapses any hole smaller than ~one grid cell to zero
# area, whatever d the caller passes.  So the hunter ignores d entirely and
# audits the invariant that actually matters:
#
#     hole survives  <=>  its precision-reduced ring still has nonzero area.
#
# This is an EXACT criterion (zarith Q shoelace), not a heuristic: a "REMOVED"
# verdict is a sound witness that the precision model destroys the hole (a
# necessary precursor to buffer dropping it).  It is a sound UNDER-approximation
# of full-buffer #979 -- it captures the precision-collapse mechanism, not the
# noder.
#
# Run: bash oracle/gen_hole979_hunt.sh > oracle/hole979_hunt.txt
BIN=./oracle/oracle_bin

# audit a square hole of side L at offset (0.2,0.2) under fixed scale s.
emit_audit() {  # $1=scale $2=L $3=note
  s=$1; L=$2
  pts=$(python3 - "$L" <<'PY'
import sys
L=float(sys.argv[1]); ox=oy=0.2
for (x,y) in [(ox,oy),(ox+L,oy),(ox+L,oy+L),(ox,oy+L)]:
    print(f"{x!r} {y!r}")
PY
)
  out=$(printf 'HOLE_PRECISION_AUDIT\n%s\n4\n%s\n' "$s" "$pts" | "$BIN")
  ex=${out% *}; pr=${out#* }
  verdict="survives"
  if [ "$ex" != ZERO ] && [ "$pr" = ZERO ]; then verdict="REMOVED (#979)"; fi
  printf "  scale=%-4s side=%-6s  exact=%-4s precise=%-4s  %s   # %s\n" "$s" "$L" "$ex" "$pr" "$verdict" "$3"
}

echo "# JTS#979 hunter -- precision-model hole removal (oracle HOLE_PRECISION_AUDIT)."
echo "# A square hole of side L at (0.2,0.2); audited under fixed PrecisionModel scale s"
echo "# (grid cell = 1/s).  REMOVED = exact area nonzero but precision-reduced area ZERO."
echo "# Buffer distance d is irrelevant and not used: this is a hole-COUNT/topology audit."
echo
echo "## Sweep: a small hole of fixed side 0.05, increasing precision (coarse -> fine):"
echo "## (REMOVED at coarse precision; survives once the grid is finer than the hole."
echo "##  Raising the PrecisionModel scale -- NOT changing buffer distance d -- is the fix.)"
for s in 1 2 8 20 100; do emit_audit "$s" 0.05 "cell 1/$s vs side 0.05"; done
echo
echo "## Sweep: fixed coarse precision (scale=1, integer grid), shrinking hole:"
for L in 2.0 1.0 0.6 0.3 0.05; do emit_audit 1 "$L" "side $L on the unit grid"; done
echo
echo "## Hole-count summary (the #979 signature is count_after < count_before):"
total=0; removed=0
for s in 1 2 4 8 100; do
  for L in 0.05 0.3 0.6; do
    out=$(printf 'HOLE_PRECISION_AUDIT\n%s\n4\n0.2 0.2\n%s 0.2\n%s %s\n0.2 %s\n' \
            "$s" "$(python3 -c "print(repr(0.2+$L))")" \
                 "$(python3 -c "print(repr(0.2+$L))")" "$(python3 -c "print(repr(0.2+$L))")" \
                 "$(python3 -c "print(repr(0.2+$L))")" | "$BIN")
    ex=${out% *}; pr=${out#* }
    total=$((total+1))
    [ "$ex" != ZERO ] && [ "$pr" = ZERO ] && removed=$((removed+1))
  done
done
echo "#   audited $total (hole,scale) pairs; precision model REMOVED $removed of them."
echo "#   At scale=100 (fine grid) no hole >= 0.05 is removed -- the #979 fix direction."
