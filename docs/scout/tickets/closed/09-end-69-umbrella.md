<!-- doc-kind: finding
date: 2026-09-01
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# End #69's umbrella role and re-parent the standing epics

**Type:** grilling · **Map:** [Retire the epic block #64–#69](../../map-epic-block-64-69.md)
**Claimed:** wayfinder 2026-09-01 · **Closed:** 2026-09-01
**Blocked by:** ~~[#64](04-retire-64-arc-primitives.md)~~ ✔ · ~~[#65](05-retire-65-buffer-and-offset.md)~~ ✔ · ~~[#66](06-retire-66-precision-and-overlay.md)~~ ✔ · ~~[#68](08-retire-68-delaunay-voronoi.md)~~ ✔ · ~~[Retire #67 — second pass](11-retire-67-second-pass.md)~~ ✔ overtaken (owner already retired the GitHub object; this ticket does not re-grill #67)

## Question

#69 (Expectant) is a tracking issue whose own body says "Tracking issue only…
Keep open as the epic tracker". Once #64–#68 are retired, what does it track — and
how does it end?

Its `69-a` ask is itself green (`theories/OracleCurveChecklist.v : w1_w5_coverage_table_complete`,
`eval/Claim69a.v`), so the question is purely about the
umbrella role.

Decide:

1. **Do #423/#424/#425 need a replacement umbrella?** They currently carry
   `Umbrella: #69` in prose. Options: a fresh umbrella issue, a GitHub project
   board, `TRIAGE_NTS_JTS_ISSUES.md` alone (it already holds the wire map), or
   nothing — each stands alone as a clearly-stated epic.
2. **What happens to the successor epics** this map creates (the module-split
   queue, #68's Voronoi phase, #64's V-CP Jordan work if it becomes an epic)? Do
   they inherit an umbrella or stand alone too?
3. **The stale body.** #69's status table is the most-read stale artifact in the
   tracker: it claims the deferred registry has "1 live entry (ArcPointDistance
   fallback)" when the registry is now empty, says "424+ cited theorems" when
   `docs/verified-claims.md` carries 700 rows, and its child map predates D-PT
   closure, the quartic, 68-a/68-b, and the extended epics entirely. If #69
   retires, this evaporates; if it survives in any form, the resync ticket owns it.

This ticket is the map's hinge: the destination is only reached if #69 itself
retires.

## Resolution

**Grilled 2026-09-01. No replacement umbrella. Successor epics stand
alone. Owner-retire packet is
[`docs/scout/69-closing-summary.md`](../../69-closing-summary.md).**
This ticket does not retire the GitHub object.

**Answer 1.** #423 / #424 / #425 stand alone. TRIAGE §Wire map is the
index. A project board is optional owner work. Their `Umbrella: #69`
lines are historical; ticket 10 rewrites surviving bodies after the
#506 queue drains. Do not mint a fresh umbrella issue.

**Answer 2.** Successor epics stand alone: #506, #509, #510, #511,
#515, #517–#520, #523, #525, #526, #564–#566, #615, leftover #522
charts. None inherit a parent.

**Answer 3.** The stale body evaporates when the owner retires the
tracker. Ticket 10 does not own #69. The June 2026 table is not
refreshed in place.

**Leftover TAGs that still named #69** (M-DIM, AT-*, LRF-* research;
S-* technique; F-CP / B-CP / C-* already housed) are parks in the
closing summary. Epic creation stays an owner-scope gate. Do not
mint `69-b`. Do not remint `69-a`.

**#67 blocker.** Lifted because the GitHub object is already retired
(owner, 2026-08-23, no commit keyword). Ticket 11 is overtaken — not
a second-pass accept of #523, and not a re-open of #67.
