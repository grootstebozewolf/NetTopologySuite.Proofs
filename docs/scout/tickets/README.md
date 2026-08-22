# Tickets — Retire the epic block #64–#69

One ticket per session. A ticket is **takeable** when every ticket blocking it is
closed and nobody has claimed it; claim by adding `**Claimed:** <name>` under the
title before doing any work. Resolve by appending a `## Resolution` section,
moving the file to `closed/`, and adding a one-line pointer to the map's
*Decisions so far*.

Order of work: top-down from #64, with the freebie first.

| # | Ticket | Type | Blocked by |
|---|---|---|---|
| 01 | ~~[Close #482 — Shewchuk half-ulp counterexample retip](closed/01-close-shewchuk-counterexample-subtask.md)~~ **closed** | task | — |
| 02 | ~~[Write the module-split gate: policy and ratchet guard](closed/02-module-split-gate-policy-and-guard.md)~~ **closed** | task | — |
| 03 | ~~[Open the module-split queue epic](closed/03-open-module-split-queue-epic.md)~~ **closed** → #506 | task | 02 |
| 04 | ~~[Retire #64 — arc primitives](closed/04-retire-64-arc-primitives.md)~~ **closed** → #508 #509 #510 #511 | grilling | — |
| 05 | ~~[Retire #65 — buffer and offset curves](closed/05-retire-65-buffer-and-offset.md)~~ **closed** → #515 #513 #514, ADR-0002 | grilling | — |
| 06 | ~~[Retire #66 — precision models, snap rounding, OverlayNG](closed/06-retire-66-precision-and-overlay.md)~~ **closed** → #517 #518 #519 #520, ADR-0002 amended | grilling | — |
| 07 | ~~[Retire #67 — RelateNG matrix and boundary handling](closed/07-retire-67-relateng.md)~~ **closed: decided not to close #67** → ADR-0003, #522, #523 | grilling | — |
| 11 | [Retire #67 — second pass](11-retire-67-second-pass.md) | grilling | ADR-0003 unconsumed, **#523**, **#503** — precondition 1 largely met by #530 |
| 08 | ~~[Retire #68 — Delaunay triangulation and Voronoi diagrams](closed/08-retire-68-delaunay-voronoi.md)~~ **closed** → #525 (global tier), #526 | grilling | — |
| 09 | [End #69's umbrella role and re-parent the standing epics](09-end-69-umbrella.md) | grilling | 11 (04–08 all closed) |
| 10 | [Resync surviving issue bodies to corpus state](10-resync-surviving-bodies.md) | task | **#506 queue empty**, 09 |

```
01 ══════════════════════════════════════ closed 2026-08-22 (#482)

02 ═══ 03 ═══ #506 ───────────────┐  gate live in CI; epic open
              (queue must empty)  ├── 10
04 ═══════════════════════╗       │  #64 closed → #508 #509 #510 #511
05 ═══════════════════════╣       │  #65 closed → #515 (hero shot), #513 #514
06 ═══════════════════════╣       │  #66 closed → #517 #518 #519 #520
07 ═══ 11 ────────────────╣       │  #67 still open (reopened after an
       (ADR-0003, #523,   ║       │  accidental keyword closure) → ADR-0003,
        #503)             ║       │  #522 half-fixed by #530, #523
08 ═══════════ 09 ────────╝───────┘  #68 closed → #525 (global tier), #526
```

**Frontier: empty.** Every remaining ticket waits on out-of-map execution —
proof work, an oracle fix, and documentation corrections — not on a decision:

| Ticket | Waiting on |
|---|---|
| 11 · second pass at #67 | ADR-0003 consumed by the capstone work · #523 · #503's four defects. Precondition 1 largely met by #530. |
| 09 · end #69's umbrella | ticket 11 |
| 10 · resync surviving bodies | #506's split queue emptying · ticket 09 |

**The map has done its job.** Four of the six epics are retired, the fifth is
deliberately open with its blockers named and one of them now fixed, and the sixth
is a hinge that cannot move until the fifth does. What remains is work, not
wayfinding — so the next useful session is `/implement`, not this skill.

Three epics retired on evidence, one deliberately not: **an epic closes only when
its closure comment would be true.**
