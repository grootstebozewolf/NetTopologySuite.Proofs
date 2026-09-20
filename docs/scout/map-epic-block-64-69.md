# Map — Retire the epic block #64–#69

A wayfinder map. Tickets live in [`tickets/`](tickets/) and are worked one per
session. Charted 2026-08-22.

> **Tracker exception.** `docs/agents/issue-tracker.md` puts wayfinder maps on
> GitHub. This map is local markdown instead, for one reason: its destination is
> an *emptier issue tracker*, and a map that must delete itself to succeed does
> not belong in the thing being emptied. This exception applies to this map only.

## Destination

**The early epic block — #64, #65, #66, #67, #68, #69 — reaches zero open.**
Each of the six either retires with an evidence pointer, or its live residue is
re-expressed as a subtask or a clearly-stated new epic before it retires.

Anything numbered above that block is by definition **not** legacy: #423
(metrics), #424 (hulls) and #425 (coverage) stand on their own as clearly-stated
new epics, and #482 is a subtask. #69's umbrella role ends with the block.
Owner-retire packet: [`69-closing-summary.md`](69-closing-summary.md).
This map does not retire the GitHub object.

## Notes

Domain: [`CONTEXT.md`](../../CONTEXT.md),
[`docs/agents/domain.md`](../agents/domain.md),
`TRIAGE_NTS_JTS_ISSUES.md`, `docs/verified-claims.md`. Parks:
CONTEXT Roadmap / **ADR-0002**. Bible lives in `jts-*` forks.
Issue ops: [`docs/agents/issue-tracker.md`](../agents/issue-tracker.md).

This map executes (`gh issue close` / residue issues; reopen undoes).
Close against the tree, not the 2026-07-04 bodies. Closure comment:
claims row + `file:line` + lane status + what is not covered.
#67 did not close on “scope achieved” — **ADR-0003**; owner retired
the GitHub object 2026-08-23;
[second pass](tickets/closed/11-retire-67-second-pass.md) is
overtaken. Module-split gate: `docs/macro-meso-micro.md` +
`scripts/check_module_split.py`. Body resync waits on an empty
split queue.

## Decisions so far

- [Close #482](tickets/closed/01-close-shewchuk-counterexample-subtask.md) — closed; register gap is #503.
- [Module-split gate](tickets/closed/02-module-split-gate-policy-and-guard.md) — `docs/macro-meso-micro.md` + `scripts/check_module_split.py`.
- [Module-split queue](tickets/closed/03-open-module-split-queue-epic.md) — live as #506.
- [Retire #68](tickets/closed/08-retire-68-delaunay-voronoi.md) — closed on local-flip; global is #525 / #526.
- [Grill #523](tickets/closed/12-grill-523-curve-relate-alphabet.md) — not resolved / not accepted; `523-a`/`523-b`/`523-c` landed ([`map-523.md`](map-523.md), [`spec-523.md`](spec-523.md)).
- [Retire #67](tickets/closed/07-retire-67-relateng.md) — decided not to close on “scope achieved”; **ADR-0003**. [Second pass](tickets/closed/11-retire-67-second-pass.md) overtaken; ticket 523 stays open.
- [Retire #66](tickets/closed/06-retire-66-precision-and-overlay.md) — closed; residue #517–#520. ADR-0002 amended (technique park).
- [Retire #65](tickets/closed/05-retire-65-buffer-and-offset.md) — closed on linear+arc; hero #515; found #513 / #514.
- [Retire #64](tickets/closed/04-retire-64-arc-primitives.md) — closed on circular-arc; residue #508–#511 / #503.
- [Retire #67 second pass](tickets/closed/11-retire-67-second-pass.md) — overtaken; does not reopen #67.
- [End #69 umbrella](tickets/closed/09-end-69-umbrella.md) — no replacement; [`69-closing-summary.md`](69-closing-summary.md). Do not remint `69-a`.

## Not yet specified
- **#66 parks.** C2 / arc Hobby: non-goal vs new epic is the ticket’s call.
- **#67 capstone.** `geom_de9im_pointset` residue; issue count unknown from here.
- **CurvePolygon kit completeness.** Laser kits (Bible §8), not `*Kit*.v`. T-in/T-out is missing vocabulary (`Tin.v` is TIN). “Complete” has a refuted ancestor (`OverlayTouchRow.v : phase0_relation_complete_hypothesis_refuted`). Ops are `OSet` / two discs only.
- **Freshness re-run.** Whether stale bodies become a quarterly chore.
- **Allowlist growth check.** `check_module_split.py` cannot see history.

## Out of scope

- Performing the module splits (governance only).
- #423 / #424 / #425 (new epics, not this block).
- Upstream filing of #482.
- Laser chord-vs-arc implementation.
