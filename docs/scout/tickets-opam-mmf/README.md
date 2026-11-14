<!-- doc-kind: guide -->
# Tickets — An MMF release bar for the opam packages

Map: [An MMF release bar for the opam packages](../map-opam-mmf-release-bar.md)

One ticket per session. A ticket is **takeable** when every ticket blocking it is
closed and nobody has claimed it; claim by adding `**Claimed:** <name>` under the
title before doing any work. Resolve by appending a `## Resolution` section,
moving the file to `closed/`, and adding a one-line pointer to the map's
*Decisions so far*.

| # | Ticket | Type | Blocked by |
|---|---|---|---|
| 01 | ~~[Collect the community verdict on the `rocq-*` rename](closed/01-community-verdict-on-rocq-rename.md)~~ **closed** — both `rocq-*`, restart at 0.1.0 | task | — |
| 02 | [Decide the shape of the manifest-closure gate](02-gate-manifest-closure.md) | grilling | — |
| 03 | ~~[Decide the Rocq version constraint](closed/03-rocq-version-constraint.md)~~ **closed** — `rocq-core {>= "9.2" & < "9.3~"}` | grilling | — |
| 04 | [Establish why `opam publish` never landed a package](04-why-opam-publish-never-landed.md) | research | — |
| 05 | [Decide the axiom-footprint line, per package](05-axiom-footprint-line.md) | grilling | — |
| 07 | [Audit the opam descriptions for stale and unearned claims](07-audit-description-claims.md) | task | — |
| 08 | [Decide how to stop CRLF breaking local verification](08-crlf-breaks-local-verification.md) | task | — |
| 06 | [Write the bar](06-write-the-bar.md) | grilling | 01, 02, 03, 04, 05, 07 |

```
01 ══╗  closed 2026-08-24 — both rocq-*, versions restart at 0.1.0
02 ──┤  closure gate
03 ══┼══ closed 2026-08-24 — rocq-core {>= "9.2" & < "9.3~"}  (9.3 unreleased)
04 ──┼── 06  write the bar
05 ──┤  axiom line, per package
07 ──┤  description accuracy
08 ──┘  CRLF blocks local verification (found while verifying)
      ↑ 04 = why publish never landed, the load-bearing diagnosis
```

**Frontier:** 02, 04, 05, 07, 08 — five takeable, none blocked. Ticket 06 is
the only blocked one, and it is the destination.

The five can run in parallel, so expect concurrent sessions. **04 is the one to
take first if you only take one**: six releases have shipped without reaching
the archive, and until that is understood the bar cannot name a gate that would
have caught it.

Ticket 06 is deliberately last-numbered-but-listed-last rather than renumbered;
the six inputs were specified together and 06 assembles them.
