# Chart COMPOUNDCURVE flatten-elimination

**Type:** grilling · **Map:** [COMPOUNDCURVE](../../map-compoundcurve.md)
**Claimed:** wayfinder 2026-09-01 · **Closed:** 2026-09-01
**Blocked by:** —
**claimId:** none · **GitHub:** none · **witness:** none

Board card: Notion CRV-CC.

## Question

What does `/wayfinder COMPOUNDCURVE` own? The board lifted HOLD
implement for flatten-elimination only. Name what is already true,
park what is HOLD, and leave one takeable leftover so the next
`/implement` cannot steal a closed letter or invent a second type.

## Resolution

**Grilled 2026-09-01. Living record:
[`docs/scout/map-compoundcurve.md`](../../map-compoundcurve.md).**
This ticket does not implement flatten-elimination.

**Already true.** HELP and READING-GUIDE name COMPOUNDCURVE (ISO/IEC
13249-3) and that Flatten-to-chords is lossy. The Coq carrier is
`CurveGeometry.v`. Named linearise is
`CurveLinearise.v : chord_approx_ring_closed`. CompoundCurve is not
the PR #8 CurveExact cell
(`HullExactExtrema.v : h_cc_still_densify`) — H-CC stays on #424.
LEC member flatten is `LECFlattenRow.v : empty_disk_flatten_iff`.
Koc files are railway alignment, not SQL/MM.

**Three words.** Silent chord Flatten is the leftover. Named
`Linearize` / `toLinear` / `chord_approx_ring` is allowed. Member /
splice flatten is already landed (`615-b` nested-CC splice is
§7.10.1).

**Parks.** JTS #27 out. JTS #38 (Option C DCEL) off #7. No public
noder. HOLD merge into #7. HOLD a second CompoundCurve type. No
type-9 reader PR. No GEO-TIN 15–17. No DOI. Cite 13249-3 only.

**Frontier.** Ticket 30 is the one takeable implement leftover.
