# ADR-0005 — Lenient intake, strict IsValid for SQL/MM curve types

| Field         | Value                                                        |
|---------------|--------------------------------------------------------------|
| **Order**     | ADR-0005                                                     |
| **Status**    | **Accepted** — decided by Jeroen (PO), 2026-08-30 (#615 grilling session) |
| **Deciders**  | Jeroen (PO)                                                  |
| **Date**      | 2026-08-30                                                   |
| **Superseded by** | — (none)                                                 |

---

## Context (self-contained)

The NTS donor branch `feat/curves-metrics-followup`
(`grootstebozewolf/NetTopologySuite`) carries the SQL/MM curve types
(CircularString, CompoundCurve, CurvePolygon — CONTEXT.md, *Curve types*).
Since NetTopologySuite#857 moved curve work in-tree, nothing pulls the branch,
so its types can be reshaped against ISO/IEC 13249-3:2016 without breaking a
consumer. The epic's governing premise (#615 decision 2, confirmed by the PO)
is that **ISO is leading**: where the spec and the branch disagree, the spec
wins unless a deviation is recorded as deliberate. The clause-by-clause gap analysis is
`docs/iso13249-3-curve-type-bindings-2026-08.md` (the clause table's single
source of truth; this ADR cites it rather than restating clauses).

Two structural questions blocked every conformance ticket:

1. **Where does each ISO "shall" get enforced?** The spec phrases its
   structural rules as constructor-time checks (`NEW ST_CircularString`
   raises on ill-formed input), and the branch already half-follows that:
   constructors check point counts and contiguity but not per-arc-segment
   endpoint distinctness (§7.3.1 Desc 6) or ring simplicity (§8.2.1), while
   curve `IsValid`/`IsSimple` fail closed entirely.

2. **Nested CompoundCurve.** §7.10.1 Desc 7 and the §5.1.67 WKT grammar admit
   COMPOUNDCURVE components inside COMPOUNDCURVE; the branch rejected them in
   constructor and reader, and its doc comment mis-attributed that
   restriction to SQL/MM (research doc §6.1, the `SUMMARY warn`).

Both questions are the same question — how the type boundary relates to the
spec — and the answer is one posture: **conform at the boundary, normalize
inside**.

## Decision 1 — lenient intake, strict IsValid

Constructors (and the WKT/WKB readers feeding them) reject only what makes a
value **unrepresentable**: CircularString point-count shape (0 or odd ≥ 3),
CompoundCurve contiguity, CurvePolygon ring closure. The one intake check
with no clause behind it — rejection of *empty* components (the spec forbids
only null, §7.10.1 Desc 5) — is removed. Every genuine ISO "shall" beyond
representability (arc-segment start≠end §7.3.1 Desc 6, ring simplicity
§8.2.1 Desc 2–3, …) is owned by arc-aware `ST_IsValid`, in the honest shape:
**definite-false detection** — a value violating an implemented rule returns
`IsValid == false` naming the clause; a value whose remaining rules need
not-yet-built machinery stays **fail-closed** (throws, naming the missing
rung) rather than returning an unchecked `true`. The validity lane is
un-bounded: it climbs rung by rung (cheap clause rules first, arc-arc
simplicity later) and outlives any one epic.

*Rejected alternatives:* NEW-time enforcement per the spec's own constructor
rules (turns every future clause into a breaking constructor change, and
makes ill-formed-but-useful diagnostic values unconstructible); returning
`true` from a partial IsValid (a green light nothing checked — the exact
failure mode issue #522 exists to kill).

## Decision 2 — nested CompoundCurve: accept and flatten on intake

Reader and constructor accept COMPOUNDCURVE components (all ST_Curve
subtypes, per §7.10.1 Desc 7 and the §5.1.67 `<curve text>`/`<ring text>`
grammar) and **splice them into the flat component list**. Component
enumeration reports the spliced sequence; the writer keeps emitting flat,
grammar-clean WKT. The in-code comment owns the flat model as
*normalization* citing §7.10.1 value semantics — the false SQL/MM
attribution goes. This matches the dominant implementations (PostGIS/GEOS)
and keeps every downstream algorithm on a flat segment list.

*Rejected alternatives:* keep the rejection and document it as deviation
(fails "ISO is leading" — grammatical WKT must parse); model nesting (the
spec's value semantics gain nothing, every consumer pays a recursion, and
the only observable difference is component enumeration — which flattening
defines away).

## Consequences

- Intake tests become the executable form of the CONTEXT.md **Intake**
  entry: everything accepted is representable, everything rejected carries a
  clause citation (#615 tickets `615-b`, `615-c`).
- Arc-aware IsValid rung 1 delivers the definite-false/fail-closed split for
  the cheap clause rules (`615-g`); ring simplicity via arc-arc intersection
  is the next rung (`615-h`) and further rungs continue past the epic.
- A value can construct and be invalid (e.g. a Desc-6-violating
  single-segment closed arc) — that pair of facts is deliberate, tested, and
  documented at both sites; whole circles are written in the two-segment
  five-point CIRCULARSTRING idiom until ST_Circle exists (§4.2.7, zoo
  backlog).
- The research doc's §6.1/§6.2 divergence rows resolve to this ADR; its
  `SUMMARY warn` dies with the flatten landing (`615-b`).
