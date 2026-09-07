# ADR-0006 — Oracle protocol is the test surface

| Field         | Value                                                        |
|---------------|--------------------------------------------------------------|
| **Order**     | ADR-0006                                                     |
| **Status**    | **Accepted** — 2026-09-02                                    |
| **Deciders**  | Jeroen Bloemscheer (PO)                                      |
| **Date**      | 2026-09-02                                                   |
| **Superseded by** | — (none)                                                 |

Does not reopen nts ADR-0001 (LinearRing retired; a ring is a predicate on a
Curve) or proofs ADR-0003 (two-tier interior) / ADR-0005 (lenient intake,
strict IsValid).

---

## Context (self-contained)

`oracle/driver.ml` is the stdin/stdout adapter around Coq-extracted functions
in `extracted.ml`. Generators already speak a **line protocol of keywords**
(`RING_SIMPLE`, `POINT_IN_CURVE_RING`, `WINDING_NUMBER`, `RING_ORIENTATION`,
`HOLES_DISJOINT`, `DISC_OVERLAY`, `ARC_LEN_UNIFIED`, `CURVE_RELATE_MATRIX`,
…). That protocol is what CI and differential harnesses pin.

The driver has failed the split rule: ring checks for closed-and-simple
Curves sit in the same compilation unit as length, overlay, and relate work
they do not own. Adding wishlist ring predicates (`IS_CLOSED`,
`IS_SIMPLE_CURVE`, `IS_RING`) as more arms on that unit would make the file
worse. A second compilation unit already exists as the precedent —
`oracle/relate_matrix.ml` returns typed catalog values; the driver prints
wire tokens; generators did not move.

Two other surfaces sit next to the protocol and are easy to confuse with it:

- **FFI** (`oracle/nts_ffi.ml` / `libntsrocq`) — in-process C ABI for NTS.
  Marshalling around extracted symbols; no hand-rolled arithmetic.
- **RocqRefRunner** — a different tool. Integer `refSign` reconstruction,
  not an Oracle keyword.

The driver header still named the subprocess the RocqRefRunner binary. That
is a name collision, not a second protocol.

Year 1 remains circular only. Hunter tokens `E`/`B` are accepted syntax on
existing keywords; they are not a certification of elliptic or Bézier
curves.

## Decision 1 — one test surface: the Oracle line protocol

The Oracle line protocol (`oracle_bin` stdin/stdout keywords) is the seam
generators and CI pin. Do not add a second external seam. Do not register
ring functions on the FFI adapter. Do not mint RocqRefRunner as a dispatch
keyword.

The subprocess is Oracle / `oracle_bin`. RocqRefRunner stays a distinct
name.

## Decision 2 — ring-predicate computation is its own compilation unit

Extract the five **existing** ring-predicate keywords (`RING_SIMPLE`,
`POINT_IN_CURVE_RING`, `WINDING_NUMBER`, `RING_ORIENTATION`,
`HOLES_DISJOINT`) into a self-contained compilation unit linked into
`oracle_bin` beside `relate_matrix.ml`.

- Five functions, one per keyword. Each returns a typed value.
- Driver adapters print the current wire tokens. Do not print from inside
  the ring unit. Do not collapse to one keyword-dispatching `eval`.
- Shared `C`/`A`/`E`/`B` parse for those five lives in the ring unit.
  `WINDING_NUMBER`'s point-list parse stays in its adapter. Relate-matrix
  and `CURVE_RELATE_MATRIX` keep their own parse copies.
- No new protocol keyword in the extract. Wishlist M1 predicates
  (`IS_RING` / `IS_CLOSED` / `IS_SIMPLE_CURVE`) attach later as adapters on
  the extracted unit, not as arms on the fat driver.

*Rejected alternatives:* more arms on `driver.ml` (fails the split rule);
one `eval` of a keyword string inside the new unit (hides a new keyword as
an internal arm); a second external seam (FFI or RocqRefRunner) for the
same predicates (two pins for one behaviour); pulling relate into the ring
unit (blast radius).

## Decision 3 — helper copies are explicit debt

The helper stack the ring family needs (`pair_pts`, circumcentre,
point-on-arc-sector, and what they call) is **copied** into the ring unit
for this cut. Length and overlay keep the originals in `driver.ml` and do
not open the ring unit. `ARC_*` keeps using the driver's originals.

A future cut may own those helpers once. This cut does not pretend it did.
A third primitives unit that length/overlay would open is out of scope.

## Consequences

- Existing generators for the five keywords stay green without edits. Same
  keyword, same payload, same wire tokens as at the accept tip.
- Deletion test is the layout check: drop the ring unit and the five
  adapters fail to compile; overlay does not open it.
- Paper trail is this ADR. Do not edit `CONTEXT.md` for this cut. Do not
  add family / mode / dispatch / kernel as glossary terms — Regime is not
  overloaded.
- Hunter `E`/`B` remain syntax in the shared parse; they are not a year-2
  opener. No clothoid / NURBS / geodesic keywords.
- A ring remains a predicate (`IsClosed` ∧ `IsSimple`) on a Curve. Intake
  vs IsValid and two-tier interior are not reopened here.

## Related — ADR-0007 (cook / intersection oracle)

[ADR-0007](ADR-0007-sheet-hen-cook-noding-model.md) makes the noding
constructor part of the specification (sheet / hen / egg / chicken / cook).
Its pairwise intersection oracle and any *testable* cook results sit on
**this** Oracle line protocol as the only external test surface (Decision 1):
adapters may later print cook outcomes as keywords; they do not open a second
seam (no FFI pin, no RocqRefRunner dispatch keyword). Minting a cook-mode
keyword is an adapter cut under this ADR, not a reopening of Decision 1.
ADR-0007 Status may still be Proposed; this related note does not Accept it.
