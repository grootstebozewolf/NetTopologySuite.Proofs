# ADR-0008 — Ellipsoid sheet: the inverse geodesic is a constructor

| Field | Value |
|---------------|--------------------------------------------------------------|
| **Order** | ADR-0008 |
| **Status** | **Proposed** — 2026-09-19 |
| **Deciders** | Joost (BDFL); proposed by Jeroen Bloemscheer |
| **Date** | 2026-09-19 |
| **Supersedes** | — (none) |
| **Does not reopen** | ADR-0006 (Oracle is the test surface); ADR-0007 (planar sheet, hen, cook) |

claimId `0008-ellipsoid-inverse-ctor`. Sister park of ADR-0007 G3 / K3 (`IntakeGeodesicCook.v : sheet_chord_misses_pole`, `IntakeKarneyPark.v`).

---

## Context (self-contained)

ADR-0007's sheet is \(S=(O;e_1,e_2)\). On that sheet a geodesic is a chord. `GEODESICSTRING` bags `MkChord`. That letter is closed as planar cook (#788) plus named parks (ambient manifold, wire, Karney 2013 ingest #789). It is **not** the inverse geodesic problem on an ellipsoid of revolution.

That problem is classical (Legendre, Oriani, Bessel, Helmert). Vincenty (1975a) gave desk-calculator iterations still in widespread use; the inverse **fails to converge** near antipodes. Vincenty (1975b) patches the back-side branch and can take many thousands of iterations. Karney (2013) replaces the fixed point with Newton on

\[
f(\alpha_1)=\lambda_{12}(\alpha_1)-\lambda^\star=0,
\]

using reduced length \(m_{12}\) as \(f'\) (his Fig. 5), and claims the first complete numerical inverse. Algorithms and series stay in GeographicLib. This ADR does not re-implement them.

What neither Vincenty nor Karney writes in ADR-0007's vocabulary: the inverse is a **constructor** with Empty ≠ Decline ≠ MintTwo. When \(m_{12}=0\), neighbouring geodesics reconverge; \(\alpha_1\) is not unique (opposite poles; the fold in Karney Fig. 4). A failed while-loop is not Decline. A second shortest geodesic is not a second Decline.

Halley iteration on the same residual is not this ADR. It does not restore uniqueness when \(f'=0\).

## Decision 1 — a second sheet class, not a new egg on \(S\)

An ellipsoid of revolution \(E(a,f)\) is a **sheet class**. It is not ADR-0007 `Sheet`. It does not inhabit `MkChord` equality.

- No `EggGeodesic` on the planar sheet.
- No `first_cook_scope` expand.
- No Oracle keyword in this ADR.
- Planar `GEODESICSTRING` intake stays #788.

Rejected: sneak Karney \(\gamma\) into ADR-0007 Parks as a discharge of G3.

## Decision 2 — inverse is `IResult`, licensed by \(m_{12}\)

On \(E(a,f)\), two distinct points determine a residual \(f(\alpha_1)\). The constructor is:

| Geometry | `IResult` | Licence |
|---|---|---|
| unique shortest geodesic | `IHit` | simple root, \(m_{12}\neq 0\) |
| two shortest geodesics (oblate fold, \(\lambda_{12}\approx\pm\pi\), \(\phi_2\approx-\phi_1\)) | `MintTwo` | two roots; same hen policy as circular \(p_\pm\) |
| opposite poles / conjugate pair, \(m_{12}=0\) | `IDecline` | constructor refuses to pick \(\alpha_1\) |
| coincident points | named degenerate, **not** Decline | no curve to mint |

Iteration (Helmert, Vincenty 1975a/b, Newton, Halley) is an **implementation** of this constructor, not the specification. 1975a has no Decline; its failure is a loop. That fact is a QEX letter (E3), not a reason to code the loop here.

## Decision 3 — letters are QED ∨ QEX only

| Ticket | Close |
|---|---|
| E0 planar sheet is not this sheet | **QED** pointer to G3 / K3 |
| E1 \(m_{12}=0\) is Decline | **QED** on a locked opposite-pole pair, or **QEX** if `m12` is only cited from Karney Eq. (38) |
| E2 two-root pocket is MintTwo, not a second Decline | **QEX** until two distinct \(\alpha_1\) on one locked oblate pair are named (witness may be GeographicLib; the *statement* is this board) |
| E3 Vincenty 1975a is not this constructor | **QEX** — no iterator in-repo |
| E4 host first cook not expanded | **QED** `~ first_cook_scope EggChord EggCircularArc` unchanged |

Stop when E0–E4 are each QED or QEX. Do not QED “the corpus solves the inverse.” Do not QED IEEE conversion of Karney series.

## Consequences

- ADR-0007 Status stays **Accepted**. G3 stays QEX on that board.
- Karney 2013 remains a research park (`docs/research/karney-2013-algorithms-for-geodesics.md`, claimId `0007-karney-2013-ingest`). This ADR cites it; it does not ingest series as \(\gamma\).
- New Coq, if any, is a sibling (`theories/EllipsoidInverseCtor.v` or similar), 3-axiom Reals ceiling, no Vincenty loop, no Flocq requirement for E0–E4.
- Oracle: no new keyword. If a later letter wants a testable inverse face, it attaches as an ADR-0006 adapter after Accept of *this* board — never as FFI or RocqRefRunner.
- A paper *The inverse geodesic problem as a partial constructor* is in scope as an external write-up of Decision 2. It is not required to Accept.

## Related

- [`ADR-0006-oracle-protocol-is-the-test-surface.md`](ADR-0006-oracle-protocol-is-the-test-surface.md)
- [`ADR-0007-sheet-hen-cook-noding-model.md`](ADR-0007-sheet-hen-cook-noding-model.md)
- Vincenty T (1975a) *Surv Rev* 23(176):88–93; addendum 23(180):294 (1976)
- Vincenty T (1975b) unpublished antipodal inverse, GeographicLib scan
- Karney CFF (2013) *J Geod* 87:43–55, doi:10.1007/s00190-012-0578-z
