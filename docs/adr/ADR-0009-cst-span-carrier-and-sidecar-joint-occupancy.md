# ADR-0009 — CST carries circular span; sidecar joints occupy R5-agree

Sheet S is a plane, not an arc. A concat-endpoint Hit on sidecar `I_ok_mixed` / `I_ok_circ` is R5-agree occupancy and is not host `I`.

| Field | Value |
|---------------|--------------------------------------------------------------|
| **Order** | ADR-0009 |
| **Status** | **Accepted** — 2026-09-30 (Joost) |
| **Deciders** | Joost (BDFL) to Accept; proposed by Jeroen Bloemscheer |
| **Date** | 2026-09-30 |
| **Supersedes** | — (none) |
| **Does not reopen** | ADR-0005 (lenient intake / strict IsValid); ADR-0007 (planar sheet, hen, cook; Accepted 2026-09-07) |

claimId `0009-cst-span-carrier`. Implements #866 / #771 carry-and-check. Does not flip `first_cook_scope`. Does not remint `0007-intake-angles`.

---

## Context

Phase B letters B.1–B.3 and B-bags already inhabit concat / ring-close / membership joints. Host mixed `I_ok` stays Decline. Intake of a proper partial arc (`A ≠ B`) still writes `θ₀ = 0`, `Δθ = ±2π` (`0007-intake-angles`), so carry-and-check has nowhere to put the numbers (`#866`).

## Decision

1. **Span carrier lives on the CST**, as `list (option (R * R))` beside `CircSlice` — one slot per 3-point window. `CircSlice` stays `CircQuarter | CircFullOgc | CircUnknown`. `Sheet` stays `(O; e₁, e₂)` + lattice. One pair for a whole multi-arc string is forbidden.
2. **Sidecar joint occupancy counts for R5-agree.** A Hit at `(end, t=1, t=0)` on `I_ok_circ` or `I_ok_mixed` is enough. Host mixed `I` is `#767`, not this occupancy.
3. **Phase B done-when** is the joints conjunction B.1 ∧ B.2 ∧ B.3 ∧ B-bags. Parks: `ι`, host mixed `I`, CircGamma, ρ, Multi required-type. Multi Gap does not block Landed. Paperwork is a letter after Accept on ADR-0007, not this ADR.
4. **Authorship and reasons.** Fixtures and factory rows supply the list. A window with `A ≠ B` and `None` is `ID_MissingCircSpan`. A present slot that fails the check is `ID_CircSpanDisagree`. `A = B` / `CircFullOgc` ignores that window's slot and stays intake-angles. The check for a window `(A M B)` is `γ(0)=A`, `γ(1)=B`, and `M` on-arc.

## Considered options

- Span fields on `Sheet` — two arcs on one plane would share one `(θ₀, Δθ)`.
- One `option (R * R)` on the whole CircularString — two windows, one span; the Sheet mistake one level up.
- Dual-write S ∧ CST — a new invariant with no buyer.
- Mint `CircularEgg` before the CST can fail closed — flips μ order.
- Fourth `CircSlice` constructor holding numbers — overloads a shape tag.
- Parser computes the pair for `A ≠ B` — remints intake-angles as compute-and-store.
- Count only host `I` as R5-agree — Mixed / mixed-CC / mixed-CP never occupy the joints climb.
- Phase B Landed waits on interior `ι` or the SQL/MM cathedral — folds parked letters into a joints campaign the files already fence.

## Consequences

- `#866` can land as a thin walker/CST patch plus `ID_*` reasons. No Sheet remint. No CircGamma remint.
- Observatory can flip Phase B to Landed from the existing joint theorems plus the done-when letter.
- `#767` remains the host mixed-`I` product decision. This ADR does not flip `first_cook_scope`.
- Production WKT partial arcs Decline until a fixture/factory carries span. That is fail-closed, not a grammar change.

## Related

- [`ADR-0005-lenient-intake-strict-isvalid-curve-types.md`](ADR-0005-lenient-intake-strict-isvalid-curve-types.md)
- [`ADR-0007-sheet-hen-cook-noding-model.md`](ADR-0007-sheet-hen-cook-noding-model.md)
- Proofs #866, #771, #767
