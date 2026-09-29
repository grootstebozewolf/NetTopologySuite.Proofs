# Glossary rows for CONTEXT.md (ADR-0009)

Splice after **Intake angles**, before **Intake MkClothoid**.
Do not treat this file as a second glossary once the rows are in `CONTEXT.md`.

```md
**Span carrier** (ADR-0009, #866 / #771):
Numeric `(θ₀, Δθ)` per 3-point window of circular text with `A ≠ B`,
carried on the CST as `list (option (R * R))` beside `CircSlice`, not
on `Sheet`. `CircSlice` stays a shape tag (`CircQuarter | CircFullOgc |
CircUnknown`). Intake *checks* each slot; it does not compute atan2 for
`A ≠ B`. A missing slot on `A ≠ B` is `ID_MissingCircSpan`. A present
slot that fails `γ(0)=A`, `γ(1)=B`, and mid-control `M` on-arc is
`ID_CircSpanDisagree`. `A = B` / `CircFullOgc` ignores its slot and
stays intake-angles. Fixtures and factory rows author the list;
production WKT without a slot Declines.
_Avoid_: span fields on Sheet, one pair for a multi-arc string,
compute-and-store, minting CircularEgg before the CST can fail closed

**Joint** (ADR-0007 Phase B, occupancy in ADR-0009):
A cook Hit at a concat or ring-close endpoint: parameters
`(end, t=1, t=0)`. CS–CS uses sidecar `I_ok_circ`; LS–LS uses host
`I_ok`; mixed LS–CS uses sidecar `I_ok_mixed`. Not an interior crossing.
_Avoid_: interior mixed cook (ι), first-cook expand, host mixed I

**Sidecar joint occupancy** (ADR-0009):
A sidecar `I_ok_mixed` / `I_ok_circ` joint Hit is R5-agree occupancy
for Mixed / CC / CP. Host mixed `I_ok` stays Decline and is the #767
letter, not this occupancy.
_Avoid_: treating I_ok_mixed as host I_ok

**Phase B done-when** (ADR-0007 letter after Accept):
B.1 CS concat joints ∧ B.2 CC member joints ∧ B.3 CP ring close ∧
B-bags membership reuse, each with a locked fixture. Parks: interior
mixed cook (ι), host mixed I, CircGamma, ρ, Multi required-type.
Multi required-type Gap does not block Landed. Letter-landed of any
one conjunct is not this conjunction. Paperwork is
`ticket_0007_phase_b_done_when_qed_or_qex`, not a new noding ADR.
_Avoid_: Phase B Open as if a theorem were missing, SQL/MM done,
cathedral Landed
```
