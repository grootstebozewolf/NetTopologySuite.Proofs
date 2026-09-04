# ATTACK hobby-41-ledger-drift
- claimId: none
- file:lemma: theories-flocq/HobbyTheorem_b64.v:hobby_theorem_4_1_conditional
- class: ledger-drift
- epic: #66
- topic: overlay
- verdict: ledger-drift
- H1-shaped: no

Target behaviour: the Phase 2 snap-rounding headline the observatory
counts as coverage should be the theorem the kernel can inhabit.

## Repro

```sh
rg -n 'hobby_theorem_4_1_conditional' docs/verified-claims.md
rg -n 'fully_intersected_snap_of_nodable|NodingSeparation' docs/verified-claims.md
rg -n 'largely delivered' TRIAGE_NTS_JTS_ISSUES.md
rg -n 'HobbyTheorem_b64|NodingSeparation_b64' _CoqProject _CoqProject.full
python3 scripts/gen_dashboard.py --check
```

Expected:

- ledger row: `HobbyTheorem_b64.v : hobby_theorem_4_1_conditional` as
  **Conditional headline** `[cond]`
- `fully_intersected_snap_of_nodable` / `NodingSeparation` : no ledger row
- `_CoqProject` (make host): no HobbyTheorem / NodingSeparation
- `_CoqProject.full` only: both modules listed
- dashboard Phase 2 area counts that `[cond]` row as coverage

## What collapses

Three-column drift:

| surface | what it says |
|---|---|
| kernel | The anonymous second premise of `hobby_theorem_4_1_conditional` is uninhabitable (companion ticket). The inhabit-able theorem is `NodingSeparation_b64.fully_intersected_snap_of_nodable` under `pairwise_nodable`. Both `.v` files live only in `_CoqProject.full`. |
| ledger | `docs/verified-claims.md` Phase 2 still cites `hobby_theorem_4_1_conditional` as the live `[cond]` headline ("assuming Lemma 4.3's no-proper half"). Zero rows for the nodable replacement. |
| TRIAGE | `TRIAGE_NTS_JTS_ISSUES.md` row for tracker #66 still says strongest coverage / "largely delivered" and names `Hobby*` among the delivered stack. Status source of record for the closed epic. |
| dashboard | Observatory Phase 2 mix treats that `[cond]` as a coverage theorem. Host-lane `make host` never builds the cited `.v` (relic-proven until a full-lane compile). No oracle mode claims Hobby 4.1 vectors — this is ledger-vs-kernel, not a 0-vector mode. |

`docs/hobby-lemma-4-3-no-proper-refutation.md` and the HobbyTheorem
header still call the headline "unaffected." That prose is the
observatory's blind spot: `[cond]` is filed as an honest gap after the
false lemma was `Abort`ed, so the scanners do not re-classify the
anonymous second arrow that remains.

## Consumer chain

no live apply of the cited headline (see companion uninhabitable
ticket). `validate-claims.sh` will keep passing: the orphan check only
asks whether the identifier exists, not whether the second premise is
inhabited.

## Not a fix

Do not add a ledger row that repeats `hobby_theorem_4_1_conditional`
under a new claimId, and do not mint a named hyp so the `[cond]` badge
can stay. Re-point the Phase 2 row onto
`fully_intersected_snap_of_nodable` after a human FIX, or drop the
`[cond]` row. Wrapping the false second premise to keep the badge is H1.

## Promote?

Phase 2 ledger still counts an uninhabitable `[cond]` and omits the
Qed nodable replacement. TRIAGE's closed-epic row still reads
"largely delivered." Companion: `2026-09-03-hobby-hlemma43-uninhabitable.md`.
Tracker #66 stands completed (2026-08-22); this ticket is a
status-table correction, not a reopen. Joost/Jeroen: promote or stand down.

OUTCOME: LANDED (companion probe Qed on flocq smoke `3515626`; this
ticket is ledger-only and does not need its own `.vo`).
