# Stage D Push Retro

**Date.** May 2026. Five red-workflow cycles across one focused session.

**Context.** Continuation of Stage D after the policy framework and CI ratchet landed earlier in the day. The session was the first sustained test of the red-green-refactor discipline operating with the rigorous CI gauntlet as the refactor phase. Goal: ship what Qeds cleanly, document tangents at the first sign of friction, accumulate empirical data on cycle time and prediction accuracy.

## Cycle outcomes

```mermaid
flowchart LR
    A[b64_Dekker_nonoverlap] -->|Qed ~10 min| A1[58e1fbf]
    B[chain3_correct] -->|Qed ~15 min| B1[174cc50]
    C[chain4 + helper] -->|Qed ~5 min| C1[2d1df4a]
    D[Dekker_then_TwoSum] -->|Qed ~5 min| D1[5badf6c]
    E[DekkerPair_sum] -->|Tangent| E1[5badf6c docs]
    style A1 fill:#d4edda,stroke:#155724
    style B1 fill:#d4edda,stroke:#155724
    style C1 fill:#d4edda,stroke:#155724
    style D1 fill:#d4edda,stroke:#155724
    style E1 fill:#fff3cd,stroke:#856404
```

| Slice | Hypothesis | Outcome | Time |
|-------|-----------|---------|------|
| `b64_Dekker_nonoverlap` | error ≤ half-ulp via Dekker_correct + error_le_half_ulp_round | Qed first attempt | ~10 min |
| `b64_TwoSum_chain3_correct` | 2× TwoSum_correct + lra | Qed first attempt | ~15 min |
| `b64_TwoSum_chain4_correct` + helper | chain_n pattern scales mechanically | Qed first attempt | ~5 min |
| `b64_Dekker_then_TwoSum_correct` | Dekker_correct + TwoSum_correct + lra | Qed first attempt | ~5 min |
| `b64_DekkerPair_sum_correct` | 2× Dekker + chain4 via lra | Tangent documented | ~10 min before stop |

Four Qed-closed cleanly, one documented tangent. All five commits landed with the full local CI gauntlet green before push (Qed-invariant grep + README↔allowlist consistency + per-theorem axiom audit running sequentially + full corpus build).

## The red workflow as it operated

```mermaid
flowchart TD
    Red[Red: state hypothesis, predict tangent]
    Green[Green: attempt proof]
    Qed{Qed?}
    Tangent[Capture tangent doc, stop]
    Refactor[Refactor: run CI gauntlet locally]
    Pass{Audit passes?}
    Commit[Commit and push]
    Fix[Fix or restructure, return to Green]
    Red --> Green
    Green --> Qed
    Qed -->|yes| Refactor
    Qed -->|no, friction surfaces| Tangent
    Refactor --> Pass
    Pass -->|yes| Commit
    Pass -->|no, axiom or invariant violation| Fix
    Fix --> Green
    style Red fill:#f8d7da,stroke:#721c24
    style Green fill:#d4edda,stroke:#155724
    style Refactor fill:#d1ecf1,stroke:#0c5460
    style Tangent fill:#fff3cd,stroke:#856404
    style Commit fill:#d4edda,stroke:#155724
```

The workflow's three phases operated with bounded cognitive load each. Red phase produced a falsifiable hypothesis with a predicted tangent. Green phase either closed with Qed or surfaced a tangent — both clean exits. Refactor phase ran the CI gauntlet as a verification step; pass means commit, fail means return to Green. No middle states.

## The calibration update

The earlier Stage D doc had estimated the chain-composition piece at "1-3 days." This session's data revises that in two directions simultaneously.

```mermaid
flowchart LR
    A[Stage D pieces]
    A --> B[Pff lifts and single-op bounds]
    A --> C[Chain composition]
    B --> B1[Original estimate: months]
    B1 --> B2[Revised estimate: minutes per piece]
    B2 --> B3[Compression: 30-150x]
    C --> C1[Original estimate: 1-3 days]
    C1 --> C2[Sum correctness: minutes each]
    C1 --> C3[Nonoverlap design: 1-3 days unchanged]
    C1 --> C4[Let-shape ergonomics: ~30 lines]
    style B3 fill:#d4edda,stroke:#155724
    style C2 fill:#d4edda,stroke:#155724
    style C3 fill:#fff3cd,stroke:#856404
    style C4 fill:#fff3cd,stroke:#856404
```

For Pff lifts and single-operation bounds, estimates compressed 30-150x. Each piece is bookkeeping plus a few well-known Flocq lemmas. The original "months" framing for the full Stage D engagement was a substantial overestimate for these pieces.

For chain composition, the picture is more nuanced than the previous revision suggested. The sum-correctness portion compresses to minutes per piece, matching the Pff lift pattern. The nonoverlap-preservation portion remains 1-3 days because it's algorithmic-design work, not bookkeeping. A new piece surfaced: the let-shape ergonomics issue costs ~30 lines for the restatement, and is its own distinct piece worth naming.

The net effect: Stage D is not "months" and not "5 days" uniformly. It's a mix of fast pieces (most lifts and sum-correctness work) and genuinely substantive pieces (nonoverlap design, the let-shape restatement, the eventual headline composition).

## Tangent prediction accuracy

Each cycle's red phase predicted a likely tangent before the proof attempt. Comparing predictions to outcomes is informative about how well the discipline's anticipation is calibrated.

```mermaid
flowchart LR
    P1[chain3: predicted bookkeeping] -->|matched| O1[no tangent, helper pre-extracted prevented]
    P2[chain4: predicted preconditions grow] -->|prevented| O2[helper extraction in advance]
    P3[Dekker_then_TwoSum: predicted let-pair extraction] -->|matched| O3[handled inline]
    P4[DekkerPair: predicted bookkeeping smell] -->|mismatched| O4[actual: let-shape lra interaction]
    style O1 fill:#d4edda,stroke:#155724
    style O2 fill:#d4edda,stroke:#155724
    style O3 fill:#d4edda,stroke:#155724
    style O4 fill:#fff3cd,stroke:#856404
```

Three predictions matched (chain3, chain4, Dekker_then_TwoSum). One missed: DekkerPair's predicted tangent was "12 nested safety preconditions, bookkeeping smell." The actual tangent was a tactical pattern-matching issue with `lra` and let-bindings — same family as Dekker attempts 2 and 3 from earlier in the project's history, but not what the red phase anticipated.

The miss is informative. In-domain pattern matching ("this looks like more of what we've been doing") drifted toward predicting the friction shape from recent successful cycles rather than from the broader corpus history. The Dekker attempt 2-3 family of friction wasn't in the immediate working memory because the recent cycles had been clean.

## Observations worth carrying forward

**The discipline self-organizes WIP selection.** At any moment in the cycle, one phase is blocked and the next action is whatever unblocks it. The cognitive load on "what should I work on" drops near zero. This is what good operational discipline produces — the decision becomes tactical rather than strategic.

**Tangent prediction is becoming part of the red phase.** The cycles that predicted their tangents accurately produced cleaner outcomes (chain4's helper extraction was pre-emptive refactor between cycles). Tangent prediction is testable and the prediction's accuracy is feedback for the next cycle's red phase.

**Family-membership of tangents matters.** The DekkerPair tangent is the same family as Dekker attempts 2-3. Documenting tangents with explicit family notes lets future cycles reach for known recipes when similar friction appears. The Dekker recipe (chain rewrites in hypotheses not in goal, `change` for definitional alignment) might apply directly to the DekkerPair fix.

**The "5 days vs months" framing was too binary.** Different pieces of Stage D have different cost shapes. The right framing is per-piece estimates with the calibration table as a reference, not a single time budget for the whole engagement.

**Meta-level pattern recognition is now visible.** The workflow operating reflexively — pre-emptive refactor between cycles, anticipating tangents in hypotheses, knowing when to stop — is the maturity of the discipline making itself legible. This is the deepest outcome of the session.

## Open items as inputs to future sessions

```mermaid
flowchart LR
    R[Retro shipped]
    R --> O1[DekkerPair let-shape fix]
    R --> O2[Chain-composition nonoverlap design]
    R --> O3[Phase 1 coordinate story]
    R --> O4[Category C policy decision]
    O1 -->|~30 lines, family-known| F1[bounded, next cycle]
    O2 -->|1-3 days, algorithmic design| F2[substantive engagement]
    O3 -->|new domain, queued| F3[unblocks Phase 2]
    O4 -->|four inputs identified| F4[pending policy work]
    style F1 fill:#d4edda,stroke:#155724
    style F2 fill:#fff3cd,stroke:#856404
    style F3 fill:#d1ecf1,stroke:#0c5460
    style F4 fill:#f8d7da,stroke:#721c24
```

The DekkerPair fix is the smallest bounded next-cycle option, with the tangent family identified. The chain-composition nonoverlap is the largest substantive piece still ahead in Stage D. Phase 1's coordinate story is the queued unblocker for Phase 2. The Category C policy decision is the load-bearing decision waiting on the four named inputs.

Each is a legitimate next slice. None has a deadline that forces ordering. The discipline says: pick one based on attention available and cognitive state, run the cycle, stop at the principled endpoint.

## What the retro itself demonstrates

Writing this retro as a session deliverable rather than another proof cycle reflects the workflow operating at its mature form. The session produced more than just commits; it produced a re-usable observation about how the discipline operates. Capturing the observation while it's vivid prevents it from fading, and gives future sessions a reference point for what good cycle execution looks like.

The retro is itself a kind of refactor at the project level — running the audit on how the project operates, not just on the corpus's invariants. The CI ratchet catches per-commit drift. The policy framework catches per-decision drift. The workflow catches per-session drift. The retro catches drift in the operating discipline itself, surfacing patterns that are otherwise tacit.

---

Five Qed commits, one tangent documented, one retro shipped. The discipline is working. The corpus is in good shape. The next session begins with whatever inputs the maintainer brings to it, and the artifacts from today are ready as that session's starting context.
