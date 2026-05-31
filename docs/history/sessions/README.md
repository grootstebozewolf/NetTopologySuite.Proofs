# Session traces — archive

Per-session forensic record from the sustained engagements that closed
the corpus's deferred-proof entries.  Top-level retros
(`docs/slice-a-retro.md`, `docs/slice-a-piece-5b-retro.md`,
`docs/phase1-c2-tight-retro.md`, `docs/stage-d-retro.md`) consolidate
the session-level material into engagement-level synthesis; the files
here are the underlying record.

Use this archive when you want to:

  - Reconstruct the exact prompt that opened a session (Scrum Master,
    Tech Lead).
  - Read the load-bearing stuck-goal text from a session that didn't
    close (Scholar).
  - Trace which session landed which Qed (Maintainer, Auditor).
  - Audit failed design-route attempts (collapse artifacts) for
    methodology lessons (Scholar).

For all other purposes, the top-level retros are the right entry
point.

---

## Slice A Piece 5b — Route 1 (Shewchuk Theorem 13 cascade-invariant path)

17 sessions, May–June 2026.  Headline:
`fast_expansion_sum_nonoverlap_shewchuk_general_conditional` Qed-closed
+ three unconditional consumer-path corollaries.  Outcome retro:
`docs/slice-a-piece-5b-retro.md`.

| Session | Prompt | Outcome / artifact | Status |
|---|---|---|---|
| 2 | `slice-a-piece-5b-route1-session-2-prompt.md` | `slice-a-piece-5b-route1-session-2-collapse.md` | collapse — `cs_run_max` mathematically inadequate |
| 3 | (consolidated into retro) | (consolidated into retro) | design refinement |
| 4 | `slice-a-piece-5b-route1-session-4-prompt.md` | `slice-a-piece-5b-route1-session-4-outcome.md` | partial — per-source maxes finding |
| 5 | (none archived) | `slice-a-piece-5b-route1-session-5-outcome.md` | partial — pivot to staged inequality |
| 6 | (none archived) | `slice-a-piece-5b-route1-session-6-outcome.md` | all clause-(d′) preservation |
| 7 | (none archived) | `slice-a-piece-5b-route1-session-7-outcome.md` | h-chain Path A positive case |
| 8 | (none archived) | `slice-a-piece-5b-route1-session-8-outcome.md` | clause-(a) preservation Path A |
| 9 | (none archived) | `slice-a-piece-5b-route1-session-9-outcome.md` | partial — negative case landed |
| 10 | (none archived) | `slice-a-piece-5b-route1-session-10-outcome.md` | cascade invariant Path A composition |
| 11 | (none archived) | `slice-a-piece-5b-route1-session-11-outcome.md` | partial — state-machine bridge |
| 12 | (none archived) | `slice-a-piece-5b-route1-session-12-outcome.md` | cascade-output nonoverlap |
| 13 | (none archived) | `slice-a-piece-5b-route1-session-13-outcome.md` | two-singletons int-safe headline |
| 14 | (none archived) | `slice-a-piece-5b-route1-session-14-outcome.md` | two-singletons general + helper |
| 15 | (none archived) | `slice-a-piece-5b-route1-session-15-outcome.md` | inductive cascade lemma |
| 16 | (none archived) | `slice-a-piece-5b-route1-session-16-outcome.md` | all three pieces landed |
| 17 | (none archived) | `slice-a-piece-5b-route1-session-17-outcome.md` | conditional general theorem Qed |

Plus design artifact: `slice-a-piece-5b-route1-design-session.md`.

## Slice A Piece 5b — Route 2 attempt (cascade_step_preserves_invariant
path)

Route 2 was a design route attempting to discharge
`cascade_step_preserves_invariant` directly.  Session 2 collapsed; the
collapse artifact informed the Route 1 design.

| Artifact | Content |
|---|---|
| `slice-a-piece-5b-session-2-prompt.md` | Route 2 Session 2 prompt |
| `slice-a-piece-5b-session-2-collapse.md` | Route 2 Session 2 collapse: nonoverlap_strict counterexample at TwoSum exact step |

## Phase 1 Scope C.2-tight — forward-error theorem

6 sessions, May 2026.  Headline: `b64_intersect_point_x_forward_error_
vs_intersect_x_R` Qed-closed (forward-error bound +
`HasIntersect_sound` typeclass instance).  Outcome retro:
`docs/phase1-c2-tight-retro.md`.

| Session | Outcome | Status |
|---|---|---|
| 1 | `phase1-c2-tight-session-1-outcome.md` | denominator forward-error |
| 2 | `phase1-c2-tight-session-2-outcome.md` | partial — subnormal-range ulp scope-down |
| 3 | `phase1-c2-tight-session-3-outcome.md` | three Qed deliverables |
| 4 | `phase1-c2-tight-session-4-outcome.md` | four Qed deliverables |
| 5 | `phase1-c2-tight-session-5-outcome.md` | x-coordinate bridge |
| 6 | `phase1-c2-tight-session-6-outcome.md` | `HasIntersect_sound_BPoint` instance |

## Single-session artifacts

| File | Engagement | Content |
|---|---|---|
| `hobby-lemma-4-2-session-1-outcome.md` | Hobby Lemma 4.2 | Single-session attempt outcome |
| `m5-s15-conditional-headline-prompt.md` | Phase 3 M5 S15 | The prompt that opened `overlay_ng_correct_conditional` (Phase 3 headline) |

---

## Naming convention

  - `*-session-N-prompt.md`: the prompt that opened session N (input).
  - `*-session-N-outcome.md`: the post-session summary (output).
  - `*-session-N-collapse.md`: a failed design-route artifact, kept
    for forensic value.
  - `*-design-session.md`: design-phase artifact between sessions.

The convention is stable; new session archives should follow it.

## Why archived rather than deleted

  - **Maintainer + Auditor**: traceability — every Qed-closed lemma
    can be linked to the session that landed it.
  - **Scrum Master**: prompt-outcome cadence for retrospective
    analysis.
  - **Scholar**: precise stuck-goal text from sessions that surfaced
    methodology lessons.
  - **Tech Lead**: design-route collapse artifacts (Route 2
    Session 2; Route 1 Session 4 per-source maxes finding) preserve
    the "what we tried and why it didn't work" record.

For day-to-day reading, the top-level retros are the right starting
point.
