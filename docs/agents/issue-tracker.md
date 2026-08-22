# Issue tracker: GitHub

Issues and specs for this repo live as GitHub issues
(`grootstebozewolf/NetTopologySuite.Proofs`). Use the `gh` CLI for all
operations.

## Conventions

- **Create an issue**: `gh issue create --title "..." --body "..."`. Use a heredoc for multi-line bodies.
- **Read an issue**: `gh issue view <number> --comments`, filtering comments by `jq` and also fetching labels.
- **List issues**: `gh issue list --state open --json number,title,body,labels,comments --jq '[.[] | {number, title, body, labels: [.labels[].name], comments: [.comments[].body]}]'` with appropriate `--label` and `--state` filters.
- **Comment on an issue**: `gh issue comment <number> --body "..."`
- **Apply / remove labels**: `gh issue edit <number> --add-label "..."` / `--remove-label "..."`
- **Close**: `gh issue close <number> --comment "..."`

Infer the repo from `git remote -v` — `gh` does this automatically when run inside a clone.

## Pull requests as a triage surface

**PRs as a request surface: no.** _(Set to `yes` if this repo treats external PRs as feature requests; `/triage` reads this flag.)_

When set to `yes`, PRs run through the same labels and states as issues, using the `gh pr` equivalents:

- **Read a PR**: `gh pr view <number> --comments` and `gh pr diff <number>` for the diff.
- **List external PRs for triage**: `gh pr list --state open --json number,title,body,labels,author,authorAssociation,comments` then keep only `authorAssociation` of `CONTRIBUTOR`, `FIRST_TIME_CONTRIBUTOR`, or `NONE` (drop `OWNER`/`MEMBER`/`COLLABORATOR`).
- **Comment / label / close**: `gh pr comment`, `gh pr edit --add-label`/`--remove-label`, `gh pr close`.

GitHub shares one number space across issues and PRs, so a bare `#42` may be either — resolve with `gh pr view 42` and fall back to `gh issue view 42`.

## When a skill says "publish to the issue tracker"

Create a GitHub issue.

## When a skill says "fetch the relevant ticket"

Run `gh issue view <number> --comments`.

## Wayfinding operations

Used by `/wayfinder`. The **map** is a single issue with **child** issues as tickets.

- **Map**: a single issue labelled `wayfinder:map`, holding the Notes / Decisions-so-far / Fog body. `gh issue create --label wayfinder:map`.
- **Child ticket**: an issue linked to the map as a GitHub sub-issue (`gh api` on the sub-issues endpoint). Where sub-issues aren't enabled, add the child to a task list in the map body and put `Part of #<map>` at the top of the child body. Labels: `wayfinder:<type>` (`research`/`prototype`/`grilling`/`task`). Once claimed, the ticket is assigned to the driving dev.
- **Blocking**: GitHub's **native issue dependencies** — the canonical, UI-visible representation. Add an edge with `gh api --method POST repos/<owner>/<repo>/issues/<child>/dependencies/blocked_by -F issue_id=<blocker-db-id>`, where `<blocker-db-id>` is the blocker's numeric **database id** (`gh api repos/<owner>/<repo>/issues/<n> --jq .id`, _not_ the `#number` or `node_id`). GitHub reports `issue_dependencies_summary.blocked_by` (open blockers only — the live gate). Where dependencies aren't available, fall back to a `Blocked by: #<n>, #<n>` line at the top of the child body. A ticket is unblocked when every blocker is closed.
- **Frontier query**: list the map's open children (`gh issue list --state open`, scoped to the map's sub-issues / task list), drop any with an open blocker (`issue_dependencies_summary.blocked_by > 0`, or an open issue in the `Blocked by` line) or an assignee; first in map order wins.
- **Claim**: `gh issue edit <n> --add-assignee @me` — the session's first write.
- **Resolve**: `gh issue comment <n> --body "<answer>"`, then `gh issue close <n>`, then append a context pointer (gist + link) to the map's Decisions-so-far.

## This repo's existing issue conventions

Facts a skill should know before writing to this tracker (audited 2026-08-22):

- **Open issues are proof _programs_, not tasks** — epics `#64`–`#69` plus
  extended programs (`#423` metrics, `#424` hulls, `#425` coverage), each with a
  horizon label (`Immediate` / `Urgent` / `Expectant` / `Non-urgent`).
- **`TRIAGE_NTS_JTS_ISSUES.md` is the declared source of record** for per-epic
  status and the upstream-issue → epic wire map. Prefer updating it over
  duplicating status into issue bodies.
- **Dependencies are expressed in prose, not GitHub machinery** — `Umbrella: #69`
  lines, `_Part of the … batch (#64–#68)._` footers, and per-epic
  `### Blocker status` sections. No issue currently uses task lists, sub-issues,
  or native dependencies. A wayfinder map introducing them is a new convention
  here; the body-convention fallbacks above are the low-friction option.
- **`claimId` is the real subtask currency** — `docs/macro-meso-micro.md` defines
  the macro (epic) / meso (`.v` module) / micro (`claimId` + `witness`) scales;
  live ids look like `64-b`, `68-a`, `424-b`, usually mirrored in
  `eval/Claim<id>.v`.
- **PR bodies carry review-gate tags** — `topics:`, `witness:`, `claimId:`, and
  an issue reference; a tooling-only PR should also state its proof surface
  explicitly (see merged `#494`–`#500` for the pattern).

## Machinery reads prose — two traps, both observed

Commits, PR bodies and docs in this repo routinely *discuss* issues and proof
artefacts rather than acting on them. Two scanners cannot tell the difference,
and both have already fired on text that asserted the opposite of what they
concluded.

**1. A negated closing keyword still closes.** GitHub matches
`close`/`closes`/`closed`/`fix`/`fixes`/`resolve`/`resolves` immediately followed
by an issue reference, and ignores everything before it. This subject line closed
issue #67:

```
Resolve ticket 07: decide NOT to close #67; settle the convention as ADR-0003
```

The commit's entire purpose was recording the decision *not* to close it. When a
commit or PR discusses an issue it is not closing, avoid those verbs next to the
number — write **retire**, **stands down**, **declines to close**, **leaves
open**, or move the reference into a separate clause. Reserve the keywords for
closures you intend.

**2. The review gate's "No new Admitted" check scans added lines regardless of
file type.** A docs-only PR (#502) was refuted because a sentence *asserted* the
corpus contains no admitted proofs and therefore contained the token. Write about
admitted proofs without the literal `Admitted.` form, or expect the block. Note
the build guard is looser than the review gate here: `scripts/check_admitted.sh`
only walks `theories*/` and anchors the pattern to a line of its own.

The general rule: **when writing about a mechanism, assume its scanner is
reading.** Both traps cost a round trip, and both looked like a substantive
review failure until the text was read.
