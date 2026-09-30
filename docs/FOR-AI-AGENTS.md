# For AI Agents (and deep contributors using agent workflows)

Root baseline (disclosure, smallest change, guards): [`AGENTS.md`](../AGENTS.md).
Session workflow and invariants for agents on this corpus, informed by Scholar
Sam, Scrum-Master Sara, Tech-Lead Tess, and Joost the BDFL in the
[Reading Guide](READING-GUIDE.md) and [Help cards](HELP.md). Start from
`make help` / `docs/HELP.md` (actor roles; the reviewer often role-plays one).

## Hard Invariants (non-negotiable, CI-enforced)
- Every theorem ends with `Qed.` (or `Defined.` for computable terms).
- No `Axiom`, no `Parameter`, no bare `admit.` in `.v` files.
- Only the three classical-reals axioms allowed (see `docs/axiom-allowlist.txt`).
- `Admitted` theorems must be registered in exactly one of:
  - `docs/admitted-counterexamples.txt` (theorem-as-stated is false; permanent; verified counterexample on file).
  - `docs/admitted-deferred-proofs.txt` (theorem is true; proof structure documented; temporary; comes off when proved).
- Run the gauntlet on changes: `make ci-guards` (plus `scripts/audit_axioms.sh` after an output-synced or -j1 build log; see the script header).
- `Print Assumptions` must pass the allowlist (with documented exceptions in `audit-exceptions.txt`).
- A False-valued marker names a missing definition/constructor; discharging it means defining the thing and proving a real statement, not proving the marker.

Unregistered `Admitted` = build failure. No quiet stubs.

## Session Workflow (Red/Green/Refactor pattern from Sara/Tess paths)
Successful sessions follow a consistent shape (see retros like `slice-a-retro.md`, `slice-a-piece-5b-retro.md`, `stage-d-retro.md` for examples):

1. **Grep first**: Use tools (grep, read_file, git log, etc.) to gather current corpus state before writing new prompts or code. Understand existing lemmas, deferred proofs, and consumer chains.

2. **Red phase**: State the simplest target lemma + predicted tangents (in order of likelihood). Document stopping conditions explicitly (full success vs. tangent-stop criteria). Use "two-route design" when the load-bearing approach is uncertain.

3. **Green phase**: Attempt deliverables in order. Stop at the first genuine tangent. Record LANDED / PARTIAL / COLLAPSED.

4. **Refactor phase**: Run the full CI gauntlet scripts. Clean up. Update registries if a new deferred Admitted or counterexample is needed (with discharge plan + consumer chain).

5. **Outcome**: attempted, landed (names), remaining gaps, branch, plan relation.

~10% of sessions collapse; document them. Stacked PRs: review bottom first.

## Using the Archive
Session essays under `docs/history/sessions/` were deleted
(claimId `0007-prose-chip-sessions`). Recover them from git history
at those paths on prior SHAs. Do not restate them. Start from the
relevant `*-retro.md`. Joost the BDFL has final say on archive decisions.

## Joost the BDFL (Joost mag het weten)
- You (or the human directing you) may be acting in this role.
- Full visibility: README (all status), entire READING-GUIDE + all referenced docs, full history/ tree.
- Powers: final authority on scope, what is "useful for an actor", pruning tie-breakers, whether marginal files stay top-level or get archived.
- In practice: when in doubt on a design or prune decision, document the rationale as if Joost is reviewing.

## Practical Tips for Agents
- The `.claude/startup-rocq.sh` (or equivalent) sets up the pinned Rocq 9.2.0 + Flocq 4.2.2 environment.
- Use the root `Makefile`: `make help`, `make host` (for theories/), `make check` (guardrails), `make env-info`.
- For extraction/oracle work: see `oracle/` + `docs/oracle-handroll-migration.md` etc. Consumer Connie path.
- Cross-reference JTS/NTS: every file header should name the corresponding module/algorithm. Use the sibling `jts/` checkout for mapping.
- Zero Coq prior: `docs/pythagoras-for-beginners.v`.
- When proposing new sessions: follow the Red/Green template. Budget 1-3 deliverables per session; multiply estimates by 1.5x for unknowns. One registry entry at a time for thesis-scale work.
- AI disclosure: always include in headers/outcomes per CONTRIBUTING.md.

## Key Files for Agents (quick reference)
- Invariants & registries: the four .txt files in docs/.
- Hunt tickets: `docs/attacks/`. Qed-claiming probes: `docs/h1-vacuity/` (compiled by the flocq job via `scripts/hunt_probe_smoke.sh`; not product modules in `_CoqProject.full`).
- Session examples: the `*-retro.md` files.
- Proof structures: `hobby-theorem-proof-structure.md`, `shewchuk-theorem-13-proof-structure.md`, seam maps.
- Soundness strategy: `soundness-strategy.md`, `stage-d-*.md` cluster.
- Current status by phase: the `phase*-completion.md`, `audit-*.md`, `*-hotpixel-progress.md` (but prefer the actor-specific ones in your path).

For a scoped slice, reproduce state from the relevant retro + outcome docs, then Red/Green.