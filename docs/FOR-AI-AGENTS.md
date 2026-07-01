# For AI Agents (and deep contributors using agent workflows)

This document extracts the session workflow, invariants, and practical guidance relevant to AI coding agents (Claude, Grok, etc.) working on this corpus. It is informed by the paths for Scholar Sam, Scrum-Master Sara, Tech-Lead Tess, and Joost the BDFL in the [Reading Guide](READING-GUIDE.md) and [Help cards](HELP.md).

**Always start here for context:**
- Read the current state via `make help` (or cat docs/HELP.md).
- The consolidated actor roles (lightly collapsed from original ~17 for overlap; see HELP.md / READING-GUIDE.md) are defined there. Your "user" or reviewer will often be role-playing one or more (e.g., Joost the BDFL for final decisions, or a specific contributor type).

## Hard Invariants (non-negotiable, CI-enforced)
- Every theorem ends with `Qed.` (or `Defined.` for computable terms).
- No `Axiom`, no `Parameter`, no bare `admit.` in `.v` files.
- Only the three classical-reals axioms allowed (see `docs/axiom-allowlist.txt`).
- `Admitted` theorems must be registered in exactly one of:
  - `docs/admitted-counterexamples.txt` (theorem-as-stated is false; permanent; verified counterexample on file).
  - `docs/admitted-deferred-proofs.txt` (theorem is true; proof structure documented; temporary; comes off when proved).
- Run the gauntlet on changes: `scripts/check_admitted.sh`, `scripts/audit_axioms.sh` (needs an output-synced or -j1 build log; see the script header), `scripts/check_readme_axioms.sh`, `scripts/validate-claims.sh`.
- `Print Assumptions` must pass the allowlist (with documented exceptions in `audit-exceptions.txt`).

Unregistered `Admitted` = build failure. No quiet stubs.

## Session Workflow (Red/Green/Refactor pattern from Sara/Tess paths)
Successful sessions follow a consistent shape (see retros like `slice-a-retro.md`, `slice-a-piece-5b-retro.md`, `stage-d-retro.md` for examples):

1. **Grep first**: Use tools (grep, read_file, git log, etc.) to gather current corpus state before writing new prompts or code. Understand existing lemmas, deferred proofs, and consumer chains.

2. **Red phase**: State the simplest target lemma + predicted tangents (in order of likelihood). Document stopping conditions explicitly (full success vs. tangent-stop criteria). Use "two-route design" when the load-bearing approach is uncertain.

3. **Green phase**: Attempt deliverables in order. Stop at the first genuine tangent. Record LANDED / PARTIAL / COLLAPSED.

4. **Refactor phase**: Run the full CI gauntlet scripts. Clean up. Update registries if a new deferred Admitted or counterexample is needed (with discharge plan + consumer chain).

5. **Outcome document**: Produce a clear outcome (prompt + outcome pair). Include:
   - What was attempted.
   - Deliverables landed (with Coq snippets or theorem names).
   - Remaining gaps (precise, with hypotheses if conditional headline).
   - Branch info.
   - Relation to the plan (e.g., "closes piece X of deferred proof Y").

**Template elements** (from Sara path):
- Grep first.
- Red: simplest target + tangents.
- Green: deliverables, stop at tangent.
- Refactor: gauntlet.
- Explicit stopping conditions.

**Collapse rate**: ~10% of sessions collapse outright; always document them (they provide useful negative results).

**Stacked PRs / cascades**: Common. Review bottom PR first.

## Using the Archive (history/sessions/)
Most actors are told to **skip** `docs/history/sessions/` except for deep work.
- Use it when you need the full chronology of a closed engagement (e.g., why Route 2 collapsed, exact tangents hit in Slice A Piece 5b).
- Start from the relevant `*-retro.md` at top level, then descend.
- The `docs/history/README.md` and `docs/history/sessions/README.md` explain the layout and recent pruning batches.
- Pruning follows the actor filter + stop condition (see pruning log in history/README). Joost the BDFL has final say on borderline archive decisions.

Never move or delete without following the process (inventory against the defined actor roles, git log + grep audit for each candidate, <10% restoration threshold on the batch).

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
- When a human (or you) says "I've never used Coq before", point them at `docs/pythagoras-for-beginners.v` first. It is a self-contained, heavily commented step-by-step example whose main purpose is to let absolute beginners experience what formal proof feels like *and* to pre-bunk "why so much compute on obvious geometry?" critiques.
- When proposing new sessions: follow the Red/Green template. Budget 1-3 deliverables per session; multiply estimates by 1.5x for unknowns. One registry entry at a time for thesis-scale work.
- AI disclosure: always include in headers/outcomes per CONTRIBUTING.md.

## Key Files for Agents (quick reference)
- Invariants & registries: the four .txt files in docs/.
- Session examples: the `*-retro.md` + specific session prompt/outcome pairs in history/sessions/ (when needed).
- Proof structures: `hobby-theorem-proof-structure.md`, `shewchuk-theorem-13-proof-structure.md`, seam maps.
- Soundness strategy: `soundness-strategy.md`, `stage-d-*.md` cluster.
- Current status by phase: the `phase*-completion.md`, `audit-*.md`, `*-hotpixel-progress.md` (but prefer the actor-specific ones in your path).

If your task is scoped to a slice (e.g., "close the deferred proof for X"), first reproduce the current state by following the relevant retro + any outcome docs. Then apply the Red/Green process.

Welcome to the corpus. Pick (or be assigned) a role card, follow the documented path, and produce clean, Qed-closed, registry-respecting work. Joost mag het weten.