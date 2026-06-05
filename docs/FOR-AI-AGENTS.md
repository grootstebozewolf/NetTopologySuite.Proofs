# For AI Agents (and deep contributors using agent workflows)

This document extracts the session workflow, invariants, and practical guidance relevant to AI coding agents (Claude, Grok, etc.) working on this corpus. It is informed by the paths for Scholar Sam, Scrum-Master Sara, Tech-Lead Tess, and Joost the BDFL in the [Reading Guide](READING-GUIDE.md) and [Help cards](HELP.md).

**Note:** This is now the HoTT-pivot era. The classical proof corpus, build, and most detailed docs are archived under `archive/`. The session workflow, Red/Green/Refactor discipline, and persona system are preserved because they remain useful. Outputs should target HoTT formalisations and C# linkage artefacts.

**Always start here for context:**
- Read the current state via top-level `README.md` + `cat docs/HELP.md`.
- The consolidated actor roles (lightly collapsed from original ~17 for overlap; see HELP.md / READING-GUIDE.md) are defined there. Your "user" or reviewer will often be role-playing one or more (e.g., Joost the BDFL for final decisions, or a specific contributor type).

## Hard Invariants (HoTT era — one axiom, let's be generous)

- New theorems, equivalences, and transports must still end with `Qed.` (or `Defined.` for computable terms). The "nothing quietly stubbed" spirit is invariant.
- **One axiom is allowed.** This is the new generous default for HoTT work (usually the Univalence axiom or the minimal standard HoTT assumption needed for the C# linkage story). See the "Axiom policy (HoTT era)" section in the root `README.md` for the exact expectations: document the justification in the header, keep the rest `Qed.`, be thoughtful rather than bureaucratic.
- Bare `admit` (without a clear justification + discharge plan) is still not okay.
- When you are reading, editing, or transporting lemmas *from the archived classical corpus*, the old strict rules apply (see `archive/docs/axiom-allowlist.txt`, the old registries, and `archive/scripts/` guardrails).
- For brand-new HoTT + C# linkage work the emphasis is on useful equivalences and transport, not on recreating the full classical audit theatre around every assumption.

The old heavy CI gauntlet scripts live in `archive/scripts/` and are only required when touching classical material. New HoTT developments will have lighter, more targeted review focused on the one-axiom justification and the actual C# correspondence value.

## Session Workflow (Red/Green/Refactor pattern from Sara/Tess paths)
Successful sessions follow a consistent shape (see archived retros like `archive/docs/slice-a-retro.md`, `archive/docs/slice-a-piece-5b-retro.md`, `archive/docs/stage-d-retro.md` for examples):

1. **Grep first**: Use tools (grep, read_file, git log, etc.) to gather current corpus state before writing new prompts or code. Understand existing lemmas, deferred proofs, and consumer chains.

2. **Red phase**: State the simplest target lemma + predicted tangents (in order of likelihood). Document stopping conditions explicitly (full success vs. tangent-stop criteria). Use "two-route design" when the load-bearing approach is uncertain.

3. **Green phase**: Attempt deliverables in order. Stop at the first genuine tangent. Record LANDED / PARTIAL / COLLAPSED.

4. **Refactor phase**: Clean up. For classical material, run the archived gauntlet in `archive/scripts/`. For new HoTT work, review the one-axiom justification (per the root README policy) and the equivalence/transport claims to C#. Update any relevant notes or future lightweight registry if a deferred piece is carried.

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
- Refactor: policy review (one-axiom justification for new HoTT work; archived classical gauntlet only when touching old material).
- Explicit stopping conditions.

**Collapse rate**: ~10% of sessions collapse outright; always document them (they provide useful negative results).

**Stacked PRs / cascades**: Common. Review bottom PR first.

## Using the Archive (now under archive/)
Most actors are told to **skip** `archive/docs/history/sessions/` except for deep work or when mining classical lemmas for HoTT re-expression.
- Use it when you need the full chronology of a closed engagement (e.g., why Route 2 collapsed, exact tangents hit in Slice A Piece 5b).
- Start from the relevant `*-retro.md` under `archive/docs/`, then descend into `archive/docs/history/`.
- The `archive/docs/history/README.md` and `archive/docs/history/sessions/README.md` explain the layout and pruning batches.
- Pruning followed (and will continue to follow) the actor filter + stop condition. Joost the BDFL has final say on borderline archive decisions.

The entire classical corpus + docs now lives under `archive/`. New HoTT work will generate its own (lighter) history under `docs/` or a `docs/hott-sessions/` subtree.

Never move or delete from `archive/` without following the process (inventory against the defined actor roles, git log + grep audit for each candidate, <10% restoration threshold on the batch). The top-level `archive/README.md` is the entry point.

## Joost the BDFL (Joost mag het weten)
- You (or the human directing you) may be acting in this role.
- Full visibility: README (all status), entire READING-GUIDE + all referenced docs, full history/ tree.
- Powers: final authority on scope, what is "useful for an actor", pruning tie-breakers, whether marginal files stay top-level or get archived.
- In practice: when in doubt on a design or prune decision, document the rationale as if Joost is reviewing.

## Practical Tips for Agents (HoTT pivot)
- The classical pinned Rocq + Flocq + `.claude/startup-rocq.sh` + container live in `archive/`.
- There is currently no root `Makefile` or `make help` (those were for the archived classical build). `docs/pythagoras-for-beginners.v` only needs a stock Rocq install.
- For extraction/oracle work (classical): everything is now under `archive/oracle/` + `archive/docs/oracle-*.md`.
- Cross-reference JTS/NTS: every new header should name the corresponding C# NTS module/algorithm + the classical archived counterpart where relevant.
- When a human (or you) says "I've never used Coq before", point them at `docs/pythagoras-for-beginners.v` first. It is a self-contained, heavily commented step-by-step example whose main purpose is to let absolute beginners experience what formal proof feels like *and* to pre-bunk "why so much compute on obvious geometry?" critiques. It has been refreshed for the pivot.
- When proposing new sessions: follow the Red/Green template (still documented here). Budget 1-3 deliverables per session; multiply estimates by 1.5x for unknowns. For the pivot, early sessions are likely "re-express X classically-proved fact in HoTT" or "sketch equivalence between Coq Foo and NTS C# Bar".
- AI disclosure: always include in headers/outcomes per CONTRIBUTING.md.

## Key Files for Agents (quick reference — HoTT pivot)
- Top-level vision + axiom policy: `README.md` (especially § "Axiom policy (HoTT era)"), `GETTING-STARTED.md`, `CONTRIBUTING.md`.
- Personas (unchanged): `docs/HELP.md`, `docs/READING-GUIDE.md`, `docs/FOR-AI-AGENTS.md` (this file), and the new `docs/axiom-policy.md`.
- Beginner on-ramp (the single kept proof): `docs/pythagoras-for-beginners.v`.
- Full classical archive: `archive/` (old README, all docs, proofs, oracle, scripts, history, CI).
- Session workflow examples: `archive/docs/*-retro.md` + `archive/docs/history/sessions/` (classical); new-era RGR pivots (e.g. risk/cost analyses for the linkage) live in `docs/` (see `docs/hott-rgr-risk-cost-pivot.md`).
- Proof structures / seam maps (still conceptually relevant): under `archive/docs/` (hobby-*, shewchuk-*, point-in-ring-*, jct-* etc.).

If your task is scoped to a slice of the *classical* work, first reproduce state from the relevant retro in the archive. For new HoTT work, the same Red/Green/Refactor + explicit stopping conditions shape applies; the deliverables are now HoTT modules + linkage sketches.

Welcome to the HoTT chapter. Pick (or be assigned) a role card, follow the documented path, and produce clean, Qed-closed work that advances the link between formal Coq and C# NTS. Joost mag het weten.