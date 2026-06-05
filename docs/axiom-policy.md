# Axiom policy — HoTT era

**One axiom allowed. Let's be generous.**

## The old (classical) rule (archived)

The pre-pivot "Froq" corpus under `archive/` was extremely strict:

- Only the three standard classical-reals axioms that Rocq ships with were permitted anywhere in `theories/`.
- `theories-flocq/` inherited one more (`Classical_Prop.classic`) structurally from Flocq's binary64 model — this was tracked per-file in `audit-exceptions.txt` and analysed in `category-c-policy.md`.
- `Axiom`, `Parameter`, and the `admit.` tactic were banned outright.
- The only exceptions were six explicitly registered `Admitted` theorems (split into permanent counterexamples and temporary deferred proofs) with full discharge plans and consumer chains.
- Every `Print Assumptions` was audited in CI against `axiom-allowlist.txt` by `scripts/audit_axioms.sh`.
- Multiple guardrail scripts (`check_admitted.sh`, `check_readme_axioms.sh`, etc.) ran on every build and PR.

This discipline was appropriate for a multi-year, multi-phase effort to mechanically verify the load-bearing geometry primitives of NetTopologySuite down to the reals with no silent stubs.

All of that machinery and history lives in `archive/`.

## The new (HoTT) rule

For the pivot to Homotopy Type Theory the priority has shifted.

We are building a **formal bridge that actually helps link the Coq model to the real C# NetTopologySuite code**. Synthetic homotopy, higher inductive types, and especially univalence are the tools that make "the C# implementation is equivalent to the formal spec" a first-class, transportable statement.

Univalence (or the small set of standard assumptions that come with a practical HoTT library setup) is the natural and expected price of working in this setting.

**Therefore:**

- **One load-bearing axiom is allowed** per major HoTT development or module family.
  - The canonical example is the Univalence axiom (or `Univalence` from the HoTT library / your chosen homotopy layer).
  - Other common candidates: function extensionality in certain universes, or a specific higher inductive type you introduce for a geometric concept (S¹, intervals, etc.).
- The axiom **must be documented** in the file (or module) header:
  - What the axiom is (name + short description).
  - Why it is required for the work.
  - How it helps (or is required for) the C# linkage / equivalence / transport story.
  - What it would take to eliminate or weaken it later.
- Everything else in the development must still be `Qed.` or `Defined.`. No quiet `admit.`
- When a development genuinely seems to need a *second* independent axiom, discuss it with Joost the BDFL. "Generous" does not mean "unlimited."

## What "generous" means in practice

- We will not automatically recreate the old three-tier admitted registry + per-theorem `Print Assumptions` audit theatre for new HoTT work.
- Scholar Sam and Quality Gatekeeper roles will spend their energy reviewing:
  - Is the justification for the one axiom clear and honest?
  - Does using it actually buy us useful, maintainable linkage to the C# side (equivalences, transport of theorems, synthetic characterisations that are hard in the classical setting, etc.)?
  - Is the rest of the code still properly `Qed.`-closed?
- Classical material (anything under `archive/`, or new work that directly re-proves or transports archived lemmas) still follows the old strict rules if you touch it.

## For AI agents and session work

See the updated "Hard Invariants" section in [`FOR-AI-AGENTS.md`](FOR-AI-AGENTS.md). When you are in Red/Green/Refactor mode on new HoTT work, the Refactor phase now includes explicitly calling out the one axiom (if any) and its justification rather than running the full old `archive/scripts/` gauntlet.

## Why this change?

The classical corpus already proved an enormous amount (see `archive/`). The remaining hard problem is not "prove one more lemma with zero extra assumptions." The hard problem is "make the verified model usable and believable for the people who actually ship NetTopologySuite in C#."

Sometimes that requires working synthetically. Sometimes that requires univalence. We are choosing to pay that cost deliberately and document it, rather than contorting the formalisation to avoid the natural axiom of the setting.

One axiom. Let's be generous, and let's ship useful linkage.

---

See also the root [`README.md`](../README.md) (especially the Axiom policy section and the HoTT roadmap) and the persona cards in [`HELP.md`](HELP.md) (Quality Gatekeeper and Scholar Sam have been lightly updated for the new policy).

The old strict allowlist and audit documents remain in `archive/docs/` for historical reference and for any work that touches the classical corpus.
