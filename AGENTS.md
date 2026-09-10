# Agent Instructions

These are baseline rules for any AI agent (Copilot, ChatGPT, Cursor, etc.)
working in this repository, whether run interactively by a contributor or
autonomously (e.g. as a coding agent on a PR).

This is **NetTopologySuite.Proofs** — a Rocq/Flocq proof corpus plus the
extracted oracle and differential harnesses. It is not the NTS C# library.
Session workflow lives in [docs/FOR-AI-AGENTS.md](docs/FOR-AI-AGENTS.md).

Adapted from [NetTopologySuite#875](https://github.com/NetTopologySuite/NetTopologySuite/pull/875)
(`e064b57`). Same shape; Proofs-specific fences below.

## Disclosure

- **Any AI-assisted contribution must be disclosed.** Say so explicitly in
  the PR description and/or commit message (e.g. "This PR was drafted with
  AI assistance"). This file is the disclosure rule; there is no separate
  `AI_POLICY.md`.
- Disclosure does not replace review: the human submitting the PR remains
  fully responsible for correctness, licensing, and quality.

## Project rules

- Read [CONTRIBUTING.md](CONTRIBUTING.md) before making changes; it defines
  the Qed / registry invariants and actor paths.
- Make the smallest change that accomplishes the task. No unrelated
  refactors, renames, or reformatting.
- Do not silently break the public surface. Prefer additive changes; flag
  any breaking change (oracle wire, extracted API, cited theorem names)
  instead of making it silently.
- Honour `claimId` / `witness` fences. Do not remint an existing claimId.
  Do not steal a witness. `claimId: none` is valid for docs and packaging.
- A QED∨QEX stop is honest: QED is a constructed inhabitant; QEX is a
  documented missing constructor or out-of-scope pair. QEX is not owner
  accept and is not "done."
- Host CircGamma stays QEX. Do not remint CircGamma theater. Sidecar cook
  ≠ host cook (`I_ok_circ` / `I_ok_mixed` Hit is not host `I_ok`).
- Rocq host lane is Stdlib (`theories/`); Flocq lane is `theories-flocq/`.
  The oracle (`oracle_bin`) is the differential test surface (ADR-0006).
  Do not invent a second protocol.
- ADR-0007 is Accepted. First cook scope stays chord–chord unless a letter
  explicitly expands it.

## Before finishing

- Run `make ci-guards` for anything you touched; don't leave CI or guards
  broken.
- Summarize what changed and why, and call out any AI involvement per the
  disclosure rule above.
