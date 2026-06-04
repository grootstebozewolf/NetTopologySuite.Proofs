# Help — pick your path

Who are you? Find your card; the OPEN action is enough for the first
60 seconds. Full reading paths in [`READING-GUIDE.md`](READING-GUIDE.md).

---

🌍 **GIS Gus**

**YOU** Use NetTopologySuite; want to know which geometric primitives are formally proved.

**OPEN** [`phase0-completion.md`](phase0-completion.md) → `phase1-completion.md` → `phase2-hotpixel-progress.md`.

**TIME** 30 min.

---

🏗️ **BIM Bea**

**YOU** Model as-built geometry; care about arcs / CIRCULARSTRING.

**OPEN** [`audit-phase4-curves.md`](audit-phase4-curves.md).

**TIME** 1 h.

---

🛠️ **Quality Gatekeeper (Max/Ruby)**

**YOU** Keep CI green, own the build pipeline details, manage the registries, review PRs for adherence to the invariants and discipline, and understand the explicit risk surface (the registered Admitted tiers).

**OPEN** The four registries (`axiom-allowlist.txt`, `audit-exceptions.txt`, `admitted-*.txt`) + [`.github/workflows/ci.yml`](../.github/workflows/ci.yml) + [`README.md`](../README.md) § "The invariant".

**BOOKMARK / REJECT** Run `scripts/check_admitted.sh`, `audit_axioms.sh`, `check_readme_axioms.sh`. Reject bare `Admitted.`, hand-rolled OCaml when extracted versions exist, or empty wrappers with no new content. (CI Cara and Risk-Officer Rico details live here now.)

---

🎓 **Scholar Sam (incl. Auditor Avery)**

**YOU** Research formal methods / mechanised geometry and evaluate the corpus methodology (including independent trust-chain audits).

**OPEN** [`slice-a-retro.md`](slice-a-retro.md) + [`slice-a-piece-5b-retro.md`](slice-a-piece-5b-retro.md) + the four registries + `scripts/audit_axioms.sh /tmp/full-build.log`.

**CITE** Conditional headline + named-hypothesis pattern (four instances).

**TIERS** Forbidden / counterexample / deferred-proof (when auditing).

---

📋 **Project Meta (Pat/Sara)**

**YOU** Decide what ships next, budget sessions, plan cadence, and retrospect on how the work actually went.

**OPEN** Top-level retros + `phase*-completion.md` / `phase2-hotpixel-progress.md` + [`admitted-deferred-proofs.txt`](admitted-deferred-proofs.txt) as backlog + [`history/sessions/README.md`](history/sessions/README.md).

**RULE / TEMPLATE** Budget per registry entry (Pat). Use "Grep first → Red → Green → Refactor → explicit stopping conditions" (Sara). Sessions average 1-3 deliverables; ~10% collapse (always documented).

---

🌱 **Newbie Nate (incl. Plain Reader Pete / 🧮 Rocq Rookie Ray)**

**YOU** First contribution, or clicked a link and want the elevator pitch, or have literally never seen a proof assistant before.

**OPEN** [`README.md`](../README.md) § "The invariant" → [`development-environment.md`](development-environment.md).

(If you have literally never seen a proof assistant before, start with the hands-on [`pythagoras-for-beginners.v`](pythagoras-for-beginners.v) example — it is self-contained, step-by-step with `ring` vs explicit rewrites, and explains why even "obvious" geometry takes real machine time + compute.)

**FIRST PR** Smallest entry in `admitted-deferred-proofs.txt` you understand.

---

🧑‍🔧 **Tech-Lead Tess**

**YOU** Design new engagements; sequence sessions.

**OPEN** Retros + [`point-in-ring-seams-3-5-7-red.md`](point-in-ring-seams-3-5-7-red.md) (or `point-in-ring-jct-path.md`) as exemplar seam-map / JCT path work.

**PATTERNS** Two-route design · Seam map · Red/green workflow.

---

📦 **Consumer Connie**

**YOU** Use `oracle_bin` from downstream (e.g. `.Curve`).

**OPEN** `oracle/driver.ml` header (protocol reference).

**ENV** `ROCQ_REF_BIN` → path to binary.

---

🧭 **NTS-Upstream Norm**

**YOU** Write NetTopologySuite upstream.

**OPEN** [`README.md`](../README.md) + phase-completion docs.

**MAP** `RobustLineIntersector` → `b64_intersect_*` · `RobustDeterminant` → `b64_orient2d`.

---

🧠 **Joost the BDFL (Joost mag het weten)**

**YOU** The benevolent dictator for life. "Joost mag het weten" — the Dutch proverb meaning only Joost (may) know(s) it all.

**OPEN** The full README + every section of [`READING-GUIDE.md`](READING-GUIDE.md) + the entire `docs/history/` tree (you are expected to understand the shape of the whole corpus and why each artifact is where it is).

**POWER** Final authority on scope, what constitutes "useful for an actor", tie-breakers in pruning decisions, and whether a marginal file stays at top level or gets archived. You can promote files back from history/.

**NEXT** Everything. You are the one person who is assumed to have (or be able to form) the complete picture.

---

**Still unsure?** Start with **Newbie Nate (incl. Plain Reader Pete / Rocq Rookie Ray)** (and the `pythagoras-for-beginners.v` example if you have literally never seen a proof assistant) and graduate. The list above has been collapsed where roles had heavy overlap (e.g. Pat/Sara, Max/Ruby, Auditor into Scholar, CI/Risk into Quality, Pete into Nate/Ray).

---

## Quick links for the impatient

- **I just cloned this** → `make help` (in the repo root) or read this file
- **I want the complete map** → [`READING-GUIDE.md`](READING-GUIDE.md)
- **I have literally never seen a proof assistant before** → [`pythagoras-for-beginners.v`](pythagoras-for-beginners.v) (step through it in an IDE; linked from the Newbie Nate / Rocq Rookie card)
- **I want to build something** → [`development-environment.md`](development-environment.md) + the root `Makefile`
- **I contribute (or an AI agent does)** → `CONTRIBUTING.md` + [`FOR-AI-AGENTS.md`](FOR-AI-AGENTS.md) + the session workflow sections of the Reading Guide
- **I am Joost the BDFL** → full README + entire READING-GUIDE + `docs/history/` tree + pruning log in history/README.md

(Note: the card list above has been lightly collapsed for overlap — e.g. Project Meta combines Pat/Sara, Quality Gatekeeper combines Max/Ruby/CI/Risk, Scholar now covers Auditor, Pete folded into Newbie Nate/Rocq Rookie Ray. The detailed guide below reflects the same grouping.)

The corpus rule is simple and non-negotiable:

> Every theorem ends with `Qed.` (or `Defined.`).  
> No bare `Admitted`, no `Axiom`, no `Parameter`, no `admit.` in the `.v` files.  
> The only exceptions are the six registered entries with explicit, documented justification.

Welcome. Pick your card and go.