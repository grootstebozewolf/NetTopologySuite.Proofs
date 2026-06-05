# Help — pick your path

**Note (HoTT pivot):** The detailed phase-completion, audit, and proof-structure documents referenced by several cards below now live under [`archive/docs/`](archive/docs/). The classical corpus they describe has been archived; the personas themselves are deliberately kept. New HoTT + C# linkage work will update or extend these cards over time.

Who are you? Find your card; the OPEN action is enough for the first
60 seconds. Full reading paths in [`READING-GUIDE.md`](READING-GUIDE.md).

---

🌍 **GIS Gus**

**YOU** Use NetTopologySuite; want to know which geometric primitives are formally proved.

**OPEN** (historical classical results — now archived) [`archive/docs/phase0-completion.md`](archive/docs/phase0-completion.md) → `archive/docs/phase1-completion.md` → `archive/docs/phase2-hotpixel-progress.md`.

**TIME** 30 min.

---

🏗️ **BIM Bea**

**YOU** Model as-built geometry; care about arcs / CIRCULARSTRING.

**OPEN** (historical) [`archive/docs/audit-phase4-curves.md`](archive/docs/audit-phase4-curves.md).

**TIME** 1 h.

---

🛠️ **Quality Gatekeeper (Max/Ruby)**

**YOU** Keep the (future) HoTT build green, review PRs for adherence to the (much lighter) HoTT invariants, and especially review the justifications for the single allowed axiom + the strength of the C# linkage/equivalence claims.

**OPEN** Top-level [`README.md`](../README.md) § "Axiom policy (HoTT era)" + [`docs/axiom-policy.md`](axiom-policy.md) + the four (archived) registries under `archive/docs/` (for any classical material) + archived CI in `archive/.github/workflows/ci.yml` + [`archive/old-README-Proofs.md`](archive/old-README-Proofs.md) § "The invariant".

**BOOKMARK / REJECT** (classical era) Run `archive/scripts/check_admitted.sh`, `archive/scripts/audit_axioms.sh`, `archive/scripts/check_readme_axioms.sh`. For new HoTT work: reject bare `admit`, undocumented extra axioms, or linkage claims with no actual equivalence or transport. Be generous on the one allowed axiom when the justification and C# story are good. (CI Cara and Risk-Officer Rico details live here now.)

---

🎓 **Scholar Sam (incl. Auditor Avery)**

**YOU** Research formal methods / mechanised geometry and evaluate the corpus methodology, now including the HoTT pivot, univalent linkage to C#, and whether "one axiom, generous" is being used responsibly.

**OPEN** (historical classical methodology) [`archive/docs/slice-a-retro.md`](archive/docs/slice-a-retro.md) + [`archive/docs/slice-a-piece-5b-retro.md`](archive/docs/slice-a-piece-5b-retro.md) + the archived registries under `archive/docs/` + (old) `archive/scripts/audit_axioms.sh`. For the new era also read [`docs/axiom-policy.md`](axiom-policy.md) + root `README.md` § "Axiom policy (HoTT era)" + any early HoTT modules + their equivalence justifications.

**CITE** Conditional headline + named-hypothesis pattern (four instances) from the classical work; also the new univalent transport / one-axiom justification patterns.

**TIERS / POLICY** Old forbidden/counterexample/deferred-proof tiers (archived); new HoTT work is judged on the quality of the single-axiom justification + real C# linkage value.

---

📋 **Project Meta (Pat/Sara)**

**YOU** Decide what ships next, budget sessions, plan cadence, and retrospect on how the work actually went.

**OPEN** Archived top-level retros under `archive/docs/` + `archive/docs/phase*-completion.md` / `phase2-hotpixel-progress.md` + archived `admitted-deferred-proofs.txt` + [`archive/docs/history/sessions/README.md`](archive/docs/history/sessions/README.md).

**RULE / TEMPLATE** Budget per registry entry (Pat). Use "Grep first → Red → Green → Refactor → explicit stopping conditions" (Sara). Sessions average 1-3 deliverables; ~10% collapse (always documented).

---

🌱 **Newbie Nate (incl. Plain Reader Pete / 🧮 Rocq Rookie Ray)**

**YOU** First contribution, or clicked a link and want the elevator pitch, or have literally never seen a proof assistant before.

**OPEN** top-level [`README.md`](../README.md) (HoTT pivot notice) + (historical) [`archive/docs/development-environment.md`](archive/docs/development-environment.md).

(If you have literally never seen a proof assistant before, start with the hands-on [`pythagoras-for-beginners.v`](pythagoras-for-beginners.v) example — it is self-contained, step-by-step with `ring` vs explicit rewrites, and explains why even "obvious" geometry takes real machine time + compute. It has been lightly updated for the HoTT pivot.)

**FIRST PR** (classical) Smallest entry in `archive/docs/admitted-deferred-proofs.txt` you understand. (For HoTT-era first contributions, see the top-level README + CONTRIBUTING.)

---

🧑‍🔧 **Tech-Lead Tess**

**YOU** Design new engagements; sequence sessions.

**OPEN** Archived retros + [`archive/docs/point-in-ring-seams-3-5-7-red.md`](archive/docs/point-in-ring-seams-3-5-7-red.md) (or `archive/docs/point-in-ring-jct-path.md`) as exemplar seam-map / JCT path work (still conceptually relevant for HoTT synthetic topology). Also the live `docs/hott-rgr-risk-cost-pivot.md` as an RGR risk/cost analysis for the linkage pivot.

**PATTERNS** Two-route design · Seam map · Red/green workflow · risk/cost pivots.

---

📦 **Consumer Connie**

**YOU** Use `oracle_bin` from downstream (e.g. `.Curve`).

**OPEN** Archived `archive/oracle/driver.ml` header (protocol reference for the classical oracles).

**ENV** `ROCQ_REF_BIN` → path to binary.

---

🧭 **NTS-Upstream Norm**

**YOU** Write NetTopologySuite upstream.

**OPEN** top-level [`README.md`](../README.md) (pivot + HoTT vision) + archived phase-completion docs under `archive/docs/`.

**MAP** `RobustLineIntersector` → `b64_intersect_*` · `RobustDeterminant` → `b64_orient2d`.

---

🧠 **Joost the BDFL (Joost mag het weten)**

**YOU** The benevolent dictator for life. "Joost mag het weten" — the Dutch proverb meaning only Joost (may) know(s) it all.

**OPEN** The full (new) README + every section of [`READING-GUIDE.md`](READING-GUIDE.md) + the entire `archive/docs/history/` tree (you are expected to understand the shape of the classical corpus and why the pivot was made; the archive is your responsibility to know).

**POWER** Final authority on scope, what constitutes "useful for an actor", tie-breakers in pruning decisions, and whether a marginal file stays at top level or gets archived. You can promote files back from history/.

**NEXT** Everything. You are the one person who is assumed to have (or be able to form) the complete picture.

---

**Still unsure?** Start with **Newbie Nate (incl. Plain Reader Pete / Rocq Rookie Ray)** (and the `pythagoras-for-beginners.v` example if you have literally never seen a proof assistant) and graduate. The list above has been collapsed where roles had heavy overlap (e.g. Pat/Sara, Max/Ruby, Auditor into Scholar, CI/Risk into Quality, Pete into Nate/Ray).

---

## Quick links for the impatient

- **I just cloned this** → read this file + top-level [`README.md`](../README.md) (HoTT pivot notice) + [`docs/axiom-policy.md`](axiom-policy.md) (the generous one-axiom rule)
- **I want the complete map** → [`READING-GUIDE.md`](READING-GUIDE.md)
- **I have literally never seen a proof assistant before** → [`pythagoras-for-beginners.v`](pythagoras-for-beginners.v) (step through it in an IDE; linked from the Newbie Nate / Rocq Rookie card)
- **I want the deep history of the classical corpus** → `archive/` (old README, all phase/audit/retro docs, full session history, the proofs themselves)
- **I contribute (or an AI agent does)** → `CONTRIBUTING.md` + [`FOR-AI-AGENTS.md`](FOR-AI-AGENTS.md) + [`docs/axiom-policy.md`](axiom-policy.md) (one axiom, generous) + the session workflow sections of the Reading Guide (still applicable; outputs now target HoTT + C# linkage)
- **I am Joost the BDFL** → full (new) README + entire READING-GUIDE + entire `archive/docs/history/` tree + pruning log in `archive/docs/history/README.md`

(Note: the card list above has been lightly collapsed for overlap — e.g. Project Meta combines Pat/Sara, Quality Gatekeeper combines Max/Ruby/CI/Risk, Scholar now covers Auditor, Pete folded into Newbie Nate/Rocq Rookie Ray. The detailed guide below reflects the same grouping.)

**Axiom policy (HoTT era):** One axiom allowed — let's be generous (see root `README.md` § "Axiom policy (HoTT era)").

The spirit of the rule remains:

> New work ends with `Qed.` (or `Defined.`).  
> Bare `admit` or extra axioms still need explicit justification.  
> Nothing quietly stubbed.

Welcome. Pick your card and go. The HoTT chapter is just beginning.