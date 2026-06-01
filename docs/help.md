# Help — pick your path

Who are you?  Find your card; the OPEN action is enough for the first
60 seconds.  Full reading paths in [`reading-guide.md`](reading-guide.md).

---

🛣️  **Plain Reader Pete**
&nbsp;&nbsp;&nbsp;&nbsp;YOU&nbsp;&nbsp;&nbsp;&nbsp;Clicked a link; want the elevator pitch.
&nbsp;&nbsp;&nbsp;&nbsp;OPEN&nbsp;&nbsp;&nbsp;[`README.md`](../README.md), first three paragraphs.
&nbsp;&nbsp;&nbsp;&nbsp;NEXT&nbsp;&nbsp;&nbsp;GIS Gus · BIM Bea · Newbie Nate.

🌍  **GIS Gus**
&nbsp;&nbsp;&nbsp;&nbsp;YOU&nbsp;&nbsp;&nbsp;&nbsp;Use NetTopologySuite; want to know which geometric primitives are formally proved.
&nbsp;&nbsp;&nbsp;&nbsp;OPEN&nbsp;&nbsp;&nbsp;[`phase0-completion.md`](phase0-completion.md) → `phase1-completion.md` → `phase2-hotpixel-progress.md`.
&nbsp;&nbsp;&nbsp;&nbsp;TIME&nbsp;&nbsp;&nbsp;30 min.

🏗️  **BIM Bea**
&nbsp;&nbsp;&nbsp;&nbsp;YOU&nbsp;&nbsp;&nbsp;&nbsp;Model as-built geometry; care about arcs / CIRCULARSTRING.
&nbsp;&nbsp;&nbsp;&nbsp;OPEN&nbsp;&nbsp;&nbsp;[`audit-phase4-curves.md`](audit-phase4-curves.md).
&nbsp;&nbsp;&nbsp;&nbsp;TIME&nbsp;&nbsp;&nbsp;1 h.

🛠️  **Maintainer Max**
&nbsp;&nbsp;&nbsp;&nbsp;YOU&nbsp;&nbsp;&nbsp;&nbsp;Keep CI green, merge PRs, manage registries.
&nbsp;&nbsp;&nbsp;&nbsp;OPEN&nbsp;&nbsp;&nbsp;[`axiom-allowlist.txt`](axiom-allowlist.txt) + [`audit-exceptions.txt`](audit-exceptions.txt) + [`admitted-deferred-proofs.txt`](admitted-deferred-proofs.txt) + [`admitted-counterexamples.txt`](admitted-counterexamples.txt).
&nbsp;&nbsp;&nbsp;&nbsp;BOOKMARK&nbsp;&nbsp;`scripts/check_admitted.sh`, `audit_axioms.sh`, `check_readme_axioms.sh`.

🎓  **Scholar Sam**
&nbsp;&nbsp;&nbsp;&nbsp;YOU&nbsp;&nbsp;&nbsp;&nbsp;Research formal methods; evaluating corpus methodology.
&nbsp;&nbsp;&nbsp;&nbsp;OPEN&nbsp;&nbsp;&nbsp;[`slice-a-retro.md`](slice-a-retro.md) + [`slice-a-piece-5b-retro.md`](slice-a-piece-5b-retro.md).
&nbsp;&nbsp;&nbsp;&nbsp;CITE&nbsp;&nbsp;&nbsp;Conditional headline + named-hypothesis pattern (four instances).

📋  **Product-Owner Pat**
&nbsp;&nbsp;&nbsp;&nbsp;YOU&nbsp;&nbsp;&nbsp;&nbsp;Decide what ships next; budget sessions.
&nbsp;&nbsp;&nbsp;&nbsp;OPEN&nbsp;&nbsp;&nbsp;[`phase0-completion.md`](phase0-completion.md), `phase1-completion.md`, `phase2-hotpixel-progress.md`, then [`admitted-deferred-proofs.txt`](admitted-deferred-proofs.txt) as backlog.
&nbsp;&nbsp;&nbsp;&nbsp;RULE&nbsp;&nbsp;&nbsp;Budget per registry entry · 1-3 deliverables / session · 1.5× multiplier.

🏃  **Scrum-Master Sara**
&nbsp;&nbsp;&nbsp;&nbsp;YOU&nbsp;&nbsp;&nbsp;&nbsp;Plan sessions; track cadence.
&nbsp;&nbsp;&nbsp;&nbsp;OPEN&nbsp;&nbsp;&nbsp;Top-level retros + [`history/sessions/README.md`](history/sessions/README.md).
&nbsp;&nbsp;&nbsp;&nbsp;TEMPLATE&nbsp;Grep · Red · Green · Refactor · Stopping conditions.

🔎  **Reviewer Ruby**
&nbsp;&nbsp;&nbsp;&nbsp;YOU&nbsp;&nbsp;&nbsp;&nbsp;Review PRs for corpus discipline.
&nbsp;&nbsp;&nbsp;&nbsp;OPEN&nbsp;&nbsp;&nbsp;[`README.md`](../README.md) § "The invariant" + the four registries.
&nbsp;&nbsp;&nbsp;&nbsp;REJECT&nbsp;&nbsp;Bare `Admitted.` · hand-rolled when extracted exists · empty wrappers.

⚙️  **CI Cara**
&nbsp;&nbsp;&nbsp;&nbsp;YOU&nbsp;&nbsp;&nbsp;&nbsp;Own the build pipeline.
&nbsp;&nbsp;&nbsp;&nbsp;OPEN&nbsp;&nbsp;&nbsp;[`.github/workflows/ci.yml`](../.github/workflows/ci.yml) + [`.github/workflows/build-oracle.yml`](../.github/workflows/build-oracle.yml).
&nbsp;&nbsp;&nbsp;&nbsp;PINS&nbsp;&nbsp;&nbsp;Rocq 9.1.1 · Flocq 4.2.2 · OCaml 4.14.2.

🌱  **Newbie Nate**
&nbsp;&nbsp;&nbsp;&nbsp;YOU&nbsp;&nbsp;&nbsp;&nbsp;First contribution.
&nbsp;&nbsp;&nbsp;&nbsp;OPEN&nbsp;&nbsp;&nbsp;[`README.md`](../README.md) § "The invariant" → [`development-environment.md`](development-environment.md).
&nbsp;&nbsp;&nbsp;&nbsp;FIRST PR&nbsp;Smallest entry in `admitted-deferred-proofs.txt` you understand.

🔬  **Auditor Avery**
&nbsp;&nbsp;&nbsp;&nbsp;YOU&nbsp;&nbsp;&nbsp;&nbsp;Independent formal-methods audit.
&nbsp;&nbsp;&nbsp;&nbsp;OPEN&nbsp;&nbsp;&nbsp;The four registries + `scripts/audit_axioms.sh /tmp/full-build.log`.
&nbsp;&nbsp;&nbsp;&nbsp;TIERS&nbsp;&nbsp;&nbsp;Forbidden / counterexample / deferred-proof.

🧑‍🔧  **Tech-Lead Tess**
&nbsp;&nbsp;&nbsp;&nbsp;YOU&nbsp;&nbsp;&nbsp;&nbsp;Design new engagements; sequence sessions.
&nbsp;&nbsp;&nbsp;&nbsp;OPEN&nbsp;&nbsp;&nbsp;Retros + [`point-in-ring-correct-seam-map.md`](point-in-ring-correct-seam-map.md) as exemplar.
&nbsp;&nbsp;&nbsp;&nbsp;PATTERNS&nbsp;Two-route design · Seam map · Red/green workflow.

📦  **Consumer Connie**
&nbsp;&nbsp;&nbsp;&nbsp;YOU&nbsp;&nbsp;&nbsp;&nbsp;Use `oracle_bin` from downstream (e.g. `.Curve`).
&nbsp;&nbsp;&nbsp;&nbsp;OPEN&nbsp;&nbsp;&nbsp;`oracle/driver.ml` header (protocol reference).
&nbsp;&nbsp;&nbsp;&nbsp;ENV&nbsp;&nbsp;&nbsp;&nbsp;`ROCQ_REF_BIN` → path to binary.

🧭  **NTS-Upstream Norm**
&nbsp;&nbsp;&nbsp;&nbsp;YOU&nbsp;&nbsp;&nbsp;&nbsp;Write NetTopologySuite upstream.
&nbsp;&nbsp;&nbsp;&nbsp;OPEN&nbsp;&nbsp;&nbsp;[`README.md`](../README.md) + phase-completion docs.
&nbsp;&nbsp;&nbsp;&nbsp;MAP&nbsp;&nbsp;&nbsp;&nbsp;`RobustLineIntersector` → `b64_intersect_*` · `RobustDeterminant` → `b64_orient2d`.

⚖️  **Risk-Officer Rico**
&nbsp;&nbsp;&nbsp;&nbsp;YOU&nbsp;&nbsp;&nbsp;&nbsp;Compliance / risk; need to know what's NOT guaranteed.
&nbsp;&nbsp;&nbsp;&nbsp;OPEN&nbsp;&nbsp;&nbsp;[`admitted-counterexamples.txt`](admitted-counterexamples.txt) + [`admitted-deferred-proofs.txt`](admitted-deferred-proofs.txt).
&nbsp;&nbsp;&nbsp;&nbsp;SURFACE&nbsp;Tier 2 (false-as-stated) + Tier 3 (not-yet-proved).

---

Still unsure?  Start with **Plain Reader Pete** and graduate.
