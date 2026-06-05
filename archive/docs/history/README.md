# History / Archive

This directory contains forensic and one-off design artifacts from completed or superseded engagements.

## What belongs here
- Per-session prompt/outcome/collapse files from multi-session proof efforts (e.g. Slice A Piece 5b Route 1, Phase 1 C.2-tight).
- Narrow tangent investigations and early scouting notes that are no longer on the active critical path for any actor.
- Session-level detail that is only required for deep archaeology or when reconstructing the exact history of a deferred-proof registry entry.

## Who this is for
Primarily **Scholar Sam** (formal-methods researcher) and **Tech-Lead Tess** (engagement designer) when they need the full chronology or to understand why a particular design route was abandoned.

Most other actors (GIS Gus, Newbie Nate, Maintainer Max, Product-Owner Pat, etc.) are pointed by the main [Reading Guide](../READING-GUIDE.md) and [Help cards](../HELP.md) to the synthesis documents that remain at the `docs/` root:
- `*-retro.md` files (engagement-level retrospectives)
- `phase*-completion.md` / `audit-*.md` / `*-hotpixel-progress.md` (the documents the roles are actually sent to)
- Proof-structure documents (`hobby-theorem-proof-structure.md`, `shewchuk-theorem-13-proof-structure.md`, etc.)
- Strategy and seam-map documents

**Joost the BDFL** (final authority, with full visibility over the entire history/ tree) has explicit say on archive decisions. (Actor count has been consolidated from 17 by folding overlaps while keeping Joost's distinct BDFL role and the Rocq Rookie on-ramp value.)

## Layout
- `sessions/` — raw per-session transcripts, prompts, collapses, and design-session notes from specific routes (plus legacy completion/retro summaries from pruning passes).
- Individual files directly under `history/` for one-off scouting or tangent work.

These files are retained in git history. They are moved out of the top-level `docs/` listing so that the directory remains scannable for the consolidated actor roles (lightly collapsed from the original 17 for overlap). See the pruning plan (in the session plan.md) for the process, git-audit requirements, and stop-condition rule that governed recent moves. Joost the BDFL has final authority on borderline archive decisions.

If you are here looking for something specific, start from the relevant retro at the parent level and follow the cross-references.
## Pruning log (actor-driven pass)

Date: 2026 (per plan execution)

Batch moved to sessions/ after git audit + stop-condition check (N=4, "meaningful recent use requiring restoration" = 0 < 10%):
- phase2-completion.md
- phase3-completion.md
- phase4-completion.md
- phase4-retro.md

Rationale: Not primary documents in any of the consolidated actor paths in HELP.md / READING-GUIDE.md. Recent activity was creation + "trim ceremony" cleanup. The more specific progress/audit/hotpixel files are the ones recommended to GIS Gus, BIM Bea, Newbie Nate, etc.

Joost the BDFL (added in this pass) has final authority on such decisions.

Core primitives detailed catalogues in README.md also condensed (replaced long per-lemma bullets with high-level list + pointers to the Reading Guide).

See the session plan.md for the full approved pruning plan, process, and stop-condition rule.

## Additional actions in this continue phase (post-initial prune batch)
- Created `docs/FOR-AI-AGENTS.md` (lightweight extraction for agent workflows, pulling session patterns from Sara/Tess/Joost/Scholar paths in the Reading Guide).
- Added Joost the BDFL card/section to live HELP.md and READING-GUIDE.md (with proverb + BDFL role).
- Link hygiene fixes: updated stale `point-in-ring-correct-seam-map.md` references in READING-GUIDE.md and `point-in-ring-jct-path.md` to point to actual existing seam/JCT files (`point-in-ring-seams-3-5-7-red.md`, `point-in-ring-jct-path.md`).
- More polish cross-links: notes in ci.yml (for CI Cara), oracle/driver.ml (for Consumer Connie), development-environment.md, .claude/startup-rocq.sh, audit-shewchuk-stages.md.
- Verified: no top-level references to moved phase completion/retro batch outside history log; old verbose lists in README gone (0 matches for sample bullets); make help promotes 16+; top-level ~37 items (including new FOR-AI-AGENTS.md).
- Actor path spot-checks (via reads): Newbie Nate / Pete / Ray (README + pythagoras), GIS Gus (phase0), BIM Bea (phase4 audit), Newbie Nate (dev-env with note), Scholar/Sara (retros + history access), Tech-Lead (updated seam exemplar), Maintainer / Quality (registries), etc. All recommended start files present at top-level or appropriately noted.
- Stop condition and audits from prior batch remain satisfied; no new large batches moved in this continue (focus on hygiene + surfaces).

See the session plan.md for the full approved plan.

## Polish and verification in final continue phase
- Added references to FOR-AI-AGENTS.md and CONTRIBUTING.md in README.md (Build, Contributing sections), GETTING-STARTED.md, scripts (check_admitted.sh, validate-claims.sh), ci.yml, oracle/driver.ml, and other surfaces.
- Performed actor path walkthroughs via reads/greps for Pete (README), Gus (phase0/1/2 docs), Bea (phase4 audit), Max (registries), Nate (dev-env), Cara (ci.yml), Connie (oracle), Rico (admitted txts), Sam/Sara/Tess (retros, seam red, history access), Joost (full + history + FOR-AI).
- Confirmed moved files only in history, no top-level breakage.
- Updated todos and plan notes.
- All consolidated actor roles' recommended entry points are present and point correctly; updated role counts/groupings in make help, HELP.md, READING-GUIDE, CONTRIBUTING etc. after overlap collapse (Pete+Nate+Ray, Cara+Rico into Quality, Norm+Connie grouping).

## Actor overlap collapse pass (responding to "17 agents, collapse a few with much overlap")

Date: post-Ray addition (17th) + Pete merge start.

**Rationale for collapses (high overlap identified by cross-reading HELP/READING-GUIDE/CONTRIBUTING/Makefile paths):**
- Plain Reader Pete (casual elevator-pitch reader, zero-prior) + Newbie Nate (first contrib + dev-env) + Rocq Rookie Ray (explicit zero-knowledge Coq on-ramp + pythagoras pre-bunk) had near-total overlap for the "absolute beginner / new to proofs" surface. Merged into single prominent card/section: Newbie Nate (incl. Plain Reader Pete / 🧮 Rocq Rookie Ray). Pythagoras integration and pre-bunk purpose preserved and now front-and-center in the beginner path.
- CI Cara and Risk-Officer Rico had dedicated full sections in READING-GUIDE but 90%+ duplicated the Quality Gatekeeper (Max/Ruby) responsibilities (registries, CI scripts, reject rules, dev-env). HELP already grouped them; GUIDE sections removed, responsibilities noted as living under Quality. (CONTRIBUTING and other surfaces folded the names into the combined bullet.)
- Consumer Connie (oracle_bin / .Curve downstream) + NTS-Upstream Norm (NTS code writer mapping algos to proofs) had adjacency for "how proofs surface in / are consumed by real NTS/JTS code". Already partially grouped in oracle/driver.ml, CONTRIBUTING, Makefile (Norm with Gus); further noted in table and on-ramps as "Consumer Connie / NTS-Upstream Norm". BIM Bea kept distinct for arc/CIRCULARSTRING specificity (less overlap).

**Changes made:**
- HELP.md: excised standalone Pete card; retitled/augmented Nate card with Pete/Ray text + pythagoras callout; updated still-unsure, quicklinks, collapsed-notes.
- READING-GUIDE.md: removed Pete section (content folded into Nate); removed full standalone ## CI Cara and ## Risk-Officer Rico sections (redirect notes added to Quality); updated Nate section + summary table + cross notes + "other 15" -> "defined actors"; grouped Connie/Norm in table.
- Makefile, CONTRIBUTING.md, FOR-AI-AGENTS.md, README.md, GETTING-STARTED.md, development-environment.md, .github/workflows/ci.yml: propagated names, updated "16 actors" phrasing to "consolidated ... (collapsed from 17 for overlap)", folded lists.
- history/README.md + sessions/README.md: updated refs + this log entry.
- No content lost: all unique responsibilities (pythagoras on-ramp, CI details, risk tiers, oracle protocol, NTS mapping) remain reachable via the merged paths. Joost BDFL card and powers untouched and still the exception for full history. Ray's zero-knowledge value preserved (not deleted, just co-located with the beginner card for scannability).

**Verification:**
- `make help` (no Rocq) shows updated beginner line and "collapsed from 17" note.
- Full grep for old standalone headers ("## Plain Reader Pete", "## ⚙️ CI Cara", "## ⚖️ Risk-Officer Rico") outside history/: none.
- "Pete", "Cara", "Rico" mentions now only in merged incl./notes or historical log entries.
- Actor paths for Joost (full + history), Ray/pythagoras (via Nate card + direct file), Quality (registries + CI), etc. still resolve.
- Stop condition not triggered (this was doc surface rationalization, no file moves; prior prune batches already audited).

This reduces the effective "card count" and eliminates redundant reading paths while keeping coverage for the original 17 personas' concerns. Joost retains BDFL tie-breaker power; the pythagoras beginner on-ramp (Ray) remains discoverable early.

See updated HELP.md and READING-GUIDE.md for the current (collapsed) set.
