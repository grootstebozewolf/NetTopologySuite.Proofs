# =============================================================================
# NetTopologySuite.Proofs — Root convenience Makefile
# -----------------------------------------------------------------------------
# This Makefile is SAFE TO COMMIT. It contains only documentation and
# lightweight convenience targets.
#
# It NEVER conflicts with the generated Makefiles produced by
# `rocq makefile` (`Makefile.gen`, `Makefile`, etc.). Those are gitignored.
#
# Philosophy:
#   - `make` or `make help` should be the single best "what do I do now?"
#     experience after a fresh clone, even with zero Rocq installed.
#   - It is persona-aware (see the project's docs/HELP.md and
#     docs/READING-GUIDE.md for the full role cards).
#   - When Rocq *is* present it can delegate; otherwise it prints beautiful,
#     copy-pasteable instructions.
#
# Usage (no Rocq required for the friendly path):
#   make
#   make help
#   make status
#
# Real build targets (require Rocq on $PATH):
#   make host          # build the easy Stdlib-only layer (_CoqProject)
#   make full          # build everything (_CoqProject.full) — needs Flocq
#   make check         # run the CI guardrail scripts
#
# See docs/HELP.md for the role-based "pick your path" cards.
# See docs/READING-GUIDE.md for the complete actor/role navigation.
# =============================================================================

SHELL := /bin/bash

# Detect whether a usable `rocq` (or legacy `coqc`) is on PATH.
# We prefer the modern `rocq` driver.
ROCQ := $(shell command -v rocq 2>/dev/null || command -v coqc 2>/dev/null || echo "")

# Phony targets only — this file never produces real build artefacts.
.PHONY: help status host full check ci-guards ci-pr ci-full oracle clean-env env-info

# -----------------------------------------------------------------------------
# Default target — the most important UX surface after `git clone`
# -----------------------------------------------------------------------------
help: status
	@echo ""
	@echo "NetTopologySuite.Proofs — Quick Start"
	@echo "======================================"
	@echo ""
	@echo "First time here?  →  Open one of these (60-second actions):"
	@echo ""
	@echo "  make help          # (you are here) — role-based guidance"
	@echo "  cat docs/HELP.md   # Beautiful card deck: \"pick your path\""
	@echo "  cat docs/READING-GUIDE.md   # Full role navigation (collapsed from 17 for overlap) with start docs"
	@echo ""
	@echo "Common first actions by role (see docs/HELP.md for the full cards):"
	@echo ""
	@echo "  Newbie Nate (Plain Reader Pete / 🧮 Rocq Rookie Ray)"
	@echo "      →  read README.md (elevator) or docs/pythagoras-for-beginners.v (zero prior Coq/Rocq)"
	@echo "      →  or follow host build / dev-env for first contrib"
	@echo ""
	@echo "  GIS Gus / NTS-Upstream Norm"
	@echo "      →  Read docs/phase0-completion.md (and the later phase docs)"
	@echo ""
	@echo "  BIM Bea (arcs / CIRCULARSTRING)"
	@echo "      →  Read docs/audit-phase4-curves.md"
	@echo ""
	@echo "  Maintainer Max / Reviewer Ruby / Auditor Avery"
	@echo "      →  Inspect the four registries in docs/ + run the check scripts"
	@echo ""
	@echo "  AI agents / Tech-Lead Tess / Scrum-Master Sara"
	@echo "      →  docs/FOR-AI-AGENTS.md (or the session workflow sections"
	@echo "         of the Reading Guide) + .claude/startup-rocq.sh"
	@echo ""
	@echo "------------------------------------------------------------"
	@echo "Build targets (require Rocq on your PATH)"
	@echo "------------------------------------------------------------"
	@echo ""
	@echo "  make host          Build the easy foundational layer (theories/)"
	@echo "                     Uses _CoqProject. Works with stock Rocq 9.1.1"
	@echo "                     (Homebrew / apt). No Flocq required."
	@echo ""
	@echo "  make full          Build the complete corpus (theories-flocq/ too)"
	@echo "                     Requires Flocq 4.2.2. Usually done inside the"
	@echo "                     pinned container (see Dockerfile and"
	@echo "                     docs/development-environment.md)."
	@echo ""
	@echo "  make check         Run the three main CI guardrails locally:"
	@echo "                       scripts/check_admitted.sh"
	@echo "                       scripts/check_readme_axioms.sh"
	@echo "                       (the axiom audit needs a sequential build log)"
	@echo ""
	@echo "  make oracle        Build the standalone RocqRefRunner binary"
	@echo "                     (after extraction). See oracle/Makefile."
	@echo ""
	@echo "  make env-info      Show detected Rocq / Flocq versions (best effort)"
	@echo ""
	@echo "  make clean-env     Remove common generated artefacts (safe)"
	@echo ""
	@echo "------------------------------------------------------------"
	@echo "Oracle differential-testing (RocqRefRunner) — JTS/NTS hardening"
	@echo "------------------------------------------------------------"
	@echo ""
	@echo "  make oracle  builds oracle/oracle_bin; feed it a mode name on the"
	@echo "  first stdin line, then the inputs.  Numbers accept decimal or hex"
	@echo "  float ('0x1.8p-3').  EXACT modes are exact (dyadic/rational) ground"
	@echo "  truth — the references a JTS/NTS implementation is diffed against:"
	@echo ""
	@echo "    ORIENT_EXACT / INCIRCLE_EXACT        exact orientation / in-circle sign"
	@echo "    PASSES_THROUGH_EXACT / _HALFOPEN_EXACT   exact hot-pixel passes-through"
	@echo ""
	@echo "  Precision / hole-count (JTS#979 'buffer with fixed precision removes"
	@echo "  a hole' — a TOPOLOGICAL bug, independent of buffer distance d: a hole"
	@echo "  smaller than the precision grid cell collapses to zero area):"
	@echo ""
	@echo "    HOLE_PRECISION_AUDIT       scale, n, n verts  -> '<exact> <precise>' area signs"
	@echo "    HOLES_SURVIVE_PRECISION    scale, k, k rings  -> 'survived s of k' hole count"
	@echo ""
	@echo "  Hunters / adversarial generators (regenerate their .txt artefacts):"
	@echo ""
	@echo "    bash   oracle/gen_adversarial_tests.sh   # orient/incircle/passes-through vs EXACT"
	@echo "    bash   oracle/gen_hole979_hunt.sh        # precision-induced hole removal (#979)"
	@echo "    python3 oracle/buffer_hole_count.py      # heuristic buffer hole-COUNT (C-shape test)"
	@echo ""
	@echo "Full documentation: README.md + docs/HELP.md + docs/READING-GUIDE.md"
	@echo "Canonical container: see the Dockerfile (Rocq 9.1.1 + Flocq 4.2.2)"
	@echo ""
	@echo "The project rule: every theorem ends with Qed. (or Defined.)."
	@echo "No Axiom, no Parameter, no bare admit. in the .v files."
	@echo ""

# -----------------------------------------------------------------------------
# Status / environment report — always safe and informative
# -----------------------------------------------------------------------------
status:
	@echo "NetTopologySuite.Proofs — Environment Status"
	@echo "============================================="
	@echo ""
	@if [ -n "$(ROCQ)" ]; then \
		echo "Rocq found: $(ROCQ)"; \
		"$(ROCQ)" -v 2>/dev/null | head -1 || echo "  (version query failed)"; \
	else \
		echo "Rocq: NOT FOUND on PATH"; \
		echo ""; \
		echo "You can still do almost everything useful:"; \
		echo "  - Read the proofs and status docs"; \
		echo "  - Use the role cards in docs/HELP.md"; \
		echo "  - Follow the container instructions (Dockerfile)"; \
		echo "  - Read the host-install fallback in docs/development-environment.md"; \
	fi
	@echo ""
	@echo "Project invariants (enforced by CI):"
	@echo "  - Every theorem ends with Qed. (or Defined.)"
	@echo "  - Only three classical-reals axioms allowed (see axiom-allowlist.txt)"
	@echo "  - Admitted theorems must be registered (see admitted-*.txt)"
	@echo "  - Axiom/Parameter/admit. are hard failures"
	@echo ""
	@echo "Next step for most new users:  make help   (or cat docs/HELP.md)"

# -----------------------------------------------------------------------------
# Real build targets (only meaningful when Rocq is present)
# -----------------------------------------------------------------------------
host:
	@if [ -z "$(ROCQ)" ]; then \
		echo "Rocq not found on PATH. Cannot build."; \
		echo "See 'make help' or docs/development-environment.md for options."; \
		exit 1; \
	fi
	@echo "Building the host (Stdlib-only) layer with _CoqProject ..."
	rocq makefile -f _CoqProject -o Makefile.gen
	$(MAKE) -f Makefile.gen -j"$(shell nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)"

full:
	@if [ -z "$(ROCQ)" ]; then \
		echo "Rocq not found on PATH. Cannot build the full corpus."; \
		echo "The full corpus (with Flocq) is normally built inside the container."; \
		echo "See Dockerfile and docs/development-environment.md."; \
		exit 1; \
	fi
	@echo "Building the full corpus (_CoqProject.full — requires Flocq) ..."
	rocq makefile -f _CoqProject.full -o Makefile.gen
	$(MAKE) -f Makefile.gen -j"$(shell nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)"

check: ci-guards

# ci-guards — the complete set of build-INDEPENDENT corpus guardrails.
# These are pure grep/perl/python (no .vo, no `rocq`), so they run in
# seconds and give fast fail-feedback decoupled from the proof build.
# CI runs exactly this set in a dedicated parallel `guards` job (see
# .github/workflows/ci.yml); `make ci-guards` reproduces it locally.
ci-guards:
	@echo "Running corpus guardrails (build-independent) ..."
	bash scripts/check_admitted.sh
	bash scripts/check_readme_axioms.sh
	bash scripts/check_deferred_registry_sync.sh
	bash scripts/validate-claims.sh
	bash scripts/check_oracle_handrolled.sh
	@echo ""
	@echo "All guardrails passed (or see output above)."

# ci-pr — the fast local PR pre-flight: guardrails + the Stdlib-only
# `theories/` build (the same lane as CI's macOS `rocq` job).  Mirrors
# what a typical proof/doc PR must satisfy without paying for the Flocq
# lane or the oracle link.
ci-pr: ci-guards host

# ci-full — the full local gate: guardrails + the whole corpus
# (`_CoqProject.full`, needs Flocq) + the oracle binary.  Matches what
# `main` re-validates end to end on every merge.
ci-full: ci-guards full oracle
	@echo ""
	@echo "Full local gate complete."

oracle:
	@echo "Building the oracle binary (RocqRefRunner) ..."
	@echo "This usually follows extraction from Validate_binary64_extract.v."
	$(MAKE) -C oracle

env-info:
	@echo "Rocq / environment information (best effort)"
	@echo "--------------------------------------------"
	@command -v rocq  >/dev/null && rocq -v || echo "rocq: not found"
	@command -v coqc  >/dev/null && coqc -v || true
	@command -v ocaml >/dev/null && ocaml -version || echo "ocaml: not found"
	@command -v opam  >/dev/null && opam --version || echo "opam: not found"
	@echo ""
	@echo "For the exact pinned environment see:"
	@echo "  docs/development-environment.md"
	@echo "  Dockerfile"
	@echo "  .claude/startup-rocq.sh"

clean-env:
	@echo "Removing common generated artefacts (safe operation) ..."
	rm -f Makefile.gen Makefile.gen.conf .Makefile.d .Makefile.gen.d .nra.cache
	rm -f theories/*.vo theories/*.glob theories/.*.aux
	rm -f theories-flocq/*.vo theories-flocq/*.glob theories-flocq/.*.aux
	rm -rf oracle/extracted.ml oracle/extracted.mli oracle/oracle_bin oracle/*.cm*
	@echo "Clean done."

# -----------------------------------------------------------------------------
# Gentle hint for people who type `make` expecting the old generated behaviour
# -----------------------------------------------------------------------------
.DEFAULT_GOAL := help
