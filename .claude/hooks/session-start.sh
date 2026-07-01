#!/usr/bin/env bash
# =============================================================================
# .claude/hooks/session-start.sh
# -----------------------------------------------------------------------------
# SessionStart hook for Claude Code on the web.  Provisions the pinned Rocq
# + rocq-stdlib + Flocq 4.2.2 toolchain so the agent can build and verify the
# corpus immediately — without re-discovering the host-install fallback by
# hand every session.
#
# ROCQ VERSION (2026-07 upgrade to 9.2.0): the shipping toolchain (Dockerfile,
# CI) is Rocq 9.2.0.  The `rocq/rocq-prover:9.2.0` image bundles a matching
# rocq-stdlib, but the DEFAULT opam repo used by this host-install fallback may
# not yet carry `rocq-stdlib` for 9.2 (rocq-core and rocq-stdlib are published
# independently, and stdlib can lag).  So we TRY 9.2.0 (letting opam resolve the
# matching stdlib) and fall back to the previous known-good pin (9.1.1 +
# rocq-stdlib 9.0.0) when 9.2 is not yet resolvable — the dev env never breaks
# and auto-adopts 9.2 the moment opam can satisfy it.
#
# This mirrors docs/development-environment.md (the proven restricted-network
# recipe) and only the reachable hosts it documents are used:
#   archive.ubuntu.com (opam) · opam.ocaml.org (rocq) · gitlab.inria.fr (Flocq)
#
# Properties: idempotent (safe to re-run), non-interactive, remote-only.  The
# heavy compile happens once; the resulting ~/.opam switch is captured in the
# cached container state for subsequent sessions.
# =============================================================================
set -euo pipefail

# Only provision in the remote (Claude Code on the web) environment.  Local
# developers use the Dockerfile or docs/development-environment.md directly.
if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
  exit 0
fi

SWITCH="nts-flocq"
ROCQ_VER="9.2.0"                    # shipping target (Dockerfile / CI)
FALLBACK_ROCQ_VER="9.1.1"          # known-good pin while 9.2 stdlib lags in opam
FALLBACK_STDLIB_VER="9.0.0"
FLOCQ_TAG="flocq-4.2.2"

log() { echo "[session-start] $*"; }

SUDO=""; [ "$(id -u)" != "0" ] && SUDO="sudo"
SANDBOX=""; [ "$(id -u)" = "0" ] && SANDBOX="--disable-sandboxing"

# --- 1. opam + base OCaml (from Ubuntu apt) ---------------------------------
if ! command -v opam >/dev/null 2>&1; then
  # Stale third-party PPAs (deadsnakes/ondrej) can 403 and fail apt outright.
  $SUDO rm -f /etc/apt/sources.list.d/*deadsnakes* \
              /etc/apt/sources.list.d/*ondrej* 2>/dev/null || true
  log "installing opam + ocaml from apt"
  $SUDO apt-get update -q
  $SUDO apt-get install -y -q opam autoconf build-essential
fi

# --- 2. opam init + the nts-flocq switch (idempotent) -----------------------
if ! opam switch list >/dev/null 2>&1; then
  log "opam init"
  opam init --bare --no-setup $SANDBOX -y
fi
if ! opam switch list --short 2>/dev/null | grep -qx "$SWITCH"; then
  log "creating switch $SWITCH (ocaml-system.4.14.1)"
  opam switch create "$SWITCH" ocaml-system.4.14.1 -y
fi
eval "$(opam env --switch="$SWITCH")"

# --- 3. Rocq (rocq-core + rocq-stdlib) from the default opam repo ------------
# Prefer the shipping target (9.2.0, matching stdlib resolved by opam); fall
# back to the known-good pin if the default opam repo can't yet satisfy 9.2.
if ! rocq --version 2>/dev/null | grep -qE "$ROCQ_VER|$FALLBACK_ROCQ_VER"; then
  log "installing rocq-core.$ROCQ_VER (+ matching rocq-stdlib; source build, slow first run)"
  if ! opam install --confirm-level=unsafe-yes "rocq-core.$ROCQ_VER" rocq-stdlib 2>/dev/null; then
    log "rocq $ROCQ_VER not resolvable in this opam repo yet — falling back to $FALLBACK_ROCQ_VER"
    opam install --confirm-level=unsafe-yes \
      "rocq-core.$FALLBACK_ROCQ_VER" "rocq-stdlib.$FALLBACK_STDLIB_VER"
  fi
  eval "$(opam env --switch="$SWITCH")"
fi

# --- 4. Flocq (binary64 layer) from gitlab source ---------------------------
# coq.inria.fr (coq-released opam repo) is typically blocked; the flocq-4.2.2
# git tag on gitlab.inria.fr produces byte-identical .vo files.  The source
# build installs into Rocq's user-contrib (NOT as an opam/ocamlfind package),
# so detect it there.
if [ ! -d "$(rocq -where)/user-contrib/Flocq" ]; then
  log "building Flocq $FLOCQ_TAG from source"
  tmp="$(mktemp -d)"
  git clone --depth 1 --branch "$FLOCQ_TAG" \
    https://gitlab.inria.fr/flocq/flocq.git "$tmp/flocq"
  (
    cd "$tmp/flocq"
    autoconf
    COQC="rocq c" COQDEP="rocq dep" ./configure
    ./remake --jobs="$(nproc)"
    ./remake install
  )
  rm -rf "$tmp"
fi

# --- 5. Persist the opam environment for the whole session ------------------
# Convert `VAR='val'; export VAR;` lines into `export VAR='val'` for the
# session env file the agent's shell sources.
if [ -n "${CLAUDE_ENV_FILE:-}" ]; then
  opam env --switch="$SWITCH" --shell=sh \
    | sed -E "s/^([A-Za-z_][A-Za-z0-9_]*)='(.*)';[[:space:]]*export[[:space:]]+\1;?$/export \1='\2'/" \
    >> "$CLAUDE_ENV_FILE"
fi

# --- 6. Regenerate the build Makefile so on-demand `.vo` builds work ---------
# (We intentionally do NOT build the whole corpus here — the agent builds the
#  targets it needs; a fresh checkout would discard pre-built .vo anyway.)
cd "${CLAUDE_PROJECT_DIR:-$(pwd)}"
if command -v rocq >/dev/null 2>&1 && [ -f _CoqProject.full ]; then
  if [ ! -f Makefile.gen ] || [ _CoqProject.full -nt Makefile.gen ]; then
    rocq makefile -f _CoqProject.full -o Makefile.gen
  fi
fi

flocq_ok="missing"; [ -d "$(rocq -where)/user-contrib/Flocq" ] && flocq_ok="$FLOCQ_TAG"
log "ready: $(rocq --version 2>/dev/null | head -1) · Flocq $flocq_ok"
echo "Build a target with:  eval \$(opam env --switch=$SWITCH); make -f Makefile.gen theories/<File>.vo"
