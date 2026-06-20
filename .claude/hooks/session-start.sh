#!/usr/bin/env bash
# =============================================================================
# .claude/hooks/session-start.sh
# -----------------------------------------------------------------------------
# SessionStart hook for Claude Code on the web.  Provisions the pinned Rocq
# 9.1.1 + rocq-stdlib 9.0.0 + Flocq 4.2.2 toolchain so the agent can build and
# verify the corpus immediately — without re-discovering the host-install
# fallback by hand every session.
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
ROCQ_VER="9.1.1"
STDLIB_VER="9.0.0"
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
if ! rocq --version 2>/dev/null | grep -q "$ROCQ_VER"; then
  log "installing rocq-core.$ROCQ_VER + rocq-stdlib.$STDLIB_VER (source build; slow first run)"
  opam install --confirm-level=unsafe-yes \
    "rocq-core.$ROCQ_VER" "rocq-stdlib.$STDLIB_VER"
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
